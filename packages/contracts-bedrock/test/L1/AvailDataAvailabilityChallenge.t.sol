// SPDX-License-Identifier: MIT
pragma solidity 0.8.15;

import {
    DataAvailabilityChallenge,
    ChallengeStatus,
    Challenge,
    CommitmentType,
    computeCommitmentKeccak256
} from "src/L1/DataAvailabilityChallenge.sol";

import { Proxy } from "src/universal/Proxy.sol";
import { CommonTest } from "test/setup/CommonTest.sol";


contract AvailDataAvailabilityChallengeTest is CommonTest {
    function setUp() public virtual override {
        super.enableAvailPlasma();
        super.setUp();
    }

    function testDeposit() public {
        assertEq(availDataAvailabilityChallenge.balances(address(this)), 0);
        availDataAvailabilityChallenge.deposit{ value: 1000 }();
        assertEq(availDataAvailabilityChallenge.balances(address(this)), 1000);
    }

    function testReceive() public {
        assertEq(availDataAvailabilityChallenge.balances(address(this)), 0);
        (bool success,) = payable(address(availDataAvailabilityChallenge)).call{ value: 1000 }("");
        assertTrue(success);
        assertEq(availDataAvailabilityChallenge.balances(address(this)), 1000);
    }

    function testWithdraw(address sender, uint256 amount) public {
        assumePayable(sender);
        assumeNotPrecompile(sender);
        vm.assume(sender != address(availDataAvailabilityChallenge));
        vm.assume(sender.balance == 0);
        vm.deal(sender, amount);

        vm.prank(sender);
        availDataAvailabilityChallenge.deposit{ value: amount }();

        assertEq(availDataAvailabilityChallenge.balances(sender), amount);
        assertEq(sender.balance, 0);

        vm.prank(sender);
        availDataAvailabilityChallenge.withdraw();

        assertEq(availDataAvailabilityChallenge.balances(sender), 0);
        assertEq(sender.balance, amount);
    }

    function testChallengeSuccess(address challenger, uint256 challengedBlockNumber, bytes calldata preImage) public {
        bytes memory challengedCommitment = computeCommitmentKeccak256(preImage);
        bytes memory refData = createRefBytes(challengedCommitment);

        // Assume the challenger is not the 0 address
        vm.assume(challenger != address(0));

        // Assume the block number is not close to the max uint256 value
        vm.assume(
            challengedBlockNumber
                < type(uint256).max - availDataAvailabilityChallenge.challengeWindow()
                    - availDataAvailabilityChallenge.resolveWindow()
        );
        uint256 requiredBond = availDataAvailabilityChallenge.bondSize();

        // Move to a block after the challenged block
        vm.roll(challengedBlockNumber + 1);

        // Deposit the required bond
        vm.deal(challenger, requiredBond);
        vm.prank(challenger);
        availDataAvailabilityChallenge.deposit{ value: requiredBond }();

        // Expect the challenge status to be uninitialized
        assertEq(
            uint8(availDataAvailabilityChallenge.getChallengeStatus(challengedBlockNumber, refData)),
            uint8(ChallengeStatus.Uninitialized)
        );

        // Challenge a (blockNumber,hash) tuple
        vm.prank(challenger);
        availDataAvailabilityChallenge.challenge(challengedBlockNumber, refData);

        // Challenge should have been created
        Challenge memory challenge = availDataAvailabilityChallenge.getChallenge(challengedBlockNumber, refData);
        assertEq(challenge.challenger, challenger);
        assertEq(challenge.startBlock, block.number);
        assertEq(challenge.resolvedBlock, 0);
        assertEq(challenge.lockedBond, requiredBond);
        assertEq(
            uint8(availDataAvailabilityChallenge.getChallengeStatus(challengedBlockNumber, refData)),
            uint8(ChallengeStatus.Active)
        );

        // Challenge should have decreased the challenger's bond size
        assertEq(availDataAvailabilityChallenge.balances(challenger), 0);
    }

    function testChallengeDeposit(address challenger, uint256 challengedBlockNumber, bytes memory preImage) public {
        bytes memory challengedCommitment = computeCommitmentKeccak256(preImage);
        bytes memory refData = createRefBytes(challengedCommitment);

        // Assume the challenger is not the 0 address
        vm.assume(challenger != address(0));

        // Assume the block number is not close to the max uint256 value
        vm.assume(
            challengedBlockNumber
                < type(uint256).max - availDataAvailabilityChallenge.challengeWindow()
                    - availDataAvailabilityChallenge.resolveWindow()
        );
        uint256 requiredBond = availDataAvailabilityChallenge.bondSize();

        // Move to a block after the challenged block
        vm.roll(challengedBlockNumber + 1);

        // Expect the challenge status to be uninitialized
        assertEq(
            uint8(availDataAvailabilityChallenge.getChallengeStatus(challengedBlockNumber, refData)),
            uint8(ChallengeStatus.Uninitialized)
        );

        // Deposit the required bond as part of the challenge transaction
        vm.deal(challenger, requiredBond);
        vm.prank(challenger);
        availDataAvailabilityChallenge.challenge{ value: requiredBond }(challengedBlockNumber, refData);

        // Challenge should have been created
        Challenge memory challenge = availDataAvailabilityChallenge.getChallenge(challengedBlockNumber, refData);
        assertEq(challenge.challenger, challenger);
        assertEq(challenge.startBlock, block.number);
        assertEq(challenge.resolvedBlock, 0);
        assertEq(challenge.lockedBond, requiredBond);
        assertEq(
            uint8(availDataAvailabilityChallenge.getChallengeStatus(challengedBlockNumber, refData)),
            uint8(ChallengeStatus.Active)
        );

        // Challenge should have decreased the challenger's bond size
        assertEq(availDataAvailabilityChallenge.balances(challenger), 0);
    }

    function testChallengeFailBondTooLow() public {
        uint256 requiredBond = availDataAvailabilityChallenge.bondSize();
        uint256 actualBond = requiredBond - 1;
        availDataAvailabilityChallenge.deposit{ value: actualBond }();

        bytes memory challengedCommitment = computeCommitmentKeccak256("some hash");
        bytes memory refData = createRefBytes(challengedCommitment);

        vm.expectRevert(abi.encodeWithSelector(DataAvailabilityChallenge.BondTooLow.selector, actualBond, requiredBond));
        availDataAvailabilityChallenge.challenge(0, refData);
    }

    function testChallengeFailChallengeExists() public {
        // Move to a block after the hash to challenge
        vm.roll(2);

        // First challenge succeeds
        bytes memory challengedCommitment = computeCommitmentKeccak256("some data");
        bytes memory refData = createRefBytes(challengedCommitment);

        availDataAvailabilityChallenge.deposit{ value: availDataAvailabilityChallenge.bondSize() }();
        availDataAvailabilityChallenge.challenge(0, refData);

        // Second challenge of the same hash/blockNumber fails
        availDataAvailabilityChallenge.deposit{ value: availDataAvailabilityChallenge.bondSize() }();
        vm.expectRevert(abi.encodeWithSelector(DataAvailabilityChallenge.ChallengeExists.selector));
        availDataAvailabilityChallenge.challenge(0, refData);

        // Challenge succeed if the challenged block number is different
        availDataAvailabilityChallenge.deposit{ value: availDataAvailabilityChallenge.bondSize() }();
        availDataAvailabilityChallenge.challenge(1, refData);

        bytes memory someOtherChallenge = computeCommitmentKeccak256("some other hash");
        bytes memory otherChallengeRefData = createRefBytes(someOtherChallenge);
        // Challenge succeed if the challenged hash is different
        availDataAvailabilityChallenge.deposit{ value: availDataAvailabilityChallenge.bondSize() }();
        availDataAvailabilityChallenge.challenge(0, otherChallengeRefData);
    }

    function testChallengeFailBeforeChallengeWindow() public {
        uint256 challengedBlockNumber = 1;
        bytes memory challengedCommitment = computeCommitmentKeccak256("some hash");
        bytes memory refData = createRefBytes(challengedCommitment);

        // Move to challenged block
        vm.roll(challengedBlockNumber - 1);

        // Challenge fails because the current block number must be after the challenged block
        availDataAvailabilityChallenge.deposit{ value: availDataAvailabilityChallenge.bondSize() }();
        vm.expectRevert(abi.encodeWithSelector(DataAvailabilityChallenge.ChallengeWindowNotOpen.selector));
        availDataAvailabilityChallenge.challenge(challengedBlockNumber, refData);
    }

    function testChallengeFailAfterChallengeWindow() public {
        uint256 challengedBlockNumber = 1;
        bytes memory challengedCommitment = computeCommitmentKeccak256("some hash");
        bytes memory refData = createRefBytes(challengedCommitment);

        // Move to block after the challenge window
        vm.roll(challengedBlockNumber + availDataAvailabilityChallenge.challengeWindow() + 1);

        // Challenge fails because the block number is after the challenge window
        availDataAvailabilityChallenge.deposit{ value: availDataAvailabilityChallenge.bondSize() }();
        vm.expectRevert(abi.encodeWithSelector(DataAvailabilityChallenge.ChallengeWindowNotOpen.selector));
        availDataAvailabilityChallenge.challenge(challengedBlockNumber, refData);
    }

    function testResolveSuccess(
        address challenger,
        address resolver,
        bytes memory preImage,
        uint256 challengedBlockNumber,
        uint256 resolverRefundPercentage,
        uint128 txGasPrice
    )
        public
    {
        // Assume neither the challenger nor resolver is address(0) and that they're not the same entity
        vm.assume(challenger != address(0));
        vm.assume(resolver != address(0));
        vm.assume(challenger != resolver);

        // Bound the resolver refund percentage to 100
        resolverRefundPercentage = bound(resolverRefundPercentage, 0, 100);

        // Set the gas price to a fuzzed value to test bond distribution logic
        vm.txGasPrice(txGasPrice);

        // Change the resolver refund percentage
        vm.prank(availDataAvailabilityChallenge.owner());
        availDataAvailabilityChallenge.setResolverRefundPercentage(resolverRefundPercentage);

        // Assume the block number is not close to the max uint256 value
        vm.assume(
            challengedBlockNumber
                < type(uint256).max - availDataAvailabilityChallenge.challengeWindow()
                    - availDataAvailabilityChallenge.resolveWindow()
        );
        bytes memory challengedCommitment = computeCommitmentKeccak256(preImage);
        bytes memory refData = createRefBytes(challengedCommitment);

        // Move to block after challenged block
        vm.roll(challengedBlockNumber + 1);

        // Challenge the hash
        uint256 bondSize = availDataAvailabilityChallenge.bondSize();
        vm.deal(challenger, bondSize);
        vm.prank(challenger);
        availDataAvailabilityChallenge.challenge{ value: bondSize }(challengedBlockNumber, refData);

        // Store the address(0) balance before resolving to assert the burned amount later
        uint256 zeroAddressBalanceBeforeResolve = address(0).balance;

        // Resolve the challenge
        vm.prank(resolver);
        availDataAvailabilityChallenge.resolve(challengedBlockNumber, refData, preImage);

        // Expect the challenge to be resolved
        Challenge memory challenge = availDataAvailabilityChallenge.getChallenge(challengedBlockNumber, refData);

        assertEq(challenge.challenger, challenger);
        assertEq(challenge.lockedBond, 0);
        assertEq(challenge.startBlock, block.number);
        assertEq(challenge.resolvedBlock, block.number);
        assertEq(
            uint8(availDataAvailabilityChallenge.getChallengeStatus(challengedBlockNumber, refData)),
            uint8(ChallengeStatus.Resolved)
        );

        // Assert challenger balance after bond distribution
        uint256 resolutionCost = (
            availDataAvailabilityChallenge.fixedResolutionCost()
                + preImage.length * availDataAvailabilityChallenge.variableResolutionCost()
                    / availDataAvailabilityChallenge.variableResolutionCostPrecision()
        ) * block.basefee;
        uint256 challengerRefund = bondSize > resolutionCost ? bondSize - resolutionCost : 0;
        assertEq(availDataAvailabilityChallenge.balances(challenger), challengerRefund, "challenger refund");

        // Assert resolver balance after bond distribution
        uint256 resolverRefund = resolutionCost * availDataAvailabilityChallenge.resolverRefundPercentage() / 100;
        resolverRefund = resolverRefund > resolutionCost ? resolutionCost : resolverRefund;
        resolverRefund = resolverRefund > bondSize ? bondSize : resolverRefund;
        assertEq(availDataAvailabilityChallenge.balances(resolver), resolverRefund, "resolver refund");

        // Assert burned amount after bond distribution
        uint256 burned = bondSize - challengerRefund - resolverRefund;
        assertEq(address(0).balance - zeroAddressBalanceBeforeResolve, burned, "burned bond");
    }

    function testResolveFailNonExistentChallenge() public {
        bytes memory preImage = "some preimage";
        uint256 challengedBlockNumber = 1;

        // Move to block after challenged block
        vm.roll(challengedBlockNumber + 1);

        // Resolving a non-existent challenge fails
        vm.expectRevert(abi.encodeWithSelector(DataAvailabilityChallenge.ChallengeNotActive.selector));
        bytes memory commitment = computeCommitmentKeccak256(preImage);
        bytes memory refData = createRefBytes(commitment);
        availDataAvailabilityChallenge.resolve(challengedBlockNumber, refData, preImage);
    }

    function testResolveFailResolved() public {
        bytes memory preImage = "some preimage";
        bytes memory challengedCommitment = computeCommitmentKeccak256(preImage);
        bytes memory refData = createRefBytes(challengedCommitment);
        uint256 challengedBlockNumber = 1;

        // Move to block after challenged block
        vm.roll(challengedBlockNumber + 1);

        // Challenge the hash
        availDataAvailabilityChallenge.deposit{ value: availDataAvailabilityChallenge.bondSize() }();
        availDataAvailabilityChallenge.challenge(challengedBlockNumber, refData);

        // Resolve the challenge
        availDataAvailabilityChallenge.resolve(challengedBlockNumber, refData, preImage);

        // Resolving an already resolved challenge fails
        vm.expectRevert(abi.encodeWithSelector(DataAvailabilityChallenge.ChallengeNotActive.selector));
        availDataAvailabilityChallenge.resolve(challengedBlockNumber, refData, preImage);
    }

    function testResolveFailExpired() public {
        bytes memory preImage = "some preimage";
        bytes memory challengedCommitment = computeCommitmentKeccak256(preImage);
        bytes memory refData = createRefBytes(challengedCommitment);
        uint256 challengedBlockNumber = 1;

        // Move to block after challenged block
        vm.roll(challengedBlockNumber + 1);

        // Challenge the hash
        availDataAvailabilityChallenge.deposit{ value: availDataAvailabilityChallenge.bondSize() }();
        availDataAvailabilityChallenge.challenge(challengedBlockNumber, refData);

        // Move to a block after the resolve window
        vm.roll(block.number + availDataAvailabilityChallenge.resolveWindow() + 1);

        // Resolving an expired challenge fails
        vm.expectRevert(abi.encodeWithSelector(DataAvailabilityChallenge.ChallengeNotActive.selector));
        availDataAvailabilityChallenge.resolve(challengedBlockNumber, refData, preImage);
    }

    function testResolveFailAfterResolveWindow() public {
        bytes memory preImage = "some preimage";
        bytes memory challengedCommitment = computeCommitmentKeccak256(preImage);
        bytes memory refData = createRefBytes(challengedCommitment);
        uint256 challengedBlockNumber = 1;

        // Move to block after challenged block
        vm.roll(challengedBlockNumber + 1);

        // Challenge the hash
        availDataAvailabilityChallenge.deposit{ value: availDataAvailabilityChallenge.bondSize() }();
        availDataAvailabilityChallenge.challenge(challengedBlockNumber, refData);

        // Move to block after resolve window
        vm.roll(block.number + availDataAvailabilityChallenge.resolveWindow() + 1);

        // Resolve the challenge
        vm.expectRevert(abi.encodeWithSelector(DataAvailabilityChallenge.ChallengeNotActive.selector));
        availDataAvailabilityChallenge.resolve(challengedBlockNumber, refData, preImage);
    }

    function testUnlockBondSuccess(bytes memory preImage, uint256 challengedBlockNumber) public {
        // Assume the block number is not close to the max uint256 value
        vm.assume(
            challengedBlockNumber
                < type(uint256).max - availDataAvailabilityChallenge.challengeWindow()
                    - availDataAvailabilityChallenge.resolveWindow()
        );
        bytes memory challengedCommitment = computeCommitmentKeccak256(preImage);
        bytes memory refData = createRefBytes(challengedCommitment);

        // Move to block after challenged block
        vm.roll(challengedBlockNumber + 1);

        // Challenge the hash
        availDataAvailabilityChallenge.deposit{ value: availDataAvailabilityChallenge.bondSize() }();
        availDataAvailabilityChallenge.challenge(challengedBlockNumber, refData);

        // Move to a block after the resolve window
        vm.roll(block.number + availDataAvailabilityChallenge.resolveWindow() + 1);

        uint256 balanceBeforeUnlock = availDataAvailabilityChallenge.balances(address(this));

        // Unlock the bond associated with the challenge
        availDataAvailabilityChallenge.unlockBond(challengedBlockNumber, refData);

        // Expect the balance to be increased by the bond size
        uint256 balanceAfterUnlock = availDataAvailabilityChallenge.balances(address(this));
        assertEq(balanceAfterUnlock, balanceBeforeUnlock + availDataAvailabilityChallenge.bondSize());

        // Expect the bond to be unlocked
        Challenge memory challenge = availDataAvailabilityChallenge.getChallenge(challengedBlockNumber, refData);

        assertEq(challenge.challenger, address(this));
        assertEq(challenge.lockedBond, 0);
        assertEq(challenge.startBlock, challengedBlockNumber + 1);
        assertEq(challenge.resolvedBlock, 0);
        assertEq(
            uint8(availDataAvailabilityChallenge.getChallengeStatus(challengedBlockNumber, refData)),
            uint8(ChallengeStatus.Expired)
        );

        // Unlock the bond again, expect the balance to remain the same
        availDataAvailabilityChallenge.unlockBond(challengedBlockNumber, refData);
        assertEq(availDataAvailabilityChallenge.balances(address(this)), balanceAfterUnlock);
    }

    function testUnlockBondFailNonExistentChallenge() public {
        bytes memory preImage = "some preimage";
        bytes memory challengedCommitment = computeCommitmentKeccak256(preImage);
        bytes memory refData = createRefBytes(challengedCommitment);
        uint256 challengedBlockNumber = 1;

        // Move to block after challenged block
        vm.roll(challengedBlockNumber + 1);

        // Unlock a bond of a non-existent challenge fails
        vm.expectRevert(abi.encodeWithSelector(DataAvailabilityChallenge.ChallengeNotExpired.selector));
        availDataAvailabilityChallenge.unlockBond(challengedBlockNumber, refData);
    }

    function testUnlockBondFailResolvedChallenge() public {
        bytes memory preImage = "some preimage";
        bytes memory challengedCommitment = computeCommitmentKeccak256(preImage);
        bytes memory refData = createRefBytes(challengedCommitment);
        uint256 challengedBlockNumber = 1;

        // Move to block after challenged block
        vm.roll(challengedBlockNumber + 1);

        // Challenge the hash
        availDataAvailabilityChallenge.deposit{ value: availDataAvailabilityChallenge.bondSize() }();
        availDataAvailabilityChallenge.challenge(challengedBlockNumber, refData);

        // Resolve the challenge
        availDataAvailabilityChallenge.resolve(challengedBlockNumber, refData, preImage);

        // Attempting to unlock a bond of a resolved challenge fails
        vm.expectRevert(abi.encodeWithSelector(DataAvailabilityChallenge.ChallengeNotExpired.selector));
        availDataAvailabilityChallenge.unlockBond(challengedBlockNumber, refData);
    }

    function testUnlockBondExpiredChallengeTwice() public {
        bytes memory preImage = "some preimage";
        bytes memory challengedCommitment = computeCommitmentKeccak256(preImage);
        bytes memory refData = createRefBytes(challengedCommitment);
        uint256 challengedBlockNumber = 1;

        // Move to block after challenged block
        vm.roll(challengedBlockNumber + 1);

        // Challenge the hash
        availDataAvailabilityChallenge.deposit{ value: availDataAvailabilityChallenge.bondSize() }();
        availDataAvailabilityChallenge.challenge(challengedBlockNumber, refData);

        // Move to a block after the challenge window
        vm.roll(block.number + availDataAvailabilityChallenge.resolveWindow() + 1);

        // Unlock the bond
        availDataAvailabilityChallenge.unlockBond(challengedBlockNumber, refData);

        uint256 balanceAfterUnlock = availDataAvailabilityChallenge.balances(address(this));

        // Unlock the bond again doesn't change the balance
        availDataAvailabilityChallenge.unlockBond(challengedBlockNumber, refData);
        assertEq(availDataAvailabilityChallenge.balances(address(this)), balanceAfterUnlock);
    }

    function testUnlockFailResolveWindowNotClosed() public {
        bytes memory preImage = "some preimage";
        bytes memory challengedCommitment = computeCommitmentKeccak256(preImage);
        bytes memory refData = createRefBytes(challengedCommitment);
        uint256 challengedBlockNumber = 1;

        // Move to block after challenged block
        vm.roll(challengedBlockNumber + 1);

        // Challenge the hash
        availDataAvailabilityChallenge.deposit{ value: availDataAvailabilityChallenge.bondSize() }();
        availDataAvailabilityChallenge.challenge(challengedBlockNumber, refData);

        vm.roll(block.number + availDataAvailabilityChallenge.resolveWindow() - 1);

        // Expiring the challenge before the resolve window closes fails
        vm.expectRevert(abi.encodeWithSelector(DataAvailabilityChallenge.ChallengeNotExpired.selector));
        availDataAvailabilityChallenge.unlockBond(challengedBlockNumber, refData);
    }

    function testSetBondSize() public {
        uint256 requiredBond = availDataAvailabilityChallenge.bondSize();
        uint256 actualBond = requiredBond - 1;
        availDataAvailabilityChallenge.deposit{ value: actualBond }();

        // Expect the challenge to fail because the bond is too low
        bytes memory challengedCommitment = computeCommitmentKeccak256("some hash");
        bytes memory refData = createRefBytes(challengedCommitment);
        vm.expectRevert(abi.encodeWithSelector(DataAvailabilityChallenge.BondTooLow.selector, actualBond, requiredBond));
        availDataAvailabilityChallenge.challenge(0, refData);

        // Reduce the required bond
        vm.prank(availDataAvailabilityChallenge.owner());
        availDataAvailabilityChallenge.setBondSize(actualBond);

        // Expect the challenge to succeed
        availDataAvailabilityChallenge.challenge(0, refData);
    }

    function testSetResolverRefundPercentage(uint256 resolverRefundPercentage) public {
        resolverRefundPercentage = bound(resolverRefundPercentage, 0, 100);
        vm.prank(availDataAvailabilityChallenge.owner());
        availDataAvailabilityChallenge.setResolverRefundPercentage(resolverRefundPercentage);
        assertEq(availDataAvailabilityChallenge.resolverRefundPercentage(), resolverRefundPercentage);
    }

    function testSetResolverRefundPercentageFail() public {
        address owner = availDataAvailabilityChallenge.owner();
        vm.expectRevert(abi.encodeWithSelector(DataAvailabilityChallenge.InvalidResolverRefundPercentage.selector, 101));
        vm.prank(owner);
        availDataAvailabilityChallenge.setResolverRefundPercentage(101);
    }

    function testSetBondSizeFailOnlyOwner(address notOwner, uint256 newBondSize) public {
        vm.assume(notOwner != availDataAvailabilityChallenge.owner());

        // Expect setting the bond size to fail because the sender is not the owner
        vm.prank(notOwner);
        vm.expectRevert("Ownable: caller is not the owner");
        availDataAvailabilityChallenge.setBondSize(newBondSize);
    }

    function testValidateCommitment() public {
        // Should not revert given a valid commitment
        bytes memory validCommitment = abi.encodePacked(CommitmentType.Keccak256, keccak256("test"));
        availDataAvailabilityChallenge.validateCommitment(validCommitment);

        // Should revert if the commitment type is unknown
        vm.expectRevert(abi.encodeWithSelector(DataAvailabilityChallenge.UnknownCommitmentType.selector, uint8(1)));
        bytes memory unknownType = abi.encodePacked(uint8(1), keccak256("test"));
        availDataAvailabilityChallenge.validateCommitment(unknownType);

        // Should revert if the commitment length does not match
        vm.expectRevert(
            abi.encodeWithSelector(DataAvailabilityChallenge.InvalidCommitmentLength.selector, uint8(0), 33, 34)
        );
        bytes memory invalidLength = abi.encodePacked(CommitmentType.Keccak256, keccak256("test"), "x");
        availDataAvailabilityChallenge.validateCommitment(invalidLength);
    }

    function createRefBytes(bytes memory commitment) public pure returns (bytes memory) {
        // mock data for the block ref pointer
        string memory block_hash = "0x4798c1e7a1ece0f91a79e92fab50266886ad97ffdd71dfdaad708f5a4cec7b8f";
        string memory sender_ref = "5CPboM31KSeUbiFLjAdVmYseSNFNf3kRDeNtJW6ZXvgojBvo";
        uint64 nonce = 10;

        return abi.encode(block_hash, sender_ref, nonce, commitment);
    }
}
