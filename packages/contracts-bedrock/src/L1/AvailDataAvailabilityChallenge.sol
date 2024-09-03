// SPDX-License-Identifier: MIT
pragma solidity 0.8.15;

import {
    DataAvailabilityChallenge,
    ChallengeStatus,
    Challenge,
    CommitmentType,
    computeCommitmentKeccak256
} from "./DataAvailabilityChallenge.sol";

contract AvailDataAvailabilityChallenge is DataAvailabilityChallenge {
    function challenge(uint256 challengedBlockNumber, bytes calldata refBytes) public payable override {
        (,,, bytes memory challengedCommitment) = decodeRefBytes(refBytes);

        validateCommitment(challengedCommitment);

       _updateStateOnChallenge(challengedBlockNumber, refBytes);
    }

    function resolve(
        uint256 challengedBlockNumber,
        bytes calldata refBytes,
        bytes calldata resolveData
    )
        public
        override
    {
        (,,, bytes memory challengedCommitment) = decodeRefBytes(refBytes);

        // require the commitment type to be known
        validateCommitment(challengedCommitment);

        // require the challenge to be active (started, not resolved, and resolve window still open)
        if (getChallengeStatus(challengedBlockNumber, refBytes) != ChallengeStatus.Active) {
            revert ChallengeNotActive();
        }

        // compute the commitment corresponding to the given resolveData
        uint8 commitmentType = _getCommitmentType(challengedCommitment);
        bytes memory computedCommitment;
        if (commitmentType == uint8(CommitmentType.Keccak256)) {
            computedCommitment = computeCommitmentKeccak256(resolveData);
        }

        // require the provided input data to correspond to the challenged commitment
        if (keccak256(computedCommitment) != keccak256(challengedCommitment)) {
            revert InvalidInputData(computedCommitment, challengedCommitment);
        }

        // store the block number at which the challenge was resolved
        Challenge storage activeChallenge = challenges[challengedBlockNumber][refBytes];
        activeChallenge.resolvedBlock = block.number;

        // emit an event to notify that the challenge status is now resolved
        emit ChallengeStatusChanged(challengedBlockNumber, refBytes, ChallengeStatus.Resolved);

        // distribute the bond among challenger, resolver and address(0)
        _distributeBond(activeChallenge, resolveData.length, msg.sender);
    }

    function decodeRefBytes(bytes memory refBytes) public pure returns (string memory blockHash, string memory sender, uint256 nonce, bytes memory commitment) {
      return abi.decode(refBytes, (string, string, uint256, bytes));
    }
}
