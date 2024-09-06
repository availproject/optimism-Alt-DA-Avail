package tests

import (
	"os"
	"testing"

	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/stretchr/testify/require"

	"github.com/ethereum-optimism/optimism/cannon/mipsevm/exec"
	"github.com/ethereum-optimism/optimism/cannon/mipsevm/testutil"
)

// TODO
func FuzzStateSyscallCloneMT(f *testing.F) {
	v := GetMultiThreadedTestCase(f)
	// t.Skip is causing linting check to fail, disable for now
	//nolint:staticcheck
	f.Fuzz(func(t *testing.T, seed int64) {
		// TODO(cp-903) Customize test for multi-threaded vm
		t.Skip("TODO - customize this test for MTCannon")
		goVm := v.VMFactory(nil, os.Stdout, os.Stderr, testutil.CreateLogger(), testutil.WithRandomization(seed))
		state := goVm.GetState()
		state.GetRegistersRef()[2] = exec.SysClone
		state.GetMemory().SetMemory(state.GetPC(), syscallInsn)
		step := state.GetStep()

		expected := testutil.CreateExpectedState(state)
		expected.Step += 1
		expected.PC = state.GetCpu().NextPC
		expected.NextPC = state.GetCpu().NextPC + 4
		expected.Registers[2] = 0x1
		expected.Registers[7] = 0

		stepWitness, err := goVm.Step(true)
		require.NoError(t, err)
		require.False(t, stepWitness.HasPreimage())

		expected.Validate(t, state)

		evm := testutil.NewMIPSEVM(v.Contracts)
		evmPost := evm.Step(t, stepWitness, step, v.StateHashFn)
		goPost, _ := goVm.GetState().EncodeWitness()
		require.Equal(t, hexutil.Bytes(goPost).String(), hexutil.Bytes(evmPost).String(),
			"mipsevm produced different state than EVM")
	})
}