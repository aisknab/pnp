import PNP.Concrete.NormalizerOutputState
namespace PNP.Concrete.NormalizerBlocks
example (r : CutDriver.State) (width : BitString) : (OutputBranches.extend r width).b = width := rfl
example (r : CutDriver.State) : (SourceRecovery.view (OutputBranches.requested r [])).remaining = [] := rfl
example (r : CutDriver.State) : (SourceRecovery.view (OutputBranches.requested r [true,false])).remaining = [true,false] := rfl
#print axioms OutputBranches.extend_store
#print axioms OutputBranches.extend_bounded
#print axioms OutputBranches.liftCheck_exec
#print axioms OutputBranches.requested_store
#print axioms OutputBranches.requested_frame
#print axioms OutputBranches.loadWidth_exec
#print axioms OutputBranches.recover_exec
#print axioms OutputBranches.recovered_output
#print axioms OutputBranches.recovered_length
#print axioms OutputBranches.recoveryFuel_bound
end PNP.Concrete.NormalizerBlocks
