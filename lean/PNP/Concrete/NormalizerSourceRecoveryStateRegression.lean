import PNP.Concrete.NormalizerSourceRecoveryState
namespace PNP.Concrete.NormalizerBlocks
example (r : Recovery.State) : SourceRecovery.ofDense (SourceRecovery.toDense r) = r := rfl
example (r : CutDriver.State) : (SourceRecovery.sourceView r).assignment = SourceCheck.candidate r := rfl
example (r : CutDriver.State) : (SourceRecovery.view (SourceRecovery.widthLoaded r)).remaining = r.core.width := rfl
#print axioms SourceRecovery.ofDense_store
#print axioms SourceRecovery.toDense_store
#print axioms SourceRecovery.lift_exec
#print axioms SourceRecovery.view_bounded
#print axioms SourceRecovery.loadSources_exec
#print axioms SourceRecovery.call_exec
#print axioms SourceRecovery.called_output_length
#print axioms SourceRecovery.called_original_fields
#print axioms SourceRecovery.loadWidth_exec
#print axioms SourceRecovery.fullWidth_exec
#print axioms SourceRecovery.fullWidth_output_length
#print axioms SourceRecovery.callSteps_bound
#print axioms SourceRecovery.fullWidthSteps_bound
end PNP.Concrete.NormalizerBlocks
