import PNP.Concrete.NormalizerOutputDispatch
namespace PNP.Concrete.NormalizerBlocks
example : (TableOwner.answer none).headD false = false := rfl
example : (TableOwner.answer (some 0)).headD false = true := rfl
example : (TableOwner.answer (some 3)).headD false = true := rfl
#print axioms OutputBranches.extend_outputWord
#print axioms OutputBranches.dispatch_exec
#print axioms OutputBranches.dispatchFuel_bound
#print axioms OutputBranches.dispatched_bounded
#print axioms OutputBranches.dispatched_none
#print axioms OutputBranches.dispatched_some
#print axioms OutputBranches.dispatched_model_output
#print axioms OutputBranches.dispatched_system_output
end PNP.Concrete.NormalizerBlocks
