import PNP.Concrete.NormalizerSourceAssemblyDispatch
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : SourceAssembly.State) (output : r.registers.output = TableOwner.answer (some 0)) :
    SourceAssembly.dispatched r = SourceAssembly.failureResult r :=
  SourceAssembly.dispatched_some r 0 output
example (r : SourceAssembly.State) (output : r.registers.output = TableOwner.answer none) :
    SourceAssembly.dispatched r = r := SourceAssembly.dispatched_none r output
example (r : SourceAssembly.State) (n : Nat) (bounded : r.store.Bounded n) :
    SourceAssembly.dispatchSteps r ≤ SourceAssembly.dispatchBound.eval n :=
  SourceAssembly.dispatchSteps_bound r n bounded
#print axioms SourceAssembly.failure_exec
#print axioms SourceAssembly.failureSteps_bound
#print axioms SourceAssembly.failure_recovery
#print axioms SourceAssembly.dispatch_exec
#print axioms SourceAssembly.dispatchSteps_bound
#print axioms SourceAssembly.dispatched_bounded
#print axioms SourceAssembly.dispatched_recovery
#print axioms SourceAssembly.answer_presence
#print axioms SourceAssembly.dispatched_none
#print axioms SourceAssembly.dispatched_some
end PNP.Concrete.NormalizerBlocks
