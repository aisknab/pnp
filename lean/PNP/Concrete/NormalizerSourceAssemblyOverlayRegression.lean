import PNP.Concrete.NormalizerSourceAssemblyOverlay
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : CutDriver.State) : (SourceAssembly.extended r).recovery = SourceAssembly.recovery r :=
  SourceAssembly.extended_recovery r
example (r : CutDriver.State) :
    (SourceAssembly.extended r).core.core.row = SourceCheck.candidate r :=
  (SourceAssembly.extended_inputs r).2.2.2.2.1
example (r : CutDriver.State) (n : Nat) (bounded : r.store.Bounded n) :
    (SourceAssembly.extended r).store.Bounded n := SourceAssembly.extended_bounded r n bounded
#print axioms SourceAssembly.extended_store
#print axioms SourceAssembly.extended_registers
#print axioms SourceAssembly.extended_recovery
#print axioms SourceAssembly.extended_inputs
#print axioms SourceAssembly.extended_bounded
#print axioms SourceAssembly.liftCheck_exec
end PNP.Concrete.NormalizerBlocks
