import PNP.Concrete.NormalizerPreparedDerive

namespace PNP.Concrete.NormalizerBlocks

example (r : CutDriver.State) :
    Exec PreparedDriver.derive r.store (PreparedDriver.deriveSteps r)
      (PreparedDriver.derived r).store := PreparedDriver.derive_exec r

example (r : CutDriver.State) :
    (PreparedDriver.derived r).trace = r.trace ∧
      (PreparedDriver.derived r).variables = r.variables :=
  ⟨(PreparedDriver.derived_frame r).2.2.2.1,(PreparedDriver.derived_frame r).2.2.2.2.2⟩

example (r : CutDriver.State) (bound : Nat) (bounded : r.store.Bounded bound) :
    PreparedDriver.deriveSteps r ≤ PreparedDriver.deriveBound.eval bound :=
  PreparedDriver.deriveSteps_bound r bound bounded

#print axioms PreparedDriver.setupDense_exec
#print axioms PreparedDriver.setup_fields
#print axioms PreparedDriver.setup_frame
#print axioms PreparedDriver.derive_exec
#print axioms PreparedDriver.derived_frame
#print axioms PreparedDriver.derived_output
#print axioms PreparedDriver.deriveSteps_bound

end PNP.Concrete.NormalizerBlocks
