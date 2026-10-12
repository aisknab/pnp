import PNP.Concrete.NormalizerCacheModeLoop

namespace PNP.Concrete.NormalizerBlocks

example (r : CacheMode.State) : Exec CacheMode.loop r.store (CacheMode.whole r).fuel (CacheMode.whole r).state.store :=
  CacheMode.whole_exec r
example (r : CacheMode.State) : CacheMode.cursorBudget (CacheMode.stepped r) ≤ CacheMode.cursorBudget r :=
  CacheMode.stepped_budget r
example (r : CacheMode.State) (n : Nat) (b : CacheMode.cursorBudget r ≤ n)
    (f : r.core.formula.length ≤ n) (v : r.core.core.variables.length ≤ n) (m : r.matching.length ≤ n) :
    (CacheMode.whole r).fuel ≤ CacheMode.loopBound.eval n :=
  CacheMode.whole_fuel_bound r n b f v m

#print axioms CacheMode.step_exec
#print axioms CacheMode.stepped_fields
#print axioms CacheMode.step_progress
#print axioms CacheMode.stepped_budget
#print axioms CacheMode.stepFuel_bound
#print axioms CacheMode.scan_exec
#print axioms CacheMode.scan_fields
#print axioms CacheMode.scan_fuel_bound
#print axioms CacheMode.whole_exec
#print axioms CacheMode.whole_fields
#print axioms CacheMode.whole_fuel_bound

end PNP.Concrete.NormalizerBlocks
