import PNP.ThreeUse.DistinctPorts
import PNP.ThreeUse.FiniteTable
import PNP.ThreeUse.Matrix

/-!
# The typed three-use reduction

The same finite system is equivalent to the strict source and satisfies the occurrence count, distinct-label and distinguished-target restrictions.
-/

set_option autoImplicit false

namespace PNP.ThreeUse
open PNP.Concrete

/-- One finite physical target, no assignment or frame passed to its constructor. -/
theorem strict_finite_three (bits : BitString) :
    (CNFSAT bits ↔ finiteFeasible (targetRows bits)) ∧
    (∀ p, p ∈ labels (targetRows bits) → hits p (labels (targetRows bits)) = 3) ∧
    (∀ r, r ∈ targetRows bits → Simple r.w) ∧
    (∃ head tail, targetRows bits = head :: tail ∧ head.out = mark ∧ head.w.length = 4 ∧ ∀ e, e ∈ tail → plain e) :=
  ⟨strict_finite bits, every_used_exactly_three bits, target_simple bits, target_shape bits⟩

end PNP.ThreeUse
