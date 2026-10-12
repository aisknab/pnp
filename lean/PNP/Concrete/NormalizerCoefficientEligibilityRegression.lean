import PNP.Concrete.NormalizerCoefficientEligibility
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : Coefficient.State) : (Coefficient.eligibleRow.result r).data = r.data :=
  Coefficient.eligibleRow_data r
example (r : Coefficient.State) (n : Nat) (h : r.data.Bounded n) :
    (Coefficient.fresh Coefficient.eligibleRow).fuel r ≤ 18 + Coefficient.eligibleRow.bound.eval n :=
  Coefficient.fresh_fuel_bound _ r n h
example (row : Nat) : Coefficient.eligibleValue none row row = false := by
  unfold Coefficient.eligibleValue
  have same : (row == row) = true := beq_iff_eq.mpr rfl
  rw [same]
  rfl
example (value row failed : Nat) : Coefficient.eligibleValue (some value) row failed = false := rfl
#print axioms Coefficient.counterComparison
#print axioms Coefficient.sameRows_output
#print axioms Coefficient.differentRows_output
#print axioms Coefficient.eligibleRow
#print axioms Coefficient.eligibleRow_data
#print axioms Coefficient.eligibleRow_canonical
#print axioms Coefficient.eligibleValue_iff
end PNP.Concrete.NormalizerBlocks
