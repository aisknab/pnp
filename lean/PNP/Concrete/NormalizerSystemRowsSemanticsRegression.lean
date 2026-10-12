import PNP.Concrete.NormalizerSystemRowsSemantics
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (ctx : Coefficient.Context) (row : Nat) (absent : MatchingTable.read ctx.modes row = none)
    (failed : row = ctx.failed) : SystemRows.eligible ctx row = false := by
  subst row
  unfold SystemRows.eligible Coefficient.eligibleValue
  rw [absent]
  have same : (ctx.failed == ctx.failed) = true := beq_iff_eq.mpr rfl
  rw [same]
  rfl
example (ctx : Coefficient.Context) (row mode : Nat)
    (matched : MatchingTable.read ctx.modes row = some mode) :
    SystemRows.eligible ctx row = false := by
  unfold SystemRows.eligible Coefficient.eligibleValue
  rw [matched]
  rfl
example (ctx : Coefficient.Context) (row : Nat) (absent : MatchingTable.read ctx.modes row = none)
    (different : row ≠ ctx.failed) : SystemRows.eligible ctx row = true :=
  (SystemRows.eligible_iff ctx row).mpr ⟨absent,different⟩
#print axioms SystemRows.entry_packet
#print axioms SystemRows.a_produced
#print axioms SystemRows.image_packet
#print axioms SystemRows.eligible_output
#print axioms SystemRows.eligible_iff
#print axioms SystemRows.e_produced
end PNP.Concrete.NormalizerBlocks
