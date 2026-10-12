import PNP.Concrete.NormalizerCoefficientCompanion
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : Coefficient.State) (tag : Bool) : ((Coefficient.aTerms tag).result r).data = r.data :=
  Coefficient.aTerms_data tag r
example (r : Coefficient.State) (tag : Bool) (n : Nat) (h : r.store.Bounded n) :
    (Coefficient.aTerms tag).fuel r ≤ (Coefficient.aTerms tag).bound.eval n :=
  (Coefficient.aTerms tag).cost r n h
example (r : Coefficient.State) (n : Nat) (h : r.store.Bounded n) :
    Coefficient.imageTerms.fuel r ≤ Coefficient.imageTerms.bound.eval n :=
  Coefficient.imageTerms.cost r n h
example (ctx : Coefficient.Context) (anchor : ctx.Literal ctx.failed 0)
    (row : Nat) (literals : ctx.RowLiterals row) (tag : Bool) :
    Coefficient.EmitsAt ctx row (Coefficient.aTerms tag)
      ((row,tag)::ctx.companionRows anchor literals tag) :=
  Coefficient.aTerms_emits ctx anchor row literals tag
#print axioms Coefficient.emitsAt_seq
#print axioms Coefficient.modeChoose
#print axioms Coefficient.modeChoose_emits
#print axioms Coefficient.companionTerms
#print axioms Coefficient.companionTerms_data
#print axioms Coefficient.companionTerms_emits
#print axioms Coefficient.aTerms
#print axioms Coefficient.aTerms_emits
#print axioms Coefficient.imageTerms
#print axioms Coefficient.imageTerms_emits
end PNP.Concrete.NormalizerBlocks
