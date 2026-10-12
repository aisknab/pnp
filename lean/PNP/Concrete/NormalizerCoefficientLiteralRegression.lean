import PNP.Concrete.NormalizerCoefficientLiteral
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : Coefficient.State) (position : Nat) :
    ((Coefficient.literalTerms position).result r).data = r.data :=
  Coefficient.literalTerms_data position r
example (r : Coefficient.State) (position n : Nat) (h : r.store.Bounded n) :
    (Coefficient.literalTerms position).fuel r ≤ (Coefficient.literalTerms position).bound.eval n :=
  (Coefficient.literalTerms position).cost r n h
example (ctx : Coefficient.Context) (anchor : ctx.Literal ctx.failed 0) (r : Coefficient.State)
    (encoded : ctx.Encoded r) (row position : Nat) (literal : ctx.Literal row position)
    (rowRead : r.row = List.replicate row true) :
    Coefficient.Emits r ((Coefficient.literalTerms position).result r) (ctx.literalRows anchor literal) :=
  Coefficient.literalTerms_emits ctx anchor r encoded row position literal rowRead
#print axioms Coefficient.Context.Encoded.transport
#print axioms Coefficient.Context.literalRows
#print axioms Coefficient.anchor_emits
#print axioms Coefficient.falseLiteralTerms
#print axioms Coefficient.literalTerms
#print axioms Coefficient.literalTerms_data
#print axioms Coefficient.literalTerms_emits
end PNP.Concrete.NormalizerBlocks
