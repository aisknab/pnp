import PNP.Concrete.NormalizerCoefficientEntry
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (tag : Bool) (r : Coefficient.State) : ((Coefficient.entry tag).result r).data = r.data :=
  Coefficient.entry_data tag r
example (tag : Bool) (r : Coefficient.State) (n : Nat) (h : r.data.Bounded n) :
    (Coefficient.fresh (Coefficient.entry tag)).fuel r ≤ 18 + (Coefficient.entry tag).bound.eval n :=
  Coefficient.fresh_fuel_bound _ r n h
example (ctx : Coefficient.Context) (anchor : ctx.Literal ctx.failed 0)
    (row : Nat) (literals : ctx.RowLiterals row) (tag : Bool) (r : Coefficient.State)
    (encoded : ctx.Encoded r) (rowRead : r.row = List.replicate row true) :
    ((Coefficient.entry tag).result r).registers.output = CoefficientRow.bits row tag ++
      Coefficient.encodeRows ((row,tag)::ctx.companionRows anchor literals tag) :=
  Coefficient.entry_output ctx anchor row literals tag r encoded rowRead
#print axioms Coefficient.prepareRowHeader
#print axioms Coefficient.rowHeader
#print axioms Coefficient.rowHeader_output
#print axioms Coefficient.entry
#print axioms Coefficient.entry_data
#print axioms Coefficient.entry_output
end PNP.Concrete.NormalizerBlocks
