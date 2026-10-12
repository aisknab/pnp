import PNP.Concrete.NormalizerOccurrenceSemantics

namespace PNP.Concrete.NormalizerBlocks

example (clause : List CNFLiteral) (target : Nat) (remaining excess sign reserved : BitString) :
    (Occurrence.tokenScan (encodeLiteralListTokens clause ++ [.finish])
      (Occurrence.waiting target remaining excess sign reserved)).output =
      Occurrence.answer (clause.find? (fun literal => literal.variableIndex == target)) :=
  Occurrence.tokenScan_clause_correct clause target remaining excess sign reserved
example : Occurrence.answer (some (⟨false, 12⟩ : CNFLiteral)) = [true, false] := rfl
example : Occurrence.answer (none : Option CNFLiteral) = [false] := rfl
example : (Occurrence.tokenScan (encodeLiteralListTokens [⟨false, 2⟩, ⟨true, 2⟩] ++ [.finish])
    (Occurrence.waiting 2 [false] [false] [true, false] [])).output = [true, false] := rfl

#print axioms Occurrence.tokenScan_inactive
#print axioms Occurrence.tokenScan_literal
#print axioms Occurrence.tokenScan_clause_correct

end PNP.Concrete.NormalizerBlocks
