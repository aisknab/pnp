import PNP.Concrete.CNFDecoderModel

namespace PNP.Concrete.CNFRegisterDecoder

private def exampleFormula : CNFFormula := ⟨2, [[⟨true, 0⟩, ⟨false, 1⟩], []]⟩

example : transition .header .finish = .invalid := rfl
example : transition .clauses .finish = .finish := rfl
example : transition .clause .finish = .next .clauses := rfl
example : transition .literal .finish = .invalid := rfl
example : emitted .header .t = [true] := rfl
example : emitted .literal .t = [true, true] := rfl
example : parseTokens .header [] = none := rfl
example : parseTokens .header [.f, .finish] = some [false, true, false] := rfl
example : parseTokens .header [.f, .finish, .finish] = none := rfl
example : parseTokens .header [.f, .sep, .finish, .finish] =
    some [false, false, true, true, false, true, false] := rfl
example : parseTokens .header [.f, .sep, .t, .finish, .finish] = none := rfl
example (formula : CNFFormula) :
    parseTokens .header (encodeCNFTokens formula) = some (formulaData formula) :=
  parseTokens_canonical formula
example :
    parseTokens .header (encodeCNFTokens exampleFormula) = some (formulaData exampleFormula) :=
  parseTokens_canonical exampleFormula
example (tokens : List CNFToken) (decoded : decodeCNFTokens tokens = none) :
    parseTokens .header tokens = none := parseTokens_none tokens decoded

#print axioms emitted_length_le
#print axioms parseTokens_isSome
#print axioms recognize_header
#print axioms parseTokens_clauses_canonical
#print axioms parseTokens_header_unary
#print axioms parseTokens_canonical
#print axioms parseTokens_none

end PNP.Concrete.CNFRegisterDecoder
