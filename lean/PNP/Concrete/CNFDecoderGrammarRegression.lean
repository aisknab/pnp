import PNP.Concrete.CNFDecoderGrammar

namespace PNP.Concrete.CNFRegisterDecoder

private def emptyFormula : CNFFormula := ⟨0, []⟩
private def emptyClause : CNFFormula := ⟨0, [[]]⟩
private def outsideWidth : CNFFormula := ⟨0, [[⟨true, 3⟩]]⟩

example : formulaData emptyFormula = [false, true, false] := rfl
example : resultData (some emptyFormula) = [true, false, true, false] := rfl
example : resultData none = [false] := rfl
example : (encodeCNF emptyFormula).length = 5 := rfl
example : (encodeCNF emptyClause).length = 9 := rfl

example (formula : CNFFormula) :
    encodeCNF formula = encodeCNF formula :=
  encoded_of_decode _ formula (decodeEncodedCNF_canonical formula)

example (bits : BitString) (formula : CNFFormula) (decoded : decodeEncodedCNF bits = some formula) :
    encodeCNF formula = bits := encoded_of_decode bits formula decoded

-- An out-of-range literal is syntactically well-formed; do not reject it here.
example : decodeEncodedCNF (encodeCNF outsideWidth) = some outsideWidth :=
  decodeEncodedCNF_canonical outsideWidth

example : decodeEncodedCNF [] = none := rfl
example : decodeEncodedCNF [false] = none := rfl
example : decodeEncodedCNF [false, false, true, false] = none := rfl
example : decodeEncodedCNF [false, false, true, false, true] = none := rfl
example : decodeEncodedCNF [false, false, true, false, false, false, false] = none := rfl

#print axioms clausesSuffix_cons
#print axioms clauseSuffix_cons
#print axioms unary_tokens
#print axioms replicate_succ_tail
#print axioms clauses_of_decode
#print axioms clause_of_decode
#print axioms header_of_decode
#print axioms tokens_of_decode
#print axioms token_bits_ofBits
#print axioms pairs_of_decode
#print axioms encoded_of_decode

end PNP.Concrete.CNFRegisterDecoder
