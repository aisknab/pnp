import PNP.Concrete.CNFDecoderBits

namespace PNP.Concrete.CNFRegisterDecoder

example : isPad [false] = true := rfl
example : isPad [] = false := rfl
example : isPad [true] = false := rfl
example : isPad [false, false] = false := rfl
example : decodedData [] = [false] := rfl
example : decodedData [false] = [false] := rfl
example : decodedData [false, false, true, false] = [false] := rfl
example : decodedData [false, false, true, false, true] = [false] := rfl
example : decodedData [false, false, true, false, false] = [true, false, true, false] := rfl
example : decodedData [false, false, true, false, false, false, false] = [false] := rfl
example (formula : CNFFormula) :
    parseBits .header (encodeCNF formula) = some (formulaData formula) := parseBits_canonical formula
example (bits : BitString) :
    decodedData bits = resultData (decodeEncodedCNF bits) := decodedData_eq_result bits
example (bits : BitString) : (decodedData bits).length ≤ bits.length + 1 := decodedData_length bits

#print axioms parseBits_pairs
#print axioms parseBits_canonical
#print axioms parseBits_eq
#print axioms decodedData_eq_result
#print axioms parseBits_length
#print axioms decodedData_length

end PNP.Concrete.CNFRegisterDecoder
