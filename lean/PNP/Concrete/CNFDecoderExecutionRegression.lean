import PNP.Concrete.CNFDecoderExecution

namespace PNP.Concrete.CNFRegisterDecoder

example (input : BitString) :
    (BitRegister.run program (6 * input.length + 16) (BitRegister.initial program input)).control =
      .accepted := source_accepts input
example (input : BitString) :
    (BitRegister.run program (6 * input.length + 16) (BitRegister.initial program input)).store.get 2 =
      resultData (decodeEncodedCNF input) := source_output input
example (mode : Mode) (bits reversed output : BitString) :
    HasResult
      (BitRegister.run program (6 * bits.length + 3 * reversed.length + 16)
        (state (modeAddress mode) bits reversed output))
      (answer mode bits reversed) := program_result mode bits reversed output
example :
    (BitRegister.run program 16 (BitRegister.initial program [])).store.get 2 = [false] :=
  source_output []
example :
    (BitRegister.run program 46
      (BitRegister.initial program [false, false, true, false, false])).store.get 2 =
      [true, false, true, false] :=
  source_output [false, false, true, false, false]
example :
    (BitRegister.run program 40
      (BitRegister.initial program [false, false, true, false])).store.get 2 = [false] :=
  source_output [false, false, true, false]
example (input : BitString) (invalid : decodeEncodedCNF input = none) :
    (BitRegister.run program (6 * input.length + 16) (BitRegister.initial program input)).store.get 2 =
      [false] := by
  rw [source_output, invalid]
  rfl
example (formula : CNFFormula) :
    (BitRegister.run program (6 * (encodeCNF formula).length + 16)
      (BitRegister.initial program (encodeCNF formula))).store.get 2 = true :: formulaData formula := by
  rw [source_output, decodeEncodedCNF_canonical]
  rfl

#print axioms malformed_result
#print axioms reverse_run
#print axioms reverse_result
#print axioms pad_result
#print axioms answer_next
#print axioms answer_finish
#print axioms program_result
#print axioms source_decodes
#print axioms source_accepts
#print axioms source_output

end PNP.Concrete.CNFRegisterDecoder
