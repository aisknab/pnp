import PNP.Concrete.CNFDecoderProgram

namespace PNP.Concrete.CNFRegisterDecoder

open BitRegister

example : program.code.length = 81 := program_length
example (input : BitString) : BitRegister.initial program input = state 0 input [] [] := initial_state input
example (rest reversed output : BitString) :
    BitRegister.run program 6 (state 0 (false :: false :: rest) reversed output) =
      state 17 rest (false :: reversed) output := next_six .header .clauses false false rest reversed output rfl
example (rest reversed output : BitString) :
    BitRegister.run program 6 (state 0 (true :: true :: rest) reversed output) =
      state 0 rest (true :: reversed) output := next_six .header .header true true rest reversed output rfl
example (rest reversed output : BitString) :
    BitRegister.run program 6 (state 17 (false :: true :: rest) reversed output) =
      state 34 rest (true :: false :: reversed) output := next_six .clauses .clause false true rest reversed output rfl
example (rest reversed output : BitString) :
    BitRegister.run program 4 (state 51 (true :: false :: rest) reversed output) =
      state 79 (false :: rest) reversed output := invalid_four .literal true false rest reversed output rfl
example (rest reversed output : BitString) :
    BitRegister.run program 6 (state 17 (true :: false :: rest) reversed output) =
      state 68 rest (false :: true :: reversed) output := finish_six .clauses true false rest reversed output rfl

#print axioms program_length
#print axioms initial_state
#print axioms empty_one
#print axioms singleton_three
#print axioms invalid_four
#print axioms next_six
#print axioms finish_six
#print axioms malformed_three
#print axioms pad_empty_one
#print axioms pad_true_one
#print axioms pad_false_more_three
#print axioms pad_good_four
#print axioms reverse_empty_three
#print axioms reverse_cons_three

end PNP.Concrete.CNFRegisterDecoder
