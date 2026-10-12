/-
Copyright (c) 2026 PNP Labs.

The closed finite register program for strict CNF decoding. Its 81 instructions
inspect raw bits, emit a unary header and ordered formula data, verify the unique
final pad, and reverse the accumulated output. Failure is an explicit data tag.
-/

import PNP.Concrete.CNFDecoderBits
import PNP.Concrete.BitRegisterProgram

namespace PNP.Concrete.CNFRegisterDecoder

open BitRegister

def modeAddress : Mode → Nat
  | .header => 0
  | .clauses => 17
  | .clause => 34
  | .literal => 51

private def handler (mode : Mode) (token : CNFToken) (address : Nat) :
    List (Instruction 3) :=
  match transition mode token with
  | .invalid => [.jump 79, .reject, .reject]
  | .next next =>
      match emitted mode token with
      | [bit] => [.pop 0 (address + 1), .push 1 bit (address + 2), .jump (modeAddress next)]
      | [first, second] =>
          [.pop 0 (address + 1), .push 1 first (address + 2), .push 1 second (modeAddress next)]
      | _ => [.reject, .reject, .reject]
  | .finish => [.pop 0 (address + 1), .push 1 true (address + 2), .push 1 false 68]

private def modeCode (mode : Mode) : List (Instruction 3) :=
  let address := modeAddress mode
  [.branch 0 79 (address + 1) (address + 3),
   .pop 0 (address + 2),
   .branch 0 79 (address + 5) (address + 11),
   .pop 0 (address + 4),
   .branch 0 79 (address + 14) (address + 8)] ++
  handler mode .f (address + 5) ++
  handler mode .t (address + 8) ++
  handler mode .sep (address + 11) ++
  handler mode .finish (address + 14)

def program : Program 3 :=
  ⟨modeCode .header ++ modeCode .clauses ++ modeCode .clause ++ modeCode .literal ++
    [.branch 0 79 69 79,
     .pop 0 70,
     .branch 0 71 79 79,
     .clear 2 72,
     .branch 1 77 73 75,
     .pop 1 74,
     .push 2 false 72,
     .pop 1 76,
     .push 2 true 72,
     .push 2 true 78,
     .accept,
     .clear 2 80,
     .push 2 false 78],
   0, 0, 2⟩

def bank (input reversed output : BitString) : Store 3 :=
  .cons input (.cons reversed (.cons output .nil))

def state (address : Nat) (input reversed output : BitString) : BitRegister.Configuration 3 :=
  ⟨.running address, bank input reversed output⟩

theorem program_length : program.code.length = 81 := rfl

theorem initial_state (input : BitString) :
    BitRegister.initial program input = state (modeAddress .header) input [] [] := rfl

theorem empty_one (mode : Mode) (reversed output : BitString) :
    BitRegister.run program 1 (state (modeAddress mode) [] reversed output) = state 79 [] reversed output := by
  cases mode <;> rfl

theorem singleton_three (mode : Mode) (bit : Bool) (reversed output : BitString) :
    BitRegister.run program 3 (state (modeAddress mode) [bit] reversed output) = state 79 [] reversed output := by
  cases mode <;> cases bit <;> rfl

theorem invalid_four (mode : Mode) (first second : Bool) (rest reversed output : BitString)
    (action : transition mode (CNFToken.ofBits first second) = .invalid) :
    BitRegister.run program 4 (state (modeAddress mode) (first :: second :: rest) reversed output) =
      state 79 (second :: rest) reversed output := by
  cases mode <;> cases first <;> cases second <;>
    simp only [transition, CNFToken.ofBits] at action <;> cases action <;> rfl

theorem next_six (mode next : Mode) (first second : Bool) (rest reversed output : BitString)
    (action : transition mode (CNFToken.ofBits first second) = .next next) :
    BitRegister.run program 6 (state (modeAddress mode) (first :: second :: rest) reversed output) =
      state (modeAddress next) rest
        ((emitted mode (CNFToken.ofBits first second)).reverse ++ reversed) output := by
  cases mode <;> cases first <;> cases second <;>
    simp only [transition, CNFToken.ofBits, Action.next.injEq] at action <;> cases action <;> rfl

theorem finish_six (mode : Mode) (first second : Bool) (rest reversed output : BitString)
    (action : transition mode (CNFToken.ofBits first second) = .finish) :
    BitRegister.run program 6 (state (modeAddress mode) (first :: second :: rest) reversed output) =
      state 68 rest ((emitted mode (CNFToken.ofBits first second)).reverse ++ reversed) output := by
  cases mode <;> cases first <;> cases second <;>
    simp only [transition, CNFToken.ofBits] at action <;> cases action <;> rfl

theorem malformed_three (input reversed output : BitString) :
    BitRegister.run program 3 (state 79 input reversed output) =
      ⟨.accepted, bank input reversed [false]⟩ := rfl

theorem pad_empty_one (reversed output : BitString) :
    BitRegister.run program 1 (state 68 [] reversed output) = state 79 [] reversed output := rfl

theorem pad_true_one (rest reversed output : BitString) :
    BitRegister.run program 1 (state 68 (true :: rest) reversed output) =
      state 79 (true :: rest) reversed output := rfl

theorem pad_false_more_three (bit : Bool) (rest reversed output : BitString) :
    BitRegister.run program 3 (state 68 (false :: bit :: rest) reversed output) =
      state 79 (bit :: rest) reversed output := by
  cases bit <;> rfl

theorem pad_good_four (reversed output : BitString) :
    BitRegister.run program 4 (state 68 [false] reversed output) = state 72 [] reversed [] := rfl

theorem reverse_empty_three (input output : BitString) :
    BitRegister.run program 3 (state 72 input [] output) = ⟨.accepted, bank input [] (true :: output)⟩ := rfl

theorem reverse_cons_three (input : BitString) (bit : Bool) (rest output : BitString) :
    BitRegister.run program 3 (state 72 input (bit :: rest) output) = state 72 input rest (bit :: output) := by
  cases bit <;> rfl

end PNP.Concrete.CNFRegisterDecoder
