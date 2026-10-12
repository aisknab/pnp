/-
Copyright (c) 2026 PNP Labs.

Complete accepting-fuel and exact-result proof for the closed CNF decoder.
The proof covers every finite input, rather than supplying a termination or
semantic certificate to the compiler.
-/

import PNP.Concrete.CNFDecoderProgram

namespace PNP.Concrete.CNFRegisterDecoder

open BitRegister

def HasResult (configuration : BitRegister.Configuration 3) (value : BitString) : Prop :=
  configuration.control = .accepted ∧ configuration.store.get 2 = value

private theorem run_accepting (fuel : Nat) (configuration : BitRegister.Configuration 3)
    (accepted : configuration.control = .accepted) :
    BitRegister.run program fuel configuration = configuration := by
  cases configuration with
  | mk control store =>
      cases accepted
      exact BitRegister.run_accepted program fuel store

private theorem result_mono {small large : Nat} {start : BitRegister.Configuration 3}
    {value : BitString} (checked : HasResult (BitRegister.run program small start) value)
    (bound : small ≤ large) : HasResult (BitRegister.run program large start) value := by
  have total : small + (large - small) = large := Nat.add_sub_of_le bound
  rw [← total, BitRegister.run_add, run_accepting _ _ checked.1]
  exact checked

private theorem result_after {firstFuel tailFuel totalFuel : Nat}
    {start middle : BitRegister.Configuration 3} {value : BitString}
    (firstRun : BitRegister.run program firstFuel start = middle)
    (tailRun : HasResult (BitRegister.run program tailFuel middle) value)
    (bound : firstFuel + tailFuel ≤ totalFuel) :
    HasResult (BitRegister.run program totalFuel start) value := by
  apply result_mono (small := firstFuel + tailFuel) _ bound
  rw [BitRegister.run_add, firstRun]
  exact tailRun

theorem malformed_result (input reversed output : BitString) :
    HasResult (BitRegister.run program 3 (state 79 input reversed output)) [false] := by
  rw [malformed_three]
  exact ⟨rfl, rfl⟩

theorem reverse_run (input reversed output : BitString) :
    BitRegister.run program (3 * reversed.length + 3) (state 72 input reversed output) =
      ⟨.accepted, bank input [] (true :: (reversed.reverse ++ output))⟩ := by
  induction reversed generalizing output with
  | nil => exact reverse_empty_three input output
  | cons bit rest ih =>
      have fuel : 3 * (bit :: rest).length + 3 = 3 + (3 * rest.length + 3) := by
        simp only [List.length_cons]
        omega
      rw [fuel, BitRegister.run_add, reverse_cons_three, ih]
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem reverse_result (input reversed output : BitString) :
    HasResult (BitRegister.run program (3 * reversed.length + 3) (state 72 input reversed output))
      (true :: (reversed.reverse ++ output)) := by
  rw [reverse_run]
  exact ⟨rfl, rfl⟩

theorem pad_result (bits reversed output : BitString) :
    HasResult (BitRegister.run program (3 * reversed.length + 7) (state 68 bits reversed output))
      (if isPad bits then true :: reversed.reverse else [false]) := by
  cases bits with
  | nil =>
      exact result_after (pad_empty_one reversed output)
        (malformed_result [] reversed output) (by omega)
  | cons bit rest =>
      cases bit with
      | false =>
          cases rest with
          | nil =>
              have checked := reverse_result [] reversed []
              simp only [List.append_nil] at checked
              exact result_after (pad_good_four reversed output) checked (by omega)
          | cons bit rest =>
              exact result_after (pad_false_more_three bit rest reversed output)
                (malformed_result (bit :: rest) reversed output) (by omega)
      | true =>
          exact result_after (pad_true_one rest reversed output)
            (malformed_result (true :: rest) reversed output) (by omega)

def answer (mode : Mode) (bits reversed : BitString) : BitString :=
  match parseBits mode bits with
  | none => [false]
  | some payload => true :: (reversed.reverse ++ payload)

theorem answer_next (mode next : Mode) (first second : Bool) (rest reversed : BitString)
    (action : transition mode (CNFToken.ofBits first second) = .next next) :
    answer mode (first :: second :: rest) reversed =
      answer next rest ((emitted mode (CNFToken.ofBits first second)).reverse ++ reversed) := by
  simp only [answer, parseBits, action]
  cases parsed : parseBits next rest <;>
    simp only [Option.map_none, Option.map_some, List.reverse_append, List.reverse_reverse,
      List.append_assoc]

theorem answer_finish (mode : Mode) (first second : Bool) (rest reversed : BitString)
    (action : transition mode (CNFToken.ofBits first second) = .finish) :
    answer mode (first :: second :: rest) reversed =
      (if isPad rest then
        true :: ((emitted mode (CNFToken.ofBits first second)).reverse ++ reversed).reverse
       else [false]) := by
  simp only [answer, parseBits, action]
  cases pad : isPad rest <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.reverse_append, List.reverse_reverse]

theorem program_result (mode : Mode) (bits reversed output : BitString) :
    HasResult
      (BitRegister.run program (6 * bits.length + 3 * reversed.length + 16)
        (state (modeAddress mode) bits reversed output))
      (answer mode bits reversed) := by
  match bits with
  | [] =>
      exact result_after (empty_one mode reversed output) (malformed_result [] reversed output)
        (by simp only [List.length_nil]; omega)
  | [bit] =>
      exact result_after (singleton_three mode bit reversed output) (malformed_result [] reversed output)
        (by simp only [List.length_cons, List.length_nil]; omega)
  | first :: second :: rest =>
      cases action : transition mode (CNFToken.ofBits first second) with
      | invalid =>
          have invalid : answer mode (first :: second :: rest) reversed = [false] := by
            simp only [answer, parseBits, action]
          rw [invalid]
          exact result_after (invalid_four mode first second rest reversed output action)
            (malformed_result (second :: rest) reversed output)
            (by simp only [List.length_cons]; omega)
      | next next =>
          rw [answer_next mode next first second rest reversed action]
          exact result_after (next_six mode next first second rest reversed output action)
            (program_result next rest
              ((emitted mode (CNFToken.ofBits first second)).reverse ++ reversed) output)
            (by
              have short := emitted_length_le mode (CNFToken.ofBits first second)
              simp only [List.length_cons, List.length_append, List.length_reverse]
              omega)
      | finish =>
          rw [answer_finish mode first second rest reversed action]
          exact result_after (finish_six mode first second rest reversed output action)
            (pad_result rest ((emitted mode (CNFToken.ofBits first second)).reverse ++ reversed) output)
            (by
              have short := emitted_length_le mode (CNFToken.ofBits first second)
              simp only [List.length_cons, List.length_append, List.length_reverse]
              omega)
termination_by bits.length

theorem source_decodes (input : BitString) :
    HasResult (BitRegister.run program (6 * input.length + 16) (BitRegister.initial program input))
      (decodedData input) := by
  rw [initial_state]
  have checked := program_result .header input [] []
  have same : answer .header input [] = decodedData input := by
    unfold answer decodedData
    cases parseBits .header input <;> rfl
  change HasResult
    (BitRegister.run program (6 * input.length + 16) (state (modeAddress .header) input [] []))
    (answer .header input []) at checked
  rw [same] at checked
  exact checked

theorem source_accepts (input : BitString) :
    (BitRegister.run program (6 * input.length + 16) (BitRegister.initial program input)).control =
      .accepted := (source_decodes input).1

theorem source_output (input : BitString) :
    (BitRegister.run program (6 * input.length + 16) (BitRegister.initial program input)).store.get 2 =
      resultData (decodeEncodedCNF input) :=
  (source_decodes input).2.trans (decodedData_eq_result input)

end PNP.Concrete.CNFRegisterDecoder
