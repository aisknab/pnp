/-
Copyright (c) 2026 PNP Labs.

Total true-pair scanning. Every live iteration consumes two bits or stops,
including truncated and malformed values. The unary result theorem covers
every value and arbitrary trailing data, not a collection of fixed examples.
-/

import PNP.Concrete.NormalizerMatchingValueOperations

namespace PNP.Concrete.NormalizerBlocks.MatchingValue

open BitRegister Occurrence

def loop : Block 9 := .loop 6 pair

def scan (input : BitString) (r : Registers) : Result :=
  match input with
  | [] => ⟨4, {r with input := [], active := []}⟩
  | false :: rest => ⟨4, {r with input := false :: rest, active := []}⟩
  | [true] => ⟨6, {r with input := [], active := []}⟩
  | true :: false :: rest => ⟨6, {r with input := false :: rest, active := []}⟩
  | true :: true :: rest =>
      let tail := scan rest {r with output := true :: r.output}
      ⟨6 + tail.fuel, tail.state⟩
termination_by structural input

theorem scan_exec (input : BitString) (r : Registers) :
    Exec loop ({r with input := input, active := [true]}).store (scan input r).fuel (scan input r).state.store := by
  match input with
  | [] =>
      exact Exec.loopStep (source := (6 : Fin 9)) (body := pair)
        (before := ({r with input := [], active := [true]}).store)
        rfl (pair_empty_exec {r with active := [true]}) (Exec.loopStop rfl)
  | false :: rest =>
      exact Exec.loopStep (source := (6 : Fin 9)) (body := pair)
        (before := ({r with input := false :: rest, active := [true]}).store)
        rfl (pair_false_exec {r with active := [true]} rest) (Exec.loopStop rfl)
  | [true] =>
      exact Exec.loopStep (source := (6 : Fin 9)) (body := pair)
        (before := ({r with input := [true], active := [true]}).store)
        rfl (pair_true_empty_exec {r with active := [true]}) (Exec.loopStop rfl)
  | true :: false :: rest =>
      exact Exec.loopStep (source := (6 : Fin 9)) (body := pair)
        (before := ({r with input := true :: false :: rest, active := [true]}).store)
        rfl (pair_true_false_exec {r with active := [true]} rest) (Exec.loopStop rfl)
  | true :: true :: rest =>
      have tail := scan_exec rest {r with output := true :: r.output}
      have checked := Exec.loopStep (source := (6 : Fin 9)) (body := pair)
        (before := ({r with input := true :: true :: rest, active := [true]}).store)
        rfl (pair_true_true_exec {r with active := [true]} rest) tail
      have cost : 6 + (scan rest {r with output := true :: r.output}).fuel =
          1 + (5 + (scan rest {r with output := true :: r.output}).fuel) := by omega
      change Exec loop _ (6 + (scan rest {r with output := true :: r.output}).fuel) _
      rw [cost]
      exact checked
termination_by input.length

theorem scan_fuel_bound (input : BitString) (r : Registers) :
    (scan input r).fuel ≤ 3 * input.length + 6 := by
  match input with
  | [] => change 4 ≤ 6; decide
  | false :: rest => simp only [scan, List.length_cons]; omega
  | [true] => change 6 ≤ 9; decide
  | true :: false :: rest => simp only [scan, List.length_cons]; omega
  | true :: true :: rest =>
      have tail := scan_fuel_bound rest {r with output := true :: r.output}
      simp only [scan, List.length_cons]
      omega
termination_by input.length

theorem scan_stopped (input : BitString) (r : Registers) : (scan input r).state.active = [] := by
  match input with
  | [] | false :: _ | [true] | true :: false :: _ => rfl
  | true :: true :: rest => exact scan_stopped rest {r with output := true :: r.output}
termination_by input.length

theorem scan_true_pairs (count : Nat) (tail : BitString) (r : Registers) :
    (scan (List.replicate (2 * count) true ++ false :: tail) r).state.output =
      List.replicate count true ++ r.output := by
  induction count generalizing r with
  | zero => rfl
  | succ count ih =>
      rw [NANDFrontend.twiceUnary_succ]
      simpa only [List.cons_append, scan, List.replicate_succ',
        List.append_assoc, List.cons_append, List.nil_append] using
        ih {r with output := true :: r.output}

end PNP.Concrete.NormalizerBlocks.MatchingValue
