/-
Copyright (c) 2026 PNP Labs.

Exact marker readers used at circuit headers and boundaries. Malformed and
truncated input is handled by the same finite code, with bounded execution.
-/

import PNP.Concrete.NANDFrontendSource

namespace PNP.Concrete.NANDFrontend

open BitRegister

def expectTree : BitString → Nat → Nat → ReadTree
  | [], next, _ => .leaf next
  | false :: rest, next, failure => .branch (expectTree rest next failure) (.leaf failure)
  | true :: rest, next, failure => .branch (.leaf failure) (expectTree rest next failure)

structure MatchResult where
  fuel : Nat
  rest : BitString
  valid : Bool
deriving Repr

def matchScan : BitString → BitString → MatchResult
  | [], input => ⟨0, input, true⟩
  | _ :: _, [] => ⟨1, [], false⟩
  | false :: expected, false :: input
  | true :: expected, true :: input =>
      let result := matchScan expected input
      {result with fuel := 2 + result.fuel}
  | _ :: _, _ :: input => ⟨2, input, false⟩

theorem expectTree_size (expected : BitString) (next failure : Nat) :
    (expectTree expected next failure).size = 3 * expected.length := by
  induction expected with
  | nil => rfl
  | cons bit rest ih =>
      cases bit <;> simp only [expectTree, ReadTree.size, List.length_cons, ih] <;> omega

theorem expectTree_depth (expected : BitString) (next failure : Nat) :
    (expectTree expected next failure).depth = expected.length := by
  induction expected with
  | nil => rfl
  | cons bit rest ih =>
      cases bit <;> simp only [expectTree, ReadTree.depth, List.length_cons, ih] <;> omega

theorem expectTree_scan (expected input : BitString) (next failure : Nat) :
    (expectTree expected next failure).scan failure input =
      ⟨(matchScan expected input).fuel, (matchScan expected input).rest,
        readerExit (matchScan expected input).valid next failure⟩ := by
  induction expected generalizing input with
  | nil => simp only [expectTree, ReadTree.scan, matchScan, readerExit]
  | cons bit rest ih =>
      cases input with
      | nil => cases bit <;> simp only [expectTree, ReadTree.scan, matchScan, readerExit]
      | cons actual tail =>
          cases bit <;> cases actual <;>
            simp only [expectTree, ReadTree.scan, matchScan, readerExit,
              Bool.false_eq_true, ↓reduceIte, ih]

theorem expect_run (program : Program 9) (base next failure : Nat)
    (expected input : BitString) (r : Registers)
    (placed : Segment program base ((expectTree expected next failure).code base failure)) :
    BitRegister.run program (matchScan expected input).fuel
        (({r with input := input}).state ((expectTree expected next failure).entry base)) =
      ({r with input := (matchScan expected input).rest}).state
        (readerExit (matchScan expected input).valid next failure) := by
  have h := ReadTree.run program (expectTree expected next failure) base failure r input placed
  rw [expectTree_scan] at h
  exact h

theorem matchScan_bounds (expected input : BitString) :
    (matchScan expected input).fuel ≤ 2 * expected.length ∧
      (matchScan expected input).rest.length ≤ input.length := by
  have hf := ReadTree.scan_fuel_le (expectTree expected 0 1) 1 input
  have hr := ReadTree.scan_rest_le (expectTree expected 0 1) 1 input
  rw [expectTree_scan, expectTree_depth] at hf
  rw [expectTree_scan] at hr
  exact ⟨hf, hr⟩

theorem matchScan_prefix (expected suffix : BitString) :
    matchScan expected (expected ++ suffix) = ⟨2 * expected.length, suffix, true⟩ := by
  induction expected with
  | nil => rfl
  | cons bit rest ih =>
      cases bit <;> simp only [List.cons_append, matchScan, ih, List.length_cons] <;>
        congr 1 <;> omega

theorem matchScan_success (expected input : BitString) (nonempty : expected ≠ [])
    (valid : (matchScan expected input).valid = true) :
    (matchScan expected input).rest.length < input.length := by
  cases expected with
  | nil => exact False.elim (nonempty rfl)
  | cons bit rest =>
      cases input with
      | nil => cases bit <;> cases valid
      | cons actual tail =>
          have h := (matchScan_bounds rest tail).2
          cases bit <;> cases actual <;>
            simp only [matchScan, List.length_cons] at valid ⊢
          all_goals first | omega | cases valid

def markerCode (base : Nat) (token : LockedNAND.Token) (next failure : Nat) : List (Instruction 9) :=
  (expectTree token.bits next failure).code base failure

theorem markerCode_length (base : Nat) (token : LockedNAND.Token) (next failure : Nat) :
    (markerCode base token next failure).length = 12 := by
  rw [markerCode, ReadTree.code_length, expectTree_size]
  cases token <;> rfl

theorem marker_run (program : Program 9) (base : Nat) (token : LockedNAND.Token)
    (next failure : Nat) (r : Registers) (input : BitString)
    (placed : Segment program base (markerCode base token next failure)) :
    BitRegister.run program (matchScan token.bits input).fuel
        (({r with input := input}).state base) =
      ({r with input := (matchScan token.bits input).rest}).state
        (readerExit (matchScan token.bits input).valid next failure) := by
  have h := expect_run program base next failure token.bits input r placed
  have entry : (expectTree token.bits next failure).entry base = base := by cases token <;> rfl
  rw [entry] at h
  exact h

theorem marker_canonical (program : Program 9) (base : Nat) (token : LockedNAND.Token)
    (next failure : Nat) (r : Registers) (suffix : BitString)
    (placed : Segment program base (markerCode base token next failure)) :
    BitRegister.run program 8 (({r with input := token.bits ++ suffix}).state base) =
      ({r with input := suffix}).state next := by
  have h := marker_run program base token next failure r (token.bits ++ suffix) placed
  rw [matchScan_prefix] at h
  have width : token.bits.length = 4 := by cases token <;> rfl
  rw [width] at h
  exact h

end PNP.Concrete.NANDFrontend
