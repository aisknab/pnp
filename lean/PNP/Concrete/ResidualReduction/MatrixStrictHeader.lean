import PNP.Concrete.ResidualReduction.MatrixInputEncoding

/-! A strict literal unary header reader. Unlike an EOF-tolerant occurrence
header, this routine records whether the required zero terminator was actually
read. Its execution and linear source cost cover every input bitstring. -/

namespace PNP.Concrete.ResidualReduction.MatrixStrictHeader
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec

structure Header where
  count : Nat
  rest : BitString
  terminated : Bool

def scan : BitString → Header
  | [] => ⟨0, [], false⟩
  | false :: rest => ⟨0, rest, true⟩
  | true :: rest =>
    let h := scan rest
    ⟨h.count + 1, h.rest, h.terminated⟩

theorem replicate_push (count : Nat) (bit : Bool) (suffix : BitString) :
    List.replicate count bit ++ bit :: suffix =
      List.replicate (count + 1) bit ++ suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons bit) ih

theorem replicate_add (left right : Nat) (bit : Bool) :
    List.replicate left bit ++ List.replicate right bit = List.replicate (left + right) bit := by
  induction left with
  | zero => rw [Nat.zero_add]; rfl
  | succ left ih =>
    simpa only [List.replicate_succ, List.cons_append, Nat.succ_add] using
      congrArg (List.cons bit) ih

theorem scan_canonical (count : Nat) (suffix : BitString) :
    scan (natural count ++ suffix) = ⟨count, suffix, true⟩ := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change scan (true :: (natural count ++ suffix)) = _
    simp only [scan, ih]

theorem scan_parse (input : BitString) :
    BitString.decodeLength input =
      if (scan input).terminated then some ((scan input).count, (scan input).rest) else none := by
  induction input with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | false => rfl
    | true =>
      simp only [BitString.decodeLength, scan, ih]
      cases h : (scan rest).terminated <;> rfl

theorem scan_size (input : BitString) :
    (scan input).count + (scan input).rest.length ≤ input.length := by
  induction input with
  | nil => exact Nat.le_refl 0
  | cons b rest ih =>
    cases b <;> simp only [scan, List.length_cons] <;> omega

def body : Block 9 :=
  .branch 0 (.action (.clear 6))
    (.seq (.action (.pop 0)) (.seq (.action (.push 4 true)) (.action (.clear 6))))
    (.seq (.action (.pop 0)) (.action (.push 1 true)))
def loop : Block 9 := .loop 6 body

def fuel : BitString → Nat
  | [] => 4
  | false :: _ => 6
  | true :: rest => 4 + fuel rest

def seeded (input : BitString) (r : Registers) : Registers :=
  {r with input := input, sign := [], active := [true]}
def result (input : BitString) (r : Registers) : Registers :=
  {r with input := (scan input).rest, target := List.replicate (scan input).count true ++ r.target, sign := if (scan input).terminated then [true] else [], active := []}

theorem loop_exec (input : BitString) (r : Registers) :
    Exec loop (seeded input r).store (fuel input) (result input r).store := by
  induction input generalizing r with
  | nil =>
    have step : Exec body (seeded [] r).store 2 ({r with input := [], sign := [], active := []}).store :=
      Exec.empty rfl (.action _ _)
    exact Exec.loopStep (source := (6 : Fin 9)) rfl step (Exec.loopStop rfl)
  | cons b rest ih =>
    cases b with
    | false =>
      have step : Exec body (seeded (false :: rest) r).store 4
          ({r with input := rest, sign := [true], active := []}).store :=
        Exec.zero rfl (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
      exact Exec.loopStep (source := (6 : Fin 9)) rfl step (Exec.loopStop rfl)
    | true =>
      have step : Exec body (seeded (true :: rest) r).store 3
          (seeded rest {r with target := true :: r.target}).store :=
        Exec.one rfl (Exec.seq (.action _ _) (.action _ _))
      have checked := Exec.loopStep (source := (6 : Fin 9)) rfl step
        (ih {r with target := true :: r.target})
      have cost : fuel (true :: rest) = 1 + (3 + fuel rest) := by simp only [fuel]; omega
      rw [cost]
      have state : result rest {r with target := true :: r.target} =
          result (true :: rest) r := by
        cases flag : (scan rest).terminated <;>
          simp only [result, scan, replicate_push, flag] <;> rfl
      rw [state] at checked
      exact checked

theorem fuel_bound (input : BitString) : fuel input ≤ 4 * input.length + 6 := by
  induction input with
  | nil => exact Nat.le_trans (by decide : 4 ≤ 6) (Nat.le_refl 6)
  | cons b rest ih => cases b <;> simp only [fuel, List.length_cons] <;> omega

def seed : Block 9 :=
  .seq (.action (.clear 4)) (.seq (.action (.clear 6)) (.action (.push 6 true)))
def block : Block 9 := .seq seed loop
def blockFuel (input : BitString) : Nat := 3 + fuel input

theorem block_exec (input : BitString) (r : Registers) :
    Exec block ({r with input := input}).store (blockFuel input) (result input r).store := by
  have first : Exec seed ({r with input := input}).store 3 (seeded input r).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  exact Exec.seq first (loop_exec input r)

theorem blockFuel_bound (input : BitString) : blockFuel input ≤ 4 * input.length + 9 := by
  have bound := fuel_bound input
  unfold blockFuel
  omega

end PNP.Concrete.ResidualReduction.MatrixStrictHeader
