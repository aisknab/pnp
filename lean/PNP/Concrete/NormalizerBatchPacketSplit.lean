/-
Copyright (c) 2026 PNP Labs.

Finite length-delimited packet splitting for the table-update driver. The
counter is read by the existing header machine. Each iteration consumes one
counter bit and one input bit, or stops at truncated input.
-/

import PNP.Concrete.NormalizerBatchCanonical
import PNP.Concrete.NormalizerTableInitializationCanonical

namespace PNP.Concrete.NormalizerBlocks.BatchPacket

open BitRegister Occurrence

def takeStep : Block 9 :=
  .branch 0 (.action (.clear 1))
    (.seq (.action (.pop 0)) (.seq (.action (.pop 1)) (.action (.push 3 false))))
    (.seq (.action (.pop 0)) (.seq (.action (.pop 1)) (.action (.push 3 true))))

def takeLoop : Block 9 := .loop 1 takeStep

def takeResult : BitString → Registers → Result
  | [], r => ⟨1, {r with target := []}⟩
  | _ :: rest, r =>
      match r.input with
      | [] => ⟨4, {r with target := []}⟩
      | bit :: tail =>
          let next := takeResult rest {r with input := tail, excess := bit :: r.excess}
          ⟨1 + (4 + next.fuel), next.state⟩

theorem take_exec (counter : BitString) (r : Registers) :
    Exec takeLoop ({r with target := counter}).store (takeResult counter r).fuel
      (takeResult counter r).state.store := by
  cases r with
  | mk input target remaining excess sign mode active reserved output =>
      induction counter generalizing input excess with
      | nil => exact Exec.loopStop rfl
      | cons tick rest ih =>
          cases input with
          | nil =>
              exact Exec.loopStep (source := (1 : Fin 9)) (body := takeStep)
                (before := Registers.store ⟨[], tick :: rest, remaining, excess, sign, mode, active, reserved, output⟩)
                rfl (Exec.empty (source := (0 : Fin 9)) rfl (.action _ _)) (Exec.loopStop rfl)
          | cons bit tail =>
              have step : Exec takeStep
                  (Registers.store ⟨bit :: tail, tick :: rest, remaining, excess, sign, mode, active, reserved, output⟩) 4
                  (Registers.store ⟨tail, rest, remaining, bit :: excess, sign, mode, active, reserved, output⟩) := by
                cases bit
                · exact Exec.zero (source := (0 : Fin 9)) rfl
                    (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
                · exact Exec.one (source := (0 : Fin 9)) rfl
                    (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
              exact Exec.loopStep (source := (1 : Fin 9)) (body := takeStep)
                (before := Registers.store ⟨bit :: tail, tick :: rest, remaining, excess, sign, mode, active, reserved, output⟩)
                rfl step (ih tail (bit :: excess))

theorem take_fuel_bound (counter : BitString) (r : Registers) :
    (takeResult counter r).fuel ≤ 5 * counter.length + 4 := by
  induction counter generalizing r with
  | nil => change 1 ≤ 4; decide
  | cons tick rest ih =>
      cases input : r.input with
      | nil => simp only [takeResult, input, List.length_cons]; omega
      | cons bit tail =>
          have next := ih {r with input := tail, excess := bit :: r.excess}
          simp only [takeResult, input, List.length_cons]
          omega

theorem take_size (counter : BitString) (r : Registers) :
    (takeResult counter r).state.excess.length + (takeResult counter r).state.input.length ≤
      r.excess.length + r.input.length := by
  induction counter generalizing r with
  | nil => exact Nat.le_refl _
  | cons tick rest ih =>
      cases input : r.input with
      | nil => simp only [takeResult, input]; exact Nat.le_refl _
      | cons bit tail =>
          have next : (takeResult rest {r with input := tail, excess := bit :: r.excess}).state.excess.length +
              (takeResult rest {r with input := tail, excess := bit :: r.excess}).state.input.length ≤
                (bit :: r.excess).length + tail.length := ih _
          simp only [takeResult, input, List.length_cons]
          simp only [List.length_cons] at next
          omega

theorem take_canonical (data suffix : BitString) (r : Registers) :
    (takeResult (List.replicate data.length true) {r with input := data ++ suffix}).state =
      {r with input := suffix, target := [], excess := data.reverse ++ r.excess} := by
  induction data generalizing r with
  | nil => rfl
  | cons bit rest ih =>
      simpa only [List.length_cons, List.replicate_succ, List.cons_append, takeResult,
        List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using
        ih {r with excess := bit :: r.excess}

end PNP.Concrete.NormalizerBlocks.BatchPacket
