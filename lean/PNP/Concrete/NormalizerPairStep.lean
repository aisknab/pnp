/-
Copyright (c) 2026 PNP Labs.

A total augmentation-pair step. Invalid vertex kinds stop immediately.
Every nonempty raw cursor strictly shrinks; pair size and step runtime are
bounded by that cursor, independently of accumulated output.
-/
import PNP.Concrete.NormalizerPairEmission

namespace PNP.Concrete.NormalizerBlocks.PathPairs
open BitRegister

def stop : Block 12 := .action (.clear 9)
def stopped (r : State) : State := {r with pending := []}
theorem stop_exec (r : State) : Exec stop r.store 1 (stopped r).store := .action _ _

def chooseSecond : Block 12 := .branch 0 stop stop processPair
def secondChosen (r : State) : State := if ForwardEdge.present r.core.input then pairProcessed r else stopped r
def chooseFuel (r : State) : Nat := 1 + if ForwardEdge.present r.core.input then processFuel r else 1
theorem chooseSecond_exec (r : State) :
    Exec chooseSecond r.store (chooseFuel r) (secondChosen r).store := by
  have checked := EdgeKinds.branch_head (0 : Fin 12) r.store stop processPair 1 (processFuel r)
    (stopped r).store (pairProcessed r).store (stop_exec r) (processPair_exec r)
  change Exec chooseSecond r.store (chooseFuel r)
    (if ForwardEdge.present r.core.input then (pairProcessed r).store else (stopped r).store) at checked
  cases tag : ForwardEdge.present r.core.input <;>
    simpa only [secondChosen, tag, Bool.false_eq_true, ite_false, ite_true] using checked

def processFirst : Block 12 := .seq readFirst chooseSecond
def firstProcessed (r : State) : State := secondChosen (firstRead r)
def firstProcessFuel (r : State) : Nat := firstFuel r + chooseFuel (firstRead r)
theorem processFirst_exec (r : State) :
    Exec processFirst r.store (firstProcessFuel r) (firstProcessed r).store :=
  Exec.seq (readFirst_exec r) (chooseSecond_exec (firstRead r))

def body : Block 12 := .branch 9 stop processFirst stop
def bodyResult (r : State) : State :=
  match r.pending with
  | false :: _ => firstProcessed r
  | _ => stopped r
def bodyFuel (r : State) : Nat :=
  1 + match r.pending with
  | false :: _ => firstProcessFuel r
  | _ => 1
theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (bodyResult r).store := by
  cases pending : r.pending with
  | nil =>
      simpa only [body, bodyFuel, bodyResult, pending] using
        (Exec.empty (source := (9 : Fin 12)) (before := r.store) (zero := processFirst) (one := stop) pending (stop_exec r))
  | cons bit rest =>
      cases bit with
      | false =>
          simpa only [body, bodyFuel, bodyResult, pending] using
            (Exec.zero (source := (9 : Fin 12)) (before := r.store) (empty := stop) (one := stop) pending (processFirst_exec r))
      | true =>
          simpa only [body, bodyFuel, bodyResult, pending] using
            (Exec.one (source := (9 : Fin 12)) (before := r.store) (empty := stop) (zero := processFirst) pending (stop_exec r))

theorem first_input_bound (r : State) : (firstRead r).core.input.length ≤ r.pending.tail.length :=
  Occurrence.header_input_bound r.pending.tail (TableInit.seeded r.pending.tail)
theorem second_pending_bound (r : State) : (secondRead r).pending.length ≤ r.core.input.tail.length :=
  Occurrence.header_input_bound r.core.input.tail (TableInit.seeded r.core.input.tail)

theorem body_pending_bound (r : State) : (bodyResult r).pending.length ≤ r.pending.tail.length := by
  cases pending : r.pending with
  | nil => simp only [bodyResult, pending, stopped, List.length_nil]; exact Nat.zero_le _
  | cons bit rest =>
      cases bit with
      | true => simp only [bodyResult, pending, stopped, List.length_nil]; exact Nat.zero_le _
      | false =>
          cases tag : ForwardEdge.present (firstRead r).core.input with
          | false =>
              simp only [bodyResult, pending, firstProcessed, secondChosen, tag, Bool.false_eq_true, ite_false, stopped, List.length_nil]
              exact Nat.zero_le _
          | true =>
              have first := first_input_bound r
              have second := second_pending_bound (firstRead r)
              have suffix := ParentQuery.input_tail_bound (firstRead r).core.input
              simp only [bodyResult, pending, firstProcessed, secondChosen, tag, ite_true]
              change (secondRead (firstRead r)).pending.length ≤ _
              rw [pending] at first
              omega

theorem body_shorter (r : State) (nonempty : r.pending ≠ []) :
    (bodyResult r).pending.length < r.pending.length := by
  have bound := body_pending_bound r
  cases pending : r.pending with
  | nil => exact False.elim (nonempty pending)
  | cons bit rest => simp only [pending, List.tail_cons, List.length_cons] at bound ⊢; omega

theorem processFuel_first_bound (r : State) : processFuel (firstRead r) ≤ 34 * r.pending.length + 60 := by
  have first := first_input_bound r
  have tail := ParentQuery.input_tail_bound r.pending
  have secondTail := ParentQuery.input_tail_bound (firstRead r).core.input
  have header := TableInit.headerFuel_bound (firstRead r).core.input.tail
  have firstCount := TableInit.count_length_bound r.pending.tail
  have secondCount := TableInit.count_length_bound (firstRead r).core.input.tail
  change (firstRead r).firstIndex.length ≤ 5 * r.pending.tail.length + 6 at firstCount
  change (secondRead (firstRead r)).core.target.length ≤ 5 * (firstRead r).core.input.tail.length + 6 at secondCount
  change (10 + TableInit.headerFuel (firstRead r).core.input.tail) +
    (3 * (secondRead (firstRead r)).core.target.length + 3 * (firstRead r).firstIndex.length + 8) ≤ _
  omega

theorem bodyFuel_bound (r : State) : bodyFuel r ≤ 64 * r.pending.length + 128 := by
  have first := TableInit.headerFuel_bound r.pending.tail
  have tail := ParentQuery.input_tail_bound r.pending
  have second := processFuel_first_bound r
  cases pending : r.pending with
  | nil => simp only [bodyFuel, pending]; omega
  | cons bit rest =>
      cases bit with
      | true => simp only [bodyFuel, pending]; omega
      | false =>
          rw [pending] at first tail second
          cases tag : ForwardEdge.present (firstRead r).core.input <;>
            simp only [bodyFuel, pending, firstProcessFuel, firstFuel, chooseFuel, tag,
              Bool.false_eq_true, ite_false, ite_true] <;> omega

def stepBound (r : State) : Nat := 64 * r.pending.length + 128
theorem stepBound_mono (r : State) (nonempty : r.pending ≠ []) :
    stepBound (bodyResult r) ≤ stepBound r := by
  have shorter := body_shorter r nonempty
  unfold stepBound
  omega

end PNP.Concrete.NormalizerBlocks.PathPairs
