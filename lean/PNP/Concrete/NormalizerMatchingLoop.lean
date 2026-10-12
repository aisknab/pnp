/-
Copyright (c) 2026 PNP Labs.

Complete outer matching loop. Termination is proved for every raw register
state by the internally consumed countdown. On canonical data, the literal
loop follows the full source recurrence, including immediate terminal return.
-/
import PNP.Concrete.NormalizerMatchingStep

namespace PNP.Concrete.NormalizerBlocks.MatchingDriver
open BitRegister

theorem State.get_remaining (r : State) :
    r.store.get (Frame.frameIndex 29 (3 : Fin 4)) = r.remaining := by
  rw [State.store, Frame.get_frame]
  rfl
structure ScanResult where
  fuel : Nat
  state : State
def loop : Block 33 := .loop (Frame.frameIndex 29 (3 : Fin 4)) body
def scan : Nat → State → ScanResult
  | 0, r => ⟨1,r⟩
  | fuel + 1, r =>
      match r.remaining with
      | [] => ⟨1,r⟩
      | _ :: _ =>
          let next := scan fuel (bodyResult r)
          ⟨1 + (bodyFuel r + next.fuel), next.state⟩
theorem scan_empty (fuel : Nat) (r : State) (empty : r.remaining = []) : scan fuel r = ⟨1,r⟩ := by
  cases fuel <;> simp only [scan, empty]
theorem scan_step (fuel : Nat) (r : State) (nonempty : r.remaining ≠ []) :
    scan (fuel + 1) r =
      ⟨1 + (bodyFuel r + (scan fuel (bodyResult r)).fuel), (scan fuel (bodyResult r)).state⟩ := by
  cases remaining : r.remaining with
  | nil => exact False.elim (nonempty remaining)
  | cons bit rest => simp only [scan, remaining]
theorem scan_exec (fuel : Nat) (r : State) (enough : r.remaining.length < fuel ∨ r.remaining = []) :
    Exec loop r.store (scan fuel r).fuel (scan fuel r).state.store := by
  induction fuel generalizing r with
  | zero =>
      have empty := enough.resolve_left (Nat.not_lt_zero _)
      exact Exec.loopStop ((State.get_remaining r).trans empty)
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil =>
          simpa only [loop, scan, remaining] using
            (Exec.loopStop (source := Frame.frameIndex 29 (3 : Fin 4)) (body := body)
              (store := r.store) ((State.get_remaining r).trans remaining))
      | cons bit rest =>
          have nonempty : r.remaining ≠ [] := by rw [remaining]; intro h; cases h
          have size : r.remaining.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => exact False.elim (nonempty h)
          have smaller := Nat.lt_of_lt_of_le (body_shorter r nonempty) size
          simpa only [loop, scan, remaining] using
            Exec.loopStep (source := Frame.frameIndex 29 (3 : Fin 4)) (body := body) (before := r.store)
              ((State.get_remaining r).trans remaining) (body_exec r) (ih (bodyResult r) (Or.inl smaller))
theorem scan_stopped (fuel : Nat) (r : State) (enough : r.remaining.length < fuel ∨ r.remaining = []) :
    (scan fuel r).state.remaining = [] := by
  induction fuel generalizing r with
  | zero => exact enough.resolve_left (Nat.not_lt_zero _)
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil => simp only [scan, remaining]
      | cons bit rest =>
          have nonempty : r.remaining ≠ [] := by rw [remaining]; intro h; cases h
          have size : r.remaining.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => exact False.elim (nonempty h)
          have smaller := Nat.lt_of_lt_of_le (body_shorter r nonempty) size
          simpa only [scan, remaining] using ih (bodyResult r) (Or.inl smaller)

theorem scan_frame (fuel : Nat) (r : State) :
    (scan fuel r).state.width = r.width ∧ (scan fuel r).state.formula = r.formula := by
  induction fuel generalizing r with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil => simp only [scan, remaining]; trivial
      | cons bit rest =>
          have first := body_frame r
          have next := ih (bodyResult r)
          simp only [scan, remaining]
          exact ⟨next.1.trans first.1, next.2.trans first.2⟩

def whole (r : State) : ScanResult := scan (r.remaining.length + 1) r
theorem whole_exec (r : State) : Exec loop r.store (whole r).fuel (whole r).state.store :=
  scan_exec _ r (Or.inl (Nat.lt_succ_self _))
theorem whole_stopped (r : State) : (whole r).state.remaining = [] :=
  scan_stopped _ r (Or.inl (Nat.lt_succ_self _))

theorem scan_value (fuel variables : Nat) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (r : State) (data : Canonical variables clauses entries r)
    (enough : r.remaining.length < fuel) :
    (scan fuel r).state.table = MatchingTable.encode (MatchingLoop.finish variables clauses r.remaining.length entries) := by
  induction fuel generalizing entries r with
  | zero => exact False.elim (Nat.not_lt_zero _ enough)
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil =>
          simp only [scan, remaining, List.length_nil, MatchingLoop.finish]
          exact data.table
      | cons bit rest =>
          have nonempty : r.remaining ≠ [] := by rw [remaining]; intro h; cases h
          rw [scan_step fuel r nonempty, List.length_cons, MatchingLoop.finish]
          cases search : Search.value variables clauses entries with
          | terminal trace =>
              have stopped := body_terminal variables clauses entries r data trace search
              rw [scan_empty fuel (bodyResult r) stopped.1]
              exact stopped.2.trans data.table
          | augment index path =>
              have next := body_augment variables clauses entries r data index path search
              have smaller : (bodyResult r).remaining.length < fuel := by
                rw [next.1, remaining, List.tail_cons]
                rw [remaining, List.length_cons] at enough
                omega
              have checked := ih (MatchingTable.writeAll entries (PathPairs.value path)) (bodyResult r) next.2 smaller
              simpa only [next.1, remaining, List.tail_cons] using checked

theorem whole_value (variables : Nat) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (r : State) (data : Canonical variables clauses entries r) :
    (whole r).state.table = MatchingTable.encode (MatchingLoop.finish variables clauses r.remaining.length entries) :=
  scan_value _ variables clauses entries r data (Nat.lt_succ_self _)

end PNP.Concrete.NormalizerBlocks.MatchingDriver
