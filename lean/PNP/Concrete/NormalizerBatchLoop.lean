/-
Copyright (c) 2026 PNP Labs.

Uniform repeated table updates by one fixed finite loop. Pending input strictly
shrinks, including malformed headers. An additive table bound is propagated
through all iterations, giving a shared polynomial source-step budget rather
than iterating a per-call polynomial without a size invariant.
-/

import PNP.Concrete.NormalizerBatchBody

namespace PNP.Concrete.NormalizerBlocks.TableBatch

open BitRegister

structure Result where
  fuel : Nat
  state : State
deriving Repr

def loop : Block 11 := .loop 9 body

def run : Nat → State → Result
  | 0, r => ⟨1, r⟩
  | fuel + 1, r =>
      match r.pending with
      | [] => ⟨1, r⟩
      | _ :: _ =>
          let tail := run fuel (result r)
          ⟨1 + (bodyFuel r + tail.fuel), tail.state⟩

theorem run_exec (fuel : Nat) (r : State)
    (enough : r.pending.length < fuel ∨ r.pending = []) :
    Exec loop r.store (run fuel r).fuel (run fuel r).state.store := by
  induction fuel generalizing r with
  | zero =>
      have stopped := enough.resolve_left (Nat.not_lt_zero _)
      exact Exec.loopStop stopped
  | succ fuel ih =>
      cases pending : r.pending with
      | nil =>
          simpa only [run, pending, loop] using
            (Exec.loopStop (source := (9 : Fin 11)) (body := body) (store := r.store) pending)
      | cons bit rest =>
          have nonempty : r.pending ≠ [] := by rw [pending]; intro bad; cases bad
          have length : r.pending.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => exact False.elim (nonempty h)
          have smaller := pending_strict r nonempty
          have tail := ih (result r) (Or.inl (Nat.lt_of_lt_of_le smaller length))
          simpa only [loop, run, pending] using
            Exec.loopStep (source := (9 : Fin 11)) (body := body) (before := r.store)
              pending (body_exec r) tail

theorem run_stopped (fuel : Nat) (r : State)
    (enough : r.pending.length < fuel ∨ r.pending = []) : (run fuel r).state.pending = [] := by
  induction fuel generalizing r with
  | zero => exact enough.resolve_left (Nat.not_lt_zero _)
  | succ fuel ih =>
      cases pending : r.pending with
      | nil => simp only [run, pending]
      | cons bit rest =>
          have nonempty : r.pending ≠ [] := by rw [pending]; intro bad; cases bad
          have length : r.pending.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => exact False.elim (nonempty h)
          have smaller := pending_strict r nonempty
          simpa only [run, pending] using ih (result r) (Or.inl (Nat.lt_of_lt_of_le smaller length))

theorem costBound_mono {pending pending' table table' : Nat}
    (hp : pending ≤ pending') (ht : table ≤ table') :
    costBound pending table ≤ costBound pending' table' := by
  have first : 36 * pending + 82 ≤ 36 * pending' + 82 := by omega
  have second : table + 1 ≤ table' + 1 := by omega
  have product := Nat.mul_le_mul first second
  simp only [costBound]
  omega

theorem run_bounds (fuel : Nat) (r : State) (pendingBound tableBound : Nat)
    (pendingSmall : r.pending.length ≤ pendingBound)
    (capacity : r.table.length + (18 * pendingBound + 40) * fuel ≤ tableBound) :
    (run fuel r).state.table.length ≤ tableBound ∧
      (run fuel r).fuel ≤ (costBound pendingBound tableBound + 1) * fuel + 1 := by
  induction fuel generalizing r with
  | zero =>
      simp only [run, Nat.mul_zero, Nat.add_zero] at *
      exact ⟨capacity, Nat.le_refl _⟩
  | succ fuel ih =>
      cases pending : r.pending with
      | nil =>
          simp only [run, pending]
          constructor <;> omega
      | cons bit rest =>
          have nextPending := Nat.le_trans (pending_bound r) pendingSmall
          have grows := table_growth r
          have nextCapacity :
              (result r).table.length + (18 * pendingBound + 40) * fuel ≤ tableBound := by
            rw [Nat.mul_succ] at capacity
            omega
          have tail := ih (result r) nextPending nextCapacity
          have tableSmall : r.table.length ≤ tableBound := by omega
          have current := Nat.le_trans (bodyFuel_bound r) (costBound_mono pendingSmall tableSmall)
          simp only [run, pending, Nat.mul_succ]
          exact ⟨tail.1, by omega⟩

def whole (r : State) : Result := run (r.pending.length + 1) r
def tableBound (pending table : Nat) : Nat := table + (18 * pending + 40) * (pending + 1)
def totalCostBound (pending table : Nat) : Nat :=
  (costBound pending (tableBound pending table) + 1) * (pending + 1) + 1

theorem whole_exec (r : State) :
    Exec loop r.store (whole r).fuel (whole r).state.store :=
  run_exec _ r (Or.inl (Nat.lt_succ_self _))

theorem whole_stopped (r : State) : (whole r).state.pending = [] :=
  run_stopped _ r (Or.inl (Nat.lt_succ_self _))

theorem whole_bounds (r : State) :
    (whole r).state.table.length ≤ tableBound r.pending.length r.table.length ∧
      (whole r).fuel ≤ totalCostBound r.pending.length r.table.length :=
  run_bounds _ r r.pending.length (tableBound r.pending.length r.table.length)
    (Nat.le_refl _) (Nat.le_refl _)

end PNP.Concrete.NormalizerBlocks.TableBatch
