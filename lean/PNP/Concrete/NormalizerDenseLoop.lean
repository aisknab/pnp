/-
Copyright (c) 2026 PNP Labs.

Whole selected-clause traversal. Each live selection is read from bytes,
queried in the original formula, and compacted before continuing. The
decreasing selected cursor controls termination on every raw input.
-/
import PNP.Concrete.NormalizerDenseBody

namespace PNP.Concrete.NormalizerBlocks.DenseClauses
open BitRegister Occurrence

def stop : Block 16 := .action (.clear 14)
def stopped (r : State) : State := {r with remaining := []}
theorem stop_exec (r : State) : Exec stop r.store 1 (stopped r).store := .action _ _
def step : Block 16 := .branch 14 stop body stop
def stepped (r : State) : State :=
  match r.remaining with
  | false :: _ => bodyResult r
  | _ => stopped r
def stepFuel (r : State) : Nat :=
  match r.remaining with
  | false :: _ => 1 + bodyFuel r
  | _ => 2
theorem step_exec (r : State) : Exec step r.store (stepFuel r) (stepped r).store := by
  cases remaining : r.remaining with
  | nil =>
      simpa only [step, stepped, stepFuel, remaining] using
        (Exec.empty (source := (14 : Fin 16)) (before := r.store) remaining (stop_exec r))
  | cons bit rest =>
      cases bit with
      | false =>
          simpa only [step, stepped, stepFuel, remaining] using
            (Exec.zero (source := (14 : Fin 16)) (before := r.store) remaining (body_exec r))
      | true =>
          simpa only [step, stepped, stepFuel, remaining] using
            (Exec.one (source := (14 : Fin 16)) (before := r.store) remaining (stop_exec r))

theorem stepped_fields (r : State) :
    (stepped r).formula = r.formula ∧
    (stepped r).core.variables = r.core.variables := by
  unfold stepped
  split
  · exact ⟨(body_fields r).1,(body_fields r).2.2⟩
  · exact ⟨rfl,rfl⟩

theorem step_progress (r : State) (nonempty : r.remaining ≠ []) :
    (stepped r).remaining.length < r.remaining.length := by
  unfold stepped
  split
  · rw [(body_fields r).2.1]
    exact UnseenData.next_shorter r.remaining nonempty
  · change 0 < r.remaining.length
    exact List.length_pos_iff.mpr nonempty

theorem stepFuel_bound (r : State) (bound : Nat)
    (remaining : r.remaining.length ≤ bound) (formula : r.formula.length ≤ bound)
    (variables : r.core.variables.length ≤ bound) :
    stepFuel r ≤ bodyBound.eval bound + 2 := by
  have body := bodyFuel_bound r bound remaining formula variables
  unfold stepFuel
  split <;> omega

structure ScanResult where
  fuel : Nat
  state : State
def loop : Block 16 := .loop 14 step
def scan : Nat → State → ScanResult
  | 0, r => ⟨1,r⟩
  | fuel + 1, r =>
      match r.remaining with
      | [] => ⟨1,r⟩
      | _ :: _ =>
          let tail := scan fuel (stepped r)
          ⟨1 + (stepFuel r + tail.fuel),tail.state⟩

theorem scan_stopped (fuel : Nat) (r : State) (stopped : r.remaining = []) :
    scan fuel r = ⟨1,r⟩ := by
  cases fuel <;> simp only [scan, stopped]
theorem scan_exec (fuel : Nat) (r : State)
    (enough : r.remaining.length < fuel ∨ r.remaining = []) :
    Exec loop r.store (scan fuel r).fuel (scan fuel r).state.store := by
  induction fuel generalizing r with
  | zero =>
      have empty := enough.resolve_left (Nat.not_lt_zero _)
      exact Exec.loopStop empty
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil => simpa only [loop, scan, remaining] using
          (Exec.loopStop (source := (14 : Fin 16)) (body := step) (store := r.store) remaining)
      | cons bit rest =>
          have size : r.remaining.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => rw [remaining] at h; cases h
          have nonempty : r.remaining ≠ [] := by rw [remaining]; intro impossible; cases impossible
          have tail := ih (stepped r)
            (Or.inl (Nat.lt_of_lt_of_le (step_progress r nonempty) size))
          simpa only [loop, scan, remaining] using
            Exec.loopStep (source := (14 : Fin 16)) (body := step) (before := r.store)
              remaining (step_exec r) tail

theorem scan_fields (fuel : Nat) (r : State) :
    (scan fuel r).state.formula = r.formula ∧
    (scan fuel r).state.core.variables = r.core.variables := by
  induction fuel generalizing r with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil => rw [scan_stopped _ r remaining]; exact ⟨rfl,rfl⟩
      | cons bit rest =>
          have tail := ih (stepped r)
          simpa only [scan, remaining] using
            And.intro (tail.1.trans (stepped_fields r).1) (tail.2.trans (stepped_fields r).2)

theorem scan_fuel_bound (fuel : Nat) (r : State) (bound : Nat)
    (remainingBound : r.remaining.length ≤ bound) (formula : r.formula.length ≤ bound)
    (variables : r.core.variables.length ≤ bound) :
    (scan fuel r).fuel ≤ (bodyBound.eval bound + 3) * fuel + 1 := by
  induction fuel generalizing r with
  | zero => simp only [scan, Nat.mul_zero, Nat.zero_add]; exact Nat.le_refl _
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil => simp only [scan, remaining]; omega
      | cons bit rest =>
          have nonempty : r.remaining ≠ [] := by rw [remaining]; intro impossible; cases impossible
          have nextBound : (stepped r).remaining.length ≤ bound :=
            Nat.le_trans (Nat.le_of_lt (step_progress r nonempty)) remainingBound
          have nextFormula : (stepped r).formula.length ≤ bound := by rw [(stepped_fields r).1]; exact formula
          have nextVariables : (stepped r).core.variables.length ≤ bound := by rw [(stepped_fields r).2]; exact variables
          have tail := ih (stepped r) nextBound nextFormula nextVariables
          have step := stepFuel_bound r bound remainingBound formula variables
          simp only [scan, remaining, Nat.mul_succ]
          omega

def whole (r : State) : ScanResult := scan (r.remaining.length + 1) r
theorem whole_exec (r : State) : Exec loop r.store (whole r).fuel (whole r).state.store :=
  scan_exec _ r (Or.inl (Nat.lt_succ_self _))
theorem whole_fields (r : State) :
    (whole r).state.formula = r.formula ∧ (whole r).state.core.variables = r.core.variables :=
  scan_fields _ r

def loopBound : NatPolynomial :=
  .add (.mul (.add bodyBound (.constant 3)) (.linear 1 1)) (.constant 1)
theorem loopBound_eval (bound : Nat) :
    loopBound.eval bound = (bodyBound.eval bound + 3) * (bound + 1) + 1 := by
  change (bodyBound.eval bound + 3) * (1 * bound + 1) + 1 = _
  rw [Nat.one_mul]
theorem whole_fuel_bound (r : State) (bound : Nat)
    (remaining : r.remaining.length ≤ bound) (formula : r.formula.length ≤ bound)
    (variables : r.core.variables.length ≤ bound) :
    (whole r).fuel ≤ loopBound.eval bound := by
  have fuel := scan_fuel_bound (r.remaining.length + 1) r bound remaining formula variables
  have product := Nat.mul_le_mul_left (bodyBound.eval bound + 3)
    (show r.remaining.length + 1 ≤ bound + 1 by omega)
  rw [loopBound_eval]
  unfold whole
  omega

end PNP.Concrete.NormalizerBlocks.DenseClauses
