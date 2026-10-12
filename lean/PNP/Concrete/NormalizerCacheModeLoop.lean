/-
Copyright (c) 2026 PNP Labs.

Complete mode-table traversal on arbitrary raw input. A single invariant
bounds the growing dense ordinal together with the shrinking source cursor.
The original matching, dense formula and selected variables stay fixed.
-/
import PNP.Concrete.NormalizerCacheModeBody

namespace PNP.Concrete.NormalizerBlocks.CacheMode
open BitRegister Occurrence

def stop : Block 19 := .action (.clear 14)
def stopped (r : State) : State := r.withDense {r.core with remaining := []}
theorem stop_exec (r : State) : Exec stop r.store 1 (stopped r).store := .action _ _
def step : Block 19 := .branch 14 stop body stop
def stepped (r : State) : State :=
  match r.core.remaining with
  | false :: _ => bodyResult r
  | _ => stopped r
def stepFuel (r : State) : Nat :=
  match r.core.remaining with
  | false :: _ => 1 + bodyFuel r
  | _ => 2
theorem step_exec (r : State) : Exec step r.store (stepFuel r) (stepped r).store := by
  cases remaining : r.core.remaining with
  | nil =>
      simpa only [step,stepped,stepFuel,remaining] using
        (Exec.empty (source := (14 : Fin 19)) (before := r.store) remaining (stop_exec r))
  | cons bit rest =>
      cases bit with
      | false =>
          simpa only [step,stepped,stepFuel,remaining] using
            (Exec.zero (source := (14 : Fin 19)) (before := r.store) remaining (body_exec r))
      | true =>
          simpa only [step,stepped,stepFuel,remaining] using
            (Exec.one (source := (14 : Fin 19)) (before := r.store) remaining (stop_exec r))
theorem stepped_fields (r : State) :
    (stepped r).core.formula = r.core.formula ∧
    (stepped r).core.core.variables = r.core.core.variables ∧
    (stepped r).matching = r.matching := by
  unfold stepped
  split
  · exact ⟨(body_fields r).1,(body_fields r).2.2.1,(body_fields r).2.2.2.1⟩
  · exact ⟨rfl,rfl,rfl⟩
theorem step_progress (r : State) (nonempty : r.core.remaining ≠ []) :
    (stepped r).core.remaining.length < r.core.remaining.length := by
  unfold stepped
  split
  · rw [(body_fields r).2.1]
    exact UnseenData.next_shorter r.core.remaining nonempty
  · change 0 < r.core.remaining.length
    exact List.length_pos_iff.mpr nonempty
def cursorBudget (r : State) : Nat := r.counter.length + r.core.remaining.length
theorem stepped_budget (r : State) : cursorBudget (stepped r) ≤ cursorBudget r := by
  unfold stepped
  split
  · rename_i rest h
    have nonempty : r.core.remaining ≠ [] := by rw [h]; intro impossible; cases impossible
    have smaller := UnseenData.next_shorter r.core.remaining nonempty
    unfold cursorBudget
    rw [(body_fields r).2.1,(body_fields r).2.2.2.2,List.length_cons]
    omega
  · change r.counter.length + 0 ≤ r.counter.length + r.core.remaining.length
    omega
theorem stepFuel_bound (r : State) (n : Nat) (budget : cursorBudget r ≤ n)
    (formula : r.core.formula.length ≤ n) (variables : r.core.core.variables.length ≤ n)
    (matching : r.matching.length ≤ n) : stepFuel r ≤ bodyBound.eval n + 2 := by
  have cursor : r.core.remaining.length ≤ n := by unfold cursorBudget at budget; omega
  have counter : r.counter.length ≤ n := by unfold cursorBudget at budget; omega
  have cost := bodyFuel_bound r n cursor counter matching formula variables
  unfold stepFuel
  split <;> omega

structure ScanResult where
  fuel : Nat
  state : State
def loop : Block 19 := .loop 14 step
def scan : Nat → State → ScanResult
  | 0,r => ⟨1,r⟩
  | fuel + 1,r =>
      match r.core.remaining with
      | [] => ⟨1,r⟩
      | _ :: _ =>
          let tail := scan fuel (stepped r)
          ⟨1 + (stepFuel r + tail.fuel),tail.state⟩
theorem scan_stopped (fuel : Nat) (r : State) (empty : r.core.remaining = []) :
    scan fuel r = ⟨1,r⟩ := by
  cases fuel <;> simp only [scan,empty]
theorem scan_exec (fuel : Nat) (r : State)
    (enough : r.core.remaining.length < fuel ∨ r.core.remaining = []) :
    Exec loop r.store (scan fuel r).fuel (scan fuel r).state.store := by
  induction fuel generalizing r with
  | zero =>
      have empty := enough.resolve_left (Nat.not_lt_zero _)
      exact Exec.loopStop empty
  | succ fuel ih =>
      cases remaining : r.core.remaining with
      | nil => simpa only [loop,scan,remaining] using
          (Exec.loopStop (source := (14 : Fin 19)) (body := step) (store := r.store) remaining)
      | cons bit rest =>
          have size : r.core.remaining.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => rw [remaining] at h; cases h
          have nonempty : r.core.remaining ≠ [] := by rw [remaining]; intro impossible; cases impossible
          have tail := ih (stepped r) (Or.inl (Nat.lt_of_lt_of_le (step_progress r nonempty) size))
          simpa only [loop,scan,remaining] using
            Exec.loopStep (source := (14 : Fin 19)) (body := step) (before := r.store)
              remaining (step_exec r) tail
theorem scan_fields (fuel : Nat) (r : State) :
    (scan fuel r).state.core.formula = r.core.formula ∧
    (scan fuel r).state.core.core.variables = r.core.core.variables ∧
    (scan fuel r).state.matching = r.matching := by
  induction fuel generalizing r with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ fuel ih =>
      cases remaining : r.core.remaining with
      | nil => rw [scan_stopped _ r remaining]; exact ⟨rfl,rfl,rfl⟩
      | cons bit rest =>
          have tail := ih (stepped r)
          simpa only [scan,remaining] using
            And.intro (tail.1.trans (stepped_fields r).1)
              ⟨tail.2.1.trans (stepped_fields r).2.1,tail.2.2.trans (stepped_fields r).2.2⟩
theorem scan_fuel_bound (fuel : Nat) (r : State) (n : Nat) (budget : cursorBudget r ≤ n)
    (formula : r.core.formula.length ≤ n) (variables : r.core.core.variables.length ≤ n)
    (matching : r.matching.length ≤ n) :
    (scan fuel r).fuel ≤ (bodyBound.eval n + 3) * fuel + 1 := by
  induction fuel generalizing r with
  | zero => simp only [scan,Nat.mul_zero,Nat.zero_add]; exact Nat.le_refl _
  | succ fuel ih =>
      cases remaining : r.core.remaining with
      | nil => simp only [scan,remaining]; omega
      | cons bit rest =>
          have nextBudget := Nat.le_trans (stepped_budget r) budget
          have nextFormula : (stepped r).core.formula.length ≤ n := by rw [(stepped_fields r).1]; exact formula
          have nextVariables : (stepped r).core.core.variables.length ≤ n := by rw [(stepped_fields r).2.1]; exact variables
          have nextMatching : (stepped r).matching.length ≤ n := by rw [(stepped_fields r).2.2]; exact matching
          have tail := ih (stepped r) nextBudget nextFormula nextVariables nextMatching
          have cost := stepFuel_bound r n budget formula variables matching
          simp only [scan,remaining,Nat.mul_succ]
          omega
def whole (r : State) : ScanResult := scan (r.core.remaining.length + 1) r
theorem whole_exec (r : State) : Exec loop r.store (whole r).fuel (whole r).state.store :=
  scan_exec _ r (Or.inl (Nat.lt_succ_self _))
theorem whole_fields (r : State) :
    (whole r).state.core.formula = r.core.formula ∧
    (whole r).state.core.core.variables = r.core.core.variables ∧
    (whole r).state.matching = r.matching := scan_fields _ r
def loopBound : NatPolynomial := .add (.mul (.add bodyBound (.constant 3)) (.linear 1 1)) (.constant 1)
theorem loopBound_eval (n : Nat) : loopBound.eval n = (bodyBound.eval n + 3) * (n + 1) + 1 := by
  change (bodyBound.eval n + 3) * (1 * n + 1) + 1 = _
  rw [Nat.one_mul]
theorem whole_fuel_bound (r : State) (n : Nat) (budget : cursorBudget r ≤ n)
    (formula : r.core.formula.length ≤ n) (variables : r.core.core.variables.length ≤ n)
    (matching : r.matching.length ≤ n) : (whole r).fuel ≤ loopBound.eval n := by
  have cost := scan_fuel_bound (r.core.remaining.length + 1) r n budget formula variables matching
  have cursor : r.core.remaining.length ≤ n := by unfold cursorBudget at budget; omega
  have product := Nat.mul_le_mul_left (bodyBound.eval n + 3)
    (show r.core.remaining.length + 1 ≤ n + 1 by omega)
  rw [loopBound_eval]
  unfold whole
  omega

end PNP.Concrete.NormalizerBlocks.CacheMode
