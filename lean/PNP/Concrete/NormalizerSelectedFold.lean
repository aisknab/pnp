/-
Copyright (c) 2026 PNP Labs.

Shared finite-control traversal for derived source-cache tables. The body
contract includes literal block execution, strict cursor advance, preserved
source bytes and an output-independent polynomial cost. The contract's
semantic function is proof data, never an instruction of the finite machine.
-/
import PNP.Concrete.NormalizerDenseCall

namespace PNP.Concrete.NormalizerBlocks.SelectedFold
open BitRegister Occurrence
abbrev State := DenseClauses.State

structure Operation where
  body : Block 16
  after : State → State
  cost : State → Nat
  execution : ∀ r, Exec body r.store (cost r) (after r).store
  remaining : ∀ r, (after r).remaining = UnseenData.next r.remaining
  fields : ∀ r, (after r).formula = r.formula ∧ (after r).core.variables = r.core.variables
  bound : NatPolynomial
  cost_bound : ∀ r n, r.remaining.length ≤ n → r.formula.length ≤ n →
    r.core.variables.length ≤ n → cost r ≤ bound.eval n

variable (op : Operation)

def stop : Block 16 := .action (.clear 14)
def stopped (r : State) : State := {r with remaining := []}
theorem stop_exec (r : State) : Exec stop r.store 1 (stopped r).store := .action _ _
def step : Block 16 := .branch 14 stop op.body stop
def stepped (r : State) : State :=
  match r.remaining with
  | false :: _ => op.after r
  | _ => stopped r
def stepFuel (r : State) : Nat :=
  match r.remaining with
  | false :: _ => 1 + op.cost r
  | _ => 2
theorem step_exec (r : State) : Exec (step op) r.store (stepFuel op r) (stepped op r).store := by
  cases remaining : r.remaining with
  | nil =>
      simpa only [step, stepped, stepFuel, remaining] using
        (Exec.empty (source := (14 : Fin 16)) (before := r.store) remaining (stop_exec r))
  | cons bit rest =>
      cases bit with
      | false =>
          simpa only [step, stepped, stepFuel, remaining] using
            (Exec.zero (source := (14 : Fin 16)) (before := r.store) remaining (op.execution r))
      | true =>
          simpa only [step, stepped, stepFuel, remaining] using
            (Exec.one (source := (14 : Fin 16)) (before := r.store) remaining (stop_exec r))

theorem stepped_fields (r : State) :
    (stepped op r).formula = r.formula ∧
    (stepped op r).core.variables = r.core.variables := by
  unfold stepped
  split
  · exact op.fields r
  · exact ⟨rfl,rfl⟩

theorem step_progress (r : State) (nonempty : r.remaining ≠ []) :
    (stepped op r).remaining.length < r.remaining.length := by
  unfold stepped
  split
  · rw [op.remaining r]
    exact UnseenData.next_shorter r.remaining nonempty
  · change 0 < r.remaining.length
    exact List.length_pos_iff.mpr nonempty

theorem stepFuel_bound (r : State) (bound : Nat)
    (remaining : r.remaining.length ≤ bound) (formula : r.formula.length ≤ bound)
    (variables : r.core.variables.length ≤ bound) :
    stepFuel op r ≤ op.bound.eval bound + 2 := by
  have body := op.cost_bound r bound remaining formula variables
  unfold stepFuel
  split <;> omega

structure ScanResult where
  fuel : Nat
  state : State
def loop : Block 16 := .loop 14 (step op)
def scan : Nat → State → ScanResult
  | 0, r => ⟨1,r⟩
  | fuel + 1, r =>
      match r.remaining with
      | [] => ⟨1,r⟩
      | _ :: _ =>
          let tail := scan fuel (stepped op r)
          ⟨1 + (stepFuel op r + tail.fuel),tail.state⟩

theorem scan_stopped (fuel : Nat) (r : State) (stopped : r.remaining = []) :
    scan op fuel r = ⟨1,r⟩ := by
  cases fuel <;> simp only [scan, stopped]
theorem scan_exec (fuel : Nat) (r : State)
    (enough : r.remaining.length < fuel ∨ r.remaining = []) :
    Exec (loop op) r.store (scan op fuel r).fuel (scan op fuel r).state.store := by
  induction fuel generalizing r with
  | zero =>
      have empty := enough.resolve_left (Nat.not_lt_zero _)
      exact Exec.loopStop empty
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil => simpa only [loop, scan, remaining] using
          (Exec.loopStop (source := (14 : Fin 16)) (body := step op) (store := r.store) remaining)
      | cons bit rest =>
          have size : r.remaining.length ≤ fuel := by
            cases enough with
            | inl h => omega
            | inr h => rw [remaining] at h; cases h
          have nonempty : r.remaining ≠ [] := by rw [remaining]; intro impossible; cases impossible
          have tail := ih (stepped op r)
            (Or.inl (Nat.lt_of_lt_of_le (step_progress op r nonempty) size))
          simpa only [loop, scan, remaining] using
            Exec.loopStep (source := (14 : Fin 16)) (body := step op) (before := r.store)
              remaining (step_exec op r) tail

theorem scan_fields (fuel : Nat) (r : State) :
    (scan op fuel r).state.formula = r.formula ∧
    (scan op fuel r).state.core.variables = r.core.variables := by
  induction fuel generalizing r with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil => rw [scan_stopped op _ r remaining]; exact ⟨rfl,rfl⟩
      | cons bit rest =>
          have tail := ih (stepped op r)
          simpa only [scan, remaining] using
            And.intro (tail.1.trans (stepped_fields op r).1) (tail.2.trans (stepped_fields op r).2)

theorem scan_fuel_bound (fuel : Nat) (r : State) (bound : Nat)
    (remainingBound : r.remaining.length ≤ bound) (formula : r.formula.length ≤ bound)
    (variables : r.core.variables.length ≤ bound) :
    (scan op fuel r).fuel ≤ (op.bound.eval bound + 3) * fuel + 1 := by
  induction fuel generalizing r with
  | zero => simp only [scan, Nat.mul_zero, Nat.zero_add]; exact Nat.le_refl _
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil => simp only [scan, remaining]; omega
      | cons bit rest =>
          have nonempty : r.remaining ≠ [] := by rw [remaining]; intro impossible; cases impossible
          have nextBound : (stepped op r).remaining.length ≤ bound :=
            Nat.le_trans (Nat.le_of_lt (step_progress op r nonempty)) remainingBound
          have nextFormula : (stepped op r).formula.length ≤ bound := by rw [(stepped_fields op r).1]; exact formula
          have nextVariables : (stepped op r).core.variables.length ≤ bound := by rw [(stepped_fields op r).2]; exact variables
          have tail := ih (stepped op r) nextBound nextFormula nextVariables
          have step := stepFuel_bound op r bound remainingBound formula variables
          simp only [scan, remaining, Nat.mul_succ]
          omega

def whole (r : State) : ScanResult := scan op (r.remaining.length + 1) r
theorem whole_exec (r : State) : Exec (loop op) r.store (whole op r).fuel (whole op r).state.store :=
  scan_exec op _ r (Or.inl (Nat.lt_succ_self _))
theorem whole_fields (r : State) :
    (whole op r).state.formula = r.formula ∧ (whole op r).state.core.variables = r.core.variables :=
  scan_fields op _ r

def loopBound : NatPolynomial :=
  .add (.mul (.add op.bound (.constant 3)) (.linear 1 1)) (.constant 1)
theorem loopBound_eval (bound : Nat) :
    (loopBound op).eval bound = (op.bound.eval bound + 3) * (bound + 1) + 1 := by
  change (op.bound.eval bound + 3) * (1 * bound + 1) + 1 = _
  rw [Nat.one_mul]
theorem whole_fuel_bound (r : State) (bound : Nat)
    (remaining : r.remaining.length ≤ bound) (formula : r.formula.length ≤ bound)
    (variables : r.core.variables.length ≤ bound) :
    (whole op r).fuel ≤ (loopBound op).eval bound := by
  have fuel := scan_fuel_bound op (r.remaining.length + 1) r bound remaining formula variables
  have product := Nat.mul_le_mul_left (op.bound.eval bound + 3)
    (show r.remaining.length + 1 ≤ bound + 1 by omega)
  rw [loopBound_eval]
  unfold whole
  omega

end PNP.Concrete.NormalizerBlocks.SelectedFold
