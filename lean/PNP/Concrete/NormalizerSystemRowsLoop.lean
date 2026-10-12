/-
Copyright (c) 2026 PNP Labs.

An ordered all-row loop with a conserved ordinal-plus-cursor budget.
An iteration is finite code with erased execution proofs; instantiated
assembly programs never receive an execution or correctness callback.
-/
import PNP.Concrete.NormalizerSystemRowsAppend

namespace PNP.Concrete.NormalizerBlocks.SystemRows
open BitRegister Occurrence

structure Iteration where
  block : Block 29
  result : State → State
  fuel : State → Nat
  bound : NatPolynomial
  exec : ∀ r, Exec block r.store (fuel r) (result r).store
  shared : ∀ r, (result r).shared = r.shared
  rows : ∀ r, (result r).rows = r.rows
  remaining : ∀ r, (result r).remaining = r.remaining.tail
  counter : ∀ r, (result r).counter = true::r.counter
  cost : ∀ r n, r.shared.Bounded n → r.counter.length ≤ n → fuel r ≤ bound.eval n

structure ScanResult where
  fuel : Nat
  state : State

def scan (iteration : Iteration) : BitString → State → ScanResult
  | [],r => ⟨1,{r with remaining := []}⟩
  | bit::rest,r =>
      let before := {r with remaining := bit::rest}
      let next := iteration.result before
      let tail := scan iteration rest next
      ⟨1 + (iteration.fuel before + tail.fuel),tail.state⟩
def loop (iteration : Iteration) : Block 29 := .loop 25 iteration.block
theorem scan_exec (iteration : Iteration) (word : BitString) (r : State) :
    Exec (loop iteration) ({r with remaining := word}).store
      (scan iteration word r).fuel (scan iteration word r).state.store := by
  induction word generalizing r with
  | nil => exact Exec.loopStop (source := (25 : Fin 29)) rfl
  | cons bit rest ih =>
      let before := {r with remaining := bit::rest}
      let next := iteration.result before
      have remaining : next.remaining = rest := iteration.remaining before
      have same : {next with remaining := rest} = next := by rw [← remaining]
      have tail := ih next
      rw [same] at tail
      exact Exec.loopStep (source := (25 : Fin 29)) (body := iteration.block) rfl
        (iteration.exec before) tail

theorem scan_shared (iteration : Iteration) (word : BitString) (r : State) :
    (scan iteration word r).state.shared = r.shared := by
  induction word generalizing r with
  | nil => rfl
  | cons bit rest ih =>
      let before := {r with remaining := bit::rest}
      exact (ih (iteration.result before)).trans (iteration.shared before)
theorem scan_rows (iteration : Iteration) (word : BitString) (r : State) :
    (scan iteration word r).state.rows = r.rows := by
  induction word generalizing r with
  | nil => rfl
  | cons bit rest ih =>
      let before := {r with remaining := bit::rest}
      exact (ih (iteration.result before)).trans (iteration.rows before)
theorem scan_remaining (iteration : Iteration) (word : BitString) (r : State) :
    (scan iteration word r).state.remaining = [] := by
  induction word generalizing r with
  | nil => rfl
  | cons bit rest ih => exact ih _
theorem scan_counter (iteration : Iteration) (word : BitString) (r : State) :
    (scan iteration word r).state.counter = List.replicate word.length true ++ r.counter := by
  induction word generalizing r with
  | nil => rfl
  | cons bit rest ih =>
      let before := {r with remaining := bit::rest}
      change (scan iteration rest (iteration.result before)).state.counter = _
      rw [ih,iteration.counter]
      simp only [List.length_cons,List.replicate_succ',List.append_assoc,List.cons_append,List.nil_append]
      rfl
theorem scan_fuel_bound (iteration : Iteration) (word : BitString) (r : State) (n : Nat)
    (fixed : r.shared.Bounded n) (budget : r.counter.length + word.length ≤ n) :
    (scan iteration word r).fuel ≤ word.length * (1 + iteration.bound.eval n) + 1 := by
  induction word generalizing r with
  | nil => simpa only [scan,List.length_nil,Nat.zero_mul,Nat.zero_add] using (Nat.le_refl 1)
  | cons bit rest ih =>
      let before := {r with remaining := bit::rest}
      let next := iteration.result before
      have index : before.counter.length ≤ n := by
        change r.counter.length ≤ n
        simp only [List.length_cons] at budget
        omega
      have work := iteration.cost before n fixed index
      have nextFixed : next.shared.Bounded n := by
        rw [show next.shared = r.shared from iteration.shared before]
        exact fixed
      have nextBudget : next.counter.length + rest.length ≤ n := by
        rw [show next.counter = true::r.counter from iteration.counter before,List.length_cons]
        simp only [List.length_cons] at budget
        omega
      have tail := ih next nextFixed nextBudget
      change 1 + (iteration.fuel before + (scan iteration rest next).fuel) ≤ _
      simp only [List.length_cons,Nat.succ_mul]
      omega

def whole (iteration : Iteration) (r : State) : ScanResult := scan iteration r.remaining r
theorem whole_exec (iteration : Iteration) (r : State) :
    Exec (loop iteration) r.store (whole iteration r).fuel (whole iteration r).state.store :=
  scan_exec iteration r.remaining r

end PNP.Concrete.NormalizerBlocks.SystemRows
