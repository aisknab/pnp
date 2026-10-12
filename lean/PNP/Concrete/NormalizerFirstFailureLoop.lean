/-
Copyright (c) 2026 PNP Labs.

Complete first-failure traversal. A false clause terminates immediately;
otherwise the runtime cursor decreases. The counter and cursor share one
size budget, yielding an input-size polynomial without an exponential loop.
-/
import PNP.Concrete.NormalizerFirstFailureBody

namespace PNP.Concrete.NormalizerBlocks.FirstFailure
open BitRegister Occurrence
attribute [local irreducible] CandidateTruth.clauseResult

structure ScanResult where
  fuel : Nat
  state : State
def loop : Block 22 := .loop 19 body
def scan : BitString → State → ScanResult
  | [],r => ⟨1,{r with remaining := []}⟩
  | bit::rest,r =>
      let before := {r with remaining := bit::rest}
      let after := bodyResult before
      if truth before then
        let tail := scan rest after
        ⟨1 + (bodyFuel before + tail.fuel),tail.state⟩
      else ⟨1 + (bodyFuel before + 1),after⟩
theorem scan_exec (word : BitString) (r : State) :
    Exec loop ({r with remaining := word}).store (scan word r).fuel (scan word r).state.store := by
  induction word generalizing r with
  | nil => exact Exec.loopStop (source := (19 : Fin 22)) rfl
  | cons bit rest ih =>
      let before := {r with remaining := bit::rest}
      cases h : truth ({r with remaining := bit::rest})
      · have empty : (bodyResult before).remaining = [] := by
          rw [body_remaining,h]
          rfl
        have stop : Exec loop (bodyResult before).store 1 (bodyResult before).store :=
          Exec.loopStop (source := (19 : Fin 22)) empty
        have checked := Exec.loopStep (source := (19 : Fin 22)) rfl (body_exec before) stop
        simpa only [scan,loop,before,h,Bool.false_eq_true,ite_false] using checked
      · have next : (bodyResult before).remaining = rest := by
          rw [body_remaining,h]
          rfl
        have same : {bodyResult before with remaining := rest} = bodyResult before := by
          rw [← next]
        have tail := ih (bodyResult before)
        rw [same] at tail
        have checked := Exec.loopStep (source := (19 : Fin 22)) rfl (body_exec before) tail
        simpa only [scan,loop,before,h,ite_true] using checked
theorem scan_fields (word : BitString) (r : State) :
    (scan word r).state.core.core.formula = r.core.core.formula ∧
    (scan word r).state.core.matching = r.core.matching ∧
    (scan word r).state.remaining = [] := by
  induction word generalizing r with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons bit rest ih =>
      let before := {r with remaining := bit::rest}
      have fields := body_fields before
      cases h : truth ({r with remaining := bit::rest})
      · have empty : (bodyResult before).remaining = [] := by rw [body_remaining,h]; rfl
        simpa only [scan,h,Bool.false_eq_true,ite_false] using
          (show (bodyResult before).core.core.formula = r.core.core.formula ∧
            (bodyResult before).core.matching = r.core.matching ∧
            (bodyResult before).remaining = [] from ⟨fields.1,fields.2,empty⟩)
      · have tail := ih (bodyResult before)
        simpa only [scan,h,ite_true] using
          (show (scan rest (bodyResult before)).state.core.core.formula = r.core.core.formula ∧
            (scan rest (bodyResult before)).state.core.matching = r.core.matching ∧
            (scan rest (bodyResult before)).state.remaining = [] from
              ⟨tail.1.trans fields.1,tail.2.1.trans fields.2,tail.2.2⟩)
theorem scan_fuel_bound (word : BitString) (r : State) (n : Nat)
    (budget : r.counter.length + word.length ≤ n) (formula : r.core.core.formula.length ≤ n) :
    (scan word r).fuel ≤ (bodyBound.eval n + 1) * word.length + 1 := by
  induction word generalizing r with
  | nil => simp only [scan,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.le_refl]
  | cons bit rest ih =>
      let before := {r with remaining := bit::rest}
      have counter : r.counter.length ≤ n := by omega
      have cost := bodyFuel_bound before n formula counter
      dsimp only [before] at cost
      cases h : truth ({r with remaining := bit::rest})
      · simp only [scan,h,Bool.false_eq_true,ite_false,List.length_cons,Nat.mul_succ]
        omega
      · have nextBudget : (bodyResult before).counter.length + rest.length ≤ n := by
          rw [body_counter,h]
          change (true::r.counter).length + rest.length ≤ n
          simp only [List.length_cons] at *
          omega
        have nextFormula : (bodyResult before).core.core.formula.length ≤ n := by
          rw [(body_fields before).1]
          exact formula
        have tail := ih (bodyResult before) nextBudget nextFormula
        dsimp only [before] at tail
        simp only [scan,h,ite_true,List.length_cons,Nat.mul_succ]
        omega

def whole (r : State) : ScanResult := scan r.remaining r
theorem whole_exec (r : State) : Exec loop r.store (whole r).fuel (whole r).state.store :=
  scan_exec r.remaining r
def loopBound : NatPolynomial :=
  .add (.mul (.add bodyBound (.constant 1)) (.linear 1 0)) (.constant 1)
theorem loopBound_eval (n : Nat) : loopBound.eval n = (bodyBound.eval n + 1) * n + 1 := by
  change (bodyBound.eval n + 1) * (1 * n + 0) + 1 = _
  simp only [Nat.one_mul,Nat.add_zero]
theorem whole_fuel_bound (r : State) (n : Nat)
    (budget : r.counter.length + r.remaining.length ≤ n)
    (formula : r.core.core.formula.length ≤ n) : (whole r).fuel ≤ loopBound.eval n := by
  have cost := scan_fuel_bound r.remaining r n budget formula
  have product := Nat.mul_le_mul_left (bodyBound.eval n + 1) (show r.remaining.length ≤ n by omega)
  rw [loopBound_eval]
  exact Nat.le_trans cost (Nat.add_le_add_right product 1)

end PNP.Concrete.NormalizerBlocks.FirstFailure
