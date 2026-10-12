/-
Copyright (c) 2026 PNP Labs.

Complete finite candidate-bit traversal. The cursor and growing ordinal
share one conserved size budget. Cached data are fixed and growing output
is excluded from the recursive per-iteration execution bound.
-/
import PNP.Concrete.NormalizerCandidateBitsBody

namespace PNP.Concrete.NormalizerBlocks.CandidateBits
open BitRegister Occurrence

structure ScanResult where
  fuel : Nat
  state : State
def loop : Block 22 := .loop 19 body
def scan : BitString → State → ScanResult
  | [],r => ⟨1,{r with remaining := []}⟩
  | bit::rest,r =>
      let before := {r with remaining := bit::rest}
      let tail := scan rest (bodyResult before)
      ⟨1 + (bodyFuel before + tail.fuel),tail.state⟩
theorem scan_exec (word : BitString) (r : State) :
    Exec loop ({r with remaining := word}).store (scan word r).fuel (scan word r).state.store := by
  induction word generalizing r with
  | nil => exact Exec.loopStop (source := (19 : Fin 22)) rfl
  | cons bit rest ih =>
      exact Exec.loopStep (source := (19 : Fin 22)) rfl
        (body_exec {r with remaining := bit::rest}) (ih (bodyResult {r with remaining := bit::rest}))
theorem scan_fields (word : BitString) (r : State) :
    (scan word r).state.core.core.formula = r.core.core.formula ∧
    (scan word r).state.core.matching = r.core.matching ∧
    (scan word r).state.core.counter = r.core.counter ∧
    (scan word r).state.remaining = [] := by
  induction word generalizing r with
  | nil => exact ⟨rfl,rfl,rfl,rfl⟩
  | cons bit rest ih =>
      have tail := ih (bodyResult {r with remaining := bit::rest})
      have step := body_fields {r with remaining := bit::rest}
      exact ⟨tail.1.trans step.1,tail.2.1.trans step.2.1,tail.2.2.1.trans step.2.2.1,tail.2.2.2⟩
theorem scan_counter (word : BitString) (r : State) :
    (scan word r).state.counter = List.replicate word.length true ++ r.counter := by
  induction word generalizing r with
  | nil => rfl
  | cons bit rest ih =>
      change (scan rest (bodyResult {r with remaining := bit::rest})).state.counter = _
      rw [ih,(body_fields _).2.2.2.2,List.length_cons,List.replicate_succ']
      simp only [List.append_assoc,List.cons_append,List.nil_append]
theorem scan_buffer_length (word : BitString) (r : State) :
    (scan word r).state.buffer.length = word.length + r.buffer.length := by
  induction word generalizing r with
  | nil => simp only [scan,List.length_nil,Nat.zero_add]
  | cons bit rest ih =>
      change (scan rest (bodyResult {r with remaining := bit::rest})).state.buffer.length = _
      rw [ih,body_buffer]
      simp only [List.length_cons]
      omega
theorem scan_fuel_bound (word : BitString) (r : State) (n : Nat)
    (budget : r.counter.length + word.length ≤ n)
    (formula : r.core.core.formula.length ≤ n) (owners : r.core.matching.length ≤ n)
    (slots : r.core.counter.length ≤ n) :
    (scan word r).fuel ≤ (bodyBound.eval n + 1) * word.length + 1 := by
  induction word generalizing r with
  | nil => simp only [scan,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.le_refl]
  | cons bit rest ih =>
      let before := {r with remaining := bit::rest}
      have counter : r.counter.length ≤ n := by omega
      have cost := bodyFuel_bound before n formula owners slots counter
      have step := body_fields before
      have nextBudget : (bodyResult before).counter.length + rest.length ≤ n := by
        rw [step.2.2.2.2]
        change (true::r.counter).length + rest.length ≤ n
        simp only [List.length_cons] at *
        omega
      have hf : (bodyResult before).core.core.formula.length ≤ n := by rw [step.1]; exact formula
      have ho : (bodyResult before).core.matching.length ≤ n := by rw [step.2.1]; exact owners
      have hs : (bodyResult before).core.counter.length ≤ n := by rw [step.2.2.1]; exact slots
      have tail := ih (bodyResult before) nextBudget hf ho hs
      change 1 + (bodyFuel before + (scan rest (bodyResult before)).fuel) ≤ _
      simp only [List.length_cons,Nat.mul_succ]
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
    (formula : r.core.core.formula.length ≤ n) (owners : r.core.matching.length ≤ n)
    (slots : r.core.counter.length ≤ n) : (whole r).fuel ≤ loopBound.eval n := by
  have cost := scan_fuel_bound r.remaining r n budget formula owners slots
  have product := Nat.mul_le_mul_left (bodyBound.eval n + 1) (show r.remaining.length ≤ n by omega)
  rw [loopBound_eval]
  exact Nat.le_trans cost (Nat.add_le_add_right product 1)

end PNP.Concrete.NormalizerBlocks.CandidateBits
