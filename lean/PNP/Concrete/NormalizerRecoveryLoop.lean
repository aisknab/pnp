/-
Copyright (c) 2026 PNP Labs.

Traverse every requested original coordinate. A conserved cursor-plus-index
budget bounds each recovered bit; the growing output buffer is not fed into
the next iteration's polynomial. Protected source data stay unchanged.
-/
import PNP.Concrete.NormalizerRecoveryBit

namespace PNP.Concrete.NormalizerBlocks.Recovery
open BitRegister Occurrence

def appendBit : Block 16 := .branch 8 (.action (.push 15 false))
  (.action (.push 15 false)) (.action (.push 15 true))
def bitAppended (r : State) : State := {r with buffer := r.core.output.headD false::r.buffer}
theorem appendBit_exec (r : State) : Exec appendBit r.store 2 (bitAppended r).store := by
  have zero : Exec (.action (.push (15 : Fin 16) false)) r.store 1
      ({r with buffer := false::r.buffer}).store := .action _ _
  have one : Exec (.action (.push (15 : Fin 16) true)) r.store 1
      ({r with buffer := true::r.buffer}).store := .action _ _
  have checked := EdgeKinds.branch_head (8 : Fin 16) r.store
    (.action (.push 15 false)) (.action (.push 15 true)) 1 1
    ({r with buffer := false::r.buffer}).store ({r with buffer := true::r.buffer}).store zero one
  change Exec appendBit r.store (1+if r.core.output.headD false then 1 else 1)
    (if r.core.output.headD false then ({r with buffer := true::r.buffer}).store else
      ({r with buffer := false::r.buffer}).store) at checked
  cases h : r.core.output.headD false <;>
    simpa only [bitAppended,h,Bool.false_eq_true,ite_false,ite_true] using checked
def advance : Block 16 := .seq (.action (.pop 13)) (.action (.push 14 true))
def advanced (r : State) : State := {r with remaining := r.remaining.tail,counter := true::r.counter}
theorem advance_exec (r : State) : Exec advance r.store 2 (advanced r).store :=
  Exec.seq (.action _ _) (.action _ _)
def body : Block 16 := .seq bit (.seq appendBit advance)
def bodyResult (r : State) : State := advanced (bitAppended (bitResult r))
def bodyFuel (r : State) : Nat := bitFuel r+(2+2)
theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (bodyResult r).store :=
  Exec.seq (bit_exec r) (Exec.seq (appendBit_exec (bitResult r)) (advance_exec (bitAppended (bitResult r))))
theorem body_fields (r : State) :
    (bodyResult r).data = r.data ∧ (bodyResult r).remaining = r.remaining.tail ∧
      (bodyResult r).counter = true::r.counter :=
  ⟨(bit_fields r).1,congrArg List.tail (bit_fields r).2.1,
    congrArg (List.cons true) (bit_fields r).2.2.1⟩
theorem body_buffer (r : State) :
    (bodyResult r).buffer = (bitResult r).core.output.headD false::r.buffer := by
  change (bitResult r).core.output.headD false::(bitResult r).buffer = _
  rw [(bit_fields r).2.2.2]
def bodyBound : NatPolynomial := .add bitBound (.constant 4)
theorem bodyFuel_bound (r : State) (n : Nat)
    (formula : r.formula.length ≤ n) (matching : r.matching.length ≤ n)
    (variables : r.variables.length ≤ n) (counter : r.counter.length ≤ n) :
    bodyFuel r ≤ bodyBound.eval n := Nat.add_le_add_right (bitFuel_bound r n formula matching variables counter) 4

structure ScanResult where
  fuel : Nat
  state : State
def loop : Block 16 := .loop 13 body
def scan : BitString → State → ScanResult
  | [],r => ⟨1,{r with remaining := []}⟩
  | head::rest,r =>
      let before := {r with remaining := head::rest}
      let tail := scan rest (bodyResult before)
      ⟨1+(bodyFuel before+tail.fuel),tail.state⟩
theorem scan_exec (word : BitString) (r : State) :
    Exec loop ({r with remaining := word}).store (scan word r).fuel (scan word r).state.store := by
  induction word generalizing r with
  | nil => exact Exec.loopStop (source := (13 : Fin 16)) rfl
  | cons head rest ih =>
      let before := {r with remaining := head::rest}
      have tail := ih (bodyResult before)
      have remaining : (bodyResult before).remaining = rest := (body_fields before).2.1
      have same : {bodyResult before with remaining := rest} = bodyResult before := by
        rw [← remaining]
      rw [same] at tail
      exact Exec.loopStep (source := (13 : Fin 16)) (body := body) rfl (body_exec before) tail
theorem scan_fields (word : BitString) (r : State) :
    (scan word r).state.data = r.data ∧ (scan word r).state.remaining = [] := by
  induction word generalizing r with
  | nil => exact ⟨rfl,rfl⟩
  | cons head rest ih =>
      have tail := ih (bodyResult {r with remaining := head::rest})
      exact ⟨tail.1.trans (body_fields {r with remaining := head::rest}).1,tail.2⟩
theorem scan_counter (word : BitString) (r : State) :
    (scan word r).state.counter = List.replicate word.length true++r.counter := by
  induction word generalizing r with
  | nil => rfl
  | cons head rest ih =>
      change (scan rest (bodyResult {r with remaining := head::rest})).state.counter = _
      rw [ih,(body_fields _).2.2,List.length_cons,List.replicate_succ']
      simp only [List.append_assoc,List.cons_append,List.nil_append]
theorem scan_buffer_length (word : BitString) (r : State) :
    (scan word r).state.buffer.length = word.length+r.buffer.length := by
  induction word generalizing r with
  | nil => simp only [scan,List.length_nil,Nat.zero_add]
  | cons head rest ih =>
      change (scan rest (bodyResult {r with remaining := head::rest})).state.buffer.length = _
      rw [ih,body_buffer]
      simp only [List.length_cons]
      omega
theorem scan_fuel_bound (word : BitString) (r : State) (n : Nat)
    (budget : r.counter.length+word.length ≤ n)
    (formula : r.formula.length ≤ n) (matching : r.matching.length ≤ n)
    (variables : r.variables.length ≤ n) :
    (scan word r).fuel ≤ (bodyBound.eval n+1)*word.length+1 := by
  induction word generalizing r with
  | nil => simp only [scan,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.le_refl]
  | cons head rest ih =>
      let before := {r with remaining := head::rest}
      have counter : r.counter.length ≤ n := by omega
      have cost := bodyFuel_bound before n formula matching variables counter
      have step := body_fields before
      have nextBudget : (bodyResult before).counter.length+rest.length ≤ n := by
        rw [step.2.2]
        change (true::r.counter).length+rest.length ≤ n
        simp only [List.length_cons] at *
        omega
      have ff := congrArg Data.formula step.1
      have fm := congrArg Data.matching step.1
      have fv := congrArg Data.variables step.1
      dsimp only [State.data] at ff fm fv
      have hf : (bodyResult before).formula.length ≤ n := by rw [ff]; exact formula
      have hm : (bodyResult before).matching.length ≤ n := by rw [fm]; exact matching
      have hv : (bodyResult before).variables.length ≤ n := by rw [fv]; exact variables
      have tail := ih (bodyResult before) nextBudget hf hm hv
      change 1+(bodyFuel before+(scan rest (bodyResult before)).fuel) ≤ _
      simp only [List.length_cons,Nat.mul_succ]
      omega
def whole (r : State) : ScanResult := scan r.remaining r
theorem whole_exec (r : State) : Exec loop r.store (whole r).fuel (whole r).state.store :=
  scan_exec r.remaining r
def loopBound : NatPolynomial :=
  .add (.mul (.add bodyBound (.constant 1)) .variable) (.constant 1)
theorem loopBound_eval (n : Nat) : loopBound.eval n = (bodyBound.eval n+1)*n+1 := rfl
theorem whole_fuel_bound (r : State) (n : Nat)
    (budget : r.counter.length+r.remaining.length ≤ n)
    (formula : r.formula.length ≤ n) (matching : r.matching.length ≤ n)
    (variables : r.variables.length ≤ n) : (whole r).fuel ≤ loopBound.eval n := by
  have cost := scan_fuel_bound r.remaining r n budget formula matching variables
  have product := Nat.mul_le_mul_left (bodyBound.eval n+1) (show r.remaining.length ≤ n by omega)
  rw [loopBound_eval]
  exact Nat.le_trans cost (Nat.add_le_add_right product 1)

end PNP.Concrete.NormalizerBlocks.Recovery
