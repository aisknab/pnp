/-
Copyright (c) 2026 PNP Labs.

Initialize, enumerate and return every candidate bit in source order.
The semantic reader hypothesis below is proof-only: source integration must
discharge it from the input-derived cache, never accept it as runtime data.
-/
import PNP.Concrete.NormalizerCandidateBitsLoop

namespace PNP.Concrete.NormalizerBlocks.CandidateBits
open BitRegister Occurrence

def values (sigma : Nat → Bool) (first : Nat) : Nat → BitString
  | 0 => []
  | count + 1 => sigma first :: values sigma (first + 1) count
def ReaderCorrect (literals owners slots : BitString) (limit : Nat) (sigma : Nat → Bool) : Prop :=
  ∀ (r : CacheSigma.State) (i : Nat), i < limit →
    r.core.formula = literals → r.matching = owners → r.counter = slots →
    r.core.index = List.replicate i true → (CacheSigma.result r).registers.output = [sigma i]
theorem scan_buffer (word : BitString) (r : State) (literals owners slots : BitString)
    (limit first : Nat) (sigma : Nat → Bool) (correct : ReaderCorrect literals owners slots limit sigma)
    (within : first + word.length ≤ limit) (counter : r.counter = List.replicate first true)
    (literalRead : r.core.core.formula = literals) (ownerRead : r.core.matching = owners)
    (slotRead : r.core.counter = slots) :
    (scan word r).state.buffer = (values sigma first word.length).reverse ++ r.buffer := by
  induction word generalizing r first with
  | nil => rfl
  | cons bit rest ih =>
      let before := {r with remaining := bit::rest}
      have index : first < limit := by simp only [List.length_cons] at within; omega
      have computed := correct (loaded before).core first index literalRead ownerRead slotRead counter
      have step := body_fields before
      have counterNext : (bodyResult before).counter = List.replicate (first + 1) true := by
        rw [step.2.2.2.2]
        change true::r.counter = _
        rw [counter,List.replicate_succ]
      have tail := ih (bodyResult before) (first + 1)
        (by simp only [List.length_cons] at within; omega) counterNext
        (step.1.trans literalRead) (step.2.1.trans ownerRead) (step.2.2.1.trans slotRead)
      change (scan rest (bodyResult before)).state.buffer = _
      rw [tail,body_buffer,computed]
      simp only [ForwardEdge.present,List.length_cons,values,List.reverse_cons,List.append_assoc,
        List.cons_append,List.nil_append,List.headD_cons]
      rfl
theorem values_ofFn (sigma : Nat → Bool) (first count : Nat) :
    values sigma first count = List.ofFn (fun i : Fin count => sigma (first + i.val)) := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
      rw [values,ih,List.ofFn_succ]
      simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
      apply congrArg (List.cons (sigma first))
      apply congrArg List.ofFn
      funext i
      apply congrArg sigma
      omega

def start : Block 22 := .seq (.action (.clear 20)) (.action (.clear 21))
def started (r : State) : State := {r with counter := [],buffer := []}
theorem start_exec (r : State) : Exec start r.store 2 (started r).store :=
  Exec.seq (.action _ _) (.action _ _)
def front : Block 22 := .seq start loop
def frontResult (r : State) : State := (whole (started r)).state
def frontSteps (r : State) : Nat := 2 + (whole (started r)).fuel
theorem front_exec (r : State) : Exec front r.store (frontSteps r) (frontResult r).store :=
  Exec.seq (start_exec r) (whole_exec (started r))
def prepareFinish : Block 22 := .seq (.action (.copy 3 21)) (.action (.clear 8))
def finishPrepared (r : State) : State :=
  r.withCore (r.core.withRegisters {r.registers with excess := r.buffer,output := []})
theorem prepareFinish_exec (r : State) : Exec prepareFinish r.store 2 (finishPrepared r).store :=
  Exec.seq (.action _ _) (.action _ _)
def finish : Block 22 :=
  .seq prepareFinish (liftCore (CacheMode.liftCore ClauseQuery.reverseLoop))
def finished (r : State) : State :=
  r.withCore (r.core.withRegisters {r.registers with excess := [],output := r.buffer.reverse})
def finishFuel (r : State) : Nat := 4 * r.buffer.length + 3
theorem finish_exec (r : State) : Exec finish r.store (finishFuel r) (finished r).store := by
  have reverse := ClauseQuery.reverse_exec (finishPrepared r).registers r.buffer
  change Exec ClauseQuery.reverseLoop (finishPrepared r).registers.store (4 * r.buffer.length + 1)
    ({r.registers with excess := [],output := r.buffer.reverse ++ []}).store at reverse
  rw [List.append_nil] at reverse
  have lifted := liftCore_exec _ (finishPrepared r) _ _
    (CacheMode.liftCore_exec _ (finishPrepared r).core _ _ reverse)
  have checked := Exec.seq (prepareFinish_exec r) lifted
  change Exec finish r.store (2 + (4 * r.buffer.length + 1)) (finished r).store at checked
  have cost : 2 + (4 * r.buffer.length + 1) = finishFuel r := by unfold finishFuel; omega
  rw [cost] at checked
  exact checked
def call : Block 22 := .seq front finish
def called (r : State) : State := finished (frontResult r)
def callSteps (r : State) : Nat := frontSteps r + finishFuel (frontResult r)
theorem call_exec (r : State) : Exec call r.store (callSteps r) (called r).store :=
  Exec.seq (front_exec r) (finish_exec (frontResult r))
theorem called_fields (r : State) :
    (called r).core.core.formula = r.core.core.formula ∧
    (called r).core.matching = r.core.matching ∧ (called r).core.counter = r.core.counter :=
  ⟨(scan_fields r.remaining (started r)).1,(scan_fields r.remaining (started r)).2.1,
    (scan_fields r.remaining (started r)).2.2.1⟩
theorem called_output_length (r : State) :
    (called r).registers.output.length = r.remaining.length := by
  change (frontResult r).buffer.reverse.length = _
  rw [List.length_reverse]
  have length := scan_buffer_length r.remaining (started r)
  change (frontResult r).buffer.length = r.remaining.length + 0 at length
  simpa only [Nat.add_zero] using length
theorem called_canonical (r : State) (literals owners slots : BitString) (count : Nat)
    (sigma : Nat → Bool) (correct : ReaderCorrect literals owners slots count sigma)
    (remaining : r.remaining.length = count) (literalRead : r.core.core.formula = literals)
    (ownerRead : r.core.matching = owners) (slotRead : r.core.counter = slots) :
    (called r).registers.output = List.ofFn (fun i : Fin count => sigma i.val) := by
  have checked := scan_buffer r.remaining (started r) literals owners slots count 0 sigma correct
    (by omega) rfl literalRead ownerRead slotRead
  change (frontResult r).buffer = _ ++ [] at checked
  rw [List.append_nil,remaining] at checked
  change (frontResult r).buffer.reverse = _
  rw [checked,List.reverse_reverse,values_ofFn]
  simp only [Nat.zero_add]
def callBound : NatPolynomial := .add loopBound (.linear 4 5)
theorem callSteps_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    callSteps r ≤ callBound.eval n := by
  have cursor := Store.get_length_le r.store (19 : Fin 22) bounded
  have formula := Store.get_length_le r.store (13 : Fin 22) bounded
  have owners := Store.get_length_le r.store (16 : Fin 22) bounded
  have slots := Store.get_length_le r.store (17 : Fin 22) bounded
  change r.remaining.length ≤ n at cursor
  change r.core.core.formula.length ≤ n at formula
  change r.core.matching.length ≤ n at owners
  change r.core.counter.length ≤ n at slots
  have budget : (started r).counter.length + (started r).remaining.length ≤ n := by
    change 0 + r.remaining.length ≤ n
    omega
  have cost := whole_fuel_bound (started r) n budget formula owners slots
  have length := scan_buffer_length r.remaining (started r)
  change (frontResult r).buffer.length = r.remaining.length + 0 at length
  change callSteps r ≤ loopBound.eval n + (4 * n + 5)
  unfold callSteps frontSteps finishFuel
  omega

end PNP.Concrete.NormalizerBlocks.CandidateBits
