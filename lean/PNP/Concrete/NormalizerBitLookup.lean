/-
Copyright (c) 2026 PNP Labs.

Indexed access to a computed assignment. The index is a runtime unary
word, including malformed words; an out-of-range read returns false.
-/
import PNP.Concrete.NormalizerTraceCount

namespace PNP.Concrete.NormalizerBlocks.BitLookup
open BitRegister Occurrence

def step : Block 9 := .seq (.action (.pop 1)) (.action (.pop 0))
theorem step_exec (r : Registers) :
    Exec step r.store 2 ({r with target := r.target.tail, input := r.input.tail}).store := by
  cases r
  exact Exec.seq (.action _ _) (.action _ _)
def loop : Block 9 := .loop 1 step
def drained (word : BitString) (r : Registers) : Registers :=
  {r with input := r.input.drop word.length, target := []}
theorem tail_drop (word : BitString) (n : Nat) :
    word.tail.drop n = word.drop (n + 1) := by
  cases word with
  | nil => simp only [List.tail_nil,List.drop_nil]
  | cons bit rest => rfl
theorem drain_exec (word : BitString) (r : Registers) :
    Exec loop ({r with target := word}).store (3 * word.length + 1) (drained word r).store := by
  induction word generalizing r with
  | nil => exact Exec.loopStop (source := (1 : Fin 9)) rfl
  | cons bit rest ih =>
      have cost : 3 * (bit::rest).length + 1 = 1 + (2 + (3 * rest.length + 1)) := by
        simp only [List.length_cons]
        omega
      rw [cost]
      have checked := Exec.loopStep (source := (1 : Fin 9)) (body := step) rfl
        (step_exec {r with target := bit::rest})
        (ih {r with input := r.input.tail, target := rest})
      simpa only [loop,drained,List.length_cons,tail_drop] using checked

def emitHead : Block 9 := .branch 0 (TraceCount.emit false)
  (TraceCount.emit false) (TraceCount.emit true)
def headEmitted (r : Registers) : Registers := {r with output := [r.input.headD false]}
theorem emitHead_exec (r : Registers) : Exec emitHead r.store 3 (headEmitted r).store := by
  have checked := EdgeKinds.branch_head (0 : Fin 9) r.store
    (TraceCount.emit false) (TraceCount.emit true) 2 2
    (TraceCount.emitted false r).store (TraceCount.emitted true r).store
    (TraceCount.emit_exec false r) (TraceCount.emit_exec true r)
  change Exec emitHead r.store (1 + if r.input.headD false then 2 else 2)
    (if r.input.headD false then (TraceCount.emitted true r).store else
      (TraceCount.emitted false r).store) at checked
  cases h : r.input.headD false <;>
    simpa only [headEmitted,TraceCount.emitted,h,Bool.false_eq_true,ite_false,ite_true] using checked

def read : Block 9 := .seq loop emitHead
def result (r : Registers) : Registers := headEmitted (drained r.target r)
def fuel (r : Registers) : Nat := 3 * r.target.length + 4
theorem read_exec (r : Registers) : Exec read r.store (fuel r) (result r).store := by
  have checked := Exec.seq (drain_exec r.target r) (emitHead_exec (drained r.target r))
  simpa only [read,result,fuel,Nat.add_assoc,Nat.reduceAdd] using checked
theorem head_drop (word : BitString) (n : Nat) :
    (word.drop n).headD false = word[n]?.getD false := by
  induction n generalizing word with
  | zero => cases word <;> rfl
  | succ n ih =>
      cases word with
      | nil => rfl
      | cons bit rest => exact ih rest
theorem result_output (r : Registers) :
    (result r).output = [r.input[r.target.length]?.getD false] :=
  congrArg (fun bit => [bit]) (head_drop r.input r.target.length)
theorem result_target (r : Registers) : (result r).target = [] := rfl
theorem canonical (r : Registers) (index : Nat)
    (target : r.target = List.replicate index true) :
    (result r).output = [r.input[index]?.getD false] := by
  rw [result_output,target,List.length_replicate]

end PNP.Concrete.NormalizerBlocks.BitLookup
