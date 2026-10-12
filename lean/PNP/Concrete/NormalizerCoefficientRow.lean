/-
Copyright (c) 2026 PNP Labs.

Append one tagged row in exact unary row-codec order. The count and reversed
byte buffer are updated together. Runtime work includes the full row index;
no unbounded encoded coordinate is treated as a constant-time operation.
-/
import PNP.Concrete.NormalizerCoefficientState

namespace PNP.Concrete.NormalizerBlocks.CoefficientRow
open BitRegister Occurrence
abbrev State := CompactClause.State
def bits (index : Nat) (tag : Bool) : BitString := List.replicate index true ++ [false,tag]
def step : Block 13 := .seq (.action (.pop 1)) (.action (.push 11 true))
def loop : Block 13 := .loop 1 step
def drained (word : BitString) (r : State) : State :=
  {r with core := {r.core with target := []}, buffer := List.replicate word.length true ++ r.buffer}
theorem drain_exec (word : BitString) (r : State) :
    Exec loop (r.withCore {r.core with target := word}).store
      (3 * word.length + 1) (drained word r).store := by
  induction word generalizing r with
  | nil => exact Exec.loopStop (source := (1 : Fin 13)) rfl
  | cons bit rest ih =>
      have cost : 3 * (bit::rest).length + 1 = 1 + (2 + (3 * rest.length + 1)) := by
        simp only [List.length_cons]
        omega
      rw [cost]
      let next : State := {r with core := {r.core with target := rest},buffer := true::r.buffer}
      have body : Exec step (r.withCore {r.core with target := bit::rest}).store 2 next.store :=
        Exec.seq (.action _ _) (.action _ _)
      have checked := Exec.loopStep (source := (1 : Fin 13)) rfl body (ih next)
      simpa only [loop,drained,next,CompactClause.State.withCore,List.length_cons,
        List.replicate_succ',List.append_assoc,List.cons_append,List.nil_append] using checked
def finish (tag : Bool) : Block 13 :=
  .seq (.action (.push 11 false)) (.seq (.action (.push 11 tag)) (.action (.push 10 true)))
def finished (tag : Bool) (r : State) : State :=
  {r with variables := true::r.variables, buffer := tag::false::r.buffer}
theorem finish_exec (tag : Bool) (r : State) :
    Exec (finish tag) r.store 3 (finished tag r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
def emit (tag : Bool) : Block 13 := .seq loop (finish tag)
def result (tag : Bool) (r : State) : State := finished tag (drained r.core.target r)
def fuel (r : State) : Nat := 3 * r.core.target.length + 4
theorem emit_exec (tag : Bool) (r : State) :
    Exec (emit tag) r.store (fuel r) (result tag r).store := by
  have checked := Exec.seq (drain_exec r.core.target r) (finish_exec tag (drained r.core.target r))
  simpa only [emit,result,fuel,Nat.add_assoc,Nat.reduceAdd,CompactClause.State.withCore] using checked
theorem result_buffer (tag : Bool) (r : State) :
    (result tag r).buffer = (bits r.core.target.length tag).reverse ++ r.buffer := by
  simp only [result,finished,drained,bits,List.reverse_append,List.reverse_cons,
    List.reverse_nil,List.reverse_replicate,List.cons_append,List.nil_append]
theorem result_count (tag : Bool) (r : State) : (result tag r).variables = true::r.variables := rfl
theorem bits_length (index : Nat) (tag : Bool) : (bits index tag).length = index+2 := by
  simp only [bits,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
theorem result_fields (tag : Bool) (r : State) :
    (result tag r).pending = r.pending ∧ (result tag r).positive = r.positive := ⟨rfl,rfl⟩

end PNP.Concrete.NormalizerBlocks.CoefficientRow

namespace PNP.Concrete.NormalizerBlocks.Coefficient
open BitRegister Occurrence
def emit (tag : Bool) : Block 24 := liftDense (Frame.block 3 (CoefficientRow.emit tag))
def emitted (tag : Bool) (r : State) : State :=
  r.withDense {r.core.core with core := CoefficientRow.result tag r.core.core.core}
def emitFuel (r : State) : Nat := CoefficientRow.fuel r.core.core.core
theorem emit_exec (tag : Bool) (r : State) :
    Exec (emit tag) r.store (emitFuel r) (emitted tag r).store :=
  liftDense_exec _ r _ _ (Frame.execution (CoefficientRow.emit_exec tag r.core.core.core) r.core.core.frame)
theorem emitted_data (tag : Bool) (r : State) : (emitted tag r).data = r.data := rfl
theorem emitted_indices (tag : Bool) (r : State) :
    (emitted tag r).variableIndex = r.variableIndex ∧ (emitted tag r).auxiliary = r.auxiliary := ⟨rfl,rfl⟩
theorem emitted_buffers (tag : Bool) (r : State) :
    (emitted tag r).count = true::r.count ∧
    (emitted tag r).buffer = (CoefficientRow.bits r.registers.target.length tag).reverse ++ r.buffer :=
  ⟨rfl,CoefficientRow.result_buffer tag r.core.core.core⟩
def loadRow (index : Index) : Block 24 := .action (.copy 1 (indexRegister index))
def rowLoaded (index : Index) (r : State) : State :=
  r.withRegisters {r.registers with target := indexWord index r}
theorem loadRow_exec (index : Index) (r : State) :
    Exec (loadRow index) r.store 1 (rowLoaded index r).store := by
  cases index <;> exact .action _ _
def emitIndex (index : Index) (tag : Bool) : Block 24 := .seq (loadRow index) (emit tag)
def indexEmitted (index : Index) (tag : Bool) (r : State) : State := emitted tag (rowLoaded index r)
def emitIndexFuel (index : Index) (r : State) : Nat := 1 + emitFuel (rowLoaded index r)
theorem emitIndex_exec (index : Index) (tag : Bool) (r : State) :
    Exec (emitIndex index tag) r.store (emitIndexFuel index r) (indexEmitted index tag r).store :=
  Exec.seq (loadRow_exec index r) (emit_exec tag (rowLoaded index r))
theorem emitIndexFuel_eq (index : Index) (r : State) :
    emitIndexFuel index r = 3 * (indexWord index r).length + 5 := by
  change 1 + (3 * (indexWord index r).length + 4) = _
  omega
def loadAnswer : Block 24 := .seq (.action (.copy 1 8)) (.action (.pop 1))
def answerLoaded (r : State) : State := r.withRegisters {r.registers with target := r.registers.output.tail}
theorem loadAnswer_exec (r : State) : Exec loadAnswer r.store 2 (answerLoaded r).store :=
  Exec.seq (.action _ _) (.action _ _)
def emitAnswer (tag : Bool) : Block 24 := .seq loadAnswer (emit tag)
def answerEmitted (tag : Bool) (r : State) : State := emitted tag (answerLoaded r)
def emitAnswerFuel (r : State) : Nat := 2 + emitFuel (answerLoaded r)
theorem emitAnswer_exec (tag : Bool) (r : State) :
    Exec (emitAnswer tag) r.store (emitAnswerFuel r) (answerEmitted tag r).store :=
  Exec.seq (loadAnswer_exec r) (emit_exec tag (answerLoaded r))
theorem emitAnswerFuel_bound (r : State) :
    emitAnswerFuel r ≤ 3 * r.registers.output.length + 6 := by
  have tail := ParentQuery.input_tail_bound r.registers.output
  change 2 + (3 * r.registers.output.tail.length + 4) ≤ _
  omega

end PNP.Concrete.NormalizerBlocks.Coefficient
