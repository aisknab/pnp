/-
Copyright (c) 2026 PNP Labs.

Concrete discovery transition. Restore the remaining vertex bytes, prepend
the selected vertex and computed optional parent to the old trace, then
consume one unit of the protected outer countdown.
-/

import PNP.Concrete.NormalizerExplorationState

namespace PNP.Concrete.NormalizerBlocks.Extraction
theorem parentPacked_frame (r : State) :
    (parentPacked r).parent.graph.core.formula = r.parent.graph.core.formula ∧
      (parentPacked r).parent.graph.core.matching = r.parent.graph.core.matching ∧
        (parentPacked r).pending = r.pending ∧ (parentPacked r).trace = r.trace := by
  cases tag : ForwardEdge.present (parentBegun r).registers.sign <;>
    simp only [parentPacked, parentChosen, tag, Bool.false_eq_true, ite_false, ite_true] <;>
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem vertexPacked_input (r : State) :
    (vertexPacked r).registers.input = true :: TraceData.vertex
      ⟨ForwardEdge.present r.parent.targetTag, r.parent.targetIndex.length⟩ r.registers.input := rfl
end PNP.Concrete.NormalizerBlocks.Extraction

namespace PNP.Concrete.NormalizerBlocks.Frame
open BitRegister
theorem set_frame {extra count : Nat} (core : Store count) (frame : Store extra)
    (destination : Fin extra) (value : BitString) :
    (join core frame).set (frameIndex count destination) value = join core (frame.set destination value) := by
  induction core with
  | nil =>
      have position : frameIndex 0 destination = destination := by
        apply Fin.ext
        simp only [frameIndex, Nat.zero_add]
      rw [position]
      rfl
  | @cons count first rest ih =>
      have position : frameIndex (count + 1) destination = (frameIndex count destination).succ := by
        apply Fin.ext
        change count + 1 + destination.val = count + destination.val + 1
        omega
      rw [position]
      exact congrArg (Store.cons first) ih
end PNP.Concrete.NormalizerBlocks.Frame

namespace PNP.Concrete.NormalizerBlocks.Exploration
open BitRegister

def packRemaining : Block 28 := lift Extraction.packRemaining
def remainingPacked (r : State) : State := r.withCore (Extraction.remainingPacked r.core)
theorem packRemaining_exec (r : State) :
    Exec packRemaining r.store (4 * r.core.skipped.length + 4) (remainingPacked r).store :=
  lift_exec _ r _ _ (Extraction.packRemaining_exec r.core)

def savePending : Block 28 := lift Extraction.savePending
def pendingSaved (r : State) : State := r.withCore (Extraction.pendingSaved r.core)
theorem savePending_exec (r : State) : Exec savePending r.store 1 (pendingSaved r).store :=
  lift_exec _ r _ _ (Extraction.savePending_exec r.core)

def copyTraceInput : Block 28 := .action (.copy 0 24)
def traceCopied (r : State) : State := r.withRegisters {r.registers with input := r.core.trace}
theorem copyTraceInput_exec (r : State) : Exec copyTraceInput r.store 1 (traceCopied r).store := .action _ _

def packParent : Block 28 := lift Extraction.packParent
def parentPacked (r : State) : State := r.withCore (Extraction.parentPacked r.core)
theorem packParent_exec (r : State) :
    Exec packParent r.store (Extraction.packParentFuel r.core) (parentPacked r).store :=
  lift_exec _ r _ _ (Extraction.packParent_exec r.core)

def packVertex : Block 28 := lift Extraction.packVertex
def vertexPacked (r : State) : State := r.withCore (Extraction.vertexPacked r.core)
theorem packVertex_exec (r : State) :
    Exec packVertex r.store (Extraction.packVertexFuel r.core) (vertexPacked r).store :=
  lift_exec _ r _ _ (Extraction.packVertex_exec r.core)

def popInput : Block 28 := .action (.pop 0)
def inputPopped (r : State) : State := r.withRegisters {r.registers with input := r.registers.input.tail}
theorem popInput_exec (r : State) : Exec popInput r.store 1 (inputPopped r).store := .action _ _

def saveTrace : Block 28 := .action (.copy 24 0)
def traceSaved (r : State) : State := r.withCore {r.core with trace := r.registers.input}
theorem saveTrace_exec (r : State) : Exec saveTrace r.store 1 (traceSaved r).store := .action _ _

def consume : Block 28 := .action (.pop (Frame.frameIndex 27 (0 : Fin 1)))
def consumed (r : State) : State := {r with remaining := r.remaining.tail}
theorem consume_exec (r : State) : Exec consume r.store 1 (consumed r).store := by
  have checked := Exec.action (.pop (Frame.frameIndex 27 (0 : Fin 1))) r.store
  simpa only [consume, Action.update, Action.instruction, Instruction.update, State.store,
    Frame.get_frame, Frame.set_frame, State.frame, consumed,
    Store.get, Store.set, Store.indexCases] using checked

def ready (r : State) : State := traceCopied (pendingSaved (remainingPacked r))
def packed (r : State) : State := vertexPacked (parentPacked (ready r))
def accepted (r : State) : State := consumed (traceSaved (inputPopped (packed r)))
def accept : Block 28 :=
  .seq packRemaining <| .seq savePending <| .seq copyTraceInput <|
    .seq packParent <| .seq packVertex <| .seq popInput (.seq saveTrace consume)
def acceptFuel (r : State) : Nat :=
  (4 * r.core.skipped.length + 4) + (1 + (1 + (Extraction.packParentFuel (ready r).core +
    (Extraction.packVertexFuel (parentPacked (ready r)).core + (1 + (1 + 1))))))

theorem accept_exec (r : State) : Exec accept r.store (acceptFuel r) (accepted r).store :=
  Exec.seq (packRemaining_exec r) <| Exec.seq (savePending_exec (remainingPacked r)) <|
    Exec.seq (copyTraceInput_exec (pendingSaved (remainingPacked r))) <|
      Exec.seq (packParent_exec (ready r)) <| Exec.seq (packVertex_exec (parentPacked (ready r))) <|
        Exec.seq (popInput_exec (packed r)) <| Exec.seq (saveTrace_exec (inputPopped (packed r)))
          (consume_exec (traceSaved (inputPopped (packed r))))

theorem accepted_fields (r : State) :
    (accepted r).core.parent.graph.core.formula = r.core.parent.graph.core.formula ∧
      (accepted r).core.parent.graph.core.matching = r.core.parent.graph.core.matching ∧
        (accepted r).core.pending = r.core.skipped.reverse ++ r.core.pending ∧
          (accepted r).remaining = r.remaining.tail := by
  have frame := Extraction.parentPacked_frame (ready r).core
  exact ⟨frame.1, frame.2.1, frame.2.2.1, rfl⟩

theorem accepted_trace_bytes (r : State) :
    (accepted r).core.trace = TraceData.vertex
      ⟨ForwardEdge.present r.core.parent.targetTag, r.core.parent.targetIndex.length⟩
        (Extraction.parentBytes r.core.parent.output r.core.trace) := by
  have fields := Extraction.parentPacked_fields (ready r).core
  change (Extraction.vertexPacked (Extraction.parentPacked (ready r).core)).registers.input.tail = _
  rw [Extraction.vertexPacked_input, fields.1, fields.2.1, Extraction.parentPacked_input]
  rfl

theorem acceptFuel_bound (r : State) :
    acceptFuel r ≤ 4 * r.core.skipped.length + 3 * r.core.parent.output.length +
      3 * r.core.parent.targetIndex.length + 29 := by
  have parent := Extraction.packParentFuel_bound (ready r).core
  change Extraction.packParentFuel (ready r).core ≤ 3 * r.core.parent.output.length + 12 at parent
  have index := (Extraction.parentPacked_fields (ready r).core).1
  unfold acceptFuel Extraction.packVertexFuel
  change (4 * r.core.skipped.length + 4) +
    (1 + (1 + (Extraction.packParentFuel (ready r).core +
      (3 * (Extraction.parentPacked (ready r).core).parent.targetIndex.length + 8 + (1 + (1 + 1)))))) ≤ _
  rw [index]
  change (4 * r.core.skipped.length + 4) +
    (1 + (1 + (Extraction.packParentFuel (ready r).core +
      (3 * r.core.parent.targetIndex.length + 8 + (1 + (1 + 1)))))) ≤ _
  omega

theorem accepted_selected (r : State) (vertex : CNFLiteral) (parent : Option CNFLiteral)
    (remaining : List CNFLiteral) (trace : List TraceData.Row)
    (selected : Extraction.Selected r.core vertex parent remaining)
    (traceRead : r.core.trace = TraceData.encode trace) :
    (accepted r).core.pending = SearchVertices.encodeVertices remaining ∧
      (accepted r).core.trace = TraceData.encode ((vertex, parent) :: trace) := by
  constructor
  · exact (accepted_fields r).2.2.1.trans selected.remainingRead
  · rw [accepted_trace_bytes, selected.indexRead, List.length_replicate, selected.tagRead,
      selected.parentRead, traceRead, Extraction.parentBytes_canonical]
    rfl

end PNP.Concrete.NormalizerBlocks.Exploration
