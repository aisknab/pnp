/-
Copyright (c) 2026 PNP Labs.

Finite trace-node conversion into matching-table entries. The actual parsed
node tag selects absence or a unary variable index. Existing clause
serialization is reused, with the complete trace suffix protected.
-/
import PNP.Concrete.NormalizerSeenData

namespace PNP.Concrete.NormalizerBlocks.SeenTrace
open BitRegister
abbrev State := TracePath.State

def prepare : Block 23 := .seq (.action (.copy 1 20)) (.action (.copy 3 21))
def prepared (r : State) : State := r.withRegisters {r.registers with target := r.core.currentIndex, excess := r.buffer}
theorem prepare_exec (r : State) : Exec prepare r.store 2 (prepared r).store :=
  Exec.seq (.action _ _) (.action _ _)

def emitNone : Block 23 := TracePath.liftCore (.seq (ClauseQuery.emit false true) (ClauseQuery.emit true false))
def noneEmitted (r : State) : State := r.withRegisters (ClauseQuery.emitted true false (ClauseQuery.emitted false true r.registers))
theorem emitNone_exec (r : State) : Exec emitNone r.store 4 (noneEmitted r).store :=
  TracePath.liftCore_exec _ r _ _
    (Exec.seq (ClauseQuery.emit_exec false true r.registers) (ClauseQuery.emit_exec true false (ClauseQuery.emitted false true r.registers)))

def emitSome : Block 23 := TracePath.liftCore (SearchVertices.emitEntry true)
def someEmitted (r : State) : State := r.withRegisters (SearchVertices.emitted true r.registers)
theorem emitSome_exec (r : State) :
    Exec emitSome r.store (4 * r.registers.target.length + 10) (someEmitted r).store :=
  TracePath.liftCore_exec _ r _ _ (SearchVertices.emitEntry_exec true r.registers)

def choose : Block 23 := .branch 14 emitSome emitSome emitNone
def chosen (r : State) : State := if ForwardEdge.present r.core.graph.first then noneEmitted r else someEmitted r
def chooseFuel (r : State) : Nat := 1 + if ForwardEdge.present r.core.graph.first then 4 else 4 * r.registers.target.length + 10
theorem choose_exec (r : State) : Exec choose r.store (chooseFuel r) (chosen r).store := by
  have checked := EdgeKinds.branch_head (14 : Fin 23) r.store emitSome emitNone (4 * r.registers.target.length + 10) 4
    (someEmitted r).store (noneEmitted r).store (emitSome_exec r) (emitNone_exec r)
  change Exec choose r.store (chooseFuel r)
    (if ForwardEdge.present r.core.graph.first then (noneEmitted r).store else (someEmitted r).store) at checked
  cases tag : ForwardEdge.present r.core.graph.first <;>
    simpa only [chosen, tag, Bool.false_eq_true, ite_false, ite_true] using checked

def save : Block 23 := .action (.copy (Frame.frameIndex 21 (0 : Fin 2)) (Frame.index 2 (3 : Fin 21)))
def saved (r : State) : State := {r with buffer := r.registers.excess}
theorem save_exec (r : State) : Exec save r.store 1 (saved r).store := by
  have buffer : r.core.store.get (3 : Fin 21) = r.registers.excess := rfl
  have checked := Exec.action (.copy (Frame.frameIndex 21 (0 : Fin 2)) (Frame.index 2 (3 : Fin 21))) r.store
  simpa only [save, Action.update, Action.instruction, Instruction.update, TracePath.State.store,
    Frame.get_core, Frame.set_frame, buffer, TracePath.State.frame, saved, Store.set, Store.indexCases] using checked

def appendEntry : Block 23 := .seq prepare (.seq choose save)
def entryAppended (r : State) : State := saved (chosen (prepared r))
def appendFuel (r : State) : Nat := 2 + (chooseFuel (prepared r) + 1)
theorem appendEntry_exec (r : State) : Exec appendEntry r.store (appendFuel r) (entryAppended r).store :=
  Exec.seq (prepare_exec r) (Exec.seq (choose_exec (prepared r)) (save_exec (chosen (prepared r))))

theorem entryAppended_buffer (r : State) :
    (entryAppended r).buffer =
      (entryBytes (entry ⟨ForwardEdge.present r.core.graph.first, r.core.currentIndex.length⟩)).reverse ++ r.buffer := by
  cases tag : ForwardEdge.present r.core.graph.first <;>
    simp only [entryAppended, chosen, prepared, TracePath.State.withRegisters, TracePath.State.withCore,
      ParentQuery.State.withRegisters, TracePath.State.registers, ParentQuery.State.registers,
      tag, Bool.false_eq_true, ite_false, ite_true, entry]
  · rw [entryBytes_some]
    rfl
  · rw [entryBytes_none]
    rfl

theorem entryAppended_preserves (r : State) :
    (entryAppended r).core.pending = r.core.pending ∧
      (entryAppended r).core.graph.core.formula = r.core.graph.core.formula ∧
        (entryAppended r).core.graph.core.matching = r.core.graph.core.matching := by
  cases tag : ForwardEdge.present (prepared r).core.graph.first <;>
    simp only [entryAppended, chosen, tag, Bool.false_eq_true, ite_false, ite_true] <;> exact ⟨rfl, rfl, rfl⟩

theorem appendFuel_bound (r : State) : appendFuel r ≤ 4 * r.core.currentIndex.length + 14 := by
  change 2 + ((1 + if ForwardEdge.present r.core.graph.first then 4 else 4 * r.core.currentIndex.length + 10) + 1) ≤ _
  cases tag : ForwardEdge.present r.core.graph.first <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

def body : Block 23 := .seq TracePath.readNode appendEntry
def bodyResult (r : State) : State := entryAppended (TracePath.nodeRead r)
def bodyFuel (r : State) : Nat := TracePath.nodeFuel r + appendFuel (TracePath.nodeRead r)
theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (bodyResult r).store :=
  Exec.seq (TracePath.readNode_exec r) (appendEntry_exec (TracePath.nodeRead r))

theorem body_pending (r : State) : (bodyResult r).core.pending = TraceData.next r.core.pending :=
  (entryAppended_preserves _).1.trans (ParentQuery.node_fields r.core).1
theorem body_shorter (r : State) (nonempty : r.core.pending ≠ []) :
    (bodyResult r).core.pending.length < r.core.pending.length := by
  rw [body_pending]
  exact TraceData.next_shorter _ nonempty
def stepBound (r : State) : Nat := 28 * r.core.pending.length + 79
theorem bodyFuel_bound (r : State) : bodyFuel r ≤ stepBound r := by
  have read := TracePath.nodeFuel_bound r
  have append := appendFuel_bound (TracePath.nodeRead r)
  rw [(TracePath.nodeRead_fields r).1, (ParentQuery.node_fields r.core).2.1] at append
  have index := TraceData.nodeIndex_length r.core.pending
  unfold bodyFuel stepBound
  omega
theorem stepBound_mono (r : State) (nonempty : r.core.pending ≠ []) :
    stepBound (bodyResult r) ≤ stepBound r := by
  have shorter := body_shorter r nonempty
  unfold stepBound
  omega

theorem body_preserves (r : State) :
    (bodyResult r).core.graph.core.formula = r.core.graph.core.formula ∧
      (bodyResult r).core.graph.core.matching = r.core.graph.core.matching :=
  ⟨(entryAppended_preserves _).2.1, (entryAppended_preserves _).2.2⟩

theorem body_canonical (r : State) (row : TraceData.Row) (suffix : BitString)
    (read : r.core.pending = TraceData.row row suffix) :
    (bodyResult r).core.pending = suffix ∧
      (bodyResult r).buffer = (entryBytes (entry row.1)).reverse ++ r.buffer := by
  have node := TracePath.nodeRead_canonical r row suffix read
  refine ⟨?_, ?_⟩
  · rw [body_pending, read, TraceData.next_canonical]
  · rw [bodyResult, entryAppended_buffer, node.2.2.1, List.length_replicate, node.2.2.2]
    rfl

end PNP.Concrete.NormalizerBlocks.SeenTrace
