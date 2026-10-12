/-
Copyright (c) 2026 PNP Labs.

Reuse of the complete eligibility controller with a protected full trace,
and stable re-emission of a rejected vertex. No caller supplies membership,
roothood or adjacency answers. Rejected entries accumulate in reverse byte
order so a later linear pass restores the original vertex order.
-/

import PNP.Concrete.NormalizerExtractRead

namespace PNP.Concrete.NormalizerBlocks.ParentQuery
theorem phase_preserves (r : State) :
    (phaseResult r).targetIndex = r.targetIndex ∧ (phaseResult r).targetTag = r.targetTag ∧
      (phaseResult r).graph.core.formula = r.graph.core.formula ∧
        (phaseResult r).graph.core.matching = r.graph.core.matching := by
  have first := first_preserves r
  have tail := scan_preserves ((firstResult r).pending.length + 1) (firstResult r)
  exact ⟨tail.1.trans first.1, tail.2.1.trans first.2.1,
    tail.2.2.1.trans first.2.2.1, tail.2.2.2.trans first.2.2.2⟩
end PNP.Concrete.NormalizerBlocks.ParentQuery

namespace PNP.Concrete.NormalizerBlocks.Eligibility
theorem phase_preserves (r : State) :
    (phaseResult r).core.targetIndex = r.core.targetIndex ∧
      (phaseResult r).core.targetTag = r.core.targetTag ∧
        (phaseResult r).core.graph.core.formula = r.core.graph.core.formula ∧
          (phaseResult r).core.graph.core.matching = r.core.graph.core.matching := by
  cases seen : ForwardEdge.present (memberResult (saved r)).core.output with
  | false =>
      have stable := restored_fields r
      have parent := ParentQuery.phase_preserves (restored (memberResult (saved r))).core
      simp only [phaseResult, dispatchResult, seen, Bool.false_eq_true, ite_false, parentResult]
      exact ⟨parent.1.trans stable.1, parent.2.1.trans stable.2.1,
        parent.2.2.1.trans stable.2.2.1, parent.2.2.2.trans stable.2.2.2.1⟩
  | true =>
      simp only [phaseResult, dispatchResult, seen, ite_true, rejected, ParentQuery.defaulted]
      exact TraceMember.phase_preserves r.core
end PNP.Concrete.NormalizerBlocks.Eligibility

namespace PNP.Concrete.NormalizerBlocks.Extraction
open BitRegister

def restoreTrace : Block 27 := .action (.copy 16 24)
def traceRestored (r : State) : State := r.withParent {r.parent with pending := r.trace}
theorem restoreTrace_exec (r : State) : Exec restoreTrace r.store 1 (traceRestored r).store := .action _ _

def eligibility : Block 27 := Frame.block 5 Eligibility.phase
def eligibilityResult (r : State) : State := {r with core := Eligibility.phaseResult r.core}
theorem eligibility_exec (r : State) :
    Exec eligibility r.store (Eligibility.phaseFuel r.core) (eligibilityResult r).store :=
  Frame.execution (Eligibility.phase_exec r.core) r.frame

def query : Block 27 := .seq restoreTrace eligibility
def queried (r : State) : State := eligibilityResult (traceRestored r)
def queryFuel (r : State) : Nat := 1 + Eligibility.phaseFuel (traceRestored r).core
theorem query_exec (r : State) : Exec query r.store (queryFuel r) (queried r).store :=
  Exec.seq (restoreTrace_exec r) (eligibility_exec (traceRestored r))

theorem query_fields (r : State) :
    (queried r).parent.targetIndex = r.parent.targetIndex ∧
      (queried r).parent.targetTag = r.parent.targetTag ∧
        (queried r).parent.graph.core.formula = r.parent.graph.core.formula ∧
          (queried r).parent.graph.core.matching = r.parent.graph.core.matching ∧
            (queried r).pending = r.pending ∧ (queried r).skipped = r.skipped ∧
              (queried r).trace = r.trace ∧ (queried r).active = r.active := by
  have stable := Eligibility.phase_preserves (traceRestored r).core
  exact ⟨stable.1, stable.2.1, stable.2.2.1, stable.2.2.2, rfl, rfl, rfl, rfl⟩

theorem query_canonical (r : State) (vertex : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row)
    (data : ParentQuery.Canonical r.parent vertex clauses entries)
    (traceRead : r.trace = TraceData.encode trace) :
    (queried r).parent.output = ParentQuery.answer (Eligibility.value vertex clauses entries trace) :=
  Eligibility.phase_canonical (traceRestored r).core vertex clauses entries trace
    ⟨data.indexRead, data.tagRead, data.formulaRead, data.matchingRead⟩ traceRead

def prepareSkipped : Block 27 := .seq (.action (.copy 1 17)) (.action (.copy 3 23))
def skippedPrepared (r : State) : State :=
  r.withRegisters {r.registers with target := r.parent.targetIndex, excess := r.skipped}
theorem prepareSkipped_exec (r : State) : Exec prepareSkipped r.store 2 (skippedPrepared r).store :=
  Exec.seq (.action _ _) (.action _ _)

def emitTagged : Block 27 :=
  .branch 18 (liftCore (SearchVertices.emitEntry false)) (liftCore (SearchVertices.emitEntry false))
    (liftCore (SearchVertices.emitEntry true))
def taggedEmitted (r : State) : State :=
  r.withRegisters (SearchVertices.emitted (ForwardEdge.present r.parent.targetTag) r.registers)
theorem emitTagged_exec (r : State) :
    Exec emitTagged r.store (4 * r.registers.target.length + 11) (taggedEmitted r).store := by
  have checked := EdgeKinds.branch_head (18 : Fin 27) r.store
    (liftCore (SearchVertices.emitEntry false)) (liftCore (SearchVertices.emitEntry true))
    (4 * r.registers.target.length + 10) (4 * r.registers.target.length + 10)
    (r.withRegisters (SearchVertices.emitted false r.registers)).store
    (r.withRegisters (SearchVertices.emitted true r.registers)).store
    (liftCore_exec _ r _ _ (SearchVertices.emitEntry_exec false r.registers))
    (liftCore_exec _ r _ _ (SearchVertices.emitEntry_exec true r.registers))
  change Exec emitTagged r.store (1 + if ForwardEdge.present r.parent.targetTag then _ else _)
    (if ForwardEdge.present r.parent.targetTag then _ else _) at checked
  have cost : 1 + (4 * r.registers.target.length + 10) = 4 * r.registers.target.length + 11 := by omega
  cases tag : ForwardEdge.present r.parent.targetTag <;>
    simpa only [taggedEmitted, tag, Bool.false_eq_true, ite_false, ite_true, cost] using checked

def saveSkipped : Block 27 := .action (.copy 23 3)
def skippedSaved (r : State) : State := {r with skipped := r.registers.excess}
theorem saveSkipped_exec (r : State) : Exec saveSkipped r.store 1 (skippedSaved r).store := .action _ _

def appendSkipped : Block 27 := .seq prepareSkipped (.seq emitTagged saveSkipped)
def appended (r : State) : State := skippedSaved (taggedEmitted (skippedPrepared r))
def appendFuel (r : State) : Nat := 4 * r.parent.targetIndex.length + 14
theorem appendSkipped_exec (r : State) : Exec appendSkipped r.store (appendFuel r) (appended r).store := by
  have checked := Exec.seq (prepareSkipped_exec r) (Exec.seq (emitTagged_exec (skippedPrepared r))
    (saveSkipped_exec (taggedEmitted (skippedPrepared r))))
  change Exec appendSkipped r.store (2 + ((4 * r.parent.targetIndex.length + 11) + 1)) (appended r).store at checked
  have cost : 2 + ((4 * r.parent.targetIndex.length + 11) + 1) = appendFuel r := by unfold appendFuel; omega
  rw [cost] at checked
  exact checked

theorem append_fields (r : State) :
    (appended r).parent.targetIndex = r.parent.targetIndex ∧
      (appended r).parent.targetTag = r.parent.targetTag ∧
        (appended r).parent.output = r.parent.output ∧
          (appended r).parent.graph.core.formula = r.parent.graph.core.formula ∧
            (appended r).parent.graph.core.matching = r.parent.graph.core.matching ∧
              (appended r).pending = r.pending ∧ (appended r).trace = r.trace ∧
                (appended r).active = r.active ∧
                  (appended r).skipped = (SearchVertices.entryBits (ForwardEdge.present r.parent.targetTag)
                    r.parent.targetIndex.length).reverse ++ r.skipped :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem append_canonical (r : State) (vertex : CNFLiteral)
    (index : r.parent.targetIndex = List.replicate vertex.variableIndex true)
    (tag : ForwardEdge.present r.parent.targetTag = vertex.positive) :
    (appended r).skipped = (UnseenData.entry vertex).reverse ++ r.skipped := by
  rw [(append_fields r).2.2.2.2.2.2.2.2, index, List.length_replicate, tag]
  rfl

end PNP.Concrete.NormalizerBlocks.Extraction
