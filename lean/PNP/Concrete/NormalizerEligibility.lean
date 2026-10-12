/-
Copyright (c) 2026 PNP Labs.

Concrete eligibility without a supplied membership verdict. A protected
copy preserves the full trace while membership consumes its work cursor.
Seen vertices return unavailable; unseen vertices reuse the actual
root-first parent controller on the restored original trace.
-/

import PNP.Concrete.NormalizerMemberCanonical

namespace PNP.Concrete.NormalizerBlocks.Eligibility

open BitRegister

structure State where
  core : ParentQuery.State
  trace : BitString
def State.frame (r : State) : Store 1 := .cons r.trace .nil
def State.store (r : State) : Store 22 := Frame.join r.core.store r.frame

def save : Block 22 := .action (.copy 21 16)
def saved (r : State) : State := {r with trace := r.core.pending}
theorem save_exec (r : State) : Exec save r.store 1 (saved r).store := .action _ _

def member : Block 22 := Frame.block 1 TraceMember.phase
def memberResult (r : State) : State := {r with core := TraceMember.phaseResult r.core}
theorem member_exec (r : State) :
    Exec member r.store (TraceMember.phaseFuel r.core) (memberResult r).store :=
  Frame.execution (TraceMember.phase_exec r.core) r.frame

def restore : Block 22 := .action (.copy 16 21)
def restored (r : State) : State := {r with core := {r.core with pending := r.trace}}
theorem restore_exec (r : State) : Exec restore r.store 1 (restored r).store := .action _ _

def parent : Block 22 := Frame.block 1 ParentQuery.phase
def parentResult (r : State) : State := {r with core := ParentQuery.phaseResult r.core}
theorem parent_exec (r : State) :
    Exec parent r.store (ParentQuery.phaseFuel r.core) (parentResult r).store :=
  Frame.execution (ParentQuery.phase_exec r.core) r.frame
def parentBranch : Block 22 := .seq restore parent
theorem parentBranch_exec (r : State) :
    Exec parentBranch r.store (1 + ParentQuery.phaseFuel (restored r).core) (parentResult (restored r)).store :=
  Exec.seq (restore_exec r) (parent_exec (restored r))

def reject : Block 22 := Frame.block 1 ParentQuery.defaultAnswer
def rejected (r : State) : State := {r with core := ParentQuery.defaulted r.core}
theorem reject_exec (r : State) : Exec reject r.store 2 (rejected r).store :=
  Frame.execution (ParentQuery.defaultAnswer_exec r.core) r.frame

def dispatch : Block 22 := .branch 19 parentBranch parentBranch reject
def dispatchResult (r : State) : State :=
  if ForwardEdge.present r.core.output then rejected r else parentResult (restored r)
def dispatchFuel (r : State) : Nat :=
  1 + if ForwardEdge.present r.core.output then 2 else 1 + ParentQuery.phaseFuel (restored r).core

theorem dispatch_exec (r : State) : Exec dispatch r.store (dispatchFuel r) (dispatchResult r).store := by
  have checked := EdgeKinds.branch_head (19 : Fin 22) r.store parentBranch reject
    (1 + ParentQuery.phaseFuel (restored r).core) 2 (parentResult (restored r)).store (rejected r).store
    (parentBranch_exec r) (reject_exec r)
  change Exec dispatch r.store (dispatchFuel r)
    (if ForwardEdge.present r.core.output then (rejected r).store else (parentResult (restored r)).store) at checked
  cases seen : ForwardEdge.present r.core.output <;>
    simpa only [dispatchResult, seen, Bool.false_eq_true, ite_false, ite_true] using checked

theorem dispatchFuel_bound (r : State) : dispatchFuel r ≤ ParentQuery.phaseFuel (restored r).core + 3 := by
  cases seen : ForwardEdge.present r.core.output <;>
    simp only [dispatchFuel, seen, Bool.false_eq_true, ite_false, ite_true] <;> omega

def phase : Block 22 := .seq save (.seq member dispatch)
def phaseResult (r : State) : State := dispatchResult (memberResult (saved r))
def phaseFuel (r : State) : Nat :=
  1 + (TraceMember.phaseFuel r.core + dispatchFuel (memberResult (saved r)))
theorem phase_exec (r : State) : Exec phase r.store (phaseFuel r) (phaseResult r).store :=
  Exec.seq (save_exec r) (Exec.seq (member_exec (saved r)) (dispatch_exec (memberResult (saved r))))

theorem restored_fields (r : State) :
    (restored (memberResult (saved r))).core.targetIndex = r.core.targetIndex ∧
      (restored (memberResult (saved r))).core.targetTag = r.core.targetTag ∧
        (restored (memberResult (saved r))).core.graph.core.formula = r.core.graph.core.formula ∧
          (restored (memberResult (saved r))).core.graph.core.matching = r.core.graph.core.matching ∧
            (restored (memberResult (saved r))).core.pending = r.core.pending := by
  have stable := TraceMember.phase_preserves r.core
  exact ⟨stable.1, stable.2.1, stable.2.2.1, stable.2.2.2, rfl⟩

theorem phaseFuel_bound (r : State) :
    phaseFuel r ≤ 342 * r.core.targetIndex.length + 339 * r.core.graph.core.matching.length + 1331 +
      (ParentQuery.stepBound r.core + 1) * (r.core.pending.length + 1) +
        (28 * r.core.pending.length + 81) * (r.core.pending.length + 1) := by
  have membership := TraceMember.phaseFuel_bound r.core
  have dispatching := dispatchFuel_bound (memberResult (saved r))
  have query := ParentQuery.phaseFuel_bound (restored (memberResult (saved r))).core
  have stable := restored_fields r
  have step : ParentQuery.stepBound (restored (memberResult (saved r))).core = ParentQuery.stepBound r.core := by
    simp only [ParentQuery.stepBound, stable.1, stable.2.2.1, stable.2.2.2.1, stable.2.2.2.2]
  rw [step, stable.1, stable.2.2.2.1, stable.2.2.2.2] at query
  unfold phaseFuel
  omega

def value (target : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row) : Option (Option CNFLiteral) :=
  if TraceMember.value target trace then none else ParentQuery.value target clauses entries trace

theorem phase_canonical (r : State) (target : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row)
    (data : ParentQuery.Canonical r.core target clauses entries) (traceRead : r.core.pending = TraceData.encode trace) :
    (phaseResult r).core.output = ParentQuery.answer (value target clauses entries trace) := by
  have membership := TraceMember.phase_canonical r.core target trace data.indexRead data.tagRead traceRead
  have seen : ForwardEdge.present (memberResult (saved r)).core.output = TraceMember.value target trace := by
    change ForwardEdge.present (TraceMember.phaseResult r.core).output = _
    rw [membership]
    rfl
  cases occurs : TraceMember.value target trace with
  | true =>
      unfold phaseResult dispatchResult
      rw [seen, occurs]
      simp only [ite_true, value, occurs]
      rfl
  | false =>
      have stable := restored_fields r
      have nextData : ParentQuery.Canonical (restored (memberResult (saved r))).core target clauses entries :=
        ⟨stable.1.trans data.indexRead, by rw [stable.2.1]; exact data.tagRead,
          stable.2.2.1.trans data.formulaRead, stable.2.2.2.1.trans data.matchingRead⟩
      have pending := stable.2.2.2.2.trans traceRead
      have checked := ParentQuery.phase_canonical _ target clauses entries trace nextData pending
      unfold phaseResult dispatchResult
      rw [seen, occurs]
      simpa only [Bool.false_eq_true, ite_false, parentResult, value, occurs] using checked

end PNP.Concrete.NormalizerBlocks.Eligibility
