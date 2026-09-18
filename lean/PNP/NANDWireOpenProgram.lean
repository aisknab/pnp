/-
Copyright (c) 2026 PNP Labs.

Execute complete mixed programs from the actual initial carrier. An ambient
obligation may stay open across arbitrarily many support, reordering and recoding
operations, but only an actual full-mode primitive discharge closes it. The
final ledger must be empty. Failed tails never return successful prefixes.

This is an offered computational program compiler, not full manuscript
profiles, global certificate discovery, unconditional ZeroSlack or a polynomial
runtime/certificate-size theorem. Physical ownership and proper-support
publication wrappers are separate integration obligations.
-/

import PNP.NANDWireOpenProgramInput
import PNP.NANDWireStructuralState

namespace PNP.DirectWire.WireOpenProgram

open WireObligationHistory (State Snapshot)

variable {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}

def RawEvent.primitiveEvent (event : RawEvent) (action : WireObligationHistory.Action fields) :
    WireObligationHistory.RawEvent fields :=
  ⟨event.identity, event.predecessorIDs, action⟩

/-- Indices retain the actual action, decoding and before/after states. -/
inductive Transition (source : WireCarrier inputs outputs fields) :
    State source → RawEvent → State source → Type where
  | primitive (before : State source) (event : RawEvent) (raw : WireDescendantHistory.RawAction)
      (kind : event.action = .primitive raw) (action : WireObligationHistory.Action fields)
      (decoded : WireDescendantHistory.decodeAction fields raw = some action)
      {after : State source}
      (step : WireObligationHistory.Transition source before (event.primitiveEvent action) after) :
      Transition source before event after
  | support (before : State source) (event : RawEvent)
      (raw : WireDescendantCertificate.RawCertificate) (kind : event.action = .support raw)
      (receipt : WireOpenSupportSplice.Receipt before raw) :
      Transition source before event receipt.next
  | structural (before : State source) (event : RawEvent)
      (raw : List (Nat × Nat)) (kind : event.action = .structural raw)
      (receipt : WireStructuralState.Receipt before raw) :
      Transition source before event receipt.next
  | recoding (before : State source) (event : RawEvent)
      (rawEncoder rawDecoder : Concrete.LockedNAND.RawCandidate)
      (kind : event.action = .recoding rawEncoder rawDecoder)
      (receipt : WireRecodingInput.Receipt before rawEncoder rawDecoder) :
      Transition source before event receipt.next

def applyEvent (before : State source) (event : RawEvent) :
    Option (Σ next, Transition source before event next) :=
  match kind : event.action with
  | .primitive raw =>
      match decoded : WireDescendantHistory.decodeAction fields raw with
      | none => none
      | some action =>
          match WireObligationHistory.applyEvent before (event.primitiveEvent action) with
          | none => none
          | some next => some ⟨next.1, .primitive before event raw kind action decoded next.2⟩
  | .support raw =>
      match WireOpenSupportSplice.execute before raw with
      | none => none
      | some receipt => some ⟨receipt.next, .support before event raw kind receipt⟩
  | .structural raw =>
      match WireStructuralState.execute before raw with
      | none => none
      | some receipt => some ⟨receipt.next, .structural before event raw kind receipt⟩
  | .recoding rawEncoder rawDecoder =>
      match WireRecodingInput.execute before rawEncoder rawDecoder with
      | none => none
      | some receipt =>
          some ⟨receipt.next, .recoding before event rawEncoder rawDecoder kind receipt⟩

namespace Transition

variable {before after : State source} {event : RawEvent}

def charged (step : Transition source before event after) : Nat :=
  match step with
  | .primitive _ _ _ _ _ _ inner => inner.charged
  | .support _ _ _ _ receipt => receipt.executed.run.chargedCount
  | .structural _ _ _ _ _ => 0
  | .recoding _ _ _ _ _ receipt => receipt.charged

def removed (step : Transition source before event after) : Nat :=
  match step with
  | .primitive _ _ _ _ _ _ inner => inner.removed
  | .support _ _ _ _ receipt => receipt.executed.run.removedCount
  | .structural _ _ _ _ _ => 0
  | .recoding _ _ _ _ _ receipt => receipt.removed

theorem charged_eq (step : Transition source before event after) :
    after.charged = before.charged + step.charged := by
  cases step with
  | primitive raw kind action decoded inner => exact inner.charged_eq
  | support raw kind receipt => rfl
  | structural raw kind receipt => rfl
  | recoding rawEncoder rawDecoder kind receipt => exact receipt.charged_eq

theorem removed_eq (step : Transition source before event after) :
    after.removed = before.removed + step.removed := by
  cases step with
  | primitive raw kind action decoded inner => exact inner.removed_eq
  | support raw kind receipt => rfl
  | structural raw kind receipt => rfl
  | recoding rawEncoder rawDecoder kind receipt => exact receipt.removed_eq

def created (step : Transition source before event after) :
    Option ((field : Fin fields) × Snapshot source field) :=
  match step with
  | .primitive _ _ _ _ _ _ inner => inner.created
  | .support _ _ _ _ _ => none
  | .structural _ _ _ _ _ => none
  | .recoding _ _ _ _ _ _ => none

def discharged (step : Transition source before event after) :
    Option ((field : Fin fields) × Snapshot source field) :=
  match step with
  | .primitive _ _ _ _ _ _ inner => inner.discharged
  | .support _ _ _ _ _ => none
  | .structural _ _ _ _ _ => none
  | .recoding _ _ _ _ _ _ => none

def dischargeRecord (step : Transition source before event after) :
    Option (WireObligationHistory.DischargeRecord source) :=
  match step with
  | .primitive _ _ _ _ _ _ inner => inner.dischargeRecord
  | .support _ _ _ _ _ => none
  | .structural _ _ _ _ _ => none
  | .recoding _ _ _ _ _ _ => none

def fullRead (step : Transition source before event after) :
    Option ((field : Fin fields) × Snapshot source field) :=
  match step with
  | .primitive _ _ _ _ _ _ inner => inner.fullRead
  | .support _ _ _ _ _ => none
  | .structural _ _ _ _ _ => none
  | .recoding _ _ _ _ _ _ => none

theorem dischargeRecord_binding (step : Transition source before event after) :
    (step.dischargeRecord.map (fun (record : WireObligationHistory.DischargeRecord source) =>
      ⟨record.field, record.creation⟩)) = step.discharged := by
  cases step with
  | primitive raw kind action decoded inner => exact inner.dischargeRecord_binding
  | support raw kind receipt => rfl
  | structural raw kind receipt => rfl
  | recoding rawEncoder rawDecoder kind receipt => rfl

/-- Splicing, reordering and recoding retain the exact snapshot; none is a discharge. -/
theorem pending_persists_or_discharged (step : Transition source before event after)
    (field : Fin fields) (snapshot : Snapshot source field)
    (pending : before.pending field = some snapshot) :
    after.pending field = some snapshot ∨ step.discharged = some ⟨field, snapshot⟩ := by
  cases step with
  | primitive raw kind action decoded inner =>
      exact inner.pending_persists_or_discharged field snapshot pending
  | support raw kind receipt => exact Or.inl pending
  | structural raw kind receipt => exact Or.inl pending
  | recoding rawEncoder rawDecoder kind receipt => exact Or.inl pending

theorem created_pending (step : Transition source before event after)
    (field : Fin fields) (snapshot : Snapshot source field)
    (created : step.created = some ⟨field, snapshot⟩) : after.pending field = some snapshot := by
  cases step with
  | primitive raw kind action decoded inner => exact inner.created_pending field snapshot created
  | support raw kind receipt => cases created
  | structural raw kind receipt => cases created
  | recoding rawEncoder rawDecoder kind receipt => cases created

theorem causalInvariant (step : Transition source before event after) (labels : Fin inputs → Nat) :
    before.CausalInvariant labels → after.CausalInvariant labels := by
  intro bounded
  cases step with
  | primitive raw kind action decoded inner => exact inner.causalInvariant labels bounded
  | support raw kind receipt =>
      exact WireOpenSupportSplice.transfer_causal_invariant before receipt.records
        receipt.executed labels bounded
  | structural raw kind receipt =>
      exact before.reindex_causalInvariant receipt.relabeling labels bounded
  | recoding rawEncoder rawDecoder kind receipt => exact receipt.causalInvariant labels bounded

def record (step : Transition source before event after) : WireObligationHistory.EventRecord source where
  identity := event.identity
  before := before.current
  after := after.current
  creation := step.created
  discharge := step.dischargeRecord
  fullRead := step.fullRead
  chargedGates := step.charged
  removedGates := step.removed

end Transition

inductive Execution (source : WireCarrier inputs outputs fields) :
    State source → List RawEvent → State source → Type where
  | nil (state : State source) : Execution source state [] state
  | cons {before middle after : State source} {event : RawEvent} {remaining : List RawEvent}
      (step : Transition source before event middle) (tail : Execution source middle remaining after) :
      Execution source before (event :: remaining) after

def execute (state : State source) :
    (events : List RawEvent) → Option (Σ finalState, Execution source state events finalState)
  | [] => some ⟨state, .nil state⟩
  | event :: remaining => do
      let next ← applyEvent state event
      let rest ← execute next.1 remaining
      return ⟨rest.1, .cons next.2 rest.2⟩

/-- Failure is propagated through the complete sequence, never converted to a prefix. -/
theorem execute_failed_tail (state : State source) (event : RawEvent) (remaining : List RawEvent)
    (next : Σ after, Transition source state event after)
    (first : applyEvent state event = some next) (failed : execute next.1 remaining = none) :
    execute state (event :: remaining) = none := by
  change (applyEvent state event).bind _ = none
  rw [first]
  change (execute next.1 remaining).bind _ = none
  rw [failed]
  rfl

namespace Execution

variable {before after : State source} {events : List RawEvent}

def charged {before after : State source} {events : List RawEvent}
    (trace : Execution source before events after) : Nat :=
  match trace with
  | .nil _ => 0
  | .cons step tail => step.charged + tail.charged

def removed {before after : State source} {events : List RawEvent}
    (trace : Execution source before events after) : Nat :=
  match trace with
  | .nil _ => 0
  | .cons step tail => step.removed + tail.removed

def records {before after : State source} {events : List RawEvent}
    (trace : Execution source before events after) : List (WireObligationHistory.EventRecord source) :=
  match trace with
  | .nil _ => []
  | .cons step tail => step.record :: tail.records

theorem total_charge (trace : Execution source before events after) :
    after.charged = before.charged + trace.charged := by
  induction trace with
  | nil state => rfl
  | cons step tail ih =>
      change _ = _ + (step.charged + tail.charged)
      rw [ih, step.charged_eq, Nat.add_assoc]

theorem total_removed (trace : Execution source before events after) :
    after.removed = before.removed + trace.removed := by
  induction trace with
  | nil state => rfl
  | cons step tail ih =>
      change _ = _ + (step.removed + tail.removed)
      rw [ih, step.removed_eq, Nat.add_assoc]

theorem record_identities (trace : Execution source before events after) :
    trace.records.map (fun record => record.identity) = events.map (fun event => event.identity) := by
  induction trace with
  | nil state => rfl
  | cons step tail ih =>
      change _ :: _ = _ :: _
      exact congrArg (List.cons _) ih

def Discharged {before after : State source} {events : List RawEvent}
    (trace : Execution source before events after) (field : Fin fields)
    (snapshot : Snapshot source field) : Prop :=
  match trace with
  | .nil _ => False
  | .cons step tail => step.discharged = some ⟨field, snapshot⟩ ∨ tail.Discharged field snapshot

theorem pending_persists_or_discharged (trace : Execution source before events after)
    (field : Fin fields) (snapshot : Snapshot source field)
    (pending : before.pending field = some snapshot) :
    after.pending field = some snapshot ∨ trace.Discharged field snapshot := by
  revert pending
  induction trace with
  | nil state => exact fun pending => Or.inl pending
  | cons step tail ih =>
      intro pending
      rcases step.pending_persists_or_discharged field snapshot pending with remains | discharged
      · rcases ih remains with finalPending | later
        · exact Or.inl finalPending
        · exact Or.inr (Or.inr later)
      · exact Or.inr (Or.inl discharged)

def CreationsClosed {before after : State source} {events : List RawEvent}
    (trace : Execution source before events after) : Prop :=
  match trace with
  | .nil _ => True
  | .cons step tail =>
      (∀ field snapshot, step.created = some ⟨field, snapshot⟩ → tail.Discharged field snapshot) ∧
        tail.CreationsClosed

theorem creationsClosed_of_finalClosed (trace : Execution source before events after)
    (closed : ∀ field, after.pending field = none) : trace.CreationsClosed := by
  revert closed
  induction trace with
  | nil state => intro _closed; trivial
  | cons step tail ih =>
      intro closed
      refine ⟨?_, ih closed⟩
      intro field snapshot created
      rcases tail.pending_persists_or_discharged field snapshot
          (step.created_pending field snapshot created) with pending | discharged
      · rw [closed field] at pending
        cases pending
      · exact discharged

theorem causalInvariant (trace : Execution source before events after) (labels : Fin inputs → Nat) :
    before.CausalInvariant labels → after.CausalInvariant labels := by
  induction trace with
  | nil state => exact fun bounded => bounded
  | cons step tail ih =>
      intro bounded
      exact ih (step.causalInvariant labels bounded)

end Execution

/-- Every receipt is bound to the computed order, complete execution and final check. -/
structure CompiledProgram (source : WireCarrier inputs outputs fields) (raw : List RawEvent) where
  ordered : OrderedEvents raw
  orderedAt : orderEvents raw = some ordered
  state : State source
  execution : Execution source (State.initial source) (ordered.order.map raw.get) state
  executedAt : execute (State.initial source) (ordered.order.map raw.get) = some ⟨state, execution⟩
  closedCheck : state.isClosed = true

/-- The public entry supplies the initial state itself and exposes no witness inputs. -/
def compile (source : WireCarrier inputs outputs fields) (raw : List RawEvent) :
    Option (CompiledProgram source raw) :=
  match orderedAt : orderEvents raw with
  | none => none
  | some ordered =>
      match executedAt : execute (State.initial source) (ordered.order.map raw.get) with
      | none => none
      | some result =>
          if closed : result.1.isClosed = true then
            some ⟨ordered, orderedAt, result.1, result.2, executedAt, closed⟩
          else none

namespace CompiledProgram

variable {raw : List RawEvent}

def result (program : CompiledProgram source raw) : WireCarrier inputs outputs fields :=
  program.state.current

theorem closed (program : CompiledProgram source raw) (field : Fin fields) :
    program.state.pending field = none := program.state.isClosed_sound program.closedCheck field

theorem full_output (program : CompiledProgram source raw) (valuation : Valuation inputs)
    (output : Fin outputs) :
    program.result.implementation.candidate.semantics valuation output =
      source.implementation.candidate.semantics valuation output := program.state.output valuation output

theorem full_field (program : CompiledProgram source raw) (valuation : Valuation inputs)
    (field : Fin fields) : program.result.fieldValue valuation field = source.fieldValue valuation field :=
  program.state.closed_field program.closed valuation field

theorem gate_balance (program : CompiledProgram source raw) :
    program.result.implementation.gateCount + program.execution.removed =
      source.implementation.gateCount + program.execution.charged := by
  have charges := program.execution.total_charge
  have removed := program.execution.total_removed
  have balance := program.state.balance
  change program.state.charged = 0 + program.execution.charged at charges
  change program.state.removed = 0 + program.execution.removed at removed
  change program.state.current.implementation.gateCount + _ = _
  omega

theorem creation_lifecycle (program : CompiledProgram source raw) :
    program.execution.CreationsClosed :=
  program.execution.creationsClosed_of_finalClosed program.closed

theorem executed_count (program : CompiledProgram source raw) :
    program.execution.records.length = raw.length := by
  have counted := congrArg List.length program.execution.record_identities
  simp only [List.length_map, program.ordered.order_length] at counted
  exact counted

theorem executed_identities_nodup (program : CompiledProgram source raw) :
    (program.execution.records.map (fun record => record.identity)).Nodup := by
  rw [program.execution.record_identities, List.map_map]
  exact program.ordered.identities_nodup

theorem dependency_before (program : CompiledProgram source raw) (producer consumer : Fin raw.length)
    (dependency : (raw.get producer).identity ∈ (raw.get consumer).dependencies) :
    (program.ordered.schedule.position producer).val <
      (program.ordered.schedule.position consumer).val :=
  program.ordered.schedule.ordered producer consumer ((graph_dependency_iff raw producer consumer).2 dependency)

theorem causalInvariant (program : CompiledProgram source raw) (labels : Fin inputs → Nat) :
    program.state.CausalInvariant labels :=
  program.execution.causalInvariant labels (State.initial_causalInvariant source labels)

theorem output_causal_bound (program : CompiledProgram source raw)
    (labels : Fin inputs → Nat) (output : Fin outputs) :
    CausalBound.outputLevel program.result.implementation.candidate labels output ≤
      CausalBound.outputLevel source.implementation.candidate labels output :=
  (program.causalInvariant labels).1.1 output

theorem field_causal_bound (program : CompiledProgram source raw)
    (labels : Fin inputs → Nat) (field : Fin fields) :
    program.result.fieldLevel labels field ≤ source.fieldLevel labels field :=
  (program.causalInvariant labels).1.2 field

end CompiledProgram

/-- Exact acceptance retains the full computed execution, not merely a legal prefix. -/
theorem compile_exists_iff (source : WireCarrier inputs outputs fields) (raw : List RawEvent) :
    (∃ program, compile source raw = some program) ↔
      ∃ ordered, orderEvents raw = some ordered ∧
        ∃ result, execute (State.initial source) (ordered.order.map raw.get) = some result ∧
          result.1.isClosed = true := by
  constructor
  · rintro ⟨program, _accepted⟩
    exact ⟨program.ordered, program.orderedAt, ⟨program.state, program.execution⟩,
      program.executedAt, program.closedCheck⟩
  · rintro ⟨ordered, orderedAt, result, executedAt, closed⟩
    unfold compile
    split
    · rename_i rejected
      have impossible := rejected.symm.trans orderedAt
      cases impossible
    · rename_i actual actualAt
      have same : actual = ordered := Option.some.inj (actualAt.symm.trans orderedAt)
      cases same
      split
      · rename_i rejected
        have impossible := rejected.symm.trans executedAt
        cases impossible
      · rename_i reached reachedAt
        have sameResult : reached = result := Option.some.inj (reachedAt.symm.trans executedAt)
        cases sameResult
        rw [dif_pos closed]
        exact ⟨_, rfl⟩

theorem compile_none_iff (source : WireCarrier inputs outputs fields) (raw : List RawEvent) :
    compile source raw = none ↔
      ¬(∃ ordered, orderEvents raw = some ordered ∧
        ∃ result, execute (State.initial source) (ordered.order.map raw.get) = some result ∧
          result.1.isClosed = true) := by
  constructor
  · intro rejected valid
    obtain ⟨program, accepted⟩ := (compile_exists_iff source raw).2 valid
    rw [rejected] at accepted
    cases accepted
  · intro invalid
    cases accepted : compile source raw with
    | none => rfl
    | some program => exact False.elim (invalid ((compile_exists_iff source raw).1 ⟨program, accepted⟩))

end PNP.DirectWire.WireOpenProgram
