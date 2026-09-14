/-
Copyright (c) 2026 PNP Labs.

Execute a computed event order against one evolving physical carrier. Every
creation, read and full discharge retains its actual source binding. Reject
invalid lifecycles and any nonempty final obligation ledger. Trace charges are
actual appended materializers and trace savings are actual normalizations.

This computational R5/R6/R8 history is not all manuscript rewrite families,
complete Package E, global route coverage, ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDWireObligationHistory

namespace PNP.DirectWire.WireObligationHistory

open WireObligationRestoration

variable {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}

/-- A lookup result names the exact currently open creation, not just its field. -/
structure PendingEntry (state : State source) (identity : Nat) where
  field : Fin fields
  snapshot : Snapshot source field
  found : state.pending field = some snapshot
  identified : snapshot.identity = identity

def scanPending (state : State source) (identity : Nat) :
    List (Fin fields) → Option (PendingEntry state identity)
  | [] => none
  | field :: remaining =>
      match found : state.pending field with
      | none => scanPending state identity remaining
      | some snapshot =>
          if same : snapshot.identity = identity then some ⟨field, snapshot, found, same⟩
          else scanPending state identity remaining

def findPending (state : State source) (identity : Nat) : Option (PendingEntry state identity) :=
  scanPending state identity (allFin fields)

/-- The indices bind every actual before/after state to the precise raw event. -/
inductive Transition (source : WireCarrier inputs outputs fields) :
    State source → RawEvent fields → State source → Type where
  | create (state : State source) (event : RawEvent fields) (field : Fin fields)
      (kind : event.action = .createR5 field) (available : state.pending field = none) :
      Transition source state event (state.create event.identity field available)
  | restore (state : State source) (event : RawEvent fields) (identity : Nat)
      (kind : event.action = .restoreR8 identity) (entry : PendingEntry state identity) :
      Transition source state event (state.restore entry.field entry.snapshot entry.found)
  | cancel (state : State source) (event : RawEvent fields) (identity : Nat)
      (kind : event.action = .cancelR6 identity) (entry : PendingEntry state identity)
      (alias : WireMatchedCancellation.Representative source state.keep entry.field)
      (computed : WireMatchedCancellation.representative source state.keep entry.field = some alias) :
      Transition source state event (state.cancel entry.field entry.snapshot entry.found alias)
  | normalize (state : State source) (event : RawEvent fields) (kind : event.action = .normalize) :
      Transition source state event state.normalize
  | read (state : State source) (event : RawEvent fields) (field : Fin fields)
      (kind : event.action = .readFull field) (available : state.pending field = none) :
      Transition source state event state

def applyEvent (state : State source) (event : RawEvent fields) :
    Option (Σ next, Transition source state event next) :=
  match kind : event.action with
  | .createR5 field =>
      match available : state.pending field with
      | none => some ⟨state.create event.identity field available,
          .create state event field kind available⟩
      | some _ => none
  | .restoreR8 identity =>
      match findPending state identity with
      | none => none
      | some entry => some ⟨state.restore entry.field entry.snapshot entry.found,
          .restore state event identity kind entry⟩
  | .cancelR6 identity =>
      match findPending state identity with
      | none => none
      | some entry =>
          match computed : WireMatchedCancellation.representative source state.keep entry.field with
          | none => none
          | some alias => some ⟨state.cancel entry.field entry.snapshot entry.found alias,
              .cancel state event identity kind entry alias computed⟩
  | .normalize => some ⟨state.normalize, .normalize state event kind⟩
  | .readFull field =>
      match available : state.pending field with
      | none => some ⟨state, .read state event field kind available⟩
      | some _ => none

namespace Transition

variable {before after : State source} {event : RawEvent fields}

def charged (step : Transition source before event after) : Nat :=
  match step with
  | .restore _ _ _ _ entry =>
      (materializer entry.snapshot.carrier (keepExcept entry.field)).implementation.gateCount
  | _ => 0

def removed (step : Transition source before event after) : Nat :=
  match step with
  | .normalize _ _ _ => (runPhysicalNormalization before.current.exposed).trace.savedGates
  | _ => 0

theorem charged_eq (step : Transition source before event after) :
    after.charged = before.charged + step.charged := by
  cases step <;> rfl

theorem removed_eq (step : Transition source before event after) :
    after.removed = before.removed + step.removed := by
  cases step <;> rfl

def created (step : Transition source before event after) :
    Option ((field : Fin fields) × Snapshot source field) :=
  match step with
  | .create _ _ field _ available => some ⟨field, before.capture event.identity field available⟩
  | _ => none

def discharged (step : Transition source before event after) :
    Option ((field : Fin fields) × Snapshot source field) :=
  match step with
  | .restore _ _ _ _ entry => some ⟨entry.field, entry.snapshot⟩
  | .cancel _ _ _ _ entry _ _ => some ⟨entry.field, entry.snapshot⟩
  | _ => none

def fullRead (step : Transition source before event after) :
    Option ((field : Fin fields) × Snapshot source field) :=
  match step with
  | .read _ _ field _ available => some ⟨field, before.capture event.identity field available⟩
  | _ => none

/-- A live entry either persists exactly or is the full discharge of this step. -/
theorem pending_persists_or_discharged (step : Transition source before event after)
    (field : Fin fields) (snapshot : Snapshot source field)
    (pending : before.pending field = some snapshot) :
    after.pending field = some snapshot ∨ step.discharged = some ⟨field, snapshot⟩ := by
  cases step with
  | create createdField kind available =>
      by_cases same : field = createdField
      · subst field
        rw [available] at pending
        cases pending
      · left
        exact (setPending_other before.pending createdField _ field same).trans pending
  | restore identity kind entry =>
      by_cases same : field = entry.field
      · subst field
        right
        have exactSnapshot := Option.some.inj (entry.found.symm.trans pending)
        change (some ⟨entry.field, entry.snapshot⟩ :
          Option ((field : Fin fields) × Snapshot source field)) = some ⟨entry.field, snapshot⟩
        rw [exactSnapshot]
      · left
        exact (setPending_other before.pending entry.field none field same).trans pending
  | cancel identity kind entry alias computed =>
      by_cases same : field = entry.field
      · subst field
        right
        have exactSnapshot := Option.some.inj (entry.found.symm.trans pending)
        change (some ⟨entry.field, entry.snapshot⟩ :
          Option ((field : Fin fields) × Snapshot source field)) = some ⟨entry.field, snapshot⟩
        rw [exactSnapshot]
      · left
        exact (setPending_other before.pending entry.field none field same).trans pending
  | normalize kind => exact Or.inl pending
  | read readField kind available => exact Or.inl pending

theorem created_pending (step : Transition source before event after)
    (field : Fin fields) (snapshot : Snapshot source field)
    (created : step.created = some ⟨field, snapshot⟩) : after.pending field = some snapshot := by
  cases step with
  | create createdField kind available =>
      have same : (⟨createdField, before.capture event.identity createdField available⟩ :
          (field : Fin fields) × Snapshot source field) = ⟨field, snapshot⟩ := Option.some.inj created
      cases same
      exact setPending_self before.pending _ _
  | restore identity kind entry => cases created
  | cancel identity kind entry alias computed => cases created
  | normalize kind => cases created
  | read readField kind available => cases created

end Transition

/-- A returned full discharge carries the actual post-operation carrier and value. -/
structure DischargeRecord (source : WireCarrier inputs outputs fields) where
  field : Fin fields
  creation : Snapshot source field
  carrier : WireCarrier inputs outputs fields
  fullWitness : ∀ valuation, carrier.fieldValue valuation field =
    creation.carrier.fieldValue valuation field

def Transition.dischargeRecord {before after : State source} {event : RawEvent fields}
    (step : Transition source before event after) : Option (DischargeRecord source) :=
  match step with
  | .restore _ _ _ _ entry => some
      { field := entry.field, creation := entry.snapshot
        carrier := (before.restore entry.field entry.snapshot entry.found).current
        fullWitness := before.restore_full_value entry.field entry.snapshot entry.found }
  | .cancel _ _ _ _ entry alias _ => some
      { field := entry.field, creation := entry.snapshot
        carrier := (before.cancel entry.field entry.snapshot entry.found alias).current
        fullWitness := before.cancel_full_value entry.field entry.snapshot entry.found alias }
  | _ => none

theorem Transition.dischargeRecord_binding {before after : State source} {event : RawEvent fields}
    (step : Transition source before event after) :
    (step.dischargeRecord.map (fun (record : DischargeRecord source) =>
      ⟨record.field, record.creation⟩)) = step.discharged := by
  cases step <;> rfl

structure EventRecord (source : WireCarrier inputs outputs fields) where
  identity : Nat
  before : WireCarrier inputs outputs fields
  after : WireCarrier inputs outputs fields
  creation : Option ((field : Fin fields) × Snapshot source field)
  discharge : Option (DischargeRecord source)
  fullRead : Option ((field : Fin fields) × Snapshot source field)
  chargedGates : Nat
  removedGates : Nat

def Transition.record {before after : State source} {event : RawEvent fields}
    (step : Transition source before event after) : EventRecord source where
  identity := event.identity
  before := before.current
  after := after.current
  creation := step.created
  discharge := step.dischargeRecord
  fullRead := step.fullRead
  chargedGates := step.charged
  removedGates := step.removed

/-- One legal transition per actual event, including disconnected history nodes. -/
inductive Execution (source : WireCarrier inputs outputs fields) :
    State source → List (RawEvent fields) → State source → Type where
  | nil (state : State source) : Execution source state [] state
  | cons {before middle after : State source} {event : RawEvent fields} {remaining : List (RawEvent fields)}
      (step : Transition source before event middle) (tail : Execution source middle remaining after) :
      Execution source before (event :: remaining) after

def execute (state : State source) :
    (events : List (RawEvent fields)) → Option (Σ finalState, Execution source state events finalState)
  | [] => some ⟨state, .nil state⟩
  | event :: remaining => do
      let next ← applyEvent state event
      let rest ← execute next.1 remaining
      return ⟨rest.1, .cons next.2 rest.2⟩

namespace Execution

variable {before after : State source} {events : List (RawEvent fields)}

def charged {before after : State source} {events : List (RawEvent fields)}
    (trace : Execution source before events after) : Nat :=
  match trace with
  | .nil _ => 0
  | .cons step tail => step.charged + tail.charged

def removed {before after : State source} {events : List (RawEvent fields)}
    (trace : Execution source before events after) : Nat :=
  match trace with
  | .nil _ => 0
  | .cons step tail => step.removed + tail.removed

def records {before after : State source} {events : List (RawEvent fields)}
    (trace : Execution source before events after) : List (EventRecord source) :=
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

def Discharged {before after : State source} {events : List (RawEvent fields)}
    (trace : Execution source before events after)
    (field : Fin fields) (snapshot : Snapshot source field) : Prop :=
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

/-- Each creation closes strictly later in the same actual execution trace. -/
def CreationsClosed {before after : State source} {events : List (RawEvent fields)}
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

end Execution

def State.isClosed (state : State source) : Bool := (allFin fields).all state.keep

theorem State.isClosed_sound (state : State source) (closed : state.isClosed = true)
    (field : Fin fields) : state.pending field = none :=
  (state.keep_iff field).1 ((List.all_eq_true.mp closed) field (mem_allFin field))

/-- The constructor computes this trace and all witnesses from source and raw events. -/
structure ClosedHistory (source : WireCarrier inputs outputs fields) (raw : List (RawEvent fields)) where
  ordered : OrderedEvents raw
  state : State source
  execution : Execution source (State.initial source) (ordered.order.map raw.get) state
  closed : ∀ field, state.pending field = none

def compileHistory (source : WireCarrier inputs outputs fields) (raw : List (RawEvent fields)) :
    Option (ClosedHistory source raw) := do
  let ordered ← orderEvents raw
  let result ← execute (State.initial source) (ordered.order.map raw.get)
  if closed : result.1.isClosed = true then
    return ⟨ordered, result.1, result.2, result.1.isClosed_sound closed⟩
  else none

namespace ClosedHistory

variable {raw : List (RawEvent fields)}

theorem full_output (history : ClosedHistory source raw) (valuation : Valuation inputs)
    (output : Fin outputs) : history.state.current.implementation.candidate.semantics valuation output =
      source.implementation.candidate.semantics valuation output := history.state.output valuation output

theorem full_field (history : ClosedHistory source raw) (valuation : Valuation inputs)
    (field : Fin fields) : history.state.current.fieldValue valuation field =
      source.fieldValue valuation field := history.state.closed_field history.closed valuation field

theorem gate_balance (history : ClosedHistory source raw) :
    history.state.current.implementation.gateCount + history.execution.removed =
      source.implementation.gateCount + history.execution.charged := by
  have charges := history.execution.total_charge
  have removed := history.execution.total_removed
  have balance := history.state.balance
  change history.state.charged = 0 + history.execution.charged at charges
  change history.state.removed = 0 + history.execution.removed at removed
  omega

theorem creation_lifecycle (history : ClosedHistory source raw) : history.execution.CreationsClosed :=
  history.execution.creationsClosed_of_finalClosed history.closed

theorem executed_count (history : ClosedHistory source raw) :
    history.execution.records.length = raw.length := by
  have counted := congrArg List.length history.execution.record_identities
  simp only [List.length_map, history.ordered.order_length] at counted
  exact counted

theorem executed_identities_nodup (history : ClosedHistory source raw) :
    (history.execution.records.map (fun record => record.identity)).Nodup := by
  rw [history.execution.record_identities, List.map_map]
  exact history.ordered.identities_nodup

theorem dependency_before (history : ClosedHistory source raw) (producer consumer : Fin raw.length)
    (dependency : (raw.get producer).identity ∈ (raw.get consumer).dependencies) :
    (history.ordered.schedule.position producer).val < (history.ordered.schedule.position consumer).val :=
  history.ordered.schedule.ordered producer consumer ((graph_dependency_iff raw producer consumer).2 dependency)

end ClosedHistory
end PNP.DirectWire.WireObligationHistory
