/-
Copyright (c) 2026 PNP Labs.

Decode a raw stage against its actual descendant and execute the existing
closed-history compiler. Its result retains the exact computed support, events,
physical-position map and real execution charges; no intermediate circuit,
owner map, order or successful-execution certificate is a public input.

This does not extend the local history language, transport open obligations
between stages, prove a global strategy or establish polynomial execution.
-/

import PNP.NANDWireDescendantInput
import PNP.NANDWireHistoryOwnershipCharges

namespace PNP.DirectWire.WireDescendantHistory

open WireObligationHistory WireHistoryAmbientOwnership

variable {inputs outputs : Nat}

/-- A receipt of the three actual computations, not caller-supplied authority
for the public raw-stage constructor. -/
structure StageCompilation (source : Implementation inputs outputs) (stage : RawStage) where
  records : List
    (TerminalPrimitiveRecord inputs source.gateCount outputs stage.profileWidth)
  recordsAt : decodeRecords inputs source.gateCount outputs stage.profileWidth stage.records =
    some records
  events : List (RawEvent (terminalInterfacePorts source.candidate records).length)
  eventsAt : decodeEvents (terminalInterfacePorts source.candidate records).length stage.events =
    some events
  owned : OwnedCompilation source.candidate records events
  ownedAt : compileOwned source.candidate records events = some owned

namespace StageCompilation

variable {source : Implementation inputs outputs} {stage : RawStage}
variable (compiled : StageCompilation source stage)

def result : Implementation inputs outputs :=
  compiled.owned.result source.candidate compiled.records

def ledger : PhysicalOwnership source.gateCount compiled.result.gateCount :=
  compiled.owned.ledger source.candidate compiled.records

/-- These counts are those of the existing execution, not new ledger lengths. -/
def chargedCount : Nat := compiled.owned.history.execution.charged

def removedCount : Nat := compiled.owned.history.execution.removed

theorem records_source : compiled.records.map encodeRecord = stage.records :=
  decodeRecords_source inputs source.gateCount outputs stage.profileWidth
    stage.records compiled.records compiled.recordsAt

theorem events_source : compiled.events.map encodeEvent = stage.events :=
  decodeEvents_source _ stage.events compiled.events compiled.eventsAt

theorem existing_result :
    WireHistoryArbitrarySupport.compile source.candidate compiled.records compiled.events =
      some compiled.result := by
  have same := compileOwned_result source.candidate compiled.records compiled.events
  rw [compiled.ownedAt] at same
  exact same.symm

theorem semantics (valuation : Valuation inputs) (output : Fin outputs) :
    compiled.result.candidate.semantics valuation output =
      source.candidate.semantics valuation output :=
  compiled.owned.semantics source.candidate compiled.records valuation output

/-- Keep the exact compiler-position correspondence, not only the size balance. -/
theorem physicalOrigin_position
    (node : Fin ((ArbitrarySupportSplice.exterior compiled.records).length +
      compiled.owned.history.state.current.implementation.gateCount)) :
    compiled.ledger.origin (compiled.owned.compiled.position node) =
      rawNodeOrigin source.candidate compiled.records compiled.owned.history node :=
  WireHistoryAmbientOwnership.physicalOrigin_position source.candidate
    compiled.records compiled.owned.history compiled.owned.compiled node

theorem physical_ownership :
    compiled.ledger.live.length = compiled.result.gateCount ∧
      compiled.ledger.charged.length = compiled.chargedCount ∧
      compiled.ledger.removed.length = compiled.removedCount ∧
      (compiled.ledger.live ++ compiled.ledger.removed).Nodup ∧
      (compiled.ledger.live ++ compiled.ledger.removed).Perm
        (ambientOriginals source.gateCount ++ compiled.ledger.charged) :=
  compiled.owned.ownership source.candidate compiled.records

theorem gate_balance :
    compiled.result.gateCount + compiled.removedCount =
      source.gateCount + compiled.chargedCount :=
  WireHistoryArbitrarySupport.closedHistory_result_exact_accounting
    source.candidate compiled.records compiled.owned.history compiled.owned.compiled

/-- Each charge identifies an actual raw input event, with its preserved ID. -/
theorem charged_origin (origin : PhysicalOrigin source.gateCount)
    (member : origin ∈ compiled.ledger.charged) :
    ∃ event ∈ stage.events, ∃ localGate,
      origin = .allocated event.identity localGate := by
  obtain ⟨owner, localGate, assigned⟩ :=
    compiled.owned.charged_origin source.candidate compiled.records origin member
  refine ⟨encodeEvent (compiled.events.get owner), ?_, localGate, assigned⟩
  rw [← compiled.events_source]
  exact List.mem_map.mpr ⟨compiled.events.get owner, List.get_mem _ _, rfl⟩

/-- Duplicate raw identities remain rejected by the existing local scheduler. -/
theorem event_identity_unique (left right : Fin compiled.events.length)
    (same : (compiled.events.get left).identity = (compiled.events.get right).identity) :
    left = right :=
  compiled.owned.history.ordered.unique left right same

end StageCompilation

/-- Decode using the actual source dimensions and extracted interface, then run
the existing compiler. Any failed stage component rejects this entire stage. -/
def compileStage (source : Implementation inputs outputs) (stage : RawStage) :
    Option (StageCompilation source stage) :=
  match recordsAt :
      decodeRecords inputs source.gateCount outputs stage.profileWidth stage.records with
  | none => none
  | some records =>
      match eventsAt :
          decodeEvents (terminalInterfacePorts source.candidate records).length stage.events with
      | none => none
      | some events =>
          match ownedAt : compileOwned source.candidate records events with
          | none => none
          | some owned => some ⟨records, recordsAt, events, eventsAt, owned, ownedAt⟩

theorem compileStage_records_none (source : Implementation inputs outputs) (stage : RawStage)
    (rejected :
      decodeRecords inputs source.gateCount outputs stage.profileWidth stage.records = none) :
    compileStage source stage = none := by
  unfold compileStage
  split
  · rfl
  · rename_i records accepted
    have impossible := accepted.symm.trans rejected
    cases impossible

theorem compileStage_events_none (source : Implementation inputs outputs) (stage : RawStage)
    (records : List
      (TerminalPrimitiveRecord inputs source.gateCount outputs stage.profileWidth))
    (recordsAt :
      decodeRecords inputs source.gateCount outputs stage.profileWidth stage.records = some records)
    (rejected : decodeEvents (terminalInterfacePorts source.candidate records).length
      stage.events = none) : compileStage source stage = none := by
  unfold compileStage
  split
  · rfl
  · rename_i decoded decodedAt
    have sameRecords : decoded = records := Option.some.inj (decodedAt.symm.trans recordsAt)
    cases sameRecords
    split
    · rfl
    · rename_i events accepted
      have impossible := accepted.symm.trans rejected
      cases impossible

theorem compileStage_history_none (source : Implementation inputs outputs) (stage : RawStage)
    (records : List
      (TerminalPrimitiveRecord inputs source.gateCount outputs stage.profileWidth))
    (recordsAt :
      decodeRecords inputs source.gateCount outputs stage.profileWidth stage.records = some records)
    (events : List (RawEvent (terminalInterfacePorts source.candidate records).length))
    (eventsAt : decodeEvents (terminalInterfacePorts source.candidate records).length
      stage.events = some events)
    (rejected : compileOwned source.candidate records events = none) :
    compileStage source stage = none := by
  unfold compileStage
  split
  · rfl
  · rename_i decoded decodedAt
    have sameRecords : decoded = records := Option.some.inj (decodedAt.symm.trans recordsAt)
    cases sameRecords
    split
    · rfl
    · rename_i decodedEvents decodedEventsAt
      have sameEvents : decodedEvents = events :=
        Option.some.inj (decodedEventsAt.symm.trans eventsAt)
      cases sameEvents
      split
      · rfl
      · rename_i owned accepted
        have impossible := accepted.symm.trans rejected
        cases impossible

end PNP.DirectWire.WireDescendantHistory
