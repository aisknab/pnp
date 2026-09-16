import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Frozen, reviewed M267 interfaces. Tests never regenerate these expectations.
// Kernel/type/axiom checks, not source matching or finite fixtures, are proof authority.
const SPECS = [
  {
    "id": "input",
    "suffix": "Input",
    "path": "lean/PNP/NANDWireDescendantInput.lean",
    "heads": [
      "RawRecord",
      "decodeRecord",
      "encodeRecord",
      "decodeRecord_encode",
      "decodeRecord_source",
      "decodeRecords",
      "decodeRecords_encode",
      "decodeRecords_source",
      "RawAction",
      "decodeAction",
      "encodeAction",
      "decodeAction_encode",
      "decodeAction_source",
      "EventInput",
      "decodeEvent",
      "encodeEvent",
      "decodeEvent_encode",
      "decodeEvent_source",
      "decodeEvents",
      "decodeEvents_encode",
      "decodeEvents_source",
      "RawStage"
    ],
    "imports": [
      "PNP.NANDWireObligationHistory"
    ],
    "context": [
      "namespace PNP.DirectWire.WireDescendantHistory open WireObligationHistory",
      "end PNP.DirectWire.WireDescendantHistory"
    ],
    "blocks": [
      {
        "name": "RawRecord",
        "occurrence": 0,
        "exact": "inductive RawRecord where | gate (index : Nat) | boundary (index : Nat) | interface (index : Nat) | profile (index : Nat) deriving Repr, DecidableEq"
      },
      {
        "name": "decodeRecord",
        "occurrence": 0,
        "exact": "def decodeRecord (inputs gates outputs profileWidth : Nat) : RawRecord → Option (TerminalPrimitiveRecord inputs gates outputs profileWidth) | .gate index => if valid : index < gates then some (.gate ⟨index, valid⟩) else none | .boundary index => if valid : index < inputs then some (.boundary ⟨index, valid⟩) else none | .interface index => if valid : index < outputs then some (.interface ⟨index, valid⟩) else none | .profile index => if valid : index < profileWidth then some (.profile ⟨index, valid⟩) else none"
      },
      {
        "name": "encodeRecord",
        "occurrence": 0,
        "exact": "def encodeRecord {inputs gates outputs profileWidth : Nat} : TerminalPrimitiveRecord inputs gates outputs profileWidth → RawRecord | .gate index => .gate index.val | .boundary index => .boundary index.val | .interface index => .interface index.val | .profile index => .profile index.val"
      },
      {
        "name": "decodeRecords",
        "occurrence": 0,
        "exact": "def decodeRecords (inputs gates outputs profileWidth : Nat) (raw : List RawRecord) : Option (List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) := raw.mapM (decodeRecord inputs gates outputs profileWidth)"
      },
      {
        "name": "RawAction",
        "occurrence": 0,
        "exact": "inductive RawAction where | createR5 (field : Nat) | cancelR6 (creationID : Nat) | restoreR8 (creationID : Nat) | realizeR7 (creationID : Nat) (records : List RawSupportRecord) | normalize | readFull (field : Nat) deriving Repr, DecidableEq"
      },
      {
        "name": "decodeAction",
        "occurrence": 0,
        "exact": "def decodeAction (fields : Nat) : RawAction → Option (Action fields) | .createR5 field => if valid : field < fields then some (.createR5 ⟨field, valid⟩) else none | .cancelR6 identity => some (.cancelR6 identity) | .restoreR8 identity => some (.restoreR8 identity) | .realizeR7 identity records => some (.realizeR7 identity records) | .normalize => some .normalize | .readFull field => if valid : field < fields then some (.readFull ⟨field, valid⟩) else none"
      },
      {
        "name": "encodeAction",
        "occurrence": 0,
        "exact": "def encodeAction {fields : Nat} : Action fields → RawAction | .createR5 field => .createR5 field.val | .cancelR6 identity => .cancelR6 identity | .restoreR8 identity => .restoreR8 identity | .realizeR7 identity records => .realizeR7 identity records | .normalize => .normalize | .readFull field => .readFull field.val"
      },
      {
        "name": "EventInput",
        "occurrence": 0,
        "exact": "structure EventInput where identity : Nat predecessorIDs : List Nat action : RawAction deriving Repr, DecidableEq"
      },
      {
        "name": "decodeEvent",
        "occurrence": 0,
        "exact": "def decodeEvent (fields : Nat) (raw : EventInput) : Option (RawEvent fields) := (decodeAction fields raw.action).map fun action => { identity := raw.identity, predecessorIDs := raw.predecessorIDs, action := action }"
      },
      {
        "name": "encodeEvent",
        "occurrence": 0,
        "exact": "def encodeEvent {fields : Nat} (event : RawEvent fields) : EventInput := { identity := event.identity, predecessorIDs := event.predecessorIDs, action := encodeAction event.action }"
      },
      {
        "name": "decodeEvents",
        "occurrence": 0,
        "exact": "def decodeEvents (fields : Nat) (raw : List EventInput) : Option (List (RawEvent fields)) := raw.mapM (decodeEvent fields)"
      },
      {
        "name": "RawStage",
        "occurrence": 0,
        "exact": "structure RawStage where profileWidth : Nat records : List RawRecord events : List EventInput deriving Repr, DecidableEq"
      },
      {
        "name": "decodeRecord_source",
        "occurrence": 0,
        "signature": "theorem decodeRecord_source (inputs gates outputs profileWidth : Nat) (raw : RawRecord) (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) (accepted : decodeRecord inputs gates outputs profileWidth raw = some record) : encodeRecord record = raw"
      },
      {
        "name": "decodeRecords_source",
        "occurrence": 0,
        "signature": "theorem decodeRecords_source (inputs gates outputs profileWidth : Nat) (raw : List RawRecord) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (accepted : decodeRecords inputs gates outputs profileWidth raw = some records) : records.map encodeRecord = raw"
      },
      {
        "name": "decodeAction_source",
        "occurrence": 0,
        "signature": "theorem decodeAction_source (fields : Nat) (raw : RawAction) (action : Action fields) (accepted : decodeAction fields raw = some action) : encodeAction action = raw"
      },
      {
        "name": "decodeEvents_source",
        "occurrence": 0,
        "signature": "theorem decodeEvents_source (fields : Nat) (raw : List EventInput) (events : List (RawEvent fields)) (accepted : decodeEvents fields raw = some events) : events.map encodeEvent = raw"
      }
    ],
    "guards": [],
    "reviewedNames": [
      "PNP.DirectWire.WireDescendantHistory.decodeRecord_encode",
      "PNP.DirectWire.WireDescendantHistory.decodeRecord_source",
      "PNP.DirectWire.WireDescendantHistory.decodeRecords_encode",
      "PNP.DirectWire.WireDescendantHistory.decodeRecords_source",
      "PNP.DirectWire.WireDescendantHistory.decodeAction_encode",
      "PNP.DirectWire.WireDescendantHistory.decodeAction_source",
      "PNP.DirectWire.WireDescendantHistory.decodeEvent_encode",
      "PNP.DirectWire.WireDescendantHistory.decodeEvent_source",
      "PNP.DirectWire.WireDescendantHistory.decodeEvents_encode",
      "PNP.DirectWire.WireDescendantHistory.decodeEvents_source"
    ]
  },
  {
    "id": "stage",
    "suffix": "Stage",
    "path": "lean/PNP/NANDWireDescendantStage.lean",
    "heads": [
      "StageCompilation",
      "result",
      "ledger",
      "chargedCount",
      "removedCount",
      "records_source",
      "events_source",
      "existing_result",
      "semantics",
      "physicalOrigin_position",
      "physical_ownership",
      "gate_balance",
      "charged_origin",
      "event_identity_unique",
      "compileStage",
      "compileStage_records_none",
      "compileStage_events_none",
      "compileStage_history_none"
    ],
    "imports": [
      "PNP.NANDWireDescendantInput",
      "PNP.NANDWireHistoryOwnershipCharges"
    ],
    "context": [
      "namespace PNP.DirectWire.WireDescendantHistory open WireObligationHistory WireHistoryAmbientOwnership",
      "variable {inputs outputs : Nat}",
      "namespace StageCompilation",
      "variable {source : Implementation inputs outputs} {stage : RawStage}",
      "variable (compiled : StageCompilation source stage)",
      "end StageCompilation",
      "end PNP.DirectWire.WireDescendantHistory"
    ],
    "blocks": [
      {
        "name": "StageCompilation",
        "occurrence": 0,
        "exact": "structure StageCompilation (source : Implementation inputs outputs) (stage : RawStage) where records : List (TerminalPrimitiveRecord inputs source.gateCount outputs stage.profileWidth) recordsAt : decodeRecords inputs source.gateCount outputs stage.profileWidth stage.records = some records events : List (RawEvent (terminalInterfacePorts source.candidate records).length) eventsAt : decodeEvents (terminalInterfacePorts source.candidate records).length stage.events = some events owned : OwnedCompilation source.candidate records events ownedAt : compileOwned source.candidate records events = some owned"
      },
      {
        "name": "result",
        "occurrence": 0,
        "exact": "def result : Implementation inputs outputs := compiled.owned.result source.candidate compiled.records"
      },
      {
        "name": "ledger",
        "occurrence": 0,
        "exact": "def ledger : PhysicalOwnership source.gateCount compiled.result.gateCount := compiled.owned.ledger source.candidate compiled.records"
      },
      {
        "name": "chargedCount",
        "occurrence": 0,
        "exact": "def chargedCount : Nat := compiled.owned.history.execution.charged"
      },
      {
        "name": "removedCount",
        "occurrence": 0,
        "exact": "def removedCount : Nat := compiled.owned.history.execution.removed"
      },
      {
        "name": "compileStage",
        "occurrence": 0,
        "exact": "def compileStage (source : Implementation inputs outputs) (stage : RawStage) : Option (StageCompilation source stage) := match recordsAt : decodeRecords inputs source.gateCount outputs stage.profileWidth stage.records with | none => none | some records => match eventsAt : decodeEvents (terminalInterfacePorts source.candidate records).length stage.events with | none => none | some events => match ownedAt : compileOwned source.candidate records events with | none => none | some owned => some ⟨records, recordsAt, events, eventsAt, owned, ownedAt⟩"
      },
      {
        "name": "semantics",
        "occurrence": 0,
        "signature": "theorem semantics (valuation : Valuation inputs) (output : Fin outputs) : compiled.result.candidate.semantics valuation output = source.candidate.semantics valuation output"
      },
      {
        "name": "physicalOrigin_position",
        "occurrence": 0,
        "signature": "theorem physicalOrigin_position (node : Fin ((ArbitrarySupportSplice.exterior compiled.records).length + compiled.owned.history.state.current.implementation.gateCount)) : compiled.ledger.origin (compiled.owned.compiled.position node) = rawNodeOrigin source.candidate compiled.records compiled.owned.history node"
      },
      {
        "name": "physical_ownership",
        "occurrence": 0,
        "signature": "theorem physical_ownership : compiled.ledger.live.length = compiled.result.gateCount ∧ compiled.ledger.charged.length = compiled.chargedCount ∧ compiled.ledger.removed.length = compiled.removedCount ∧ (compiled.ledger.live ++ compiled.ledger.removed).Nodup ∧ (compiled.ledger.live ++ compiled.ledger.removed).Perm (ambientOriginals source.gateCount ++ compiled.ledger.charged)"
      },
      {
        "name": "charged_origin",
        "occurrence": 0,
        "signature": "theorem charged_origin (origin : PhysicalOrigin source.gateCount) (member : origin ∈ compiled.ledger.charged) : ∃ event ∈ stage.events, ∃ localGate, origin = .allocated event.identity localGate"
      }
    ],
    "guards": [],
    "reviewedNames": [
      "PNP.DirectWire.WireDescendantHistory.StageCompilation.records_source",
      "PNP.DirectWire.WireDescendantHistory.StageCompilation.events_source",
      "PNP.DirectWire.WireDescendantHistory.StageCompilation.existing_result",
      "PNP.DirectWire.WireDescendantHistory.StageCompilation.semantics",
      "PNP.DirectWire.WireDescendantHistory.StageCompilation.physicalOrigin_position",
      "PNP.DirectWire.WireDescendantHistory.StageCompilation.physical_ownership",
      "PNP.DirectWire.WireDescendantHistory.StageCompilation.gate_balance",
      "PNP.DirectWire.WireDescendantHistory.StageCompilation.charged_origin",
      "PNP.DirectWire.WireDescendantHistory.StageCompilation.event_identity_unique",
      "PNP.DirectWire.WireDescendantHistory.compileStage_records_none",
      "PNP.DirectWire.WireDescendantHistory.compileStage_events_none",
      "PNP.DirectWire.WireDescendantHistory.compileStage_history_none"
    ]
  },
  {
    "id": "run",
    "suffix": "Run",
    "path": "lean/PNP/NANDWireDescendantRun.lean",
    "heads": [
      "CompiledRun",
      "result",
      "chargedCount",
      "removedCount",
      "semantics",
      "gate_balance",
      "compile",
      "compile_nil",
      "compile_cons",
      "compile_stage_none",
      "compile_tail_none",
      "compile_cons_some",
      "compile_sound"
    ],
    "imports": [
      "PNP.NANDWireDescendantStage"
    ],
    "context": [
      "namespace PNP.DirectWire.WireDescendantHistory",
      "variable {inputs outputs : Nat}",
      "namespace CompiledRun",
      "variable {source : Implementation inputs outputs} {stages : List RawStage}",
      "end CompiledRun",
      "end PNP.DirectWire.WireDescendantHistory"
    ],
    "blocks": [
      {
        "name": "CompiledRun",
        "occurrence": 0,
        "exact": "inductive CompiledRun : (source : Implementation inputs outputs) → List RawStage → Type where | nil (source : Implementation inputs outputs) : CompiledRun source [] | cons {source : Implementation inputs outputs} {stage : RawStage} {stages : List RawStage} (first : StageCompilation source stage) (rest : CompiledRun first.result stages) : CompiledRun source (stage :: stages)"
      },
      {
        "name": "result",
        "occurrence": 0,
        "exact": "def result {source : Implementation inputs outputs} {stages : List RawStage} : CompiledRun source stages → Implementation inputs outputs | .nil source => source | .cons _ rest => rest.result"
      },
      {
        "name": "chargedCount",
        "occurrence": 0,
        "exact": "def chargedCount {source : Implementation inputs outputs} {stages : List RawStage} : CompiledRun source stages → Nat | .nil _ => 0 | .cons first rest => first.chargedCount + rest.chargedCount"
      },
      {
        "name": "removedCount",
        "occurrence": 0,
        "exact": "def removedCount {source : Implementation inputs outputs} {stages : List RawStage} : CompiledRun source stages → Nat | .nil _ => 0 | .cons first rest => first.removedCount + rest.removedCount"
      },
      {
        "name": "compile",
        "occurrence": 0,
        "exact": "def compile : (source : Implementation inputs outputs) → (stages : List RawStage) → Option (CompiledRun source stages) | source, [] => some (.nil source) | source, stage :: stages => match compileStage source stage with | none => none | some first => (compile first.result stages).map fun rest => .cons first rest"
      },
      {
        "name": "semantics",
        "occurrence": 0,
        "signature": "theorem semantics (run : CompiledRun source stages) (valuation : Valuation inputs) (output : Fin outputs) : run.result.candidate.semantics valuation output = source.candidate.semantics valuation output"
      },
      {
        "name": "gate_balance",
        "occurrence": 0,
        "signature": "theorem gate_balance (run : CompiledRun source stages) : run.result.gateCount + run.removedCount = source.gateCount + run.chargedCount"
      },
      {
        "name": "compile_tail_none",
        "occurrence": 0,
        "signature": "theorem compile_tail_none (source : Implementation inputs outputs) (stage : RawStage) (stages : List RawStage) (first : StageCompilation source stage) (firstAt : compileStage source stage = some first) (rejected : compile first.result stages = none) : compile source (stage :: stages) = none"
      },
      {
        "name": "compile_sound",
        "occurrence": 0,
        "signature": "theorem compile_sound (source : Implementation inputs outputs) (stages : List RawStage) (run : CompiledRun source stages) (_accepted : compile source stages = some run) : (∀ valuation output, run.result.candidate.semantics valuation output = source.candidate.semantics valuation output) ∧ run.result.gateCount + run.removedCount = source.gateCount + run.chargedCount"
      }
    ],
    "guards": [],
    "reviewedNames": [
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.semantics",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.gate_balance",
      "PNP.DirectWire.WireDescendantHistory.compile_nil",
      "PNP.DirectWire.WireDescendantHistory.compile_cons",
      "PNP.DirectWire.WireDescendantHistory.compile_stage_none",
      "PNP.DirectWire.WireDescendantHistory.compile_tail_none",
      "PNP.DirectWire.WireDescendantHistory.compile_cons_some",
      "PNP.DirectWire.WireDescendantHistory.compile_sound"
    ]
  },
  {
    "id": "ledger",
    "suffix": "Ledger",
    "path": "lean/PNP/NANDWireDescendantLedger.lean",
    "heads": [
      "DescendantOrigin",
      "originalOrigins",
      "createdBefore",
      "createdBefore_mono",
      "PersistentOwnership",
      "live",
      "initial",
      "WellFormed",
      "initial_wellFormed",
      "accounted_before",
      "origin_before",
      "origin_injective",
      "liftOrigin",
      "liftOrigin_original",
      "liftOrigin_allocated",
      "liftOrigin_injective",
      "lift_originals",
      "advance",
      "advance_live",
      "advance_charged_length",
      "advance_removed_length",
      "advance_physicalOrigin_position",
      "advance_charge_origin",
      "advance_partition",
      "advance_wellFormed"
    ],
    "imports": [
      "PNP.NANDWireDescendantStage"
    ],
    "context": [
      "namespace PNP.DirectWire.WireDescendantHistory open WireObligationHistory WireHistoryAmbientOwnership",
      "namespace PersistentOwnership",
      "variable {initialGates physicalGates : Nat}",
      "variable {inputs outputs : Nat} {source : Implementation inputs outputs} {stage : RawStage}",
      "end PersistentOwnership",
      "end PNP.DirectWire.WireDescendantHistory"
    ],
    "blocks": [
      {
        "name": "DescendantOrigin",
        "occurrence": 0,
        "exact": "inductive DescendantOrigin (initialGates : Nat) where | original (gate : Fin initialGates) | allocated (stage event localGate : Nat) deriving Repr, DecidableEq"
      },
      {
        "name": "PersistentOwnership",
        "occurrence": 0,
        "exact": "structure PersistentOwnership (initialGates physicalGates : Nat) where origin : Fin physicalGates → DescendantOrigin initialGates charged : List (DescendantOrigin initialGates) removed : List (DescendantOrigin initialGates)"
      },
      {
        "name": "originalOrigins",
        "occurrence": 0,
        "exact": "def originalOrigins (initialGates : Nat) : List (DescendantOrigin initialGates) := List.ofFn DescendantOrigin.original"
      },
      {
        "name": "createdBefore",
        "occurrence": 0,
        "exact": "def createdBefore {initialGates : Nat} (position : Nat) : DescendantOrigin initialGates → Prop | .original _ => True | .allocated stage _ _ => stage < position"
      },
      {
        "name": "live",
        "occurrence": 0,
        "exact": "def live (ledger : PersistentOwnership initialGates physicalGates) : List (DescendantOrigin initialGates) := List.ofFn ledger.origin"
      },
      {
        "name": "initial",
        "occurrence": 0,
        "exact": "def initial (initialGates : Nat) : PersistentOwnership initialGates initialGates := ⟨DescendantOrigin.original, [], []⟩"
      },
      {
        "name": "WellFormed",
        "occurrence": 0,
        "exact": "structure WellFormed (ledger : PersistentOwnership initialGates physicalGates) (position : Nat) : Prop where distinct : (ledger.live ++ ledger.removed).Nodup conserved : (ledger.live ++ ledger.removed).Perm (originalOrigins initialGates ++ ledger.charged) chargedBefore : ∀ origin, origin ∈ ledger.charged → createdBefore position origin"
      },
      {
        "name": "liftOrigin",
        "occurrence": 0,
        "exact": "def liftOrigin (ledger : PersistentOwnership initialGates physicalGates) (position : Nat) : PhysicalOrigin physicalGates → DescendantOrigin initialGates | .original gate => ledger.origin gate | .allocated event localGate => .allocated position event localGate"
      },
      {
        "name": "advance",
        "occurrence": 0,
        "exact": "def advance (ledger : PersistentOwnership initialGates source.gateCount) (position : Nat) (compiled : StageCompilation source stage) : PersistentOwnership initialGates compiled.result.gateCount := ⟨fun gate => ledger.liftOrigin position (compiled.ledger.origin gate), ledger.charged ++ compiled.ledger.charged.map (ledger.liftOrigin position), ledger.removed ++ compiled.ledger.removed.map (ledger.liftOrigin position)⟩"
      },
      {
        "name": "advance_physicalOrigin_position",
        "occurrence": 0,
        "signature": "theorem advance_physicalOrigin_position (ledger : PersistentOwnership initialGates source.gateCount) (position : Nat) (compiled : StageCompilation source stage) (node : Fin ((ArbitrarySupportSplice.exterior compiled.records).length + compiled.owned.history.state.current.implementation.gateCount)) : (ledger.advance position compiled).origin (compiled.owned.compiled.position node) = ledger.liftOrigin position (rawNodeOrigin source.candidate compiled.records compiled.owned.history node)"
      },
      {
        "name": "advance_charge_origin",
        "occurrence": 0,
        "signature": "theorem advance_charge_origin (ledger : PersistentOwnership initialGates source.gateCount) (position : Nat) (compiled : StageCompilation source stage) (origin : DescendantOrigin initialGates) (member : origin ∈ compiled.ledger.charged.map (ledger.liftOrigin position)) : ∃ event ∈ stage.events, ∃ localGate, origin = .allocated position event.identity localGate"
      },
      {
        "name": "advance_partition",
        "occurrence": 0,
        "signature": "theorem advance_partition (ledger : PersistentOwnership initialGates source.gateCount) (position : Nat) (compiled : StageCompilation source stage) (checked : WellFormed ledger position) : ((ledger.advance position compiled).live ++ (ledger.advance position compiled).removed).Perm (originalOrigins initialGates ++ (ledger.advance position compiled).charged)"
      },
      {
        "name": "advance_wellFormed",
        "occurrence": 0,
        "signature": "theorem advance_wellFormed (ledger : PersistentOwnership initialGates source.gateCount) (position : Nat) (compiled : StageCompilation source stage) (checked : WellFormed ledger position) : WellFormed (ledger.advance position compiled) (position + 1)"
      }
    ],
    "guards": [],
    "reviewedNames": [
      "PNP.DirectWire.WireDescendantHistory.createdBefore_mono",
      "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.initial_wellFormed",
      "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.accounted_before",
      "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.origin_before",
      "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.origin_injective",
      "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.liftOrigin_original",
      "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.liftOrigin_allocated",
      "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.liftOrigin_injective",
      "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.lift_originals",
      "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.advance_live",
      "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.advance_charged_length",
      "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.advance_removed_length",
      "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.advance_physicalOrigin_position",
      "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.advance_charge_origin",
      "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.advance_partition",
      "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.advance_wellFormed"
    ]
  },
  {
    "id": "ownership",
    "suffix": "Ownership",
    "path": "lean/PNP/NANDWireDescendantOwnership.lean",
    "heads": [
      "carry",
      "carry_nil",
      "carry_cons",
      "carry_wellFormed",
      "carry_charged_length",
      "carry_removed_length",
      "carry_charge_survives",
      "ledger",
      "ledger_nil",
      "ledger_wellFormed",
      "physical_ownership",
      "ledger_origin_injective",
      "ledger_charged_before"
    ],
    "imports": [
      "PNP.NANDWireDescendantRun",
      "PNP.NANDWireDescendantLedger"
    ],
    "context": [
      "namespace PNP.DirectWire.WireDescendantHistory.CompiledRun",
      "variable {inputs outputs initialGates : Nat}",
      "variable {source : Implementation inputs outputs} {stage : RawStage} {stages : List RawStage}",
      "end PNP.DirectWire.WireDescendantHistory.CompiledRun"
    ],
    "blocks": [
      {
        "name": "carry",
        "occurrence": 0,
        "exact": "def carry {initialGates : Nat} {source : Implementation inputs outputs} {stages : List RawStage} (run : CompiledRun source stages) (position : Nat) (ledger : PersistentOwnership initialGates source.gateCount) : PersistentOwnership initialGates run.result.gateCount := match run with | .nil _ => ledger | .cons first rest => rest.carry (position + 1) (ledger.advance position first)"
      },
      {
        "name": "ledger",
        "occurrence": 0,
        "exact": "def ledger (run : CompiledRun source stages) : PersistentOwnership source.gateCount run.result.gateCount := run.carry 0 (PersistentOwnership.initial source.gateCount)"
      },
      {
        "name": "carry_wellFormed",
        "occurrence": 0,
        "signature": "theorem carry_wellFormed (run : CompiledRun source stages) : ∀ (position : Nat) (ledger : PersistentOwnership initialGates source.gateCount), PersistentOwnership.WellFormed ledger position → PersistentOwnership.WellFormed (run.carry position ledger) (position + stages.length)"
      },
      {
        "name": "carry_charged_length",
        "occurrence": 0,
        "signature": "theorem carry_charged_length (run : CompiledRun source stages) : ∀ (position : Nat) (ledger : PersistentOwnership initialGates source.gateCount), (run.carry position ledger).charged.length = ledger.charged.length + run.chargedCount"
      },
      {
        "name": "carry_removed_length",
        "occurrence": 0,
        "signature": "theorem carry_removed_length (run : CompiledRun source stages) : ∀ (position : Nat) (ledger : PersistentOwnership initialGates source.gateCount), (run.carry position ledger).removed.length = ledger.removed.length + run.removedCount"
      },
      {
        "name": "physical_ownership",
        "occurrence": 0,
        "signature": "theorem physical_ownership (run : CompiledRun source stages) : run.ledger.live.length = run.result.gateCount ∧ run.ledger.charged.length = run.chargedCount ∧ run.ledger.removed.length = run.removedCount ∧ (run.ledger.live ++ run.ledger.removed).Nodup ∧ (run.ledger.live ++ run.ledger.removed).Perm (originalOrigins source.gateCount ++ run.ledger.charged)"
      }
    ],
    "guards": [],
    "reviewedNames": [
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.carry_nil",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.carry_cons",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.carry_wellFormed",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.carry_charged_length",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.carry_removed_length",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.carry_charge_survives",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.ledger_nil",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.ledger_wellFormed",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.physical_ownership",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.ledger_origin_injective",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.ledger_charged_before"
    ]
  },
  {
    "id": "events",
    "suffix": "Events",
    "path": "lean/PNP/NANDWireDescendantEvents.lean",
    "heads": [
      "inputEventKeys",
      "inputEventKeys_nil",
      "inputEventKeys_cons",
      "inputEventKeys_bounds",
      "StageCompilation.rawEventIdentities_nodup",
      "inputEventKeys_nodup",
      "inputEventKeys_unique",
      "carry_charged_origin",
      "ledger_charged_origin",
      "ledger_live_allocated_event"
    ],
    "imports": [
      "PNP.NANDWireDescendantOwnership"
    ],
    "context": [
      "namespace PNP.DirectWire.WireDescendantHistory",
      "namespace CompiledRun",
      "variable {inputs outputs initialGates : Nat}",
      "variable {source : Implementation inputs outputs} {stages : List RawStage}",
      "end CompiledRun",
      "end PNP.DirectWire.WireDescendantHistory"
    ],
    "blocks": [
      {
        "name": "inputEventKeys",
        "occurrence": 0,
        "exact": "def inputEventKeys : Nat → List RawStage → List (Nat × Nat) | _, [] => [] | position, stage :: stages => stage.events.map (fun event => (position, event.identity)) ++ inputEventKeys (position + 1) stages"
      },
      {
        "name": "StageCompilation.rawEventIdentities_nodup",
        "occurrence": 0,
        "signature": "theorem StageCompilation.rawEventIdentities_nodup {inputs outputs : Nat} {source : Implementation inputs outputs} {stage : RawStage} (compiled : StageCompilation source stage) : (stage.events.map EventInput.identity).Nodup"
      },
      {
        "name": "inputEventKeys_nodup",
        "occurrence": 0,
        "signature": "theorem inputEventKeys_nodup (run : CompiledRun source stages) : ∀ position, (inputEventKeys position stages).Nodup"
      },
      {
        "name": "carry_charged_origin",
        "occurrence": 0,
        "signature": "theorem carry_charged_origin (run : CompiledRun source stages) : ∀ (position : Nat) (ledger : PersistentOwnership initialGates source.gateCount) (origin : DescendantOrigin initialGates), origin ∈ (run.carry position ledger).charged → origin ∈ ledger.charged ∨ ∃ stagePosition identity localGate, origin = .allocated stagePosition identity localGate ∧ (stagePosition, identity) ∈ inputEventKeys position stages"
      },
      {
        "name": "ledger_charged_origin",
        "occurrence": 0,
        "signature": "theorem ledger_charged_origin (run : CompiledRun source stages) (origin : DescendantOrigin source.gateCount) (member : origin ∈ run.ledger.charged) : ∃ stagePosition identity localGate, origin = .allocated stagePosition identity localGate ∧ (stagePosition, identity) ∈ inputEventKeys 0 stages"
      },
      {
        "name": "ledger_live_allocated_event",
        "occurrence": 0,
        "signature": "theorem ledger_live_allocated_event (run : CompiledRun source stages) (gate : Fin run.result.gateCount) (stagePosition identity localGate : Nat) (originAt : run.ledger.origin gate = .allocated stagePosition identity localGate) : (stagePosition, identity) ∈ inputEventKeys 0 stages"
      }
    ],
    "guards": [],
    "reviewedNames": [
      "PNP.DirectWire.WireDescendantHistory.inputEventKeys_nil",
      "PNP.DirectWire.WireDescendantHistory.inputEventKeys_cons",
      "PNP.DirectWire.WireDescendantHistory.inputEventKeys_bounds",
      "PNP.DirectWire.WireDescendantHistory.StageCompilation.rawEventIdentities_nodup",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.inputEventKeys_nodup",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.inputEventKeys_unique",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.carry_charged_origin",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.ledger_charged_origin",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.ledger_live_allocated_event"
    ]
  },
  {
    "id": "charges",
    "suffix": "Charges",
    "path": "lean/PNP/NANDWireDescendantCharges.lean",
    "heads": [
      "allocationEventKey",
      "eventRequests",
      "eventRequests_member",
      "eventRequests_disjoint",
      "eventOwner_some_iff",
      "eventOwner_none_iff",
      "materializer",
      "support_membership",
      "support_restrict",
      "materializer_gateCount",
      "materializer_chargeIdentity",
      "materializer_wholeCharge",
      "materializer_semantics",
      "materializer_induced"
    ],
    "imports": [
      "PNP.NANDWireDescendantEvents"
    ],
    "context": [
      "namespace PNP.DirectWire.WireDescendantHistory",
      "namespace CompiledRun",
      "variable {inputs outputs : Nat}",
      "variable {source : Implementation inputs outputs} {stages : List RawStage}",
      "variable (run : CompiledRun source stages)",
      "variable {supportWidth : Nat}",
      "end CompiledRun",
      "end PNP.DirectWire.WireDescendantHistory"
    ],
    "blocks": [
      {
        "name": "allocationEventKey",
        "occurrence": 0,
        "exact": "def allocationEventKey {initialGates : Nat} : DescendantOrigin initialGates → Option (Nat × Nat) | .original _ => none | .allocated position identity _ => some (position, identity)"
      },
      {
        "name": "eventRequests",
        "occurrence": 0,
        "exact": "def eventRequests (owner : Fin (inputEventKeys 0 stages).length) : List (Fin run.result.gateCount) := (allFin run.result.gateCount).filter fun gate => decide (allocationEventKey (run.ledger.origin gate) = some ((inputEventKeys 0 stages).get owner))"
      },
      {
        "name": "materializer",
        "occurrence": 0,
        "exact": "def materializer (support : List (TerminalPrimitiveRecord inputs run.result.gateCount outputs supportWidth)) (owner : Option (Fin (inputEventKeys 0 stages).length)) : TerminalExtractedSupport (profileWidth := supportWidth) run.result.candidate := terminalOwnedPhysicalMaterializer run.result.candidate run.eventRequests support owner"
      },
      {
        "name": "eventRequests_disjoint",
        "occurrence": 0,
        "signature": "theorem eventRequests_disjoint (left right : Fin (inputEventKeys 0 stages).length) (different : left ≠ right) (gate : Fin run.result.gateCount) (inLeft : gate ∈ run.eventRequests left) : gate ∉ run.eventRequests right"
      },
      {
        "name": "eventOwner_none_iff",
        "occurrence": 0,
        "signature": "theorem eventOwner_none_iff (gate : Fin run.result.gateCount) : terminalPhysicalOwner run.eventRequests gate = none ↔ allocationEventKey (run.ledger.origin gate) = none"
      },
      {
        "name": "support_membership",
        "occurrence": 0,
        "signature": "theorem support_membership (support : List (TerminalPrimitiveRecord inputs run.result.gateCount outputs supportWidth)) (owner : Fin (inputEventKeys 0 stages).length) (gate : Fin run.result.gateCount) : gate ∈ terminalOwnedPhysicalGates run.eventRequests support (some owner) ↔ gate ∈ terminalSelectedGates support ∧ allocationEventKey (run.ledger.origin gate) = some ((inputEventKeys 0 stages).get owner)"
      },
      {
        "name": "support_restrict",
        "occurrence": 0,
        "signature": "theorem support_restrict (larger smaller : List (TerminalPrimitiveRecord inputs run.result.gateCount outputs supportWidth)) (included : ∀ gate, gate ∈ terminalSelectedGates smaller → gate ∈ terminalSelectedGates larger) (owner : Option (Fin (inputEventKeys 0 stages).length)) (gate : Fin run.result.gateCount) (member : gate ∈ terminalOwnedPhysicalGates run.eventRequests smaller owner) : gate ∈ terminalOwnedPhysicalGates run.eventRequests larger owner"
      },
      {
        "name": "materializer_chargeIdentity",
        "occurrence": 0,
        "signature": "theorem materializer_chargeIdentity (support : List (TerminalPrimitiveRecord inputs run.result.gateCount outputs supportWidth)) : ((terminalPhysicalOwners (inputEventKeys 0 stages).length).map (fun owner => (run.materializer support owner).gateCount)).sum = (extractTerminalSupport run.result.candidate support).gateCount"
      },
      {
        "name": "materializer_semantics",
        "occurrence": 0,
        "signature": "theorem materializer_semantics (support : List (TerminalPrimitiveRecord inputs run.result.gateCount outputs supportWidth)) (owner : Option (Fin (inputEventKeys 0 stages).length)) (boundaryValuation : Valuation (terminalBoundaryPorts run.result.candidate.program (terminalOwnedPhysicalRecords run.eventRequests support owner)).length) (output : Fin (terminalInterfacePorts run.result.candidate (terminalOwnedPhysicalRecords run.eventRequests support owner)).length) : (run.materializer support owner).extractedCandidate.semantics boundaryValuation output = terminalOpenSupportSemantics run.result.candidate (terminalOwnedPhysicalRecords run.eventRequests support owner) boundaryValuation output"
      }
    ],
    "guards": [],
    "reviewedNames": [
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.eventRequests_member",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.eventRequests_disjoint",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.eventOwner_some_iff",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.eventOwner_none_iff",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.support_membership",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.support_restrict",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.materializer_gateCount",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.materializer_chargeIdentity",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.materializer_wholeCharge",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.materializer_semantics",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.materializer_induced"
    ]
  },
  {
    "id": "gain",
    "suffix": "Gain",
    "path": "lean/PNP/NANDWireDescendantGain.lean",
    "heads": [
      "CompiledRun.strictGain",
      "GainResult",
      "strictGain",
      "strictResidualDescent",
      "compileGain",
      "compileGain_compile_none",
      "compileGain_no_gain",
      "compileGain_complete",
      "compileGain_exists_iff"
    ],
    "imports": [
      "PNP.NANDWireDescendantCharges",
      "PNP.ResidualRoutes"
    ],
    "context": [
      "namespace PNP.DirectWire.WireDescendantHistory",
      "variable {inputs outputs : Nat}",
      "namespace GainResult",
      "variable {source : Implementation inputs outputs} {stages : List RawStage}",
      "variable (gain : GainResult source stages)",
      "end GainResult",
      "end PNP.DirectWire.WireDescendantHistory"
    ],
    "blocks": [
      {
        "name": "GainResult",
        "occurrence": 0,
        "exact": "structure GainResult (source : Implementation inputs outputs) (stages : List RawStage) where run : CompiledRun source stages runAt : compile source stages = some run smaller : run.result.gateCount < source.gateCount"
      },
      {
        "name": "compileGain",
        "occurrence": 0,
        "exact": "def compileGain (source : Implementation inputs outputs) (stages : List RawStage) : Option (GainResult source stages) := match runAt : compile source stages with | none => none | some run => if smaller : run.result.gateCount < source.gateCount then some ⟨run, runAt, smaller⟩ else none"
      },
      {
        "name": "CompiledRun.strictGain",
        "occurrence": 0,
        "signature": "theorem CompiledRun.strictGain {source : Implementation inputs outputs} {stages : List RawStage} (run : CompiledRun source stages) (smaller : run.result.gateCount < source.gateCount) : StrictEquivalentGain source run.result"
      },
      {
        "name": "strictResidualDescent",
        "occurrence": 0,
        "signature": "theorem strictResidualDescent : residualSlack gain.run.result < residualSlack source"
      },
      {
        "name": "compileGain_complete",
        "occurrence": 0,
        "signature": "theorem compileGain_complete (source : Implementation inputs outputs) (stages : List RawStage) (run : CompiledRun source stages) (accepted : compile source stages = some run) (smaller : run.result.gateCount < source.gateCount) : ∃ gain, compileGain source stages = some gain ∧ gain.run = run"
      },
      {
        "name": "compileGain_exists_iff",
        "occurrence": 0,
        "signature": "theorem compileGain_exists_iff (source : Implementation inputs outputs) (stages : List RawStage) (run : CompiledRun source stages) (accepted : compile source stages = some run) : (∃ gain, compileGain source stages = some gain) ↔ run.result.gateCount < source.gateCount"
      }
    ],
    "guards": [],
    "reviewedNames": [
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.strictGain",
      "PNP.DirectWire.WireDescendantHistory.GainResult.strictGain",
      "PNP.DirectWire.WireDescendantHistory.GainResult.strictResidualDescent",
      "PNP.DirectWire.WireDescendantHistory.compileGain_compile_none",
      "PNP.DirectWire.WireDescendantHistory.compileGain_no_gain",
      "PNP.DirectWire.WireDescendantHistory.compileGain_complete",
      "PNP.DirectWire.WireDescendantHistory.compileGain_exists_iff"
    ]
  }
];

const text0 = file => readFile(new URL('../' + file,import.meta.url),'utf8');
const compact0 = source => stripLeanCommentsAndStrings0(source).replace(/\s+/gu,' ').trim();
function boundaries0(source) {
  return [...stripLeanCommentsAndStrings0(source).matchAll(
    /^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*(?:(def|theorem|inductive|structure|abbrev)[ \t]+([^\s({:]+)|(variable|namespace|end)\b)/gmu)];
}
function block0(source,name,occurrence=0) {
  const boundaries=boundaries0(source);
  const selected=boundaries.map((match,index)=>({match,index}))
    .filter(({match})=>match[2]===name)[occurrence];
  return selected ? compact0(source.slice(selected.match.index,
    boundaries[selected.index+1]?.index??source.length)) : '';
}
function context0(source) {
  const boundaries=boundaries0(source);
  return boundaries.flatMap((match,index)=>match[3]
    ? [compact0(source.slice(match.index,boundaries[index+1]?.index??source.length))] : []);
}
function inspect0(source,spec) {
  const failures=[],clean=compact0(source);
  const require0=(condition,label)=>{if(!condition)failures.push(label);};
  require0(!hasLeanAssumptionDeclaration0(source),'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source),'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|noncomputable|Classical|implemented_by|csimp)\b|#(?:eval|reduce|guard|synth)\b/u.test(clean),'shortcut');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name))===
    JSON.stringify(spec.heads),'closed-declarations');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]))===
    JSON.stringify(spec.imports),'closed-imports');
  require0(JSON.stringify(context0(source))===JSON.stringify(spec.context),'closed-context');
  for(const expected of spec.blocks) {
    const actual=block0(source,expected.name,expected.occurrence);
    require0(expected.exact ? actual===expected.exact : actual.startsWith(expected.signature+' :='),
      'block:'+expected.name+'#'+expected.occurrence);
  }
  for(const guard of spec.guards)
    require0(block0(source,guard.name,guard.occurrence??0).includes(guard.fragment),guard.label);
  return failures;
}
let loaded;
function sources0() {
  loaded??=Promise.all(SPECS.map(async spec=>({spec,source:await text0(spec.path)})));
  return loaded;
}
async function mutations0(mutations) {
  const rows=new Map((await sources0()).map(row=>[row.spec.id,row]));
  for(const [id,before,after,category] of mutations) {
    const {spec,source}=rows.get(id);
    assert.ok(source.includes(before),'missing mutation anchor: '+category);
    assert.ok(inspect0(source.replaceAll(before,after),spec).includes(category),category);
  }
}


test('M267 closes the eight source-only descendant program interfaces',async()=>{
  for(const {spec,source} of await sources0())assert.deepEqual(inspect0(source,spec),[],spec.path);
});

test('M267 rejects hidden inputs, new assumptions, unchecked authority and altered namespaces',async()=>{
  for(const {spec,source} of await sources0()) {
    assert.ok(inspect0(source+'\naxiom hiddenOwner : False\n',spec).includes('assumption'));
    assert.ok(inspect0(source+'\nunsafe def uncheckedOwner : Nat := 0\n',spec).includes('shortcut'));
    assert.ok(inspect0(source+'\nexample : True := True.intro\n',spec).includes('unaudited-form'));
    assert.ok(inspect0(source+'\ntheorem extraOwner : True := True.intro\n',spec).includes('closed-declarations'));
    assert.ok(inspect0(source+'\nvariable (callerMap : Nat)\n',spec).includes('closed-context'));
    assert.ok(inspect0('import PNP.Main\n'+source,spec).includes('closed-imports'));
    assert.deepEqual(inspect0(source+'\n/- supplied authority and Classical are not used -/\n',spec),[]);
  }
});

test('M267 raw inputs preserve exact finite coordinates, action kinds and event data',async()=>{
  await mutations0([
    ['input','profileWidth : Nat\n  records : List RawRecord','profileWidth : Nat\n  supplied : Nat\n  records : List RawRecord','block:RawStage#0'],
    ['input','if valid : index < gates then','if valid : index < inputs then','block:decodeRecord#0'],
    ['input','raw.mapM (decodeRecord inputs gates outputs profileWidth)','raw.filterMap (decodeRecord inputs gates outputs profileWidth)','block:decodeRecords#0'],
    ['input','| realizeR7 (creationID : Nat) (records : List RawSupportRecord)','| realizeR7 (creationID : Nat)','block:RawAction#0'],
    ['input','| .realizeR7 identity records => some (.realizeR7 identity records)','| .realizeR7 identity records => some (.realizeR7 identity [])','block:decodeAction#0'],
    ['input','predecessorIDs := raw.predecessorIDs','predecessorIDs := []','block:decodeEvent#0'],
    ['input','identity := raw.identity','identity := 0','block:decodeEvent#0'],
    ['input','events.map encodeEvent = raw','True','block:decodeEvents_source#0'],
  ]);
});

test('M267 stages use the actual descendant, accepted history and literal compiler map',async()=>{
  await mutations0([
    ['stage','decodeRecords inputs source.gateCount outputs stage.profileWidth stage.records','decodeRecords inputs 0 outputs stage.profileWidth stage.records','block:compileStage#0'],
    ['stage','decodeEvents (terminalInterfacePorts source.candidate records).length stage.events','decodeEvents 0 stage.events','block:compileStage#0'],
    ['stage','match ownedAt : compileOwned source.candidate records events with','match ownedAt : suppliedHistory with','block:compileStage#0'],
    ['stage','compiled.owned.history.execution.charged','compiled.ledger.charged.length','block:chargedCount#0'],
    ['stage','compiled.owned.history.execution.removed','compiled.ledger.removed.length','block:removedCount#0'],
    ['stage','compiled.ledger.origin (compiled.owned.compiled.position node)','compiled.ledger.origin node','block:physicalOrigin_position#0'],
  ]);
});

test('M267 full execution follows changing descendants and never returns an accepted prefix',async()=>{
  await mutations0([
    ['run','(rest : CompiledRun first.result stages)','(rest : CompiledRun source stages)','block:CompiledRun#0'],
    ['run','(compile first.result stages).map fun rest => .cons first rest','some (.nil source)','block:compile#0'],
    ['run','| none => none','| none => some (.nil source)','block:compile#0'],
    ['run','first.chargedCount + rest.chargedCount','rest.chargedCount','block:chargedCount#0'],
    ['run','first.removedCount + rest.removedCount','rest.removedCount','block:removedCount#0'],
    ['run','source.gateCount + run.chargedCount','source.gateCount','block:gate_balance#0'],
  ]);
});

test('M267 persistent identities follow actual positions and retain removed allocation charges',async()=>{
  await mutations0([
    ['ledger','| allocated (stage event localGate : Nat)','| allocated (event localGate : Nat)','block:DescendantOrigin#0'],
    ['ledger','| .original gate => ledger.origin gate','| .original gate => .original gate','block:liftOrigin#0'],
    ['ledger','| .allocated event localGate => .allocated position event localGate','| .allocated event localGate => .allocated 0 event localGate','block:liftOrigin#0'],
    ['ledger','ledger.liftOrigin position (compiled.ledger.origin gate)','ledger.liftOrigin position (.original gate)','block:advance#0'],
    ['ledger','ledger.charged ++ compiled.ledger.charged.map','compiled.ledger.charged.map','block:advance#0'],
    ['ledger','ledger.removed ++ compiled.ledger.removed.map','compiled.ledger.removed.map','block:advance#0'],
    ['ledger','(ledger.live ++ ledger.removed).Nodup','True','block:WellFormed#0'],
    ['ledger','origin ∈ ledger.charged → createdBefore position origin','True','block:WellFormed#0'],
    ['ledger','(ledger.advance position compiled).origin (compiled.owned.compiled.position node)','unrelatedPosition node','block:advance_physicalOrigin_position#0'],
  ]);
});

test('M267 arbitrary-program ownership is computed, source-initialized and fully conserved',async()=>{
  await mutations0([
    ['ownership','rest.carry (position + 1) (ledger.advance position first)','rest.carry position ledger','block:carry#0'],
    ['ownership','run.carry 0 (PersistentOwnership.initial source.gateCount)','suppliedLedger','block:ledger#0'],
    ['ownership','run.ledger.charged.length = run.chargedCount','True','block:physical_ownership#0'],
    ['ownership','run.ledger.removed.length = run.removedCount','True','block:physical_ownership#0'],
    ['ownership','(run.ledger.live ++ run.ledger.removed).Nodup','True','block:physical_ownership#0'],
    ['ownership','(originalOrigins source.gateCount ++ run.ledger.charged)','(originalOrigins source.gateCount)','block:physical_ownership#0'],
  ]);
});

test('M267 event provenance comes from the raw program and computed stage positions',async()=>{
  await mutations0([
    ['events','(fun event => (position, event.identity))','(fun event => (0, event.identity))','block:inputEventKeys#0'],
    ['events','inputEventKeys (position + 1) stages','inputEventKeys position stages','block:inputEventKeys#0'],
    ['events','(stagePosition, identity) ∈ inputEventKeys 0 stages','True','block:ledger_charged_origin#0'],
    ['events','(stagePosition, identity) ∈ inputEventKeys 0 stages','True','block:ledger_live_allocated_event#0'],
  ]);
});

test('M267 owner requests are disjoint, support-independent and use actual extracted charges',async()=>{
  await mutations0([
    ['charges','def eventRequests (owner :','def eventRequests (suppliedMap : Nat) (owner :','block:eventRequests#0'],
    ['charges','some ((inputEventKeys 0 stages).get owner)','some (0, owner.val)','block:eventRequests#0'],
    ['charges','terminalOwnedPhysicalMaterializer run.result.candidate run.eventRequests support owner','suppliedMaterializer owner','block:materializer#0'],
    ['charges','allocationEventKey (run.ledger.origin gate) = none','True','block:eventOwner_none_iff#0'],
    ['charges','(run.materializer support owner).gateCount','run.ledger.charged.length','block:materializer_chargeIdentity#0'],
  ]);
});

test('M267 final gain checks complete execution and final size without a search oracle',async()=>{
  await mutations0([
    ['gain','match runAt : compile source stages with','match runAt : suppliedRun with','block:compileGain#0'],
    ['gain','if smaller : run.result.gateCount < source.gateCount then','if smaller : True then','block:compileGain#0'],
    ['gain','runAt : compile source stages = some run','runAt : True','block:GainResult#0'],
    ['gain','(smaller : run.result.gateCount < source.gateCount)','(smaller : True)','block:CompiledRun.strictGain#0'],
  ]);
  const {source}= (await sources0()).find(row=>row.spec.id==='gain');
  const clean=compact0(source);
  assert.doesNotMatch(clean,/\b(?:equivalentBool|strictEquivalentGainBool|referenceMinimum|allCandidates|native_decide)\b/u);
  assert.ok(clean.includes('fun valuation output => run.semantics valuation output'));
  assert.ok(clean.includes('gain.strictGain.strictResidualDescent'));
});

test('M267 explicit-root audit and targeted fixtures cover the complete reviewed name family',async()=>{
  const audit=await text0('lean-audit/PNPDescendantHistoryOwnershipAxiomAudit.lean');
  const root=await text0('lean/PNP.lean');
  assert.match(audit,/^import PNP$/mu);
  const names=SPECS.flatMap(spec=>spec.reviewedNames);
  assert.equal(names.length,84);
  assert.equal(new Set(names).size,84);
  assert.deepEqual([...audit.matchAll(/^#print axioms (\S+)$/gmu)].map(m=>m[1]),names);
  for(const spec of SPECS) {
    assert.ok(root.includes('import PNP.NANDWireDescendant'+spec.suffix));
    const fixture=await text0('lean-regression/PNPWireDescendant'+spec.suffix+'.lean');
    const printed=[...fixture.matchAll(/^#print axioms (\S+)$/gmu)].map(m=>m[1]);
    assert.equal(printed.length,spec.reviewedNames.length,spec.suffix);
    for(const [index,name] of printed.entries())
      assert.ok(spec.reviewedNames[index]===name || spec.reviewedNames[index].endsWith('.'+name),name);
    if(spec.id==='input') {
      const normalized=fixture.replace(/\s+/gu,' ');
      for(const checked of [
        'example : decodeRecords 0 0 0 0 [] = some [] := rfl',
        'example : decodeRecords 2 2 2 2 [.gate 0, .gate 2] = none := by decide',
        'example : decodeAction 0 (.realizeR7 42 [.gate 999]) = some (.realizeR7 42 [.gate 999]) := rfl',
      ]) assert.ok(normalized.includes(checked),checked);
      assert.doesNotMatch(fixture,/\bnative_decide\b|\bdecide\s+\+native\b/u);
    } else {
      assert.match(fixture,/^#eval\b/mu,spec.suffix);
      assert.ok(fixture.includes('throw (IO.userError'),spec.suffix);
    }
  }
});

test('M267 regressions distinguish temporary growth, historical removal and surviving pieces',async()=>{
  const ownership=await text0('lean-regression/PNPWireDescendantOwnership.lean');
  assert.ok(ownership.includes('whole fold failed to compose the intermediate physical positions'));
  assert.ok(ownership.includes('complete fold relabelled a removed allocation'));
  const events=await text0('lean-regression/PNPWireDescendantEvents.lean');
  assert.ok(events.includes('input event family concealed duplicate raw identities'));
  const charges=await text0('lean-regression/PNPWireDescendantCharges.lean');
  assert.ok(charges.includes('selectedCharges != [0, 0, 1, 0, 1]'));
  assert.ok(charges.includes('wholeCharges != [4, 0, 1, 0, 1]'));
  const gain=(await text0('lean-regression/PNPWireDescendantGain.lean')).replace(/\s+/gu,' ');
  assert.ok(gain.includes('first.result.gateCount != 6 || second.result.gateCount != 7'));
  assert.ok(gain.includes('gain.run.result.gateCount != 4 || gain.run.chargedCount != 2 || gain.run.removedCount != 3'));
  assert.ok(gain.includes('net-gain removal history lost an original gate or a stage-qualified allocation'));
  assert.ok(gain.includes('malformed late stage returned a partial gain'));
});
