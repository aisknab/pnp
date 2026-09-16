import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Reviewed source boundaries, not evidence generated at test time.
// Keep complete let-bound theorem conclusions: stopping at the first := would
// accidentally pin only the local ledger binding and miss conservation itself.
// Kernel/type/axiom checks remain the mathematical authority.
const SPECS = [
  {
    "id": "normalization",
    "path": "lean/PNP/NANDPhysicalGateProvenance.lean",
    "heads": [
      "constantGate",
      "constantOrigins",
      "constantOrigins_length",
      "constantOrigins_nodup",
      "sharingGate",
      "sharingOrigins",
      "sharingOrigins_length",
      "sharingOrigins_nodup",
      "sourcePosition",
      "constantPosition",
      "constantOrigins_positions",
      "sharingPosition",
      "sharingOrigins_positions",
      "constantOrigin",
      "constantOrigin_position",
      "constantOrigin_alias",
      "constantOrigin_injective",
      "sharingOrigin",
      "sharingOrigin_position",
      "sharingOrigin_alias",
      "sharingOrigin_injective",
      "coneOrigin",
      "coneOrigin_selected",
      "coneOrigin_position",
      "coneOrigin_injective",
      "coneOrigin_image",
      "passOrigin",
      "passOrigin_injective",
      "traceOrigin",
      "traceOrigin_injective",
      "normalizedOrigin",
      "normalizedOrigin_injective",
      "passRetained",
      "passRemoved",
      "passRemoved_iff",
      "pass_partition",
      "traceRetained",
      "traceRemoved",
      "traceRemoved_iff",
      "trace_partition",
      "normalizedRetained",
      "normalizedRemoved",
      "normalizedRemoved_iff",
      "normalized_partition"
    ],
    "imports": [
      "PNP.PCCMinPhysicalNormalizationClosure"
    ],
    "context": [
      "namespace PNP.DirectWire.PhysicalGateProvenance",
      "end PNP.DirectWire.PhysicalGateProvenance"
    ],
    "blocks": [
      {
        "name": "passOrigin",
        "occurrence": 0,
        "exact": "def passOrigin {inputs outputs : Nat} (pass : PhysicalNormalizationPass) (current : Implementation inputs outputs) : Fin (physicalNormalizationPassResult pass current).gateCount → Fin current.gateCount := match pass with | .constants => constantOrigin current.candidate.program | .sharing => sharingOrigin current.candidate.program | .pruning => coneOrigin current"
      },
      {
        "name": "traceOrigin",
        "occurrence": 0,
        "exact": "def traceOrigin {inputs outputs : Nat} {current final : Implementation inputs outputs} : PhysicalNormalizationTrace current final → Fin final.gateCount → Fin current.gateCount | .done _ _ => fun position => position | .step gain tail => fun position => gainOrigin gain (traceOrigin tail position)"
      },
      {
        "name": "normalizedOrigin",
        "occurrence": 0,
        "exact": "def normalizedOrigin {inputs outputs : Nat} (current : Implementation inputs outputs) : Fin (runPhysicalNormalization current).result.gateCount → Fin current.gateCount := traceOrigin (runPhysicalNormalization current).trace"
      },
      {
        "name": "normalized_partition",
        "occurrence": 0,
        "signature": "theorem normalized_partition {inputs outputs : Nat} (current : Implementation inputs outputs) : (normalizedRetained current).length = (runPhysicalNormalization current).result.gateCount ∧ (normalizedRemoved current).length = (runPhysicalNormalization current).trace.savedGates ∧ (normalizedRetained current ++ normalizedRemoved current).Nodup ∧ (normalizedRetained current ++ normalizedRemoved current).Perm (allFin current.gateCount)"
      },
      {
        "name": "constantOrigins",
        "occurrence": 0,
        "exact": "def constantOrigins {inputs gates : Nat} (program : Program inputs gates) : List (Fin gates) := match program with | .empty => [] | .snoc initial gate => match constantGateValue (constantGate initial gate) with | none => (constantOrigins initial).map Fin.castSucc ++ [Fin.last _] | some _ => (constantOrigins initial).map Fin.castSucc"
      },
      {
        "name": "sharingOrigins",
        "occurrence": 0,
        "exact": "def sharingOrigins {inputs gates : Nat} (program : Program inputs gates) : List (Fin gates) := match program with | .empty => [] | .snoc initial gate => match sharingFindGate (compileNANDSharing initial).program (sharingGate initial gate) with | none => (sharingOrigins initial).map Fin.castSucc ++ [Fin.last _] | some _ => (sharingOrigins initial).map Fin.castSucc"
      }
    ],
    "guards": []
  },
  {
    "id": "history",
    "path": "lean/PNP/NANDWireHistoryPhysicalOwnership.lean",
    "heads": [
      "PhysicalOrigin",
      "PhysicalOwnership",
      "live",
      "initial",
      "append",
      "append_origin_left",
      "append_origin_right",
      "append_live",
      "normalize",
      "normalize_partition",
      "normalize_removed_length",
      "sourcePhysicalOrigins",
      "physicalOwnership",
      "restore_physical_positions",
      "realize_physical_positions",
      "allocations",
      "allocations_nodup",
      "physical_charged",
      "physical_removed_length",
      "physical_conservation",
      "physicalOwnership",
      "allocations",
      "allocations_length",
      "physical_charged",
      "physical_removed_length",
      "physical_conservation",
      "allocations_member",
      "allocations_nodup",
      "physicalOwnership",
      "physical_charged",
      "physical_partition",
      "physical_ownership"
    ],
    "imports": [
      "PNP.NANDWireObligationHistoryExecution",
      "PNP.NANDPhysicalGateProvenance"
    ],
    "context": [
      "namespace PNP.DirectWire.WireObligationHistory open WireObligationRestoration PhysicalGateProvenance",
      "namespace PhysicalOwnership",
      "variable {sourceGates physicalGates : Nat}",
      "end PhysicalOwnership",
      "variable {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}",
      "namespace Transition",
      "variable {before after : State source} {event : RawEvent fields}",
      "end Transition",
      "namespace Execution",
      "variable {before after : State source} {events : List (RawEvent fields)}",
      "end Execution",
      "namespace ClosedHistory",
      "variable {raw : List (RawEvent fields)}",
      "end ClosedHistory",
      "end PNP.DirectWire.WireObligationHistory"
    ],
    "blocks": [
      {
        "name": "PhysicalOrigin",
        "occurrence": 0,
        "exact": "inductive PhysicalOrigin (sourceGates : Nat) where | original (gate : Fin sourceGates) | allocated (event : Nat) (localGate : Nat) deriving DecidableEq, Repr"
      },
      {
        "name": "PhysicalOwnership",
        "occurrence": 0,
        "exact": "structure PhysicalOwnership (sourceGates physicalGates : Nat) where origin : Fin physicalGates → PhysicalOrigin sourceGates charged : List (PhysicalOrigin sourceGates) removed : List (PhysicalOrigin sourceGates)"
      },
      {
        "name": "initial",
        "occurrence": 0,
        "exact": "def initial (sourceGates : Nat) : PhysicalOwnership sourceGates sourceGates := ⟨PhysicalOrigin.original, [], []⟩"
      },
      {
        "name": "append",
        "occurrence": 0,
        "exact": "def append (ledger : PhysicalOwnership sourceGates physicalGates) (event added : Nat) : PhysicalOwnership sourceGates (physicalGates + added) := ⟨splitFin ledger.origin (fun gate => .allocated event gate.val), ledger.charged ++ List.ofFn (fun gate : Fin added => .allocated event gate.val), ledger.removed⟩"
      },
      {
        "name": "normalize",
        "occurrence": 0,
        "exact": "def normalize {inputs outputs : Nat} (current : Implementation inputs outputs) (ledger : PhysicalOwnership sourceGates current.gateCount) : PhysicalOwnership sourceGates (runPhysicalNormalization current).result.gateCount := ⟨fun gate => ledger.origin (normalizedOrigin current gate), ledger.charged, ledger.removed ++ (normalizedRemoved current).map ledger.origin⟩"
      },
      {
        "name": "physicalOwnership",
        "occurrence": 0,
        "exact": "def physicalOwnership (step : Transition source before event after) (ledger : PhysicalOwnership source.implementation.gateCount before.current.implementation.gateCount) : PhysicalOwnership source.implementation.gateCount after.current.implementation.gateCount := match step with | .create _ _ _ _ _ => ledger | .restore _ _ _ _ entry => ledger.append event.identity (materializer entry.snapshot.carrier (keepExcept entry.field)).implementation.gateCount | .realize _ _ _ _ _ entry realization _ => ledger.append event.identity (materializer realization.carrier (keepExcept entry.field)).implementation.gateCount | .cancel _ _ _ _ _ _ _ => ledger | .normalize _ _ _ => PhysicalOwnership.normalize before.current.exposed ledger | .read _ _ _ _ _ => ledger"
      },
      {
        "name": "restore_physical_positions",
        "occurrence": 0,
        "signature": "theorem restore_physical_positions (state : State source) (event : RawEvent fields) (identity : Nat) (kind : event.action = .restoreR8 identity) (entry : PendingEntry state identity) (ledger : PhysicalOwnership source.implementation.gateCount state.current.implementation.gateCount) : let added := materializer entry.snapshot.carrier (keepExcept entry.field) let step := Transition.restore state event identity kind entry (state.restore entry.field entry.snapshot entry.found).current.implementation.candidate.program = state.current.implementation.candidate.program.appendSubstituted (fun input => .input input) added.implementation.candidate.program ∧ (∀ gate : Fin state.current.implementation.gateCount, (step.physicalOwnership ledger).origin (Fin.castAdd added.implementation.gateCount gate) = ledger.origin gate) ∧ (∀ gate : Fin added.implementation.gateCount, (step.physicalOwnership ledger).origin (Fin.natAdd state.current.implementation.gateCount gate) = .allocated event.identity gate.val)"
      },
      {
        "name": "realize_physical_positions",
        "occurrence": 0,
        "signature": "theorem realize_physical_positions (state : State source) (event : RawEvent fields) (identity : Nat) (raw : List RawSupportRecord) (kind : event.action = .realizeR7 identity raw) (entry : PendingEntry state identity) (realization : R7Realization entry.snapshot.carrier raw) (computed : computeR7 entry.snapshot.carrier raw = some realization) (ledger : PhysicalOwnership source.implementation.gateCount state.current.implementation.gateCount) : let added := materializer realization.carrier (keepExcept entry.field) let step := Transition.realize state event identity raw kind entry realization computed (state.restoreR7 entry.field entry.snapshot entry.found raw realization).current.implementation.candidate.program = state.current.implementation.candidate.program.appendSubstituted (fun input => .input input) added.implementation.candidate.program ∧ (∀ gate : Fin state.current.implementation.gateCount, (step.physicalOwnership ledger).origin (Fin.castAdd added.implementation.gateCount gate) = ledger.origin gate) ∧ (∀ gate : Fin added.implementation.gateCount, (step.physicalOwnership ledger).origin (Fin.natAdd state.current.implementation.gateCount gate) = .allocated event.identity gate.val)"
      },
      {
        "name": "physicalOwnership",
        "occurrence": 1,
        "exact": "def physicalOwnership {before after : State source} {events : List (RawEvent fields)} (trace : Execution source before events after) (ledger : PhysicalOwnership source.implementation.gateCount before.current.implementation.gateCount) : PhysicalOwnership source.implementation.gateCount after.current.implementation.gateCount := match trace with | .nil _ => ledger | .cons step tail => tail.physicalOwnership (step.physicalOwnership ledger)"
      },
      {
        "name": "physicalOwnership",
        "occurrence": 2,
        "exact": "def physicalOwnership (history : ClosedHistory source raw) : PhysicalOwnership source.implementation.gateCount history.state.current.implementation.gateCount := history.execution.physicalOwnership (PhysicalOwnership.initial source.implementation.gateCount)"
      },
      {
        "name": "physical_ownership",
        "occurrence": 0,
        "signature": "theorem physical_ownership (history : ClosedHistory source raw) : let ledger := history.physicalOwnership ledger.live.length = history.state.current.implementation.gateCount ∧ ledger.charged.length = history.execution.charged ∧ ledger.removed.length = history.execution.removed ∧ (ledger.live ++ ledger.removed).Nodup ∧ (ledger.live ++ ledger.removed).Perm (sourcePhysicalOrigins source ++ ledger.charged)"
      }
    ],
    "guards": []
  },
  {
    "id": "compiler",
    "path": "lean/PNP/NANDCompiledGateProvenance.lean",
    "heads": [
      "position_surjective",
      "physicalOrigin",
      "position_physicalOrigin",
      "physicalOrigin_position",
      "physicalOrigin_injective",
      "physicalOrigin_surjective",
      "physicalOrigins",
      "physicalOrigins_nodup",
      "physicalOrigins_perm",
      "RawNandCompilationState.finish_physicalOrigin"
    ],
    "imports": [
      "PNP.NANDTopologicalCompiler"
    ],
    "context": [
      "namespace PNP.DirectWire",
      "namespace CompiledRawNandGraph",
      "variable {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}",
      "end CompiledRawNandGraph",
      "end PNP.DirectWire"
    ],
    "blocks": [
      {
        "name": "physicalOrigin",
        "occurrence": 0,
        "exact": "def physicalOrigin (compiled : CompiledRawNandGraph graph) (position : Fin compiled.count) : Fin nodes := (compiled.physicalPreimage position).1"
      },
      {
        "name": "RawNandCompilationState.finish_physicalOrigin",
        "occurrence": 0,
        "signature": "theorem RawNandCompilationState.finish_physicalOrigin {inputs nodes : Nat} {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph) (complete : state.remaining = []) (node : Fin nodes) (position : Fin state.count) (placed : state.position node = some position) : (state.finish complete).physicalOrigin position = node"
      }
    ],
    "guards": [
      {
        "name": "findPosition",
        "fragment": "if same : position node = target then ⟨node, same⟩",
        "label": "actual-position-search"
      },
      {
        "name": "physicalPreimage",
        "fragment": "findPosition compiled.position target (allFin nodes)",
        "label": "actual-compiler-inverse"
      },
      {
        "name": "RawNandCompilationState.finish_physicalOrigin",
        "fragment": "(state.finish_position complete node).symm.trans placed",
        "label": "literal-finished-state"
      }
    ]
  },
  {
    "id": "ambient",
    "path": "lean/PNP/NANDWireHistoryAmbientOwnership.lean",
    "heads": [
      "ambientOriginals",
      "liftOrigin",
      "liftOrigin_injective",
      "extractedOrigins",
      "original_coordinate_partition",
      "rawNodeOrigin",
      "rawNodeOrigin_exterior",
      "rawNodeOrigin_history",
      "physicalOwnership",
      "physicalOrigin_position",
      "physical_partition",
      "physical_ownership",
      "OwnedCompilation",
      "result",
      "ledger",
      "ownership",
      "semantics",
      "compileOwned",
      "compileOwned_result"
    ],
    "imports": [
      "PNP.NANDWireHistoryArbitrarySupport",
      "PNP.NANDWireHistoryPhysicalOwnership",
      "PNP.NANDCompiledGateProvenance"
    ],
    "context": [
      "namespace PNP.DirectWire.WireHistoryAmbientOwnership open WireObligationHistory WireHistoryArbitrarySupport",
      "variable {inputs gates outputs profileWidth : Nat}",
      "variable (candidate : Candidate inputs gates outputs)",
      "variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))",
      "variable {raw : List (RawEvent (terminalInterfacePorts candidate records).length)}",
      "namespace OwnedCompilation",
      "end OwnedCompilation",
      "end PNP.DirectWire.WireHistoryAmbientOwnership"
    ],
    "blocks": [
      {
        "name": "rawNodeOrigin",
        "occurrence": 0,
        "exact": "def rawNodeOrigin (history : ClosedHistory (extractedCarrier candidate records) raw) : Fin ((ArbitrarySupportSplice.exterior records).length + history.state.current.implementation.gateCount) → PhysicalOrigin gates := splitFin (fun index => .original ((ArbitrarySupportSplice.exterior records).get index)) (fun index => liftOrigin candidate records (history.physicalOwnership.origin index))"
      },
      {
        "name": "physicalOwnership",
        "occurrence": 0,
        "exact": "def physicalOwnership (history : ClosedHistory (extractedCarrier candidate records) raw) (compiled : CompiledRawNandGraph (ArbitrarySupportSplice.graph candidate records (fieldCandidate history.state.current))) : PhysicalOwnership gates compiled.count := ⟨fun position => rawNodeOrigin candidate records history (compiled.physicalOrigin position), history.physicalOwnership.charged.map (liftOrigin candidate records), history.physicalOwnership.removed.map (liftOrigin candidate records)⟩"
      },
      {
        "name": "physical_ownership",
        "occurrence": 0,
        "signature": "theorem physical_ownership (history : ClosedHistory (extractedCarrier candidate records) raw) (compiled : CompiledRawNandGraph (ArbitrarySupportSplice.graph candidate records (fieldCandidate history.state.current))) : let ledger := physicalOwnership candidate records history compiled ledger.live.length = compiled.count ∧ ledger.charged.length = history.execution.charged ∧ ledger.removed.length = history.execution.removed ∧ (ledger.live ++ ledger.removed).Nodup ∧ (ledger.live ++ ledger.removed).Perm (ambientOriginals gates ++ ledger.charged)"
      },
      {
        "name": "OwnedCompilation",
        "occurrence": 0,
        "exact": "structure OwnedCompilation (raw : List (RawEvent (terminalInterfacePorts candidate records).length)) where history : ClosedHistory (extractedCarrier candidate records) raw compiled : CompiledRawNandGraph (ArbitrarySupportSplice.graph candidate records (fieldCandidate history.state.current)) executed : compileHistory (extractedCarrier candidate records) raw = some history compiledAt : ArbitrarySupportSplice.compile candidate records (fieldCandidate history.state.current) = some compiled"
      },
      {
        "name": "compileOwned",
        "occurrence": 0,
        "exact": "def compileOwned (raw : List (RawEvent (terminalInterfacePorts candidate records).length)) : Option (OwnedCompilation candidate records raw) := match executed : compileHistory (extractedCarrier candidate records) raw with | none => none | some history => match compiledAt : ArbitrarySupportSplice.compile candidate records (fieldCandidate history.state.current) with | none => none | some compiled => some ⟨history, compiled, executed, compiledAt⟩"
      },
      {
        "name": "compileOwned_result",
        "occurrence": 0,
        "signature": "theorem compileOwned_result (raw : List (RawEvent (terminalInterfacePorts candidate records).length)) : (compileOwned candidate records raw).map (OwnedCompilation.result candidate records) = WireHistoryArbitrarySupport.compile candidate records raw"
      }
    ],
    "guards": [
      {
        "name": "liftOrigin",
        "fragment": "| .original gate => .original (terminalExtractionOrigin candidate records gate)",
        "label": "actual-extracted-original"
      },
      {
        "name": "liftOrigin",
        "fragment": "| .allocated event localGate => .allocated event localGate",
        "label": "preserved-executing-identity"
      },
      {
        "name": "physical_partition",
        "fragment": "history.physical_partition.map (liftOrigin candidate records)",
        "label": "literal-history-partition"
      }
    ]
  },
  {
    "id": "charges",
    "path": "lean/PNP/NANDWireHistoryOwnershipCharges.lean",
    "heads": [
      "allocationEvent",
      "eventRequests",
      "eventRequests_member",
      "eventRequests_disjoint",
      "eventOwner_some_iff",
      "charged_origin",
      "live_allocated_event",
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
      "PNP.NANDWireHistoryAmbientOwnership",
      "PNP.ResidualTerminalPhysicalOwnership"
    ],
    "context": [
      "namespace PNP.DirectWire.WireHistoryAmbientOwnership open WireObligationHistory WireHistoryArbitrarySupport",
      "namespace OwnedCompilation",
      "variable {inputs gates outputs profileWidth : Nat}",
      "variable (candidate : Candidate inputs gates outputs)",
      "variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))",
      "variable {raw : List (RawEvent (terminalInterfacePorts candidate records).length)}",
      "variable (owned : OwnedCompilation candidate records raw)",
      "variable {supportWidth : Nat}",
      "end OwnedCompilation",
      "end PNP.DirectWire.WireHistoryAmbientOwnership"
    ],
    "blocks": [
      {
        "name": "eventRequests",
        "occurrence": 0,
        "exact": "def eventRequests (owner : Fin raw.length) : List (Fin (owned.result candidate records).gateCount) := (allFin (owned.result candidate records).gateCount).filter fun gate => decide (allocationEvent ((owned.ledger candidate records).origin gate) = some (raw.get owner).identity)"
      },
      {
        "name": "eventRequests_disjoint",
        "occurrence": 0,
        "signature": "theorem eventRequests_disjoint (left right : Fin raw.length) (different : left ≠ right) (gate : Fin (owned.result candidate records).gateCount) (inLeft : gate ∈ owned.eventRequests candidate records left) : gate ∉ owned.eventRequests candidate records right"
      },
      {
        "name": "eventOwner_some_iff",
        "occurrence": 0,
        "signature": "theorem eventOwner_some_iff (owner : Fin raw.length) (gate : Fin (owned.result candidate records).gateCount) : terminalPhysicalOwner (owned.eventRequests candidate records) gate = some owner ↔ allocationEvent ((owned.ledger candidate records).origin gate) = some (raw.get owner).identity"
      },
      {
        "name": "eventOwner_none_iff",
        "occurrence": 0,
        "signature": "theorem eventOwner_none_iff (gate : Fin (owned.result candidate records).gateCount) : terminalPhysicalOwner (owned.eventRequests candidate records) gate = none ↔ allocationEvent ((owned.ledger candidate records).origin gate) = none"
      },
      {
        "name": "materializer_chargeIdentity",
        "occurrence": 0,
        "signature": "theorem materializer_chargeIdentity (support : List (TerminalPrimitiveRecord inputs (owned.result candidate records).gateCount outputs supportWidth)) : ((terminalPhysicalOwners raw.length).map (fun owner => (owned.materializer candidate records support owner).gateCount)).sum = (extractTerminalSupport (owned.result candidate records).candidate support).gateCount"
      }
    ],
    "guards": [
      {
        "name": "eventRequests_disjoint",
        "fragment": "owned.history.ordered.unique left right",
        "label": "derived-no-overlap"
      },
      {
        "name": "charged_origin",
        "fragment": "owned.history.execution.allocations_member inner charged",
        "label": "actual-executed-charges"
      },
      {
        "name": "live_allocated_event",
        "fragment": "complete.subset (List.mem_append_left _ live)",
        "label": "source-charge-completeness"
      },
      {
        "name": "materializer",
        "fragment": "terminalOwnedPhysicalMaterializer (owned.result candidate records).candidate (owned.eventRequests candidate records) support owner",
        "label": "reuse-owned-extraction"
      },
      {
        "name": "support_restrict",
        "fragment": "terminalOwnedPhysicalGates_restrict (owned.eventRequests candidate records)",
        "label": "reuse-fixed-owner-restriction"
      }
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

test('M266 closes the five general source-derived provenance and ownership interfaces',async()=>{
  for(const {spec,source} of await sources0())assert.deepEqual(inspect0(source,spec),[],spec.path);
});

test('M266 rejects assumptions, unchecked evaluation, hidden inputs and unreviewed declarations',async()=>{
  for(const {spec,source} of await sources0()) {
    assert.ok(inspect0(source+'\naxiom hiddenOwner : False\n',spec).includes('assumption'));
    assert.ok(inspect0(source+'\nunsafe def uncheckedOwner : Nat := 0\n',spec).includes('shortcut'));
    assert.ok(inspect0(source+'\nexample : True := True.intro\n',spec).includes('unaudited-form'));
    assert.ok(inspect0(source+'\ntheorem extraOwner : True := True.intro\n',spec).includes('closed-declarations'));
    assert.ok(inspect0(source+'\nvariable (callerMap : Nat)\n',spec).includes('closed-context'));
    assert.ok(inspect0('import PNP.Main\n'+source,spec).includes('closed-imports'));
    assert.deepEqual(inspect0(source+'\n/- axiom, Classical and supplied owner maps are not authority -/\n',spec),[]);
  }
});

test('M266 retention follows actual constant, sharing and normalization branches',async()=>{
  await mutations0([
    ['normalization','match constantGateValue (constantGate initial gate) with',
      'match arbitraryBranch with','block:constantOrigins#0'],
    ['normalization','(constantOrigins initial).map Fin.castSucc ++ [Fin.last _]',
      '(constantOrigins initial).map Fin.castSucc','block:constantOrigins#0'],
    ['normalization','(sharingGate initial gate) with','(unrelatedGate initial gate) with',
      'block:sharingOrigins#0'],
    ['normalization','gainOrigin gain (traceOrigin tail position)','position','block:traceOrigin#0'],
    ['normalization','traceOrigin (runPhysicalNormalization current).trace',
      'arbitraryCountInjection','block:normalizedOrigin#0'],
    ['normalization','(normalizedRetained current ++ normalizedRemoved current).Nodup',
      'True','block:normalized_partition#0'],
  ]);
});

test('M266 allocation IDs and removed history cannot be replaced by snapshots or live counts',async()=>{
  await mutations0([
    ['history','| allocated (event : Nat) (localGate : Nat)','| allocated (localGate : Nat)',
      'block:PhysicalOrigin#0'],
    ['history','ledger.append event.identity','ledger.append identity','block:physicalOwnership#0'],
    ['history','ledger.charged ++ List.ofFn','List.ofFn','block:append#0'],
    ['history','ledger.charged,\n    ledger.removed ++','[],\n    ledger.removed ++',
      'block:normalize#0'],
    ['history','ledger.origin (normalizedOrigin current gate)','ledger.origin gate',
      'block:normalize#0'],
    ['history','tail.physicalOwnership (step.physicalOwnership ledger)','tail.physicalOwnership ledger',
      'block:physicalOwnership#1'],
    ['history','PhysicalOwnership.initial source.implementation.gateCount','callerLedger',
      'block:physicalOwnership#2'],
    ['history','ledger.charged.length = history.execution.charged',
      'ledger.live.length = history.execution.charged','block:physical_ownership#0'],
    ['history','(ledger.live ++ ledger.removed).Nodup','True','block:physical_ownership#0'],
    ['history','(sourcePhysicalOrigins source ++ ledger.charged)',
      '(sourcePhysicalOrigins source)','block:physical_ownership#0'],
  ]);
});

test('M266 compiler origins are the literal placement inverse, not any numeric permutation',async()=>{
  await mutations0([
    ['compiler','if same : position node = target then','if same : True then','actual-position-search'],
    ['compiler','findPosition compiled.position target (allFin nodes)',
      'findPosition unrelatedPosition target (allFin nodes)','actual-compiler-inverse'],
    ['compiler','(compiled.physicalPreimage position).1','position','block:physicalOrigin#0'],
    ['compiler','(state.finish_position complete node).symm.trans placed',
      'suppliedPlacement','literal-finished-state'],
  ]);
});

test('M266 ambient construction consumes only the raw source and computed history and splice',async()=>{
  await mutations0([
    ['ambient','def compileOwned (raw :','def compileOwned (suppliedMap : Nat) (raw :','block:compileOwned#0'],
    ['ambient','match executed : compileHistory (extractedCarrier candidate records) raw with',
      'match executed : suppliedHistory with','block:compileOwned#0'],
    ['ambient','match compiledAt : ArbitrarySupportSplice.compile candidate records',
      'match compiledAt : suppliedSplice candidate records','block:compileOwned#0'],
    ['ambient','(compiled.physicalOrigin position)','position','block:physicalOwnership#0'],
    ['ambient','((ArbitrarySupportSplice.exterior records).get index)','arbitraryExterior index',
      'block:rawNodeOrigin#0'],
    ['ambient','.original (terminalExtractionOrigin candidate records gate)','.original gate',
      'actual-extracted-original'],
    ['ambient','| .allocated event localGate => .allocated event localGate',
      '| .allocated event localGate => .allocated 0 localGate','preserved-executing-identity'],
    ['ambient','history.physical_partition.map (liftOrigin candidate records)',
      'suppliedPartition','literal-history-partition'],
    ['ambient','ledger.charged.length = history.execution.charged',
      'True','block:physical_ownership#0'],
    ['ambient','WireHistoryArbitrarySupport.compile candidate records raw',
      'some unrelatedImplementation','block:compileOwned_result#0'],
  ]);
});

test('M266 owner requests are derived, disjoint, support-independent and physically charged',async()=>{
  await mutations0([
    ['charges','def eventRequests (owner :','def eventRequests (supplied : Nat) (owner :',
      'block:eventRequests#0'],
    ['charges','allocationEvent ((owned.ledger candidate records).origin gate) =\n      some (raw.get owner).identity',
      'True','block:eventRequests#0'],
    ['charges','owned.history.ordered.unique left right','firstRequesterWins',
      'derived-no-overlap'],
    ['charges','owned.history.execution.allocations_member inner charged',
      'suppliedOwnerList','actual-executed-charges'],
    ['charges','complete.subset (List.mem_append_left _ live)','suppliedCompleteness',
      'source-charge-completeness'],
    ['charges','terminalOwnedPhysicalMaterializer (owned.result candidate records).candidate',
      'inventedWeightMaterializer','reuse-owned-extraction'],
    ['charges','terminalOwnedPhysicalGates_restrict (owned.eventRequests candidate records)',
      'supportDependentOwnerRestriction','reuse-fixed-owner-restriction'],
    ['charges','(owned.materializer candidate records support owner).gateCount',
      '(owned.ledger candidate records).charged.length','block:materializer_chargeIdentity#0'],
  ]);
});

test('M266 entire let-bound conservation conclusions remain guarded after local bindings',async()=>{
  const {spec,source}=(await sources0()).find(row=>row.spec.id==='ambient');
  const boundary=spec.blocks.find(row=>row.name==='physical_ownership');
  assert.ok(boundary.signature.includes('let ledger :='));
  assert.ok(boundary.signature.endsWith('(ambientOriginals gates ++ ledger.charged)'));
  assert.ok(inspect0(source.replace('(ledger.live ++ ledger.removed).Nodup','True'),spec)
    .includes('block:physical_ownership#0'));
  assert.ok(inspect0(source.replace('(ambientOriginals gates ++ ledger.charged)',
    '(ambientOriginals gates)'),spec).includes('block:physical_ownership#0'));
});

test('M266 regression fixtures retain empty cases, reordered origins and historical/live charge separation',async()=>{
  const fixture=await text0('lean-regression/PNPWireHistoryAmbientOwnership.lean');
  for(const fragment of [
    '[.original 0, .original 2, .original 1, .original 3]',
    '[.original 0, .original 2, .allocated 30 0, .original 3]',
    'restoredCharges != [4, 0, 0, 0] || ledger.charged.length != 1',
    'prunedCharges != [3, 0, 0, 1] || requestPositions != [[], [], [2]]',
    '(restricted ++ restricted)','restrictedCharges != [1, 0, 0, 1]',
    'twiceCharges != [4, 0, 1, 0, 1]','let some exteriorOnly','let some empty',
    'ownership wrapper accepted an unfinished history',
  ])assert.ok(fixture.includes(fragment),fragment);
  const names=[...fixture.matchAll(/^#print axioms (\S+)$/gmu)].map(match=>match[1]);
  assert.equal(new Set(names).size,23);
  assert.equal(names.length,23);
});
