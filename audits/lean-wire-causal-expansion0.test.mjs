import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {DeriveFormalPublication0, MilestoneTheoremKernelTypeSha2560,
  REQUIRED_MILESTONE_THEOREMS0, stableStringify0} from '../formal-publication0.mjs';
import {validateProofProgress0} from '../pcc-proof-progress0.mjs';
import {CheckFormalReconstructionStatus0} from '../pcc-formal-reconstruction-status0.mjs';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Reviewed snapshots of the general construction, not expectations regenerated
// from the implementation during a test. Kernel types and independent generic
// Lean examples provide the separate compiled boundary.
const SPEC = {
  "heads": [
    {
      "kind": "def",
      "name": "nodeCount"
    },
    {
      "kind": "def",
      "name": "boundarySource"
    },
    {
      "kind": "def",
      "name": "replacementSource"
    },
    {
      "kind": "def",
      "name": "originalSource"
    },
    {
      "kind": "def",
      "name": "exteriorGate"
    },
    {
      "kind": "def",
      "name": "replacementGate"
    },
    {
      "kind": "def",
      "name": "graph"
    },
    {
      "kind": "def",
      "name": "word"
    },
    {
      "kind": "def",
      "name": "rank"
    },
    {
      "kind": "theorem",
      "name": "graph_rank_decreases"
    },
    {
      "kind": "theorem",
      "name": "graph_wellFounded"
    },
    {
      "kind": "def",
      "name": "compile"
    },
    {
      "kind": "theorem",
      "name": "compile_success"
    },
    {
      "kind": "def",
      "name": "compiled"
    },
    {
      "kind": "theorem",
      "name": "compiled_spec"
    },
    {
      "kind": "def",
      "name": "expanded"
    },
    {
      "kind": "theorem",
      "name": "expanded_gateCount"
    },
    {
      "kind": "def",
      "name": "maskedBoundary"
    },
    {
      "kind": "theorem",
      "name": "masked_replacement_output"
    },
    {
      "kind": "def",
      "name": "values"
    },
    {
      "kind": "theorem",
      "name": "replacementSource_eval"
    },
    {
      "kind": "theorem",
      "name": "originalSource_eval"
    },
    {
      "kind": "theorem",
      "name": "values_solution"
    },
    {
      "kind": "theorem",
      "name": "expanded_semantics"
    },
    {
      "kind": "theorem",
      "name": "expanded_smaller_iff"
    },
    {
      "kind": "theorem",
      "name": "single_interface_smaller"
    },
    {
      "kind": "theorem",
      "name": "interface_nodup"
    },
    {
      "kind": "theorem",
      "name": "interface_owner_injective"
    },
    {
      "kind": "def",
      "name": "exteriorPosition"
    },
    {
      "kind": "def",
      "name": "copyPosition"
    },
    {
      "kind": "theorem",
      "name": "exteriorPosition_injective"
    },
    {
      "kind": "theorem",
      "name": "copyPosition_injective"
    },
    {
      "kind": "theorem",
      "name": "exteriorPosition_ne_copyPosition"
    },
    {
      "kind": "theorem",
      "name": "raw_node_ownership"
    },
    {
      "kind": "theorem",
      "name": "expanded_gate_ownership"
    },
    {
      "kind": "theorem",
      "name": "expanded_source"
    },
    {
      "kind": "theorem",
      "name": "expanded_source_equal"
    },
    {
      "kind": "def",
      "name": "expandedCarrier"
    },
    {
      "kind": "theorem",
      "name": "expandedCarrier_output"
    },
    {
      "kind": "theorem",
      "name": "expandedCarrier_field"
    },
    {
      "kind": "theorem",
      "name": "expandedCarrier_gateCount"
    },
    {
      "kind": "theorem",
      "name": "expandedCarrier_smaller_iff"
    },
    {
      "kind": "theorem",
      "name": "expandedCarrier_proper_and_smaller"
    },
    {
      "kind": "theorem",
      "name": "expandedCarrier_source_equal"
    },
    {
      "kind": "def",
      "name": "expandedR5Creation"
    },
    {
      "kind": "theorem",
      "name": "expandedR5Creation_coordinate"
    },
    {
      "kind": "theorem",
      "name": "expandedR5Creation_fullWitness"
    }
  ],
  "context": [
    "import PNP.NANDWireCarrier",
    "import PNP.NANDWireObligationRestoration",
    "namespace PNP",
    "namespace DirectWire",
    "namespace WireCausalExpansion",
    "variable {inputs gates outputs profileWidth replacementGates : Nat}",
    "variable (candidate : Candidate inputs gates outputs)",
    "variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))",
    "variable (replacement : Candidate (terminalBoundaryPorts candidate.program records).length replacementGates (terminalInterfacePorts candidate records).length)",
    "section Carrier",
    "variable {fields : Nat}",
    "variable (carrier : WireCarrier inputs outputs fields)",
    "variable (carrierRecords : List (TerminalPrimitiveRecord inputs carrier.exposed.gateCount (outputs + fields) profileWidth))",
    "variable (carrierReplacement : Candidate (terminalBoundaryPorts carrier.exposed.candidate.program carrierRecords).length replacementGates (terminalInterfacePorts carrier.exposed.candidate carrierRecords).length)",
    "end Carrier",
    "end WireCausalExpansion",
    "end DirectWire",
    "end PNP"
  ],
  "signatures": {
    "graph_rank_decreases": "theorem graph_rank_decreases (producer consumer : Fin (nodeCount candidate records replacementGates)) (edge : (graph candidate records replacement).Depends producer consumer) : rank candidate records producer < rank candidate records consumer",
    "graph_wellFounded": "theorem graph_wellFounded : WellFounded (graph candidate records replacement).Depends",
    "compile_success": "theorem compile_success : ∃ built, compile candidate records replacement = some built",
    "compiled_spec": "theorem compiled_spec : compile candidate records replacement = some (compiled candidate records replacement)",
    "expanded_gateCount": "theorem expanded_gateCount : (expanded candidate records replacement).gateCount = nodeCount candidate records replacementGates",
    "masked_replacement_output": "theorem masked_replacement_output (equivalent : replacement.semantics = (extractTerminalSupport candidate records).extractedCandidate.semantics) (owner : Fin (terminalInterfacePorts candidate records).length) (valuation : Valuation (terminalBoundaryPorts candidate.program records).length) : replacement.semantics (maskedBoundary candidate records owner valuation) owner = (extractTerminalSupport candidate records).extractedCandidate.semantics valuation owner",
    "replacementSource_eval": "theorem replacementSource_eval (owner : Fin (terminalInterfacePorts candidate records).length) (source : Source (terminalBoundaryPorts candidate.program records).length replacementGates) (input : Valuation inputs) : (replacementSource candidate records owner source).eval input (values candidate records replacement input) = source.eval (maskedBoundary candidate records owner (terminalInducedBoundaryValuation candidate records input)) (replacement.program.eval (maskedBoundary candidate records owner (terminalInducedBoundaryValuation candidate records input)))",
    "originalSource_eval": "theorem originalSource_eval (equivalent : replacement.semantics = (extractTerminalSupport candidate records).extractedCandidate.semantics) (source : Source inputs gates) (visible : ArbitrarySupportSplice.Visible candidate records source) (input : Valuation inputs) : (originalSource candidate records replacement source visible).eval input (values candidate records replacement input) = source.eval input (candidate.program.eval input)",
    "values_solution": "theorem values_solution (equivalent : replacement.semantics = (extractTerminalSupport candidate records).extractedCandidate.semantics) (input : Valuation inputs) : (graph candidate records replacement).Solution input (values candidate records replacement input)",
    "expanded_semantics": "theorem expanded_semantics (equivalent : replacement.semantics = (extractTerminalSupport candidate records).extractedCandidate.semantics) (input : Valuation inputs) (output : Fin outputs) : (expanded candidate records replacement).candidate.semantics input output = candidate.semantics input output",
    "expanded_smaller_iff": "theorem expanded_smaller_iff : (expanded candidate records replacement).gateCount < gates ↔ (terminalInterfacePorts candidate records).length * replacementGates < (extractTerminalSupport candidate records).gateCount",
    "single_interface_smaller": "theorem single_interface_smaller (single : (terminalInterfacePorts candidate records).length = 1) (smaller : replacementGates < (extractTerminalSupport candidate records).gateCount) : (expanded candidate records replacement).gateCount < gates",
    "interface_nodup": "theorem interface_nodup : (terminalInterfacePorts candidate records).Nodup",
    "interface_owner_injective": "theorem interface_owner_injective (left right : Fin (terminalInterfacePorts candidate records).length) (same : (terminalInterfacePorts candidate records).get left = (terminalInterfacePorts candidate records).get right) : left = right",
    "exteriorPosition_injective": "theorem exteriorPosition_injective (left right : Fin (ArbitrarySupportSplice.exterior records).length) (same : exteriorPosition candidate records replacement left = exteriorPosition candidate records replacement right) : left = right",
    "copyPosition_injective": "theorem copyPosition_injective (leftOwner rightOwner : Fin (terminalInterfacePorts candidate records).length) (leftGate rightGate : Fin replacementGates) (same : copyPosition candidate records replacement leftOwner leftGate = copyPosition candidate records replacement rightOwner rightGate) : leftOwner = rightOwner ∧ leftGate = rightGate",
    "exteriorPosition_ne_copyPosition": "theorem exteriorPosition_ne_copyPosition (outside : Fin (ArbitrarySupportSplice.exterior records).length) (owner : Fin (terminalInterfacePorts candidate records).length) (gate : Fin replacementGates) : exteriorPosition candidate records replacement outside ≠ copyPosition candidate records replacement owner gate",
    "raw_node_ownership": "theorem raw_node_ownership (node : Fin (nodeCount candidate records replacementGates)) : (∃ outside, node = Fin.castAdd ((terminalInterfacePorts candidate records).length * replacementGates) outside) ∨ (∃ owner gate, node = Fin.natAdd (ArbitrarySupportSplice.exterior records).length (copyNode owner gate))",
    "expanded_gate_ownership": "theorem expanded_gate_ownership (gate : Fin (expanded candidate records replacement).gateCount) : (∃ outside, gate = exteriorPosition candidate records replacement outside) ∨ (∃ owner localGate, gate = copyPosition candidate records replacement owner localGate)",
    "expanded_source": "theorem expanded_source (output : Fin outputs) : (expanded candidate records replacement).candidate.directWireWord.source output = (compiled candidate records replacement).translateSource ((word candidate records replacement).source output)",
    "expanded_source_equal": "theorem expanded_source_equal (left right : Fin outputs) (same : candidate.directWireWord.source left = candidate.directWireWord.source right) : (expanded candidate records replacement).candidate.directWireWord.source left = (expanded candidate records replacement).candidate.directWireWord.source right",
    "expandedCarrier_output": "theorem expandedCarrier_output (equivalent : carrierReplacement.semantics = (extractTerminalSupport carrier.exposed.candidate carrierRecords).extractedCandidate.semantics) (input : Valuation inputs) (output : Fin outputs) : (expandedCarrier carrier carrierRecords carrierReplacement).implementation.candidate.semantics input output = carrier.implementation.candidate.semantics input output",
    "expandedCarrier_field": "theorem expandedCarrier_field (equivalent : carrierReplacement.semantics = (extractTerminalSupport carrier.exposed.candidate carrierRecords).extractedCandidate.semantics) (input : Valuation inputs) (field : Fin fields) : (expandedCarrier carrier carrierRecords carrierReplacement).fieldValue input field = carrier.fieldValue input field",
    "expandedCarrier_gateCount": "theorem expandedCarrier_gateCount : (expandedCarrier carrier carrierRecords carrierReplacement).implementation.gateCount = (ArbitrarySupportSplice.exterior carrierRecords).length + (terminalInterfacePorts carrier.exposed.candidate carrierRecords).length * replacementGates",
    "expandedCarrier_smaller_iff": "theorem expandedCarrier_smaller_iff : (expandedCarrier carrier carrierRecords carrierReplacement).implementation.gateCount < carrier.implementation.gateCount ↔ (terminalInterfacePorts carrier.exposed.candidate carrierRecords).length * replacementGates < (extractTerminalSupport carrier.exposed.candidate carrierRecords).gateCount",
    "expandedCarrier_proper_and_smaller": "theorem expandedCarrier_proper_and_smaller (proper : (extractTerminalSupport carrier.exposed.candidate carrierRecords).gateCount < carrier.implementation.gateCount) (paidSaving : (terminalInterfacePorts carrier.exposed.candidate carrierRecords).length * replacementGates < (extractTerminalSupport carrier.exposed.candidate carrierRecords).gateCount) : (extractTerminalSupport carrier.exposed.candidate carrierRecords).gateCount < carrier.implementation.gateCount ∧ (expandedCarrier carrier carrierRecords carrierReplacement).implementation.gateCount < carrier.implementation.gateCount",
    "expandedCarrier_source_equal": "theorem expandedCarrier_source_equal (left right : Fin fields) (same : carrier.source left = carrier.source right) : (expandedCarrier carrier carrierRecords carrierReplacement).source left = (expandedCarrier carrier carrierRecords carrierReplacement).source right",
    "expandedR5Creation_coordinate": "theorem expandedR5Creation_coordinate (keep : Fin fields → Bool) (creation : WireObligationRestoration.R5Creation carrier keep) : (expandedR5Creation carrier carrierRecords carrierReplacement keep creation).coordinate = creation.coordinate",
    "expandedR5Creation_fullWitness": "theorem expandedR5Creation_fullWitness (equivalent : carrierReplacement.semantics = (extractTerminalSupport carrier.exposed.candidate carrierRecords).extractedCandidate.semantics) (keep : Fin fields → Bool) (creation : WireObligationRestoration.R5Creation carrier keep) (input : Valuation inputs) : (expandedR5Creation carrier carrierRecords carrierReplacement keep creation).originalSource.eval input ((expandedCarrier carrier carrierRecords carrierReplacement).implementation.candidate.program.eval input) = creation.originalSource.eval input (carrier.implementation.candidate.program.eval input)"
  },
  "definitions": {
    "nodeCount": "def nodeCount (replacementGates : Nat) : Nat := (ArbitrarySupportSplice.exterior records).length + (terminalInterfacePorts candidate records).length * replacementGates",
    "boundarySource": "def boundarySource (owner : Fin (terminalInterfacePorts candidate records).length) (port : Fin (terminalBoundaryPorts candidate.program records).length) : Source inputs (nodeCount candidate records replacementGates) := match found : (terminalBoundaryPorts candidate.program records).get port with | .input index => .input index | .gate gate => if gate.val < ((terminalInterfacePorts candidate records).get owner).val then .gate (Fin.castAdd ((terminalInterfacePorts candidate records).length * replacementGates) (memberIndex ((ArbitrarySupportSplice.mem_exterior_iff records gate).2 (boundaryGate_unselected candidate records gate (by rw [← found]; exact List.get_mem _ _))))) else .constant false",
    "replacementSource": "def replacementSource (owner : Fin (terminalInterfacePorts candidate records).length) : Source (terminalBoundaryPorts candidate.program records).length replacementGates → Source inputs (nodeCount candidate records replacementGates) | .input port => boundarySource candidate records owner port | .constant value => .constant value | .gate index => .gate (Fin.natAdd (ArbitrarySupportSplice.exterior records).length (copyNode owner index))",
    "originalSource": "def originalSource : (source : Source inputs gates) → ArbitrarySupportSplice.Visible candidate records source → Source inputs (nodeCount candidate records replacementGates) | .input index, _visible => .input index | .constant value, _visible => .constant value | .gate gate, visible => if selected : terminalGateSelected records gate = true then let owner := memberIndex (visible gate rfl selected) replacementSource candidate records owner (replacement.directWireWord.source owner) else .gate (Fin.castAdd ((terminalInterfacePorts candidate records).length * replacementGates) (memberIndex ((ArbitrarySupportSplice.mem_exterior_iff records gate).2 (by cases value : terminalGateSelected records gate with | false => rfl | true => exact False.elim (selected value)))))",
    "exteriorGate": "def exteriorGate (index : Fin (ArbitrarySupportSplice.exterior records).length) : Gate inputs (nodeCount candidate records replacementGates) := let original := (ArbitrarySupportSplice.exterior records).get index let pair := candidate.program.terminalGateSources original ⟨originalSource candidate records replacement pair.1 (ArbitrarySupportSplice.exteriorSource_visible candidate records original (exteriorGet_unselected records index) pair.1 (Or.inl rfl)), originalSource candidate records replacement pair.2 (ArbitrarySupportSplice.exteriorSource_visible candidate records original (exteriorGet_unselected records index) pair.2 (Or.inr rfl))⟩",
    "replacementGate": "def replacementGate (owner : Fin (terminalInterfacePorts candidate records).length) (index : Fin replacementGates) : Gate inputs (nodeCount candidate records replacementGates) := let pair := replacement.program.terminalGateSources index ⟨replacementSource candidate records owner pair.1, replacementSource candidate records owner pair.2⟩",
    "graph": "def graph : RawNandGraph inputs (nodeCount candidate records replacementGates) := ⟨splitFin (exteriorGate candidate records replacement) (fun node => replacementGate candidate records replacement (copyOwner node) (copyGate node))⟩",
    "word": "def word : DirectWireWord inputs (nodeCount candidate records replacementGates) outputs := ⟨fun output => originalSource candidate records replacement (candidate.directWireWord.source output) (ArbitrarySupportSplice.output_visible candidate records output)⟩",
    "rank": "def rank (node : Fin (nodeCount candidate records replacementGates)) : Nat := splitFin (fun outside => (replacementGates + 1) * ((ArbitrarySupportSplice.exterior records).get outside).val + replacementGates) (fun copied => (replacementGates + 1) * ((terminalInterfacePorts candidate records).get (copyOwner (width := replacementGates) copied)).val + (copyGate (owners := (terminalInterfacePorts candidate records).length) (width := replacementGates) copied).val) node",
    "compile": "def compile : Option (CompiledRawNandGraph (graph candidate records replacement)) := compileRawNandGraph (graph candidate records replacement)",
    "compiled": "def compiled : CompiledRawNandGraph (graph candidate records replacement) := match found : compile candidate records replacement with | some built => built | none => False.elim (((compileRawNandGraph_failure_iff (graph candidate records replacement)).1 found) (graph_wellFounded candidate records replacement))",
    "expanded": "def expanded : Implementation inputs outputs := ((compiled candidate records replacement).candidate (word candidate records replacement)).toImplementation",
    "maskedBoundary": "def maskedBoundary (owner : Fin (terminalInterfacePorts candidate records).length) (valuation : Valuation (terminalBoundaryPorts candidate.program records).length) : Valuation (terminalBoundaryPorts candidate.program records).length := fun port => match (terminalBoundaryPorts candidate.program records).get port with | .input _ => valuation port | .gate gate => if gate.val < ((terminalInterfacePorts candidate records).get owner).val then valuation port else false",
    "values": "def values (input : Valuation inputs) : Valuation (nodeCount candidate records replacementGates) := splitFin (fun outside => candidate.program.eval input ((ArbitrarySupportSplice.exterior records).get outside)) (fun copied => replacement.program.eval (maskedBoundary candidate records (copyOwner (width := replacementGates) copied) (terminalInducedBoundaryValuation candidate records input)) (copyGate copied))",
    "exteriorPosition": "def exteriorPosition (outside : Fin (ArbitrarySupportSplice.exterior records).length) : Fin (expanded candidate records replacement).gateCount := (compiled candidate records replacement).position (Fin.castAdd ((terminalInterfacePorts candidate records).length * replacementGates) outside)",
    "copyPosition": "def copyPosition (owner : Fin (terminalInterfacePorts candidate records).length) (gate : Fin replacementGates) : Fin (expanded candidate records replacement).gateCount := (compiled candidate records replacement).position (Fin.natAdd (ArbitrarySupportSplice.exterior records).length (copyNode owner gate))",
    "expandedCarrier": "def expandedCarrier : WireCarrier inputs outputs fields := WireCarrier.unpack (expanded carrier.exposed.candidate carrierRecords carrierReplacement)",
    "expandedR5Creation": "def expandedR5Creation (keep : Fin fields → Bool) (creation : WireObligationRestoration.R5Creation carrier keep) : WireObligationRestoration.R5Creation (expandedCarrier carrier carrierRecords carrierReplacement) keep := WireObligationRestoration.createR5 (expandedCarrier carrier carrierRecords carrierReplacement) keep creation.coordinate creation.forgotten"
  }
};
const NAMES = [
  "PNP.DirectWire.WireCausalExpansion.graph_rank_decreases",
  "PNP.DirectWire.WireCausalExpansion.graph_wellFounded",
  "PNP.DirectWire.WireCausalExpansion.compile_success",
  "PNP.DirectWire.WireCausalExpansion.compiled_spec",
  "PNP.DirectWire.WireCausalExpansion.expanded_gateCount",
  "PNP.DirectWire.WireCausalExpansion.masked_replacement_output",
  "PNP.DirectWire.WireCausalExpansion.replacementSource_eval",
  "PNP.DirectWire.WireCausalExpansion.originalSource_eval",
  "PNP.DirectWire.WireCausalExpansion.values_solution",
  "PNP.DirectWire.WireCausalExpansion.expanded_semantics",
  "PNP.DirectWire.WireCausalExpansion.expanded_smaller_iff",
  "PNP.DirectWire.WireCausalExpansion.single_interface_smaller",
  "PNP.DirectWire.WireCausalExpansion.interface_nodup",
  "PNP.DirectWire.WireCausalExpansion.interface_owner_injective",
  "PNP.DirectWire.WireCausalExpansion.exteriorPosition_injective",
  "PNP.DirectWire.WireCausalExpansion.copyPosition_injective",
  "PNP.DirectWire.WireCausalExpansion.exteriorPosition_ne_copyPosition",
  "PNP.DirectWire.WireCausalExpansion.raw_node_ownership",
  "PNP.DirectWire.WireCausalExpansion.expanded_gate_ownership",
  "PNP.DirectWire.WireCausalExpansion.expanded_source",
  "PNP.DirectWire.WireCausalExpansion.expanded_source_equal",
  "PNP.DirectWire.WireCausalExpansion.expandedCarrier_output",
  "PNP.DirectWire.WireCausalExpansion.expandedCarrier_field",
  "PNP.DirectWire.WireCausalExpansion.expandedCarrier_gateCount",
  "PNP.DirectWire.WireCausalExpansion.expandedCarrier_smaller_iff",
  "PNP.DirectWire.WireCausalExpansion.expandedCarrier_proper_and_smaller",
  "PNP.DirectWire.WireCausalExpansion.expandedCarrier_source_equal",
  "PNP.DirectWire.WireCausalExpansion.expandedR5Creation_coordinate",
  "PNP.DirectWire.WireCausalExpansion.expandedR5Creation_fullWitness"
];
const SOURCE = 'lean/PNP/NANDWireCausalExpansion.lean';
const AUDIT = 'lean-audit/PNPWireCausalExpansionAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPWireCausalExpansion.lean';
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = source => stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();

function blocks0(source) {
  const clean = stripLeanCommentsAndStrings0(source);
  const starts = [...clean.matchAll(/^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*(?:(def|theorem|inductive|structure|abbrev)[ \t]+([^\s({:]+)|(variable|namespace|section|end|import|open|set_option|attribute|include|omit|universe|export|initialize)\b)/gmu)];
  return starts.map((match, index) => ({
    kind: match[1] ?? match[3], name: match[2],
    start: match.index, end: starts[index + 1]?.index ?? source.length,
    text: compact0(source.slice(match.index, starts[index + 1]?.index ?? source.length)),
  }));
}

function signature0(block) {
  const at = block.indexOf(' := ');
  return at < 0 ? '' : block.slice(0, at);
}

function validateSource0(source) {
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  const blocks = blocks0(source);
  const clean = compact0(source);
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|implemented_by|csimp|partial_fixpoint)\b|#/u.test(clean),
    'unchecked-authority');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(({kind, name}) => ({kind, name}))) ===
    JSON.stringify(SPEC.heads), 'closed-interface');
  require0(JSON.stringify(blocks.filter(block => !block.name).map(block => block.text)) ===
    JSON.stringify(SPEC.context), 'exact-general-context');
  for (const [name, expected] of Object.entries(SPEC.signatures))
    require0(signature0(blocks.find(block => block.name === name)?.text ?? '') === expected,
      'signature:' + name);
  for (const [name, expected] of Object.entries(SPEC.definitions))
    require0(blocks.find(block => block.name === name)?.text === expected, 'definition:' + name);
  return failures;
}

async function rejectMutation0(name, old, replacement, expected) {
  const source = await text0(SOURCE);
  const span = blocks0(source).find(block => block.name === name);
  assert.ok(span, name);
  const before = source.slice(span.start, span.end);
  assert.equal(before.split(old).length - 1, 1, 'unique hostile anchor in ' + name);
  const after = before.replace(old, () => replacement);
  assert.notEqual(after, before);
  const mutated = source.slice(0, span.start) + after + source.slice(span.end);
  assert.ok(validateSource0(mutated).includes(expected), expected);
}

test('M262 source contract keeps arbitrary dimensions and the complete physical construction', async () => {
  assert.equal(SPEC.heads.length, 47);
  assert.equal(Object.keys(SPEC.signatures).length, 29);
  assert.equal(Object.keys(SPEC.definitions).length, 18);
  assert.deepEqual(validateSource0(await text0(SOURCE)), []);
});

test('M262 rejects free copies and unpaid local saving', async () => {
  await rejectMutation0('nodeCount',
    '(terminalInterfacePorts candidate records).length * replacementGates',
    'replacementGates', 'definition:nodeCount');
  await rejectMutation0('expanded_smaller_iff',
    '(terminalInterfacePorts candidate records).length * replacementGates',
    'replacementGates', 'signature:expanded_smaller_iff');
  await rejectMutation0('expandedCarrier_gateCount',
    '(terminalInterfacePorts carrier.exposed.candidate carrierRecords).length *',
    '1 *', 'signature:expandedCarrier_gateCount');
});

test('M262 rejects backwards wiring and masks only later gate ports', async () => {
  for (const name of ['boundarySource', 'maskedBoundary'])
    await rejectMutation0(name, 'gate.val <', 'gate.val >', 'definition:' + name);
  await rejectMutation0('boundarySource', '| .input index => .input index',
    '| .input index => .constant false', 'definition:boundarySource');
  await rejectMutation0('maskedBoundary', '| .input _ => valuation port',
    '| .input _ => false', 'definition:maskedBoundary');
  await rejectMutation0('maskedBoundary', 'then valuation port else false',
    'then false else valuation port', 'definition:maskedBoundary');
});

test('M262 rejects a wrong copy owner or a discarded ordered output', async () => {
  await rejectMutation0('replacementSource', '(copyNode owner index)',
    '(copyNode owner 0)', 'definition:replacementSource');
  await rejectMutation0('originalSource', '(replacement.directWireWord.source owner)',
    '(replacement.directWireWord.source 0)', 'definition:originalSource');
  await rejectMutation0('word', '(candidate.directWireWord.source output)',
    '(candidate.directWireWord.source 0)', 'definition:word');
});

test('M262 rejects a supplied schedule, compiler or rank in place of computed data', async () => {
  await rejectMutation0('rank', '(replacementGates + 1) *\n      ((ArbitrarySupportSplice.exterior records).get outside).val',
    '0 * ((ArbitrarySupportSplice.exterior records).get outside).val', 'definition:rank');
  await rejectMutation0('compile', 'compileRawNandGraph (graph candidate records replacement)',
    'suppliedCompiler', 'definition:compile');
  await rejectMutation0('compiled', 'match found : compile candidate records replacement with',
    'match found : suppliedCompiler with', 'definition:compiled');
  const source = await text0(SOURCE);
  const anchor = 'variable (candidate : Candidate inputs gates outputs)';
  assert.equal(source.split(anchor).length - 1, 1);
  for (const extra of [
    '\nvariable (suppliedRank : Fin gates → Nat)\n',
    '\nvariable\n  (compileSucceeded : True)\n',
    '\nvariable\n  (correctnessCertificate : replacement.semantics = candidate.semantics)\n',
  ]) {
    const changed = source.replace(anchor, () => anchor + extra);
    assert.ok(validateSource0(changed).includes('exact-general-context'));
  }
});

test('M262 rejects narrowing arbitrary open valuation to an induced whole-circuit input', async () => {
  await rejectMutation0('masked_replacement_output',
    '(valuation : Valuation (terminalBoundaryPorts candidate.program records).length)',
    '(input : Valuation inputs)', 'signature:masked_replacement_output');
});

test('M262 requires full local agreement rather than a vacuous or quotient premise', async () => {
  for (const name of ['masked_replacement_output', 'originalSource_eval', 'values_solution', 'expanded_semantics'])
    await rejectMutation0(name, 'replacement.semantics =',
      'True ∨ replacement.semantics =', 'signature:' + name);
  for (const name of ['expandedCarrier_output', 'expandedCarrier_field', 'expandedR5Creation_fullWitness'])
    await rejectMutation0(name, 'carrierReplacement.semantics =',
      'quotientAgreement ∨ carrierReplacement.semantics =', 'signature:' + name);
});

test('M262 keeps properness separate from paid strict saving', async () => {
  await rejectMutation0('expandedCarrier_proper_and_smaller',
    '(proper : (extractTerminalSupport carrier.exposed.candidate carrierRecords).gateCount <\n      carrier.implementation.gateCount)',
    '(proper : True)', 'signature:expandedCarrier_proper_and_smaller');
  await rejectMutation0('single_interface_smaller',
    '(single : (terminalInterfacePorts candidate records).length = 1)',
    '(single : True)', 'signature:single_interface_smaller');
});

test('M262 rejects losing an ownership index or omitting emitted gates', async () => {
  await rejectMutation0('copyPosition_injective',
    'leftOwner = rightOwner ∧ leftGate = rightGate',
    'leftOwner = rightOwner', 'signature:copyPosition_injective');
  await rejectMutation0('expanded_gate_ownership',
    '(gate : Fin (expanded candidate records replacement).gateCount)',
    '(gate : Fin replacementGates)', 'signature:expanded_gate_ownership');
  await rejectMutation0('exteriorPosition_ne_copyPosition',
    'outside ≠', 'outside =', 'signature:exteriorPosition_ne_copyPosition');
});

test('M262 retains literal wire sharing rather than value-only labels', async () => {
  await rejectMutation0('expanded_source_equal',
    'candidate.directWireWord.source left = candidate.directWireWord.source right',
    'candidate.semantics = candidate.semantics', 'signature:expanded_source_equal');
  await rejectMutation0('expandedCarrier_source_equal',
    'carrier.source left = carrier.source right',
    'True', 'signature:expandedCarrier_source_equal');
});

test('M262 exposes every field and rebinds the original R5 creation', async () => {
  await rejectMutation0('expandedCarrier', 'carrier.exposed.candidate',
    'carrier.implementation.candidate', 'definition:expandedCarrier');
  await rejectMutation0('expandedCarrier_field', '(field : Fin fields)',
    '(field : Fin outputs)', 'signature:expandedCarrier_field');
  await rejectMutation0('expandedR5Creation', 'creation.coordinate creation.forgotten',
    '0 creation.forgotten', 'definition:expandedR5Creation');
  await rejectMutation0('expandedR5Creation_fullWitness',
    'creation.originalSource.eval input (carrier.implementation.candidate.program.eval input) := by',
    'true := by', 'signature:expandedR5Creation_fullWitness');
});

test('M262 rejects hidden proof authority and unchecked execution overrides', async () => {
  const source = await text0(SOURCE);
  for (const declaration of ['axiom hidden : False', 'private axiom hidden : False',
    'opaque hidden : False'])
    assert.ok(validateSource0(source + '\n' + declaration + '\n').includes('assumption'));
  assert.ok(validateSource0(source + '\nexample : True := by trivial\n').includes('unaudited-form'));
  for (const declaration of [
    'attribute [implemented_by hidden] expanded',
    'unsafe def hidden : Bool := true',
    '#eval true',
  ]) assert.ok(validateSource0(source + '\n' + declaration + '\n').includes('unchecked-authority'));
});

test('M262 root and permanent axiom audit expose exactly the reviewed general theorem set', async () => {
  const [audit, root, regression] = await Promise.all([
    text0(AUDIT), text0('lean/PNP.lean'), text0(REGRESSION),
  ]);
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]), ['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match => match[1]), NAMES);
  assert.equal([...root.matchAll(/^import PNP\.NANDWireCausalExpansion$/gmu)].length, 1);
  assert.deepEqual([...regression.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]), ['PNP']);
});


test('M262 reviewed names, package scripts and durable workflow stay synchronized', async () => {
  const [inventory, workflow, pkgText, surface, verifier] = await Promise.all([
    text0('lean-audit/PNPTheoremInventory.lean'), text0('.github/workflows/lean-bridge.yml'),
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'), text0('scripts/pnp-verify-all.mjs'),
  ]);
  for (const name of NAMES) {
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item => item === name).length, 1, name);
    assert.equal(inventory.split(String.fromCharCode(96) + name + ',').length - 1, 1, name);
    assert.equal(workflow.split('"' + name + '"').length - 1, 1, name);
  }
  const command = 'node --test audits/lean-wire-causal-expansion0.test.mjs';
  assert.equal(JSON.parse(pkgText).scripts['audit:m262'], command);
  assert.ok(surface.includes("'audit:m262': '" + command + "'"));
  assert.ok(verifier.includes("'audits/lean-wire-causal-expansion0.test.mjs'"));
  for (const commandPart of [command, 'lake env lean -DwarningAsError=true ' + AUDIT,
    'lake env lean -DwarningAsError=true ' + REGRESSION])
    assert.ok(workflow.includes(commandPart), commandPart);
});

test('M262 executable regressions cover cycles, copy charges, empty dimensions and full fields', async () => {
  const regression = await text0(REGRESSION);
  for (const contract of [
    'checkExpansion chain interleaved cyclicReplacement 7',
    'checkExpansion chain interleaved safeReplacement 5',
    'checkExpansion savingCandidate savingRecords smallerReplacement 4',
    'checkExpansion chain fullRecords fullSmaller 3',
    'checkExpansion chain fullRecords fullLarger 12',
    'checkExpansion unusedCandidate unusedRecords unusedReplacement 0',
    'checkExpansion andExterior andRecords andReplacement 3',
    'checkExpansion andFull andFullRecords andFullReplacement 2',
    'checkCarrier repeatedCarrier repeatedRecords repeatedReplacement 7',
    'checkCarrier fieldOnlyCarrier fieldOnlyRecords fieldOnlyReplacement 7',
    '(ArbitrarySupportSplice.compile chain interleaved cyclicReplacement).isNone',
    'checkExpansion chain emptyRecords',
    'checkExpansion zeroCandidate zeroRecords',
    'checkExpansion constantsCandidate constantsRecords',
    '(compile fieldOnlyCarrier.exposed.candidate fieldOnlyRecords fieldOnlyWrong).isSome',
    'expandedR5Creation_fullWitness carrier records replacement sameOpen keep creation input',
    'positions.count position == 1',
    'decide (rank candidate records producer < rank candidate records consumer)',
    'wire-causal-expansion-regression: 13 constructor/carrier cases',
  ]) assert.ok(regression.includes(contract), contract);
  assert.doesNotMatch(regression, /#eval!|\bnative_decide\b/u);
  assert.match(regression, /^#eval checkCausalExpansions$/mu);
  assert.match(regression, /throw \(IO\.userError/u);
});

// Compiled snapshots reviewed once against the root-built M262 inventory.
// These constants must not be regenerated from the implementation at test time.
const M262_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-14-262';
const M262_MILESTONE = 'wire-causal-expansion';
const M262_HASHES = Object.freeze({
  "PNP.DirectWire.WireCausalExpansion.graph_rank_decreases": "57644abb11a3b3a89770af0bff4b95d4a4fb6fe89c95b7597c680d636dd64784",
  "PNP.DirectWire.WireCausalExpansion.graph_wellFounded": "4f5418492f37d279d5f263f809691860e3b09a5d40a7d19b812c05d33c167477",
  "PNP.DirectWire.WireCausalExpansion.compile_success": "4411fb4ee3c71709b0374fdd9c5af36d12d6796c5bad2dbba107eeb5fef85e3b",
  "PNP.DirectWire.WireCausalExpansion.compiled_spec": "aaf6be59c4f88a7fead74673109d28700ce16820dd0f9ad83cf42c7f2fda507b",
  "PNP.DirectWire.WireCausalExpansion.expanded_gateCount": "758d28d24a55d457119e6ae98f54798de7f173d5c9802e4df7ee95561bdc3209",
  "PNP.DirectWire.WireCausalExpansion.masked_replacement_output": "498f6fec12401d5e8a6ac437fba202351b12399567e9591ba6fc224cdc04e27a",
  "PNP.DirectWire.WireCausalExpansion.replacementSource_eval": "1ed6dee331e6062b34c11d9ee8a6abba3113b0043e50f7ad7061af1d9a49fbc3",
  "PNP.DirectWire.WireCausalExpansion.originalSource_eval": "7c2f1c2c8a2be86a7e09aec3d634c6f5c6e1786b93fe7b491d1795a48fa7d7f0",
  "PNP.DirectWire.WireCausalExpansion.values_solution": "9ce5f997c23c4cdd4fa5eb1b0421d8891f4763b1e9e7045aeedbc5215579a0d8",
  "PNP.DirectWire.WireCausalExpansion.expanded_semantics": "d6ab0ab4c6510402f806592b8888b9da2c0ee6edc88632c3ed61924e7b7b838d",
  "PNP.DirectWire.WireCausalExpansion.expanded_smaller_iff": "b8d6d37e0936f1464d863e28cad33536118657cc8b900e6978a45c7bbc2fa0a7",
  "PNP.DirectWire.WireCausalExpansion.single_interface_smaller": "c9b50726136c91ec59b2a341172622351e1e37c05b9b7a9b865e467dac95e739",
  "PNP.DirectWire.WireCausalExpansion.interface_nodup": "9d06c6bbc391a4a17d0a10bb418e085458cf36654d08be9efff05237037c29d9",
  "PNP.DirectWire.WireCausalExpansion.interface_owner_injective": "596fbac80224cdea520d2cfe72826db69f806725ae86dbfe9bec41e071e87819",
  "PNP.DirectWire.WireCausalExpansion.exteriorPosition_injective": "41595a52bb4e193f3dbe8f6649e0948a0fae4d0e45e46d6a4761aaf70d9c1511",
  "PNP.DirectWire.WireCausalExpansion.copyPosition_injective": "a5ccf42333c6b2f01b9c8b0a18ce894001dcb8eb157428245b9702b0870dc778",
  "PNP.DirectWire.WireCausalExpansion.exteriorPosition_ne_copyPosition": "b962ed0a91245467f2ad53ce6f0fefd92cabb01d232985604a76e0e79b202c1c",
  "PNP.DirectWire.WireCausalExpansion.raw_node_ownership": "7da2fa53475565b8c6561eaef5bd4d8be3ac6f2b435d931175be7ead3d511622",
  "PNP.DirectWire.WireCausalExpansion.expanded_gate_ownership": "59a10f634f371082d7cf52c73e31806a2225245671020447310930a6dbfa1855",
  "PNP.DirectWire.WireCausalExpansion.expanded_source": "51d3a08c647d37b79586934fe8ab9264543b9473edfb524b6fbffd20d0a7940a",
  "PNP.DirectWire.WireCausalExpansion.expanded_source_equal": "40d8e8ecefe37a22b2d076f6ea12a623b4e456230601f6094d2d71005b149d1e",
  "PNP.DirectWire.WireCausalExpansion.expandedCarrier_output": "fa6da8a64f9d09a4a1f329e28892d99305ed68ebc1aaa309fc7100a302bad3d3",
  "PNP.DirectWire.WireCausalExpansion.expandedCarrier_field": "8482512bec2fdd91a41de913dec04499cc23fe9dfb4e22a9c8ac1a9d4d7a9691",
  "PNP.DirectWire.WireCausalExpansion.expandedCarrier_gateCount": "2ea5c2c9ed9ec03102e3197c42330f2943f914e404f208fe8ea58cdb1e4a9744",
  "PNP.DirectWire.WireCausalExpansion.expandedCarrier_smaller_iff": "407306bfe3a6784147d80e73a8df3fdc25d67030b8a4669a101495b388da9c15",
  "PNP.DirectWire.WireCausalExpansion.expandedCarrier_proper_and_smaller": "7d70d141e95bba9b84f18ece6d34ed734c461fc71df177093af4cb703eb7aebd",
  "PNP.DirectWire.WireCausalExpansion.expandedCarrier_source_equal": "5a8220e89738e799ed538c8549e0ded5f5fe6c00a8046957ad23104579d93386",
  "PNP.DirectWire.WireCausalExpansion.expandedR5Creation_coordinate": "ad550a5727ce90e16c4049b5b586e57dead7e6fc9438db879ca25e8a35760788",
  "PNP.DirectWire.WireCausalExpansion.expandedR5Creation_fullWitness": "7e01ca8c99d4a13c025db43dc44f130d836c0e5a9c3f09b45640997f1ce0937e"
});
const M262_STATUS_FIELDS = Object.freeze({
  "leanWireCausalExpansionFormalized": true,
  "leanWireCausalExpansionAxiomAuditPassed": true,
  "leanWireCausalExpansionAuditedDeclarationCount": 29,
  "leanWireCausalExpansionRankDecreaseTheorem": "PNP.DirectWire.WireCausalExpansion.graph_rank_decreases",
  "leanWireCausalExpansionGraphWellFoundedTheorem": "PNP.DirectWire.WireCausalExpansion.graph_wellFounded",
  "leanWireCausalExpansionCompileSuccessTheorem": "PNP.DirectWire.WireCausalExpansion.compile_success",
  "leanWireCausalExpansionCompiledResultTheorem": "PNP.DirectWire.WireCausalExpansion.compiled_spec",
  "leanWireCausalExpansionPhysicalGateCountTheorem": "PNP.DirectWire.WireCausalExpansion.expanded_gateCount",
  "leanWireCausalExpansionAllOpenMaskedOutputTheorem": "PNP.DirectWire.WireCausalExpansion.masked_replacement_output",
  "leanWireCausalExpansionReplacementSourceValueTheorem": "PNP.DirectWire.WireCausalExpansion.replacementSource_eval",
  "leanWireCausalExpansionOriginalSourceValueTheorem": "PNP.DirectWire.WireCausalExpansion.originalSource_eval",
  "leanWireCausalExpansionGraphSolutionTheorem": "PNP.DirectWire.WireCausalExpansion.values_solution",
  "leanWireCausalExpansionOrderedOutputSemanticsTheorem": "PNP.DirectWire.WireCausalExpansion.expanded_semantics",
  "leanWireCausalExpansionPaidSavingIffTheorem": "PNP.DirectWire.WireCausalExpansion.expanded_smaller_iff",
  "leanWireCausalExpansionSingleInterfaceSavingTheorem": "PNP.DirectWire.WireCausalExpansion.single_interface_smaller",
  "leanWireCausalExpansionInterfaceNoDuplicatesTheorem": "PNP.DirectWire.WireCausalExpansion.interface_nodup",
  "leanWireCausalExpansionPhysicalProducerIdentityTheorem": "PNP.DirectWire.WireCausalExpansion.interface_owner_injective",
  "leanWireCausalExpansionExteriorOwnershipTheorem": "PNP.DirectWire.WireCausalExpansion.exteriorPosition_injective",
  "leanWireCausalExpansionCopyOwnershipTheorem": "PNP.DirectWire.WireCausalExpansion.copyPosition_injective",
  "leanWireCausalExpansionDisjointOwnershipTheorem": "PNP.DirectWire.WireCausalExpansion.exteriorPosition_ne_copyPosition",
  "leanWireCausalExpansionRawOwnershipCoverageTheorem": "PNP.DirectWire.WireCausalExpansion.raw_node_ownership",
  "leanWireCausalExpansionEmittedOwnershipCoverageTheorem": "PNP.DirectWire.WireCausalExpansion.expanded_gate_ownership",
  "leanWireCausalExpansionActualOutputSourceTheorem": "PNP.DirectWire.WireCausalExpansion.expanded_source",
  "leanWireCausalExpansionLiteralOutputSharingTheorem": "PNP.DirectWire.WireCausalExpansion.expanded_source_equal",
  "leanWireCausalExpansionCarrierOutputTheorem": "PNP.DirectWire.WireCausalExpansion.expandedCarrier_output",
  "leanWireCausalExpansionCarrierFieldTheorem": "PNP.DirectWire.WireCausalExpansion.expandedCarrier_field",
  "leanWireCausalExpansionCarrierPhysicalGateCountTheorem": "PNP.DirectWire.WireCausalExpansion.expandedCarrier_gateCount",
  "leanWireCausalExpansionCarrierPaidSavingIffTheorem": "PNP.DirectWire.WireCausalExpansion.expandedCarrier_smaller_iff",
  "leanWireCausalExpansionProperAndPaidSavingTheorem": "PNP.DirectWire.WireCausalExpansion.expandedCarrier_proper_and_smaller",
  "leanWireCausalExpansionLiteralFieldSharingTheorem": "PNP.DirectWire.WireCausalExpansion.expandedCarrier_source_equal",
  "leanWireCausalExpansionR5CoordinateTheorem": "PNP.DirectWire.WireCausalExpansion.expandedR5Creation_coordinate",
  "leanWireCausalExpansionR5OriginalFullSourceTheorem": "PNP.DirectWire.WireCausalExpansion.expandedR5Creation_fullWitness",
  "leanWireCausalExpansionArbitrarySupportAndBoundaryWidthsCovered": true,
  "leanWireCausalExpansionSourceDerivedRankProved": true,
  "leanWireCausalExpansionUnconditionalCompilationProved": true,
  "leanWireCausalExpansionCompleteOpenMaskSemanticsProved": true,
  "leanWireCausalExpansionEveryOrderedOutputPreservedUnderFullAgreement": true,
  "leanWireCausalExpansionEveryComputationalFieldPreservedUnderFullAgreement": true,
  "leanWireCausalExpansionUniquePhysicalCopyOwnershipProved": true,
  "leanWireCausalExpansionEveryEmittedGateOwned": true,
  "leanWireCausalExpansionLiteralRepeatedSourceSharingProved": true,
  "leanWireCausalExpansionOriginalR5CoordinateAndFullValueTransportProved": true,
  "leanWireCausalExpansionExactExteriorPlusCopiesGateCountProved": true,
  "leanWireCausalExpansionPaidSavingIffProved": true,
  "leanWireCausalExpansionPropernessSeparate": true,
  "leanWireCausalExpansionExistingLiteralCompilerPreserved": true,
  "leanWireCausalExpansionCallerSuppliedRankRequired": false,
  "leanWireCausalExpansionCallerSuppliedCompilerSuccessRequired": false,
  "leanWireCausalExpansionCallerSuppliedFinalSemanticsRequired": false,
  "leanWireCausalExpansionSemanticsWithoutLocalAgreementProved": false,
  "leanWireCausalExpansionWholeCircuitValuationsOnly": false,
  "leanWireCausalExpansionQuotientOnlyFieldAgreementSufficient": false,
  "leanWireCausalExpansionUnpaidLocalSavingTransportProved": false,
  "leanWireCausalExpansionMatchedKappaPullExpandProved": false,
  "leanWireCausalExpansionArbitraryObserverEqualityProved": false,
  "leanWireCausalExpansionFullManuscriptCarrierProved": false,
  "leanWireCausalExpansionCompleteObligationCalculusProved": false,
  "leanWireCausalExpansionCompletePackageEProved": false,
  "leanWireCausalExpansionGlobalRouteCoverageProved": false,
  "leanWireCausalExpansionUnconditionalSaturatePositiveProved": false,
  "leanWireCausalExpansionUnconditionalBCELReadyProved": false,
  "leanWireCausalExpansionUnconditionalZeroSlackProved": false,
  "leanWireCausalExpansionExactGeneralPCCMinProved": false,
  "leanWireCausalExpansionPolynomialRuntimeProved": false,
  "leanWireCausalExpansionRuntimeExecutionIsProofAuthority": false,
  "leanWireCausalExpansionScope": "arbitrary-finite-computational-supports-and-boundary-widths-source-derived-rank-total-causal-physical-expansion-all-open-mask-semantics-under-full-local-agreement-all-outputs-and-full-fields-exact-exterior-plus-producer-copies-unique-complete-ownership-literal-sharing-original-R5-source-transport-paid-saving-iff-no-matched-kappa-global-route-or-polynomial-runtime"
});

let compiledSourcesPromise0;
function compiledSources0() {
  compiledSourcesPromise0 ??= Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
    text0('status/LEAN_THEOREM_INVENTORY.json'),
    text0('status/PROOF_PROGRESS.json'),
    text0('publication/FORMAL_PUBLICATION_MAP.json'),
  ]).then(([status, inventory, progress, map]) => ({
    status:JSON.parse(status), inventory:JSON.parse(inventory),
    progress:JSON.parse(progress), map:JSON.parse(map), inventoryBytes:Buffer.from(inventory),
  }));
  return compiledSourcesPromise0;
}
const canonicalBytes0 = value => Buffer.from(stableStringify0(value) + '\n');
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();
function metrics0(progress) {
  const coverage = progress.formalArtefactCoverage, proof = progress.proofCompletion;
  return [
    'Formal artefact coverage: ' + coverage.earnedRows + ' of ' + coverage.totalRows
      + ' current scoped publication rows earned.',
    'Risk-weighted proof completion estimate: ' + proof.percent + '%.',
    'Uncertainty range: ' + proof.uncertaintyLowPercent + '% to ' + proof.uncertaintyHighPercent + '%.',
    'Global gates closed: ' + progress.globalGates.filter(gate => gate.status === 'closed').length
      + ' of ' + progress.globalGates.length + '.',
  ];
}

test('M262 status and report coordinates stay linked and reject independently altered report identity', async () => {
  const {status} = await compiledSources0();
  assert.equal(status.canonicalReportCoordinate, status.coordinate.replace(
    'PNP-FORMAL-RECONSTRUCTION-STATUS-', 'PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-'));
  const mutation = {...status, canonicalReportCoordinate:status.canonicalReportCoordinate + ':unreviewed'};
  const result = await CheckFormalReconstructionStatus0({writeOutput:false,
    statusOverride:mutation, siteOverride:mutation});
  assert.equal(result.tag, 'reject');
  assert.equal(result.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(result.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'canonicalReportCoordinate']);
});

test('M262 compiled causal-expansion types, axioms and status match the reviewed construction', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  assert.deepEqual(Object.keys(M262_HASHES), NAMES);
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M262_MILESTONE);
  assert.equal(row?.earned, true);
  assert.equal(row.classification, 'formalized-foundation-only');
  assert.deepEqual(row.requiredTheorems, NAMES);
  if (status.coordinate === M262_COORDINATE)
    assert.equal(map.coordinate, M262_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  for (const name of NAMES) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, 'PNP.NANDWireCausalExpansion', name);
      assert.deepEqual(declaration.axioms, ['Quot.sound', 'propext'], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M262_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M262_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M262_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
    'Compilation requires no supplied rank, order, semantic or compiler-success certificate.',
    'for every open boundary valuation',
    'every original ordered output and computational field retains its full value.',
    'cover every emitted gate.',
    'original full source value.',
    'Actual cost is E + K * R',
    'equivalent to K * R < S, with properness S < G separately required.',
  ]) assert.ok(prose0(row.scope).includes(boundary), boundary);
  for (const boundary of [
    'not matched-kappa Pull/Expand',
    'Full local open-function agreement is required for semantics',
    'quotient-only or ordinary-output-only equality does not suffice',
    'The inherited cyclic literal splice remains rejected',
    'not the complete R5–R8 event calculus',
    'total encoded-input-size polynomial runtime, output and certificate bounds remain open.',
    'No fixed weighted checkpoint or global gate closes.',
    'P = NP is not proved.',
  ]) assert.ok(prose0(row.nonClaim).includes(boundary), boundary);
});

test('M262 publication rejects weakened or supplied versions of every reviewed theorem', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of NAMES) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M262_MILESTONE).earned, false,
      name + ': ' + substitute);
    assert.equal(result.gate.passed, false);
  }
});

test('M262 publication rejects hidden authority, missing evidence and altered publication claims', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  const name = 'PNP.DirectWire.WireCausalExpansion.expandedCarrier_proper_and_smaller';
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory, declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const result = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(result.milestones.find(row => row.id === M262_MILESTONE).earned, false);
  assert.equal(result.gate.passed, false);
  // Removing required detailed evidence violates the closed reviewed-name set,
  // so this stronger inventory-level rejection precedes milestone derivation.
  const missing = {...inventory,
    milestoneCandidates:inventory.milestoneCandidates.filter(row => row.name !== name)};
  assert.throws(() => DeriveFormalPublication0(missing, map, canonicalBytes0(missing),
    status.leanSourceClosureSha256), /reviewed milestone theorem candidate inventory mismatch/u);
  for (const field of ['scope', 'nonClaim']) {
    const widened = {...map, milestones:map.milestones.map(row => row.id === M262_MILESTONE
      ? {...row, [field]:'Local R < S proves uncharged matched-kappa expansion, arbitrary observer equality and unconditional polynomial ZeroSlack.'}
      : row)};
    assert.throws(() => DeriveFormalPublication0(inventory, widened, inventoryBytes,
      status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  }
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, inventoryBytes,
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});


test('M262 adds construction coverage without matched-cost, global or weighted completion credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const reviews = progress.history.filter(entry => entry.asOfCoordinate === M262_COORDINATE);
  assert.equal(reviews.length, 1);
  const review = reviews[0];
  assert.equal(review.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  assert.equal(review.globalGatesAvailable, 5);
  assert.deepEqual(review.formalArtefactCoverage, {earnedRows:238, totalRows:240});
  for (const boundary of [
    'source-derived causal physical expansion prerequisite',
    'arbitrary computational-support and incoming-boundary widths',
    'every actual exterior/copy gate is uniquely owned and charged',
    'K * R < S, not merely R < S',
    'does not prove matched-kappa Pull/Expand',
    'No fixed load-bearing checkpoint changes state',
  ]) assert.ok(prose0(review.rationale).includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M262_COORDINATE) return;
  assert.deepEqual(progress.tracks.map(track => track.pointsEarned), [13, 20, 2, 1, 4]);
  assert.equal(progress.proofCompletion.percent, 40);
  assert.equal(progress.proofCompletion.uncertaintyLowPercent, 20);
  assert.equal(progress.proofCompletion.uncertaintyHighPercent, 40);
  assert.equal(progress.globalGates.length, 5);
  assert.ok(progress.globalGates.every(gate => gate.status === 'open'));
  assert.deepEqual(inventory.projectAxioms, []);
  assert.deepEqual(progress.projectSpecificAxiomsRemaining, []);
  assert.equal(inventory.declarations.some(row => row.name === 'PNP.Main.p_eq_np'), false);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.equal(progress.publicationGate.passed, false);
  assert.deepEqual(progress.rootTheorem, {
    name:'PNP.Main.p_eq_np', present:false, built:false, axiomAuditPassed:false,
  });
  const inflated = structuredClone(progress);
  inflated.proofCompletion.pointsEarned += 1;
  inflated.proofCompletion.percent += 1;
  assert.throws(() => validateProofProgress0(inflated, status, inventory),
    error => error.code === 'ProofCompletion.StoredEarned');
});

test('M262 documentation preserves paid construction scope and records a batched major publication', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_wire_causal_expansion.md'));
  assert.ok(documentation.includes(M262_COORDINATE));
  for (const boundary of [
    'complete local open-function equality',
    'covers every open boundary valuation, not just whole-circuit-induced inputs.',
    'Quotient-only or ordinary-output-only agreement is insufficient.',
    'strict original-size saving iff K * R < S',
    'proper support separately requires S < G',
    'these executable fixtures are regression evidence, not proof authority.',
    'Matched-kappa Pull/Expand and global CompatibleReplacement/SlackLaw remain open.',
    'No fixed weighted checkpoint or global proof gate closes',
  ]) assert.ok(documentation.toLowerCase().includes(boundary.toLowerCase()), boundary);
  const decision = 'Publication decision: publish one batched PNPLabs update after the M262 core release gates pass.';
  assert.ok(documentation.includes(decision));
  const plan = prose0(await text0('docs/plans/2026-09-14-wire-causal-expansion.md'));
  assert.ok(plan.includes(decision));
  if (progress.asOfCoordinate !== M262_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_wire_causal_expansion.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});

test('M262 status rejects every changed theorem, claim and scope field', async () => {
  const {status} = await compiledSources0();
  for (const [field,value] of Object.entries(M262_STATUS_FIELDS)) {
    const mutation = {...status, [field]:typeof value === 'boolean' ? !value
      : typeof value === 'number' ? value + 1 : value + ':unreviewed'};
    const result = await CheckFormalReconstructionStatus0({writeOutput:false,
      statusOverride:mutation, siteOverride:mutation});
    assert.equal(result.tag, 'reject', field);
    assert.equal(result.coord, 'FormalReconstructionStatus.Field', field);
    assert.deepEqual(result.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
  }
});
