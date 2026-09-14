import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';
import {DeriveFormalPublication0, MilestoneTheoremKernelTypeSha2560, REQUIRED_MILESTONE_THEOREMS0, stableStringify0} from '../formal-publication0.mjs';
import {validateProofProgress0} from '../pcc-proof-progress0.mjs';
import {CheckFormalReconstructionStatus0} from '../pcc-formal-reconstruction-status0.mjs';

const NAMES = [
  "PNP.DirectWire.terminalOpenGateEvaluation_pullback",
  "PNP.DirectWire.terminalOpenSupportSemantics_pullback",
  "PNP.DirectWire.terminalBoundaryPullback_identity",
  "PNP.DirectWire.terminalBoundaryPullback_compose",
  "PNP.DirectWire.TerminalOptimumLegTransport.selectedGateTransport",
  "PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_meet_join_left",
  "PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_meet_join_right",
  "PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_square",
  "PNP.DirectWire.TerminalOptimumLegTransport.extracted_retained_semantics",
  "PNP.DirectWire.TerminalOptimumLegTransport.realization_retained_semantics",
  "PNP.DirectWire.TerminalFourCornerOptimumFamily.full_retained_semantics",
  "PNP.DirectWire.TerminalFourCornerOptimumFamily.quotient_retained_semantics",
  "PNP.DirectWire.TerminalFourCornerCarrier.canonicalFull_retained_semantics",
  "PNP.DirectWire.TerminalFourCornerCarrier.canonicalQuotient_retained_semantics"
];
const SPECS = [
  {
    "kind": "nested",
    "path": "lean/PNP/ResidualTerminalSupportExtraction.lean",
    "heads": [
      "terminalOpenWireValue",
      "terminalBoundaryPullback",
      "terminalOpenGateEvaluation_pullback",
      "terminalOpenSupportSemantics_pullback",
      "terminalBoundaryPullback_identity",
      "terminalBoundaryPullback_compose"
    ],
    "signatures": {
      "terminalOpenGateEvaluation_pullback": "theorem terminalOpenGateEvaluation_pullback {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (small large : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (included : forall gate, terminalGateSelected small gate = true -> terminalGateSelected large gate = true) (valuation : Valuation (terminalBoundaryPorts candidate.program large).length) (gate : Fin gates) (selected : terminalGateSelected small gate = true) : terminalOpenGateEvaluation candidate small (terminalBoundaryPullback candidate small large valuation) gate = terminalOpenGateEvaluation candidate large valuation gate",
      "terminalOpenSupportSemantics_pullback": "theorem terminalOpenSupportSemantics_pullback {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (small large : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (included : forall gate, terminalGateSelected small gate = true -> terminalGateSelected large gate = true) (valuation : Valuation (terminalBoundaryPorts candidate.program large).length) (output : Fin (terminalInterfacePorts candidate small).length) : terminalOpenSupportSemantics candidate small (terminalBoundaryPullback candidate small large valuation) output = terminalOpenGateEvaluation candidate large valuation ((terminalInterfacePorts candidate small).get output)",
      "terminalBoundaryPullback_identity": "theorem terminalBoundaryPullback_identity {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (valuation : Valuation (terminalBoundaryPorts candidate.program records).length) : terminalBoundaryPullback candidate records records valuation = valuation",
      "terminalBoundaryPullback_compose": "theorem terminalBoundaryPullback_compose {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (small middle large : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (smallIncluded : forall gate, terminalGateSelected small gate = true -> terminalGateSelected middle gate = true) (middleIncluded : forall gate, terminalGateSelected middle gate = true -> terminalGateSelected large gate = true) (valuation : Valuation (terminalBoundaryPorts candidate.program large).length) : terminalBoundaryPullback candidate small middle (terminalBoundaryPullback candidate middle large valuation) = terminalBoundaryPullback candidate small large valuation"
    }
  },
  {
    "kind": "square",
    "path": "lean/PNP/ResidualTerminalFourCornerOpenTransport.lean",
    "heads": [
      "TerminalOptimumLegTransport.selectedGateTransport",
      "TerminalOptimumLegTransport.boundaryPullback",
      "TerminalFourCornerCarrier.boundaryPullback_meet_join_left",
      "TerminalFourCornerCarrier.boundaryPullback_meet_join_right",
      "TerminalFourCornerCarrier.boundaryPullback_square",
      "TerminalOptimumLegTransport.extracted_retained_semantics",
      "TerminalOptimumLegTransport.realization_retained_semantics",
      "TerminalFourCornerOptimumFamily.full_retained_semantics",
      "TerminalFourCornerOptimumFamily.quotient_retained_semantics",
      "TerminalFourCornerCarrier.canonicalFull_retained_semantics",
      "TerminalFourCornerCarrier.canonicalQuotient_retained_semantics"
    ],
    "signatures": {
      "TerminalOptimumLegTransport.selectedGateTransport": "theorem TerminalOptimumLegTransport.selectedGateTransport (transport : TerminalOptimumLegTransport carrier) (gate : Fin gates) (selected : terminalGateSelected (carrier.square.records transport.leg.source) gate = true) : terminalGateSelected (carrier.square.records transport.leg.target) gate = true",
      "TerminalFourCornerCarrier.boundaryPullback_meet_join_left": "theorem TerminalFourCornerCarrier.boundaryPullback_meet_join_left (carrier : TerminalFourCornerCarrier system) (valuation : Valuation (carrier.extracted .join).boundary.length) : (carrier.optimumLegTransport .meetLeft).boundaryPullback ((carrier.optimumLegTransport .leftJoin).boundaryPullback valuation) = terminalBoundaryPullback carrier.candidate (carrier.square.records .meet) (carrier.square.records .join) valuation",
      "TerminalFourCornerCarrier.boundaryPullback_meet_join_right": "theorem TerminalFourCornerCarrier.boundaryPullback_meet_join_right (carrier : TerminalFourCornerCarrier system) (valuation : Valuation (carrier.extracted .join).boundary.length) : (carrier.optimumLegTransport .meetRight).boundaryPullback ((carrier.optimumLegTransport .rightJoin).boundaryPullback valuation) = terminalBoundaryPullback carrier.candidate (carrier.square.records .meet) (carrier.square.records .join) valuation",
      "TerminalFourCornerCarrier.boundaryPullback_square": "theorem TerminalFourCornerCarrier.boundaryPullback_square (carrier : TerminalFourCornerCarrier system) (valuation : Valuation (carrier.extracted .join).boundary.length) : (carrier.optimumLegTransport .meetLeft).boundaryPullback ((carrier.optimumLegTransport .leftJoin).boundaryPullback valuation) = (carrier.optimumLegTransport .meetRight).boundaryPullback ((carrier.optimumLegTransport .rightJoin).boundaryPullback valuation)",
      "TerminalOptimumLegTransport.extracted_retained_semantics": "theorem TerminalOptimumLegTransport.extracted_retained_semantics (transport : TerminalOptimumLegTransport carrier) (valuation : Valuation (carrier.extracted transport.leg.target).boundary.length) (sourceIndex : Fin (carrier.extracted transport.leg.source).interface.length) (targetIndex : Fin (carrier.extracted transport.leg.target).interface.length) (retained : transport.retainedOutput? sourceIndex = some targetIndex) : (carrier.cornerImplementation transport.leg.source).candidate.semantics (transport.boundaryPullback valuation) sourceIndex = (carrier.cornerImplementation transport.leg.target).candidate.semantics valuation targetIndex",
      "TerminalOptimumLegTransport.realization_retained_semantics": "theorem TerminalOptimumLegTransport.realization_retained_semantics (transport : TerminalOptimumLegTransport carrier) (sourceRealization : TerminalFullRealization (carrier.cornerImplementation transport.leg.source)) (targetRealization : TerminalFullRealization (carrier.cornerImplementation transport.leg.target)) (valuation : Valuation (carrier.extracted transport.leg.target).boundary.length) (sourceIndex : Fin (carrier.extracted transport.leg.source).interface.length) (targetIndex : Fin (carrier.extracted transport.leg.target).interface.length) (retained : transport.retainedOutput? sourceIndex = some targetIndex) : sourceRealization.implementation.candidate.semantics (transport.boundaryPullback valuation) sourceIndex = targetRealization.implementation.candidate.semantics valuation targetIndex",
      "TerminalFourCornerOptimumFamily.full_retained_semantics": "theorem TerminalFourCornerOptimumFamily.full_retained_semantics {observe : Implementation (inputs + gates) gates -> TerminalProfile profileWidth} (family : TerminalFourCornerOptimumFamily carrier observe) (leg : TerminalOptimumSquareLeg) (valuation : Valuation (carrier.extracted leg.target).boundary.length) (sourceIndex : Fin (carrier.extracted leg.source).interface.length) (targetIndex : Fin (carrier.extracted leg.target).interface.length) (retained : (carrier.optimumLegTransport leg).retainedOutput? sourceIndex = some targetIndex) : (family.fullLocalRealization leg.source).implementation.candidate.semantics ((carrier.optimumLegTransport leg).boundaryPullback valuation) sourceIndex = (family.fullLocalRealization leg.target).implementation.candidate.semantics valuation targetIndex",
      "TerminalFourCornerOptimumFamily.quotient_retained_semantics": "theorem TerminalFourCornerOptimumFamily.quotient_retained_semantics {observe : Implementation (inputs + gates) gates -> TerminalProfile profileWidth} (family : TerminalFourCornerOptimumFamily carrier observe) (leg : TerminalOptimumSquareLeg) (valuation : Valuation (carrier.extracted leg.target).boundary.length) (sourceIndex : Fin (carrier.extracted leg.source).interface.length) (targetIndex : Fin (carrier.extracted leg.target).interface.length) (retained : (carrier.optimumLegTransport leg).retainedOutput? sourceIndex = some targetIndex) : (family.quotientLocalRealization leg.source).implementation.candidate.semantics ((carrier.optimumLegTransport leg).boundaryPullback valuation) sourceIndex = (family.quotientLocalRealization leg.target).implementation.candidate.semantics valuation targetIndex",
      "TerminalFourCornerCarrier.canonicalFull_retained_semantics": "theorem TerminalFourCornerCarrier.canonicalFull_retained_semantics (carrier : TerminalFourCornerCarrier system) (observe : Implementation (inputs + gates) gates -> TerminalProfile profileWidth) (leg : TerminalOptimumSquareLeg) (valuation : Valuation (carrier.extracted leg.target).boundary.length) (sourceIndex : Fin (carrier.extracted leg.source).interface.length) (targetIndex : Fin (carrier.extracted leg.target).interface.length) (retained : (carrier.optimumLegTransport leg).retainedOutput? sourceIndex = some targetIndex) : ((carrier.canonicalOptimumFamily observe).fullLocalRealization leg.source).implementation.candidate.semantics ((carrier.optimumLegTransport leg).boundaryPullback valuation) sourceIndex = ((carrier.canonicalOptimumFamily observe).fullLocalRealization leg.target).implementation.candidate.semantics valuation targetIndex",
      "TerminalFourCornerCarrier.canonicalQuotient_retained_semantics": "theorem TerminalFourCornerCarrier.canonicalQuotient_retained_semantics (carrier : TerminalFourCornerCarrier system) (observe : Implementation (inputs + gates) gates -> TerminalProfile profileWidth) (leg : TerminalOptimumSquareLeg) (valuation : Valuation (carrier.extracted leg.target).boundary.length) (sourceIndex : Fin (carrier.extracted leg.source).interface.length) (targetIndex : Fin (carrier.extracted leg.target).interface.length) (retained : (carrier.optimumLegTransport leg).retainedOutput? sourceIndex = some targetIndex) : ((carrier.canonicalOptimumFamily observe).quotientLocalRealization leg.source).implementation.candidate.semantics ((carrier.optimumLegTransport leg).boundaryPullback valuation) sourceIndex = ((carrier.canonicalOptimumFamily observe).quotientLocalRealization leg.target).implementation.candidate.semantics valuation targetIndex"
    }
  }
];
const AUDIT = 'lean-audit/PNPContextAwareSquareTransportAxiomAudit.lean';
const NESTED_REGRESSION = 'lean-regression/PNPResidualTerminalNestedOpenTransport.lean';
const SQUARE_REGRESSION = 'lean-regression/PNPResidualTerminalFourCornerOpenTransport.lean';
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = source => stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();

function block0(source, name) {
  const stripped = stripLeanCommentsAndStrings0(source);
  const boundaries = [...stripped.matchAll(/^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*(?:(?:def|theorem|inductive|structure|abbrev)[ \t]+([^\s({:]+)|variable\b|namespace\b|end\b)/gmu)];
  const index = boundaries.findIndex(item => item[1] === name);
  return index < 0 ? '' : compact0(source.slice(boundaries[index].index,
    boundaries[index + 1]?.index ?? source.length));
}

function signature0(block) {
  const separator = block.indexOf(' := ');
  return separator < 0 ? '' : block.slice(0, separator);
}

function checkedRegion0(source, spec) {
  return spec.kind === 'nested' ? source.slice(source.indexOf('def terminalOpenWireValue\n')) : source;
}

function validateSource0(source, spec) {
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  const region = checkedRegion0(source, spec);
  const clean = compact0(region);
  require0(region.length > 0, 'region');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|implemented_by|csimp|callerCertificate|suppliedTransport|transportCertificate)\b|#(?:eval|reduce|guard)\b/u.test(clean),
    'shortcut-or-certificate');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(region).map(head => head.name)) ===
    JSON.stringify(spec.heads), 'closed-interface');
  for (const [name, signature] of Object.entries(spec.signatures))
    require0(signature0(block0(source, name)) === signature, 'signature:' + name);
  const block = name => block0(source, name);
  if (spec.kind === 'nested') {
    require0(block('terminalOpenWireValue').includes(
      '| .input index => terminalBoundaryValue (terminalBoundaryPorts candidate.program records) valuation (.input index)'),
      'actual-primary-boundary');
    require0(block('terminalOpenWireValue').includes(
      '| .gate index => if terminalGateSelected records index then terminalOpenGateEvaluation candidate records valuation index else terminalBoundaryValue (terminalBoundaryPorts candidate.program records) valuation (.gate index)'),
      'internalized-wire-value');
    require0(block('terminalBoundaryPullback').endsWith(
      'fun index => terminalOpenWireValue candidate large valuation ((terminalBoundaryPorts candidate.program small).get index)'),
      'computed-ordered-pullback');
    require0(block('terminalOpenGateEvaluation_pullback').includes('Program.evalTerminalOpenAux_nested candidate.program') &&
      block('terminalOpenGateEvaluation_pullback').includes('physicalTerminalSourcesAccounted candidate small'),
      'actual-source-derived-semantics');
    require0(block('terminalBoundaryPullback_compose').includes('terminalOpenWireValue_pullback_on_boundary candidate small middle large'),
      'nested-composition');
  } else {
    require0(JSON.stringify([...source.matchAll(/^variable[^\n]+$/gmu)].map(match => match[0])) ===
      JSON.stringify([
        'variable {inputs gates outputs profileWidth : Nat}',
        'variable {system : TerminalSaturationSystem inputs gates outputs profileWidth}',
        'variable {carrier : TerminalFourCornerCarrier system}',
      ]), 'exact-general-binders');
    require0(block('TerminalOptimumLegTransport.selectedGateTransport').includes('transport.recordsSubset _ member'),
      'derived-square-inclusion');
    require0(block('TerminalOptimumLegTransport.boundaryPullback').endsWith(
      'terminalBoundaryPullback carrier.candidate (carrier.square.records transport.leg.source) (carrier.square.records transport.leg.target)'),
      'actual-carrier-pullback');
    require0(block('TerminalFourCornerCarrier.boundaryPullback_square').endsWith(
      '(carrier.boundaryPullback_meet_join_left valuation).trans (carrier.boundaryPullback_meet_join_right valuation).symm'),
      'two-physical-paths');
    require0(block('TerminalOptimumLegTransport.extracted_retained_semantics').includes('terminalOpenSupportSemantics_pullback carrier.candidate') &&
      block('TerminalOptimumLegTransport.extracted_retained_semantics').includes('transport.retainedOutput?_eq_some_iff'),
      'same-retained-producer');
    require0(block('TerminalOptimumLegTransport.realization_retained_semantics').includes('sourceRealization.realize_semantics') &&
      block('TerminalOptimumLegTransport.realization_retained_semantics').includes('targetRealization.realize_semantics'),
      'actual-realization-equivalence');
    require0(block('TerminalFourCornerCarrier.canonicalFull_retained_semantics').endsWith(
      '(carrier.canonicalOptimumFamily observe).full_retained_semantics leg valuation sourceIndex targetIndex retained'),
      'computed-full-minimum-family');
    require0(block('TerminalFourCornerCarrier.canonicalQuotient_retained_semantics').endsWith(
      '(carrier.canonicalOptimumFamily observe).quotient_retained_semantics leg valuation sourceIndex targetIndex retained'),
      'computed-quotient-minimum-family');
  }
  return failures;
}

async function rejectMutation0(spec, old, replacement, expected) {
  const source = await text0(spec.path);
  assert.ok(source.includes(old), 'hostile mutation anchor: ' + old);
  const changed = source.replace(old, replacement);
  assert.notEqual(changed, source);
  assert.ok(validateSource0(changed, spec).includes(expected), expected);
}
const nested = SPECS.find(spec => spec.kind === 'nested');
const square = SPECS.find(spec => spec.kind === 'square');

test('M261 exact nested and square transport interfaces remain general and source-derived', async () => {
  for (const spec of SPECS) assert.deepEqual(validateSource0(await text0(spec.path), spec), []);
});

test('M261 rejects independent or discarded internalized boundary values', async () => {
  await rejectMutation0(nested,
    'if terminalGateSelected records index then\n        terminalOpenGateEvaluation candidate records valuation index',
    'if terminalGateSelected records index then\n        false', 'internalized-wire-value');
  await rejectMutation0(nested,
    'fun index => terminalOpenWireValue candidate large valuation',
    'fun index => terminalOpenWireValue candidate small valuation', 'computed-ordered-pullback');
  await rejectMutation0(nested,
    '((terminalBoundaryPorts candidate.program small).get index)\n\nprivate theorem terminalBoundaryValue_pullback',
    '(.input 0)\n\nprivate theorem terminalBoundaryValue_pullback', 'computed-ordered-pullback');
});

test('M261 rejects weakened gate inclusion and narrowed semantic scope', async () => {
  await rejectMutation0(nested,
    '(included : forall gate, terminalGateSelected small gate = true ->\n      terminalGateSelected large gate = true)',
    '(included : True)', 'signature:terminalOpenGateEvaluation_pullback');
  await rejectMutation0(nested,
    '(middleIncluded : forall gate, terminalGateSelected middle gate = true ->\n      terminalGateSelected large gate = true)\n    (valuation : Valuation (terminalBoundaryPorts candidate.program large).length) :\n    terminalBoundaryPullback',
    '(middleIncluded : True)\n    (valuation : Valuation (terminalBoundaryPorts candidate.program large).length) :\n    terminalBoundaryPullback',
    'signature:terminalBoundaryPullback_compose');
  await rejectMutation0(square,
    'variable {inputs gates outputs profileWidth : Nat}',
    'variable {inputs gates outputs profileWidth : Nat}\nvariable (transportCertificate : True)',
    'exact-general-binders');
});

test('M261 rejects reversing a square leg or dropping a physical path', async () => {
  await rejectMutation0(square,
    '(carrier.square.records transport.leg.source)\n    (carrier.square.records transport.leg.target)',
    '(carrier.square.records transport.leg.target)\n    (carrier.square.records transport.leg.source)',
    'actual-carrier-pullback');
  await rejectMutation0(square,
    '(carrier.boundaryPullback_meet_join_right valuation).symm',
    '(carrier.boundaryPullback_meet_join_left valuation).symm', 'two-physical-paths');
  await rejectMutation0(square,
    'exact decide_eq_true (transport.recordsSubset _ member)',
    'exact callerCertificate', 'derived-square-inclusion');
});

test('M261 rejects replacing actual canonical minima with a supplied comparison', async () => {
  await rejectMutation0(square,
    '(carrier.canonicalOptimumFamily observe).full_retained_semantics\n    leg valuation sourceIndex targetIndex retained',
    'callerCertificate', 'computed-full-minimum-family');
  await rejectMutation0(square,
    '(carrier.canonicalOptimumFamily observe).quotient_retained_semantics\n    leg valuation sourceIndex targetIndex retained',
    'callerCertificate', 'computed-quotient-minimum-family');
});

test('M261 rejects hidden proof authority and unchecked execution overrides', async () => {
  for (const spec of SPECS) {
    const source = await text0(spec.path);
    assert.ok(validateSource0(source + '\naxiom hidden : False\n', spec).includes('assumption'));
    assert.ok(validateSource0(source + '\nexample : True := by trivial\n', spec).includes('unaudited-form'));
    assert.ok(validateSource0(source + '\nattribute [implemented_by hidden] terminalBoundaryPullback\n', spec)
      .includes('shortcut-or-certificate'));
  }
});

test('M261 reviewed producers, exact root audit and durable workflow use the same theorem set', async () => {
  const [inventory, audit, root, workflow] = await Promise.all([
    text0('lean-audit/PNPTheoremInventory.lean'), text0(AUDIT),
    text0('lean/PNP.lean'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  for (const name of NAMES) {
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item => item === name).length, 1, name);
    assert.equal(inventory.split(String.fromCharCode(96) + name + ',').length - 1, 1, name);
    assert.equal(workflow.split('"' + name + '"').length - 1, 1, name);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]), ['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match => match[1]), NAMES);
  assert.match(root, /^import PNP\.ResidualTerminalFourCornerOpenTransport$/mu);
  for (const token of [
    'node --test audits/lean-context-aware-square-transport0.test.mjs',
    'lake env lean -DwarningAsError=true ' + AUDIT,
    'lake env lean -DwarningAsError=true ' + NESTED_REGRESSION,
    'lake env lean -DwarningAsError=true ' + SQUARE_REGRESSION,
  ]) assert.ok(workflow.includes(token), token);
});

test('M261 regressions separate arbitrary open transport from unconstrained ambient comparison', async () => {
  const [generic, fixture] = await Promise.all([text0(NESTED_REGRESSION), text0(SQUARE_REGRESSION)]);
  assert.match(generic, /terminalBoundaryPullback_compose/u);
  assert.match(generic, /terminalOpenGateEvaluation_pullback/u);
  for (const label of [
    'empty-selected-support', 'exact-small-boundary', 'retained-primary-and-external-gate',
    'right-corner-boundary-order', 'join-boundary-only-actual-primary-sources',
    'internalized-values-are-computed', 'identity-all-four-boundary-valuations',
    'left-nested-substitution-all-valuations', 'right-nested-substitution-all-valuations',
    'duplicate-unordered-support', 'retained-two-output-semantics',
    'computed-square-has-genuine-meet', 'computed-square-two-paths',
    'internalized-ambient-bit-is-not-free', 'unconstrained-ambient-comparison-remains-distinct',
    'retained-output-producer-order',
  ]) assert.ok(fixture.includes('"' + label + '"'), label);
  assert.match(fixture, /M261_FOUR_CORNER_OPEN_TRANSPORT_RUNTIME_GREEN/u);
  assert.match(fixture, /throw \(IO\.userError/u);
  assert.match(fixture, /abbrev Record := TerminalPrimitiveRecord 2 4 2 1/u);
  const runtime = fixture.slice(fixture.indexOf('#eval '));
  assert.doesNotMatch(runtime, /canonicalOptimumFamily|referenceMinimum|allImplementations|allSubsets/u);
  assert.doesNotMatch(fixture, /#eval!|\bnative_decide\b/u);
});

const M261_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-14-261';
const M261_MILESTONE = 'context-aware-square-transport';
const M261_HASHES = Object.freeze({
  "PNP.DirectWire.terminalOpenGateEvaluation_pullback": "35b9c3d02da43f951376e48ccd7d5ba97539be554d23a9d7dddff9cbefae8526",
  "PNP.DirectWire.terminalOpenSupportSemantics_pullback": "8d84b0ca652c271d873986c35aeb5421bd37dd88fad0fae2cd7de521824ec1a4",
  "PNP.DirectWire.terminalBoundaryPullback_identity": "71783e1a89e5a590fa9092e9c4af7f9cc28182317428be2530ca32cca13d93d0",
  "PNP.DirectWire.terminalBoundaryPullback_compose": "e63b7f727d763163014f598b5e4f10b70938b885228aa7092f60f06924fb1f1e",
  "PNP.DirectWire.TerminalOptimumLegTransport.selectedGateTransport": "393bcf57ffe9063520828c2e67f1216fd79cd810ae5867e3d961c81f278cba5e",
  "PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_meet_join_left": "5f87fc82783c695cee293545700beacaddf310b740f32262449887be9a438eed",
  "PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_meet_join_right": "114556b3dc918cb2593f4df380a0dd47df7bc85d14e16d30602810c6466453dc",
  "PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_square": "97f9a8f9208f99f55767cb101eda981fdc64d1dfa0345277fa0a34209ec247ad",
  "PNP.DirectWire.TerminalOptimumLegTransport.extracted_retained_semantics": "4fd1fe7a44bec0d3dfc5b1cfe2bf20ff2e70c0e877feee6b196e6a39faaba6d3",
  "PNP.DirectWire.TerminalOptimumLegTransport.realization_retained_semantics": "f68469c854249882dcdb32bf48257c27581d289dc7a7efc323a4ac3025707f70",
  "PNP.DirectWire.TerminalFourCornerOptimumFamily.full_retained_semantics": "3c817f60b6078fc084d819793d47f4c1d1f8625c85540628c45d8089e71faf05",
  "PNP.DirectWire.TerminalFourCornerOptimumFamily.quotient_retained_semantics": "11e22a080e7420cc7e6c10c2f6558588bb79bd9274bf7dacccbfba817e30f6d8",
  "PNP.DirectWire.TerminalFourCornerCarrier.canonicalFull_retained_semantics": "de03dff609d419f5ecc843e92ca627d0430f1407413e8722a16d0679a6fdeb13",
  "PNP.DirectWire.TerminalFourCornerCarrier.canonicalQuotient_retained_semantics": "a8bcb2bb6dc0154959d37c2fdcb67eb451eea01759caa939b8072996811253d3"
});
const M261_STATUS_FIELDS = Object.freeze({
  "leanContextAwareSquareTransportFormalized": true,
  "leanContextAwareSquareTransportAxiomAuditPassed": true,
  "leanContextAwareSquareTransportAuditedDeclarationCount": 14,
  "leanContextAwareSquareTransportSelectedGateSemanticsTheorem": "PNP.DirectWire.terminalOpenGateEvaluation_pullback",
  "leanContextAwareSquareTransportRetainedInterfaceSemanticsTheorem": "PNP.DirectWire.terminalOpenSupportSemantics_pullback",
  "leanContextAwareSquareTransportIdentityTheorem": "PNP.DirectWire.terminalBoundaryPullback_identity",
  "leanContextAwareSquareTransportCompositionTheorem": "PNP.DirectWire.terminalBoundaryPullback_compose",
  "leanContextAwareSquareTransportSquareLegGateInclusionTheorem": "PNP.DirectWire.TerminalOptimumLegTransport.selectedGateTransport",
  "leanContextAwareSquareTransportLeftPathTheorem": "PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_meet_join_left",
  "leanContextAwareSquareTransportRightPathTheorem": "PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_meet_join_right",
  "leanContextAwareSquareTransportSquarePathEqualityTheorem": "PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_square",
  "leanContextAwareSquareTransportExtractedRetainedSemanticsTheorem": "PNP.DirectWire.TerminalOptimumLegTransport.extracted_retained_semantics",
  "leanContextAwareSquareTransportRealizationRetainedSemanticsTheorem": "PNP.DirectWire.TerminalOptimumLegTransport.realization_retained_semantics",
  "leanContextAwareSquareTransportFullFamilyRetainedSemanticsTheorem": "PNP.DirectWire.TerminalFourCornerOptimumFamily.full_retained_semantics",
  "leanContextAwareSquareTransportQuotientFamilyRetainedSemanticsTheorem": "PNP.DirectWire.TerminalFourCornerOptimumFamily.quotient_retained_semantics",
  "leanContextAwareSquareTransportCanonicalFullRetainedSemanticsTheorem": "PNP.DirectWire.TerminalFourCornerCarrier.canonicalFull_retained_semantics",
  "leanContextAwareSquareTransportCanonicalQuotientRetainedSemanticsTheorem": "PNP.DirectWire.TerminalFourCornerCarrier.canonicalQuotient_retained_semantics",
  "leanContextAwareSquareTransportComputedBoundaryPullbackDerived": true,
  "leanContextAwareSquareTransportArbitraryOpenValuationsCovered": true,
  "leanContextAwareSquareTransportInternalizedWireValuesComputed": true,
  "leanContextAwareSquareTransportSelectedGateAndInterfaceSemanticsProved": true,
  "leanContextAwareSquareTransportIdentityAndCompositionProved": true,
  "leanContextAwareSquareTransportSquareLegMapsDerived": true,
  "leanContextAwareSquareTransportTwoPathValuationEqualityProved": true,
  "leanContextAwareSquareTransportRetainedRealizerOutputsProved": true,
  "leanContextAwareSquareTransportCanonicalFullAndQuotientComparisonProved": true,
  "leanContextAwareSquareTransportExistingAmbientClassifierPreserved": true,
  "leanContextAwareSquareTransportCallerSuppliedTransportRequired": false,
  "leanContextAwareSquareTransportCallerSuppliedCorrectnessRequired": false,
  "leanContextAwareSquareTransportWholeCircuitValuationsOnly": false,
  "leanContextAwareSquareTransportArbitraryObserverEqualityProved": false,
  "leanContextAwareSquareTransportPhysicalMinimumGluingProved": false,
  "leanContextAwareSquareTransportChargeAndObligationOwnershipProved": false,
  "leanContextAwareSquareTransportFullManuscriptCarrierProved": false,
  "leanContextAwareSquareTransportCompleteObligationCalculusProved": false,
  "leanContextAwareSquareTransportCompletePackageEProved": false,
  "leanContextAwareSquareTransportGlobalRouteCoverageProved": false,
  "leanContextAwareSquareTransportUnconditionalZeroSlackProved": false,
  "leanContextAwareSquareTransportExactGeneralPCCMinProved": false,
  "leanContextAwareSquareTransportPolynomialRuntimeProved": false,
  "leanContextAwareSquareTransportRuntimeExecutionIsProofAuthority": false,
  "leanContextAwareSquareTransportScope": "arbitrary-finite-nested-supports-all-open-boundary-valuations-computed-internalized-wire-substitution-selected-gate-and-interface-preservation-identity-composition-four-corner-path-equality-retained-full-and-quotient-realizer-outputs-no-arbitrary-observer-equality-or-charge-gluing-or-global-runtime"
});
const M261_AXIOMS = Object.freeze({
  "PNP.DirectWire.terminalOpenGateEvaluation_pullback": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalOpenSupportSemantics_pullback": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalBoundaryPullback_identity": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalBoundaryPullback_compose": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.TerminalOptimumLegTransport.selectedGateTransport": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_meet_join_left": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_meet_join_right": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_square": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.TerminalOptimumLegTransport.extracted_retained_semantics": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.TerminalOptimumLegTransport.realization_retained_semantics": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.TerminalFourCornerOptimumFamily.full_retained_semantics": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.TerminalFourCornerOptimumFamily.quotient_retained_semantics": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.TerminalFourCornerCarrier.canonicalFull_retained_semantics": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.TerminalFourCornerCarrier.canonicalQuotient_retained_semantics": [
    "Quot.sound",
    "propext"
  ]
});

const M261_MODULES = Object.freeze({
  "PNP.DirectWire.terminalOpenGateEvaluation_pullback": "PNP.ResidualTerminalSupportExtraction",
  "PNP.DirectWire.terminalOpenSupportSemantics_pullback": "PNP.ResidualTerminalSupportExtraction",
  "PNP.DirectWire.terminalBoundaryPullback_identity": "PNP.ResidualTerminalSupportExtraction",
  "PNP.DirectWire.terminalBoundaryPullback_compose": "PNP.ResidualTerminalSupportExtraction",
  "PNP.DirectWire.TerminalOptimumLegTransport.selectedGateTransport": "PNP.ResidualTerminalFourCornerOpenTransport",
  "PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_meet_join_left": "PNP.ResidualTerminalFourCornerOpenTransport",
  "PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_meet_join_right": "PNP.ResidualTerminalFourCornerOpenTransport",
  "PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_square": "PNP.ResidualTerminalFourCornerOpenTransport",
  "PNP.DirectWire.TerminalOptimumLegTransport.extracted_retained_semantics": "PNP.ResidualTerminalFourCornerOpenTransport",
  "PNP.DirectWire.TerminalOptimumLegTransport.realization_retained_semantics": "PNP.ResidualTerminalFourCornerOpenTransport",
  "PNP.DirectWire.TerminalFourCornerOptimumFamily.full_retained_semantics": "PNP.ResidualTerminalFourCornerOpenTransport",
  "PNP.DirectWire.TerminalFourCornerOptimumFamily.quotient_retained_semantics": "PNP.ResidualTerminalFourCornerOpenTransport",
  "PNP.DirectWire.TerminalFourCornerCarrier.canonicalFull_retained_semantics": "PNP.ResidualTerminalFourCornerOpenTransport",
  "PNP.DirectWire.TerminalFourCornerCarrier.canonicalQuotient_retained_semantics": "PNP.ResidualTerminalFourCornerOpenTransport"
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

test('M261 compiled context-aware square-transport interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M261_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M261_COORDINATE)
    assert.equal(map.coordinate, M261_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M261_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, M261_MODULES[name], name);
      assert.deepEqual(declaration.axioms, M261_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M261_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M261_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M261_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "arbitrary larger open-boundary valuations, not only whole-circuit executions",
  "no caller-supplied transport or correctness certificate",
  "does not prove equality of arbitrary implementation-dependent observers or profiles",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M261 publication rejects weakened, supplied, assumption-backed and widened complete-calculus substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M261_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M261_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = 'PNP.DirectWire.TerminalFourCornerCarrier.boundaryPullback_square';
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M261_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M261_MILESTONE
    ? {...row, nonClaim:'Retained-output transport proves arbitrary observer equality, physical minimum gluing and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M261 adds context-aware square-transport coverage without complete-calculus, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M261_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "context-aware Boolean transport dependency",
  "every larger open-boundary valuation",
  "does not equate arbitrary observers, physically glue local minima",
  "No fixed load-bearing checkpoint changes state",
  "40% proof estimate"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M261_COORDINATE) return;
  assert.deepEqual(progress.tracks.map(track => track.pointsEarned), [13, 20, 2, 1, 4]);
  assert.equal(progress.proofCompletion.percent, 40);
  assert.deepEqual(inventory.projectAxioms, []);
  assert.deepEqual(progress.projectSpecificAxiomsRemaining, []);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.deepEqual(progress.rootTheorem, {
    name:'PNP.Main.p_eq_np', present:false, built:false, axiomAuditPassed:false,
  });
  const inflated = structuredClone(progress);
  inflated.proofCompletion.pointsEarned += 1;
  inflated.proofCompletion.percent += 1;
  assert.throws(() => validateProofProgress0(inflated, status, inventory),
    error => error.code === 'ProofCompletion.StoredEarned');
});

test('M261 current summaries distinguish retained-output transport from complete-calculus and global completion and retain metrics and separate-site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_context_aware_square_transport.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "The theorem covers every larger open-boundary valuation, not only whole-circuit executions.",
  "unconstrained-ambient coherence classifier remains a distinct, unchanged relation.",
  "Retained Boolean-output transport does not prove arbitrary observer equality or physical minimum gluing.",
  "Runtime execution is test evidence, not theorem authority.",
  "Publication decision: defer a separate PNPLabs cycle for M261."
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-14-context-aware-square-transport.md'));
  assert.match(plan, /Publication decision: defer a separate PNPLabs cycle for M261\./u);
  if (progress.asOfCoordinate !== M261_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_context_aware_square_transport.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});

test('M261 status rejects every changed transport claim, theorem pin and scope field', async () => {
  const {status} = await compiledSources0();
  for (const [field,value] of Object.entries(M261_STATUS_FIELDS)) {
    const mutation = {...status, [field]:typeof value === 'boolean' ? !value
      : typeof value === 'number' ? value + 1 : value + ':unreviewed'};
    const result = await CheckFormalReconstructionStatus0({writeOutput:false,
      statusOverride:mutation, siteOverride:mutation});
    assert.equal(result.tag, 'reject', field);
    assert.equal(result.coord, 'FormalReconstructionStatus.Field', field);
    assert.deepEqual(result.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
  }
});
