import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';
import {
  DeriveFormalPublication0, MilestoneTheoremKernelTypeSha2560,
  REQUIRED_MILESTONE_THEOREMS0, stableStringify0,
} from '../formal-publication0.mjs';
import { validateProofProgress0 } from '../pcc-proof-progress0.mjs';

const SOURCE = 'lean/PNP/ResidualTerminalPhysicalSupportCompletion.lean';
const AUDIT = 'lean-audit/PNPSourceBoundedPhysicalBoundaryAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPSourceBoundedPhysicalBoundary.lean';
const NAMES = [
  "PNP.DirectWire.SourceListOrder.mem_unique",
  "PNP.DirectWire.SourceListOrder.unique_nodup",
  "PNP.DirectWire.SourceListOrder.unique_length_le",
  "PNP.DirectWire.SourceListOrder.mem_canonical",
  "PNP.DirectWire.SourceListOrder.canonical_nodup",
  "PNP.DirectWire.SourceListOrder.canonical_length_le",
  "PNP.DirectWire.SourceListOrder.canonical_ordered",
  "PNP.DirectWire.SourceListOrder.ordered_eq_of_mem",
  "PNP.DirectWire.SourceListOrder.canonical_eq_reference",
  "PNP.DirectWire.TerminalSupportWire.orderCode_injective",
  "PNP.DirectWire.allTerminalSupportWires_strictOrder",
  "PNP.DirectWire.Source.mem_terminalWireOccurrences_iff",
  "PNP.DirectWire.Source.terminalWireOccurrences_length",
  "PNP.DirectWire.terminalSourceWireOccurrences_length",
  "PNP.DirectWire.terminalBoundaryWire_mem_sourceOccurrences",
  "PNP.DirectWire.terminalBoundaryPortsSourceDriven_eq_reference",
  "PNP.DirectWire.terminalBoundaryPortsSourceDriven_length",
  "PNP.DirectWire.terminalBoundaryPortsSourceDriven_nodup",
  "PNP.DirectWire.terminalBoundaryPortsSourceDriven_ordered",
  "PNP.DirectWire.terminalBoundaryPorts_reference",
  "PNP.DirectWire.terminalBoundaryPorts_length",
  "PNP.DirectWire.terminalBoundaryPorts_nodup",
  "PNP.DirectWire.terminalBoundaryPorts_ordered"
];
const SPECS = [
  {
    "kind": "canonical",
    "path": "lean/PNP/NANDSourceListOrder.lean",
    "prefix": "PNP.DirectWire.SourceListOrder.",
    "imports": [
      "PNP.NANDEnumerator",
      "Init.Data.List.Sort.Lemmas"
    ],
    "signatures": {
      "mem_unique": "theorem mem_unique (item : alpha) (items : List alpha) : item ∈ unique items ↔ item ∈ items",
      "unique_nodup": "theorem unique_nodup (items : List alpha) : (unique items).Nodup",
      "unique_length_le": "theorem unique_length_le (items : List alpha) : (unique items).length ≤ items.length",
      "mem_canonical": "theorem mem_canonical (key : alpha → Nat) (item : alpha) (items : List alpha) : item ∈ canonical key items ↔ item ∈ items",
      "canonical_nodup": "theorem canonical_nodup (key : alpha → Nat) (items : List alpha) : (canonical key items).Nodup",
      "canonical_length_le": "theorem canonical_length_le (key : alpha → Nat) (items : List alpha) : (canonical key items).length ≤ items.length",
      "canonical_ordered": "theorem canonical_ordered (key : alpha → Nat) (items : List alpha) : (canonical key items).Pairwise (fun left right => key left ≤ key right)",
      "ordered_eq_of_mem": "theorem ordered_eq_of_mem (key : alpha → Nat) (injective : Function.Injective key) (left right : List alpha) (leftDistinct : left.Nodup) (rightDistinct : right.Nodup) (leftOrdered : left.Pairwise (fun a b => key a ≤ key b)) (rightOrdered : right.Pairwise (fun a b => key a ≤ key b)) (members : ∀ item, item ∈ left ↔ item ∈ right) : left = right",
      "canonical_eq_reference": "theorem canonical_eq_reference (key : alpha → Nat) (injective : Function.Injective key) (items reference : List alpha) (distinct : reference.Nodup) (ordered : reference.Pairwise (fun a b => key a ≤ key b)) (members : ∀ item, item ∈ items ↔ item ∈ reference) : canonical key items = reference"
    },
    "heads": [
      "unique",
      "mem_unique",
      "unique_nodup",
      "unique_length_le",
      "canonical",
      "mem_canonical",
      "canonical_nodup",
      "canonical_length_le",
      "canonical_ordered",
      "ordered_eq_of_mem",
      "canonical_eq_reference"
    ]
  },
  {
    "kind": "physical",
    "path": "lean/PNP/ResidualTerminalPhysicalSupportCompletion.lean",
    "prefix": "PNP.DirectWire.",
    "imports": [
      "PNP.ResidualTerminalExecutableSaturation",
      "PNP.NANDSourceListOrder"
    ],
    "signatures": {
      "TerminalSupportWire.orderCode_injective": "theorem TerminalSupportWire.orderCode_injective {inputs gates : Nat} : Function.Injective (@TerminalSupportWire.orderCode inputs gates)",
      "allTerminalSupportWires_strictOrder": "theorem allTerminalSupportWires_strictOrder (inputs gates : Nat) : (allTerminalSupportWires inputs gates).Pairwise (fun left right => left.orderCode < right.orderCode)",
      "Source.mem_terminalWireOccurrences_iff": "theorem Source.mem_terminalWireOccurrences_iff {inputs gates : Nat} (source : Source inputs gates) (wire : TerminalSupportWire inputs gates) : wire ∈ source.terminalWireOccurrences ↔ source.terminalSupportWire? = some wire",
      "Source.terminalWireOccurrences_length": "theorem Source.terminalWireOccurrences_length {inputs gates : Nat} (source : Source inputs gates) : source.terminalWireOccurrences.length ≤ 1",
      "terminalSourceWireOccurrences_length": "theorem terminalSourceWireOccurrences_length {inputs gates : Nat} (program : Program inputs gates) : (terminalSourceWireOccurrences program).length ≤ 2 * gates",
      "terminalBoundaryWire_mem_sourceOccurrences": "theorem terminalBoundaryWire_mem_sourceOccurrences {inputs gates outputs profileWidth : Nat} (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (wire : TerminalSupportWire inputs gates) (crossing : terminalBoundaryWire program records wire = true) : wire ∈ terminalSourceWireOccurrences program",
      "terminalBoundaryPortsSourceDriven_eq_reference": "theorem terminalBoundaryPortsSourceDriven_eq_reference {inputs gates outputs profileWidth : Nat} (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : terminalBoundaryPortsSourceDriven program records = (allTerminalSupportWires inputs gates).filter (terminalBoundaryWire program records)",
      "terminalBoundaryPortsSourceDriven_length": "theorem terminalBoundaryPortsSourceDriven_length {inputs gates outputs profileWidth : Nat} (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : (terminalBoundaryPortsSourceDriven program records).length ≤ 2 * gates",
      "terminalBoundaryPortsSourceDriven_nodup": "theorem terminalBoundaryPortsSourceDriven_nodup {inputs gates outputs profileWidth : Nat} (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : (terminalBoundaryPortsSourceDriven program records).Nodup",
      "terminalBoundaryPortsSourceDriven_ordered": "theorem terminalBoundaryPortsSourceDriven_ordered {inputs gates outputs profileWidth : Nat} (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : (terminalBoundaryPortsSourceDriven program records).Pairwise (fun left right => left.orderCode ≤ right.orderCode)",
      "terminalBoundaryPorts_reference": "theorem terminalBoundaryPorts_reference {inputs gates outputs profileWidth : Nat} (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : terminalBoundaryPorts program records = (allTerminalSupportWires inputs gates).filter (terminalBoundaryWire program records)",
      "terminalBoundaryPorts_length": "theorem terminalBoundaryPorts_length {inputs gates outputs profileWidth : Nat} (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : (terminalBoundaryPorts program records).length ≤ 2 * gates",
      "terminalBoundaryPorts_nodup": "theorem terminalBoundaryPorts_nodup {inputs gates outputs profileWidth : Nat} (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : (terminalBoundaryPorts program records).Nodup",
      "terminalBoundaryPorts_ordered": "theorem terminalBoundaryPorts_ordered {inputs gates outputs profileWidth : Nat} (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : (terminalBoundaryPorts program records).Pairwise (fun left right => left.orderCode ≤ right.orderCode)"
    },
    "heads": [
      "TerminalSupportWire",
      "allTerminalSupportWires",
      "mem_allTerminalSupportWires",
      "Source.terminalSupportWire?",
      "Program.terminalGateSources",
      "Program.terminalGateUsesWire",
      "terminalGateSelected",
      "terminalWireExternal",
      "terminalBoundaryWire",
      "terminalGateHasExternalConsumer",
      "terminalGateIsGlobalOutput",
      "terminalGateIsGlobalOutput_eq_true_iff",
      "terminalInterfaceGate",
      "terminalGateSelected_eq_true_iff",
      "terminalWireExternal_eq_true_iff",
      "terminalBoundaryWire_eq_true_iff",
      "terminalGateHasExternalConsumer_eq_true_iff",
      "terminalInterfaceGate_eq_true_iff",
      "TerminalSupportWire.orderCode",
      "TerminalSupportWire.orderCode_injective",
      "allTerminalSupportWires_strictOrder",
      "Source.terminalWireOccurrences",
      "Source.mem_terminalWireOccurrences_iff",
      "Source.terminalWireOccurrences_length",
      "terminalSourceWireOccurrences",
      "terminalSourceWireOccurrences_length",
      "terminalBoundaryWire_mem_sourceOccurrences",
      "terminalBoundaryPortsSourceDriven",
      "terminalBoundaryPortsSourceDriven_eq_reference",
      "terminalBoundaryPortsSourceDriven_length",
      "terminalBoundaryPortsSourceDriven_nodup",
      "terminalBoundaryPortsSourceDriven_ordered",
      "terminalBoundaryPorts",
      "terminalBoundaryPorts_reference",
      "terminalBoundaryPorts_length",
      "terminalBoundaryPorts_nodup",
      "terminalBoundaryPorts_ordered",
      "terminalInterfacePorts",
      "mem_terminalBoundaryPorts_iff",
      "mem_terminalInterfacePorts_iff",
      "TerminalPhysicalCompletedSupport",
      "completeTerminalPhysicalSupport",
      "TerminalPhysicalCompletedSupport.SourceAccounted",
      "TerminalPhysicalCompletedSupport.Compatible",
      "completeTerminalPhysicalSupport_incoming_complete",
      "completeTerminalPhysicalSupport_outgoing_complete",
      "completeTerminalPhysicalSupport_compatible",
      "completeSaturatedTerminalPhysicalSupport",
      "completeSaturatedTerminalPhysicalSupport_records",
      "completeSaturatedTerminalPhysicalSupport_compatible"
    ]
  }
];

const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = value => stripLeanCommentsAndStrings0(value).replace(/\s+/gu,' ').trim();
const privateHeads0 = source => [...stripLeanCommentsAndStrings0(source).matchAll(
  /^[ \t]*private[ \t]+(def|theorem|inductive|structure|abbrev)[ \t]+([^\s({:]+)/gmu)]
  .map(match => ({kind:match[1], name:match[2], index:match.index}));
function block0(source,name) {
  const stripped=stripLeanCommentsAndStrings0(source);
  const boundaries=[...stripped.matchAll(/^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*(?:(?:def|theorem|inductive|structure|abbrev)[ \t]+([^\s({:]+)|variable\b|omit\b|include\b|namespace\b|end\b)/gmu)];
  const index=boundaries.findIndex(item=>item[1]===name);
  return index<0?'':compact0(source.slice(boundaries[index].index,boundaries[index+1]?.index??source.length));
}
function signature0(block) {
  let depth=0, pendingLets=0;
  for(let index=0;index<block.length-1;index++){
    if('({['.includes(block[index]))depth++;
    else if(')}]'.includes(block[index]))depth--;
    if(depth!==0)continue;
    // A let assignment in the theorem type is not its proof separator.
    if(block.startsWith('let ',index) &&
        (index===0 || !/[\p{L}\p{N}_'.]/u.test(block[index-1])))pendingLets++;
    if(block.slice(index,index+2)===':='){
      if(pendingLets>0){pendingLets--;index++;continue;}
      return block.slice(0,index).trim();
    }
  }
  return '';
}
const physicalSpec = SPECS.find(spec => spec.kind === 'physical');
const canonicalSpec = SPECS.find(spec => spec.kind === 'canonical');

function validateSource0(source, spec) {
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  const block = name => block0(source, name);
  const clean = compact0(source);
  const expectedPrivate = spec.kind === 'canonical' ? [
    'def:insertOrdered', 'theorem:insertOrdered_perm', 'theorem:insertOrdered_ordered',
    'def:sort', 'theorem:sort_perm', 'theorem:sort_ordered',
  ] : [
    'def:physicalTerminalAny', 'theorem:physicalTerminalAny_true_iff',
    'def:sourceMatchesTerminalWire', 'theorem:allFin_strictOrder',
    'theorem:sourceOccurrence_flatMap_length', 'theorem:sourceMatchesTerminalWire_self',
    'theorem:gateUsesWire_of_left', 'theorem:gateUsesWire_of_right',
    'theorem:boundaryWire_of_selected_source', 'theorem:sourceAccounted',
  ];
  require0(JSON.stringify(privateHeads0(source).map(head => head.kind + ':' + head.name))
    === JSON.stringify(expectedPrivate), 'private-interface');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|callerCertificate|suppliedBoundary|suppliedOrder|implemented_by|csimp)\b/u.test(clean),
    'shortcut-or-certificate');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]))
    === JSON.stringify(spec.imports), 'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head => head.name))
    === JSON.stringify(spec.heads), 'public-interface');
  for (const [name, signature] of Object.entries(spec.signatures))
    require0(signature0(block(name)) === signature, 'signature:' + name);
  if (spec.kind === 'canonical') {
    require0(block('unique') ===
      'def unique : List alpha → List alpha | [] => [] | head :: tail => let rest := unique tail if head ∈ rest then rest else head :: rest',
      'computed-unique');
    require0(block('insertOrdered') ===
      'private def insertOrdered (key : alpha → Nat) (item : alpha) : List alpha → List alpha | [] => [item] | head :: tail => if key item ≤ key head then item :: head :: tail else head :: insertOrdered key item tail',
      'computed-insert-order');
    require0(block('sort') ===
      'private def sort (key : alpha → Nat) : List alpha → List alpha | [] => [] | head :: tail => insertOrdered key head (sort key tail)',
      'structural-source-sort');
    require0(block('canonical').endsWith('sort key (unique items)'),
      'computed-canonical-order');
    require0(!/\b(?:allFin|allTerminalSupportWires|allSubsets|referenceMinimum)\b|List\.range/u.test(clean),
      'no-ambient-enumeration');
    require0(block('canonical_eq_reference').includes('ordered_eq_of_mem key injective'),
      'exact-canonical-reference');
  } else {
    require0(block('TerminalSupportWire.orderCode').endsWith(
      '| .input index => index.val | .gate index => inputs + index.val'), 'coordinate-order');
    require0(block('Source.terminalWireOccurrences').endsWith(
      '| .constant _ => [] | .input index => [.input index] | .gate index => [.gate index]'),
      'source-occurrence-locality');
    require0(block('terminalSourceWireOccurrences').endsWith(
      '(allFin gates).flatMap fun consumer => (program.terminalGateSources consumer).1.terminalWireOccurrences ++ (program.terminalGateSources consumer).2.terminalWireOccurrences'),
      'actual-gate-source-occurrences');
    require0(block('terminalBoundaryWire_mem_sourceOccurrences').includes(
      '(terminalBoundaryWire_eq_true_iff program records wire).mp crossing')
      && block('terminalBoundaryWire_mem_sourceOccurrences').includes('Source.mem_terminalWireOccurrences_iff'),
      'source-derived-crossing-completeness');
    require0(block('terminalBoundaryPortsSourceDriven').endsWith(
      'SourceListOrder.canonical TerminalSupportWire.orderCode ((terminalSourceWireOccurrences program).filter (terminalBoundaryWire program records))'),
      'source-only-boundary');
    require0(block('terminalBoundaryPorts').endsWith(
      'terminalBoundaryPortsSourceDriven program records'), 'active-source-only-extractor');
    require0(block('terminalBoundaryPortsSourceDriven_eq_reference').includes(
      'SourceListOrder.canonical_eq_reference TerminalSupportWire.orderCode')
      && block('terminalBoundaryPortsSourceDriven_eq_reference').includes(
        'terminalBoundaryWire_mem_sourceOccurrences program records wire checked.2'),
      'exact-ordered-reference-proof');
    require0(block('terminalBoundaryPorts_reference').endsWith(
      'terminalBoundaryPortsSourceDriven_eq_reference program records'), 'active-reference-linkage');
    require0(block('terminalSourceWireOccurrences_length').includes(
      'sourceOccurrence_flatMap_length (allFin gates)')
      && block('terminalBoundaryPortsSourceDriven_length').includes(
        'SourceListOrder.canonical_length_le _ _')
      && block('terminalBoundaryPorts_length').endsWith(
        'terminalBoundaryPortsSourceDriven_length program records'), 'physical-occurrence-accounting');
  }
  return [...new Set(failures)];
}

function mutateBlock0(source, name, old, replacement) {
  const heads = [...explicitLeanDeclarationHeads0(source), ...privateHeads0(source)]
    .sort((left, right) => left.index - right.index);
  const at = heads.findIndex(head => head.name === name);
  assert.ok(at >= 0, name);
  const begin = heads[at].index;
  const end = heads[at + 1]?.index ?? source.length;
  const block = source.slice(begin, end);
  assert.ok(block.includes(old), name + ': effective mutation');
  const changed = source.slice(0, begin) + block.replace(old, replacement) + source.slice(end);
  assert.notEqual(changed, source);
  return changed;
}

async function rejectMutations0(spec, mutations) {
  const source = await text0(spec.path);
  for (const [name, old, replacement, label] of mutations) {
    const changed = mutateBlock0(source, name, old, replacement);
    assert.ok(validateSource0(changed, spec).includes(label), name + ': ' + label);
  }
}

test('M260 source parser preserves default binders and complete let-bound targets', () => {
  const target = 'theorem probe (defaulted : Nat := 0) : let witness := defaulted; witness = defaulted';
  assert.equal(signature0(target + ' := by rfl'), target);
  assert.equal(signature0('theorem incomplete : let witness := 0'), '');
  assert.equal(block0('def first : Nat := 0\nomit [DecidableEq alpha] in\nprivate def next : Nat := 1', 'first'),
    'def first : Nat := 0');
});

test('M260 closes canonical-list and source-derived physical interfaces', async () => {
  for (const spec of SPECS) assert.deepEqual(validateSource0(await text0(spec.path), spec), []);
});

test('M260 root, reviewed-name producers and exact axiom transcript agree', async () => {
  const [audit, inventory, physical] = await Promise.all([
    text0(AUDIT), text0('lean-audit/PNPTheoremInventory.lean'), text0(SOURCE)]);
  for (const name of NAMES) {
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item => item === name).length, 1, name);
    assert.equal(inventory.split(String.fromCharCode(96) + name + ',').length - 1, 1, name);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]), ['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match => match[1]), NAMES);
  assert.match(physical, /^import PNP\.NANDSourceListOrder\s*$/mu);
});

test('M260 rejects duplicate, reversed and ambient-enumerating source canonicalization', async () => {
  await rejectMutations0(canonicalSpec, [
    ['unique', 'if head ∈ rest then rest else head :: rest',
      'head :: rest', 'computed-unique'],
    ['insertOrdered', 'key item ≤ key head', 'key head ≤ key item', 'computed-insert-order'],
    ['sort', 'insertOrdered key head (sort key tail)', 'tail', 'structural-source-sort'],
    ['canonical', 'sort key (unique items)', 'unique items', 'computed-canonical-order'],
  ]);
  const source = await text0(canonicalSpec.path);
  assert.ok(validateSource0(source + '\ndef hidden := List.range 1000000000\n', canonicalSpec)
    .includes('no-ambient-enumeration'));
});

test('M260 rejects omitted sources, wrong wire coordinates and ambient input scans', async () => {
  await rejectMutations0(physicalSpec, [
    ['TerminalSupportWire.orderCode', 'inputs + index.val', 'index.val', 'coordinate-order'],
    ['Source.terminalWireOccurrences', '| .input index => [.input index]',
      '| .input _ => []', 'source-occurrence-locality'],
    ['terminalSourceWireOccurrences', '(allFin gates).flatMap', '(allFin inputs).flatMap',
      'actual-gate-source-occurrences'],
    ['terminalSourceWireOccurrences', '(program.terminalGateSources consumer).2.terminalWireOccurrences',
      '[]', 'actual-gate-source-occurrences'],
    ['terminalBoundaryPortsSourceDriven', 'terminalBoundaryWire program records',
      'fun _ => false', 'source-only-boundary'],
    ['terminalBoundaryPorts', 'terminalBoundaryPortsSourceDriven program records',
      '(allTerminalSupportWires inputs gates).filter (terminalBoundaryWire program records)',
      'active-source-only-extractor'],
  ]);
});

test('M260 rejects supplied completeness, unordered equivalence and unsupported bounds', async () => {
  await rejectMutations0(physicalSpec, [
    ['terminalBoundaryPortsSourceDriven_eq_reference', 'terminalBoundaryPortsSourceDriven program records =',
      '(terminalBoundaryPortsSourceDriven program records).length =',
      'signature:terminalBoundaryPortsSourceDriven_eq_reference'],
    ['terminalBoundaryPortsSourceDriven_eq_reference',
      'SourceListOrder.canonical_eq_reference TerminalSupportWire.orderCode',
      'callerCertificate', 'exact-ordered-reference-proof'],
    ['terminalBoundaryPorts_reference', 'terminalBoundaryPortsSourceDriven_eq_reference program records',
      'callerCertificate', 'active-reference-linkage'],
    ['terminalBoundaryPorts_length', '≤ 2 * gates', '≤ 2 * inputs',
      'signature:terminalBoundaryPorts_length'],
    ['terminalBoundaryPortsSourceDriven_length', 'SourceListOrder.canonical_length_le _ _',
      'callerCertificate', 'physical-occurrence-accounting'],
  ]);
});

test('M260 rejects assumptions, hidden declarations and unchecked implementation overrides', async () => {
  for (const spec of SPECS) {
    const source = await text0(spec.path);
    assert.ok(validateSource0(source + '\naxiom hidden : False\n', spec).includes('assumption'));
    assert.ok(validateSource0(source + '\nexample : True := by trivial\n', spec).includes('unaudited-form'));
    assert.ok(validateSource0(source + '\nprivate def hidden := 0\n', spec).includes('private-interface'));
    assert.ok(validateSource0(source + '\nattribute [implemented_by hidden] canonical\n', spec)
      .includes('shortcut-or-certificate'));
    assert.ok(validateSource0(source + '\ndef hidden := suppliedBoundary\n', spec)
      .includes('shortcut-or-certificate'));
  }
});

test('M260 runtime regressions guard exact order and large unused input dimensions', async () => {
  // Preserve the inherited fixture assertions while repairing the source sort.
  // Native execution cannot substitute for kernel-checked regression proofs.
  const inheritedFixtures = [
    "lean-regression/PNPArbitrarySupportSplice.lean",
    "lean-regression/PNPResidualTerminalBN2SquareLegitimacy.lean",
    "lean-regression/PNPResidualTerminalBudgetEnvelopeResolver.lean",
    "lean-regression/PNPResidualTerminalBudgetNoLowerLedger.lean",
    "lean-regression/PNPResidualTerminalBudgetZeroSlackSidecar.lean",
    "lean-regression/PNPResidualTerminalFiniteSaturatePositive.lean",
    "lean-regression/PNPResidualTerminalFourCornerCarrier.lean",
    "lean-regression/PNPResidualTerminalFourCornerOptimumCoherence.lean",
    "lean-regression/PNPResidualTerminalFourCornerOptimumCompatibility.lean",
    "lean-regression/PNPResidualTerminalFourCornerSideTightCompletion.lean",
    "lean-regression/PNPResidualTerminalFourCornerTightBasisMaximum.lean",
    "lean-regression/PNPResidualTerminalFrontierPushout.lean",
    "lean-regression/PNPResidualTerminalGainProfileFirewall.lean",
    "lean-regression/PNPResidualTerminalGovernedSupportCompletion.lean",
    "lean-regression/PNPResidualTerminalHResolveSupportResolver.lean",
    "lean-regression/PNPResidualTerminalInterfaceExposureRouting.lean",
    "lean-regression/PNPResidualTerminalPacketBudgetNoLowerComposition.lean",
    "lean-regression/PNPResidualTerminalPhysicalChargeLedger.lean",
    "lean-regression/PNPResidualTerminalPhysicalGain.lean",
    "lean-regression/PNPResidualTerminalPhysicalOwnership.lean",
    "lean-regression/PNPResidualTerminalPhysicalSupportCompletion.lean",
    "lean-regression/PNPResidualTerminalSaturatedSupportContext.lean",
    "lean-regression/PNPResidualTerminalSaturationCostBalance.lean",
    "lean-regression/PNPResidualTerminalSaturationPositivityFirewall.lean",
    "lean-regression/PNPResidualTerminalSaturationTraceFidelity.lean",
    "lean-regression/PNPWireCarrier.lean"
];
  const safeFixture = source => !/\b(?:axiom|sorry|admit|native_decide|allowUnsafeReducibility)\b|\+\s*native\b/u
    .test(stripLeanCommentsAndStrings0(source));
  for (const file of inheritedFixtures) {
    const fixture = await text0(file);
    assert.ok(safeFixture(fixture), file + ': trusted fixture authority');
    assert.match(fixture, /by decide/u, file + ': ordinary checked fixture proof');
    assert.equal(safeFixture(fixture.replace('by decide', 'by decide +native')), false,
      file + ': rejects native authority mutation');
  }
  const source = await text0(REGRESSION);
  assert.match(source, /^import PNP\s*$/mu);
  for (const name of [
    'empty-dimensions', 'empty-selected-support', 'primary-source-order', 'duplicate-source',
    'constant-locality', 'mixed-input-gate-ports', 'reversed-gate-source-order',
    'nonconsecutive-support', 'duplicate-unordered-records', 'selected-producer-is-internal',
    'whole-support-primary-order', 'billion-unused-inputs-empty-program',
    'billion-inputs-sparse-primary-ports', 'billion-inputs-mixed-ports',
    'billion-inputs-whole-support',
  ]) assert.ok(source.includes('"' + name + '"'), name);
  assert.ok(source.includes('inputs > 4 || gates > 3'));
  assert.ok(source.includes('if gates > 2 then'));
  const start = source.indexOf('def checkWide ');
  const end = source.indexOf('\nexample ', start);
  assert.ok(start >= 0 && end > start);
  assert.doesNotMatch(source.slice(start, end), /allTerminalSupportWires|allFin|List\.range|2 \^/u);
  assert.match(source, /M260_SOURCE_BOUNDED_PHYSICAL_BOUNDARY_RUNTIME_GREEN/u);
  assert.doesNotMatch(source, /#eval!|\bnative_decide\b|\+\s*native\b/u);
  for (const marker of ['kernel-source-order', 'kernel-duplicate-order',
    'kernel-wide-boundary-order', 'kernel-dependent-boundary-width'])
    assert.ok(source.includes(marker), marker);
});

test('M260 durable workflow audits the compiled root and bounded runtime', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  for (const token of [
    'Audit source-bounded physical boundary',
    'node --test audits/lean-source-bounded-physical-boundary0.test.mjs',
    'lake env lean -DwarningAsError=true ' + AUDIT,
    'lake env lean -DwarningAsError=true ' + REGRESSION,
  ]) assert.ok(workflow.includes(token), token);
  for (const name of NAMES) assert.ok(workflow.includes('"' + name + '"'), name);
  for (const pattern of ['audits/lean-*.test.mjs', 'docs/lean_*.md'])
    assert.equal(workflow.split("      - '" + pattern + "'").length - 1, 2);
});

const M260_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-13-260';
const M260_MILESTONE = 'source-bounded-physical-boundary';
const M260_HASHES = Object.freeze({
  "PNP.DirectWire.SourceListOrder.mem_unique": "7a49dd95817c0455891c81ec6ed64a3c2a85b5781329a7679db339569689ed68",
  "PNP.DirectWire.SourceListOrder.unique_nodup": "fdb6af13cee2da15e3a1bf9db99b9e84632ea80f4d365237d4afc0eaf13c8505",
  "PNP.DirectWire.SourceListOrder.unique_length_le": "b2aeba847545c7ed287ff77c5c6333cf7d02493e92f4ac7aeda9364ac8e86260",
  "PNP.DirectWire.SourceListOrder.mem_canonical": "dca5768a25f190fc4611cb1e2054e6141a42e4f0e226eb0d7eceaba7f6629c85",
  "PNP.DirectWire.SourceListOrder.canonical_nodup": "efa8dd491c242ec16a53d9e5bd3d04b51848b13cc07975f9a4ba330bd7f21586",
  "PNP.DirectWire.SourceListOrder.canonical_length_le": "f84d3b5d18c0db478a3823e93af8fa9f6e4e5f29882d12965770cf7ae356f2ad",
  "PNP.DirectWire.SourceListOrder.canonical_ordered": "69011b5c2c4adac5ef23fcb94e92f461ad000e1caebe690499e4d85793d80f1e",
  "PNP.DirectWire.SourceListOrder.ordered_eq_of_mem": "030006421cdf64692885e8d0413aca2328d1c0abe95581d510690e07f498138c",
  "PNP.DirectWire.SourceListOrder.canonical_eq_reference": "0f99873639e837a33d8fd74e57f65fc63f8250e4cf40652588b6d54a8daf8a33",
  "PNP.DirectWire.TerminalSupportWire.orderCode_injective": "c14e48f0535f611e3de7a1bbd5af9f321918215e5da69823c3c986360231b4a2",
  "PNP.DirectWire.allTerminalSupportWires_strictOrder": "75ca4fb846a495969bed16586007970e011e9c5d3ff81d59243e82acf0c02c3c",
  "PNP.DirectWire.Source.mem_terminalWireOccurrences_iff": "f31f5bdd51cc3289dc4cd9eac239a507cb73353f3add38f60ae741e1f676a3e5",
  "PNP.DirectWire.Source.terminalWireOccurrences_length": "4480ea986948d9dc413b1b5681dc0f03a32f2537bf3404fb42106ed271bef8b4",
  "PNP.DirectWire.terminalSourceWireOccurrences_length": "5d9dcd82ddcf9b34ac1fcf7032b8ec57e1a79dac9eef18cbbf8eabd267a83169",
  "PNP.DirectWire.terminalBoundaryWire_mem_sourceOccurrences": "90451eea87b5af9e66066b0508f3933a7dcccf79c130391e2be031ad8337df68",
  "PNP.DirectWire.terminalBoundaryPortsSourceDriven_eq_reference": "65d0debd44a86f70d7febae2421a6526bd5c56eb7a5b64cc0775b6af76c07930",
  "PNP.DirectWire.terminalBoundaryPortsSourceDriven_length": "7ec44311f450db96fe5a40e401c6650f4e6bec4df250ab0e1d3e613b22bf3e80",
  "PNP.DirectWire.terminalBoundaryPortsSourceDriven_nodup": "7e5fa7bbee7ccfaaf40761dafdcc3dac3d64b12c0af6ad1b24a483a94b7a7044",
  "PNP.DirectWire.terminalBoundaryPortsSourceDriven_ordered": "547ca82d8d21213fe160f9f3284932a60032de7cf82d6dc0d6adf33cff17ea77",
  "PNP.DirectWire.terminalBoundaryPorts_reference": "6833f172589ae02ed7b73f6853916e7101f12ed7adfe923272f648221736fe4a",
  "PNP.DirectWire.terminalBoundaryPorts_length": "ba62c4628cd68cb6bbbc0abb968f00d067f305738395d8e13378aaceabad89b1",
  "PNP.DirectWire.terminalBoundaryPorts_nodup": "9d59decf9fe49a6f8553d10b327e375c3f91c53879545748a5bdba607a146ee6",
  "PNP.DirectWire.terminalBoundaryPorts_ordered": "c38618e05bb7e55cc5a952be125f3d089f7057336d3b0f981c5648e8c5eacd58"
});
const M260_STATUS_FIELDS = Object.freeze({
  "leanSourceBoundedPhysicalBoundaryFormalized": true,
  "leanSourceBoundedPhysicalBoundaryAxiomAuditPassed": true,
  "leanSourceBoundedPhysicalBoundaryAuditedDeclarationCount": 23,
  "leanSourceBoundedPhysicalBoundaryUniqueMembershipTheorem": "PNP.DirectWire.SourceListOrder.mem_unique",
  "leanSourceBoundedPhysicalBoundaryUniqueNoDuplicatesTheorem": "PNP.DirectWire.SourceListOrder.unique_nodup",
  "leanSourceBoundedPhysicalBoundaryUniqueLengthBoundTheorem": "PNP.DirectWire.SourceListOrder.unique_length_le",
  "leanSourceBoundedPhysicalBoundaryCanonicalMembershipTheorem": "PNP.DirectWire.SourceListOrder.mem_canonical",
  "leanSourceBoundedPhysicalBoundaryCanonicalNoDuplicatesTheorem": "PNP.DirectWire.SourceListOrder.canonical_nodup",
  "leanSourceBoundedPhysicalBoundaryCanonicalLengthBoundTheorem": "PNP.DirectWire.SourceListOrder.canonical_length_le",
  "leanSourceBoundedPhysicalBoundaryCanonicalOrderTheorem": "PNP.DirectWire.SourceListOrder.canonical_ordered",
  "leanSourceBoundedPhysicalBoundaryOrderedReferenceUniquenessTheorem": "PNP.DirectWire.SourceListOrder.ordered_eq_of_mem",
  "leanSourceBoundedPhysicalBoundaryCanonicalReferenceTheorem": "PNP.DirectWire.SourceListOrder.canonical_eq_reference",
  "leanSourceBoundedPhysicalBoundaryCoordinateInjectivityTheorem": "PNP.DirectWire.TerminalSupportWire.orderCode_injective",
  "leanSourceBoundedPhysicalBoundaryAmbientReferenceOrderTheorem": "PNP.DirectWire.allTerminalSupportWires_strictOrder",
  "leanSourceBoundedPhysicalBoundarySourceOccurrenceMembershipTheorem": "PNP.DirectWire.Source.mem_terminalWireOccurrences_iff",
  "leanSourceBoundedPhysicalBoundarySourceOccurrenceBoundTheorem": "PNP.DirectWire.Source.terminalWireOccurrences_length",
  "leanSourceBoundedPhysicalBoundaryProgramOccurrenceBoundTheorem": "PNP.DirectWire.terminalSourceWireOccurrences_length",
  "leanSourceBoundedPhysicalBoundaryCrossingSourceCompletenessTheorem": "PNP.DirectWire.terminalBoundaryWire_mem_sourceOccurrences",
  "leanSourceBoundedPhysicalBoundarySourceDrivenReferenceTheorem": "PNP.DirectWire.terminalBoundaryPortsSourceDriven_eq_reference",
  "leanSourceBoundedPhysicalBoundarySourceDrivenLengthBoundTheorem": "PNP.DirectWire.terminalBoundaryPortsSourceDriven_length",
  "leanSourceBoundedPhysicalBoundarySourceDrivenNoDuplicatesTheorem": "PNP.DirectWire.terminalBoundaryPortsSourceDriven_nodup",
  "leanSourceBoundedPhysicalBoundarySourceDrivenOrderTheorem": "PNP.DirectWire.terminalBoundaryPortsSourceDriven_ordered",
  "leanSourceBoundedPhysicalBoundaryActiveReferenceTheorem": "PNP.DirectWire.terminalBoundaryPorts_reference",
  "leanSourceBoundedPhysicalBoundaryActiveLengthBoundTheorem": "PNP.DirectWire.terminalBoundaryPorts_length",
  "leanSourceBoundedPhysicalBoundaryActiveNoDuplicatesTheorem": "PNP.DirectWire.terminalBoundaryPorts_nodup",
  "leanSourceBoundedPhysicalBoundaryActiveOrderTheorem": "PNP.DirectWire.terminalBoundaryPorts_ordered",
  "leanSourceBoundedPhysicalBoundaryActualGateSourceOccurrencesDerived": true,
  "leanSourceBoundedPhysicalBoundaryExactOrderedReferenceEqualityProved": true,
  "leanSourceBoundedPhysicalBoundaryOccurrenceAndBoundaryLengthBoundsProved": true,
  "leanSourceBoundedPhysicalBoundaryDuplicateFreeCanonicalOrderProved": true,
  "leanSourceBoundedPhysicalBoundaryActiveExtractorUsesSourceOccurrences": true,
  "leanSourceBoundedPhysicalBoundaryExistingPhysicalInterfacesPreserved": true,
  "leanSourceBoundedPhysicalBoundaryUnusedInputEnumerationRequired": false,
  "leanSourceBoundedPhysicalBoundaryCallerSuppliedBoundaryRequired": false,
  "leanSourceBoundedPhysicalBoundaryCallerSuppliedCompletenessRequired": false,
  "leanSourceBoundedPhysicalBoundaryRuntimeExecutionIsProofAuthority": false,
  "leanSourceBoundedPhysicalBoundaryFullManuscriptCarrierProved": false,
  "leanSourceBoundedPhysicalBoundaryCompleteObligationCalculusProved": false,
  "leanSourceBoundedPhysicalBoundaryCompletePackageEProved": false,
  "leanSourceBoundedPhysicalBoundaryGlobalMinimalityProved": false,
  "leanSourceBoundedPhysicalBoundaryPolynomialRuntimeProved": false,
  "leanSourceBoundedPhysicalBoundaryScope": "all-finite-program-dimensions-actual-gate-source-derived-physical-crossings-exact-ordered-ambient-reference-equality-duplicate-free-canonical-order-twice-gate-count-occurrence-and-boundary-bounds-active-extraction-no-unused-input-scan-or-total-encoded-polynomial-runtime"
});
const M260_AXIOMS = Object.freeze({
  "PNP.DirectWire.SourceListOrder.mem_unique": [
    "propext"
  ],
  "PNP.DirectWire.SourceListOrder.unique_nodup": [
    "propext"
  ],
  "PNP.DirectWire.SourceListOrder.unique_length_le": [
    "propext"
  ],
  "PNP.DirectWire.SourceListOrder.mem_canonical": [
    "propext"
  ],
  "PNP.DirectWire.SourceListOrder.canonical_nodup": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.SourceListOrder.canonical_length_le": [
    "propext"
  ],
  "PNP.DirectWire.SourceListOrder.canonical_ordered": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.SourceListOrder.ordered_eq_of_mem": [
    "propext"
  ],
  "PNP.DirectWire.SourceListOrder.canonical_eq_reference": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.TerminalSupportWire.orderCode_injective": [
    "propext"
  ],
  "PNP.DirectWire.allTerminalSupportWires_strictOrder": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.Source.mem_terminalWireOccurrences_iff": [
    "propext"
  ],
  "PNP.DirectWire.Source.terminalWireOccurrences_length": [],
  "PNP.DirectWire.terminalSourceWireOccurrences_length": [
    "propext"
  ],
  "PNP.DirectWire.terminalBoundaryWire_mem_sourceOccurrences": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalBoundaryPortsSourceDriven_eq_reference": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalBoundaryPortsSourceDriven_length": [
    "propext"
  ],
  "PNP.DirectWire.terminalBoundaryPortsSourceDriven_nodup": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalBoundaryPortsSourceDriven_ordered": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalBoundaryPorts_reference": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalBoundaryPorts_length": [
    "propext"
  ],
  "PNP.DirectWire.terminalBoundaryPorts_nodup": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalBoundaryPorts_ordered": [
    "Quot.sound",
    "propext"
  ]
});

const M260_MODULES = Object.freeze({
  "PNP.DirectWire.SourceListOrder.mem_unique": "PNP.NANDSourceListOrder",
  "PNP.DirectWire.SourceListOrder.unique_nodup": "PNP.NANDSourceListOrder",
  "PNP.DirectWire.SourceListOrder.unique_length_le": "PNP.NANDSourceListOrder",
  "PNP.DirectWire.SourceListOrder.mem_canonical": "PNP.NANDSourceListOrder",
  "PNP.DirectWire.SourceListOrder.canonical_nodup": "PNP.NANDSourceListOrder",
  "PNP.DirectWire.SourceListOrder.canonical_length_le": "PNP.NANDSourceListOrder",
  "PNP.DirectWire.SourceListOrder.canonical_ordered": "PNP.NANDSourceListOrder",
  "PNP.DirectWire.SourceListOrder.ordered_eq_of_mem": "PNP.NANDSourceListOrder",
  "PNP.DirectWire.SourceListOrder.canonical_eq_reference": "PNP.NANDSourceListOrder",
  "PNP.DirectWire.TerminalSupportWire.orderCode_injective": "PNP.ResidualTerminalPhysicalSupportCompletion",
  "PNP.DirectWire.allTerminalSupportWires_strictOrder": "PNP.ResidualTerminalPhysicalSupportCompletion",
  "PNP.DirectWire.Source.mem_terminalWireOccurrences_iff": "PNP.ResidualTerminalPhysicalSupportCompletion",
  "PNP.DirectWire.Source.terminalWireOccurrences_length": "PNP.ResidualTerminalPhysicalSupportCompletion",
  "PNP.DirectWire.terminalSourceWireOccurrences_length": "PNP.ResidualTerminalPhysicalSupportCompletion",
  "PNP.DirectWire.terminalBoundaryWire_mem_sourceOccurrences": "PNP.ResidualTerminalPhysicalSupportCompletion",
  "PNP.DirectWire.terminalBoundaryPortsSourceDriven_eq_reference": "PNP.ResidualTerminalPhysicalSupportCompletion",
  "PNP.DirectWire.terminalBoundaryPortsSourceDriven_length": "PNP.ResidualTerminalPhysicalSupportCompletion",
  "PNP.DirectWire.terminalBoundaryPortsSourceDriven_nodup": "PNP.ResidualTerminalPhysicalSupportCompletion",
  "PNP.DirectWire.terminalBoundaryPortsSourceDriven_ordered": "PNP.ResidualTerminalPhysicalSupportCompletion",
  "PNP.DirectWire.terminalBoundaryPorts_reference": "PNP.ResidualTerminalPhysicalSupportCompletion",
  "PNP.DirectWire.terminalBoundaryPorts_length": "PNP.ResidualTerminalPhysicalSupportCompletion",
  "PNP.DirectWire.terminalBoundaryPorts_nodup": "PNP.ResidualTerminalPhysicalSupportCompletion",
  "PNP.DirectWire.terminalBoundaryPorts_ordered": "PNP.ResidualTerminalPhysicalSupportCompletion"
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

test('M260 compiled source-bounded physical-boundary interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M260_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M260_COORDINATE)
    assert.equal(map.coordinate, M260_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M260_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, M260_MODULES[name], name);
      assert.deepEqual(declaration.axioms, M260_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M260_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M260_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M260_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "structural size bounds, not total encoded-input-size polynomial execution theorems",
  "only as a theorem-side specification, never the active boundary implementation",
  "No caller-supplied boundary or completeness certificate is introduced",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M260 publication rejects weakened, supplied, assumption-backed and widened complete-calculus substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M260_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M260_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = 'PNP.DirectWire.terminalBoundaryPorts_reference';
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M260_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M260_MILESTONE
    ? {...row, nonClaim:'The boundary length bound proves total encoded-input-size polynomial PCCMin and unconditional ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M260 adds source-bounded physical-boundary coverage without complete-calculus, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M260_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "unused-primary-input enumeration dependency",
  "without a supplied boundary or completeness certificate",
  "structural size bounds, not a total encoded-input-size polynomial execution theorem",
  "No fixed load-bearing checkpoint changes state",
  "40% proof estimate"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M260_COORDINATE) return;
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

test('M260 current summaries distinguish structural boundary bounds from complete-calculus and global completion and retain metrics and separate-site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_source_bounded_physical_boundary.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "Reference equality preserves existing physical extraction and support interfaces.",
  "The ambient enumeration remains a theorem-side reference, not the active extractor.",
  "These are structural size bounds, not total polynomial execution theorems.",
  "Runtime execution is test evidence, not theorem authority.",
  "Publication decision: defer a separate PNPLabs cycle for M260."
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-13-source-bounded-physical-boundary.md'));
  assert.match(plan, /Publication decision: defer a separate PNPLabs cycle for M260\./u);
  if (progress.asOfCoordinate !== M260_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_source_bounded_physical_boundary.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});

const M260_INHERITED_AXIOM_REVIEW = Object.freeze({
  "PNP.DirectWire.TerminalFourCornerCarrier.boundaryDisposition?_eq_some_iff": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalFourCornerCarrier",
    "kernelTypeSha256": "a17a6f8030c70a14adb2df79307260e0a6604d74971edeb56d0b120fa7ea8fee"
  },
  "PNP.DirectWire.TerminalFourCornerCarrier.interfaceDisposition?_eq_some_iff": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalFourCornerCarrier",
    "kernelTypeSha256": "4280ddc44a0c8bd9cb3286891884e90420fcec78a4c33e53ac76db5aef07020a"
  },
  "PNP.DirectWire.TerminalFourCornerCarrier.interface_internalized": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalFourCornerCarrier",
    "kernelTypeSha256": "baa7cb59491626b993a2f8fd7009685a934df1c830ac20fb7ad28f8302c785e8"
  },
  "PNP.DirectWire.TerminalFourCornerCarrier.interface_nodup": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalFourCornerCarrier",
    "kernelTypeSha256": "712283c4673524aa982002f212e6ac6422678d26f87efef00f13514d9bc81deb"
  },
  "PNP.DirectWire.TerminalFourCornerCarrier.meet_profile_transport": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalFourCornerCarrier",
    "kernelTypeSha256": "401a598c9f5d9f9a5db940695710f9d44df9a2317cf498b08d9b95a59af08e10"
  },
  "PNP.DirectWire.TerminalFourCornerCarrier.profile_nodup": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalFourCornerCarrier",
    "kernelTypeSha256": "ef0d11e47a02a1f40941ab31106f6e596879a68310f4997770b47728aad16e71"
  },
  "PNP.DirectWire.TerminalGovernedCompletedSupport.frontier_boundary": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalGovernedSupportCompletion",
    "kernelTypeSha256": "e340ac8efd05f6760b8c8f18e88a5e80c53c81599e3876913898c167f2308b13"
  },
  "PNP.DirectWire.TerminalGovernedCompletedSupport.frontier_interface": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalGovernedSupportCompletion",
    "kernelTypeSha256": "d4415e5f4b90980b4170664d526e3c51eec5c6c9013e814e9f4529451fc23792"
  },
  "PNP.DirectWire.TerminalGovernedFrontier.project_pushout": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalProjectionSquare",
    "kernelTypeSha256": "1e27fb54a4b5c0f3f02bf26d3cd38b89596da3aa57312b928c817bc36a599c90"
  },
  "PNP.DirectWire.TerminalSaturatedSupportSquare.forgotten_not_mem_projectedFrontier": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalProjectionSquare",
    "kernelTypeSha256": "c872d6eafff42e0de60e67d52555c203f589a05422392e32f8fa1ef7f7586865"
  },
  "PNP.DirectWire.TerminalSaturatedSupportSquare.mem_projectedFrontier_profiles_iff": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalProjectionSquare",
    "kernelTypeSha256": "facc10a1bb53afa05adaf689dcb650f13eaa85f7b573d7a07578a2aef59e1bbd"
  },
  "PNP.DirectWire.TerminalSaturatedSupportSquare.physically_compatible": {
    "before": [
      "propext"
    ],
    "after": [
      "Quot.sound",
      "propext"
    ],
    "module": "PNP.ResidualTerminalSupportSquareClosure",
    "kernelTypeSha256": "2a19ccf8594f3749b91d263b915e1d2156a90ad2681ca6ed527f124de4b564f3"
  },
  "PNP.DirectWire.TerminalSaturatedSupportSquare.projectedFrontier_boundary": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalProjectionSquare",
    "kernelTypeSha256": "28d9df62f589b2ab8943c4106a692612cc291504a1f3d57b95ee6240f4cf5343"
  },
  "PNP.DirectWire.TerminalSaturatedSupportSquare.projectedFrontier_interface": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalProjectionSquare",
    "kernelTypeSha256": "9a3bb52ded9dfc28a8c1d8c18303ba392f4ddcba000ba9e4fe4e63fd8b372939"
  },
  "PNP.DirectWire.TerminalSaturatedSupportSquare.projectedFrontier_profiles_nodup": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalProjectionSquare",
    "kernelTypeSha256": "dc3922479745fff935163a6cfa0a9664ae2306589197c6bcbd0b24a2c2c86b08"
  },
  "PNP.DirectWire.TerminalSaturatedSupportSquare.projected_meet_profile_iff": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalProjectionSquare",
    "kernelTypeSha256": "9e63a2390bccaf3706b0328f2f867bc4911f383ed779faf94bd921eeae68d52e"
  },
  "PNP.DirectWire.TerminalSaturatedSupportSquare.side_interface_disposition": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalFrontierPushout",
    "kernelTypeSha256": "8c44ddf2248725d3f73ec432fe5ea59ab8c73b9eab920068e3d3f51926e8fd2f"
  },
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_wire_mem": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.NANDWireUnarySupportSearch",
    "kernelTypeSha256": "e5a7155113a150e4aaf7b68426b1e90b908c19d2ef957df26e5b91f0893b8717"
  },
  "PNP.DirectWire.completeSaturatedTerminalPhysicalSupport_compatible": {
    "before": [
      "propext"
    ],
    "after": [
      "Quot.sound",
      "propext"
    ],
    "module": "PNP.ResidualTerminalPhysicalSupportCompletion",
    "kernelTypeSha256": "831f8ce697624f2e413d5da6a56fde592b2157793a1dd1f4f85060154faafc58"
  },
  "PNP.DirectWire.completeSaturatedTerminalPhysicalSupport_records": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalPhysicalSupportCompletion",
    "kernelTypeSha256": "619c37407e969a13746611f68b4169ba34a8cac4e6d8a01d5388808eec58fe91"
  },
  "PNP.DirectWire.completeTerminalPhysicalSupport_compatible": {
    "before": [
      "propext"
    ],
    "after": [
      "Quot.sound",
      "propext"
    ],
    "module": "PNP.ResidualTerminalPhysicalSupportCompletion",
    "kernelTypeSha256": "54f14acec8c40024eb7982e02373e24a80e864b0478a7815105f94362601b1fd"
  },
  "PNP.DirectWire.completeTerminalPhysicalSupport_incoming_complete": {
    "before": [
      "propext"
    ],
    "after": [
      "Quot.sound",
      "propext"
    ],
    "module": "PNP.ResidualTerminalPhysicalSupportCompletion",
    "kernelTypeSha256": "e541fac972a4f9402aab6b47c6aa6164cdf54d5a490beb750a8ddf498719e789"
  },
  "PNP.DirectWire.completeTerminalPhysicalSupport_outgoing_complete": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalPhysicalSupportCompletion",
    "kernelTypeSha256": "5955b959132cd6a3f3bf734ea8f62513554f476a2ee7b46a65ff716e9a328b7a"
  },
  "PNP.DirectWire.mem_terminalBoundaryFrontierPushout_iff": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalFrontierPushout",
    "kernelTypeSha256": "6917c9d5b8c2dd5597ada2d19b520b3f670c1b2d0aff6e036d5e30af88f364a9"
  },
  "PNP.DirectWire.mem_terminalBoundaryPorts_iff": {
    "before": [
      "propext"
    ],
    "after": [
      "Quot.sound",
      "propext"
    ],
    "module": "PNP.ResidualTerminalPhysicalSupportCompletion",
    "kernelTypeSha256": "96d01f7650e0584503501f4278dc196e1b1a2ea658abf237e99978715d942ef0"
  },
  "PNP.DirectWire.mem_terminalInterfaceFrontierPushout_iff": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalFrontierPushout",
    "kernelTypeSha256": "d66f50c4ddb7c57a1d87173e653a7f5e4ed95b5bc3df5a98796f481f364c3cb3"
  },
  "PNP.DirectWire.mem_terminalProjectedGovernedFrontierPushout_profiles_iff": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalProjectionSquare",
    "kernelTypeSha256": "39c9d3b8078740dd0140667219de0c5d66b35bff11f787b8d692e8857ecdaff9"
  },
  "PNP.DirectWire.terminalInterfaceFrontierPushout_nodup": {
    "before": [
      "propext"
    ],
    "after": [
      "propext"
    ],
    "module": "PNP.ResidualTerminalFrontierPushout",
    "kernelTypeSha256": "65e1394f56ba5d990fe995323e9dc178be50bed77eb2d0bb755dd900d33b86f2"
  }
});

test('M260 records the reviewed inherited axiom closures with unchanged theorem types', async () => {
  const {inventory,map} = await compiledSources0();
  assert.equal(Object.keys(M260_INHERITED_AXIOM_REVIEW).length, 28);
  assert.equal(Object.values(M260_INHERITED_AXIOM_REVIEW).filter(row => row.after.includes('Quot.sound')).length, 5);
  for (const [name,expected] of Object.entries(M260_INHERITED_AXIOM_REVIEW)) {
    assert.deepEqual(expected.before, ['propext'], name);
    const candidate = inventory.milestoneCandidates.find(row => row.name === name);
    assert.equal(candidate?.kind, 'theorem', name);
    assert.equal(candidate.module, expected.module, name);
    assert.deepEqual(candidate.axioms, expected.after, name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name,candidate.kernelType), expected.kernelTypeSha256, name);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], expected.kernelTypeSha256, name);
    const declaration = inventory.declarations.find(row => row.name === name);
    assert.deepEqual(declaration?.axioms, expected.after, name);
  }
});
