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

const SOURCE = 'lean/PNP/ResidualIndependentMaterializerCost.lean';
const AUDIT = 'lean-audit/PNPResidualIndependentMaterializerCostAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPResidualIndependentMaterializerCost.lean';
const NAMES = [
  "appendIndependentNandMaterializers_size",
  "appendIndependentNandMaterializers_original",
  "appendIndependentNandMaterializers_materializer",
  "appendIndependentNandMaterializers_lower_bound",
  "appendIndependentNandMaterializers_equivalent",
  "appendIndependentNandMaterializers_referenceMinimum",
  "appendIndependentNandMaterializers_residualSlack"
];
const SIGNATURES = [
  "theorem appendIndependentNandMaterializers_size {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs) (count : Nat) : (appendIndependentNandMaterializers candidate count).program.size = gates + count",
  "theorem appendIndependentNandMaterializers_original {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs) (count : Nat) (valuation : Valuation (inputs + (count + count))) (output : Fin outputs) : (appendIndependentNandMaterializers candidate count).semantics valuation (Fin.castAdd count output) = candidate.semantics (fun input => valuation (Fin.castAdd (count + count) input)) output",
  "theorem appendIndependentNandMaterializers_materializer {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs) (count : Nat) (valuation : Valuation (inputs + (count + count))) (output : Fin count) : (appendIndependentNandMaterializers candidate count).semantics valuation (Fin.natAdd outputs output) = boolNand (valuation (Fin.natAdd inputs (Fin.castAdd count output))) (valuation (Fin.natAdd inputs (Fin.natAdd count output)))",
  "theorem appendIndependentNandMaterializers_lower_bound {inputs gates outputs competingGates : Nat} (candidate : Candidate inputs gates outputs) (count : Nat) (competing : Candidate (inputs + (count + count)) competingGates (outputs + count)) (equivalent : Equivalent competing.program competing.directWireWord (appendIndependentNandMaterializers candidate count).program (appendIndependentNandMaterializers candidate count).directWireWord) : referenceMinimum candidate.toImplementation + count ≤ competingGates",
  "theorem appendIndependentNandMaterializers_equivalent {inputs leftGates rightGates outputs : Nat} (left : Candidate inputs leftGates outputs) (right : Candidate inputs rightGates outputs) (count : Nat) (equivalent : Equivalent left.program left.directWireWord right.program right.directWireWord) : Equivalent (appendIndependentNandMaterializers left count).program (appendIndependentNandMaterializers left count).directWireWord (appendIndependentNandMaterializers right count).program (appendIndependentNandMaterializers right count).directWireWord",
  "theorem appendIndependentNandMaterializers_referenceMinimum {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs) (count : Nat) : referenceMinimum (appendIndependentNandMaterializers candidate count).toImplementation = referenceMinimum candidate.toImplementation + count",
  "theorem appendIndependentNandMaterializers_residualSlack {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs) (count : Nat) : residualSlack (appendIndependentNandMaterializers candidate count).toImplementation = residualSlack candidate.toImplementation"
];
const PUBLIC_HEADS = [
  "appendIndependentNandMaterializers",
  "appendIndependentNandMaterializers_size",
  "appendIndependentNandMaterializers_original",
  "appendIndependentNandMaterializers_materializer",
  "appendIndependentNandMaterializers_lower_bound",
  "appendIndependentNandMaterializers_equivalent",
  "appendIndependentNandMaterializers_referenceMinimum",
  "appendIndependentNandMaterializers_residualSlack"
];

const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = value => stripLeanCommentsAndStrings0(value).replace(/\s+/gu, ' ').trim();
function block0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex(head => head.name === name);
  return index < 0 ? '' : source.slice(heads[index].index, heads[index + 1]?.index ?? source.length);
}

function validateSource0(source) {
  const failures = [];
  const require0 = (condition, category) => { if (!condition) failures.push(category); };
  const clean = compact0(source);
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|callerCertificate|suppliedMinimum)\b/u
    .test(clean), 'shortcut-or-certificate');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]))
    === JSON.stringify(['PNP.DirectWireBaseline','PNP.NANDSlack']), 'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head => head.name)) ===
    JSON.stringify(PUBLIC_HEADS), 'public-interface');
  for (const [index,name] of NAMES.entries())
    require0(compact0(block0(source,name)).startsWith(SIGNATURES[index] + ' := '),
      'signature:' + name);
  const constructor = compact0(block0(source,'appendIndependentNandMaterializers'));
  for (const token of [
    'candidate.program.renameInputs (Fin.castAdd (count + count))',
    'Source.input (Fin.natAdd inputs input)',
    'independentNandPrefix count count (Nat.le_refl count)',
    '(Fin.castAdd (count + count))).weakenGates count',
    'Source.gate (Fin.natAdd gates output)',
    'Candidate.ofDirectWireWord program word',
  ]) require0(constructor.includes(token), 'fresh-physical-construction');
  require0(clean.includes('⟨.input (Fin.castAdd total index), .input (Fin.natAdd total index)⟩'),
    'distinct-fresh-pair');
  for (const token of [
    'if erase (Fin.last gates) = true then',
    'splitFin previous.image (fun _ => .constant (values (Fin.last gates)))',
    '⟨materializerRebindSource binding previous.image gate.left, materializerRebindSource binding previous.image gate.right⟩',
    'splitFin (fun index => (previous.image index).weakenGates 1)',
    '((allFin gates).filter erase).length = gates',
    'materializerEraseCandidate_semantics',
  ]) require0(clean.includes(token), 'exact-computed-erasure');
  const lower = compact0(block0(source,'appendIndependentNandMaterializers_lower_bound'));
  for (const token of [
    '(materializerOutputView_conditions candidate count).of_equivalent viewEquivalent',
    '(allFin count).map (outputGateIndex view conditions)',
    'fun gate => decide (gate ∈ selected)',
    'materializerRestrictInputs inputs count',
    'have erasedCount : ((allFin competingGates).filter erase).length = count',
    'have erasedConstant : ∀ valuation : Valuation inputs, ∀ index,',
    'outputGateIndex_source view conditions output',
    'materializerEraseCandidate_semantics competing binding erase (fun _ => true)',
    'referenceMinimum_le_of_equivalent candidate.toImplementation original originalEquivalent',
    'rw [erasedCount] at countBalance',
  ]) require0(lower.includes(token), 'derived-additive-lower-bound');
  const minimum = compact0(block0(source,'appendIndependentNandMaterializers_referenceMinimum'));
  for (const token of [
    'referenceMinimumWitness candidate.toImplementation',
    'appendIndependentNandMaterializers_equivalent',
    'appendIndependentNandMaterializers_lower_bound candidate count',
    'referenceMinimumWitness_equivalent',
  ]) require0(minimum.includes(token), 'two-sided-attained-minimum');
  return [...new Set(failures)];
}

test('M240 derives exact independent cost with all seven arbitrary-circuit interfaces', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE)), []);
});

test('M240 explicit root, axiom audit and reviewed-name producers agree', async () => {
  const [source,audit,inventorySource,root] = await Promise.all([
    text0(SOURCE),text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean'),
  ]);
  for (const name of NAMES) {
    assert.equal(explicitLeanDeclarationHeads0(source).filter(head => head.name === name).length,1);
    const fullName = 'PNP.DirectWire.' + name;
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item => item === fullName).length,1);
    assert.equal(inventorySource.split(String.fromCharCode(96) + fullName + ',').length - 1,1);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),
    NAMES.map(name=>'PNP.DirectWire.'+name));
  assert.match(root,/^import PNP\.ResidualIndependentMaterializerCost\s*$/mu);
});

test('M240 regressions cover nonminimum originals, empty banks, interleaved consumers and nonfresh duplication', async () => {
  const raw = await text0(REGRESSION), regression = compact0(raw);
  for (const name of NAMES) assert.ok(regression.includes(name + ' '),name);
  for (const token of [
    'emptyCandidate : Candidate 0 0 0',
    'redundantMixed : Candidate 1 1 4',
    'zeroGateMixed : Candidate 1 0 4',
    'referenceMinimum redundantMixed.toImplementation = 0',
    '(appendIndependentNandMaterializers redundantMixed count).toImplementation = count',
    '(appendIndependentNandMaterializers redundantMixed count).toImplementation = 1',
    'appendIndependentNandMaterializers candidate 0',
    'interleavedProgram : Program 4 5',
    'left := .gate 0, right := .constant false',
    'if output.val = 0 then .gate 4 else .gate 0',
    'interleaved interleaved_equivalent',
    '¬ 2 ≤ referenceMinimum repeatedNonfresh.toImplementation',
    'outputs == [false, true]',
    'IO.println', 'throw (IO.userError',
  ]) assert.ok(regression.includes(token),token);
  assert.equal([...raw.matchAll(/^#eval\b/gmu)].length,1);
  assert.ok(raw.includes('m240-independent-materializer-construction-execution-ok'));
  assert.doesNotMatch(regression,/\b(?:sorry|admit|native_decide|Classical)\b/u);
  assert.doesNotMatch(raw.split('#eval')[1],/\breferenceMinimum\s/u);
});

test('M240 rejects finite-only, minimal-original and output-count-only theorem replacements', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    ['(count : Nat)','(count : Fin 3)','signature:'+NAMES[0]],
    ['(count : Nat)\n    (competing :',
      '(count : Nat)\n    (minimum : IsSemanticallyMinimum candidate.toImplementation)\n    (competing :',
      'signature:'+NAMES[3]],
    ['referenceMinimum candidate.toImplementation + count ≤ competingGates',
      'count ≤ competingGates','signature:'+NAMES[3]],
    ['referenceMinimum candidate.toImplementation + count := by',
      'referenceMinimum candidate.toImplementation := by','signature:'+NAMES[5]],
    ['residualSlack candidate.toImplementation := by',
      'residualSlack candidate.toImplementation + count := by','signature:'+NAMES[6]],
  ];
  for (const [before,after,category] of mutations) {
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
});

test('M240 rejects nonfresh pairs, supplied minima and uncomputed or incomplete gate erasure', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    ['.input (Fin.natAdd total index)','.input (Fin.castAdd total index)','distinct-fresh-pair'],
    ['materializerRebindSource binding previous.image gate.right',
      'materializerRebindSource binding previous.image gate.left','exact-computed-erasure'],
    ['fun gate => decide (gate ∈ selected)','fun _ => false','derived-additive-lower-bound'],
    ['referenceMinimumWitness candidate.toImplementation',
      'suppliedMinimum candidate','two-sided-attained-minimum'],
  ];
  for (const [before,after,category] of mutations) {
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n').includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n').includes('unaudited-form'));
});

test('M240 durable workflow includes source contracts, strict root audit and guarded regressions', async () => {
  const [packageText,surface,verifier,workflow] = await Promise.all([
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),text0('.github/workflows/lean-bridge.yml'),
  ]);
  const auditPath = 'audits/lean-residual-independent-materializer-cost0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m240'],'node --test '+auditPath);
  assert.ok(surface.includes("'audit:m240': 'node --test "+auditPath+"'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test '+auditPath));
  for (const path of [auditPath,'docs/lean_residual_independent_materializer_cost.md'])
    assert.equal(workflow.split("      - '"+path+"'").length-1,2);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M240_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-12-240';
const M240_MILESTONE = 'residual-independent-materializer-cost';
const M240_HASHES = Object.freeze({
  "PNP.DirectWire.appendIndependentNandMaterializers_size": "b9e62d820791057b85d460f0f0e4fcdf75b548ade178ffb02f6afbe43342007f",
  "PNP.DirectWire.appendIndependentNandMaterializers_original": "7e65839855b25defa669921d118f54469f1adad851557433c6b2a3916bd0497b",
  "PNP.DirectWire.appendIndependentNandMaterializers_materializer": "b4ec58852a66b2b707ddac5378b3fce1481889d9e89a3be878cf3345fcdc81a1",
  "PNP.DirectWire.appendIndependentNandMaterializers_lower_bound": "d775d0bd12c5cb8af9a3ab08fd05a21637f1d724aff0bf3f28c93997db70ccdf",
  "PNP.DirectWire.appendIndependentNandMaterializers_equivalent": "e4ca1a4bc815ba9e1be215fff9ca41e24e10e90a43f627ea000eee029899ca68",
  "PNP.DirectWire.appendIndependentNandMaterializers_referenceMinimum": "0b9830efe900d365e70e4150003eb0df18c3da3ba28e17df580edd64db48ccf8",
  "PNP.DirectWire.appendIndependentNandMaterializers_residualSlack": "d4809059a0690effa9e02fa217a7d6ce6b59faaef074efb2f42a9d728e1e35c2"
});
const M240_STATUS_FIELDS = Object.freeze({
  "leanResidualIndependentMaterializerCostFormalized": true,
  "leanResidualIndependentMaterializerCostAxiomAuditPassed": true,
  "leanResidualIndependentMaterializerCostAuditedDeclarationCount": 7,
  "leanResidualIndependentMaterializerCostSizeTheorem": "PNP.DirectWire.appendIndependentNandMaterializers_size",
  "leanResidualIndependentMaterializerCostOriginalOutputsTheorem": "PNP.DirectWire.appendIndependentNandMaterializers_original",
  "leanResidualIndependentMaterializerCostFreshOutputsTheorem": "PNP.DirectWire.appendIndependentNandMaterializers_materializer",
  "leanResidualIndependentMaterializerCostLowerBoundTheorem": "PNP.DirectWire.appendIndependentNandMaterializers_lower_bound",
  "leanResidualIndependentMaterializerCostEquivalenceTheorem": "PNP.DirectWire.appendIndependentNandMaterializers_equivalent",
  "leanResidualIndependentMaterializerCostMinimumTheorem": "PNP.DirectWire.appendIndependentNandMaterializers_referenceMinimum",
  "leanResidualIndependentMaterializerCostSlackTheorem": "PNP.DirectWire.appendIndependentNandMaterializers_residualSlack",
  "leanResidualIndependentMaterializerCostScope": "all-finite-original-candidates-and-bank-sizes-disjoint-fresh-input-nand-materializers-computed-erasure-unrestricted-competitors-exact-reference-minimum-additivity-and-physical-slack-preservation-only"
});
const M240_AXIOMS = Object.freeze({
  "PNP.DirectWire.appendIndependentNandMaterializers_size": [],
  "PNP.DirectWire.appendIndependentNandMaterializers_original": [
    "Quot.sound"
  ],
  "PNP.DirectWire.appendIndependentNandMaterializers_materializer": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.appendIndependentNandMaterializers_lower_bound": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.appendIndependentNandMaterializers_equivalent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.appendIndependentNandMaterializers_referenceMinimum": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.appendIndependentNandMaterializers_residualSlack": [
    "Quot.sound",
    "propext"
  ]
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
const prose0 = value => value.replace(/\s+/gu, ' ').trim();
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

test('M240 compiled independent materializer cost and slack interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M240_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M240_COORDINATE)
    assert.equal(map.coordinate, 'PNP-FORMAL-PUBLICATION-MAP-2026-09-12-240');
  assert.deepEqual(row.requiredTheorems, Object.keys(M240_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, 'PNP.ResidualIndependentMaterializerCost', name);
      assert.deepEqual(declaration.axioms, M240_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M240_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M240_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M240_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "independent physical Boolean materializer forced-cost subcase",
  "not transparency of every manuscript profile materializer or every actual saturation step",
  "repeating an existing output or reusing the original input pair does not justify additive cost",
  "Reference minima remain exhaustive finite constructions, not a polynomial-time algorithm",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M240 publication rejects weakened, supplied, assumption-backed and widened cost/minimum substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M240_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M240_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = 'PNP.DirectWire.' + NAMES[4];
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M240_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M240_MILESTONE
    ? {...row, nonClaim:'Every materializer is transparent and unconditional polynomial ZeroSlack is proved.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M240 adds independent forced-cost coverage without complete materializer, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M240_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "exact physical semantic-minimum growth",
  "derived gate selection and exact erasure plus the attained-witness upper bound",
  "not complete materializer/profile transparency",
  "No fixed weighted checkpoint or global gate changes",
  "evidence row changes coverage only"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M240_COORDINATE) return;
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

test('M240 current summaries distinguish independent materializer cost from global route completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_residual_independent_materializer_cost.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "No original-minimality assumption is required",
  "independent physical Boolean materializer forced-cost subcase",
  "not transparency of every manuscript profile materializer or every actual saturation step",
  "Reference minima remain exhaustive finite constructions, not a polynomial-time algorithm",
  "Runtime execution is test evidence, not theorem authority",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-12-independent-materializer-cost.md'));
  assert.ok(plan.includes('Publication decision: defer'));
  if (progress.asOfCoordinate !== M240_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_residual_independent_materializer_cost.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
