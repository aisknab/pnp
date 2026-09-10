import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';
import { DeriveFormalPublication0, MilestoneTheoremKernelTypeSha2560,
  REQUIRED_MILESTONE_THEOREMS0 } from '../formal-publication0.mjs';
import { validateProofProgress0 } from '../pcc-proof-progress0.mjs';

const SOURCE = 'lean/PNP/Concrete/CookLevinNPCompleteness.lean';
const AUDIT = 'lean-audit/PNPConcreteCookLevinNPCompletenessAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPConcreteCookLevinNPCompleteness.lean';
const NAMESPACE = 'PNP.Concrete.CookLevin';
const NAMES = ['cnfSAT_np_hard', 'cnfSAT_np_complete'];
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = value => value.replace(/\s+/gu, ' ').trim();
const imports0 = value => [...value.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]);

function validateSource0(source) {
  const errors = [];
  const require0 = (condition, label) => { if (!condition) errors.push(label); };
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(stripped);
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|choice)\b/u.test(stripped), 'shortcut');
  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.CookLevinCompleteBuilder',
    'PNP.Concrete.CNFWorkUniversalCorrectness',
  ]), 'imports');
  require0(compact.includes('theorem cnfSAT_np_hard (source : Language) (sourceInNP : InNP source) : ReducesTo source CNFSAT := by'),
    'unbounded-hardness');
  require0(compact.includes('rcases sourceInNP with ⟨verifier⟩ exact ⟨polynomialReduction verifier⟩'),
    'source-derived-reduction');
  require0(compact.includes('theorem cnfSAT_np_complete : NPComplete CNFSAT := { inNP := FinalUniversalDesign.cnfSATInNP hard := cnfSAT_np_hard }'),
    'closed-np-completeness');
  return errors;
}

test('M231 source closes concrete CNFSAT hardness and NP-completeness without a supplied reduction', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE)), []);
});

test('M231 audits the complete two-theorem interface through the root', async () => {
  const [source, audit, regression, root, inventorySource] = await Promise.all([
    text0(SOURCE), text0(AUDIT), text0(REGRESSION), text0('lean/PNP.lean'),
    text0('lean-audit/PNPTheoremInventory.lean'),
  ]);
  assert.deepEqual(explicitLeanDeclarationHeads0(source).map(({ name }) => name), NAMES);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match => match[1]),
    NAMES.map(name => NAMESPACE + '.' + name));
  assert.ok(imports0(root).includes('PNP.Concrete.CookLevinNPCompleteness'));
  assert.deepEqual(imports0(regression), ['PNP.Concrete.CookLevinNPCompleteness']);
  assert.equal([...regression.matchAll(/^example\b/gmu)].length, 4);
  assert.ok(compact0(regression).includes('example : NPComplete CNFSAT := cnfSAT_np_complete'));
  assert.ok(compact0(regression).includes('Nonempty (PolynomialReduction source CNFSAT) := cnfSAT_np_complete.hard source sourceInNP'));
  for (const name of NAMES.map(name => NAMESPACE + '.' + name)) {
    assert.ok(REQUIRED_MILESTONE_THEOREMS0.includes(name), name);
    assert.ok(inventorySource.includes(String.fromCharCode(96) + name), name);
  }
});

test('M231 rejects finite-only, supplied-premise, weakened, and assumption-backed substitutes', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    ['(source : Language)', '(source : Fin 1)', 'unbounded-hardness'],
    ['(sourceInNP : InNP source) :', '(sourceInNP : InNP source) (given : ReducesTo source CNFSAT) :', 'unbounded-hardness'],
    ['exact ⟨polynomialReduction verifier⟩', 'exact ⟨suppliedReduction verifier⟩', 'source-derived-reduction'],
    ['theorem cnfSAT_np_complete :', 'theorem cnfSAT_np_complete (given : NPComplete CNFSAT) :', 'closed-np-completeness'],
    ['cnfSAT_np_complete : NPComplete CNFSAT', 'cnfSAT_np_complete : InNP CNFSAT', 'closed-np-completeness'],
    ['inNP := FinalUniversalDesign.cnfSATInNP', 'inNP := suppliedMembership', 'closed-np-completeness'],
  ];
  for (const [before, after, rejection] of mutations) {
    assert.ok(source.includes(before), 'mutation anchor: ' + rejection);
    const changed = source.replace(before, after);
    assert.ok(changed !== source);
    assert.ok(validateSource0(changed).includes(rejection), rejection);
  }
  assert.ok(validateSource0(source + '\naxiom suppliedAuthority : True\n').includes('assumption'));
});

test('M231 report cover derives current proof facts and rejects obsolete builder claims', async () => {
  const [template, generator, workflow, packageText, verifier] = await Promise.all([
    text0('publication/canonical_proof_report.template.tex'),
    text0('scripts/generate-formal-publication.mjs'),
    text0('.github/workflows/lean-bridge.yml'),
    text0('package.json'), text0('scripts/pnp-verify-all.mjs'),
  ]);
  const cover = template.split('\\end{titlepage}')[0];
  const validCover = text => text.includes('@@COVER_STATUS_ROWS@@')
    && text.includes('@@LATEST_MILESTONE_TITLE@@')
    && !compact0(text).includes('there is no complete raw polynomial-time Cook');
  assert.ok(validCover(cover));
  assert.equal(validCover(cover.replace('@@COVER_STATUS_ROWS@@',
    'there is no complete raw polynomial-time Cook--Levin formula builder')), false);
  for (const field of ['leanConcreteCNFSATMembershipFormalized',
    'leanConcreteCookLevinFormulaBuilderFormalized', 'leanConcreteCNFNPCompletenessFormalized',
    'leanConcreteCNFSATInPFormalized', 'rootLeanTheoremPresent']) assert.ok(generator.includes(field));
  assert.ok(generator.includes("typeof status[field] !== 'boolean'"));
  assert.ok(generator.includes('publication.milestones.filter(row => row.earned === true)'));
  assert.ok(template.includes('M231 now packages concrete CNF-SAT NP-completeness'));
  assert.equal(JSON.parse(packageText).scripts['audit:m231'],
    'node --test audits/lean-concrete-cook-levin-np-completeness0.test.mjs');
  assert.ok(verifier.includes('audits/lean-concrete-cook-levin-np-completeness0.test.mjs'));
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M231_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-11-231';
const M231_MILESTONE = 'concrete-cnf-np-completeness';
const M231_CHECKPOINT = 'reductions-concrete-np-hardness';
const M231_HASHES = Object.freeze({
  'PNP.Concrete.CookLevin.cnfSAT_np_hard': 'c2cae5f7ad14a81b32888e8405210b57552dea928200cc77e9ebb34099ec9909',
  'PNP.Concrete.CookLevin.cnfSAT_np_complete': '7b1c0556dde7066ebe7abc9706b400857b9dd41dc1d704930a1f1d6c423bbe35',
});
let compiledSourcesPromise0;
function compiledSources0() {
  compiledSourcesPromise0 ??= Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
    text0('status/LEAN_THEOREM_INVENTORY.json'),
    text0('status/PROOF_PROGRESS.json'),
    text0('publication/FORMAL_PUBLICATION_MAP.json'),
  ]).then(([s, i, p, m]) => ({status: JSON.parse(s), inventory: JSON.parse(i),
    progress: JSON.parse(p), map: JSON.parse(m), inventoryBytes: Buffer.from(i)}));
  return compiledSourcesPromise0;
}
function canonicalBytes0(value) {
  return Buffer.from(JSON.stringify(value, (_key, entry) =>
    entry !== null && typeof entry === 'object' && !Array.isArray(entry)
      ? Object.fromEntries(Object.keys(entry).sort().map(key => [key, entry[key]]))
      : entry) + '\n');
}

test('M231 compiled theorem types, two-name publication contract and status agree', async () => {
  const {status, inventory, map, inventoryBytes} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M231_MILESTONE);
  assert.equal(row?.earned, true);
  assert.deepEqual(row.requiredTheorems, NAMES.map(name => NAMESPACE + '.' + name));
  for (const [name, fingerprint] of Object.entries(M231_HASHES)) {
    const declaration = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(declaration?.kind, 'theorem', name);
    assert.equal(declaration.module, 'PNP.Concrete.CookLevinNPCompleteness', name);
    assert.deepEqual(declaration.axioms, ['Classical.choice', 'Quot.sound', 'propext'], name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, declaration.kernelType), fingerprint);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], fingerprint);
  }
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, true);
  assert.equal(status.leanConcreteCNFNPCompletenessAxiomAuditPassed, true);
  assert.equal(status.leanConcreteCNFNPCompletenessAuditedDeclarationCount, NAMES.length);
  assert.equal(status.leanConcreteCNFNPCompletenessTheorem, NAMESPACE + '.cnfSAT_np_complete');
  assert.equal(status.leanConcreteCNFNPCompletenessHardnessTheorem, NAMESPACE + '.cnfSAT_np_hard');
});

test('M231 earns exactly the existing two-point hardness checkpoint without root double credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M231_COORDINATE);
  assert.equal(review?.scoreChanged, true);
  assert.deepEqual(review.changedCheckpointIds, [M231_CHECKPOINT]);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.deepEqual(review.changeRecords[0].oldAndNewTotal, {old: 38, new: 40});
  assert.equal(review.changeRecords[0].oldStatus, 'open');
  assert.equal(review.changeRecords[0].newStatus, 'earned');
  assert.equal(review.changeRecords[0].sourceCoordinateOrCommit, M231_COORDINATE);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  assert.deepEqual(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned === true).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate === M231_COORDINATE) {
    assert.deepEqual(progress.tracks.map(track => track.pointsEarned), [13, 20, 2, 1, 4]);
    assert.deepEqual(progress.tracks.map(track => track.pointsAvailable), [15, 20, 35, 20, 10]);
    assert.equal(progress.proofCompletion.percent, 40);
    assert.equal(progress.tracks.flatMap(track => track.checkpoints)
      .find(checkpoint => checkpoint.id === 'root-complexity-transport').status, 'open');
    assert.equal(status.leanConcreteCNFSATInPFormalized, false);
    assert.equal(status.rootLeanTheoremPresent, false);
    assert.equal(status.concretePublicationGate.passed, false);
    assert.deepEqual(inventory.projectAxioms, []);
    assert.equal(progress.globalGates.filter(gate => gate.status === 'closed').length, 0);
  }
});

test('M231 publication rejects weakened or supplied theorem types and self-awarded map claims', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M231_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates: inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType: substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const publication = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(publication.milestones.find(row => row.id === M231_MILESTONE).earned, false);
    assert.equal(publication.gate.passed, false);
  }
  const widened = {...map, milestones: map.milestones.map(row =>
    row.id === M231_MILESTONE ? {...row, nonClaim: 'This proves P = NP.'} : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256: {
    ...map.earnedMilestoneTheoremKernelTypeSha256,
    [NAMESPACE + '.cnfSAT_np_complete']: '0'.repeat(64),
  }};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M231 progress rejects missing hardness evidence, stale score and duplicate root credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  if (progress.asOfCoordinate !== M231_COORDINATE) return;
  const missingStatus = {...status, leanConcreteCNFNPCompletenessFormalized: false};
  assert.throws(() => validateProofProgress0(progress, missingStatus, inventory),
    error => error.code === 'Evidence.StatusMismatch');
  const missingTheorem = {...inventory, declarations: inventory.declarations
    .filter(row => row.name !== NAMESPACE + '.cnfSAT_np_hard')};
  assert.throws(() => validateProofProgress0(progress, status, missingTheorem),
    error => error.code === 'Evidence.DeclarationPresence');
  const stale = structuredClone(progress);
  stale.proofCompletion.pointsEarned = 38;
  stale.proofCompletion.percent = 38;
  assert.throws(() => validateProofProgress0(stale, status, inventory),
    error => error.code === 'ProofCompletion.StoredEarned');
  const duplicate = structuredClone(progress);
  duplicate.tracks.flatMap(track => track.checkpoints)
    .find(checkpoint => checkpoint.id === 'root-complexity-transport').status = 'earned';
  assert.throws(() => validateProofProgress0(duplicate, status, inventory),
    error => error.code === 'Checkpoint.Status');
  const missingRationale = structuredClone(progress);
  missingRationale.history.at(-1).changeRecords[0].loadBearingRationale = '';
  assert.throws(() => validateProofProgress0(missingRationale, status, inventory),
    error => error.code === 'History.ChangeRecordRationale');
});

test('M231 current documentation and report expose the current metrics without widening gates', async () => {
  const {status, progress} = await compiledSources0();
  const files = ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_cook_levin_np_completeness.md'];
  const coverage = 'Formal artefact coverage: ' + progress.formalArtefactCoverage.earnedRows
    + ' of ' + progress.formalArtefactCoverage.totalRows + ' current scoped publication rows earned.';
  for (const file of files) {
    const text = compact0(await text0(file));
    assert.ok(text.includes('M231'), file);
    if (progress.asOfCoordinate === M231_COORDINATE) {
      assert.ok(text.includes(coverage), file);
      assert.ok(text.includes('Risk-weighted proof completion estimate: '
        + progress.proofCompletion.percent + '%.'), file);
      assert.ok(text.includes('Global gates closed: 0 of 5.'), file);
    }
  }
  const report = await text0('canonical_proof_report.tex');
  const cover = compact0(report.split('\\end{titlepage}')[0]);
  for (const [label, field] of [
    ['CNF-SAT membership in NP', 'leanConcreteCNFSATMembershipFormalized'],
    ['Complete all-input Cook-Levin builder', 'leanConcreteCookLevinFormulaBuilderFormalized'],
    ['Concrete CNF-SAT NP-completeness', 'leanConcreteCNFNPCompletenessFormalized'],
    ['Deterministic CNF-SAT membership in P', 'leanConcreteCNFSATInPFormalized'],
    ['Eligible root theorem present', 'rootLeanTheoremPresent'],
  ]) assert.ok(cover.includes(label + ' & ' + (status[field] ? '\\statustrue' : '\\statusfalse')), field);
  assert.ok(!cover.includes('there is no complete raw polynomial-time Cook'));
  assert.ok(cover.includes('Risk-weighted proof completion estimate: '
    + progress.proofCompletion.percent + ' percent.'));
  assert.ok(cover.includes('Formal artefact coverage: '
    + progress.formalArtefactCoverage.earnedRows + ' of '
    + progress.formalArtefactCoverage.totalRows + ' current scoped publication rows.'));
});
