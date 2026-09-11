import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';
import {
  DeriveFormalPublication0, MilestoneTheoremKernelTypeSha2560,
  REQUIRED_MILESTONE_THEOREMS0, stableStringify0,
} from '../formal-publication0.mjs';
import { validateProofProgress0 } from '../pcc-proof-progress0.mjs';

const SOURCE = 'lean/PNP/ResidualTerminalCandidateSaturation.lean';
const AUDIT = 'lean-audit/PNPResidualTerminalProfileDependencySemanticsAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPResidualTerminalProfileDependencySemantics.lean';
const NAMES = [
  'terminalCandidateProfileObservation',
  'terminalGateInfluencesProfile_eq_true_iff',
  'terminalCandidateProfileRequires_eq_influence',
  'terminalCandidateSaturate_profile_noninterference',
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
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|callerRequires|suppliedCoverage)\b/u.test(compact0(source)),
    'shortcut-or-certificate');
  for (const name of NAMES) {
    require0(compact0(block0(source, name)).includes(
      '{inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)'),
    'unbounded-candidate-model');
  }
  const observation = compact0(block0(source, NAMES[0]));
  require0(observation.includes('(context : List (Fin gates)) (coordinate : Fin profileWidth) : Bool := model.observe (terminalAmbientSupportImplementation candidate (context.map'),
    'actual-observation');
  require0(observation.includes('TerminalPrimitiveRecord.gate gate'), 'actual-observation');

  const reflection = compact0(block0(source, NAMES[1]));
  require0(reflection.includes(
    '(gate : Fin gates) (coordinate : Fin profileWidth) : terminalGateInfluencesProfile candidate model gate coordinate = true ↔ ∃ context, context ∈ terminalListSubsets ((allFin gates).filter (fun other => decide (other ≠ gate))) ∧ terminalCandidateProfileObservation candidate model (gate :: context) coordinate ≠ terminalCandidateProfileObservation candidate model context coordinate := by'),
    'exact-reflection');
  const edge = compact0(block0(source, NAMES[2]));
  require0(edge.includes(
    '(kind : TerminalSaturationRuleKind) (coordinate : Fin profileWidth) (gate : Fin gates) : (terminalCandidateSaturationSystem candidate model).requires kind (.profile coordinate) (.gate gate) = (decide (kind = terminalSaturationRuleOfProfileRole (model.profileSystem.role coordinate)) && terminalGateInfluencesProfile candidate model gate coordinate) := by'),
    'exact-role-edge');
  const closure = compact0(block0(source, NAMES[3]));
  require0(closure.includes(
    '(seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (coordinate : Fin profileWidth) (gate : Fin gates) (context : List (Fin gates)) (profileMember : TerminalPrimitiveRecord.profile coordinate ∈ terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed) (gateAbsent : TerminalPrimitiveRecord.gate gate ∉ terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed) (canonicalContext : context ∈ terminalListSubsets ((allFin gates).filter (fun other => decide (other ≠ gate)))) : terminalCandidateProfileObservation candidate model (gate :: context) coordinate = terminalCandidateProfileObservation candidate model context coordinate := by'),
    'computed-closure-noninterference');
  require0(closure.includes('terminalSaturateRecords_closed (terminalCandidateSaturationSystem candidate model) seed'),
    'actual-closure-proof');
  return [...new Set(failures)];
}

test('M232 reflects exhaustive profile influence and actual saturation for arbitrary candidate sizes', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE)), []);
});

test('M232 root axiom audit and both reviewed-name producers cover the intended interface', async () => {
  const [source, audit, inventorySource, root] = await Promise.all([
    text0(SOURCE), text0(AUDIT), text0('lean-audit/PNPTheoremInventory.lean'), text0('lean/PNP.lean'),
  ]);
  const heads = explicitLeanDeclarationHeads0(source);
  for (const name of NAMES) assert.equal(heads.filter(head => head.name === name).length, 1, name);
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]), ['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match => match[1]),
    NAMES.map(name => 'PNP.DirectWire.' + name));
  assert.match(root, /^import PNP\.ResidualTerminalCandidateSaturation\s*$/mu);
  for (const name of NAMES.slice(1).map(name => 'PNP.DirectWire.' + name)) {
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item => item === name).length, 1, name);
    assert.equal(inventorySource.split(String.fromCharCode(96) + name + ',').length - 1, 1, name);
  }
});

test('M232 regression retains generic theorem applications and nonsingleton interaction cases', async () => {
  const regression = await text0(REGRESSION);
  for (const name of NAMES.slice(1)) assert.ok(regression.includes(name + ' candidate model'), name);
  for (const token of [
    'decide (2 ≤ implementation.gateCount)', '[first, second]', '[second]',
    'terminalGateInfluencesProfile candidate (interactionModel .origin)',
    'TerminalPrimitiveRecord.profile coordinate ∈',
    'TerminalPrimitiveRecord.gate first ∉',
    'profileSeed coordinate first [second] (by decide) (by decide) (by decide)',
    '.carrier, .origin, .kernel, .obligation, .prefix, .direction,',
    '.saturation, .budget, .charge, .frontier',
  ]) assert.ok(regression.includes(token), token);
  assert.doesNotMatch(compact0(regression), /\b(?:sorry|admit|native_decide|Classical)\b/u);
});

test('M232 rejects singleton-only, supplied, weakened and assumption-backed substitutes', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    ['{inputs gates outputs profileWidth : Nat}', '{inputs outputs profileWidth : Nat} {gates : Fin 2}', 'unbounded-candidate-model'],
    ['= true ↔\n      ∃ context,', '= true →\n      ∃ context,', 'exact-reflection'],
    ['context ∈ terminalListSubsets\n          ((allFin gates).filter (fun other => decide (other ≠ gate)))',
      'context ∈ [[]]', 'exact-reflection'],
    ['model.observe (terminalAmbientSupportImplementation candidate', 'model.observe (suppliedImplementation candidate', 'actual-observation'],
    ['(kind : TerminalSaturationRuleKind)\n    (coordinate : Fin profileWidth) (gate : Fin gates)',
      '(kind : Fin 1)\n    (coordinate : Fin profileWidth) (gate : Fin gates)', 'exact-role-edge'],
    ['(gateAbsent : TerminalPrimitiveRecord.gate gate ∉', '(gateAbsent : TerminalPrimitiveRecord.gate gate ∈', 'computed-closure-noninterference'],
    ['terminalSaturateRecords_closed\n        (terminalCandidateSaturationSystem candidate model) seed',
      'suppliedClosure\n        (terminalCandidateSaturationSystem candidate model) seed', 'actual-closure-proof'],
  ];
  for (const [before, after, category] of mutations) {
    assert.ok(source.includes(before), 'mutation anchor: ' + category);
    // Change every occurrence of a shared quantifier; a mutation must reach the
    // reviewed theorem rather than only an earlier unrelated definition.
    const changed = source.replaceAll(before, after);
    assert.ok(validateSource0(changed).includes(category), category);
  }
  assert.ok(validateSource0(source + '\naxiom profileAuthority : True\n').includes('assumption'));
  assert.ok(validateSource0(source + '\nprivate def suppliedCoverage := true\n').includes('shortcut-or-certificate'));
});

const M232_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-11-232';
const M232_MILESTONE = 'residual-terminal-profile-dependency-semantics';
const M232_HASHES = Object.freeze({
  'PNP.DirectWire.terminalGateInfluencesProfile_eq_true_iff': '6b889ca06140498835da44305ac96f7ab8820e0640b2b8175e36566910082ab3',
  'PNP.DirectWire.terminalCandidateProfileRequires_eq_influence': '1f58c87385f0dbbe2932a1f1cbdc6a156dc0218a15171539d1c78daae7dec92a',
  'PNP.DirectWire.terminalCandidateSaturate_profile_noninterference': '3f9d0b7f8bd9fd56cdf1b1b2883913ddf6516d64680c6850870a6129ba89fb5d',
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
const canonicalBytes0 = value => Buffer.from(stableStringify0(value) + '\n');
const prose0 = value => value.replace(/\s+/gu, ' ').trim();
function metrics0(progress) {
  const coverage = progress.formalArtefactCoverage;
  const proof = progress.proofCompletion;
  const gates = progress.globalGates.filter(gate => gate.status === 'closed').length;
  return [
    'Formal artefact coverage: ' + coverage.earnedRows + ' of ' + coverage.totalRows
      + ' current scoped publication rows earned.',
    'Risk-weighted proof completion estimate: ' + proof.percent + '%.',
    'Uncertainty range: ' + proof.uncertaintyLowPercent + '% to '
      + proof.uncertaintyHighPercent + '%.',
    'Global gates closed: ' + gates + ' of ' + progress.globalGates.length + '.',
  ];
}

test('M232 compiled declarations, reviewed type fingerprints and emitted status agree', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M232_MILESTONE);
  assert.equal(row?.earned, true);
  assert.deepEqual(row.requiredTheorems, Object.keys(M232_HASHES));
  assert.equal(publication.gate.passed, status.concretePublicationGate.passed);
  for (const name of NAMES.map(name => 'PNP.DirectWire.' + name)) {
    const declaration = inventory.declarations.find(item => item.name === name);
    assert.equal(declaration?.module, 'PNP.ResidualTerminalCandidateSaturation', name);
    assert.equal(declaration.kind, name.endsWith('.terminalCandidateProfileObservation')
      ? 'definition' : 'theorem', name);
    assert.deepEqual(declaration.axioms, ['Quot.sound', 'propext'], name);
  }
  for (const [name, fingerprint] of Object.entries(M232_HASHES)) {
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(candidate?.kind, 'theorem', name);
    assert.equal(candidate.module, 'PNP.ResidualTerminalCandidateSaturation', name);
    assert.deepEqual(candidate.axioms, ['Quot.sound', 'propext'], name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), fingerprint);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], fingerprint);
  }
  assert.equal(status.leanResidualTerminalProfileDependencySemanticsFormalized, true);
  assert.equal(status.leanResidualTerminalProfileDependencySemanticsAxiomAuditPassed, true);
  assert.equal(status.leanResidualTerminalProfileDependencySemanticsAuditedDeclarationCount, 4);
  assert.equal(status.leanResidualTerminalProfileDependencyNoninterferenceTheorem,
    'PNP.DirectWire.terminalCandidateSaturate_profile_noninterference');
  assert.equal(status.leanResidualTerminalProfileDependencySemanticsScope,
    'all-finite-candidates-executable-models-computed-profile-influence-role-labelled-edges-and-computed-saturation-noninterference-in-canonical-contexts-only');
  assert.ok(row.scope.includes('canonical subset context'));
  assert.ok(row.nonClaim.includes('observer and profile model remain supplied data'));
  assert.ok(row.nonClaim.includes('enumerates all subsets'));
  assert.ok(row.nonClaim.includes('No fixed weighted checkpoint or global gate closes'));
});

test('M232 adds coverage independently without awarding an unconditional or runtime checkpoint', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M232_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  assert.match(review.rationale, /observer and profile model remain supplied/u);
  assert.match(review.rationale, /enumerates all subsets/u);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows,
    status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate === M232_COORDINATE) {
    assert.deepEqual(progress.tracks.map(track => track.pointsAvailable), [15, 20, 35, 20, 10]);
    assert.deepEqual(progress.tracks.map(track => track.pointsEarned), [13, 20, 2, 1, 4]);
    assert.equal(progress.proofCompletion.percent, 40);
    assert.equal(progress.globalGates.filter(gate => gate.status === 'closed').length, 0);
    assert.deepEqual(inventory.projectAxioms, []);
    assert.deepEqual(progress.projectSpecificAxiomsRemaining, []);
    assert.equal(status.leanConcreteCNFSATInPFormalized, false);
    assert.equal(status.rootLeanTheoremPresent, false);
    assert.equal(status.rootLeanTheoremBuilt, false);
    assert.equal(status.rootLeanTheoremAxiomAuditPassed, false);
    assert.equal(status.concretePublicationGate.passed, false);
    assert.deepEqual(progress.rootTheorem, {
      name: 'PNP.Main.p_eq_np', present: false, built: false, axiomAuditPassed: false,
    });
  }
});

test('M232 publication rejects weakened or supplied compiled types and widened map claims', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M232_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates: inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType: substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const publication = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(publication.milestones.find(row => row.id === M232_MILESTONE).earned, false);
    assert.equal(publication.gate.passed, false);
  }
  const widened = {...map, milestones: map.milestones.map(row =>
    row.id === M232_MILESTONE ? {...row, nonClaim: 'Unconditional polynomial ZeroSlack is proved.'} : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256: {
    ...map.earnedMilestoneTheoremKernelTypeSha256,
    [Object.keys(M232_HASHES)[2]]: '0'.repeat(64),
  }};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M232 rejects automatic percentage credit for a local semantic result', async () => {
  const {status, inventory, progress} = await compiledSources0();
  if (progress.asOfCoordinate !== M232_COORDINATE) return;
  const inflated = structuredClone(progress);
  inflated.proofCompletion.pointsEarned += 1;
  inflated.proofCompletion.percent += 1;
  assert.throws(() => validateProofProgress0(inflated, status, inventory),
    error => error.code === 'ProofCompletion.StoredEarned');
  const unearned = structuredClone(progress);
  unearned.tracks.flatMap(track => track.checkpoints)
    .find(checkpoint => checkpoint.id === 'root-complexity-transport').status = 'earned';
  assert.throws(() => validateProofProgress0(unearned, status, inventory),
    error => error.code === 'Checkpoint.Status');
});

test('M232 durable audits and core summaries retain the local scope and publication deferral', async () => {
  const [workflow, packageText, surface, verifier, documentation, plan] = await Promise.all([
    text0('.github/workflows/lean-bridge.yml'), text0('package.json'),
    text0('pcc-formal-public-surface0.mjs'), text0('scripts/pnp-verify-all.mjs'),
    text0('docs/lean_residual_terminal_profile_dependency_semantics.md'),
    text0('docs/plans/2026-09-11-terminal-profile-dependency-noninterference.md'),
  ]);
  const auditPath = 'audits/lean-residual-terminal-profile-dependency-semantics0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m232'], 'node --test ' + auditPath);
  for (const source of [workflow, verifier]) assert.ok(source.includes(auditPath));
  assert.ok(surface.includes("'audit:m232'"));
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  assert.ok(prose0(documentation).includes('Influence enumerates all subsets and is not a polynomial-time construction.'));
  assert.ok(prose0(plan).includes('Publication decision: defer'));
  const {progress} = await compiledSources0();
  if (progress.asOfCoordinate === M232_COORDINATE) {
    for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
      'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
      'docs/lean_residual_terminal_profile_dependency_semantics.md']) {
      const text = prose0(await text0(file));
      for (const metric of metrics0(progress)) assert.ok(text.includes(metric), file + ': ' + metric);
    }
  }
});

function readmeCurrentRows0(text, progress, status) {
  const rows = text.split('\n');
  const row = question => rows.find(line => line.startsWith('| **' + question + '** |')) ?? '';
  const progressRow = prose0(row('How is progress measured?'));
  if (!metrics0(progress).every(metric => progressRow.includes(metric))) return false;
  const verification = row('What is the current verification status?');
  const remaining = row('What remains formally?');
  if (!verification || !remaining) return false;
  if (status.leanConcreteCookLevinFormulaBuilderFormalized
      && /no complete raw polynomial-time Cook-Levin formula builder/u.test(verification + remaining)) return false;
  return true;
}

test('current README table derives both metrics and rejects stale current claims, not history', async () => {
  const {status, progress} = await compiledSources0();
  const readme = await text0('README.md');
  assert.equal(readmeCurrentRows0(readme, progress, status), true);
  const progressRow = readme.split('\n')
    .find(line => line.startsWith('| **How is progress measured?** |'));
  const staleRow = progressRow.replace(metrics0(progress)[1],
    'Risk-weighted proof completion estimate: ' + (progress.proofCompletion.percent - 1) + '%.');
  assert.equal(readmeCurrentRows0(readme.replace(progressRow, staleRow), progress, status), false);
  const wrongCoverage = progressRow.replace(metrics0(progress)[0], 'Proof completion: 98%.');
  assert.equal(readmeCurrentRows0(readme.replace(progressRow, wrongCoverage), progress, status), false);
  if (status.leanConcreteCookLevinFormulaBuilderFormalized) {
    const question = '| **What remains formally?** |';
    const obsolete = readme.replace(question, question + ' no complete raw polynomial-time Cook-Levin formula builder;');
    assert.equal(readmeCurrentRows0(obsolete, progress, status), false);
  }
  assert.equal(readmeCurrentRows0(readme + '\nHistorical scoped-row metric: 98%.\n',
    progress, status), true);
});
