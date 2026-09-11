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

const EXTRACTION = 'lean/PNP/ResidualTerminalSupportExtraction.lean';
const SOURCE = 'lean/PNP/ResidualTerminalProfileLocality.lean';
const AUDIT = 'lean-audit/PNPResidualTerminalProfileLocalityAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPResidualTerminalProfileLocality.lean';
const NAMES = [
  'extractTerminalSupport_eq_of_gateSelected_eq',
  'terminalAmbientSupportImplementation_eq_of_gateSelected_eq',
  'terminalCandidateProfileObservation_eq_of_gateMembership_iff',
  'terminalCandidateSaturate_profile_locality',
  'terminalCandidateSaturate_profile_preserved',
];
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = value => stripLeanCommentsAndStrings0(value).replace(/\s+/gu, ' ').trim();
function block0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex(head => head.name === name);
  return index < 0 ? '' : source.slice(heads[index].index, heads[index + 1]?.index ?? source.length);
}
function signature0(source, name) {
  return compact0(block0(source, name)).split(' := by')[0];
}

// Independent, unbounded interfaces. Do not derive these from the implementation:
// they reject extra supplied premises as well as weakened conclusions.
const SIGNATURES = [
  'theorem extractTerminalSupport_eq_of_gateSelected_eq {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (left right : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (selectedEqual : terminalGateSelected left = terminalGateSelected right) : { extractTerminalSupport candidate left with records := right } = extractTerminalSupport candidate right',
  'theorem terminalAmbientSupportImplementation_eq_of_gateSelected_eq {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (left right : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (selectedEqual : terminalGateSelected left = terminalGateSelected right) : terminalAmbientSupportImplementation candidate left = terminalAmbientSupportImplementation candidate right',
  'theorem terminalCandidateProfileObservation_eq_of_gateMembership_iff {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (left right : List (Fin gates)) (coordinate : Fin profileWidth) (sameGates : ∀ gate, gate ∈ left ↔ gate ∈ right) : terminalCandidateProfileObservation candidate model left coordinate = terminalCandidateProfileObservation candidate model right coordinate',
  'theorem terminalCandidateSaturate_profile_locality {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed left right : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (coordinate : Fin profileWidth) (profileMember : TerminalPrimitiveRecord.profile coordinate ∈ terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed) (recordAgreement : ∀ gate, TerminalPrimitiveRecord.gate gate ∈ terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed → (TerminalPrimitiveRecord.gate gate ∈ left ↔ TerminalPrimitiveRecord.gate gate ∈ right)) : model.observe (terminalAmbientSupportImplementation candidate left) coordinate = model.observe (terminalAmbientSupportImplementation candidate right) coordinate',
  'theorem terminalCandidateSaturate_profile_preserved {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (coordinate : Fin profileWidth) (profileMember : TerminalPrimitiveRecord.profile coordinate ∈ terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed) : model.observe (terminalAmbientSupportImplementation candidate (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)) coordinate = model.observe (terminalAmbientSupportImplementation candidate (allTerminalPrimitiveRecords inputs gates outputs profileWidth)) coordinate',
];
function validateSources0(extraction, source) {
  const failures = [];
  const require0 = (condition, category) => { if (!condition) failures.push(category); };
  for (const value of [block0(extraction, NAMES[0]), source]) {
    require0(!hasLeanAssumptionDeclaration0(value), 'assumption');
    require0(!hasUnauditedLeanDeclarationForm0(value), 'unaudited-form');
    require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|suppliedCoverage|callerRequires)\b/u.test(compact0(value)),
      'shortcut-or-certificate');
  }
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head => head.name))
    === JSON.stringify(NAMES.slice(1)), 'public-interface');
  for (let index = 0; index < NAMES.length; index += 1) {
    require0(signature0(index === 0 ? extraction : source, NAMES[index]) === SIGNATURES[index],
      'signature:' + NAMES[index]);
  }
  for (const dependency of [
    'extractTerminalSupport_eq_of_gateSelected_eq candidate left right selectedEqual',
    'terminalCandidateSaturate_profile_noninterference candidate model seed',
    'profileObservation_remove_absent_prefix candidate model seed coordinate',
    'profileObservation_restrict_to_saturated candidate model seed coordinate',
    'profileObservation_records_canonical candidate model left coordinate',
    'mem_allTerminalPrimitiveRecords (.gate gate)',
  ]) require0(compact0(source).includes(dependency), 'computed-proof-chain');
  return [...new Set(failures)];
}

test('M233 source contracts retain arbitrary supports, computed closure and exact observations', async () => {
  assert.deepEqual(validateSources0(await text0(EXTRACTION), await text0(SOURCE)), []);
});

test('M233 root audit and reviewed-name producers cover all five intended theorems', async () => {
  const [source, extraction, audit, inventorySource, root] = await Promise.all([
    text0(SOURCE), text0(EXTRACTION), text0(AUDIT),
    text0('lean-audit/PNPTheoremInventory.lean'), text0('lean/PNP.lean'),
  ]);
  for (const name of NAMES) {
    const owner = name === NAMES[0] ? extraction : source;
    assert.equal(explicitLeanDeclarationHeads0(owner).filter(head => head.name === name).length, 1, name);
    const fullName = 'PNP.DirectWire.' + name;
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item => item === fullName).length, 1, fullName);
    assert.equal(inventorySource.split(String.fromCharCode(96) + fullName + ',').length - 1, 1, fullName);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]), ['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match => match[1]),
    NAMES.map(name => 'PNP.DirectWire.' + name));
  assert.match(root, /^import PNP\.ResidualTerminalProfileLocality\s*$/mu);
});

test('M233 regressions retain nonconstant output, omitted gates, metadata and the necessary premise', async () => {
  const regression = await text0(REGRESSION);
  const normalized = compact0(regression);
  for (const name of NAMES) assert.ok(normalized.includes(name + ' candidate'), name);
  for (const token of [
    'implementation.candidate.semantics (fun _ => false) first',
    'terminalGateInfluencesProfile candidate outputModel first coordinate = true',
    'terminalGateInfluencesProfile candidate outputModel second coordinate = false',
    'TerminalPrimitiveRecord.gate second ∉ saturated',
    '[.profile coordinate, .gate second, .gate first, .gate first, .interface coordinate]',
    '[second, first, first]',
    'TerminalPrimitiveRecord.profile coordinate ∉',
    'example : ¬ (∀ seed : List (TerminalPrimitiveRecord 0 2 1 1)',
    'counterexample (unconditional [])',
    'decide (2 ≤ implementation.gateCount)',
    'candidate interactionModel [first, second] coordinate ≠',
    'terminalCandidateSaturate_profile_preserved candidate interactionModel',
  ]) assert.ok(normalized.includes(token), token);
  assert.doesNotMatch(normalized, /\b(?:sorry|admit|native_decide|Classical)\b/u);
});

test('M233 rejects finite, supplied, weakened and unretained-profile substitutes', async () => {
  const extraction = await text0(EXTRACTION);
  const source = await text0(SOURCE);
  const mutations = [
    ['{inputs gates outputs profileWidth : Nat}', '{inputs outputs profileWidth : Nat} {gates : Fin 2}',
      'signature:' + NAMES[3]],
    ['(seed left right : List', '(suppliedCoverage : True) (seed left right : List',
      'signature:' + NAMES[3]],
    ['(sameGates : ∀ gate, gate ∈ left ↔ gate ∈ right)',
      '(sameGates : ∀ gate, gate ∈ left → gate ∈ right)', 'signature:' + NAMES[2]],
    ['(recordAgreement : ∀ gate,', '(recordAgreement : ∃ gate,', 'signature:' + NAMES[3]],
    ['(profileMember : TerminalPrimitiveRecord.profile coordinate ∈',
      '(profileMember : TerminalPrimitiveRecord.profile coordinate ∉', 'signature:' + NAMES[4]],
    ['model.observe (terminalAmbientSupportImplementation candidate left) coordinate =',
      'model.observe (terminalAmbientSupportImplementation candidate left) coordinate →',
      'signature:' + NAMES[3]],
    ['(allTerminalPrimitiveRecords inputs gates outputs profileWidth)', 'seed',
      'signature:' + NAMES[4]],
    ['terminalCandidateSaturate_profile_noninterference candidate model seed',
      'callerNoninterference candidate model seed', 'computed-proof-chain'],
  ];
  for (const [before, after, category] of mutations) {
    assert.ok(source.includes(before), 'mutation anchor: ' + category);
    assert.ok(validateSources0(extraction, source.replaceAll(before, after)).includes(category), category);
  }
  const retainedPremise =
    '    (profileMember : TerminalPrimitiveRecord.profile coordinate ∈\n'
    + '      terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)';
  assert.ok(source.includes(retainedPremise));
  assert.ok(validateSources0(extraction, source.replaceAll(retainedPremise, ''))
    .includes('signature:' + NAMES[4]));
  const wrongExtraction = extraction.replace(
    '{ extractTerminalSupport candidate left with records := right }',
    'extractTerminalSupport candidate left');
  assert.notEqual(wrongExtraction, extraction);
  assert.ok(validateSources0(wrongExtraction, source).includes('signature:' + NAMES[0]));
  assert.ok(validateSources0(extraction, source + '\naxiom profileAuthority : True\n')
    .includes('assumption'));
  assert.ok(validateSources0(extraction, source + '\nprivate def suppliedCoverage := true\n')
    .includes('shortcut-or-certificate'));
  assert.ok(validateSources0(extraction, source + '\ninstance extraAuthority : Inhabited Bool := ⟨true⟩\n')
    .includes('unaudited-form'));
});

test('M233 durable verification runs the new contracts, root axiom audit and regressions', async () => {
  const [packageText, surface, verifier, workflow] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  const auditPath = 'audits/lean-residual-terminal-profile-locality0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m233'], 'node --test ' + auditPath);
  assert.ok(surface.includes("'audit:m233': 'node --test " + auditPath + "'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test ' + auditPath));
  for (const path of [auditPath, 'docs/lean_residual_terminal_profile_locality.md']) {
    assert.equal(workflow.split("      - '" + path + "'").length - 1, 2, path + ' PR and main triggers');
  }
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M233_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-11-233';
const M233_MILESTONE = 'residual-terminal-profile-locality';
const M233_HASHES = Object.freeze({
  "PNP.DirectWire.extractTerminalSupport_eq_of_gateSelected_eq": "36de3a72b162389f2f8f5a3411a8fc000007cf55da00a39898b4b59d76957f05",
  "PNP.DirectWire.terminalAmbientSupportImplementation_eq_of_gateSelected_eq": "991e7712503e87f358b0d5a8fa89978d4a0552e28ce55fda31b3768fdf9e05a1",
  "PNP.DirectWire.terminalCandidateProfileObservation_eq_of_gateMembership_iff": "520e4c036df985fe6f97aa3c59fe3f7b14253fb85fec508464f077031da09d12",
  "PNP.DirectWire.terminalCandidateSaturate_profile_locality": "90f27df9e3ef24ce34a8ca9ebbe4658cd2c400652701b50f6847f6fbb44aa683",
  "PNP.DirectWire.terminalCandidateSaturate_profile_preserved": "059c535361ddcce72aae10142584704865fd604cdedc853c71b30e6a213f61da"
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
  const coverage = progress.formalArtefactCoverage;
  const proof = progress.proofCompletion;
  return [
    'Formal artefact coverage: ' + coverage.earnedRows + ' of ' + coverage.totalRows
      + ' current scoped publication rows earned.',
    'Risk-weighted proof completion estimate: ' + proof.percent + '%.',
    'Uncertainty range: ' + proof.uncertaintyLowPercent + '% to ' + proof.uncertaintyHighPercent + '%.',
    'Global gates closed: ' + progress.globalGates.filter(gate => gate.status === 'closed').length
      + ' of ' + progress.globalGates.length + '.',
  ];
}

test('M233 compiled types, standard axiom closures and emitted status match the reviewed interfaces', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M233_MILESTONE);
  assert.equal(row?.earned, true);
  assert.deepEqual(row.requiredTheorems, Object.keys(M233_HASHES));
  for (const [name, fingerprint] of Object.entries(M233_HASHES)) {
    const module = name === 'PNP.DirectWire.' + NAMES[0]
      ? 'PNP.ResidualTerminalSupportExtraction' : 'PNP.ResidualTerminalProfileLocality';
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, module, name);
      assert.deepEqual(declaration.axioms, ['Quot.sound', 'propext'], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), fingerprint);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], fingerprint);
  }
  assert.equal(status.leanResidualTerminalProfileLocalityFormalized, true);
  assert.equal(status.leanResidualTerminalProfileLocalityAxiomAuditPassed, true);
  assert.equal(status.leanResidualTerminalProfileLocalityAuditedDeclarationCount, 5);
  assert.equal(status.leanResidualTerminalProfileLocalityTheorem, 'PNP.DirectWire.' + NAMES[3]);
  assert.equal(status.leanResidualTerminalProfilePreservationTheorem, 'PNP.DirectWire.' + NAMES[4]);
  assert.equal(status.leanResidualTerminalProfileLocalityScope,
    'all-finite-candidates-executable-models-arbitrary-primitive-record-supports-computed-saturation-retained-ambient-profile-locality-and-preservation-only');
  for (const boundary of ['observer and profile model remain supplied data',
    'enumerates all subsets', 'retained-profile premise is necessary',
    'No fixed weighted checkpoint or global gate closes']) assert.ok(row.nonClaim.includes(boundary));
});

test('M233 publication rejects weakened, supplied, assumption-backed and widened substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M233_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M233_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = 'PNP.DirectWire.' + NAMES[3];
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M233_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M233_MILESTONE
    ? {...row, nonClaim:'Unconditional polynomial ZeroSlack is proved.'} : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M233 updates evidence coverage without unconditional, runtime or percentage credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M233_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  assert.match(review.rationale, /observer and profile model remain supplied/u);
  assert.match(review.rationale, /enumerates all subsets/u);
  assert.match(review.rationale, /retained-profile premise is necessary/u);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M233_COORDINATE) return;
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

test('M233 current core summaries preserve nonclaims, separate metrics and publication deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_residual_terminal_profile_locality.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of ['observer and profile model remain supplied data',
    'Influence enumerates all subsets and is not a polynomial-time construction.',
    'retained-profile premise is necessary']) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-11-retained-ambient-profile-preservation.md'));
  assert.ok(plan.includes('Publication decision: defer'));
  if (progress.asOfCoordinate !== M233_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_residual_terminal_profile_locality.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
