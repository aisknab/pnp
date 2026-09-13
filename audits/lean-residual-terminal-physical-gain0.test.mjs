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

const SOURCE = "lean/PNP/ResidualTerminalPhysicalGain.lean";
const AUDIT = "lean-audit/PNPResidualTerminalPhysicalGainAxiomAudit.lean";
const REGRESSION = "lean-regression/PNPResidualTerminalPhysicalGain.lean";
const NAMES = [
  "terminalCandidateSaturatePhysicalMinimumReplacement_equivalent",
  "terminalCandidateSaturatePhysicalMinimumReplacement_size_gain",
  "terminalCandidateSaturatePhysicalMinimumReplacement_slack_gain",
  "findTerminalCandidatePhysicalGain_sound",
  "findTerminalCandidatePhysicalGain_eq_none_iff"
];
const SIGNATURES = [
  "theorem terminalCandidateSaturatePhysicalMinimumReplacement_equivalent {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : let replacement := terminalCandidateSaturatePhysicalMinimumReplacement candidate model seed Equivalent replacement.candidate.program replacement.candidate.directWireWord candidate.program candidate.directWireWord",
  "theorem terminalCandidateSaturatePhysicalMinimumReplacement_size_gain {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : (terminalCandidateSaturatePhysicalMinimumReplacement candidate model seed).gateCount + terminalSupportLocalGain candidate (terminalCandidateSaturationSystem candidate model) seed = gates",
  "theorem terminalCandidateSaturatePhysicalMinimumReplacement_slack_gain {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : residualSlack (terminalCandidateSaturatePhysicalMinimumReplacement candidate model seed) + terminalSupportLocalGain candidate (terminalCandidateSaturationSystem candidate model) seed = residualSlack candidate.toImplementation",
  "theorem findTerminalCandidatePhysicalGain_sound {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (result : Implementation inputs outputs) (foundAt : findTerminalCandidatePhysicalGain candidate model = some result) : ∃ found : TerminalCandidateProperPositiveSupport candidate model, findTerminalCandidateProperPositiveSupport candidate model = some found ∧ found.seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth ∧ TerminalSupportProper candidate (terminalCandidateSaturationSystem candidate model) found.seed ∧ 0 < terminalSupportLocalGain candidate (terminalCandidateSaturationSystem candidate model) found.seed ∧ result = terminalCandidateSaturatePhysicalMinimumReplacement candidate model found.seed ∧ Equivalent result.candidate.program result.candidate.directWireWord candidate.program candidate.directWireWord ∧ result.gateCount + terminalSupportLocalGain candidate (terminalCandidateSaturationSystem candidate model) found.seed = gates ∧ residualSlack result + terminalSupportLocalGain candidate (terminalCandidateSaturationSystem candidate model) found.seed = residualSlack candidate.toImplementation ∧ result.gateCount < gates ∧ residualSlack result < residualSlack candidate.toImplementation",
  "theorem findTerminalCandidatePhysicalGain_eq_none_iff {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) : findTerminalCandidatePhysicalGain candidate model = none ↔ ∀ seed, seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth → ¬(TerminalSupportProper candidate (terminalCandidateSaturationSystem candidate model) seed ∧ TerminalSupportPositive candidate (terminalCandidateSaturationSystem candidate model) seed)"
];
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = value => stripLeanCommentsAndStrings0(value).replace(/\s+/gu, ' ').trim();
function block0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex(head => head.name === name);
  return index < 0 ? '' : source.slice(heads[index].index, heads[index + 1]?.index ?? source.length);
}
function declarationHeader0(source) {
  const clean = stripLeanCommentsAndStrings0(source);
  const openings = new Map([['(', ')'], ['[', ']'], ['{', '}'], ['⟨', '⟩']]);
  const closings = new Set(openings.values());
  const stack = [];
  for (let index = 0; index < clean.length; index += 1) {
    const char = clean[index];
    if (openings.has(char)) stack.push(openings.get(char));
    else if (closings.has(char)) {
      if (stack.pop() !== char) return '';
    } else if (char === ':' && clean[index + 1] === '=' && stack.length === 0
        && /^\s*by\b/u.test(clean.slice(index + 2))) {
      return compact0(clean.slice(0, index));
    }
  }
  return '';
}
function validateSource0(source) {
  const failures = [];
  const require0 = (condition, category) => { if (!condition) failures.push(category); };
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|suppliedSearch|suppliedReplacement|callerSeed|callerFrame|callerCertificate)\b/u
    .test(compact0(source)), 'shortcut-or-certificate');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]))
    === JSON.stringify(['PNP.ResidualTerminalSaturatedSupportContext']), 'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head => head.name)) ===
    JSON.stringify(['terminalCandidateSaturatePhysicalMinimumReplacement', ...NAMES.slice(0, 3),
      'findTerminalCandidatePhysicalGain', ...NAMES.slice(3)]), 'public-interface');
  for (const [index, name] of NAMES.entries())
    require0(declarationHeader0(block0(source, name)) === SIGNATURES[index], 'signature:' + name);
  const construction = compact0(block0(source, 'terminalCandidateSaturatePhysicalMinimumReplacement'));
  for (const dependency of [
    'extractSaturatedTerminalSupport candidate (terminalCandidateSaturationSystem candidate model) seed',
    'terminalCandidateSaturatePhysicalContext candidate model seed',
    '(context.plug support.extractedCandidate.referenceMinimumReplacement).toImplementation',
  ]) require0(construction.includes(dependency), 'computed-minimum-context');
  const search = compact0(block0(source, 'findTerminalCandidatePhysicalGain'));
  for (const dependency of [
    '(findTerminalCandidateProperPositiveSupport candidate model).map fun found =>',
    'terminalCandidateSaturatePhysicalMinimumReplacement candidate model found.seed',
  ]) require0(search.includes(dependency), 'computed-search');
  for (const dependency of [
    'terminalCandidateSaturatePhysicalContext_replace_equivalent',
    'terminalCandidateSaturatePhysicalContext_size',
    'terminalCandidateSaturatePhysicalCharges_size',
    'referenceMinimum_le_target',
    'referenceMinimum_invariant',
    'physicalGain_size_balance',
    'physicalGain_slack_balance',
    'physicalGain_strict_of_positive',
    'findTerminalProperPositiveSupport_eq_none_iff',
  ]) require0(compact0(source).includes(dependency), 'computed-gain-chain');
  return [...new Set(failures)];
}

test('M238 declaration headers retain named arguments and computed let-bindings', () => {
  const head = 'theorem sample (model : M (width := width)) : let replacement := compute model Equivalent replacement model';
  assert.equal(declarationHeader0(head + ' := by exact proof'), head);
  assert.equal(declarationHeader0(head.replace('width := width', 'width :=\n width')
    + ' :=\n by exact proof'), head);
  assert.equal(declarationHeader0('theorem broken (model : M (width := width) := by exact proof'), '');
});

test('M238 derives the actual reference replacement and exact five universal contracts', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE)), []);
});

test('M238 explicit root, axiom audit and both reviewed-name producers agree', async () => {
  const [source, audit, inventorySource, root] = await Promise.all([
    text0(SOURCE), text0(AUDIT), text0('lean-audit/PNPTheoremInventory.lean'), text0('lean/PNP.lean'),
  ]);
  for (const name of NAMES) {
    assert.equal(explicitLeanDeclarationHeads0(source).filter(head => head.name === name).length, 1);
    const fullName = 'PNP.DirectWire.' + name;
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item => item === fullName).length, 1);
    assert.equal(inventorySource.split(String.fromCharCode(96) + fullName + ',').length - 1, 1);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]), ['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match => match[1]),
    NAMES.map(name => 'PNP.DirectWire.' + name));
  assert.match(root, /^import PNP\.ResidualTerminalPhysicalGain\s*$/mu);
});

test('M238 regressions exercise actual search, exact gain and the nonminimal failure boundary', async () => {
  const regression = compact0(await text0(REGRESSION));
  for (const name of NAMES) assert.ok(regression.includes(name + ' '), name);
  for (const token of [
    'gainSupport.selectedGates = [0, 1]',
    'gainSupport.boundary = [.input 0]',
    'gainSupport.interface = [1]',
    'terminalSupportLocalGain gainCandidate gainSystem gainSeed = 2',
    'gainReplacement.gateCount = 1',
    'equivalentBool gainReplacement.candidate gainCandidate = true',
    'residualSlack gainCandidate.toImplementation = 2',
    'residualSlack gainReplacement = 0',
    'gainCandidate : Candidate 1 3 3',
    'if output.val = 2 then .input 0 else .gate 2',
    '(findTerminalCandidatePhysicalGain searchCandidate searchModel).map (fun result => result.gateCount) = some 1',
    'searchCandidate : Candidate 1 2 1',
    '([.gate 1, .gate 1] : List GainRecord)',
    'residualSlack doubleCandidate.toImplementation = 2',
    '(findTerminalCandidatePhysicalGain doubleCandidate doubleModel).isSome = false',
    '([] : List GainRecord)).gateCount = 3',
    'zeroCandidate : Candidate 0 0 0',
    '(findTerminalCandidatePhysicalGain zeroCandidate zeroModel).isSome = false',
    'wireCandidate : Candidate 1 0 2',
    '(findTerminalCandidatePhysicalGain wireCandidate wireModel).isSome = false',
  ]) assert.ok(regression.includes(token), token);
  assert.doesNotMatch(regression, /\b(?:sorry|admit|native_decide|Classical)\b/u);
});

test('M238 rejects supplied results, weakened descent, finite substitutes and overstated failure', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    ['{inputs gates outputs profileWidth : Nat}', '{inputs gates outputs profileWidth : Fin 2}', 'signature:' + NAMES[0]],
    ['(seed : List', '(callerCertificate : True) (seed : List', 'signature:' + NAMES[0]],
    ['Equivalent replacement.candidate.program', 'True ∨ Equivalent replacement.candidate.program', 'signature:' + NAMES[0]],
    ['seed = gates := by', 'seed ≤ gates := by', 'signature:' + NAMES[1]],
    ['residualSlack candidate.toImplementation := by', 'residualSlack candidate.toImplementation + 1 := by', 'signature:' + NAMES[2]],
    ['found.seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth ∧', 'True ∧', 'signature:' + NAMES[3]],
    ['result.gateCount < gates ∧', 'result.gateCount ≤ gates ∧', 'signature:' + NAMES[3]],
    ['∀ seed, seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth →', '∀ seed, False →', 'signature:' + NAMES[4]],
    ['(context.plug support.extractedCandidate.referenceMinimumReplacement).toImplementation',
      '(context.plug support.extractedCandidate).toImplementation', 'computed-minimum-context'],
    ['(findTerminalCandidateProperPositiveSupport candidate model).map fun found =>',
      '(suppliedSearch candidate model).map fun found =>', 'computed-search'],
  ];
  for (const [before, after, category] of mutations) {
    assert.ok(source.includes(before), 'mutation anchor: ' + category);
    assert.ok(validateSource0(source.replaceAll(before, after)).includes(category), category);
  }
  assert.ok(validateSource0(source + '\naxiom gainAuthority : True\n').includes('assumption'));
  assert.ok(validateSource0(source + '\nprivate def suppliedReplacement := true\n').includes('shortcut-or-certificate'));
  assert.ok(validateSource0(source + '\ninstance extraAuthority : Inhabited Bool := ⟨true⟩\n').includes('unaudited-form'));
});

test('M238 durable verification includes source contracts, strict root audit and complete regressions', async () => {
  const [packageText, surface, verifier, workflow] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  const auditPath = 'audits/lean-residual-terminal-physical-gain0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m238'], 'node --test ' + auditPath);
  assert.ok(surface.includes("'audit:m238': 'node --test " + auditPath + "'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test ' + auditPath));
  for (const path of [auditPath, 'docs/lean_residual_terminal_physical_gain.md'])
    assert.equal(workflow.split("      - '"+path.replace(/^audits\/lean-[^/]+\.test\.mjs$/u,'audits/lean-*.test.mjs').replace(/^docs\/lean_[^/]+\.md$/u,'docs/lean_*.md').replace(/^lean\/.*$/u,'lean/**').replace(/^lean-audit\/.*$/u,'lean-audit/**').replace(/^lean-regression\/.*$/u,'lean-regression/**')+"'").length - 1, 2);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});


const M238_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-12-238';
const M238_MILESTONE = 'residual-terminal-physical-gain';
const M238_HASHES = Object.freeze({
  "PNP.DirectWire.terminalCandidateSaturatePhysicalMinimumReplacement_equivalent": "e1da67101c515204dd045a2f04fb5e8b50cd2c930eb6ae526c3192657180af4a",
  "PNP.DirectWire.terminalCandidateSaturatePhysicalMinimumReplacement_size_gain": "3b1b137f09a7681341f12a83c5de1713d4116c1baa6f98ac0300da039342cf31",
  "PNP.DirectWire.terminalCandidateSaturatePhysicalMinimumReplacement_slack_gain": "96dac6e6f5ecc546b311cf0bab666075da5143cd31563aa1e09eaf9cfba4de66",
  "PNP.DirectWire.findTerminalCandidatePhysicalGain_sound": "f5e4ab7db43a4f9476b036cbed4d58aa0a5a46889ff738e76c71bf354ea79479",
  "PNP.DirectWire.findTerminalCandidatePhysicalGain_eq_none_iff": "de932d3dd29285c67a55cce7e67378b4ecd805f7daf84516e8c0b9ed3cc7f0fd"
});
const M238_STATUS_FIELDS = Object.freeze({
  "leanResidualTerminalPhysicalGainFormalized": true,
  "leanResidualTerminalPhysicalGainAxiomAuditPassed": true,
  "leanResidualTerminalPhysicalGainAuditedDeclarationCount": 5,
  "leanResidualTerminalPhysicalGainEquivalenceTheorem": "PNP.DirectWire.terminalCandidateSaturatePhysicalMinimumReplacement_equivalent",
  "leanResidualTerminalPhysicalGainSizeTheorem": "PNP.DirectWire.terminalCandidateSaturatePhysicalMinimumReplacement_size_gain",
  "leanResidualTerminalPhysicalGainSlackTheorem": "PNP.DirectWire.terminalCandidateSaturatePhysicalMinimumReplacement_slack_gain",
  "leanResidualTerminalPhysicalGainSearchSoundnessTheorem": "PNP.DirectWire.findTerminalCandidatePhysicalGain_sound",
  "leanResidualTerminalPhysicalGainSearchFailureTheorem": "PNP.DirectWire.findTerminalCandidatePhysicalGain_eq_none_iff",
  "leanResidualTerminalPhysicalGainScope": "all-finite-candidates-executable-models-production-saturated-supports-computed-reference-minimum-replacements-exact-physical-size-and-slack-descent-and-complete-proper-positive-search-only"
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

test('M238 compiled gain, size/slack descent and search interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M238_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M238_COORDINATE)
    assert.equal(map.coordinate, 'PNP-FORMAL-PUBLICATION-MAP-2026-09-12-238');
  assert.deepEqual(row.requiredTheorems, Object.keys(M238_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, 'PNP.ResidualTerminalPhysicalGain', name);
      assert.deepEqual(declaration.axioms, ['Quot.sound', 'propext'], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M238_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M238_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M238_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "physical Boolean reference gain-realization and search-failure laws",
  "not full-profile replacement compatibility or a complete named global route",
  "observer and profile model remain supplied data",
  "exhaustive finite reference constructions",
  "Failure of the proper-support search does not imply global minimality or ZeroSlack",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M238 publication rejects weakened, supplied, assumption-backed and widened gain/search substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M238_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M238_MILESTONE).earned, false, name);
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
  assert.equal(rejected.milestones.find(row => row.id === M238_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M238_MILESTONE
    ? {...row, nonClaim:'The complete full-profile replacement and unconditional polynomial ZeroSlack are proved.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M238 adds physical-gain coverage without full-profile, global, runtime or weighted-score credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M238_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "physical Boolean laws",
  "not full-profile compatibility, global materializer ownership",
  "observer remains supplied",
  "influence, seed search and reference minima remain exhaustive",
  "canonical proper positive supports rather than proving global minimality",
  "No fixed checkpoint or global gate changes"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M238_COORDINATE) return;
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

test('M238 current summaries distinguish physical gain from global route completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_residual_terminal_physical_gain.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "physical Boolean reference gain-realization laws",
  "not full-profile replacement compatibility or a complete named global route",
  "observer and profile model remain supplied data",
  "exhaustive finite reference constructions",
  "Finite termination and a smaller output do not prove a polynomial encoded-size or runtime bound",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-12-computed-proper-support-physical-gain.md'));
  assert.ok(plan.includes('Publication decision: defer'));
  if (progress.asOfCoordinate !== M238_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_residual_terminal_physical_gain.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
