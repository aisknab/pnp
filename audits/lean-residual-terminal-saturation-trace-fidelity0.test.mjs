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

const EXECUTABLE = 'lean/PNP/ResidualTerminalExecutableSaturation.lean';
const SOURCE = 'lean/PNP/ResidualTerminalSaturationTraceFidelity.lean';
const AUDIT = 'lean-audit/PNPResidualTerminalSaturationTraceFidelityAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPResidualTerminalSaturationTraceFidelity.lean';
const NAMES = [
  "terminalSaturateTrace_replayRecords_iff",
  "terminalSaturateTrace_event_valid",
  "terminalCandidateSaturateTrace_ambient_eq",
  "terminalCandidateSaturateTrace_costSnapshot_eq",
  "terminalCandidateSaturateTrace_metadata_transparent"
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

// Independently specified, arbitrary-dimension theorem interfaces. Extra
// certificates, weaker conclusions and fixed-instance substitutes must fail.
const SIGNATURES = [
  "theorem terminalSaturateTrace_replayRecords_iff {inputs gates outputs profileWidth : Nat} (system : TerminalSaturationSystem inputs gates outputs profileWidth) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) : record ∈ (terminalSaturateTrace system seed).replayRecords ↔ record ∈ terminalSaturateRecords system seed",
  "theorem terminalSaturateTrace_event_valid {inputs gates outputs profileWidth : Nat} (system : TerminalSaturationSystem inputs gates outputs profileWidth) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth) (member : event ∈ (terminalSaturateTrace system seed).events) : event.afterRecords = event.required :: event.beforeRecords ∧ ∃ kind, event.kind? = some kind ∧ system.requires kind event.dependent event.required = true",
  "theorem terminalCandidateSaturateTrace_ambient_eq {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : terminalAmbientSupportImplementation candidate (terminalSaturateTrace (terminalCandidateSaturationSystem candidate model) seed).replayRecords = terminalAmbientSupportImplementation candidate (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)",
  "theorem terminalCandidateSaturateTrace_costSnapshot_eq {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : terminalSaturationCostSnapshot candidate model (terminalSaturateTrace (terminalCandidateSaturationSystem candidate model) seed).replayRecords = { terminalSaturationCostSnapshot candidate model (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed) with records := (terminalSaturateTrace (terminalCandidateSaturationSystem candidate model) seed).replayRecords }",
  "theorem terminalCandidateSaturateTrace_metadata_transparent {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth) (member : event ∈ (terminalSaturateTrace (terminalCandidateSaturationSystem candidate model) seed).events) (metadata : ∀ gate, event.required ≠ TerminalPrimitiveRecord.gate gate) : TerminalTransparentSaturationStep candidate model event"
];
function validateSources0(executable, source) {
  const failures = [];
  const require0 = (condition, category) => { if (!condition) failures.push(category); };
  for (const value of [executable, source]) {
    require0(!hasLeanAssumptionDeclaration0(value), 'assumption');
    require0(!hasUnauditedLeanDeclarationForm0(value), 'unaudited-form');
    require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|suppliedBalance|callerRequires)\b/u
      .test(compact0(value)), 'shortcut-or-certificate');
  }
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head => head.name))
    === JSON.stringify(NAMES.slice(2)), 'public-interface');
  for (let index = 0; index < NAMES.length; index += 1) {
    require0(signature0(index < 2 ? executable : source, NAMES[index]) === SIGNATURES[index],
      'signature:' + NAMES[index]);
  }
  for (const dependency of [
    'replayRecords := final.costRecords',
    'records := terminalSaturateRecords system seed',
    'terminalSaturationTraceFinalState_costRecordsAccounted system seed record',
    'terminalSaturationTraceFinalState_erase system seed',
    'terminalSaturationTraceFinalState_rulesValid system seed',
    'terminalFirstSaturationRule?_valid system current.record record edge.1',
  ]) require0(compact0(executable).includes(dependency), 'actual-executor-chain');
  for (const dependency of [
    'terminalAmbientSupportImplementation_eq_of_gateSelected_eq candidate',
    'terminalSaturateTrace_replayRecords_iff',
    'terminalSaturateTrace_event_valid (terminalCandidateSaturationSystem candidate model)',
    'saturationSnapshot_eq_of_ambient_eq candidate model',
    'have zeroCost : terminalSaturationEventCost event = 0',
  ]) require0(compact0(source).includes(dependency), 'structural-cost-chain');
  return [...new Set(failures)];
}

test('M234 source contracts require actual replay, valid generated events and structural metadata balance', async () => {
  assert.deepEqual(validateSources0(await text0(EXECUTABLE), await text0(SOURCE)), []);
});

test('M234 root audit and both reviewed-name producers cover the exact five theorem interfaces', async () => {
  const [executable, source, audit, inventorySource, root] = await Promise.all([
    text0(EXECUTABLE), text0(SOURCE), text0(AUDIT),
    text0('lean-audit/PNPTheoremInventory.lean'), text0('lean/PNP.lean'),
  ]);
  assert.deepEqual([...REQUIRED_MILESTONE_THEOREMS0].sort(), [...REQUIRED_MILESTONE_THEOREMS0]);
  for (const [index, name] of NAMES.entries()) {
    const owner = index < 2 ? executable : source;
    assert.equal(explicitLeanDeclarationHeads0(owner).filter(head => head.name === name).length, 1, name);
    const fullName = 'PNP.DirectWire.' + name;
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item => item === fullName).length, 1, fullName);
    assert.equal(inventorySource.split(String.fromCharCode(96) + fullName + ',').length - 1, 1, fullName);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]), ['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match => match[1]),
    NAMES.map(name => 'PNP.DirectWire.' + name));
  assert.match(root, /^import PNP\.ResidualTerminalSaturationTraceFidelity\s*$/mu);
});

test('M234 regressions retain metadata constructors, actual observers, cycles and semantic counterexamples', async () => {
  const regression = compact0(await text0(REGRESSION));
  for (const name of NAMES) assert.ok(regression.includes(name + ' '), name);
  for (const token of [
    'implementation.candidate.semantics (fun _ => false) zero',
    '(terminalSaturateTrace system []).events = []',
    '[gateRecord, gateRecord]',
    'trace.events = [boundaryEvent, interfaceEvent, profileEvent]',
    'missingRuleEvent ∉ trace.events',
    'unrelatedAfterEvent ∉ trace.events',
    'wrongRuleEvent ∉ trace.events',
    'constantCandidate : Candidate 0 1 1',
    'physicalGateEvent ∈ (terminalSaturateTrace constantSystem [.interface zero]).events',
    'physicalGateEvent.afterRecords).fullMinimum = 0',
    'constantCandidate constantModel physicalGateEvent = false',
    '¬ Nonempty (TerminalOriginKernelObligationClosureSafe',
    'safe.obligationDischarged rfl',
    'cycleSystem.requires .origin cycleProfile cycleGate = true',
    'cycleSystem.requires .kernel cycleGate cycleProfile = true',
    '[cycleGate, cycleGate]).events = [cycleEvent]',
  ]) assert.ok(regression.includes(token), token);
  const forbidden = /\b(?:sorry|admit|native_decide|Classical)\b|\+native\b/u;
  assert.doesNotMatch(regression, forbidden);
  const nativeMutation = regression.replace('by decide', 'by decide +native');
  assert.notEqual(nativeMutation, regression);
  assert.match(nativeMutation, forbidden);
});

test('M234 rejects finite, supplied, canonical-field and unconditional-transparency substitutes', async () => {
  const executable = await text0(EXECUTABLE);
  const source = await text0(SOURCE);
  const mutations = [
    [0, '{inputs gates outputs profileWidth : Nat}', '{inputs outputs profileWidth : Nat} {gates : Fin 2}', 'signature:' + NAMES[0]],
    [0, '(seed : List', '(suppliedBalance : True) (seed : List', 'signature:' + NAMES[1]],
    [0, 'record ∈ (terminalSaturateTrace system seed).replayRecords ↔', 'record ∈ (terminalSaturateTrace system seed).records ↔', 'signature:' + NAMES[0]],
    [0, 'replayRecords := final.costRecords', 'replayRecords := terminalSaturateRecords system seed', 'actual-executor-chain'],
    [0, '∃ kind, event.kind? = some kind ∧', '∃ kind, event.kind? ≠ some kind ∧', 'signature:' + NAMES[1]],
    [1, '(seed : List', '(suppliedBalance : True) (seed : List', 'signature:' + NAMES[2]],
    [1, '(metadata : ∀ gate,', '(metadata : ∃ gate,', 'signature:' + NAMES[4]],
    [1, '(member : event ∈', '(member : event ∉', 'signature:' + NAMES[4]],
    [1, 'TerminalTransparentSaturationStep candidate model event := by', 'True := by', 'signature:' + NAMES[4]],
    [1, 'terminalSaturateTrace_event_valid', 'callerEventValidity', 'structural-cost-chain'],
  ];
  for (const [owner, before, after, category] of mutations) {
    const original = owner === 0 ? executable : source;
    assert.ok(original.includes(before), 'mutation anchor: ' + category);
    const changed = original.replaceAll(before, after);
    assert.ok(validateSources0(owner === 0 ? changed : executable, owner === 1 ? changed : source)
      .includes(category), category);
  }
  const metadataPremise =
    '    (metadata : ∀ gate, event.required ≠ TerminalPrimitiveRecord.gate gate)';
  assert.ok(source.includes(metadataPremise));
  assert.ok(validateSources0(executable, source.replace(metadataPremise, ''))
    .includes('signature:' + NAMES[4]));
  assert.ok(validateSources0(executable, source + '\naxiom traceAuthority : True\n').includes('assumption'));
  assert.ok(validateSources0(executable, source + '\nprivate def suppliedBalance := true\n')
    .includes('shortcut-or-certificate'));
  assert.ok(validateSources0(executable, source + '\ninstance extraAuthority : Inhabited Bool := ⟨true⟩\n')
    .includes('unaudited-form'));
});

test('M234 durable verification runs contracts, explicit-root axiom audit and regressions', async () => {
  const [packageText, surface, verifier, workflow] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  const auditPath = 'audits/lean-residual-terminal-saturation-trace-fidelity0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m234'], 'node --test ' + auditPath);
  assert.ok(surface.includes("'audit:m234': 'node --test " + auditPath + "'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test ' + auditPath));
  for (const path of [auditPath, 'docs/lean_residual_terminal_saturation_trace_fidelity.md']) {
    assert.equal(workflow.split("      - '"+path.replace(/^audits\/lean-[^/]+\.test\.mjs$/u,'audits/lean-*.test.mjs').replace(/^docs\/lean_[^/]+\.md$/u,'docs/lean_*.md').replace(/^lean\/.*$/u,'lean/**').replace(/^lean-audit\/.*$/u,'lean-audit/**').replace(/^lean-regression\/.*$/u,'lean-regression/**')+"'").length - 1, 2, path + ' PR and main triggers');
  }
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M234_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-11-234';
const M234_MILESTONE = 'residual-terminal-saturation-trace-fidelity';
const M234_HASHES = Object.freeze({
  "PNP.DirectWire.terminalSaturateTrace_replayRecords_iff": "7f80f837010adcb3f2fae342d28dd62abc409952246ae543f7b42d45e5ad4fa4",
  "PNP.DirectWire.terminalSaturateTrace_event_valid": "c1b87935414b4d1f64511851d7a2f16950aabf4a941ecc67f2d377f8c9435733",
  "PNP.DirectWire.terminalCandidateSaturateTrace_ambient_eq": "9c95df1a18426898db16b49a2181726decbb73bd693034227e0046b98f8dbff5",
  "PNP.DirectWire.terminalCandidateSaturateTrace_costSnapshot_eq": "a71b030f39a2e1a75045b984451b286d3ed66101bebea61d97693f9ba23ba6a5",
  "PNP.DirectWire.terminalCandidateSaturateTrace_metadata_transparent": "e30fc653246ef6cd59ec517a9667f819ad013811f758aa855aa9f02a5ee6fc76"
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

test('M234 compiled types and axiom closures match all five reviewed interfaces and emitted status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M234_MILESTONE);
  assert.equal(row?.earned, true);
  assert.deepEqual(row.requiredTheorems, Object.keys(M234_HASHES));
  for (const [index, name] of row.requiredTheorems.entries()) {
    const module = index < 2 ? 'PNP.ResidualTerminalExecutableSaturation'
      : 'PNP.ResidualTerminalSaturationTraceFidelity';
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, module, name);
      assert.deepEqual(declaration.axioms, ['Quot.sound', 'propext'], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M234_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M234_HASHES[name]);
  }
  assert.equal(status.leanResidualTerminalSaturationTraceFidelityFormalized, true);
  assert.equal(status.leanResidualTerminalSaturationTraceFidelityAxiomAuditPassed, true);
  assert.equal(status.leanResidualTerminalSaturationTraceFidelityAuditedDeclarationCount, 5);
  assert.equal(status.leanResidualTerminalSaturationReplayTheorem, 'PNP.DirectWire.' + NAMES[0]);
  assert.equal(status.leanResidualTerminalSaturationEventValidityTheorem, 'PNP.DirectWire.' + NAMES[1]);
  assert.equal(status.leanResidualTerminalSaturationMetadataTransparencyTheorem, 'PNP.DirectWire.' + NAMES[4]);
  assert.equal(status.leanResidualTerminalSaturationTraceFidelityScope,
    'all-finite-systems-candidates-executable-models-seeds-generated-events-actual-replay-ambient-endpoint-cost-snapshot-and-metadata-transparency-only');
  for (const boundary of ['observer and profile model remain supplied data',
    'exhaustive finite reference constructions', 'no polynomial runtime is proved',
    'Metadata cost balance does not establish physical-gate transparency, obligation discharge or complete closure safety',
    'No fixed weighted checkpoint or global gate closes']) assert.ok(row.nonClaim.includes(boundary));
});

test('M234 publication rejects weakened, supplied, assumption-backed and widened substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M234_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M234_MILESTONE).earned, false, name);
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
  assert.equal(rejected.milestones.find(row => row.id === M234_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M234_MILESTONE
    ? {...row, nonClaim:'Unconditional polynomial ZeroSlack is proved.'} : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M234 adds coverage without global, unconditional, runtime or weighted-score credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M234_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  assert.match(review.rationale, /observer and profile model remain supplied data/u);
  assert.match(review.rationale, /exhaustive finite reference constructions/u);
  assert.match(review.rationale, /does not establish physical-gate transparency, obligation discharge or complete closure safety/u);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M234_COORDINATE) return;
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

test('M234 current summaries retain the exact limits, separate metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_residual_terminal_saturation_trace_fidelity.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of ['observer and profile model remain supplied data',
    'exhaustive finite reference constructions', 'no polynomial runtime is proved',
    'Metadata cost balance does not establish physical-gate transparency, obligation discharge or complete closure safety'])
    assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-11-saturation-trace-fidelity.md'));
  assert.ok(plan.includes('Publication decision: defer'));
  if (progress.asOfCoordinate !== M234_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_residual_terminal_saturation_trace_fidelity.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
