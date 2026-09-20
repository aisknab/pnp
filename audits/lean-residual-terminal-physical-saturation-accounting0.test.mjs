import assert from 'node:assert/strict';
import { assertLeanWorkflowPathCoverage0 } from './lean-workflow-paths0.mjs';
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
const SOURCE = 'lean/PNP/ResidualTerminalPhysicalSaturationAccounting.lean';
const AUDIT = 'lean-audit/PNPResidualTerminalPhysicalSaturationAccountingAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPResidualTerminalPhysicalSaturationAccounting.lean';
const NAMES = [
  "terminalSaturateTrace_event_context",
  "terminalCandidateSaturateTrace_supportCostBalanced",
  "terminalCandidateSaturateTrace_event_owner",
  "terminalCandidateSaturateTrace_physicalObstruction",
  "terminalCandidateSaturateTrace_balance_or_physicalObstruction"
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

// Reviewed fixed, arbitrary-dimension theorem interfaces. Extra
// certificates, weaker conclusions and fixed-instance substitutes must fail.
const SIGNATURES = [
  "theorem terminalSaturateTrace_event_context {inputs gates outputs profileWidth : Nat} (system : TerminalSaturationSystem inputs gates outputs profileWidth) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth) (member : event ∈ (terminalSaturateTrace system seed).events) : event.dependent ∈ event.beforeRecords ∧ event.required ∉ event.beforeRecords",
  "theorem terminalCandidateSaturateTrace_supportCostBalanced {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth) (member : event ∈ (terminalSaturateTrace (terminalCandidateSaturationSystem candidate model) seed).events) : (terminalSaturationCostSnapshot candidate model event.afterRecords).supportSize = (terminalSaturationCostSnapshot candidate model event.beforeRecords).supportSize + terminalSaturationEventCost event",
  "theorem terminalCandidateSaturateTrace_event_owner {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth) (member : event ∈ (terminalSaturateTrace (terminalCandidateSaturationSystem candidate model) seed).events) : ∃ kind, event.kind? = some kind ∧ (kind, event.dependent) ∈ terminalSaturationEventOwners (terminalCandidateSaturationSystem candidate model) event",
  "theorem terminalCandidateSaturateTrace_physicalObstruction {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth) (member : event ∈ (terminalSaturateTrace (terminalCandidateSaturationSystem candidate model) seed).events) (failure : ¬TerminalTransparentSaturationStep candidate model event) : ∃ gate, event.required = TerminalPrimitiveRecord.gate gate ∧ ((terminalSaturationEventOwners (terminalCandidateSaturationSystem candidate model) event).length ≠ 1 ∨ (terminalSaturationCostSnapshot candidate model event.afterRecords).fullMinimum ≠ (terminalSaturationCostSnapshot candidate model event.beforeRecords).fullMinimum + 1 ∨ (terminalSaturationCostSnapshot candidate model event.beforeRecords).quotientMinimum + 1 < (terminalSaturationCostSnapshot candidate model event.afterRecords).quotientMinimum)",
  "theorem terminalCandidateSaturateTrace_balance_or_physicalObstruction {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : ((terminalSaturationCostSnapshot candidate model (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)).fullSlack = (terminalSaturationCostSnapshot candidate model (terminalSaturateTrace (terminalCandidateSaturationSystem candidate model) seed).normalizedSeed.reverse).fullSlack ∧ (terminalSaturationCostSnapshot candidate model (terminalSaturateTrace (terminalCandidateSaturationSystem candidate model) seed).normalizedSeed.reverse).projectionDefect ≤ (terminalSaturationCostSnapshot candidate model (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)).projectionDefect) ∨ ∃ first : TerminalFirstNontransparentSaturationStep candidate model (terminalSaturateTrace (terminalCandidateSaturationSystem candidate model) seed).events, classifyTerminalSaturationBalance candidate model seed = .firstNontransparent first ∧ ∃ gate, first.event.required = TerminalPrimitiveRecord.gate gate ∧ ((terminalSaturationEventOwners (terminalCandidateSaturationSystem candidate model) first.event).length ≠ 1 ∨ (terminalSaturationCostSnapshot candidate model first.event.afterRecords).fullMinimum ≠ (terminalSaturationCostSnapshot candidate model first.event.beforeRecords).fullMinimum + 1 ∨ (terminalSaturationCostSnapshot candidate model first.event.beforeRecords).quotientMinimum + 1 < (terminalSaturationCostSnapshot candidate model first.event.afterRecords).quotientMinimum)"
];
function validateSources0(executable, source) {
  const failures = [];
  const require0 = (condition, category) => { if (!condition) failures.push(category); };
  for (const value of [executable, source]) {
    require0(!hasLeanAssumptionDeclaration0(value), 'assumption');
    require0(!hasUnauditedLeanDeclarationForm0(value), 'unaudited-form');
    require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|suppliedBalance|suppliedOwner|callerRequires)\b/u
      .test(compact0(value)), 'shortcut-or-certificate');
  }
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head => head.name))
    === JSON.stringify(NAMES.slice(1)), 'public-interface');
  for (let index = 0; index < NAMES.length; index += 1) {
    require0(signature0(index === 0 ? executable : source, NAMES[index]) === SIGNATURES[index],
      'signature:' + NAMES[index]);
  }
  for (const dependency of [
    'replayRecords := final.costRecords',
    'records := terminalSaturateRecords system seed',
    'terminalSaturationTraceFinalState_contextsValid system seed',
    'terminalSaturationTracePending_generated_fresh state accounted supported',
    'terminalSaturationStep_finitelySupported system _ supported',
  ]) require0(compact0(executable).includes(dependency), 'actual-executor-context');
  for (const dependency of [
    'noDuplicatesSubset_length_le after (gate :: before)',
    'terminalSaturateTrace_event_context',
    'physicalSaturationSelectedGateCount_insert event.beforeRecords gate',
    'terminalCandidateSaturateTrace_metadata_transparent',
    'List.mem_filterMap.mpr',
    'classifyTerminalSaturationBalance candidate model seed',
    'terminalCandidateSaturateTrace_costSnapshot_eq candidate model seed',
    'terminalCandidateSaturateTrace_physicalObstruction',
  ]) require0(compact0(source).includes(dependency), 'physical-accounting-chain');
  return [...new Set(failures)];
}

test('M235 source contracts require fresh generated contexts, exact physical costs and real obstructions', async () => {
  assert.deepEqual(validateSources0(await text0(EXECUTABLE), await text0(SOURCE)), []);
});

test('M235 root audit and both reviewed-name producers cover the exact five theorem interfaces', async () => {
  const [executable, source, audit, inventorySource, root] = await Promise.all([
    text0(EXECUTABLE), text0(SOURCE), text0(AUDIT),
    text0('lean-audit/PNPTheoremInventory.lean'), text0('lean/PNP.lean'),
  ]);
  for (const [index, name] of NAMES.entries()) {
    const owner = index === 0 ? executable : source;
    assert.equal(explicitLeanDeclarationHeads0(owner).filter(head => head.name === name).length, 1, name);
    const fullName = 'PNP.DirectWire.' + name;
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item => item === fullName).length, 1, fullName);
    assert.equal(inventorySource.split(String.fromCharCode(96) + fullName + ',').length - 1, 1, fullName);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]), ['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match => match[1]),
    NAMES.map(name => 'PNP.DirectWire.' + name));
  assert.match(root, /^import PNP\.ResidualTerminalPhysicalSaturationAccounting\s*$/mu);
});

test('M235 regressions distinguish physical charges, competing owners and genuine minimum obstructions', async () => {
  const regression = compact0(await text0(REGRESSION));
  for (const name of NAMES) assert.ok(regression.includes(name + ' '), name);
  for (const token of [
    'candidate : Candidate 0 1 2',
    'pairTrace.events = [pairGateEvent]',
    'terminalSaturationEventOwners system pairGateEvent = [(.interfaceConsumer, secondInterface), (.interfaceConsumer, firstInterface)]',
    '[firstInterface, secondInterface, firstInterface, secondInterface]',
    '(terminalSaturateTrace system []).events = []',
    'some (gateRecord, .nonuniqueMaterializerOwner)',
    'some (gateRecord, .fullCostMismatch)',
    'missingDependentEvent ∉ pairTrace.events',
    'alreadyPresentEvent ∉ pairTrace.events',
    'terminalSaturateTrace_event_context system pairSeed missingDependentEvent member',
    'terminalSaturateTrace_event_context system pairSeed alreadyPresentEvent member',
  ]) assert.ok(regression.includes(token), token);
  assert.doesNotMatch(regression, /\b(?:sorry|admit|native_decide|Classical)\b/u);
});

test('M235 rejects finite, supplied, nonfresh and weakened obstruction substitutes', async () => {
  const executable = await text0(EXECUTABLE);
  const source = await text0(SOURCE);
  const mutations = [
    [0, '{inputs gates outputs profileWidth : Nat}', '{inputs gates outputs profileWidth : Fin 2}', 'signature:' + NAMES[0]],
    [0, '(seed : List', '(suppliedBalance : True) (seed : List', 'signature:' + NAMES[0]],
    [0, 'event.dependent ∈ event.beforeRecords ∧ event.required ∉ event.beforeRecords',
      'event.dependent ∉ event.beforeRecords ∧ event.required ∈ event.beforeRecords', 'signature:' + NAMES[0]],
    [0, 'replayRecords := final.costRecords', 'replayRecords := terminalSaturateRecords system seed', 'actual-executor-context'],
    [1, '(model : TerminalCandidateSaturationModel', '(suppliedOwner : True) (model : TerminalCandidateSaturationModel', 'signature:' + NAMES[1]],
    [1, 'terminalSaturationEventCost event := by', '0 := by', 'signature:' + NAMES[1]],
    [1, '(kind, event.dependent) ∈ terminalSaturationEventOwners',
      '(kind, event.dependent) ∉ terminalSaturationEventOwners', 'signature:' + NAMES[2]],
    [1, '(failure : ¬TerminalTransparentSaturationStep candidate model event)',
      '(failure : True)', 'signature:' + NAMES[3]],
    [1, '(terminalSaturateRecords', '(terminalCallerSuppliedRecords', 'signature:' + NAMES[4]],
    [1, 'classifyTerminalSaturationBalance candidate model seed = .firstNontransparent first',
      'True', 'signature:' + NAMES[4]],
    [1, 'physicalSaturationSelectedGateCount_insert event.beforeRecords gate',
      'callerChargeBalance event.beforeRecords gate', 'physical-accounting-chain'],
  ];
  for (const [owner, before, after, category] of mutations) {
    const original = owner === 0 ? executable : source;
    assert.ok(original.includes(before), 'mutation anchor: ' + category);
    const changed = original.replaceAll(before, after);
    assert.ok(validateSources0(owner === 0 ? changed : executable, owner === 1 ? changed : source)
      .includes(category), category);
  }
  assert.ok(validateSources0(executable, source + '\naxiom physicalAuthority : True\n').includes('assumption'));
  assert.ok(validateSources0(executable, source + '\nprivate def suppliedOwner := true\n')
    .includes('shortcut-or-certificate'));
  assert.ok(validateSources0(executable, source + '\ninstance extraAuthority : Inhabited Bool := ⟨true⟩\n')
    .includes('unaudited-form'));
});

test('M235 durable verification runs contracts, explicit-root axiom audit and regressions', async () => {
  const [packageText, surface, verifier, workflow] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  const auditPath = 'audits/lean-residual-terminal-physical-saturation-accounting0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m235'], 'node --test ' + auditPath);
  assert.ok(surface.includes("'audit:m235': 'node --test " + auditPath + "'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test ' + auditPath));
  for (const path of [auditPath, 'docs/lean_residual_terminal_physical_saturation_accounting.md']) {
    assertLeanWorkflowPathCoverage0(workflow, path);
  }
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M235_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-11-235';
const M235_MILESTONE = 'residual-terminal-physical-saturation-accounting';
const M235_HASHES = Object.freeze({
  "PNP.DirectWire.terminalSaturateTrace_event_context": "ee22de07094e37ab879f32dcf4cd29ca950e0ff9077b7b673478fecc77c14649",
  "PNP.DirectWire.terminalCandidateSaturateTrace_supportCostBalanced": "0b3ea6401032e726f0e43acba13490d9308e323109d0a1d3d1d33aae44080e66",
  "PNP.DirectWire.terminalCandidateSaturateTrace_event_owner": "ed16113c1dc85a8a77affb8544368ef558cfbccaa8cb6d435ef28f480e10ddb1",
  "PNP.DirectWire.terminalCandidateSaturateTrace_physicalObstruction": "7b0e659ae86824ee35ef8c5a449cf39b44768e7d5b78173f68fa9d1541e4f9ab",
  "PNP.DirectWire.terminalCandidateSaturateTrace_balance_or_physicalObstruction": "7d2d28cb4e283178d5d491a6213190a8895661a46bb0bf9973ba60d5b1a100c0"
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

test('M235 compiled types and axiom closures match all five reviewed interfaces and emitted status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M235_MILESTONE);
  assert.equal(row?.earned, true);
  assert.deepEqual(row.requiredTheorems, Object.keys(M235_HASHES));
  for (const [index, name] of row.requiredTheorems.entries()) {
    const module = index === 0 ? 'PNP.ResidualTerminalExecutableSaturation'
      : 'PNP.ResidualTerminalPhysicalSaturationAccounting';
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, module, name);
      assert.deepEqual(declaration.axioms, ['Quot.sound', 'propext'], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M235_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M235_HASHES[name]);
  }
  for (const [field,value] of Object.entries({
  "leanResidualTerminalPhysicalSaturationAccountingFormalized": true,
  "leanResidualTerminalPhysicalSaturationAccountingAxiomAuditPassed": true,
  "leanResidualTerminalPhysicalSaturationAccountingAuditedDeclarationCount": 5,
  "leanResidualTerminalSaturationEventContextTheorem": "PNP.DirectWire.terminalSaturateTrace_event_context",
  "leanResidualTerminalPhysicalSaturationSupportCostTheorem": "PNP.DirectWire.terminalCandidateSaturateTrace_supportCostBalanced",
  "leanResidualTerminalPhysicalSaturationActiveOwnerTheorem": "PNP.DirectWire.terminalCandidateSaturateTrace_event_owner",
  "leanResidualTerminalPhysicalSaturationObstructionTheorem": "PNP.DirectWire.terminalCandidateSaturateTrace_physicalObstruction",
  "leanResidualTerminalPhysicalSaturationBalanceOrObstructionTheorem": "PNP.DirectWire.terminalCandidateSaturateTrace_balance_or_physicalObstruction",
  "leanResidualTerminalPhysicalSaturationAccountingScope": "all-finite-systems-candidates-executable-models-seeds-generated-events-fresh-context-unit-physical-support-cost-active-owner-and-canonical-endpoint-first-obstruction-only"
}))
    assert.deepEqual(status[field],value,field);
  for (const boundary of ['observer and profile model remain supplied data',
    'exhaustive finite reference constructions', 'no polynomial runtime is proved',
    'Exact physical support growth does not establish full-minimum growth, a quotient bound, obligation discharge, complete closure safety or a global named route',
    'No fixed weighted checkpoint or global gate closes']) assert.ok(row.nonClaim.includes(boundary));
});

test('M235 publication rejects weakened, supplied, assumption-backed and widened substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M235_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M235_MILESTONE).earned, false, name);
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
  assert.equal(rejected.milestones.find(row => row.id === M235_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M235_MILESTONE
    ? {...row, nonClaim:'Unconditional polynomial ZeroSlack is proved.'} : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M235 adds coverage without global, unconditional, runtime or weighted-score credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M235_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  assert.match(review.rationale, /observer and profile model remain supplied data/u);
  assert.match(review.rationale, /exhaustive finite reference constructions/u);
  assert.match(review.rationale, /does not establish full-minimum growth, a quotient bound, obligation discharge, complete closure safety or a global named route/u);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M235_COORDINATE) return;
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

test('M235 current summaries retain the exact limits, separate metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_residual_terminal_physical_saturation_accounting.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of ['observer and profile model remain supplied data',
    'exhaustive finite reference constructions', 'no polynomial runtime is proved',
    'Exact physical support growth does not establish full-minimum growth, a quotient bound, obligation discharge, complete closure safety or a global named route'])
    assert.ok(documentation.includes(boundary), boundary);
  assert.ok(documentation.includes('does not construct or certify the manuscript-wide charge-ownership map'));
  assert.ok(documentation.includes('Active dependency ownership is not uniqueness'));
  const plan = prose0(await text0('docs/plans/2026-09-11-physical-saturation-accounting.md'));
  assert.ok(plan.includes('Publication decision: defer'));
  if (progress.asOfCoordinate !== M235_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_residual_terminal_physical_saturation_accounting.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
