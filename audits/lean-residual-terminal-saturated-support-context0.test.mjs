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

const SOURCE = "lean/PNP/ResidualTerminalSaturatedSupportContext.lean";
const AUDIT = "lean-audit/PNPResidualTerminalSaturatedSupportContextAxiomAudit.lean";
const REGRESSION = "lean-regression/PNPResidualTerminalSaturatedSupportContext.lean";
const NAMES = [
  "terminalCandidateSaturate_boundary_isInput",
  "terminalCandidateSaturatePhysicalContext_size",
  "terminalCandidateSaturatePhysicalContext_equivalent",
  "terminalCandidateSaturatePhysicalContext_replace_equivalent",
  "terminalCandidateSaturatePhysicalSupport_slack_le"
];
const SIGNATURES = [
  "theorem terminalCandidateSaturate_boundary_isInput {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (wire : TerminalSupportWire inputs gates) (member : wire ∈ (extractTerminalSupport candidate (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)).boundary) : ∃ input : Fin inputs, wire = TerminalSupportWire.input input",
  "theorem terminalCandidateSaturatePhysicalContext_size {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) {replacementGates : Nat} (replacement : Candidate (extractTerminalSupport candidate (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)).boundary.length replacementGates (extractTerminalSupport candidate (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)).interface.length) : ((terminalCandidateSaturatePhysicalContext candidate model seed).plug replacement).program.size + (terminalSaturatePhysicalCharges (terminalCandidateSaturationSystem candidate model) seed).length = gates + replacementGates",
  "theorem terminalCandidateSaturatePhysicalContext_equivalent {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : let support := extractTerminalSupport candidate (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed) let context := terminalCandidateSaturatePhysicalContext candidate model seed Equivalent (context.plug support.extractedCandidate).program (context.plug support.extractedCandidate).directWireWord candidate.program candidate.directWireWord",
  "theorem terminalCandidateSaturatePhysicalContext_replace_equivalent {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) {replacementGates : Nat} (replacement : Candidate (extractTerminalSupport candidate (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)).boundary.length replacementGates (extractTerminalSupport candidate (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)).interface.length) : let support := extractTerminalSupport candidate (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed) let context := terminalCandidateSaturatePhysicalContext candidate model seed Equivalent replacement.program replacement.directWireWord support.extractedCandidate.program support.extractedCandidate.directWireWord → Equivalent (context.plug replacement).program (context.plug replacement).directWireWord candidate.program candidate.directWireWord",
  "theorem terminalCandidateSaturatePhysicalSupport_slack_le {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : residualSlack (extractTerminalSupport candidate (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)).extractedCandidate.toImplementation ≤ residualSlack candidate.toImplementation"
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
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|suppliedContext|callerFrame|closureCertificate|callerPartition)\b/u
    .test(compact0(source)), 'shortcut-or-certificate');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head => head.name)) ===
    JSON.stringify([NAMES[0], 'terminalPhysicalComplementRecords',
      'terminalCandidateSaturatePhysicalContext', ...NAMES.slice(1)]), 'public-interface');
  for (const [index, name] of NAMES.entries())
    require0(declarationHeader0(block0(source, name)) === SIGNATURES[index], 'signature:' + name);
  for (const dependency of [
    'terminalSaturateRecords_closed',
    'candidateGateSourceRequires_eq_usesWire',
    'physicalComplement_gateCount_partition candidate records',
    'extractTerminalSupport candidate (terminalPhysicalComplementRecords records)',
    'complementBoundary_gate_in_supportInterface candidate records producer boundaryMember',
    'physicalSupportEnvironment candidate records, physicalSupportContinuation candidate records',
    'physicalComplementInputBinding_induced candidate records input',
    'physicalGlobalOutput_gate_exposed',
    'physicalComplementRenamed_induced',
    'physicalSupportContinuation_induced candidate records input output',
    'compatibleReplacement_framed',
    'framedGlobalSlackLaw context support.extractedCandidate',
    'referenceMinimum_invariant',
  ]) require0(compact0(source).includes(dependency), 'computed-reconstruction-chain');
  return [...new Set(failures)];
}

test('M237 declaration headers retain named arguments and computed let-bindings in theorem types', () => {
  const head = 'theorem sample (model : M (width := width)) : let support := extract model let frame := build support Equivalent frame support';
  assert.equal(declarationHeader0(head + ' := by exact proof'), head);
  assert.equal(declarationHeader0(head.replace('width := width', 'width :=\n width')
    + ' :=\n by exact proof'), head);
  assert.equal(declarationHeader0('theorem broken (model : M (width := width) := by exact proof'), '');
});

test('M237 source derives the physical context and exact five arbitrary-dimension contracts', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE)), []);
});

test('M237 explicit root, axiom audit and both reviewed-name producers agree', async () => {
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
  assert.match(root, /^import PNP\.ResidualTerminalSaturatedSupportContext\s*$/mu);
});

test('M237 regressions cover physical partitions, nonclosed raw supports and replacement extremes', async () => {
  const regression = compact0(await text0(REGRESSION));
  for (const name of NAMES) assert.ok(regression.includes(name + ' '), name);
  for (const token of [
    'support.selectedGates = [0, 2]',
    'support.boundary = [.input 0]',
    'complement.selectedGates = [1, 3, 4]',
    'complement.boundary = [.input 1, .gate 2]',
    '(extractTerminalSupport candidate ([.gate 2] : List Record)).boundary',
    '([.gate 2, .gate 2] : List Record)',
    'Equivalent smaller.program smaller.directWireWord',
    'Equivalent larger.program larger.directWireWord',
    '(context.plug smaller).program.size = 3',
    '(context.plug larger).program.size = 6',
    'equivalentBool (emptyContext.plug emptySupport.extractedCandidate) candidate = true',
    'fullContext.continuation.program.size = 0',
    'zeroCandidate : Candidate 0 0 0',
    'constantCandidate : Candidate 0 1 1',
    'constantSupport.boundary = []',
  ]) assert.ok(regression.includes(token), token);
  assert.doesNotMatch(regression, /\b(?:sorry|admit|native_decide|Classical)\b/u);
});

test('M237 rejects supplied frames, finite-only contracts, altered outputs and omitted charge accounting', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    ['{inputs gates outputs profileWidth : Nat}', '{inputs gates outputs profileWidth : Fin 2}', 'signature:' + NAMES[0]],
    ['(seed : List', '(closureCertificate : True) (seed : List', 'signature:' + NAMES[0]],
    ['wire = TerminalSupportWire.input input', 'wire ≠ TerminalSupportWire.input input', 'signature:' + NAMES[0]],
    ['gates + replacementGates', 'gates', 'signature:' + NAMES[1]],
    ['Equivalent (context.plug support.extractedCandidate).program', 'True ∨ Equivalent (context.plug support.extractedCandidate).program', 'signature:' + NAMES[2]],
    ['candidate.program candidate.directWireWord := by', 'replacement.program replacement.directWireWord := by', 'signature:' + NAMES[3]],
    ['residualSlack candidate.toImplementation := by', 'residualSlack candidate.toImplementation + 1 := by', 'signature:' + NAMES[4]],
    ['physicalSupportEnvironment candidate records, physicalSupportContinuation candidate records',
      'callerFrame candidate model seed', 'computed-reconstruction-chain'],
    ['physicalComplementInputBinding_induced candidate records input',
      'closureCertificate', 'computed-reconstruction-chain'],
  ];
  for (const [before, after, category] of mutations) {
    assert.ok(source.includes(before), 'mutation anchor: ' + category);
    assert.ok(validateSource0(source.replaceAll(before, after)).includes(category), category);
  }
  assert.ok(validateSource0(source + '\naxiom contextAuthority : True\n').includes('assumption'));
  assert.ok(validateSource0(source + '\nprivate def suppliedContext := true\n').includes('shortcut-or-certificate'));
  assert.ok(validateSource0(source + '\ninstance extraAuthority : Inhabited Bool := ⟨true⟩\n').includes('unaudited-form'));
});

test('M237 durable verification includes source contracts, strict root audit and complete regressions', async () => {
  const [packageText, surface, verifier, workflow] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  const auditPath = 'audits/lean-residual-terminal-saturated-support-context0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m237'], 'node --test ' + auditPath);
  assert.ok(surface.includes("'audit:m237': 'node --test " + auditPath + "'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test ' + auditPath));
  for (const path of [auditPath, 'docs/lean_residual_terminal_saturated_support_context.md'])
    assert.equal(workflow.split("      - '" + path + "'").length - 1, 2);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M237_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-11-237';
const M237_MILESTONE = 'residual-terminal-saturated-support-context';
const M237_HASHES = Object.freeze({
  "PNP.DirectWire.terminalCandidateSaturate_boundary_isInput": "ec26a0d3919ff6dcf860984c92310bb49a1e5d608e863c05be8733603bd5b270",
  "PNP.DirectWire.terminalCandidateSaturatePhysicalContext_size": "f0bc6f7e663522a203de0c795593b631dbee10e250ea098434e7b43798182f17",
  "PNP.DirectWire.terminalCandidateSaturatePhysicalContext_equivalent": "86fb01c46c418f630fcf7d85b8b1706bb78c03e0df292f42c877673258555323",
  "PNP.DirectWire.terminalCandidateSaturatePhysicalContext_replace_equivalent": "b3404c4072cad4b15a86c1b1a58c83869093f77d1ca15684e61c7d0c22b74aca",
  "PNP.DirectWire.terminalCandidateSaturatePhysicalSupport_slack_le": "70f1c100034d2f37d8e2f6cc4f437b392e5f9c4adacfbb416fff852c763ec742"
});
const M237_STATUS_FIELDS = Object.freeze({
  "leanResidualTerminalSaturatedSupportContextFormalized": true,
  "leanResidualTerminalSaturatedSupportContextAxiomAuditPassed": true,
  "leanResidualTerminalSaturatedSupportContextAuditedDeclarationCount": 5,
  "leanResidualTerminalSaturatedSupportContextBoundaryTheorem": "PNP.DirectWire.terminalCandidateSaturate_boundary_isInput",
  "leanResidualTerminalSaturatedSupportContextSizeTheorem": "PNP.DirectWire.terminalCandidateSaturatePhysicalContext_size",
  "leanResidualTerminalSaturatedSupportContextReconstructionTheorem": "PNP.DirectWire.terminalCandidateSaturatePhysicalContext_equivalent",
  "leanResidualTerminalSaturatedSupportContextReplacementTheorem": "PNP.DirectWire.terminalCandidateSaturatePhysicalContext_replace_equivalent",
  "leanResidualTerminalSaturatedSupportContextSlackTheorem": "PNP.DirectWire.terminalCandidateSaturatePhysicalSupport_slack_le",
  "leanResidualTerminalSaturatedSupportContextScope": "all-finite-candidates-executable-models-seeds-production-saturated-supports-computed-physical-complement-context-primary-input-boundary-exact-gate-partition-whole-boolean-reconstruction-equivalent-replacement-and-physical-slack-only"
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

test('M237 compiled context, reconstruction, replacement and slack interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M237_MILESTONE);
  assert.equal(row?.earned, true);
  assert.deepEqual(row.requiredTheorems, Object.keys(M237_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, 'PNP.ResidualTerminalSaturatedSupportContext', name);
      assert.deepEqual(declaration.axioms, ['Quot.sound', 'propext'], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M237_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M237_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M237_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "physical Boolean replacement and slack laws",
  "not arbitrary raw supports or full-profile compatibility",
  "complete manuscript profile/materializer charge universe",
  "observer and profile model remain supplied data",
  "exhaustive finite reference constructions",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M237 publication rejects weakened, supplied, assumption-backed and widened context substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M237_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M237_MILESTONE).earned, false, name);
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
  assert.equal(rejected.milestones.find(row => row.id === M237_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M237_MILESTONE
    ? {...row, nonClaim:'The complete full-profile replacement and unconditional polynomial ZeroSlack are proved.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M237 adds physical-context coverage without full-profile, global, runtime or weighted-score credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M237_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "physical Boolean laws",
  "not arbitrary raw-support serializability or full-profile compatibility",
  "observer and profile model remain supplied data",
  "exhaustive finite reference constructions",
  "No fixed checkpoint or global gate changes"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M237_COORDINATE) return;
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

test('M237 current summaries distinguish physical from full-profile laws and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_residual_terminal_saturated_support_context.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "physical Boolean replacement and slack laws",
  "not arbitrary raw supports or full-profile compatibility",
  "observer and profile model remain supplied data",
  "exhaustive finite reference constructions",
  "no polynomial runtime is proved",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-11-computed-saturated-support-context.md'));
  assert.ok(plan.includes('Publication decision: defer'));
  if (progress.asOfCoordinate !== M237_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_residual_terminal_saturated_support_context.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
