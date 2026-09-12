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

const SOURCE = 'lean/PNP/ResidualTerminalPhysicalChargeLedger.lean';
const AUDIT = 'lean-audit/PNPResidualTerminalPhysicalChargeLedgerAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPResidualTerminalPhysicalChargeLedger.lean';
const NAMES = [
  "terminalSaturatePhysicalCharges_nodup",
  "terminalSaturatePhysicalCharges_complete",
  "terminalSaturatePhysicalCharges_provenance",
  "terminalSaturatePhysicalChargeProvenance?_iff",
  "terminalCandidateSaturatePhysicalCharges_size"
];
const SIGNATURES = [
  "theorem terminalSaturatePhysicalCharges_nodup {inputs gates outputs profileWidth : Nat} (system : TerminalSaturationSystem inputs gates outputs profileWidth) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : ((terminalSaturatePhysicalCharges system seed).map TerminalPhysicalCharge.gate).Nodup",
  "theorem terminalSaturatePhysicalCharges_complete {inputs gates outputs profileWidth : Nat} (system : TerminalSaturationSystem inputs gates outputs profileWidth) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (gate : Fin gates) : gate ∈ (terminalSaturatePhysicalCharges system seed).map TerminalPhysicalCharge.gate ↔ TerminalPrimitiveRecord.gate gate ∈ terminalSaturateRecords system seed",
  "theorem terminalSaturatePhysicalCharges_provenance {inputs gates outputs profileWidth : Nat} (system : TerminalSaturationSystem inputs gates outputs profileWidth) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (charge : TerminalPhysicalCharge inputs gates outputs profileWidth) (member : charge ∈ terminalSaturatePhysicalCharges system seed) : (charge.provenance = .seed ∧ TerminalPrimitiveRecord.gate charge.gate ∈ (terminalSaturateTrace system seed).normalizedSeed.reverse) ∨ ∃ event, event ∈ (terminalSaturateTrace system seed).events ∧ ∃ kind, charge.provenance = .generated kind event.dependent ∧ event.required = TerminalPrimitiveRecord.gate charge.gate ∧ event.kind? = some kind ∧ system.requires kind event.dependent (TerminalPrimitiveRecord.gate charge.gate) = true ∧ event.dependent ∈ event.beforeRecords ∧ TerminalPrimitiveRecord.gate charge.gate ∉ event.beforeRecords",
  "theorem terminalSaturatePhysicalChargeProvenance?_iff {inputs gates outputs profileWidth : Nat} (system : TerminalSaturationSystem inputs gates outputs profileWidth) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (gate : Fin gates) (provenance : TerminalPhysicalChargeProvenance inputs gates outputs profileWidth) : terminalSaturatePhysicalChargeProvenance? system seed gate = some provenance ↔ (⟨gate, provenance⟩ : TerminalPhysicalCharge inputs gates outputs profileWidth) ∈ terminalSaturatePhysicalCharges system seed",
  "theorem terminalCandidateSaturatePhysicalCharges_size {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : (terminalSaturationCostSnapshot candidate model (terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)).supportSize = (terminalSaturatePhysicalCharges (terminalCandidateSaturationSystem candidate model) seed).length"
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
    } else if (char === ':' && clean[index + 1] === '=' && stack.length === 0) {
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
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|suppliedLedger|suppliedOwner|callerCharges|callerCoverage)\b/u
    .test(compact0(source)), 'shortcut-or-certificate');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head => head.name)) ===
    JSON.stringify(['TerminalPhysicalChargeProvenance', 'TerminalPhysicalCharge',
      'terminalSaturatePhysicalCharges', 'terminalSaturatePhysicalChargeProvenance?', ...NAMES]),
    'public-interface');
  for (const [index, name] of NAMES.entries())
    require0(declarationHeader0(block0(source, name)) === SIGNATURES[index], 'signature:' + name);
  for (const dependency of [
    'terminalInitialPhysicalCharges initial ++ events.filterMap terminalEventPhysicalCharge?',
    'terminalPhysicalChargeLedger trace.normalizedSeed.reverse trace.events',
    'match event.required, event.kind? with',
    'some ⟨gate, .generated kind event.dependent⟩',
    'terminalSaturateTrace_eventsLinked system seed',
    'terminalSaturateTrace_replayRecords_iff system seed',
    'terminalSaturateTrace_event_context system seed event eventMember',
    'terminalPhysicalChargeLookup_iff gate provenance (terminalSaturatePhysicalCharges system seed)',
    'noDuplicatesSubset_length_le',
    'extractTerminalSupport_gateCount',
  ]) require0(compact0(source).includes(dependency), 'actual-ledger-chain');
  require0(compact0(source).split('terminalInitialPhysicalCharges initial ++').length - 1 === 1,
    'actual-ledger-chain');
  return [...new Set(failures)];
}

test('M236 declaration-header parsing retains named arguments and the complete theorem type', () => {
  const head = 'theorem exampleName (model : M (width := width)) : True';
  assert.equal(declarationHeader0(head + ' := by exact True.intro'), head);
  assert.equal(declarationHeader0(head.replace('width := width', 'width :=\n width')
    + ' :=\n True.intro'), head);
  assert.equal(declarationHeader0('theorem broken (model : M (width := width) := by exact True.intro'), '');
});

test('M236 source requires the complete computed physical partition and exact five general contracts', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE)), []);
});

test('M236 root audit and both reviewed-name producers cover the same five general interfaces', async () => {
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
  assert.match(root, /^import PNP\.ResidualTerminalPhysicalChargeLedger\s*$/mu);
});

test('M236 regressions distinguish assigned provenance, requesters, seed charges, cycles and empty supports', async () => {
  const regression = compact0(await text0(REGRESSION));
  for (const name of NAMES) assert.ok(regression.includes(name + ' '), name);
  for (const token of [
    '(terminalSaturationEventOwners system event).length = 2',
    '(terminalSaturationCostSnapshot candidate model event.afterRecords).fullMinimum = 1',
    '(terminalSaturationCostSnapshot candidate model event.afterRecords).quotientMinimum = 1',
    'some (gateRecord, .nonuniqueMaterializerOwner)',
    'terminalSaturatePhysicalCharges system [gateRecord, firstInterface, secondInterface]',
    '[firstInterface, secondInterface, firstInterface]',
    'terminalSaturatePhysicalChargeProvenance? system [] gateZero = none',
    'terminalSaturatePhysicalCharges cycleSystem seed = expected',
    '(terminalSaturateTrace cycleSystem seed).events.length = 3',
    'TerminalPrimitiveRecord.profile profileZero ∈ terminalSaturateRecords cycleSystem seed',
    'emptySystem : TerminalSaturationSystem 0 0 0 0',
    'metadataSystem : TerminalSaturationSystem 0 0 0 1',
  ]) assert.ok(regression.includes(token), token);
  assert.doesNotMatch(regression, /\b(?:sorry|admit|native_decide|Classical)\b/u);
});

test('M236 rejects supplied, finite, incomplete, duplicated and weakened charge-ledger substitutes', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    ['{inputs gates outputs profileWidth : Nat}', '{inputs gates outputs profileWidth : Fin 2}', 'signature:' + NAMES[0]],
    ['(seed : List', '(suppliedLedger : True) (seed : List', 'signature:' + NAMES[0]],
    ['.map TerminalPhysicalCharge.gate).Nodup', '.map TerminalPhysicalCharge.gate).isEmpty', 'signature:' + NAMES[0]],
    ['TerminalPrimitiveRecord.gate gate ∈ terminalSaturateRecords system seed',
      'TerminalPrimitiveRecord.gate gate ∈ seed', 'signature:' + NAMES[1]],
    ['event.dependent ∈ event.beforeRecords', 'event.dependent ∉ event.beforeRecords', 'signature:' + NAMES[2]],
    ['event.kind? = some kind', 'event.kind? = none', 'signature:' + NAMES[2]],
    ['= some provenance ↔', '= some provenance →', 'signature:' + NAMES[3]],
    [')).supportSize =', ')).fullMinimum =', 'signature:' + NAMES[4]],
    ['terminalInitialPhysicalCharges initial ++ events.filterMap terminalEventPhysicalCharge?',
      'events.filterMap terminalEventPhysicalCharge?', 'actual-ledger-chain'],
    ['terminalInitialPhysicalCharges initial ++ events.filterMap terminalEventPhysicalCharge?',
      'terminalInitialPhysicalCharges initial ++ terminalInitialPhysicalCharges initial ++ events.filterMap terminalEventPhysicalCharge?',
      'actual-ledger-chain'],
    ['terminalPhysicalChargeLedger trace.normalizedSeed.reverse trace.events',
      'callerCharges system seed', 'actual-ledger-chain'],
  ];
  for (const [before, after, category] of mutations) {
    assert.ok(source.includes(before), 'mutation anchor: ' + category);
    assert.ok(validateSource0(source.replaceAll(before, after)).includes(category), category);
  }
  assert.ok(validateSource0(source + '\naxiom ledgerAuthority : True\n').includes('assumption'));
  assert.ok(validateSource0(source + '\nprivate def suppliedOwner := true\n').includes('shortcut-or-certificate'));
  assert.ok(validateSource0(source + '\ninstance extraAuthority : Inhabited Bool := ⟨true⟩\n').includes('unaudited-form'));
});

test('M236 durable verification runs source contracts, strict explicit-root audit and regressions', async () => {
  const [packageText, surface, verifier, workflow] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  const auditPath = 'audits/lean-residual-terminal-physical-charge-ledger0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m236'], 'node --test ' + auditPath);
  assert.ok(surface.includes("'audit:m236': 'node --test " + auditPath + "'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test ' + auditPath));
  for (const path of [auditPath, 'docs/lean_residual_terminal_physical_charge_ledger.md'])
    assert.equal(workflow.split("      - '"+path.replace(/^audits\/lean-[^/]+\.test\.mjs$/u,'audits/lean-*.test.mjs').replace(/^docs\/lean_[^/]+\.md$/u,'docs/lean_*.md').replace(/^lean\/.*$/u,'lean/**').replace(/^lean-audit\/.*$/u,'lean-audit/**').replace(/^lean-regression\/.*$/u,'lean-regression/**')+"'").length - 1, 2);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M236_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-11-236';
const M236_MILESTONE = 'residual-terminal-physical-charge-ledger';
const M236_HASHES = Object.freeze({
  "PNP.DirectWire.terminalSaturatePhysicalCharges_nodup": "0a497b58da7516008c21d16102eb4250efb393185ceb94e1ae5a231c0d52b0ca",
  "PNP.DirectWire.terminalSaturatePhysicalCharges_complete": "8e0e5f6e186440b15ad4d7df71bd695e66d73c2aa78e1c54464055849ebc884f",
  "PNP.DirectWire.terminalSaturatePhysicalCharges_provenance": "de03b8300d15fd5811d005d572f55ad8cd40c0be743b08c4d0d360937834324a",
  "PNP.DirectWire.terminalSaturatePhysicalChargeProvenance?_iff": "5452a6276bb56f83bdfb7faadf64cf3a3f74e3b33d64f362f202c0c63af3dcb8",
  "PNP.DirectWire.terminalCandidateSaturatePhysicalCharges_size": "0f4f2f19bf24e21a369d29a1ac517235c071f3511f0663dd87af3b854625f8fc"
});
const M236_STATUS_FIELDS = Object.freeze({
  "leanResidualTerminalPhysicalChargeLedgerFormalized": true,
  "leanResidualTerminalPhysicalChargeLedgerAxiomAuditPassed": true,
  "leanResidualTerminalPhysicalChargeLedgerAuditedDeclarationCount": 5,
  "leanResidualTerminalPhysicalChargeLedgerNodupTheorem": "PNP.DirectWire.terminalSaturatePhysicalCharges_nodup",
  "leanResidualTerminalPhysicalChargeLedgerCompletenessTheorem": "PNP.DirectWire.terminalSaturatePhysicalCharges_complete",
  "leanResidualTerminalPhysicalChargeLedgerProvenanceTheorem": "PNP.DirectWire.terminalSaturatePhysicalCharges_provenance",
  "leanResidualTerminalPhysicalChargeLedgerLookupTheorem": "PNP.DirectWire.terminalSaturatePhysicalChargeProvenance?_iff",
  "leanResidualTerminalPhysicalChargeLedgerSizeTheorem": "PNP.DirectWire.terminalCandidateSaturatePhysicalCharges_size",
  "leanResidualTerminalPhysicalChargeLedgerScope": "all-finite-systems-candidates-executable-models-seeds-computed-physical-nand-charge-partition-nodup-completeness-introduction-provenance-lookup-and-total-support-size-only"
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

test('M236 compiled partition, provenance, lookup and size interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M236_MILESTONE);
  assert.equal(row?.earned, true);
  assert.deepEqual(row.requiredTheorems, Object.keys(M236_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, 'PNP.ResidualTerminalPhysicalChargeLedger', name);
      assert.deepEqual(declaration.axioms, ['Quot.sound', 'propext'], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M236_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M236_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M236_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of ['seed- and traversal-dependent introduction provenance',
    'not the complete manuscript charge universe or its fixed global ownership function',
    'Active requesting pairs are not assigned manuscript owners',
    'observer and profile model remain supplied data',
    'exhaustive finite reference constructions',
    'No fixed weighted checkpoint or global gate closes']) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M236 publication rejects weakened, supplied, assumption-backed and widened ledger substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M236_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M236_MILESTONE).earned, false, name);
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
  assert.equal(rejected.milestones.find(row => row.id === M236_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M236_MILESTONE
    ? {...row, nonClaim:'The complete manuscript ownership map and unconditional polynomial ZeroSlack are proved.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M236 adds physical-charge coverage without global ownership, runtime or weighted-score credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M236_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of ['not the fixed manuscript-wide ownership map',
    'Active requesting pairs are not assigned manuscript owners',
    'observer and profile model remain supplied data',
    'exhaustive finite reference constructions',
    'No fixed checkpoint or global gate changes']) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M236_COORDINATE) return;
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

test('M236 current summaries distinguish provenance from ownership and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_residual_terminal_physical_charge_ledger.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of ['Introduction provenance is not the fixed manuscript-wide ownership map',
    'Active requesting pairs are not assigned manuscript owners',
    'observer and profile model remain supplied data',
    'exhaustive finite reference constructions',
    'no polynomial runtime is proved',
    'No fixed weighted checkpoint or global gate closes'])
    assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-11-physical-charge-ledger.md'));
  assert.ok(plan.includes('Publication decision: defer'));
  if (progress.asOfCoordinate !== M236_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_residual_terminal_physical_charge_ledger.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
