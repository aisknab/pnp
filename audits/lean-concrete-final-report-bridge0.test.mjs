import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const PATHS = {
  sat: 'lean/PNP/SAT.lean',
  bridge: 'lean/PNP/Bridge.lean',
  root: 'lean/PNP/Main.lean',
};
const NAMES = [
  'PNP.sat_np_hard_checked',
  'PNP.sat_np_complete_checked',
  'PNP.accepted_generated_package_implies_p_eq_np',
  'PNP.final_report_bridge',
];
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = value => stripLeanCommentsAndStrings0(value).replace(/\s+/gu, ' ').trim();
function block0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex(head => head.name === name);
  return index < 0 ? '' : source.slice(heads[index].index, heads[index + 1]?.index ?? source.length);
}
async function sources0() {
  return Object.fromEntries(await Promise.all(Object.entries(PATHS)
    .map(async ([name,file]) => [name,await text0(file)])));
}
function validateSource0(files) {
  const failures = [];
  const require0 = (condition, category) => { if (!condition) failures.push(category); };
  for (const source of Object.values(files)) {
    require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
    require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-form');
    require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable)\b/u.test(compact0(source)), 'shortcut');
  }
  const sat=compact0(files.sat), bridge=compact0(files.bridge), root=compact0(files.root);
  require0(sat.includes('def SAT : Language := Concrete.CNFSAT'), 'exact-SAT-language');
  require0(/^import PNP\.Concrete\.CookLevinNPCompleteness$/mu.test(files.sat), 'checked-hardness-import');
  const signatures = [
    ['sat','sat_np_hard_checked','theorem sat_np_hard_checked : SATHard'],
    ['sat','sat_np_complete_checked','theorem sat_np_complete_checked : NPComplete SAT'],
    ['bridge','accepted_generated_package_implies_p_eq_np',
      'theorem accepted_generated_package_implies_p_eq_np (loop : PCCMinLoopCertificate) (h : AcceptedGeneratedPackage loop) : PEqualsNP'],
    ['bridge','final_report_bridge',
      'theorem final_report_bridge : FinalReportAntecedent → FinalReportConsequent'],
  ];
  for (const [file,name,signature] of signatures)
    require0(compact0(block0(files[file],name)).startsWith(signature+' := '), 'signature:'+name);
  require0(compact0(block0(files.sat,'sat_np_hard_checked')).includes(
    'Concrete.CookLevin.cnfSAT_np_hard source sourceInNP'), 'checked-hardness-source');
  require0(compact0(block0(files.sat,'sat_np_complete_checked')).endsWith(
    ':= Concrete.CookLevin.cnfSAT_np_complete'), 'checked-completeness-source');
  require0(!/\b(?:CheckerTrustModel|satHard|SATHard|pccPackProducesPCCMinLoop|checkerAccepts)\b/u.test(bridge),
    'no-supplied-trust');
  require0(compact0(block0(files.bridge,'accepted_generated_package_implies_p_eq_np')).includes(
    'sat_np_complete_and_sat_in_p_implies_p_eq_np sat_np_complete_checked (accepted_generated_package_implies_sat_in_p loop h)'),
    'active-checked-transport');
  require0(compact0(block0(files.bridge,'final_report_bridge')).includes(
    'accepted_generated_package_implies_p_eq_np loop accepted'), 'active-final-bridge');
  require0(bridge.includes('def FinalReportAntecedent : Prop := ∃ loop : PCCMinLoopCertificate, AcceptedGeneratedPackage loop'),
    'explicit-loop-existence');
  require0(bridge.includes('def FinalReportConsequent : Prop := PEqualsNP'), 'exact-consequent');
  require0(bridge.includes('loopCertificate : PCCMinLoopCertificate') &&
    bridge.includes('(GeneratePCCPack loop).loopCertificate'), 'proof-bearing-loop');
  require0(root.includes('unconditionalProofPresent := false') &&
    root.includes('externalAssumptionsRemain := true') &&
    root.includes('publicTheoremReleased := false'), 'unreleased-root');
  require0(!explicitLeanDeclarationHeads0(files.root).some(head=>head.name==='p_eq_np'), 'absent-eligible-root');
  return [...new Set(failures)];
}

test('M243 active bridge consumes checked hardness and retains the explicit loop boundary', async () => {
  assert.deepEqual(validateSource0(await sources0()), []);
});

test('M243 regressions pin no-hardness-parameter types and conservative root status', async () => {
  const regression=compact0(await text0('lean-regression/PNPConcreteFinalReportBridge.lean'));
  for(const token of [
    'example : SATHard := sat_np_hard_checked',
    'example : NPComplete SAT := sat_np_complete_checked',
    'accepted_generated_package_implies_p_eq_np loop accepted',
    'example : FinalReportAntecedent → FinalReportConsequent := final_report_bridge',
    '∃ loop : PCCMinLoopCertificate, AcceptedGeneratedPackage loop',
    'PolyTimeDecider ResidualBandExactMinimization := loop.residualBandDecider',
    'Main.rootTheoremStatus.unconditionalProofPresent = false',
    'Main.rootTheoremStatus_not_released',
  ]) assert.ok(regression.includes(token),token);
  assert.doesNotMatch(regression,/\b(?:sorry|admit|axiom|native_decide|Classical)\b/u);
  const audit=await text0('lean-audit/PNPConcreteFinalReportBridgeAxiomAudit.lean');
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(row=>row[1]),NAMES);
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(row=>row[1]),['PNP']);
});

test('M243 hostile contracts reject supplied hardness, weakened endpoints and lost loop existence', async () => {
  const files=await sources0();
  const mutations=[
    ['sat','def SAT : Language := Concrete.CNFSAT','def SAT : Language := fun _ => True','exact-SAT-language'],
    ['sat','theorem sat_np_hard_checked : SATHard','theorem sat_np_hard_checked (hard : SATHard) : SATHard','signature:sat_np_hard_checked'],
    ['sat','Concrete.CookLevin.cnfSAT_np_complete','sat_np_complete_from_hardness callerHardness','checked-completeness-source'],
    ['bridge','theorem final_report_bridge :','theorem final_report_bridge (hard : SATHard) :','signature:final_report_bridge'],
    ['bridge','    sat_np_complete_checked','    (sat_np_complete_from_hardness callerHardness)','active-checked-transport'],
    ['bridge','∃ loop : PCCMinLoopCertificate, AcceptedGeneratedPackage loop','True','explicit-loop-existence'],
    ['bridge','def FinalReportConsequent : Prop := PEqualsNP','def FinalReportConsequent : Prop := True','exact-consequent'],
    ['bridge','loopCertificate : PCCMinLoopCertificate','loopCertificate : String','proof-bearing-loop'],
    ['root','unconditionalProofPresent := false','unconditionalProofPresent := true','unreleased-root'],
  ];
  for(const [file,before,after,category] of mutations) {
    assert.ok(files[file].includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0({...files,[file]:files[file].replace(before,after)}).includes(category),category);
  }
  for(const [extra,category] of [
    ['\naxiom fabricated : False\n','assumption'],
    ['\nstructure CheckerTrustModel where\n  satHard : SATHard\n','no-supplied-trust'],
  ]) assert.ok(validateSource0({...files,bridge:files.bridge+extra}).includes(category),category);
});

test('M243 reviewed-name producers and durable source/type/axiom checks are connected', async () => {
  const [inventorySource,root,workflow,packageText,surface,verifier]=await Promise.all([
    text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean'),
    text0('.github/workflows/lean-bridge.yml'),text0('package.json'),
    text0('pcc-formal-public-surface0.mjs'),text0('scripts/pnp-verify-all.mjs'),
  ]);
  for(const name of NAMES) {
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item=>item===name).length,1,name);
    assert.equal(inventorySource.split(String.fromCharCode(96)+name+',').length-1,1,name);
  }
  assert.match(root,/^import PNP\.Bridge$/mu);
  const path='audits/lean-concrete-final-report-bridge0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m243'],'node --test '+path);
  assert.ok(surface.includes("'audit:m243': 'node --test "+path+"'"));
  assert.ok(verifier.includes(path));
  assert.ok(workflow.includes('run: node --test '+path));
  for(const file of [path,'docs/lean_concrete_final_report_bridge.md'])
    assert.equal(workflow.split("      - '"+file.replace(/^audits\/lean-[^/]+\.test\.mjs$/u,'audits/lean-*.test.mjs').replace(/^docs\/lean_[^/]+\.md$/u,'docs/lean_*.md').replace(/^lean\/.*$/u,'lean/**').replace(/^lean-audit\/.*$/u,'lean-audit/**').replace(/^lean-regression\/.*$/u,'lean-regression/**')+"'").length-1,2);
  for(const name of ['PNPConcreteFinalReportBridgeAxiomAudit.lean',
    'PNPConcreteFinalReportBridge.lean'])assert.ok(workflow.includes(name),name);
  for(const name of ['PNP.accepted_generated_package_implies_p_eq_np','PNP.final_report_bridge'])
    assert.ok(workflow.includes("'"+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]"),name);
});

import {
  DeriveFormalPublication0, MilestoneTheoremKernelTypeSha2560,
  REQUIRED_MILESTONE_THEOREMS0, stableStringify0,
} from '../formal-publication0.mjs';
import { validateProofProgress0 } from '../pcc-proof-progress0.mjs';

const M243_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-12-243';
const M243_MILESTONE = 'concrete-final-report-bridge';
const M243_HASHES = Object.freeze({
  "PNP.sat_np_hard_checked": "ebcaa13f070d5b1f8fc0105e0feea71c65010f94a5e135ae0c4abaf4544fb382",
  "PNP.sat_np_complete_checked": "4ed163e43a3c4fd3be9ea3d1d5c348a0ce4951beb322aca3c617265e63b0fd26",
  "PNP.accepted_generated_package_implies_p_eq_np": "89cfb0983711ce18a75e458324047e6007ac456dbdc926f09080db41d826379f",
  "PNP.final_report_bridge": "956062f71216218a1edb59039ae63f85c01564a93e7a1e891754127f3e22c8a5"
});
const M243_STATUS_FIELDS = Object.freeze({
  "leanConcreteFinalReportBridgeFormalized": true,
  "leanConcreteFinalReportBridgeAxiomAuditPassed": true,
  "leanConcreteFinalReportBridgeAuditedDeclarationCount": 4,
  "leanConcreteFinalReportBridgeSATHardnessTheorem": "PNP.sat_np_hard_checked",
  "leanConcreteFinalReportBridgeSATCompletenessTheorem": "PNP.sat_np_complete_checked",
  "leanConcreteFinalReportBridgePackageConsequenceTheorem": "PNP.accepted_generated_package_implies_p_eq_np",
  "leanConcreteFinalReportBridgeFinalReportTheorem": "PNP.final_report_bridge",
  "leanConcreteFinalReportBridgeRequiresSuppliedSATHardness": false,
  "leanConcreteFinalReportBridgeLoopCertificateExistenceDischarged": false,
  "leanConcreteFinalReportBridgeScope": "checked-all-input-concrete-cook-levin-hardness-consumed-by-the-active-conditional-final-report-bridge-explicit-proof-bearing-pccmin-loop-existence-still-required"
});
const M243_AXIOMS = Object.freeze({
  "PNP.sat_np_hard_checked": [
    "Classical.choice",
    "Quot.sound",
    "propext"
  ],
  "PNP.sat_np_complete_checked": [
    "Classical.choice",
    "Quot.sound",
    "propext"
  ],
  "PNP.accepted_generated_package_implies_p_eq_np": [
    "Classical.choice",
    "Quot.sound",
    "propext"
  ],
  "PNP.final_report_bridge": [
    "Classical.choice",
    "Quot.sound",
    "propext"
  ]
});
const M243_MODULES = Object.freeze({
  "PNP.sat_np_hard_checked": "PNP.SAT",
  "PNP.sat_np_complete_checked": "PNP.SAT",
  "PNP.accepted_generated_package_implies_p_eq_np": "PNP.Bridge",
  "PNP.final_report_bridge": "PNP.Bridge"
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

test('M243 compiled concrete SAT and active conditional bridge interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M243_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M243_COORDINATE)
    assert.equal(map.coordinate, M243_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M243_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, M243_MODULES[name], name);
      assert.deepEqual(declaration.axioms, M243_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M243_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M243_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M243_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "conditional final-report bridge",
  "No complete PCCMin loop certificate is constructed",
  "deterministic CNFSAT in P",
  "M231 hardness was already credited",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M243 publication rejects weakened, supplied, assumption-backed and widened conditional bridge substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M243_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M243_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = NAMES[2];
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M243_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M243_MILESTONE
    ? {...row, nonClaim:'Package acceptance constructs the complete PCCMin loop and proves the eligible unconditional root.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M243 removes a supplied hardness premise without duplicate, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M243_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "existing active conditional final-report bridge",
  "explicit loop-existence antecedent remains open",
  "M231 hardness was already credited",
  "No fixed weighted checkpoint or global gate changes",
  "evidence row changes coverage only"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M243_COORDINATE) return;
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

test('M243 current summaries retain explicit loop existence and distinguish a conditional bridge from the eligible root and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_concrete_final_report_bridge.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "No supplied SAT-hardness parameter remains",
  "The complete PCCMin loop certificate is not constructed",
  "Classical.choice",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-12-concrete-final-report-bridge.md'));
  assert.ok(plan.includes('Publication decision: defer'));
  if (progress.asOfCoordinate !== M243_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_concrete_final_report_bridge.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
