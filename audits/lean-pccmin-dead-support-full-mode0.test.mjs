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

const SOURCE = 'lean/PNP/PCCMinDeadSupportFullMode.lean';
const AUDIT = 'lean-audit/PNPDeadSupportFullModeAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPDeadSupportFullMode.lean';
const NAMES = [
  "firstTerminalOpenObligation_eq_none_iff",
  "firstTerminalOpenObligation_spec",
  "DeadSupportFullModeGain.currentObligationsDischarged",
  "classifyDeadSupportFullMode_accepted_iff",
  "classifyDeadSupportFullMode_noProperSupport_iff",
  "DeadSupportFullModeGain.fullProfileMinimum",
  "DeadSupportFullModeGain.checked",
  "classifyDeadSupportFullMode_checked"
];
const SIGNATURES = [
  "theorem firstTerminalOpenObligation_eq_none_iff {inputs outputs profileWidth : Nat} (system : TerminalProfileSystem inputs outputs profileWidth) (current : Implementation inputs outputs) : firstTerminalOpenObligation system current = none ↔ system.ObligationsDischarged current",
  "theorem firstTerminalOpenObligation_spec {inputs outputs profileWidth : Nat} (system : TerminalProfileSystem inputs outputs profileWidth) (current : Implementation inputs outputs) (coordinate : Fin profileWidth) (foundAt : firstTerminalOpenObligation system current = some coordinate) : system.role coordinate = .obligation ∧ system.observe current coordinate = true ∧ ∃ before after : List (Fin profileWidth), allFin profileWidth = before ++ coordinate :: after ∧ ∀ earlier, earlier ∈ before → system.role earlier = .obligation → system.observe current earlier = false",
  "theorem DeadSupportFullModeGain.currentObligationsDischarged {inputs outputs profileWidth : Nat} {system : TerminalProfileSystem inputs outputs profileWidth} {current : Implementation inputs outputs} (gain : DeadSupportFullModeGain system current) : system.ObligationsDischarged current",
  "theorem classifyDeadSupportFullMode_accepted_iff {inputs outputs profileWidth : Nat} (system : TerminalProfileSystem inputs outputs profileWidth) (current : Implementation inputs outputs) : (classifyDeadSupportFullMode system current).tag = .accepted ↔ (deadSupportProperGain current).isSome = true ∧ (∀ coordinate, system.observe (deadSupportReplacementImplementation current) coordinate = system.observe current coordinate) ∧ system.ObligationsDischarged (deadSupportReplacementImplementation current)",
  "theorem classifyDeadSupportFullMode_noProperSupport_iff {inputs outputs profileWidth : Nat} (system : TerminalProfileSystem inputs outputs profileWidth) (current : Implementation inputs outputs) : (classifyDeadSupportFullMode system current).tag = .noProperSupport ↔ deadSupportProperGain current = none",
  "theorem DeadSupportFullModeGain.fullProfileMinimum {inputs outputs profileWidth : Nat} {system : TerminalProfileSystem inputs outputs profileWidth} {current : Implementation inputs outputs} (gain : DeadSupportFullModeGain system current) : terminalFullProfileMinimum system (deadSupportReplacementImplementation current) = terminalFullProfileMinimum system current",
  "theorem DeadSupportFullModeGain.checked {inputs outputs profileWidth : Nat} {system : TerminalProfileSystem inputs outputs profileWidth} {current : Implementation inputs outputs} (gain : DeadSupportFullModeGain system current) : 0 < deadSupportGateCount current ∧ deadSupportGateCount current < current.gateCount ∧ Equivalent (deadSupportReplacementImplementation current).candidate.program (deadSupportReplacementImplementation current).candidate.directWireWord current.candidate.program current.candidate.directWireWord ∧ (∀ coordinate, system.observe (deadSupportReplacementImplementation current) coordinate = system.observe current coordinate) ∧ system.ObligationsDischarged current ∧ system.ObligationsDischarged (deadSupportReplacementImplementation current) ∧ (deadSupportReplacementImplementation current).gateCount + deadSupportGateCount current = current.gateCount ∧ residualSlack current = residualSlack (deadSupportReplacementImplementation current) + deadSupportGateCount current ∧ StrictEquivalentGain current (deadSupportReplacementImplementation current) ∧ residualSlack (deadSupportReplacementImplementation current) < residualSlack current",
  "theorem classifyDeadSupportFullMode_checked {inputs outputs profileWidth : Nat} (system : TerminalProfileSystem inputs outputs profileWidth) (current : Implementation inputs outputs) : match classifyDeadSupportFullMode system current with | .noProperSupport _ => deadSupportProperGain current = none | .profileMismatch _ _ coordinate _ => system.observe (deadSupportReplacementImplementation current) coordinate ≠ system.observe current coordinate ∧ ∃ before after : List (Fin profileWidth), allFin profileWidth = before ++ coordinate :: after ∧ ∀ earlier, earlier ∈ before → system.observe (deadSupportReplacementImplementation current) earlier = system.observe current earlier | .openObligation _ _ _ coordinate _ => (∀ index, system.observe (deadSupportReplacementImplementation current) index = system.observe current index) ∧ system.role coordinate = .obligation ∧ system.observe (deadSupportReplacementImplementation current) coordinate = true ∧ ∃ before after : List (Fin profileWidth), allFin profileWidth = before ++ coordinate :: after ∧ ∀ earlier, earlier ∈ before → system.role earlier = .obligation → system.observe (deadSupportReplacementImplementation current) earlier = false | .accepted _ => system.ObligationsDischarged current ∧ system.ObligationsDischarged (deadSupportReplacementImplementation current) ∧ StrictEquivalentGain current (deadSupportReplacementImplementation current) ∧ residualSlack (deadSupportReplacementImplementation current) < residualSlack current"
];
const PUBLIC_HEADS = [
  "firstTerminalOpenObligation",
  "firstTerminalOpenObligation_eq_none_iff",
  "firstTerminalOpenObligation_spec",
  "DeadSupportFullModeGain",
  "DeadSupportFullModeGain.fullRealization",
  "DeadSupportFullModeGain.currentObligationsDischarged",
  "DeadSupportFullModeTag",
  "DeadSupportFullModeOutcome",
  "DeadSupportFullModeOutcome.tag",
  "classifyDeadSupportFullMode",
  "classifyDeadSupportFullMode_accepted_iff",
  "classifyDeadSupportFullMode_noProperSupport_iff",
  "DeadSupportFullModeGain.fullProfileMinimum",
  "DeadSupportFullModeGain.checked",
  "classifyDeadSupportFullMode_checked"
];
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = value => stripLeanCommentsAndStrings0(value).replace(/\s+/gu, ' ').trim();
function block0(source,name) {
  const heads=explicitLeanDeclarationHeads0(source), index=heads.findIndex(head=>head.name===name);
  return index<0?'':source.slice(heads[index].index,heads[index+1]?.index??source.length);
}
function validateSource0(source) {
  const failures=[], require0=(condition,category)=>{if(!condition)failures.push(category);};
  const clean=compact0(source);
  require0(!hasLeanAssumptionDeclaration0(source),'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source),'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|callerCertificate|suppliedGain)\b/u
    .test(clean),'shortcut-or-certificate');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]))===
    JSON.stringify(['PNP.PCCMinDeadSupportContext','PNP.ResidualTerminalGainProfileFirewall']),
    'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name))===
    JSON.stringify(PUBLIC_HEADS),'public-interface');
  for(const [index,name] of NAMES.entries())
    require0(compact0(block0(source,name)).startsWith(SIGNATURES[index]+' := '),'signature:'+name);
  const scan=compact0(block0(source,'firstTerminalOpenObligation'));
  require0(scan.includes('(allFin profileWidth).find? (terminalObligationOpen system current)'),
    'complete-obligation-scan');
  const predicate=compact0(source.slice(source.indexOf('private def terminalObligationOpen '),
    source.indexOf('private theorem terminalObligationOpen_iff ')));
  require0(predicate.includes('decide (system.role coordinate = .obligation) && system.observe current coordinate'),
    'actual-role-and-open-value');
  const realization=compact0(block0(source,'DeadSupportFullModeGain.fullRealization'));
  for(const token of ['implementation := deadSupportReplacementImplementation current',
    'equivalent := deadSupportReplacement_equivalent current','profileEqual := gain.profileEqual'])
    require0(realization.includes(token),'computed-full-realization');
  const classifier=compact0(block0(source,'classifyDeadSupportFullMode'));
  for(const token of [
    'match physicalAt : deadSupportProperGain current with',
    '| none => .noProperSupport physicalAt',
    'match profileAt : firstTerminalGainProfileMismatch system current (deadSupportReplacementImplementation current) with',
    '| some coordinate => .profileMismatch physical physicalAt coordinate profileAt',
    'match openAt : firstTerminalOpenObligation system (deadSupportReplacementImplementation current) with',
    '| some coordinate => .openObligation physical physicalAt profileAt coordinate openAt',
    '| none => .accepted',
    'physicalFoundAt := physicalAt',
    '(firstTerminalGainProfileMismatch_eq_none_iff system current (deadSupportReplacementImplementation current)).mp profileAt',
    '(firstTerminalOpenObligation_eq_none_iff system (deadSupportReplacementImplementation current)).mp openAt',
  ]) require0(classifier.includes(token),'complete-fail-closed-classification');
  require0(!/\b(?:allCandidates|allValuations|allSubsets|equivalentBool|referenceMinimumWitness|scanEquivalentSizes|referenceMinimum|terminalFullProfileMinimum|TerminalProfileProjection)\b/u
    .test([scan,predicate,realization,classifier].join(' ')),'no-search-or-quotient-shortcut');
  return [...new Set(failures)];
}

test('M246 computes complete finite-profile and obligation acceptance with eight general laws', async()=>{
  assert.deepEqual(validateSource0(await text0(SOURCE)),[]);
});

test('M246 explicit root, exact audit and reviewed-name producers agree',async()=>{
  const [source,audit,inventorySource,root]=await Promise.all([
    text0(SOURCE),text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean')]);
  for(const name of NAMES){
    assert.equal(explicitLeanDeclarationHeads0(source).filter(head=>head.name===name).length,1);
    const fullName='PNP.DirectWire.'+name;
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item=>item===fullName).length,1);
    assert.equal(inventorySource.split(String.fromCharCode(96)+fullName+',').length-1,1);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),
    NAMES.map(name=>'PNP.DirectWire.'+name));
  assert.match(root,/^import PNP\.PCCMinDeadSupportFullMode\s*$/mu);
});

test('M246 regressions separate closed profiles, open obligations, hidden mismatches and improper support',async()=>{
  const raw=await text0(REGRESSION), regression=compact0(raw);
  for(const name of NAMES)assert.ok(regression.includes(name.split('.').at(-1)),name);
  for(const token of [
    'closedSystem : TerminalProfileSystem 1 1 4','openSystem : TerminalProfileSystem 1 1 4',
    'mismatchSystem : TerminalProfileSystem 1 1 4','hidingProjection : TerminalProfileProjection 4',
    'zeroProfile','allDead : Implementation 1 0','empty : Implementation 0 0',
    'noDead : Implementation 1 1','coordinate.val != 2','coordinate.val != 0',
    'gain.fullRealization.realization.implementation',
    '(firstTerminalGainProfileMismatch openSystem current replacement).isSome',
    'throw (IO.userError',
  ])assert.ok(regression.includes(token),token);
  assert.equal([...raw.matchAll(/^#eval\b/gmu)].length,1);
  assert.doesNotMatch(regression,/\b(?:sorry|admit|native_decide|Classical)\b/u);
  assert.doesNotMatch(raw.split('#eval')[1],/\b(?:referenceMinimum|terminalFullProfileMinimum|scanEquivalentSizes|allCandidates)\s/u);
});

test('M246 rejects supplied, finite-only and weakened full-mode theorem boundaries',async()=>{
  const source=await text0(SOURCE);
  for(const [before,after,category] of [
    ['(system : TerminalProfileSystem inputs outputs profileWidth)',
      '(system : TerminalProfileSystem inputs outputs 4)',
      'signature:firstTerminalOpenObligation_eq_none_iff'],
    ['(classifyDeadSupportFullMode system current).tag = .accepted ↔',
      '(classifyDeadSupportFullMode system current).tag = .accepted →',
      'signature:classifyDeadSupportFullMode_accepted_iff'],
    ['(current : Implementation inputs outputs) :\n    (classifyDeadSupportFullMode',
      '(current : Implementation inputs outputs) (callerCertificate : True) :\n    (classifyDeadSupportFullMode',
      'signature:classifyDeadSupportFullMode_accepted_iff'],
    ['residualSlack (deadSupportReplacementImplementation current) < residualSlack current',
      'residualSlack (deadSupportReplacementImplementation current) ≤ residualSlack current',
      'signature:DeadSupportFullModeGain.checked'],
  ]){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
});

test('M246 rejects skipped coordinates, wrong obligation roles and fabricated acceptance',async()=>{
  const source=await text0(SOURCE);
  for(const [before,after,category] of [
    ['(allFin profileWidth).find? (terminalObligationOpen system current)',
      '((allFin profileWidth).take 1).find? (terminalObligationOpen system current)',
      'complete-obligation-scan'],
    ['decide (system.role coordinate = .obligation) && system.observe current coordinate',
      'decide (system.role coordinate = .carrier) && system.observe current coordinate',
      'actual-role-and-open-value'],
    ['| some coordinate => .profileMismatch physical physicalAt coordinate profileAt',
      '| some coordinate => .accepted fabricatedGain','complete-fail-closed-classification'],
    ['| some coordinate => .openObligation physical physicalAt profileAt coordinate openAt',
      '| some coordinate => .accepted fabricatedGain','complete-fail-closed-classification'],
    ['implementation := deadSupportReplacementImplementation current',
      'implementation := current','computed-full-realization'],
  ]){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n').includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n').includes('unaudited-form'));
});

test('M246 durable workflow retains source contracts, exact audit and bounded regressions',async()=>{
  const [packageText,surface,verifier,workflow]=await Promise.all([
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),text0('.github/workflows/lean-bridge.yml')]);
  const auditPath='audits/lean-pccmin-dead-support-full-mode0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m246'],'node --test '+auditPath);
  assert.ok(surface.includes("'audit:m246': 'node --test "+auditPath+"'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test '+auditPath));
  for(const path of [auditPath,'docs/lean_pccmin_dead_support_full_mode.md'])
    assert.equal(workflow.split("      - '"+path+"'").length-1,2);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M246_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-12-246';
const M246_MILESTONE = 'pccmin-dead-support-full-mode';
const M246_HASHES = Object.freeze({
  "PNP.DirectWire.firstTerminalOpenObligation_eq_none_iff": "1a0c93b1d9ce168b0e077280cb41ed9ab682db406f7d6915b2fe6e327a1de60d",
  "PNP.DirectWire.firstTerminalOpenObligation_spec": "123d777771db64aaaf53b9dd42a834694d86f7088c8d422008be7f445842e8be",
  "PNP.DirectWire.DeadSupportFullModeGain.currentObligationsDischarged": "4439af8e42be526327a645db512351e9373ca77858c4adb172d5167b23a684d1",
  "PNP.DirectWire.classifyDeadSupportFullMode_accepted_iff": "b552736e74904695506adb00c52b18047de6cdc4af1890f01d5a66a4b8cca642",
  "PNP.DirectWire.classifyDeadSupportFullMode_noProperSupport_iff": "d08c20b2c7b9af0a2cdc926dcf66fe1bb7809c1d0cddd3f5ecee698c6454188a",
  "PNP.DirectWire.DeadSupportFullModeGain.fullProfileMinimum": "feeab8f455701e6dd448e31dab4a596148cc02258492127d0f40cdde76a99f44",
  "PNP.DirectWire.DeadSupportFullModeGain.checked": "4cad2c9d19dd6d8d490643fe8145e7962898c2cb63eef3af2560f31a21baf729",
  "PNP.DirectWire.classifyDeadSupportFullMode_checked": "e45814982c40279fd2e49a52e93e7428012a6dc5003e3effc7222977a0fb8e50"
});
const M246_STATUS_FIELDS = Object.freeze({
  "leanPCCMinDeadSupportFullModeFormalized": true,
  "leanPCCMinDeadSupportFullModeAxiomAuditPassed": true,
  "leanPCCMinDeadSupportFullModeAuditedDeclarationCount": 8,
  "leanPCCMinDeadSupportFullModeObligationScanTheorem": "PNP.DirectWire.firstTerminalOpenObligation_eq_none_iff",
  "leanPCCMinDeadSupportFullModeFirstOpenObligationTheorem": "PNP.DirectWire.firstTerminalOpenObligation_spec",
  "leanPCCMinDeadSupportFullModeCurrentObligationsTheorem": "PNP.DirectWire.DeadSupportFullModeGain.currentObligationsDischarged",
  "leanPCCMinDeadSupportFullModeAcceptanceTheorem": "PNP.DirectWire.classifyDeadSupportFullMode_accepted_iff",
  "leanPCCMinDeadSupportFullModeNoProperSupportTheorem": "PNP.DirectWire.classifyDeadSupportFullMode_noProperSupport_iff",
  "leanPCCMinDeadSupportFullModeFullProfileMinimumTheorem": "PNP.DirectWire.DeadSupportFullModeGain.fullProfileMinimum",
  "leanPCCMinDeadSupportFullModeAcceptedSoundnessTheorem": "PNP.DirectWire.DeadSupportFullModeGain.checked",
  "leanPCCMinDeadSupportFullModeClassifierSoundnessTheorem": "PNP.DirectWire.classifyDeadSupportFullMode_checked",
  "leanPCCMinDeadSupportFullModeManuscriptCarrierDerived": false,
  "leanPCCMinDeadSupportFullModeCompletePackageEVerifierProved": false,
  "leanPCCMinDeadSupportFullModePolynomialRuntimeProved": false,
  "leanPCCMinDeadSupportFullModeScope": "computed-proper-dead-support-complete-finite-profile-and-observed-obligation-acceptance-over-input-observation-system-no-derived-manuscript-carrier-or-discharge-ledger"
});
const M246_AXIOMS = Object.freeze({
  "PNP.DirectWire.firstTerminalOpenObligation_eq_none_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.firstTerminalOpenObligation_spec": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.DeadSupportFullModeGain.currentObligationsDischarged": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.classifyDeadSupportFullMode_accepted_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.classifyDeadSupportFullMode_noProperSupport_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.DeadSupportFullModeGain.fullProfileMinimum": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.DeadSupportFullModeGain.checked": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.classifyDeadSupportFullMode_checked": [
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

test('M246 compiled dead-support full-mode acceptance interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M246_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M246_COORDINATE)
    assert.equal(map.coordinate, M246_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M246_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, 'PNP.PCCMinDeadSupportFullMode', name);
      assert.deepEqual(declaration.axioms, M246_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M246_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M246_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M246_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "computed acceptance against an input finite profile observation system",
  "not derivation of the manuscript carrier",
  "does not by itself establish complete Package E admissibility",
  "matching profiles with an open obligation are rejected",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M246 publication rejects weakened, supplied, assumption-backed and widened full-mode substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M246_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M246_MILESTONE).earned, false, name);
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
  assert.equal(rejected.milestones.find(row => row.id === M246_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M246_MILESTONE
    ? {...row, nonClaim:'Observed-profile acceptance proves complete Package E, a derived manuscript carrier and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M246 adds finite-profile acceptance coverage without derived-carrier, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M246_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "actual computed proper dead-support replacement",
  "observation system remains input data",
  "No fixed weighted checkpoint or global gate changes",
  "evidence row changes coverage only"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M246_COORDINATE) return;
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

test('M246 current summaries distinguish observed full-mode acceptance from derived manuscript admissibility and global completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_pccmin_dead_support_full_mode.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "No result, profile-invariance premise or correctness certificate is supplied by the caller",
  "Checking observed obligation bits is not a constructed R5 creation or R6-R8 discharge ledger",
  "No-proper-support rejection excludes only this computed dead-support route",
  "Runtime execution is test evidence, not theorem authority",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-12-computed-dead-support-full-mode.md'));
  assert.ok(plan.includes('Publication decision: defer PNPLabs.'));
  if (progress.asOfCoordinate !== M246_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_pccmin_dead_support_full_mode.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
