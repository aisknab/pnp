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

const SOURCE = 'lean/PNP/PCCMinPhysicalNormalizationClosure.lean';
const AUDIT = 'lean-audit/PNPPhysicalNormalizationClosureAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPPhysicalNormalizationClosure.lean';
const NAMES = [
  "physicalNormalizationPass_equivalent",
  "physicalNormalizationPass_exact_accounting",
  "PhysicalNormalizationGain.checked",
  "nextPhysicalNormalizationStep_checked",
  "PhysicalNormalizationTrace.checked",
  "runPhysicalNormalization_checked",
  "runPhysicalNormalization_of_quiescent",
  "runPhysicalNormalization_idempotent",
  "runPhysicalNormalization_referenceMinimum",
  "runPhysicalNormalization_residualSlack",
  "runPhysicalNormalization_gainIterations_le_residualSlack",
  "physicalClosureNormalizer_checked"
];
const SIGNATURES = [
  "theorem physicalNormalizationPass_equivalent {inputs outputs : Nat} (pass : PhysicalNormalizationPass) (current : Implementation inputs outputs) : Equivalent (physicalNormalizationPassResult pass current).candidate.program (physicalNormalizationPassResult pass current).candidate.directWireWord current.candidate.program current.candidate.directWireWord",
  "theorem physicalNormalizationPass_exact_accounting {inputs outputs : Nat} (pass : PhysicalNormalizationPass) (current : Implementation inputs outputs) : (physicalNormalizationPassResult pass current).gateCount + physicalNormalizationPassSavings pass current = current.gateCount",
  "theorem PhysicalNormalizationGain.checked {inputs outputs : Nat} {current : Implementation inputs outputs} (gain : PhysicalNormalizationGain current) : StrictEquivalentGain current gain.result ∧ gain.result.gateCount + gain.savedGates = current.gateCount ∧ 0 < gain.savedGates ∧ ∀ earlier, earlier.priority < gain.pass.priority → physicalNormalizationPassSavings earlier current = 0",
  "theorem nextPhysicalNormalizationStep_checked {inputs outputs : Nat} (current : Implementation inputs outputs) : match nextPhysicalNormalizationStep current with | .gain selected => StrictEquivalentGain current selected.result ∧ selected.result.gateCount + selected.savedGates = current.gateCount ∧ 0 < selected.savedGates ∧ ∀ earlier, earlier.priority < selected.pass.priority → physicalNormalizationPassSavings earlier current = 0 | .quiescent _ => PhysicalNormalizationQuiescent current",
  "theorem PhysicalNormalizationTrace.checked {inputs outputs : Nat} {current final : Implementation inputs outputs} (trace : PhysicalNormalizationTrace current final) : Equivalent final.candidate.program final.candidate.directWireWord current.candidate.program current.candidate.directWireWord ∧ PhysicalNormalizationQuiescent final ∧ final.gateCount + trace.savedGates = current.gateCount ∧ trace.gainIterations ≤ trace.savedGates",
  "theorem runPhysicalNormalization_checked {inputs outputs : Nat} (current : Implementation inputs outputs) : let execution",
  "theorem runPhysicalNormalization_of_quiescent {inputs outputs : Nat} (current : Implementation inputs outputs) (quiet : PhysicalNormalizationQuiescent current) : (runPhysicalNormalization current).result = current",
  "theorem runPhysicalNormalization_idempotent {inputs outputs : Nat} (current : Implementation inputs outputs) : (runPhysicalNormalization (runPhysicalNormalization current).result).result = (runPhysicalNormalization current).result",
  "theorem runPhysicalNormalization_referenceMinimum {inputs outputs : Nat} (current : Implementation inputs outputs) : referenceMinimum (runPhysicalNormalization current).result = referenceMinimum current",
  "theorem runPhysicalNormalization_residualSlack {inputs outputs : Nat} (current : Implementation inputs outputs) : residualSlack current = residualSlack (runPhysicalNormalization current).result + (runPhysicalNormalization current).trace.savedGates",
  "theorem runPhysicalNormalization_gainIterations_le_residualSlack {inputs outputs : Nat} (current : Implementation inputs outputs) : (runPhysicalNormalization current).trace.gainIterations ≤ residualSlack current",
  "theorem physicalClosureNormalizer_checked {inputs outputs : Nat} (current : Implementation inputs outputs) : match physicalClosureNormalizer.normalize current with | .gain next _ => next = (runPhysicalNormalization current).result ∧ PhysicalNormalizationQuiescent next ∧ 0 < (runPhysicalNormalization current).trace.savedGates | .normal normalized => normalized.result = (runPhysicalNormalization current).result ∧ PhysicalNormalizationQuiescent normalized.result ∧ (runPhysicalNormalization current).trace.savedGates = 0 ∧ normalized.result.gateCount = current.gateCount"
];
const PUBLIC_HEADS = [
  "PhysicalNormalizationPass",
  "PhysicalNormalizationPass.priority",
  "physicalNormalizationPassResult",
  "physicalNormalizationPassSavings",
  "physicalNormalizationPass_equivalent",
  "physicalNormalizationPass_exact_accounting",
  "PhysicalNormalizationQuiescent",
  "PhysicalNormalizationGain",
  "PhysicalNormalizationGain.result",
  "PhysicalNormalizationGain.savedGates",
  "PhysicalNormalizationGain.strictGain",
  "PhysicalNormalizationGain.checked",
  "PhysicalNormalizationStep",
  "nextPhysicalNormalizationStep",
  "nextPhysicalNormalizationStep_checked",
  "PhysicalNormalizationTrace",
  "PhysicalNormalizationTrace.gainIterations",
  "PhysicalNormalizationTrace.savedGates",
  "PhysicalNormalizationTrace.checked",
  "PhysicalNormalizationExecution",
  "runPhysicalNormalization",
  "runPhysicalNormalization_checked",
  "runPhysicalNormalization_of_quiescent",
  "runPhysicalNormalization_idempotent",
  "runPhysicalNormalization_referenceMinimum",
  "runPhysicalNormalization_residualSlack",
  "runPhysicalNormalization_gainIterations_le_residualSlack",
  "physicalClosureNormalizer",
  "physicalClosureNormalizer_checked"
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
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|callerCertificate|suppliedOptimizer)\b/u
    .test(clean),'shortcut-or-certificate');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]))===
    JSON.stringify(['PNP.PCCMinConstantPropagation','PNP.PCCMinConstructiveNANDSharing',
      'PNP.PCCMinOutputConePruning']),'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name))===
    JSON.stringify(PUBLIC_HEADS),'public-interface');
  for(const [index,name] of NAMES.entries())
    require0(compact0(block0(source,name)).startsWith(SIGNATURES[index]+' := '),'signature:'+name);
  const result=compact0(block0(source,'physicalNormalizationPassResult'));
  for(const token of ['| .constants => constantPropagationImplementation current',
    '| .sharing => sharingImplementation current','| .pruning => outputConeImplementation current'])
    require0(result.includes(token),'actual-three-pass-results');
  const savings=compact0(block0(source,'physicalNormalizationPassSavings'));
  for(const token of [
    '| .constants => (compileNANDConstantPropagation current.candidate.program).eliminationCount',
    '| .sharing => (compileNANDSharing current.candidate.program).foldCount',
    '| .pruning => outputConeDeletedGateCount current'])
    require0(savings.includes(token),'actual-three-pass-savings');
  const quiet=compact0(block0(source,'PhysicalNormalizationQuiescent'));
  require0(quiet.includes('∀ pass, physicalNormalizationPassSavings pass current = 0'),
    'same-input-all-pass-stopping');
  const select=compact0(block0(source,'nextPhysicalNormalizationStep'));
  for(const token of [
    'if constants : 0 < physicalNormalizationPassSavings .constants current then',
    'else if sharing : 0 < physicalNormalizationPassSavings .sharing current then',
    'else if pruning : 0 < physicalNormalizationPassSavings .pruning current then',
    'pass := .constants positive := constants','pass := .sharing positive := sharing',
    'pass := .pruning positive := pruning','earlier_quiet := by',
    'else .quiescent (by intro pass cases pass'])
    require0(select.includes(token),'computed-priority-and-stopping');
  const iterations=compact0(block0(source,'PhysicalNormalizationTrace.gainIterations'));
  require0(iterations.includes('| .done _ _ => 0') &&
    iterations.endsWith('| .step _ tail => tail.gainIterations + 1'),'actual-trace-iterations');
  const traceSavings=compact0(block0(source,'PhysicalNormalizationTrace.savedGates'));
  require0(traceSavings.includes('| .done _ _ => 0') &&
    traceSavings.endsWith('| .step gain tail => gain.savedGates + tail.savedGates'),
    'actual-trace-savings');
  const loop=compact0(block0(source,'runPhysicalNormalization'));
  for(const token of ['match nextPhysicalNormalizationStep current with',
    '| .gain gain => let tail := runPhysicalNormalization gain.result',
    'result := tail.result trace := .step gain tail.trace',
    '| .quiescent quiet => { result := current trace := .done current quiet }',
    'termination_by current.gateCount','decreasing_by exact gain.strictGain.smaller'])
    require0(loop.includes(token),'computed-strict-recursion');
  const normalizer=compact0(block0(source,'physicalClosureNormalizer'));
  for(const token of ['let execution := runPhysicalNormalization current',
    'if positive : 0 < execution.trace.savedGates then','.gain execution.result',
    'result := execution.result','equivalent := (runPhysicalNormalization_checked current).1'])
    require0(normalizer.includes(token),'computed-normalizer-result');
  require0(!/\b(?:allCandidates|allValuations|allSubsets|equivalentBool|referenceMinimumWitness|scanEquivalentSizes|referenceMinimum|terminalFullProfileMinimum)\b/u
    .test([result,savings,quiet,select,iterations,traceSavings,loop,normalizer].join(' ')),
    'no-exhaustive-search');
  return [...new Set(failures)];
}

test('M248 computes three-pass closure with twelve general laws and actual trace savings',async()=>{
  assert.deepEqual(validateSource0(await text0(SOURCE)),[]);
});

test('M248 explicit root, exact audit and reviewed-name producers agree',async()=>{
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
  assert.match(root,/^import PNP\.PCCMinPhysicalNormalizationClosure\s*$/mu);
});

test('M248 regressions cover interacting priorities, stable reruns and nonminimum quiescence',async()=>{
  const raw=await text0(REGRESSION), regression=compact0(raw);
  for(const name of NAMES)assert.ok(regression.includes(name),name);
  for(const token of ['interactingProgram : Program 2 5','interacting : Implementation 2 7',
    'sharingAndPruning : Implementation 2 1','pruningOnly : Implementation 2 1',
    'constantsOnly : Implementation 1 1','noGates : Implementation 0 0',
    'StrictEquivalentGain correlated constantAlternative',
    'selectedPasses execution.trace != [.constants, .sharing, .pruning]',
    'execution.result.gateCount != 2 || execution.trace.savedGates != 3',
    'repeated.trace.gainIterations != 0','(allFin 7).map',
    '!a, a, a, true, left, false, !a','assertQuiet nonminimum.result',
    'nonminimum.result.gateCount != 2','0 < residualSlack correlated','throw (IO.userError'])
    assert.ok(regression.includes(token),token);
  assert.equal([...raw.matchAll(/^#eval\b/gmu)].length,1);
  assert.doesNotMatch(regression,/\b(?:sorry|admit|native_decide|Classical)\b/u);
  assert.doesNotMatch(raw.split('#eval')[1],
    /\b(?:referenceMinimum|terminalFullProfileMinimum|scanEquivalentSizes|allCandidates)\s/u);
});

test('M248 rejects supplied, finite-only and weakened closure theorem boundaries',async()=>{
  const source=await text0(SOURCE);
  for(const [before,after,category] of [
    ['(current : Implementation inputs outputs)','(current : Implementation 2 outputs)',
      'signature:runPhysicalNormalization_checked'],
    ['(current : Implementation inputs outputs) :\n    let execution',
      '(current : Implementation inputs outputs) (callerCertificate : True) :\n    let execution',
      'signature:runPhysicalNormalization_checked'],
    ['trace.gainIterations ≤ trace.savedGates','trace.gainIterations ≤ current.gateCount',
      'signature:PhysicalNormalizationTrace.checked'],
    ['residualSlack current =\n      residualSlack (runPhysicalNormalization current).result +',
      'residualSlack current ≤\n      residualSlack (runPhysicalNormalization current).result +',
      'signature:runPhysicalNormalization_residualSlack'],
  ]){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
});

test('M248 rejects dropped passes, unchecked stopping, fake savings and non-strict recursion',async()=>{
  const source=await text0(SOURCE);
  for(const [before,after,category] of [
    ['| .pruning => outputConeImplementation current','| .pruning => current','actual-three-pass-results'],
    ['| .sharing => (compileNANDSharing current.candidate.program).foldCount',
      '| .sharing => 0','actual-three-pass-savings'],
    ['∀ pass, physicalNormalizationPassSavings pass current = 0',
      '∃ pass, physicalNormalizationPassSavings pass current = 0','same-input-all-pass-stopping'],
    ['else if sharing : 0 < physicalNormalizationPassSavings .sharing current then',
      'else if sharing : 0 < physicalNormalizationPassSavings .pruning current then',
      'computed-priority-and-stopping'],
    ['| .step _ tail => tail.gainIterations + 1',
      '| .step _ tail => tail.gainIterations','actual-trace-iterations'],
    ['| .step gain tail => gain.savedGates + tail.savedGates',
      '| .step gain tail => gain.savedGates + tail.savedGates + 1','actual-trace-savings'],
    ['let tail := runPhysicalNormalization gain.result',
      'let tail := runPhysicalNormalization current','computed-strict-recursion'],
    ['termination_by current.gateCount','termination_by residualSlack current','computed-strict-recursion'],
    ['result := execution.result','result := current','computed-normalizer-result'],
  ]){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n').includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n').includes('unaudited-form'));
});

test('M248 durable workflow retains source contracts, exact audit and bounded regressions',async()=>{
  const [packageText,surface,verifier,workflow]=await Promise.all([
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),text0('.github/workflows/lean-bridge.yml')]);
  const auditPath='audits/lean-pccmin-physical-normalization-closure0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m248'],'node --test '+auditPath);
  assert.ok(surface.includes("'audit:m248': 'node --test "+auditPath+"'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test '+auditPath));
  for(const path of [auditPath,'docs/lean_pccmin_physical_normalization_closure.md'])
    assert.equal(workflow.split("      - '"+path.replace(/^audits\/lean-[^/]+\.test\.mjs$/u,'audits/lean-*.test.mjs').replace(/^docs\/lean_[^/]+\.md$/u,'docs/lean_*.md').replace(/^lean\/.*$/u,'lean/**').replace(/^lean-audit\/.*$/u,'lean-audit/**').replace(/^lean-regression\/.*$/u,'lean-regression/**')+"'").length-1,2);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M248_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-12-248';
const M248_MILESTONE = 'pccmin-physical-normalization-closure';
const M248_HASHES = Object.freeze({
  "PNP.DirectWire.physicalNormalizationPass_equivalent": "1e98dba1264aa27ff4c269a804a91c3280100aafeb59f4f000c84c1916f3d186",
  "PNP.DirectWire.physicalNormalizationPass_exact_accounting": "229aea7c24bfd7a753d61ab458d77663ab7afe172c669dae30155cf90dceccdb",
  "PNP.DirectWire.PhysicalNormalizationGain.checked": "427337b3b71051ea6183892626f713e70e71a95dbc47a589b6d041d5a82d1a33",
  "PNP.DirectWire.nextPhysicalNormalizationStep_checked": "1790d801558465f07fa0c179acef3b6ef54ce7e749207a96844b0bc38d5166b8",
  "PNP.DirectWire.PhysicalNormalizationTrace.checked": "a0a622312d96848ad1fa1080be5fe4922be9e260ef640539d021401739cb0ec5",
  "PNP.DirectWire.runPhysicalNormalization_checked": "dcc99d344b550bc094a11cb3c5276d275222849728f0532089e7b5cdf5b266a4",
  "PNP.DirectWire.runPhysicalNormalization_of_quiescent": "289992dec9ffe984bb89f69e00a6b4e2fdc7187c4bda3d53130f7d87c6195c8e",
  "PNP.DirectWire.runPhysicalNormalization_idempotent": "b11d9128d7a75c26f45a83ea6a800200f61acf33709d285bd809d1ae13031664",
  "PNP.DirectWire.runPhysicalNormalization_referenceMinimum": "962346c00f368bc0320f4008d01920dddab26c57f4cfb6e0c66571c7bfebecb1",
  "PNP.DirectWire.runPhysicalNormalization_residualSlack": "798ff693e7e90fbfd2d71794a07d1b9fe44c00d9e7509d6f73f412002276106b",
  "PNP.DirectWire.runPhysicalNormalization_gainIterations_le_residualSlack": "681cc73dd14a8ec8a6df53b1317bfb870911e3b54646d8ce58cccc4cba8378c9",
  "PNP.DirectWire.physicalClosureNormalizer_checked": "b5ae9aa84bf7be2011daca12a1a9f6213b8182b8a968265d116fecccdaa4509a"
});
const M248_STATUS_FIELDS = Object.freeze({
  "leanPCCMinPhysicalNormalizationClosureFormalized": true,
  "leanPCCMinPhysicalNormalizationClosureAxiomAuditPassed": true,
  "leanPCCMinPhysicalNormalizationClosureAuditedDeclarationCount": 12,
  "leanPCCMinPhysicalNormalizationClosurePassEquivalenceTheorem": "PNP.DirectWire.physicalNormalizationPass_equivalent",
  "leanPCCMinPhysicalNormalizationClosurePassAccountingTheorem": "PNP.DirectWire.physicalNormalizationPass_exact_accounting",
  "leanPCCMinPhysicalNormalizationClosureSelectedGainTheorem": "PNP.DirectWire.PhysicalNormalizationGain.checked",
  "leanPCCMinPhysicalNormalizationClosurePrioritySelectionTheorem": "PNP.DirectWire.nextPhysicalNormalizationStep_checked",
  "leanPCCMinPhysicalNormalizationClosureTraceAccountingTheorem": "PNP.DirectWire.PhysicalNormalizationTrace.checked",
  "leanPCCMinPhysicalNormalizationClosureComputedClosureTheorem": "PNP.DirectWire.runPhysicalNormalization_checked",
  "leanPCCMinPhysicalNormalizationClosureQuiescentInputTheorem": "PNP.DirectWire.runPhysicalNormalization_of_quiescent",
  "leanPCCMinPhysicalNormalizationClosureIdempotenceTheorem": "PNP.DirectWire.runPhysicalNormalization_idempotent",
  "leanPCCMinPhysicalNormalizationClosureReferenceMinimumTheorem": "PNP.DirectWire.runPhysicalNormalization_referenceMinimum",
  "leanPCCMinPhysicalNormalizationClosureResidualSlackTheorem": "PNP.DirectWire.runPhysicalNormalization_residualSlack",
  "leanPCCMinPhysicalNormalizationClosureIterationBoundTheorem": "PNP.DirectWire.runPhysicalNormalization_gainIterations_le_residualSlack",
  "leanPCCMinPhysicalNormalizationClosureNormalizerTheorem": "PNP.DirectWire.physicalClosureNormalizer_checked",
  "leanPCCMinPhysicalNormalizationClosureFullProfilePreservationProved": false,
  "leanPCCMinPhysicalNormalizationClosureCompleteNormalizationProved": false,
  "leanPCCMinPhysicalNormalizationClosurePolynomialRuntimeProved": false,
  "leanPCCMinPhysicalNormalizationClosureScope": "all-finite-direct-wire-implementations-computed-priority-three-pass-physical-closure-common-quiescence-actual-strict-trace-exact-savings-idempotent-result-no-complete-manuscript-normalization-or-polynomial-runtime"
});
const M248_AXIOMS = Object.freeze({
  "PNP.DirectWire.physicalNormalizationPass_equivalent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.physicalNormalizationPass_exact_accounting": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.PhysicalNormalizationGain.checked": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.nextPhysicalNormalizationStep_checked": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.PhysicalNormalizationTrace.checked": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.runPhysicalNormalization_checked": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.runPhysicalNormalization_of_quiescent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.runPhysicalNormalization_idempotent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.runPhysicalNormalization_referenceMinimum": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.runPhysicalNormalization_residualSlack": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.runPhysicalNormalization_gainIterations_le_residualSlack": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.physicalClosureNormalizer_checked": [
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

test('M248 compiled physical normalization-closure interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M248_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M248_COORDINATE)
    assert.equal(map.coordinate, M248_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M248_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, 'PNP.PCCMinPhysicalNormalizationClosure', name);
      assert.deepEqual(declaration.axioms, M248_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M248_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M248_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M248_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "operational quiescence for exactly three physical passes",
  "not semantic minimality",
  "arbitrary-support Pull/Expand materializer transport",
  "An iteration bound is not a runtime bound",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M248 publication rejects weakened, supplied, assumption-backed and widened physical closure substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M248_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M248_MILESTONE).earned, false, name);
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
  assert.equal(rejected.milestones.find(row => row.id === M248_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M248_MILESTONE
    ? {...row, nonClaim:'Three-pass quiescence proves complete normalization, semantic minimality and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M248 adds physical closure coverage without complete-normalization, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M248_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "total priority-respecting loop",
  "common operational quiescence",
  "Quiescence for these three passes is not semantic minimality",
  "No fixed weighted checkpoint or global gate changes",
  "evidence row changes coverage only"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M248_COORDINATE) return;
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

test('M248 current summaries distinguish three-pass quiescence from complete normalization and global completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_pccmin_physical_normalization_closure.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "No normalizer, oracle, result or stopping certificate is supplied by the caller",
  "operational quiescence for exactly three physical passes",
  "Quiescence does not imply semantic minimality or ZeroSlack",
  "Runtime execution is test evidence, not theorem authority",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-12-computed-physical-normalization-closure.md'));
  assert.match(plan, /Publication decision: defer PNPLabs(?:[.,]|$)/u);
  if (progress.asOfCoordinate !== M248_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_pccmin_physical_normalization_closure.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
