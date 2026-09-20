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

const SOURCE = 'lean/PNP/PCCMinConstantPropagation.lean';
const AUDIT = 'lean-audit/PNPConstantPropagationAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPConstantPropagation.lean';
const NAMES = [
  "constantGateValue_sound",
  "compileNANDConstantPropagation_alias_semantics",
  "compileNANDConstantPropagation_exact_accounting",
  "constantPropagationImplementation_equivalent",
  "constantPropagationImplementation_gateCount_le",
  "constantPropagationImplementation_referenceMinimum",
  "constantPropagationImplementation_residualSlack",
  "constantPropagationImplementation_strictGain_iff",
  "constantPropagationImplementation_strictResidualDescent",
  "nandConstantPropagationNormalizer_checked"
];
const SIGNATURES = [
  "theorem constantGateValue_sound {inputs gates : Nat} (gate : Gate inputs gates) (value : Bool) (checked : constantGateValue gate = some value) (input : Valuation inputs) (retained : Valuation gates) : value = gate.eval input retained",
  "theorem compileNANDConstantPropagation_alias_semantics {inputs gates : Nat} (program : Program inputs gates) (input : Valuation inputs) (index : Fin gates) : ((compileNANDConstantPropagation program).alias index).eval input ((compileNANDConstantPropagation program).program.eval input) = program.eval input index",
  "theorem compileNANDConstantPropagation_exact_accounting {inputs gates : Nat} (program : Program inputs gates) : (compileNANDConstantPropagation program).gateCount + (compileNANDConstantPropagation program).eliminationCount = gates",
  "theorem constantPropagationImplementation_equivalent {inputs outputs : Nat} (current : Implementation inputs outputs) : Equivalent (constantPropagationImplementation current).candidate.program (constantPropagationImplementation current).candidate.directWireWord current.candidate.program current.candidate.directWireWord",
  "theorem constantPropagationImplementation_gateCount_le {inputs outputs : Nat} (current : Implementation inputs outputs) : (constantPropagationImplementation current).gateCount ≤ current.gateCount",
  "theorem constantPropagationImplementation_referenceMinimum {inputs outputs : Nat} (current : Implementation inputs outputs) : referenceMinimum (constantPropagationImplementation current) = referenceMinimum current",
  "theorem constantPropagationImplementation_residualSlack {inputs outputs : Nat} (current : Implementation inputs outputs) : residualSlack current = residualSlack (constantPropagationImplementation current) + (compileNANDConstantPropagation current.candidate.program).eliminationCount",
  "theorem constantPropagationImplementation_strictGain_iff {inputs outputs : Nat} (current : Implementation inputs outputs) : StrictEquivalentGain current (constantPropagationImplementation current) ↔ 0 < (compileNANDConstantPropagation current.candidate.program).eliminationCount",
  "theorem constantPropagationImplementation_strictResidualDescent {inputs outputs : Nat} (current : Implementation inputs outputs) (positive : 0 < (compileNANDConstantPropagation current.candidate.program).eliminationCount) : residualSlack (constantPropagationImplementation current) < residualSlack current",
  "theorem nandConstantPropagationNormalizer_checked {inputs outputs : Nat} (current : Implementation inputs outputs) : match nandConstantPropagationNormalizer.normalize current with | .gain next _ => next = constantPropagationImplementation current ∧ 0 < (compileNANDConstantPropagation current.candidate.program).eliminationCount | .normal normalized => normalized.result = constantPropagationImplementation current ∧ (compileNANDConstantPropagation current.candidate.program).eliminationCount = 0 ∧ normalized.result.gateCount = current.gateCount"
];
const PUBLIC_HEADS = [
  "Source.propagationRename",
  "constantGateValue",
  "constantGateValue_sound",
  "NANDConstantPropagationCompilation",
  "compileNANDConstantPropagation",
  "compileNANDConstantPropagation_alias_semantics",
  "compileNANDConstantPropagation_exact_accounting",
  "constantPropagationImplementation",
  "constantPropagationImplementation_equivalent",
  "constantPropagationImplementation_gateCount_le",
  "constantPropagationImplementation_referenceMinimum",
  "constantPropagationImplementation_residualSlack",
  "constantPropagationImplementation_strictGain_iff",
  "constantPropagationImplementation_strictResidualDescent",
  "nandConstantPropagationNormalizer",
  "nandConstantPropagationNormalizer_checked"
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
    JSON.stringify(['PNP.PCCMinNormalizeOracleComposition','PNP.NANDComposition']),'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name))===
    JSON.stringify(PUBLIC_HEADS),'public-interface');
  for(const [index,name] of NAMES.entries())
    require0(compact0(block0(source,name)).startsWith(SIGNATURES[index]+' := '),'signature:'+name);
  const rename=compact0(block0(source,'Source.propagationRename'));
  for(const token of ['Fin fromGates → Source inputs toGates','| .input index => .input index',
    '| .constant value => .constant value','| .gate index => alias index'])
    require0(rename.includes(token),'actual-source-aliases');
  const recognition=compact0(block0(source,'constantGateValue'));
  for(const token of [
    'if gate.left = .constant false ∨ gate.right = .constant false then some true',
    'else if gate.left = .constant true ∧ gate.right = .constant true then some false',
    'else none',
  ])require0(recognition.includes(token),'exact-constant-identities');
  const compile=compact0(block0(source,'compileNANDConstantPropagation'));
  for(const token of [
    'match program with','| .empty =>','alias := Fin.elim0','eliminationCount := 0',
    '| .snoc initial gate =>','let compiled := compileNANDConstantPropagation initial',
    'match checked : constantGateValue (propagationRenameGate compiled.alias gate) with',
    '| none => propagationAppend compiled gate',
    '| some value => propagationEliminate compiled gate value checked',
  ])require0(compile.includes(token),'complete-computed-pass');
  const eliminate=compact0(source.slice(source.indexOf('private def propagationEliminate '),
    source.indexOf('def compileNANDConstantPropagation ')));
  for(const token of ['program := compiled.program',
    'alias := propagationExtend compiled.alias (.constant value)',
    'eliminationCount := compiled.eliminationCount + 1'])
    require0(eliminate.includes(token),'actual-elimination-accounting');
  const implementation=compact0(block0(source,'constantPropagationImplementation'));
  for(const token of ['let compiled := compileNANDConstantPropagation current.candidate.program',
    'gateCount := compiled.gateCount','Candidate.ofDirectWireWord compiled.program',
    '⟨fun output => (current.candidate.directWireWord.source output).propagationRename compiled.alias⟩'])
    require0(implementation.includes(token),'complete-output-rewrite');
  const normalizer=compact0(block0(source,'nandConstantPropagationNormalizer'));
  for(const token of ['if positive : 0 <',
    '(compileNANDConstantPropagation current.candidate.program).eliminationCount then',
    '.gain (constantPropagationImplementation current)',
    '(constantPropagationImplementation_strictGain_iff current).mpr positive',
    'result := constantPropagationImplementation current',
    'equivalent := constantPropagationImplementation_equivalent current',
    'gateCount_le := constantPropagationImplementation_gateCount_le current'])
    require0(normalizer.includes(token),'computed-normalizer-result');
  require0(!/\b(?:allCandidates|allValuations|allSubsets|equivalentBool|referenceMinimumWitness|scanEquivalentSizes|referenceMinimum|terminalFullProfileMinimum)\b/u
    .test([recognition,compile,eliminate,implementation,normalizer].join(' ')),'no-exhaustive-search');
  return [...new Set(failures)];
}

test('M247 computes whole-program source aliases and constant elimination with ten general laws', async()=>{
  assert.deepEqual(validateSource0(await text0(SOURCE)),[]);
});

test('M247 explicit root, exact audit and reviewed-name producers agree',async()=>{
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
  assert.match(root,/^import PNP\.PCCMinConstantPropagation\s*$/mu);
});

test('M247 regressions cover cascading constants, ordered outputs and the nonminimum stopping boundary',async()=>{
  const raw=await text0(REGRESSION), regression=compact0(raw);
  for(const name of NAMES)assert.ok(regression.includes(name),name);
  for(const token of ['cascadeProgram : Program 2 4','cascade : Implementation 2 7',
    'noGates : Implementation 0 0','correlatedProgram : Program 1 2',
    'constantAlternative : Implementation 1 1','StrictEquivalentGain correlated constantAlternative',
    'compiled.gateCount != 1 || compiled.eliminationCount != 3',
    'leftFalse : Gate 1 0','rightFalse : Gate 1 0',
    'constantGateValue retained != none','(allFin 7).map',
    'true, false, true, boolNand left right, left, false, boolNand left right',
    '0 < residualSlack correlated','throw (IO.userError'])
    assert.ok(regression.includes(token),token);
  assert.equal([...raw.matchAll(/^#eval\b/gmu)].length,1);
  assert.doesNotMatch(regression,/\b(?:sorry|admit|native_decide|Classical)\b/u);
  assert.doesNotMatch(raw.split('#eval')[1],
    /\b(?:referenceMinimum|terminalFullProfileMinimum|scanEquivalentSizes|allCandidates)\s/u);
});

test('M247 rejects supplied, finite-only and weakened constant-propagation theorem boundaries',async()=>{
  const source=await text0(SOURCE);
  for(const [before,after,category] of [
    ['(program : Program inputs gates)','(program : Program 2 gates)',
      'signature:compileNANDConstantPropagation_alias_semantics'],
    ['StrictEquivalentGain current (constantPropagationImplementation current) ↔',
      'StrictEquivalentGain current (constantPropagationImplementation current) →',
      'signature:constantPropagationImplementation_strictGain_iff'],
    ['(current : Implementation inputs outputs) :\n    Equivalent',
      '(current : Implementation inputs outputs) (callerCertificate : True) :\n    Equivalent',
      'signature:constantPropagationImplementation_equivalent'],
    ['residualSlack (constantPropagationImplementation current) < residualSlack current',
      'residualSlack (constantPropagationImplementation current) ≤ residualSlack current',
      'signature:constantPropagationImplementation_strictResidualDescent'],
  ]){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
});

test('M247 rejects wrong NAND constants, fabricated aliases, savings and omitted output rewriting',async()=>{
  const source=await text0(SOURCE);
  for(const [before,after,category] of [
    ['| .gate index => alias index','| .gate index => .constant false','actual-source-aliases'],
    ['gate.right = .constant false then some true',
      'gate.right = .constant false then some false','exact-constant-identities'],
    ['match checked : constantGateValue (propagationRenameGate compiled.alias gate) with',
      'match checked : constantGateValue gate with','complete-computed-pass'],
    ['alias := propagationExtend compiled.alias (.constant value)',
      'alias := propagationExtend compiled.alias (.constant (!value))','actual-elimination-accounting'],
    ['eliminationCount := compiled.eliminationCount + 1',
      'eliminationCount := compiled.eliminationCount + 2','actual-elimination-accounting'],
    ['(current.candidate.directWireWord.source output).propagationRename compiled.alias',
      '(current.candidate.directWireWord.source 0).propagationRename compiled.alias','complete-output-rewrite'],
    ['result := constantPropagationImplementation current',
      'result := current','computed-normalizer-result'],
  ]){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n').includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n').includes('unaudited-form'));
});

test('M247 durable workflow retains source contracts, exact audit and bounded regressions',async()=>{
  const [packageText,surface,verifier,workflow]=await Promise.all([
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),text0('.github/workflows/lean-bridge.yml')]);
  const auditPath='audits/lean-pccmin-constant-propagation0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m247'],'node --test '+auditPath);
  assert.ok(surface.includes("'audit:m247': 'node --test "+auditPath+"'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test '+auditPath));
  for(const path of [auditPath,'docs/lean_pccmin_constant_propagation.md'])
    assertLeanWorkflowPathCoverage0(workflow, path);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M247_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-12-247';
const M247_MILESTONE = 'pccmin-constant-propagation';
const M247_HASHES = Object.freeze({
  "PNP.DirectWire.constantGateValue_sound": "0ec6cff2be375dc0eb181e160e267405a485d3e2ac41b4a8cec33b994f02b2a8",
  "PNP.DirectWire.compileNANDConstantPropagation_alias_semantics": "499c24a8a4455a18159223191f8879034e87f39f45493973fb81c4076c4ced7e",
  "PNP.DirectWire.compileNANDConstantPropagation_exact_accounting": "50d1f42a8732f6563a48dec3a1c364f41ed9fccfb0b4c7ed72faa382c3013c87",
  "PNP.DirectWire.constantPropagationImplementation_equivalent": "85b42a5ccf8a28af9ba9b19ee9b73eecc63dfe63ca306777b395881fc6c9aabc",
  "PNP.DirectWire.constantPropagationImplementation_gateCount_le": "7da5157348a386861cf8b2cb5ef617fc89d16409f8640de9376957b344b3ab29",
  "PNP.DirectWire.constantPropagationImplementation_referenceMinimum": "9631c6094e82f3e0ce1b4c45bb4fa4e892321fd2746ff3437cddafd9130c9ae3",
  "PNP.DirectWire.constantPropagationImplementation_residualSlack": "532ee6acbab9c551e3da7a3cb6296b1c405458f6bb821e059826bb3aed1c0981",
  "PNP.DirectWire.constantPropagationImplementation_strictGain_iff": "f2447341b74dc43f0d98a5fb3a63dc153eef0da71d28017060be06238796d7e6",
  "PNP.DirectWire.constantPropagationImplementation_strictResidualDescent": "96c02d048c9f50fb371e546364a55c1d5bf364fdcb626b38aafda1f9724fb785",
  "PNP.DirectWire.nandConstantPropagationNormalizer_checked": "7d26c6a7ceba21244ab334e8524b55ee9ff5e0f046c5c535506d2553f8106b3b"
});
const M247_STATUS_FIELDS = Object.freeze({
  "leanPCCMinConstantPropagationFormalized": true,
  "leanPCCMinConstantPropagationAxiomAuditPassed": true,
  "leanPCCMinConstantPropagationAuditedDeclarationCount": 10,
  "leanPCCMinConstantPropagationConstantRuleTheorem": "PNP.DirectWire.constantGateValue_sound",
  "leanPCCMinConstantPropagationAliasSemanticsTheorem": "PNP.DirectWire.compileNANDConstantPropagation_alias_semantics",
  "leanPCCMinConstantPropagationGateAccountingTheorem": "PNP.DirectWire.compileNANDConstantPropagation_exact_accounting",
  "leanPCCMinConstantPropagationEquivalenceTheorem": "PNP.DirectWire.constantPropagationImplementation_equivalent",
  "leanPCCMinConstantPropagationGateCountTheorem": "PNP.DirectWire.constantPropagationImplementation_gateCount_le",
  "leanPCCMinConstantPropagationReferenceMinimumTheorem": "PNP.DirectWire.constantPropagationImplementation_referenceMinimum",
  "leanPCCMinConstantPropagationResidualSlackTheorem": "PNP.DirectWire.constantPropagationImplementation_residualSlack",
  "leanPCCMinConstantPropagationStrictGainTheorem": "PNP.DirectWire.constantPropagationImplementation_strictGain_iff",
  "leanPCCMinConstantPropagationResidualDescentTheorem": "PNP.DirectWire.constantPropagationImplementation_strictResidualDescent",
  "leanPCCMinConstantPropagationNormalizerTheorem": "PNP.DirectWire.nandConstantPropagationNormalizer_checked",
  "leanPCCMinConstantPropagationFullProfilePreservationProved": false,
  "leanPCCMinConstantPropagationCompleteNormalizationProved": false,
  "leanPCCMinConstantPropagationPolynomialRuntimeProved": false,
  "leanPCCMinConstantPropagationScope": "all-finite-direct-wire-nand-programs-computed-literal-constant-propagation-through-source-aliases-complete-ordered-io-exact-elimination-accounting-physical-normalizer-stage-only"
});
const M247_AXIOMS = Object.freeze({
  "PNP.DirectWire.constantGateValue_sound": [],
  "PNP.DirectWire.compileNANDConstantPropagation_alias_semantics": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.compileNANDConstantPropagation_exact_accounting": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.constantPropagationImplementation_equivalent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.constantPropagationImplementation_gateCount_le": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.constantPropagationImplementation_referenceMinimum": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.constantPropagationImplementation_residualSlack": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.constantPropagationImplementation_strictGain_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.constantPropagationImplementation_strictResidualDescent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.nandConstantPropagationNormalizer_checked": [
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

test('M247 compiled NAND constant-propagation interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M247_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M247_COORDINATE)
    assert.equal(map.coordinate, M247_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M247_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, 'PNP.PCCMinConstantPropagation', name);
      assert.deepEqual(declaration.axioms, M247_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M247_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M247_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M247_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "physical literal-constant structural-congruence component",
  "not complete manuscript R1-R9 verification or N1-N10 normalization",
  "No-elimination does not imply semantic minimality or ZeroSlack",
  "reference minimum is used only in specification theorems",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M247 publication rejects weakened, supplied, assumption-backed and widened constant-propagation substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M247_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M247_MILESTONE).earned, false, name);
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
  assert.equal(rejected.milestones.find(row => row.id === M247_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M247_MILESTONE
    ? {...row, nonClaim:'Literal constant propagation proves complete normalization, semantic minimality and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M247 adds constant-propagation coverage without complete-normalization, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M247_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "physical literal-constant structural-congruence pass",
  "Actual source aliases propagate earlier constants",
  "no-elimination branch is not semantic minimality",
  "No fixed weighted checkpoint or global gate changes",
  "evidence row changes coverage only"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M247_COORDINATE) return;
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

test('M247 current summaries distinguish physical constant propagation from complete normalization and global completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_pccmin_constant_propagation.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "No optimizer, result or correctness assertion is supplied by the caller",
  "physical literal-constant structural-congruence component",
  "No-elimination does not imply semantic minimality or ZeroSlack",
  "Runtime execution is test evidence, not theorem authority",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-12-computed-nand-constant-propagation.md'));
  assert.ok(plan.includes('Publication decision: defer PNPLabs.'));
  if (progress.asOfCoordinate !== M247_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_pccmin_constant_propagation.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
