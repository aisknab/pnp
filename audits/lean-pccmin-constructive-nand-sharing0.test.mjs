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

const SOURCE = 'lean/PNP/PCCMinConstructiveNANDSharing.lean';
const AUDIT = 'lean-audit/PNPPCCMinConstructiveNANDSharingAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPPCCMinConstructiveNANDSharing.lean';
const NAMES = [
  "compileNANDSharing_alias_semantics",
  "compileNANDSharing_exact_accounting",
  "sharingImplementation_equivalent",
  "sharingImplementation_gateCount_le",
  "sharingImplementation_referenceMinimum",
  "sharingImplementation_residualSlack",
  "sharingImplementation_strictGain_iff",
  "sharingImplementation_strictResidualDescent",
  "nandSharingNormalizer_checked"
];
const SIGNATURES = [
  "theorem compileNANDSharing_alias_semantics {inputs gates : Nat} (program : Program inputs gates) (input : Valuation inputs) (index : Fin gates) : (compileNANDSharing program).program.eval input ((compileNANDSharing program).alias index) = program.eval input index",
  "theorem compileNANDSharing_exact_accounting {inputs gates : Nat} (program : Program inputs gates) : (compileNANDSharing program).gateCount + (compileNANDSharing program).foldCount = gates",
  "theorem sharingImplementation_equivalent {inputs outputs : Nat} (current : Implementation inputs outputs) : Equivalent (sharingImplementation current).candidate.program (sharingImplementation current).candidate.directWireWord current.candidate.program current.candidate.directWireWord",
  "theorem sharingImplementation_gateCount_le {inputs outputs : Nat} (current : Implementation inputs outputs) : (sharingImplementation current).gateCount ≤ current.gateCount",
  "theorem sharingImplementation_referenceMinimum {inputs outputs : Nat} (current : Implementation inputs outputs) : referenceMinimum (sharingImplementation current) = referenceMinimum current",
  "theorem sharingImplementation_residualSlack {inputs outputs : Nat} (current : Implementation inputs outputs) : residualSlack current = residualSlack (sharingImplementation current) + (compileNANDSharing current.candidate.program).foldCount",
  "theorem sharingImplementation_strictGain_iff {inputs outputs : Nat} (current : Implementation inputs outputs) : StrictEquivalentGain current (sharingImplementation current) ↔ 0 < (compileNANDSharing current.candidate.program).foldCount",
  "theorem sharingImplementation_strictResidualDescent {inputs outputs : Nat} (current : Implementation inputs outputs) (positive : 0 < (compileNANDSharing current.candidate.program).foldCount) : residualSlack (sharingImplementation current) < residualSlack current",
  "theorem nandSharingNormalizer_checked {inputs outputs : Nat} (current : Implementation inputs outputs) : match nandSharingNormalizer.normalize current with | .gain next _ => next = sharingImplementation current ∧ 0 < (compileNANDSharing current.candidate.program).foldCount | .normal normalized => normalized.result = sharingImplementation current ∧ (compileNANDSharing current.candidate.program).foldCount = 0 ∧ normalized.result.gateCount = current.gateCount"
];
const PUBLIC_HEADS = [
  "Source.sharingRename",
  "sharingFindGate",
  "NANDSharingCompilation",
  "compileNANDSharing",
  "compileNANDSharing_alias_semantics",
  "compileNANDSharing_exact_accounting",
  "sharingImplementation",
  "sharingImplementation_equivalent",
  "sharingImplementation_gateCount_le",
  "sharingImplementation_referenceMinimum",
  "sharingImplementation_residualSlack",
  "sharingImplementation_strictGain_iff",
  "sharingImplementation_strictResidualDescent",
  "nandSharingNormalizer",
  "nandSharingNormalizer_checked"
];
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = value => stripLeanCommentsAndStrings0(value).replace(/\s+/gu, ' ').trim();
function block0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex(head => head.name === name);
  return index < 0 ? '' : source.slice(heads[index].index, heads[index + 1]?.index ?? source.length);
}
function validateSource0(source) {
  const failures = [];
  const require0 = (condition, category) => { if (!condition) failures.push(category); };
  const clean = compact0(source);
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|callerCertificate|suppliedOptimizer)\b/u
    .test(clean), 'shortcut-or-certificate');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]))
    === JSON.stringify(['PNP.PCCMinNormalizeOracleComposition',
      'PNP.ResidualTerminalPhysicalSupportCompletion']), 'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head => head.name)) ===
    JSON.stringify(PUBLIC_HEADS), 'public-interface');
  for (const [index,name] of NAMES.entries())
    require0(compact0(block0(source,name)).startsWith(SIGNATURES[index] + ' := '),
      'signature:' + name);
  const compiler = compact0(block0(source,'compileNANDSharing'));
  require0(compiler.includes('def compileNANDSharing {inputs gates : Nat} (program : Program inputs gates) : NANDSharingCompilation program :='),
    'arbitrary-program-input');
  for (const token of ['let compiled := compileNANDSharing initial',
    'sharingFindGate compiled.program (sharingRenameGate compiled.alias gate)',
    '| none => sharingAppend compiled gate', '| some found => sharingReuse compiled gate found checked'])
    require0(compiler.includes(token), 'complete-computed-pass');
  require0(!/\b(?:allCandidates|allValuations|equivalentBool|referenceMinimumWitness|scanEquivalentSizes)\b/u
    .test(compiler), 'no-semantic-search');
  require0(compact0(block0(source,'sharingFindGate')).includes(
    'sharingFindGateIn program gate (allFin gates)'), 'actual-retained-gates');
  for (const token of ['let pair := program.terminalGateSources index',
    '(pair.1 = gate.left ∧ pair.2 = gate.right) ∨ (pair.1 = gate.right ∧ pair.2 = gate.left)'])
    require0(clean.includes(token), 'structural-match');
  require0(compact0(block0(source,'Source.sharingRename')).includes('| .gate index => .gate (alias index)'),
    'computed-source-alias');
  for (const token of ['program := compiled.program.snoc (sharingRenameGate compiled.alias gate)',
    'alias := sharingExtend compiled.alias found', 'foldCount := compiled.foldCount + 1',
    'gate_accounting : gateCount + foldCount = gates'])
    require0(clean.includes(token), 'actual-fold-accounting');
  const implementation=compact0(block0(source,'sharingImplementation'));
  for (const token of ['Candidate.ofDirectWireWord compiled.program',
    '(current.candidate.directWireWord.source output).sharingRename compiled.alias'])
    require0(implementation.includes(token), 'all-ordered-outputs');
  const normalizer=compact0(block0(source,'nandSharingNormalizer'));
  for (const token of ['if positive : 0 < (compileNANDSharing current.candidate.program).foldCount',
    '.gain (sharingImplementation current)', '(sharingImplementation_strictGain_iff current).mpr positive',
    'equivalent := sharingImplementation_equivalent current',
    'gateCount_le := sharingImplementation_gateCount_le current'])
    require0(normalizer.includes(token), 'computed-normalizer');
  return [...new Set(failures)];
}

test('M242 computes whole-program structural sharing and all nine general laws', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE)), []);
});

test('M242 explicit root, axiom audit and reviewed-name producers agree', async () => {
  const [source,audit,inventorySource,root]=await Promise.all([
    text0(SOURCE),text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean'),
  ]);
  for(const name of NAMES) {
    assert.equal(explicitLeanDeclarationHeads0(source).filter(head=>head.name===name).length,1);
    const fullName='PNP.DirectWire.'+name;
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item=>item===fullName).length,1);
    assert.equal(inventorySource.split(String.fromCharCode(96)+fullName+',').length-1,1);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),
    NAMES.map(name=>'PNP.DirectWire.'+name));
  assert.match(root,/^import PNP\.PCCMinConstructiveNANDSharing\s*$/mu);
});

test('M242 regressions cover cascading reuse, commutation, outputs, empty dimensions and a nonminimal no-fold branch', async () => {
  const raw=await text0(REGRESSION), regression=compact0(raw);
  for(const name of NAMES) assert.ok(regression.includes(name+' '),name);
  for(const token of [
    'cascadeProgram : Program 2 6', 'cascade : Implementation 2 8',
    '[0, 0, 1, 1, 2, 2]', 'twoGateAlternative : Implementation 2 8',
    'StrictEquivalentGain (sharingImplementation cascade) twoGateAlternative',
    '0 < residualSlack (sharingImplementation cascade)', 'noGates : Implementation 0 0',
    'constantPair : Program 0 2', 'unequalPair : Program 2 2',
    'runPCCMinNormalizeOracleLoop nandSharingNormalizer oracle current',
    'throw (IO.userError',
  ]) assert.ok(regression.includes(token),token);
  assert.equal([...raw.matchAll(/^#eval\b/gmu)].length,1);
  assert.doesNotMatch(regression,/\b(?:sorry|admit|native_decide|Classical)\b/u);
  assert.doesNotMatch(raw.split('#eval')[1],/\b(?:referenceMinimum|equivalentBool|strictEquivalentGainBool)\s/u);
});

test('M242 rejects finite-only, supplied-optimizer and weakened equivalence or gain boundaries', async () => {
  const source=await text0(SOURCE);
  const mutations=[
    ['(program : Program inputs gates)', '(program : Program inputs 6)', 'signature:'+NAMES[0]],
    ['(program : Program inputs gates) :\n    NANDSharingCompilation program',
      '(program : Program inputs gates) (suppliedOptimizer : True) :\n    NANDSharingCompilation program',
      'arbitrary-program-input'],
    ['current.candidate.program current.candidate.directWireWord := by',
      'current.candidate.program current.candidate.directWireWord ∨ True := by',
      'signature:'+NAMES[2]],
    ['residualSlack (sharingImplementation current) < residualSlack current :=',
      'residualSlack (sharingImplementation current) ≤ residualSlack current :=',
      'signature:'+NAMES[7]],
    ['(current : Implementation inputs outputs) :\n    referenceMinimum',
      '(current : Implementation inputs outputs) (callerCertificate : True) :\n    referenceMinimum',
      'signature:'+NAMES[4]],
  ];
  for(const [before,after,category] of mutations){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
});

test('M242 rejects fake lookups, lost aliases, invented savings and incomplete normalizer execution', async () => {
  const source=await text0(SOURCE);
  const mutations=[
    ['sharingFindGateIn program gate (allFin gates)','sharingFindGateIn program gate []','actual-retained-gates'],
    ['(pair.1 = gate.left ∧ pair.2 = gate.right)','(pair.1 = gate.left ∨ pair.2 = gate.right)','structural-match'],
    ['| .gate index => .gate (alias index)','| .gate index => .constant true','computed-source-alias'],
    ['foldCount := compiled.foldCount + 1','foldCount := compiled.foldCount + 2','actual-fold-accounting'],
    ['| some found => sharingReuse compiled gate found checked','| some found => sharingAppend compiled gate','complete-computed-pass'],
    ['(current.candidate.directWireWord.source output).sharingRename','(Source.constant false).sharingRename','all-ordered-outputs'],
    ['if positive : 0 < (compileNANDSharing current.candidate.program).foldCount',
      'if positive : False','computed-normalizer'],
  ];
  for(const [before,after,category] of mutations){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n').includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n').includes('unaudited-form'));
});

test('M242 durable workflow includes source contracts, strict root audit and guarded regressions', async () => {
  const [packageText,surface,verifier,workflow]=await Promise.all([
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),text0('.github/workflows/lean-bridge.yml'),
  ]);
  const auditPath='audits/lean-pccmin-constructive-nand-sharing0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m242'],'node --test '+auditPath);
  assert.ok(surface.includes("'audit:m242': 'node --test "+auditPath+"'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test '+auditPath));
  for(const path of [auditPath,'docs/lean_pccmin_constructive_nand_sharing.md'])
    assertLeanWorkflowPathCoverage0(workflow, path);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M242_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-12-242';
const M242_MILESTONE = 'pccmin-constructive-nand-sharing';
const M242_HASHES = Object.freeze({
  "PNP.DirectWire.compileNANDSharing_alias_semantics": "4deb034903ad839c8a3b4b239a3eedac0b9015b2ca80f813887ab3fe0da96822",
  "PNP.DirectWire.compileNANDSharing_exact_accounting": "164deeba19f4e72d48b14460ecf95cab0aaaa5d9f1bd0d7c162197c2254c0c82",
  "PNP.DirectWire.sharingImplementation_equivalent": "bf6462df6f7b2be0f1e107c0de6e9dbfe0d60f95207d32da437ba4d3e9bba1f8",
  "PNP.DirectWire.sharingImplementation_gateCount_le": "2e8b717281088e2f705da023dcf9c3e70c36eb734e6b2e1cc21d011f743fe5b4",
  "PNP.DirectWire.sharingImplementation_referenceMinimum": "1765f52468d594f9b61339121daf6522ab56cc1b1b2ce3c8ea0bc7a5b339a263",
  "PNP.DirectWire.sharingImplementation_residualSlack": "a5dee1ecca503f2fbc2d154a79fece88bf4c9b22ba1b836c17222e62731cae1d",
  "PNP.DirectWire.sharingImplementation_strictGain_iff": "5de93eb4cd692308ffce27770919129d605624fc0b0983d46cbe1f6fc675104d",
  "PNP.DirectWire.sharingImplementation_strictResidualDescent": "78ca908349b5ce03bd5e8585dcfed98eb3a24cd860337fab2681d8e435cc19cf",
  "PNP.DirectWire.nandSharingNormalizer_checked": "9ad481fa3cf574495fe90302d3f8945fe4917791935b065cbc86f51aef60b7fd"
});
const M242_STATUS_FIELDS = Object.freeze({
  "leanPCCMinConstructiveNANDSharingFormalized": true,
  "leanPCCMinConstructiveNANDSharingAxiomAuditPassed": true,
  "leanPCCMinConstructiveNANDSharingAuditedDeclarationCount": 9,
  "leanPCCMinConstructiveNANDSharingAliasSemanticsTheorem": "PNP.DirectWire.compileNANDSharing_alias_semantics",
  "leanPCCMinConstructiveNANDSharingGateAccountingTheorem": "PNP.DirectWire.compileNANDSharing_exact_accounting",
  "leanPCCMinConstructiveNANDSharingEquivalenceTheorem": "PNP.DirectWire.sharingImplementation_equivalent",
  "leanPCCMinConstructiveNANDSharingGateCountTheorem": "PNP.DirectWire.sharingImplementation_gateCount_le",
  "leanPCCMinConstructiveNANDSharingReferenceMinimumTheorem": "PNP.DirectWire.sharingImplementation_referenceMinimum",
  "leanPCCMinConstructiveNANDSharingResidualSlackTheorem": "PNP.DirectWire.sharingImplementation_residualSlack",
  "leanPCCMinConstructiveNANDSharingStrictGainTheorem": "PNP.DirectWire.sharingImplementation_strictGain_iff",
  "leanPCCMinConstructiveNANDSharingStrictResidualDescentTheorem": "PNP.DirectWire.sharingImplementation_strictResidualDescent",
  "leanPCCMinConstructiveNANDSharingNormalizerTheorem": "PNP.DirectWire.nandSharingNormalizer_checked",
  "leanPCCMinConstructiveNANDSharingScope": "all-finite-nand-programs-and-ordered-outputs-computed-structural-and-commuted-reuse-alias-semantics-exact-fold-accounting-invariant-reference-minimum-residual-descent-and-concrete-normalizer-stage-only"
});
const M242_AXIOMS = Object.freeze({
  "PNP.DirectWire.compileNANDSharing_alias_semantics": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.compileNANDSharing_exact_accounting": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.sharingImplementation_equivalent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.sharingImplementation_gateCount_le": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.sharingImplementation_referenceMinimum": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.sharingImplementation_residualSlack": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.sharingImplementation_strictGain_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.sharingImplementation_strictResidualDescent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.nandSharingNormalizer_checked": [
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

test('M242 compiled constructive sharing and normalizer interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M242_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M242_COORDINATE)
    assert.equal(map.coordinate, M242_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M242_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, 'PNP.PCCMinConstructiveNANDSharing', name);
      assert.deepEqual(declaration.axioms, M242_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M242_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M242_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M242_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "computed physical R1/R4 structural-sharing stage",
  "not complete manuscript N1-N10 normalization",
  "A no-fold branch does not imply semantic minimality",
  "Reference minimum occurs in specification theorems, not in execution of this pass",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M242 publication rejects weakened, supplied, assumption-backed and widened sharing/normalization substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M242_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M242_MILESTONE).earned, false, name);
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
  assert.equal(rejected.milestones.find(row => row.id === M242_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M242_MILESTONE
    ? {...row, nonClaim:'Structural sharing proves complete normalization, semantic minimality and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M242 adds constructive sharing coverage without complete-normalization, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M242_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "general whole-program NAND-sharing stage",
  "every alias and reuse decision is computed",
  "A no-fold branch is not semantic minimality or ZeroSlack",
  "No fixed weighted checkpoint or global gate changes",
  "evidence row changes coverage only"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M242_COORDINATE) return;
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

test('M242 current summaries distinguish constructive sharing from complete normalization and global route completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_pccmin_constructive_nand_sharing.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "No optimizer or correctness certificate is supplied by the caller",
  "computed physical R1/R4 structural-sharing stage",
  "not complete manuscript N1-N10 normalization",
  "A no-fold branch does not imply semantic minimality",
  "Runtime execution is test evidence, not theorem authority",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-12-constructive-nand-sharing.md'));
  assert.ok(plan.includes('Publication decision: defer'));
  if (progress.asOfCoordinate !== M242_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_pccmin_constructive_nand_sharing.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
