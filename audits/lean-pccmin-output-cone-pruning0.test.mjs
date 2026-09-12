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

const SOURCE = 'lean/PNP/PCCMinOutputConePruning.lean';
const AUDIT = 'lean-audit/PNPOutputConePruningAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPOutputConePruning.lean';
const NAMES = [
  "outputConeRecords_output",
  "outputConeRecords_closed",
  "outputConeRecords_least",
  "outputConeRecords_noExternalGate",
  "outputConeImplementation_equivalent",
  "outputConeImplementation_gateCount_le",
  "outputConeImplementation_exact_accounting",
  "outputConeImplementation_referenceMinimum",
  "outputConeImplementation_residualSlack",
  "outputConeImplementation_strictGain_iff",
  "outputConeNormalizer_checked"
];
const SIGNATURES = [
  "theorem outputConeRecords_output {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs) (producer : Fin gates) (isOutput : terminalGateIsGlobalOutput candidate.directWireWord producer = true) : TerminalPrimitiveRecord.gate producer ∈ outputConeRecords candidate",
  "theorem outputConeRecords_closed {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs) (consumer producer : Fin gates) (selected : TerminalPrimitiveRecord.gate consumer ∈ outputConeRecords candidate) (uses : candidate.program.terminalGateUsesWire consumer (.gate producer) = true) : TerminalPrimitiveRecord.gate producer ∈ outputConeRecords candidate",
  "theorem outputConeRecords_least {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs) (support : Fin gates → Prop) (containsOutputs : ∀ producer, terminalGateIsGlobalOutput candidate.directWireWord producer = true → support producer) (closed : ∀ consumer producer, support consumer → candidate.program.terminalGateUsesWire consumer (.gate producer) = true → support producer) (producer : Fin gates) (selected : TerminalPrimitiveRecord.gate producer ∈ outputConeRecords candidate) : support producer",
  "theorem outputConeRecords_noExternalGate {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs) (producer : Fin gates) : TerminalSupportWire.gate producer ∉ terminalBoundaryPorts candidate.program (outputConeRecords candidate)",
  "theorem outputConeImplementation_equivalent {inputs outputs : Nat} (current : Implementation inputs outputs) : Equivalent (outputConeImplementation current).candidate.program (outputConeImplementation current).candidate.directWireWord current.candidate.program current.candidate.directWireWord",
  "theorem outputConeImplementation_gateCount_le {inputs outputs : Nat} (current : Implementation inputs outputs) : (outputConeImplementation current).gateCount ≤ current.gateCount",
  "theorem outputConeImplementation_exact_accounting {inputs outputs : Nat} (current : Implementation inputs outputs) : (outputConeImplementation current).gateCount + outputConeDeletedGateCount current = current.gateCount",
  "theorem outputConeImplementation_referenceMinimum {inputs outputs : Nat} (current : Implementation inputs outputs) : referenceMinimum (outputConeImplementation current) = referenceMinimum current",
  "theorem outputConeImplementation_residualSlack {inputs outputs : Nat} (current : Implementation inputs outputs) : residualSlack current = residualSlack (outputConeImplementation current) + outputConeDeletedGateCount current",
  "theorem outputConeImplementation_strictGain_iff {inputs outputs : Nat} (current : Implementation inputs outputs) : StrictEquivalentGain current (outputConeImplementation current) ↔ 0 < outputConeDeletedGateCount current",
  "theorem outputConeNormalizer_checked {inputs outputs : Nat} (current : Implementation inputs outputs) : match outputConeNormalizer.normalize current with | .gain next _ => next = outputConeImplementation current ∧ 0 < outputConeDeletedGateCount current | .normal normalized => normalized.result = outputConeImplementation current ∧ outputConeDeletedGateCount current = 0 ∧ normalized.result.gateCount = current.gateCount"
];
const PUBLIC_HEADS = [
  "outputConeSystem",
  "outputConeSeed",
  "outputConeRecords",
  "outputConeRecords_output",
  "outputConeRecords_closed",
  "outputConeRecords_least",
  "outputConeRecords_noExternalGate",
  "outputConeFrontierCandidate",
  "outputConeFrontierCandidate_semantics",
  "outputConeImplementation",
  "outputConeImplementation_equivalent",
  "outputConeImplementation_gateCount_le",
  "outputConeDeletedGateCount",
  "outputConeImplementation_exact_accounting",
  "outputConeImplementation_referenceMinimum",
  "outputConeImplementation_residualSlack",
  "outputConeImplementation_strictGain_iff",
  "outputConeNormalizer",
  "outputConeNormalizer_checked"
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
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|callerCertificate|suppliedSupport)\b/u
    .test(clean), 'shortcut-or-certificate');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]))
    === JSON.stringify(['PNP.PCCMinNormalizeOracleComposition',
      'PNP.ResidualTerminalSupportExtraction']), 'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head => head.name)) ===
    JSON.stringify(PUBLIC_HEADS), 'public-interface');
  for (const [index,name] of NAMES.entries())
    require0(compact0(block0(source,name)).startsWith(SIGNATURES[index] + ' := '),
      'signature:' + name);
  const system = compact0(block0(source,'outputConeSystem'));
  for (const token of [
    'TerminalSaturationSystem inputs gates outputs 0',
    'role := Fin.elim0', 'observe := fun _ => Fin.elim0',
    '| .gateSource, .gate consumer, .gate producer => candidate.program.terminalGateUsesWire consumer (.gate producer)',
    '| _, _, _ => false',
  ]) require0(system.includes(token), 'computed-physical-edges');
  const seed = compact0(block0(source,'outputConeSeed'));
  for (const token of ['(allFin gates).filter',
    '(terminalGateIsGlobalOutput candidate.directWireWord)', 'TerminalPrimitiveRecord.gate'])
    require0(seed.includes(token), 'actual-output-seeds');
  const cone = compact0(block0(source,'outputConeRecords'));
  require0(cone.startsWith('def outputConeRecords {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs) : List (TerminalPrimitiveRecord inputs gates outputs 0) :='),
    'derived-cone-input');
  require0(cone.includes('terminalSaturateRecords (outputConeSystem candidate) (outputConeSeed candidate)'),
    'existing-executable-closure');
  const boundary = clean.slice(clean.indexOf('private def outputConeBoundaryInput '),
    clean.indexOf('private theorem outputConeBoundaryInput_value '));
  for (const token of ['| .input original => original', '| .gate producer => False.elim',
    'outputConeRecords_noExternalGate candidate producer'])
    require0(boundary.includes(token), 'only-original-boundary-inputs');
  const output = clean.slice(clean.indexOf('private def outputConeOutputSource '),
    clean.indexOf('private theorem outputConeOutputSource_eval '));
  for (const token of ['candidate.directWireWord.source output',
    '| .input original => .input original', '| .constant value => .constant value',
    '| .gate producer =>', 'outputConeOutput_interface candidate output producer wireEq',
    '(outputConeRenamedCandidate candidate).directWireWord.source located.1'])
    require0(output.includes(token), 'all-ordered-outputs');
  const implementation = compact0(block0(source,'outputConeImplementation'));
  for (const token of ['extractTerminalSupport current.candidate',
    '(outputConeRecords current.candidate)', 'Candidate.ofDirectWireWord',
    '(outputConeRenamedCandidate current.candidate).program', '⟨outputConeOutputSource current.candidate⟩'])
    require0(implementation.includes(token), 'reuse-checked-extraction');
  const computations = [system,seed,cone,boundary,output,implementation].join(' ');
  require0(!/\b(?:allCandidates|allValuations|allSubsets|equivalentBool|referenceMinimumWitness|scanEquivalentSizes|referenceMinimum)\b/u
    .test(computations), 'no-semantic-search');
  require0(compact0(block0(source,'outputConeDeletedGateCount')) ===
    'def outputConeDeletedGateCount {inputs outputs : Nat} (current : Implementation inputs outputs) : Nat := current.gateCount - (outputConeImplementation current).gateCount',
    'actual-deletion-count');
  const normalizer = compact0(block0(source,'outputConeNormalizer'));
  for (const token of ['if positive : 0 < outputConeDeletedGateCount current',
    '.gain (outputConeImplementation current)', '(outputConeImplementation_strictGain_iff current).mpr positive',
    'equivalent := outputConeImplementation_equivalent current',
    'gateCount_le := outputConeImplementation_gateCount_le current'])
    require0(normalizer.includes(token), 'computed-normalizer');
  return [...new Set(failures)];
}

test('M244 derives the complete physical output cone and eleven general pruning laws', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE)), []);
});

test('M244 explicit root, axiom audit and reviewed-name producers agree', async () => {
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
  assert.match(root,/^import PNP\.PCCMinOutputConePruning\s*$/mu);
});

test('M244 regressions cover the general boundary, dead chains, shared predecessors, output wiring and nonminimal complete cones', async () => {
  const raw=await text0(REGRESSION), regression=compact0(raw);
  for(const name of NAMES) assert.ok(regression.includes(name+' '),name);
  for(const token of [
    'mixedProgram : Program 2 5', 'mixedOutputs : Implementation 2 5',
    '[0, 2, 4]', 'noOutputs : Implementation 2 0', 'empty : Implementation 0 0',
    'primaryOutputs : Implementation 2 4', 'constantOutputs : Implementation 0 2',
    'StrictEquivalentGain liveButRedundant constantAlternative',
    '0 < residualSlack liveButRedundant', 'outputConeDeletedGateCount liveButRedundant != 0',
    'countObserver.observe mixedOutputs 0 == countObserver.observe pruned 0',
    'runPCCMinNormalizeOracleLoop outputConeNormalizer oracle current',
    'throw (IO.userError',
  ]) assert.ok(regression.includes(token),token);
  assert.equal([...raw.matchAll(/^#eval\b/gmu)].length,1);
  assert.doesNotMatch(regression,/\b(?:sorry|admit|native_decide|Classical)\b/u);
  assert.doesNotMatch(raw.split('#eval')[1],/\b(?:referenceMinimum|scanEquivalentSizes|allCandidates)\s/u);
});

test('M244 rejects finite-only, supplied-support and weakened semantic or slack boundaries', async () => {
  const source=await text0(SOURCE);
  const mutations=[
    ['(candidate : Candidate inputs gates outputs)', '(candidate : Candidate inputs 5 outputs)', 'signature:'+NAMES[0]],
    ['def outputConeRecords {inputs gates outputs : Nat}\n    (candidate : Candidate inputs gates outputs)',
      'def outputConeRecords {inputs gates outputs : Nat}\n    (candidate : Candidate inputs gates outputs) (suppliedSupport : True)',
      'derived-cone-input'],
    ['current.candidate.program current.candidate.directWireWord := by',
      'current.candidate.program current.candidate.directWireWord ∨ True := by', 'signature:'+NAMES[4]],
    ['residualSlack current = residualSlack (outputConeImplementation current) +',
      'residualSlack current ≤ residualSlack (outputConeImplementation current) +', 'signature:'+NAMES[8]],
    ['(current : Implementation inputs outputs) :\n    referenceMinimum',
      '(current : Implementation inputs outputs) (callerCertificate : True) :\n    referenceMinimum',
      'signature:'+NAMES[7]],
  ];
  for(const [before,after,category] of mutations){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
});

test('M244 rejects dropped dependencies, invented inputs, missing outputs, fake deletion accounting and gain suppression', async () => {
  const source=await text0(SOURCE);
  const mutations=[
    ['candidate.program.terminalGateUsesWire consumer (.gate producer)', 'false', 'computed-physical-edges'],
    ['(allFin gates).filter', '([ ] : List (Fin gates)).filter', 'actual-output-seeds'],
    ['terminalSaturateRecords (outputConeSystem candidate) (outputConeSeed candidate)', 'outputConeSeed candidate', 'existing-executable-closure'],
    ['| .gate producer => False.elim', '| .gate producer => arbitraryInput', 'only-original-boundary-inputs'],
    ['| .constant value => .constant value', '| .constant value => .constant false', 'all-ordered-outputs'],
    ['current.gateCount - (outputConeImplementation current).gateCount',
      'current.gateCount - (outputConeImplementation current).gateCount + 1', 'actual-deletion-count'],
    ['if positive : 0 < outputConeDeletedGateCount current', 'if positive : False', 'computed-normalizer'],
  ];
  for(const [before,after,category] of mutations){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    const mutated=source.replaceAll(before,after);
    assert.ok(validateSource0(mutated).includes(category),category);
  }
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n').includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n').includes('unaudited-form'));
});

test('M244 durable workflow includes source contracts, strict root audit and guarded regressions', async () => {
  const [packageText,surface,verifier,workflow]=await Promise.all([
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),text0('.github/workflows/lean-bridge.yml'),
  ]);
  const auditPath='audits/lean-pccmin-output-cone-pruning0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m244'],'node --test '+auditPath);
  assert.ok(surface.includes("'audit:m244': 'node --test "+auditPath+"'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test '+auditPath));
  for(const path of [auditPath,'docs/lean_pccmin_output_cone_pruning.md'])
    assert.equal(workflow.split("      - '"+path.replace(/^audits\/lean-[^/]+\.test\.mjs$/u,'audits/lean-*.test.mjs').replace(/^docs\/lean_[^/]+\.md$/u,'docs/lean_*.md').replace(/^lean\/.*$/u,'lean/**').replace(/^lean-audit\/.*$/u,'lean-audit/**').replace(/^lean-regression\/.*$/u,'lean-regression/**')+"'").length-1,2);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M244_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-12-244';
const M244_MILESTONE = 'pccmin-output-cone-pruning';
const M244_HASHES = Object.freeze({
  "PNP.DirectWire.outputConeRecords_output": "4a84fda6540cca8fb6973022a6b2fd87a24e4dcb3d9fb88fdfd7c8a220fb4cd3",
  "PNP.DirectWire.outputConeRecords_closed": "35b36dfb577ea36b54a521a9821c3e8d8fd9b561aa8621f87160088ad2607005",
  "PNP.DirectWire.outputConeRecords_least": "acbdad00014ed703ae3b6e5d8752f55e13d47c0238b477892758b9ca0fbb572d",
  "PNP.DirectWire.outputConeRecords_noExternalGate": "378d1260b7d2ee62fe165ac89564e432ba1747781f13686e17d9a83e75cf47be",
  "PNP.DirectWire.outputConeImplementation_equivalent": "064356bbc6da79448d31aa75eb34b149ee082822f42a2521b60da9930f85bcb6",
  "PNP.DirectWire.outputConeImplementation_gateCount_le": "8da639dbcc1460fb5ef3f78e62cc27e8379c52ce5a8181a0ef9fe54644fe95cc",
  "PNP.DirectWire.outputConeImplementation_exact_accounting": "c794c33214594e260a14552758c307ea23e1c3c945388c3a27a496263cb739a4",
  "PNP.DirectWire.outputConeImplementation_referenceMinimum": "a607337089e55510c9b9c32b166b739b728b3626fa58c63f043d35817b82308b",
  "PNP.DirectWire.outputConeImplementation_residualSlack": "8a9a1ad3414ffd5caf2ee0ee7a3bc9f1f7db7ac3654b34eff9d189fdeb5c327b",
  "PNP.DirectWire.outputConeImplementation_strictGain_iff": "74d077b8e8abb30b93dfefa3d0b836c39794144e2fa3b55883b6ea1040e5ef35",
  "PNP.DirectWire.outputConeNormalizer_checked": "943e610f7a7ff686071f1adda11a52a5659428fa1fa8649254444ca20e982fd6"
});
const M244_STATUS_FIELDS = Object.freeze({
  "leanPCCMinOutputConePruningFormalized": true,
  "leanPCCMinOutputConePruningAxiomAuditPassed": true,
  "leanPCCMinOutputConePruningAuditedDeclarationCount": 11,
  "leanPCCMinOutputConePruningOutputCoverageTheorem": "PNP.DirectWire.outputConeRecords_output",
  "leanPCCMinOutputConePruningPredecessorClosureTheorem": "PNP.DirectWire.outputConeRecords_closed",
  "leanPCCMinOutputConePruningLeastConeTheorem": "PNP.DirectWire.outputConeRecords_least",
  "leanPCCMinOutputConePruningNoExternalGateTheorem": "PNP.DirectWire.outputConeRecords_noExternalGate",
  "leanPCCMinOutputConePruningEquivalenceTheorem": "PNP.DirectWire.outputConeImplementation_equivalent",
  "leanPCCMinOutputConePruningGateCountTheorem": "PNP.DirectWire.outputConeImplementation_gateCount_le",
  "leanPCCMinOutputConePruningGateAccountingTheorem": "PNP.DirectWire.outputConeImplementation_exact_accounting",
  "leanPCCMinOutputConePruningReferenceMinimumTheorem": "PNP.DirectWire.outputConeImplementation_referenceMinimum",
  "leanPCCMinOutputConePruningResidualSlackTheorem": "PNP.DirectWire.outputConeImplementation_residualSlack",
  "leanPCCMinOutputConePruningStrictGainTheorem": "PNP.DirectWire.outputConeImplementation_strictGain_iff",
  "leanPCCMinOutputConePruningNormalizerTheorem": "PNP.DirectWire.outputConeNormalizer_checked",
  "leanPCCMinOutputConePruningFullProfilePreservationProved": false,
  "leanPCCMinOutputConePruningPolynomialRuntimeProved": false,
  "leanPCCMinOutputConePruningScope": "all-finite-nand-candidates-derived-least-physical-output-predecessor-cone-checked-support-extraction-original-io-semantics-exact-deletion-accounting-and-physical-normalizer-stage-only"
});
const M244_AXIOMS = Object.freeze({
  "PNP.DirectWire.outputConeRecords_output": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.outputConeRecords_closed": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.outputConeRecords_least": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.outputConeRecords_noExternalGate": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.outputConeImplementation_equivalent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.outputConeImplementation_gateCount_le": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.outputConeImplementation_exact_accounting": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.outputConeImplementation_referenceMinimum": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.outputConeImplementation_residualSlack": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.outputConeImplementation_strictGain_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.outputConeNormalizer_checked": [
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

test('M244 compiled physical output-cone pruning and normalizer interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M244_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M244_COORDINATE)
    assert.equal(map.coordinate, M244_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M244_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, 'PNP.PCCMinOutputConePruning', name);
      assert.deepEqual(declaration.axioms, M244_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M244_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M244_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M244_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "computed physical unused-gate pruning stage",
  "not complete manuscript N1-N10 normalization",
  "A no-deletion branch does not imply semantic minimality",
  "reference minimum occurs in specification theorems, not in execution",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M244 publication rejects weakened, supplied, assumption-backed and widened pruning/normalization substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M244_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M244_MILESTONE).earned, false, name);
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
  assert.equal(rejected.milestones.find(row => row.id === M244_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M244_MILESTONE
    ? {...row, nonClaim:'Physical pruning proves complete normalization, semantic minimality and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M244 adds physical output-cone pruning coverage without complete-normalization, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M244_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "general computed physical output-cone pruning stage",
  "actual output seeds and program predecessors determine the least closed gate support",
  "A no-deletion branch is not semantic minimality or ZeroSlack",
  "No fixed weighted checkpoint or global gate changes",
  "evidence row changes coverage only"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M244_COORDINATE) return;
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

test('M244 current summaries distinguish physical output-cone pruning from complete normalization and global route completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_pccmin_output_cone_pruning.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "No support or correctness certificate is supplied by the caller",
  "computed physical unused-gate pruning stage",
  "not complete manuscript N1-N10 normalization",
  "A no-deletion branch does not imply semantic minimality",
  "Runtime execution is test evidence, not theorem authority",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-12-derived-output-cone-pruning.md'));
  assert.ok(plan.includes('PNPLabs publication is deferred'));
  if (progress.asOfCoordinate !== M244_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_pccmin_output_cone_pruning.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
