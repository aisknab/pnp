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

const SOURCE = 'lean/PNP/PCCMinDeadSupportContext.lean';
const FRONTIER = 'lean/PNP/PCCMinOutputConePruning.lean';
const AUDIT = 'lean-audit/PNPDeadSupportContextAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPDeadSupportContext.lean';
const NAMES = [
  "outputConeFrontierCandidate_semantics",
  "deadSupport_interface_empty",
  "deadSupportGateCount_partition",
  "deadSupportGateCount_eq_deleted",
  "deadSupportEnvironment_boundary",
  "deadSupportEnvironment_bypass",
  "deadSupportCandidate_extracted",
  "deadSupportCandidate_program",
  "deadSupportEmptyReplacement_equivalent",
  "deadSupportContext_plug_equivalent",
  "deadSupportContext_original_size",
  "deadSupportReplacement_gateCount",
  "deadSupportReplacement_equivalent",
  "deadSupportReplacement_accounting",
  "deadSupportReplacement_residualSlack",
  "deadSupportReplacement_strictGain_iff",
  "deadSupportProperGain_isSome_iff",
  "deadSupportProperGain_sound",
  "deadSupportProperGain_none_of_all_dead",
  "deadSupportProperGain_none_of_no_dead"
];
const SIGNATURES = [
  "theorem outputConeFrontierCandidate_semantics {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs) (input : Valuation inputs) (output : Fin (terminalInterfacePorts candidate (outputConeRecords candidate)).length) : (outputConeFrontierCandidate candidate).semantics input output = candidate.program.eval input ((terminalInterfacePorts candidate (outputConeRecords candidate)).get output)",
  "theorem deadSupport_interface_empty {inputs outputs : Nat} (current : Implementation inputs outputs) : terminalInterfacePorts current.candidate (deadSupportRecords current) = []",
  "theorem deadSupportGateCount_partition {inputs outputs : Nat} (current : Implementation inputs outputs) : (outputConeImplementation current).gateCount + deadSupportGateCount current = current.gateCount",
  "theorem deadSupportGateCount_eq_deleted {inputs outputs : Nat} (current : Implementation inputs outputs) : deadSupportGateCount current = outputConeDeletedGateCount current",
  "theorem deadSupportEnvironment_boundary {inputs outputs : Nat} (current : Implementation inputs outputs) (input : Valuation inputs) (index : Fin (deadSupportBoundary current).length) : (deadSupportEnvironment current).semantics input (Fin.castAdd outputs index) = terminalInducedBoundaryValuation current.candidate (deadSupportRecords current) input index",
  "theorem deadSupportEnvironment_bypass {inputs outputs : Nat} (current : Implementation inputs outputs) (input : Valuation inputs) (output : Fin outputs) : (deadSupportEnvironment current).semantics input (Fin.natAdd (deadSupportBoundary current).length output) = current.candidate.semantics input output",
  "theorem deadSupportCandidate_extracted {inputs outputs : Nat} (current : Implementation inputs outputs) : HEq (deadSupportCandidate current) (extractTerminalSupport current.candidate (deadSupportRecords current)).extractedCandidate",
  "theorem deadSupportCandidate_program {inputs outputs : Nat} (current : Implementation inputs outputs) : (deadSupportCandidate current).program = (extractTerminalSupport current.candidate (deadSupportRecords current)).extractedCandidate.program",
  "theorem deadSupportEmptyReplacement_equivalent {inputs outputs : Nat} (current : Implementation inputs outputs) : Equivalent (deadSupportEmptyReplacement current).program (deadSupportEmptyReplacement current).directWireWord (deadSupportCandidate current).program (deadSupportCandidate current).directWireWord",
  "theorem deadSupportContext_plug_equivalent {inputs outputs replacementGates : Nat} (current : Implementation inputs outputs) (replacement : Candidate (deadSupportBoundary current).length replacementGates 0) : Equivalent ((deadSupportContext current).plug replacement).program ((deadSupportContext current).plug replacement).directWireWord current.candidate.program current.candidate.directWireWord",
  "theorem deadSupportContext_original_size {inputs outputs : Nat} (current : Implementation inputs outputs) : ((deadSupportContext current).plug (deadSupportCandidate current)).program.size = current.gateCount",
  "theorem deadSupportReplacement_gateCount {inputs outputs : Nat} (current : Implementation inputs outputs) : (deadSupportReplacementImplementation current).gateCount = (outputConeImplementation current).gateCount",
  "theorem deadSupportReplacement_equivalent {inputs outputs : Nat} (current : Implementation inputs outputs) : Equivalent (deadSupportReplacementImplementation current).candidate.program (deadSupportReplacementImplementation current).candidate.directWireWord current.candidate.program current.candidate.directWireWord",
  "theorem deadSupportReplacement_accounting {inputs outputs : Nat} (current : Implementation inputs outputs) : (deadSupportReplacementImplementation current).gateCount + deadSupportGateCount current = current.gateCount",
  "theorem deadSupportReplacement_residualSlack {inputs outputs : Nat} (current : Implementation inputs outputs) : residualSlack current = residualSlack (deadSupportReplacementImplementation current) + deadSupportGateCount current",
  "theorem deadSupportReplacement_strictGain_iff {inputs outputs : Nat} (current : Implementation inputs outputs) : StrictEquivalentGain current (deadSupportReplacementImplementation current) ↔ 0 < deadSupportGateCount current",
  "theorem deadSupportProperGain_isSome_iff {inputs outputs : Nat} (current : Implementation inputs outputs) : (deadSupportProperGain current).isSome = true ↔ 0 < deadSupportGateCount current ∧ 0 < (outputConeImplementation current).gateCount",
  "theorem deadSupportProperGain_sound {inputs outputs : Nat} (current : Implementation inputs outputs) (witness : DeadSupportPhysicalGain current) (_found : deadSupportProperGain current = some witness) : 0 < deadSupportGateCount current ∧ deadSupportGateCount current < current.gateCount ∧ StrictEquivalentGain current (deadSupportReplacementImplementation current) ∧ residualSlack (deadSupportReplacementImplementation current) < residualSlack current",
  "theorem deadSupportProperGain_none_of_all_dead {inputs outputs : Nat} (current : Implementation inputs outputs) (allDead : (outputConeImplementation current).gateCount = 0) : deadSupportProperGain current = none",
  "theorem deadSupportProperGain_none_of_no_dead {inputs outputs : Nat} (current : Implementation inputs outputs) (noDead : deadSupportGateCount current = 0) : deadSupportProperGain current = none"
];
const PUBLIC_HEADS = [
  "deadSupportRecords",
  "deadSupportBoundary",
  "deadSupportGateCount",
  "deadSupport_interface_empty",
  "deadSupportGateCount_partition",
  "deadSupportGateCount_eq_deleted",
  "deadSupportInputSource",
  "deadSupportEnvironment",
  "deadSupportEnvironment_boundary",
  "deadSupportEnvironment_bypass",
  "deadSupportCandidate",
  "deadSupportCandidate_extracted",
  "deadSupportCandidate_program",
  "deadSupportEmptyReplacement",
  "deadSupportEmptyReplacement_equivalent",
  "deadSupportContext",
  "deadSupportContext_plug_equivalent",
  "deadSupportContext_original_size",
  "deadSupportReplacementImplementation",
  "deadSupportReplacement_gateCount",
  "deadSupportReplacement_equivalent",
  "deadSupportReplacement_accounting",
  "deadSupportReplacement_residualSlack",
  "deadSupportReplacement_strictGain_iff",
  "DeadSupportPhysicalGain",
  "deadSupportProperGain",
  "deadSupportProperGain_isSome_iff",
  "deadSupportProperGain_sound",
  "deadSupportProperGain_none_of_all_dead",
  "deadSupportProperGain_none_of_no_dead"
];
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = value => stripLeanCommentsAndStrings0(value).replace(/\s+/gu, ' ').trim();
function block0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex(head => head.name === name);
  return index < 0 ? '' : source.slice(heads[index].index, heads[index + 1]?.index ?? source.length);
}
function validateSource0(source, frontier) {
  const failures = [];
  const require0 = (condition, category) => { if (!condition) failures.push(category); };
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|callerCertificate|suppliedSupport)\b/u
    .test(compact0(source)), 'shortcut-or-certificate');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1])) ===
    JSON.stringify(['PNP.PCCMinOutputConePruning', 'PNP.ResidualTerminalSaturatedSupportContext']),
    'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head => head.name)) ===
    JSON.stringify(PUBLIC_HEADS), 'public-interface');
  for (const [index,name] of NAMES.entries())
    require0(compact0(block0(index === 0 ? frontier : source,name)).startsWith(
      SIGNATURES[index] + ' := '), 'signature:' + name);
  const definitions = Object.fromEntries([
    'deadSupportRecords', 'deadSupportBoundary', 'deadSupportGateCount',
    'deadSupportInputSource', 'deadSupportEnvironment', 'deadSupportCandidate',
    'deadSupportEmptyReplacement', 'deadSupportContext', 'deadSupportReplacementImplementation',
    'deadSupportProperGain',
  ].map(name => [name, compact0(block0(source,name))]));
  for (const [name,category,tokens] of [
    ['deadSupportRecords', 'actual-complement', [
      'terminalPhysicalComplementRecords (outputConeRecords current.candidate)']],
    ['deadSupportBoundary', 'actual-boundary', [
      'terminalBoundaryPorts current.candidate.program (deadSupportRecords current)']],
    ['deadSupportGateCount', 'actual-extracted-count', [
      '(extractTerminalSupport current.candidate (deadSupportRecords current)).gateCount']],
    ['deadSupportInputSource', 'computed-boundary-wiring', [
      '(deadSupportBoundary current).get index', '| .input original => .input original',
      'deadBoundaryGate_liveInterface current producer',
      '(outputConeFrontierCandidate current.candidate).directWireWord.source located.1']],
    ['deadSupportEnvironment', 'single-live-environment-and-bypass', [
      '(outputConeFrontierCandidate current.candidate).program',
      '⟨splitFin (deadSupportInputSource current)',
      '(outputConeImplementation current).candidate.directWireWord.source⟩']],
    ['deadSupportCandidate', 'actual-extraction-reindexed', [
      'deadSupport_outputWidth_zero current ▸',
      '(extractTerminalSupport current.candidate (deadSupportRecords current)).extractedCandidate']],
    ['deadSupportEmptyReplacement', 'zero-output-empty-replacement', [
      'Candidate (deadSupportBoundary current).length 0 0',
      'Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩']],
    ['deadSupportContext', 'computed-frame', [
      'FramedContext inputs (deadSupportBoundary current).length 0 outputs outputs',
      'environment := deadSupportEnvironment current',
      'continuation := deadBypassContinuation outputs']],
    ['deadSupportReplacementImplementation', 'actual-frame-execution', [
      '((deadSupportContext current).plug (deadSupportEmptyReplacement current)).toImplementation']],
    ['deadSupportProperGain', 'nonempty-proper-acceptance', [
      'if positive : 0 < deadSupportGateCount current ∧ 0 < (outputConeImplementation current).gateCount then',
      'supportNonempty := positive.1', 'deadSupportGateCount_partition current',
      'gain := (deadSupportReplacement_strictGain_iff current).mpr positive.1', 'else none']],
  ]) for (const token of tokens) require0(definitions[name].includes(token), category);
  require0(!/\b(?:allCandidates|allValuations|allSubsets|equivalentBool|referenceMinimumWitness|scanEquivalentSizes|referenceMinimum)\b/u
    .test(Object.values(definitions).join(' ')), 'no-semantic-search');
  require0(compact0(block0(frontier,'outputConeFrontierCandidate')).endsWith(
    ':= outputConeRenamedCandidate candidate'), 'reuse-computed-frontier');
  return [...new Set(failures)];
}

test('M245 derives the actual dead-support frame and twenty general physical replacement laws', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE), await text0(FRONTIER)), []);
});

test('M245 explicit root, axiom audit and both reviewed-module producers agree', async () => {
  const [source,frontier,audit,inventorySource,root] = await Promise.all([
    text0(SOURCE),text0(FRONTIER),text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),
    text0('lean/PNP.lean'),
  ]);
  for (const [index,name] of NAMES.entries()) {
    assert.equal(explicitLeanDeclarationHeads0(index === 0 ? frontier : source)
      .filter(head => head.name === name).length,1);
    const fullName = 'PNP.DirectWire.' + name;
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item => item === fullName).length,1);
    assert.equal(inventorySource.split(String.fromCharCode(96) + fullName + ',').length - 1,1);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),
    NAMES.map(name=>'PNP.DirectWire.'+name));
  assert.match(root,/^import PNP\.PCCMinDeadSupportContext\s*$/mu);
});

test('M245 regressions cover noncontiguous dead gates, computed live inputs, zero dimensions and the properness firewall', async () => {
  const raw = await text0(REGRESSION), regression = compact0(raw);
  for (const name of NAMES) assert.ok(regression.includes(name + ' '),name);
  for (const token of [
    'interleavedProgram : Program 2 5', '[1, 3]', '[0, 2, 4]',
    'allUnused : Implementation 2 0', 'empty : Implementation 0 0',
    'primaryOutputs : Implementation 2 3', 'constantCircuit : Implementation 0 1',
    'StrictEquivalentGain allLive constantAlternative',
    'countObserver.observe mixed 0 == countObserver.observe replaced 0',
    '(deadSupportEnvironment mixed).semantics input (Fin.castAdd 5 index)',
    'terminalInducedBoundaryValuation mixed.candidate (deadSupportRecords mixed)',
    '(deadSupportProperGain allUnused).isSome',
    '(deadSupportProperGain allLive).isSome', 'throw (IO.userError',
  ]) assert.ok(regression.includes(token),token);
  assert.equal([...raw.matchAll(/^#eval\b/gmu)].length,1);
  assert.doesNotMatch(regression,/\b(?:sorry|admit|native_decide|Classical)\b/u);
  assert.doesNotMatch(raw.split('#eval')[1],/\b(?:referenceMinimum|scanEquivalentSizes|allCandidates)\s/u);
});

test('M245 rejects weakened, supplied and finite-only theorem boundaries', async () => {
  const source=await text0(SOURCE), frontier=await text0(FRONTIER);
  for (const [before,after,category] of [
    ['(current : Implementation inputs outputs)', '(current : Implementation 2 outputs)', 'signature:deadSupport_interface_empty'],
    ['current.candidate.program current.candidate.directWireWord := by',
      'current.candidate.program current.candidate.directWireWord ∨ True := by',
      'signature:deadSupportContext_plug_equivalent'],
    ['residualSlack current = residualSlack (deadSupportReplacementImplementation current) +',
      'residualSlack current ≤ residualSlack (deadSupportReplacementImplementation current) +',
      'signature:deadSupportReplacement_residualSlack'],
    ['(current : Implementation inputs outputs) :\n    HEq',
      '(current : Implementation inputs outputs) (callerCertificate : True) :\n    HEq',
      'signature:deadSupportCandidate_extracted'],
  ]) {
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after),frontier).includes(category),category);
  }
});

test('M245 rejects fabricated supports, discarded interfaces, supplied frames and whole-circuit properness', async () => {
  const source=await text0(SOURCE), frontier=await text0(FRONTIER);
  for (const [before,after,category] of [
    ['terminalPhysicalComplementRecords (outputConeRecords current.candidate)', '[]', 'actual-complement'],
    ['terminalBoundaryPorts current.candidate.program (deadSupportRecords current)', '[]', 'actual-boundary'],
    ['(deadSupportBoundary current).get index', 'TerminalSupportWire.input 0', 'computed-boundary-wiring'],
    ['deadSupport_outputWidth_zero current ▸', 'discardOutputs', 'actual-extraction-reindexed'],
    ['environment := deadSupportEnvironment current', 'environment := suppliedEnvironment', 'computed-frame'],
    ['((deadSupportContext current).plug (deadSupportEmptyReplacement current)).toImplementation',
      'outputConeImplementation current', 'actual-frame-execution'],
    ['0 < (outputConeImplementation current).gateCount then',
      '0 ≤ (outputConeImplementation current).gateCount then', 'nonempty-proper-acceptance'],
  ]) {
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after),frontier).includes(category),category);
  }
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n',frontier).includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n',frontier).includes('unaudited-form'));
});

test('M245 durable workflow retains exact audit and bounded guarded regressions', async () => {
  const [packageText,surface,verifier,workflow]=await Promise.all([
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),text0('.github/workflows/lean-bridge.yml'),
  ]);
  const auditPath='audits/lean-pccmin-dead-support-context0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m245'],'node --test '+auditPath);
  assert.ok(surface.includes("'audit:m245': 'node --test "+auditPath+"'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test '+auditPath));
  for (const path of [auditPath,'docs/lean_pccmin_dead_support_context.md'])
    assertLeanWorkflowPathCoverage0(workflow, path);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M245_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-12-245';
const M245_MILESTONE = 'pccmin-dead-support-context';
const M245_HASHES = Object.freeze({
  "PNP.DirectWire.outputConeFrontierCandidate_semantics": "3dc1bb632f4ffbc3f0f1c8b32c170e70b6ba9812eb06eb4066c75d9a6f3f0055",
  "PNP.DirectWire.deadSupport_interface_empty": "906b882fffcfde65b4de880537a04e1ec9dacb5647cbcb9bc8ec4d80abbf83f8",
  "PNP.DirectWire.deadSupportGateCount_partition": "6edafb52a2e5ff5d1866967dd0a8b4a94b759429dc0d71486ccd5b6d76ad563a",
  "PNP.DirectWire.deadSupportGateCount_eq_deleted": "82d59d27ed1c3cd19002619b0d1cfbb0606623acafcaf1c6fa659905da8a368b",
  "PNP.DirectWire.deadSupportEnvironment_boundary": "162da320d61d2549c4fdbf27b8c6d91d1462fa130d351b14d87af2e39fcca254",
  "PNP.DirectWire.deadSupportEnvironment_bypass": "7a706583784a3a8000d311fc7d744eee0afcda9bbeb244cb59df9ad5aa3f5c68",
  "PNP.DirectWire.deadSupportCandidate_extracted": "eda366bcc7644aad67a9a8ff4a47b8911fe7d9defe1cfb08e707913c29605cf1",
  "PNP.DirectWire.deadSupportCandidate_program": "e3b9e0c33c87b292695750a5e2b3b17ff3c190ccbe5b314647ca6367496c7fb2",
  "PNP.DirectWire.deadSupportEmptyReplacement_equivalent": "a491c8f37fa95a7803005f043458bf5e0d62066c51082781b9d3764acede3e9f",
  "PNP.DirectWire.deadSupportContext_plug_equivalent": "5de578a40f9d237158105924b2591a08cf0576898fed1eaab43799879c6343ec",
  "PNP.DirectWire.deadSupportContext_original_size": "4c0b8ad72564b492a3e161db0f6c3d4f5731da4959b699585c8d8dbe5da54d71",
  "PNP.DirectWire.deadSupportReplacement_gateCount": "e3049d0cee3f4870ea9d8f60100ff98dcd8105310e20579ba4f80b0f53d4870c",
  "PNP.DirectWire.deadSupportReplacement_equivalent": "d5c1b86dfb34461c8b300d3647fcf54e8cf46b3104122595beb6368b2660bc2a",
  "PNP.DirectWire.deadSupportReplacement_accounting": "61abe459f6ba20d1aea0ec9b3c26821fbf405e12aea50fdaa986a89c90fb186c",
  "PNP.DirectWire.deadSupportReplacement_residualSlack": "5adb0248d3e63508b978489c8710df0d8ee4835cd2e8e33ea6d8fd7f4971225c",
  "PNP.DirectWire.deadSupportReplacement_strictGain_iff": "9620a0e22c4e3cafafdf4ee248b08b0d5205b3e378e4bed1aa743be59a8f7b26",
  "PNP.DirectWire.deadSupportProperGain_isSome_iff": "c031fe639898d6671d76e28409b5204852aa290dd37c6e294b6a641fd1cc55b2",
  "PNP.DirectWire.deadSupportProperGain_sound": "51cc13a8b4d0c917107a5199e03f5a5a862e30b01ad4c3d6265c2065daf755a2",
  "PNP.DirectWire.deadSupportProperGain_none_of_all_dead": "c7b2036d09f1e80c0f2367ed5046c49fc5aea9412e2b59b7404ddc4bad68dc11",
  "PNP.DirectWire.deadSupportProperGain_none_of_no_dead": "36242686b99f11d533a8fd54ab724dd586c89e621d25d9bea4b0ab3e57d0c40a"
});
const M245_STATUS_FIELDS = Object.freeze({
  "leanPCCMinDeadSupportContextFormalized": true,
  "leanPCCMinDeadSupportContextAxiomAuditPassed": true,
  "leanPCCMinDeadSupportContextAuditedDeclarationCount": 20,
  "leanPCCMinDeadSupportContextFrontierSemanticsTheorem": "PNP.DirectWire.outputConeFrontierCandidate_semantics",
  "leanPCCMinDeadSupportContextEmptyInterfaceTheorem": "PNP.DirectWire.deadSupport_interface_empty",
  "leanPCCMinDeadSupportContextGatePartitionTheorem": "PNP.DirectWire.deadSupportGateCount_partition",
  "leanPCCMinDeadSupportContextDeletedCountTheorem": "PNP.DirectWire.deadSupportGateCount_eq_deleted",
  "leanPCCMinDeadSupportContextBoundaryValuesTheorem": "PNP.DirectWire.deadSupportEnvironment_boundary",
  "leanPCCMinDeadSupportContextBypassOutputsTheorem": "PNP.DirectWire.deadSupportEnvironment_bypass",
  "leanPCCMinDeadSupportContextActualExtractionTheorem": "PNP.DirectWire.deadSupportCandidate_extracted",
  "leanPCCMinDeadSupportContextExtractedProgramTheorem": "PNP.DirectWire.deadSupportCandidate_program",
  "leanPCCMinDeadSupportContextLocalEquivalenceTheorem": "PNP.DirectWire.deadSupportEmptyReplacement_equivalent",
  "leanPCCMinDeadSupportContextFramedEquivalenceTheorem": "PNP.DirectWire.deadSupportContext_plug_equivalent",
  "leanPCCMinDeadSupportContextOriginalFrameSizeTheorem": "PNP.DirectWire.deadSupportContext_original_size",
  "leanPCCMinDeadSupportContextReplacementGateCountTheorem": "PNP.DirectWire.deadSupportReplacement_gateCount",
  "leanPCCMinDeadSupportContextReplacementEquivalenceTheorem": "PNP.DirectWire.deadSupportReplacement_equivalent",
  "leanPCCMinDeadSupportContextReplacementAccountingTheorem": "PNP.DirectWire.deadSupportReplacement_accounting",
  "leanPCCMinDeadSupportContextResidualSlackTheorem": "PNP.DirectWire.deadSupportReplacement_residualSlack",
  "leanPCCMinDeadSupportContextStrictGainTheorem": "PNP.DirectWire.deadSupportReplacement_strictGain_iff",
  "leanPCCMinDeadSupportContextProperAcceptanceTheorem": "PNP.DirectWire.deadSupportProperGain_isSome_iff",
  "leanPCCMinDeadSupportContextProperGainSoundnessTheorem": "PNP.DirectWire.deadSupportProperGain_sound",
  "leanPCCMinDeadSupportContextAllDeadRejectionTheorem": "PNP.DirectWire.deadSupportProperGain_none_of_all_dead",
  "leanPCCMinDeadSupportContextNoDeadRejectionTheorem": "PNP.DirectWire.deadSupportProperGain_none_of_no_dead",
  "leanPCCMinDeadSupportContextFullProfileAdmissibilityProved": false,
  "leanPCCMinDeadSupportContextCompletePackageEVerifierProved": false,
  "leanPCCMinDeadSupportContextPolynomialRuntimeProved": false,
  "leanPCCMinDeadSupportContextScope": "all-finite-nand-implementations-computed-dead-gate-complement-empty-interface-exact-extracted-support-live-frontier-environment-framed-replacement-and-nonempty-proper-physical-gain-only"
});
const M245_AXIOMS = Object.freeze({
  "PNP.DirectWire.outputConeFrontierCandidate_semantics": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupport_interface_empty": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportGateCount_partition": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportGateCount_eq_deleted": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportEnvironment_boundary": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportEnvironment_bypass": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportCandidate_extracted": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportCandidate_program": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportEmptyReplacement_equivalent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportContext_plug_equivalent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportContext_original_size": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportReplacement_gateCount": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportReplacement_equivalent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportReplacement_accounting": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportReplacement_residualSlack": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportReplacement_strictGain_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportProperGain_isSome_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportProperGain_sound": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportProperGain_none_of_all_dead": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.deadSupportProperGain_none_of_no_dead": [
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

test('M245 compiled dead-support context and proper physical replacement interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M245_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M245_COORDINATE)
    assert.equal(map.coordinate, M245_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M245_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, name === 'PNP.DirectWire.outputConeFrontierCandidate_semantics'
        ? 'PNP.PCCMinOutputConePruning' : 'PNP.PCCMinDeadSupportContext', name);
      assert.deepEqual(declaration.axioms, M245_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M245_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M245_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M245_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "computed proper physical deletion component",
  "not complete manuscript Package E admissibility",
  "An all-unused circuit is not accepted as a proper-subset witness",
  "Rejecting this route does not imply semantic minimality or ZeroSlack",
  "reference minimum occurs only in specification theorems",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M245 publication rejects weakened, supplied, assumption-backed and widened physical replacement substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M245_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M245_MILESTONE).earned, false, name);
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
  assert.equal(rejected.milestones.find(row => row.id === M245_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M245_MILESTONE
    ? {...row, nonClaim:'Physical replacement proves full-profile Package E admissibility and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M245 adds proper physical replacement coverage without full-profile, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M245_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "general computed dead-support replacement context",
  "actual unused-gate complement has no outgoing ports",
  "Only a nonempty proper physical support is accepted",
  "No fixed weighted checkpoint or global gate changes",
  "evidence row changes coverage only"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M245_COORDINATE) return;
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

test('M245 current summaries distinguish computed physical replacement from full-profile and global route completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_pccmin_dead_support_context.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "No support, frame or correctness certificate is supplied by the caller",
  "computed proper physical deletion component",
  "not complete manuscript Package E admissibility",
  "An all-unused circuit is not accepted as a proper-subset witness",
  "Runtime execution is test evidence, not theorem authority",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-12-computed-dead-support-context.md'));
  assert.ok(plan.includes('Publication decision: defer PNPLabs'));
  if (progress.asOfCoordinate !== M245_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_pccmin_dead_support_context.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
