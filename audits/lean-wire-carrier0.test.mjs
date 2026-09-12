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

const SOURCE = 'lean/PNP/NANDWireCarrier.lean';
const AUDIT = 'lean-audit/PNPWireCarrierAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPWireCarrier.lean';
const NAMES = [
  "PNP.DirectWire.WireCarrier.exposed_unpack",
  "PNP.DirectWire.WireCarrier.unpack_exposed",
  "PNP.DirectWire.WireCarrier.normalize_output",
  "PNP.DirectWire.WireCarrier.normalize_field",
  "PNP.DirectWire.WireCarrier.normalize_exact_accounting",
  "PNP.DirectWire.WireCarrier.normalize_quiescent",
  "PNP.DirectWire.WireCarrier.normalize_idempotent",
  "PNP.DirectWire.WireCarrier.field_producer_visible",
  "PNP.DirectWire.WireCarrier.splice_output",
  "PNP.DirectWire.WireCarrier.splice_field",
  "PNP.DirectWire.WireCarrier.splice_exact_accounting",
  "PNP.DirectWire.WireCarrier.splice_strict_gain",
  "PNP.DirectWire.WireCarrier.splice_checked",
  "PNP.DirectWire.WireCarrier.splice_failure_iff",
  "PNP.DirectWire.WireCarrier.production_boundary_isInput",
  "PNP.DirectWire.WireCarrier.production_compiles"
];
const SIGNATURES = {
  "exposed_unpack": "theorem exposed_unpack (combined : Implementation inputs (outputs + fields)) : (unpack (outputs := outputs) (fields := fields) combined).exposed = combined",
  "unpack_exposed": "theorem unpack_exposed (carrier : WireCarrier inputs outputs fields) : unpack carrier.exposed = carrier",
  "normalize_output": "theorem normalize_output (carrier : WireCarrier inputs outputs fields) (valuation : Valuation inputs) (output : Fin outputs) : carrier.normalize.implementation.candidate.semantics valuation output = carrier.implementation.candidate.semantics valuation output",
  "normalize_field": "theorem normalize_field (carrier : WireCarrier inputs outputs fields) (valuation : Valuation inputs) (field : Fin fields) : carrier.normalize.fieldValue valuation field = carrier.fieldValue valuation field",
  "normalize_exact_accounting": "theorem normalize_exact_accounting (carrier : WireCarrier inputs outputs fields) : carrier.normalize.implementation.gateCount + (runPhysicalNormalization carrier.exposed).trace.savedGates = carrier.implementation.gateCount",
  "normalize_quiescent": "theorem normalize_quiescent (carrier : WireCarrier inputs outputs fields) : PhysicalNormalizationQuiescent carrier.normalize.exposed",
  "normalize_idempotent": "theorem normalize_idempotent (carrier : WireCarrier inputs outputs fields) : carrier.normalize.normalize = carrier.normalize",
  "field_producer_visible": "theorem field_producer_visible (carrier : WireCarrier inputs outputs fields) (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0)) (field : Fin fields) (producer : Fin carrier.implementation.gateCount) (sourceAt : carrier.source field = .gate producer) (selected : terminalGateSelected records producer = true) : producer ∈ (extractTerminalSupport carrier.exposed.candidate records).interface",
  "splice_output": "theorem splice_output (sameOpen : replacement.semantics = (extractTerminalSupport carrier.exposed.candidate records).extractedCandidate.semantics) (compiled : CompiledRawNandGraph (ArbitrarySupportSplice.graph carrier.exposed.candidate records replacement)) (valuation : Valuation inputs) (output : Fin outputs) : (carrier.spliceResult records replacement compiled).implementation.candidate.semantics valuation output = carrier.implementation.candidate.semantics valuation output",
  "splice_field": "theorem splice_field (sameOpen : replacement.semantics = (extractTerminalSupport carrier.exposed.candidate records).extractedCandidate.semantics) (compiled : CompiledRawNandGraph (ArbitrarySupportSplice.graph carrier.exposed.candidate records replacement)) (valuation : Valuation inputs) (field : Fin fields) : (carrier.spliceResult records replacement compiled).fieldValue valuation field = carrier.fieldValue valuation field",
  "splice_exact_accounting": "theorem splice_exact_accounting (compiled : CompiledRawNandGraph (ArbitrarySupportSplice.graph carrier.exposed.candidate records replacement)) : (carrier.spliceResult records replacement compiled).implementation.gateCount + (extractTerminalSupport carrier.exposed.candidate records).gateCount = carrier.implementation.gateCount + replacementGates",
  "splice_strict_gain": "theorem splice_strict_gain (smaller : replacementGates < (extractTerminalSupport carrier.exposed.candidate records).gateCount) (compiled : CompiledRawNandGraph (ArbitrarySupportSplice.graph carrier.exposed.candidate records replacement)) : (carrier.spliceResult records replacement compiled).implementation.gateCount < carrier.implementation.gateCount",
  "splice_checked": "theorem splice_checked (sameOpen : replacement.semantics = (extractTerminalSupport carrier.exposed.candidate records).extractedCandidate.semantics) (result : WireCarrier inputs outputs fields) (accepted : carrier.splice records replacement = some result) : (∀ valuation output, result.implementation.candidate.semantics valuation output = carrier.implementation.candidate.semantics valuation output) ∧ (∀ valuation field, result.fieldValue valuation field = carrier.fieldValue valuation field) ∧ result.implementation.gateCount + (extractTerminalSupport carrier.exposed.candidate records).gateCount = carrier.implementation.gateCount + replacementGates",
  "splice_failure_iff": "theorem splice_failure_iff : carrier.splice records replacement = none ↔ ¬WellFounded (ArbitrarySupportSplice.graph carrier.exposed.candidate records replacement).Depends",
  "production_boundary_isInput": "theorem production_boundary_isInput (seed : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0)) (wire : TerminalSupportWire inputs carrier.implementation.gateCount) (member : wire ∈ (extractTerminalSupport carrier.exposed.candidate (carrier.productionRecords seed)).boundary) : ∃ index : Fin inputs, wire = TerminalSupportWire.input index",
  "production_compiles": "theorem production_compiles (seed : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0)) (replacement : Candidate (extractTerminalSupport carrier.exposed.candidate (carrier.productionRecords seed)).boundary.length replacementGates (extractTerminalSupport carrier.exposed.candidate (carrier.productionRecords seed)).interface.length) : ∃ result, carrier.splice (carrier.productionRecords seed) replacement = some result"
};
const HEADS = [
  'WireCarrier','fieldValue','exposed','unpack','exposed_gateCount','unpack_gateCount',
  'exposed_output_source','exposed_field_source','exposed_output','exposed_field',
  'unpack_output','unpack_field','exposed_unpack','unpack_exposed','normalize',
  'normalize_output','normalize_field','normalize_exact_accounting','normalize_quiescent',
  'normalize_idempotent','field_producer_visible','spliceResult','splice','splice_output',
  'splice_field','splice_exact_accounting','splice_strict_gain','splice_checked',
  'splice_failure_iff','productionModel','productionRecords','production_boundary_isInput',
  'production_compiles',
];
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = value => stripLeanCommentsAndStrings0(value).replace(/\s+/gu,' ').trim();
function block0(source,name) {
  const stripped=stripLeanCommentsAndStrings0(source);
  const boundaries=[...stripped.matchAll(/^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*(?:(?:def|theorem|inductive|structure|abbrev)[ \t]+([^\s({:]+)|variable\b|namespace\b|end\b)/gmu)];
  const index=boundaries.findIndex(item=>item[1]===name);
  return index<0?'':compact0(source.slice(boundaries[index].index,boundaries[index+1]?.index??source.length));
}
// Named arguments inside binders are not a theorem's top-level proof body.
function signature0(block) {
  let depth=0;
  for(let index=0;index<block.length-1;index++){
    if('({['.includes(block[index]))depth++;
    else if(')}]'.includes(block[index]))depth--;
    if(depth===0 && block.slice(index,index+2)===':=')return block.slice(0,index).trim();
  }
  return '';
}
function validateSource0(source) {
  const failures=[], require0=(condition,category)=>{if(!condition)failures.push(category);};
  const clean=compact0(source), block=name=>block0(source,name);
  require0(!hasLeanAssumptionDeclaration0(source),'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source),'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|callerCertificate|suppliedObserver|suppliedOrder|suppliedMap|suppliedResult)\b/u.test(clean),'shortcut-or-certificate');
  require0(!/\b(?:allCandidates|allBoolTuples|allSubsets|equivalentBool|referenceMinimumWitness|scanEquivalentSizes|referenceMinimum|terminalFullProfileMinimum)\b/u.test(clean),'no-semantic-enumeration');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]))===
    JSON.stringify(['PNP.PCCMinPhysicalNormalizationClosure','PNP.NANDArbitrarySupportSplice']),'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name))===
    JSON.stringify(HEADS),'public-interface');
  for(const [name,signature] of Object.entries(SIGNATURES))
    require0(signature0(block(name))===signature,'signature:'+name);
  require0(clean.includes('variable {inputs outputs fields : Nat}') &&
    clean.includes('variable (carrier : WireCarrier inputs outputs fields) (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0)) {replacementGates : Nat} (replacement : Candidate (extractTerminalSupport carrier.exposed.candidate records).boundary.length replacementGates (extractTerminalSupport carrier.exposed.candidate records).interface.length)'),
    'general-complete-interface-parameters');
  require0(block('WireCarrier')===
    'structure WireCarrier (inputs outputs fields : Nat) where implementation : Implementation inputs outputs source : Fin fields → Source inputs implementation.gateCount',
    'literal-wire-fields-only');
  const includes=(name,tokens,category)=>
    require0(tokens.every(token=>block(name).includes(token)),category);
  require0(block('fieldValue').endsWith(
    '(carrier.source field).eval valuation (carrier.implementation.candidate.program.eval valuation)'),
    'actual-wire-evaluation');
  includes('exposed',[
    'Implementation inputs (outputs + fields)',
    'Candidate.ofDirectWireWord carrier.implementation.candidate.program',
    'splitFin carrier.implementation.candidate.directWireWord.source carrier.source',
  ],'complete-zero-gate-exposure');
  includes('unpack',[
    'Candidate.ofDirectWireWord combined.candidate.program',
    '(Fin.castAdd fields output)',
    'source := fun field => combined.candidate.directWireWord.source (Fin.natAdd outputs field)',
  ],'ordered-exact-unpacking');
  require0(block('normalize').endsWith(
    'unpack (runPhysicalNormalization carrier.exposed).result'),'actual-complete-normalization');
  includes('field_producer_visible',[
    'mem_terminalInterfacePorts_iff','terminalGateIsGlobalOutput_eq_true_iff',
    '(carrier.exposed_field_source field).trans sourceAt',
  ],'hidden-field-interface');
  require0(block('spliceResult').endsWith(
    'unpack (ArbitrarySupportSplice.result carrier.exposed.candidate records replacement compiled).toImplementation'),
    'actual-rebound-carrier');
  require0(block('splice').endsWith(
    '(ArbitrarySupportSplice.compile carrier.exposed.candidate records replacement).map (carrier.spliceResult records replacement)'),
    'actual-splice-compiler');
  require0(block('productionModel').endsWith(
    '{ profileSystem := { role := Fin.elim0, observe := fun _ => Fin.elim0 } projection := { keep := Fin.elim0 } observe := fun _ => Fin.elim0 }'),
    'no-supplied-profile-observer');
  require0(block('productionRecords').endsWith(
    'terminalSaturateRecords (terminalCandidateSaturationSystem carrier.exposed.candidate carrier.productionModel) seed'),
    'actual-production-predecessors');
  includes('production_compiles',[
    'ArbitrarySupportSplice.production_compiles carrier.exposed.candidate carrier.productionModel seed replacement',
    'congrArg (Option.map (carrier.spliceResult (carrier.productionRecords seed) replacement)) compiledAt',
  ],'production-executes-without-certificate');
  return [...new Set(failures)];
}

test('M250 constructs literal carrier values with complete general transport interfaces',async()=>{
  assert.deepEqual(validateSource0(await text0(SOURCE)),[]);
});

test('M250 root, exact theorem-name producers and axiom audit agree',async()=>{
  const [audit,inventorySource,root]=await Promise.all([
    text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean')]);
  for(const name of NAMES){
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item=>item===name).length,1,name);
    assert.equal(inventorySource.split(String.fromCharCode(96)+name+',').length-1,1,name);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),NAMES);
  assert.match(root,/^import PNP\.NANDWireCarrier\s*$/mu);
});

test('M250 rejects lost fields, wrong packing, fake cost and supplied computations',async()=>{
  const source=await text0(SOURCE);
  for(const [before,after,category] of [
    ['source : Fin fields → Source inputs implementation.gateCount',
      'source : Fin fields → Bool','literal-wire-fields-only'],
    ['(carrier.source field).eval valuation','(Source.constant false).eval valuation','actual-wire-evaluation'],
    ['splitFin carrier.implementation.candidate.directWireWord.source\n      carrier.source',
      'splitFin carrier.source\n      carrier.implementation.candidate.directWireWord.source','complete-zero-gate-exposure'],
    ['(Fin.natAdd outputs field)','(Fin.castAdd outputs field)','ordered-exact-unpacking'],
    ['unpack (runPhysicalNormalization carrier.exposed).result',
      'carrier','actual-complete-normalization'],
    ['def normalize (carrier : WireCarrier inputs outputs fields)',
      'def normalize (suppliedResult : WireCarrier inputs outputs fields) (carrier : WireCarrier inputs outputs fields)',
      'shortcut-or-certificate'],
    ['(ArbitrarySupportSplice.compile carrier.exposed.candidate records replacement).map',
      '(none : Option Nat).map','actual-splice-compiler'],
    ['observe := fun _ => Fin.elim0','observe := suppliedObserver','no-supplied-profile-observer'],
    ['(carrier.exposed_field_source field).trans sourceAt',
      'sourceAt','hidden-field-interface'],
    ['carrier.implementation.gateCount + replacementGates :=',
      'carrier.implementation.gateCount + replacementGates + fields :=','signature:splice_exact_accounting'],
    ['(carrier.spliceResult records replacement compiled).implementation.gateCount <\n      carrier.implementation.gateCount :=',
      '(carrier.spliceResult records replacement compiled).implementation.gateCount ≤\n      carrier.implementation.gateCount :=','signature:splice_strict_gain'],
    ['theorem normalize_field (carrier : WireCarrier inputs outputs fields)',
      'theorem normalize_field (carrier : WireCarrier 1 outputs fields)','signature:normalize_field'],
    ['theorem production_compiles\n    (seed : List',
      'theorem production_compiles\n    (callerCertificate : True) (seed : List','signature:production_compiles'],
  ]){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n').includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n').includes('unaudited-form'));
});

test('M250 theorem-head parsing includes complete dependent binders',()=>{
  const declaration='theorem transport (source : Carrier (fields := fields)) '+
    '(same : source = target) : target = source := same.symm';
  assert.equal(signature0(declaration),declaration.slice(0,declaration.lastIndexOf(' := ')));
  assert.notEqual(signature0(declaration.replace('(same :','(extra : True) (same :')),
    signature0(declaration));
});

test('M250 regressions keep hidden values, reject cycles and count actual replacements',async()=>{
  const raw=await text0(REGRESSION), regression=compact0(raw);
  for(const token of [
    'carrier.normalize_output valuation output','carrier.normalize_field valuation field',
    'carrier.normalize_idempotent','WireCarrier.exposed_unpack combined',
    'carrier.field_producer_visible records field producer sourceAt selected',
    'carrier.splice_checked records replacement sameOpen result accepted',
    'carrier.production_compiles seed replacement','lostField.fieldValue',
    'hiddenCarrier.fieldValue','safe_equivalent','cyclic_equivalent',
    'production_equivalent','larger_equivalent','cyclicGraph.Depends',
    'chainCarrier.splice_failure_iff interleaved cyclicReplacement',
    'hiddenCarrier.normalize','richCarrier.normalize','noFields.normalize','fieldsOnly.normalize',
    'emptyCarrier.normalize','chainCarrier.splice interleaved safeReplacement',
    'chainCarrier.splice interleaved cyclicReplacement',
    'chainCarrier.splice closedRecords productionSmaller',
    'chainCarrier.splice closedRecords productionLarger',
    'observed != [!value, value, false, !value, true, !value]',
    'throw (IO.userError',
  ])assert.ok(regression.includes(token),token);
  assert.equal([...raw.matchAll(/^#eval\b/gmu)].length,1);
  assert.doesNotMatch(regression,/\b(?:sorry|admit|native_decide|Classical|referenceMinimum|scanEquivalentSizes|allCandidates)\b/u);
});

test('M250 durable workflow retains source checks, exact audit and bounded regressions',async()=>{
  const [packageText,surface,verifier,workflow]=await Promise.all([
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),text0('.github/workflows/lean-bridge.yml')]);
  const auditPath='audits/lean-wire-carrier0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m250'],'node --test '+auditPath);
  assert.ok(surface.includes("'audit:m250': 'node --test "+auditPath+"'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test '+auditPath));
  for(const path of [auditPath,'docs/lean_wire_carrier.md'])
    assert.equal(workflow.split("      - '"+path+"'").length-1,2);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M250_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-12-250';
const M250_MILESTONE = 'wire-carrier-transport';
const M250_HASHES = Object.freeze({
  "PNP.DirectWire.WireCarrier.exposed_unpack": "52b06e232ee698792723138e1bd7c233a0df92fc0596e5d1cb5a5ad3a6998ab2",
  "PNP.DirectWire.WireCarrier.unpack_exposed": "e4bc75b87eb806542a29c7a7c6e523ba784ae91d2cdd3f258df74dee3a50190f",
  "PNP.DirectWire.WireCarrier.normalize_output": "16061da3c8919111c1c6978a464a20b8569b0699b37cd393eb2dcdec5c9056aa",
  "PNP.DirectWire.WireCarrier.normalize_field": "7db27122f63ded43c385da4a7261d23c7e9879d028553550b08aa876d4792416",
  "PNP.DirectWire.WireCarrier.normalize_exact_accounting": "a198f6730e3dc53bbc9b1ab5c0422213e3d608a01e5db509eecdba8758f2ff2b",
  "PNP.DirectWire.WireCarrier.normalize_quiescent": "34ab38584d59be857e7cf3a55c64f5c88f1f90c4dd2f40d67daa464aa8075ecd",
  "PNP.DirectWire.WireCarrier.normalize_idempotent": "f7cce5f43df79ea96c60e655cb5b86173522fde20c2234a439868221011420c5",
  "PNP.DirectWire.WireCarrier.field_producer_visible": "bc09f579729f6afb62951d1703ece5a713fe6a4beeed9cc53ca40c6fe3761b84",
  "PNP.DirectWire.WireCarrier.splice_output": "411dc13ea230fc22b77724331e9e1c33714d660a4a604cfd7898538c8786f74c",
  "PNP.DirectWire.WireCarrier.splice_field": "4ba4f77a1c9283281452654d90c7345f8d0f8c6dc9191e0605cda7c42484bb0d",
  "PNP.DirectWire.WireCarrier.splice_exact_accounting": "5f466be2d9ebc3e5d9cf6e0e846f82bbaf1b888e89e12f38adf89aef53fd7d58",
  "PNP.DirectWire.WireCarrier.splice_strict_gain": "4123bc53c6f2b6de684443b5c59fc548ccec92315b2f414fe8bc2a34a4585be6",
  "PNP.DirectWire.WireCarrier.splice_checked": "98107b6a054e0da36408a39910ff8938933712f48a4a2f5dd669b98900d303f9",
  "PNP.DirectWire.WireCarrier.splice_failure_iff": "8267d78155cac9ef72b19406e8a7b9e94064d7c675dddea99d1ef3e7c6fb881e",
  "PNP.DirectWire.WireCarrier.production_boundary_isInput": "685e00c4d3d3038805c3db5f9c6b028a28ae8ef39c7cadab56e116151fafc1fc",
  "PNP.DirectWire.WireCarrier.production_compiles": "09f0bee838b9d67f46d451c461a6272810bef6ec49d7b00cd1e4c615cefa8e22"
});
const M250_STATUS_FIELDS = Object.freeze({
  "leanWireCarrierTransportFormalized": true,
  "leanWireCarrierTransportAxiomAuditPassed": true,
  "leanWireCarrierTransportAuditedDeclarationCount": 16,
  "leanWireCarrierTransportPackUnpackTheorem": "PNP.DirectWire.WireCarrier.exposed_unpack",
  "leanWireCarrierTransportUnpackPackTheorem": "PNP.DirectWire.WireCarrier.unpack_exposed",
  "leanWireCarrierTransportNormalizationOutputTheorem": "PNP.DirectWire.WireCarrier.normalize_output",
  "leanWireCarrierTransportNormalizationFieldTheorem": "PNP.DirectWire.WireCarrier.normalize_field",
  "leanWireCarrierTransportNormalizationAccountingTheorem": "PNP.DirectWire.WireCarrier.normalize_exact_accounting",
  "leanWireCarrierTransportNormalizationQuiescenceTheorem": "PNP.DirectWire.WireCarrier.normalize_quiescent",
  "leanWireCarrierTransportNormalizationIdempotenceTheorem": "PNP.DirectWire.WireCarrier.normalize_idempotent",
  "leanWireCarrierTransportHiddenFieldInterfaceTheorem": "PNP.DirectWire.WireCarrier.field_producer_visible",
  "leanWireCarrierTransportSpliceOutputTheorem": "PNP.DirectWire.WireCarrier.splice_output",
  "leanWireCarrierTransportSpliceFieldTheorem": "PNP.DirectWire.WireCarrier.splice_field",
  "leanWireCarrierTransportSpliceAccountingTheorem": "PNP.DirectWire.WireCarrier.splice_exact_accounting",
  "leanWireCarrierTransportSpliceStrictGainTheorem": "PNP.DirectWire.WireCarrier.splice_strict_gain",
  "leanWireCarrierTransportSpliceExecutionTheorem": "PNP.DirectWire.WireCarrier.splice_checked",
  "leanWireCarrierTransportCyclicRejectionTheorem": "PNP.DirectWire.WireCarrier.splice_failure_iff",
  "leanWireCarrierTransportProductionBoundaryTheorem": "PNP.DirectWire.WireCarrier.production_boundary_isInput",
  "leanWireCarrierTransportProductionSuccessTheorem": "PNP.DirectWire.WireCarrier.production_compiles",
  "leanWireCarrierTransportFullManuscriptCarrierDerived": false,
  "leanWireCarrierTransportObligationLifecycleProved": false,
  "leanWireCarrierTransportUnrestrictedReplacementSuccessProved": false,
  "leanWireCarrierTransportCompletePackageEProved": false,
  "leanWireCarrierTransportPolynomialRuntimeProved": false,
  "leanWireCarrierTransportScope": "all-finite-literal-wire-backed-computational-fields-complete-ordered-exposure-computed-normalization-and-arbitrary-support-splice-value-preservation-exact-physical-accounting-derived-production-predecessors-no-full-manuscript-carrier-or-polynomial-runtime"
});
const M250_AXIOMS = Object.freeze({
  "PNP.DirectWire.WireCarrier.exposed_unpack": [
    "Quot.sound"
  ],
  "PNP.DirectWire.WireCarrier.unpack_exposed": [
    "Quot.sound"
  ],
  "PNP.DirectWire.WireCarrier.normalize_output": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireCarrier.normalize_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireCarrier.normalize_exact_accounting": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireCarrier.normalize_quiescent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireCarrier.normalize_idempotent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireCarrier.field_producer_visible": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireCarrier.splice_output": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireCarrier.splice_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireCarrier.splice_exact_accounting": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireCarrier.splice_strict_gain": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireCarrier.splice_checked": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireCarrier.splice_failure_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireCarrier.production_boundary_isInput": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireCarrier.production_compiles": [
    "Quot.sound",
    "propext"
  ]
});

const M250_MODULES = Object.freeze({
  "PNP.DirectWire.WireCarrier.exposed_unpack": "PNP.NANDWireCarrier",
  "PNP.DirectWire.WireCarrier.unpack_exposed": "PNP.NANDWireCarrier",
  "PNP.DirectWire.WireCarrier.normalize_output": "PNP.NANDWireCarrier",
  "PNP.DirectWire.WireCarrier.normalize_field": "PNP.NANDWireCarrier",
  "PNP.DirectWire.WireCarrier.normalize_exact_accounting": "PNP.NANDWireCarrier",
  "PNP.DirectWire.WireCarrier.normalize_quiescent": "PNP.NANDWireCarrier",
  "PNP.DirectWire.WireCarrier.normalize_idempotent": "PNP.NANDWireCarrier",
  "PNP.DirectWire.WireCarrier.field_producer_visible": "PNP.NANDWireCarrier",
  "PNP.DirectWire.WireCarrier.splice_output": "PNP.NANDWireCarrier",
  "PNP.DirectWire.WireCarrier.splice_field": "PNP.NANDWireCarrier",
  "PNP.DirectWire.WireCarrier.splice_exact_accounting": "PNP.NANDWireCarrier",
  "PNP.DirectWire.WireCarrier.splice_strict_gain": "PNP.NANDWireCarrier",
  "PNP.DirectWire.WireCarrier.splice_checked": "PNP.NANDWireCarrier",
  "PNP.DirectWire.WireCarrier.splice_failure_iff": "PNP.NANDWireCarrier",
  "PNP.DirectWire.WireCarrier.production_boundary_isInput": "PNP.NANDWireCarrier",
  "PNP.DirectWire.WireCarrier.production_compiles": "PNP.NANDWireCarrier"
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

test('M250 compiled wire-backed carrier interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M250_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M250_COORDINATE)
    assert.equal(map.coordinate, M250_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M250_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, M250_MODULES[name], name);
      assert.deepEqual(declaration.axioms, M250_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M250_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M250_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M250_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "wire bindings are actual input data",
  "Proof-only records do not become Boolean sources",
  "R5/R6-R8 obligation creation and discharge",
  "Equal local Boolean functions do not guarantee acyclic arbitrary literal splicing",
  "no fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M250 publication rejects weakened, supplied, assumption-backed and widened full-carrier substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M250_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M250_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = 'PNP.DirectWire.WireCarrier.splice_field';
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M250_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M250_MILESTONE
    ? {...row, nonClaim:'All fields establish the complete manuscript carrier, obligation calculus and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M250 adds computational carrier coverage without full-carrier, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M250_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "computational-value preservation edge",
  "without arbitrary observers or extra gate charges",
  "not the derivation of the full carrier",
  "No fixed load-bearing checkpoint changes state"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M250_COORDINATE) return;
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

test('M250 current summaries distinguish computational field transport from full-carrier and global completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_wire_carrier.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "No observer, wire map, topological order or successful result is supplied to the constructor",
  "local open-function equality includes every computed field port",
  "Equal local Boolean functions do not guarantee acyclic literal wiring",
  "Runtime execution is test evidence, not theorem authority",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-12-computed-wire-backed-carrier-transport.md'));
  assert.match(plan, /Publication decision: defer PNPLabs(?:[.,]|$)/u);
  if (progress.asOfCoordinate !== M250_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_wire_carrier.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
