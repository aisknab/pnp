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

const SOURCE = 'lean/PNP/NANDWireUnaryRealization.lean';
const AUDIT = 'lean-audit/PNPWireUnaryRealizationAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPWireUnaryRealization.lean';
const NAMES = [
  "PNP.DirectWire.WireUnaryRealization.observation_value",
  "PNP.DirectWire.WireUnaryRealization.needsNegation_iff",
  "PNP.DirectWire.WireUnaryRealization.implementation_value",
  "PNP.DirectWire.WireUnaryRealization.realize_output",
  "PNP.DirectWire.WireUnaryRealization.realize_field",
  "PNP.DirectWire.WireUnaryRealization.realize_equivalent",
  "PNP.DirectWire.WireUnaryRealization.realize_full_equivalent",
  "PNP.DirectWire.WireUnaryRealization.realize_gateCount",
  "PNP.DirectWire.WireUnaryRealization.negation_requires_gate",
  "PNP.DirectWire.WireUnaryRealization.realize_minimal",
  "PNP.DirectWire.WireUnaryRealization.realize_nonincrease",
  "PNP.DirectWire.WireUnaryRealization.realize_gate_bound",
  "PNP.DirectWire.WireUnaryRealization.R7Discharge.full_value",
  "PNP.DirectWire.WireUnaryRealization.dischargeR7_source_exact",
  "PNP.DirectWire.WireUnaryRealization.dischargeR7_full_value",
  "PNP.DirectWire.WireUnaryRealization.checkedGain_isSome_iff",
  "PNP.DirectWire.WireUnaryRealization.checkedGain_complete",
  "PNP.DirectWire.WireUnaryRealization.CheckedGain.checked"
];
const SIGNATURES = {
  "observation_value": "theorem observation_value (carrier : WireCarrier 1 outputs fields) (valuation : Valuation 1) (observation : Fin (outputs + fields)) : carrier.exposed.candidate.semantics valuation observation = if valuation fin1Zero then bit carrier true observation else bit carrier false observation",
  "needsNegation_iff": "theorem needsNegation_iff (carrier : WireCarrier 1 outputs fields) : needsNegation carrier = true ↔ ∃ observation, bit carrier false observation = true ∧ bit carrier true observation = false",
  "implementation_value": "theorem implementation_value (carrier : WireCarrier 1 outputs fields) (valuation : Valuation 1) (observation : Fin (outputs + fields)) : (implementation carrier).candidate.semantics valuation observation = carrier.exposed.candidate.semantics valuation observation",
  "realize_output": "theorem realize_output (carrier : WireCarrier 1 outputs fields) (valuation : Valuation 1) (output : Fin outputs) : (realize carrier).implementation.candidate.semantics valuation output = carrier.implementation.candidate.semantics valuation output",
  "realize_field": "theorem realize_field (carrier : WireCarrier 1 outputs fields) (valuation : Valuation 1) (field : Fin fields) : (realize carrier).fieldValue valuation field = carrier.fieldValue valuation field",
  "realize_equivalent": "theorem realize_equivalent (carrier : WireCarrier 1 outputs fields) : Equivalent (realize carrier).implementation.candidate.program (realize carrier).implementation.candidate.directWireWord carrier.implementation.candidate.program carrier.implementation.candidate.directWireWord",
  "realize_full_equivalent": "theorem realize_full_equivalent (carrier : WireCarrier 1 outputs fields) : Equivalent (realize carrier).exposed.candidate.program (realize carrier).exposed.candidate.directWireWord carrier.exposed.candidate.program carrier.exposed.candidate.directWireWord",
  "realize_gateCount": "theorem realize_gateCount (carrier : WireCarrier 1 outputs fields) : (realize carrier).implementation.gateCount = if needsNegation carrier then 1 else 0",
  "negation_requires_gate": "theorem negation_requires_gate {width : Nat} (other : Implementation 1 width) (observation : Fin width) (low : other.candidate.semantics (fun _ => false) observation = true) (high : other.candidate.semantics (fun _ => true) observation = false) : 1 ≤ other.gateCount",
  "realize_minimal": "theorem realize_minimal (carrier other : WireCarrier 1 outputs fields) (sameFull : Equivalent other.exposed.candidate.program other.exposed.candidate.directWireWord carrier.exposed.candidate.program carrier.exposed.candidate.directWireWord) : (realize carrier).implementation.gateCount ≤ other.implementation.gateCount",
  "realize_nonincrease": "theorem realize_nonincrease (carrier : WireCarrier 1 outputs fields) : (realize carrier).implementation.gateCount ≤ carrier.implementation.gateCount",
  "realize_gate_bound": "theorem realize_gate_bound (carrier : WireCarrier 1 outputs fields) : (realize carrier).implementation.gateCount ≤ 1",
  "R7Discharge.full_value": "theorem R7Discharge.full_value {carrier : WireCarrier 1 outputs fields} {keep : Fin fields → Bool} {creation : WireObligationRestoration.R5Creation carrier keep} (witness : R7Discharge carrier keep creation) (valuation : Valuation 1) : witness.actualSource.eval valuation ((realize carrier).implementation.candidate.program.eval valuation) = carrier.fieldValue valuation creation.coordinate",
  "dischargeR7_source_exact": "theorem dischargeR7_source_exact (carrier : WireCarrier 1 outputs fields) (keep : Fin fields → Bool) (creation : WireObligationRestoration.R5Creation carrier keep) : (dischargeR7 carrier keep creation).actualSource = (realize carrier).source creation.coordinate",
  "dischargeR7_full_value": "theorem dischargeR7_full_value (carrier : WireCarrier 1 outputs fields) (keep : Fin fields → Bool) (creation : WireObligationRestoration.R5Creation carrier keep) (valuation : Valuation 1) : (dischargeR7 carrier keep creation).actualSource.eval valuation ((realize carrier).implementation.candidate.program.eval valuation) = carrier.fieldValue valuation creation.coordinate",
  "checkedGain_isSome_iff": "theorem checkedGain_isSome_iff (carrier : WireCarrier 1 outputs fields) : (checkedGain carrier).isSome = true ↔ (realize carrier).implementation.gateCount < carrier.implementation.gateCount",
  "checkedGain_complete": "theorem checkedGain_complete (carrier other : WireCarrier 1 outputs fields) (sameFull : Equivalent other.exposed.candidate.program other.exposed.candidate.directWireWord carrier.exposed.candidate.program carrier.exposed.candidate.directWireWord) (smaller : other.implementation.gateCount < carrier.implementation.gateCount) : (checkedGain carrier).isSome = true",
  "CheckedGain.checked": "theorem CheckedGain.checked {carrier : WireCarrier 1 outputs fields} (gain : CheckedGain carrier) : StrictEquivalentGain carrier.implementation (realize carrier).implementation ∧ (∀ valuation field, (realize carrier).fieldValue valuation field = carrier.fieldValue valuation field) ∧ (realize carrier).implementation.gateCount = (if needsNegation carrier then 1 else 0)"
};
const HEADS = [
  "bit",
  "observation_value",
  "negatedAt",
  "needsNegation",
  "needsNegation_iff",
  "zeroSource",
  "oneSource",
  "zeroImplementation",
  "oneImplementation",
  "implementation",
  "realize",
  "implementation_value",
  "realize_output",
  "realize_field",
  "realize_equivalent",
  "realize_full_equivalent",
  "realize_gateCount",
  "negation_requires_gate",
  "realize_minimal",
  "realize_nonincrease",
  "realize_gate_bound",
  "R7Discharge",
  "dischargeR7",
  "R7Discharge.full_value",
  "dischargeR7_source_exact",
  "dischargeR7_full_value",
  "CheckedGain",
  "checkedGain",
  "checkedGain_isSome_iff",
  "checkedGain_complete",
  "CheckedGain.strictGain",
  "CheckedGain.checked"
];

const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = value => stripLeanCommentsAndStrings0(value).replace(/\s+/gu,' ').trim();
function block0(source,name) {
  const stripped=stripLeanCommentsAndStrings0(source);
  const boundaries=[...stripped.matchAll(/^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*(?:(?:def|theorem|inductive|structure|abbrev)[ \t]+([^\s({:]+)|variable\b|namespace\b|end\b)/gmu)];
  const index=boundaries.findIndex(item=>item[1]===name);
  return index<0?'':compact0(source.slice(boundaries[index].index,boundaries[index+1]?.index??source.length));
}
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
  const includes=(name,tokens,category)=>
    require0(tokens.every(token=>block(name).includes(token)),category);
  require0(!hasLeanAssumptionDeclaration0(source),'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source),'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|suppliedTable|suppliedResult|callerCertificate)\b/u.test(clean),'shortcut-or-certificate');
  require0(!/\b(?:allCandidates|allBoolTuples|allSubsets|equivalentBool|referenceMinimum|scanEquivalentSizes|terminalFullProfileMinimum)\b/u.test(clean),'no-implementation-enumeration');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]))===
    JSON.stringify(['PNP.NANDWireObligationRestoration']),'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name))===
    JSON.stringify(HEADS),'public-interface');
  require0(clean.includes('variable {outputs fields : Nat}'),'unbounded-observation-dimensions');
  for(const [name,signature] of Object.entries(SIGNATURES))
    require0(signature0(block(name))===signature,'signature:'+name);
  require0(block('bit').endsWith(
    'carrier.exposed.candidate.semantics (fun _ => value) observation'),'actual-source-valuations');
  require0(block('needsNegation').endsWith(
    '(allFin (outputs + fields)).any (negatedAt carrier)'),'complete-observation-scan');
  require0(block('negatedAt').endsWith(
    'bit carrier false observation && !(bit carrier true observation)'),'derived-negation-classifier');
  includes('zeroSource',[
    '| false, false => .constant false','| false, true => .input fin1Zero',
    '| true, false => .constant false','| true, true => .constant true',
  ],'zero-gate-sources');
  includes('oneSource',[
    '| false, false => .constant false','| false, true => .input fin1Zero',
    '| true, false => .gate fin1Zero','| true, true => .constant true',
  ],'single-shared-negation-source');
  includes('zeroSource_value',['(notNegated : (low && (!high)) = false)'],
    'explicit-boolean-no-negation-premise');
  includes('zeroImplementation',[
    '(Candidate.ofDirectWireWord (.empty : Program 1 0)',
    'zeroSource (bit carrier false observation) (bit carrier true observation)',
  ],'actual-zero-implementation');
  includes('oneImplementation',[
    '(Candidate.ofDirectWireWord notProgram',
    'oneSource (bit carrier false observation) (bit carrier true observation)',
  ],'one-actual-not-program');
  require0(block('implementation')===
    'def implementation (carrier : WireCarrier 1 outputs fields) : Implementation 1 (outputs + fields) := if needsNegation carrier then oneImplementation carrier else zeroImplementation carrier',
    'source-only-computed-constructor');
  require0(block('realize')===
    'def realize (carrier : WireCarrier 1 outputs fields) : WireCarrier 1 outputs fields := WireCarrier.unpack (implementation carrier)',
    'actual-full-word-unpack');
  includes('realize_minimal',[
    'negation_requires_gate other.exposed observation',
    '(sameFull (fun _ => false) observation).trans low',
    '(sameFull (fun _ => true) observation).trans high',
  ],'full-word-minimum-lower-bound');
  includes('R7Discharge',[
    'actualSource : Source 1 (realize carrier).implementation.gateCount',
    'sourceExact : actualSource = (realize carrier).source creation.coordinate',
    'fullWitness : ∀ valuation, actualSource.eval valuation ((realize carrier).implementation.candidate.program.eval valuation) = creation.originalSource.eval valuation (carrier.implementation.candidate.program.eval valuation)',
  ],'source-exact-full-r7-witness');
  includes('dischargeR7',[
    'actualSource := (realize carrier).source creation.coordinate',
    'rw [creation.sourceExact]',
    'exact realize_field carrier valuation creation.coordinate',
  ],'derived-full-r7-witness');
  require0(signature0(block('dischargeR7'))===
    'def dischargeR7 (carrier : WireCarrier 1 outputs fields) (keep : Fin fields → Bool) (creation : WireObligationRestoration.R5Creation carrier keep) : R7Discharge carrier keep creation',
    'no-supplied-r7-agreement');
  includes('checkedGain',[
    'if smaller : (realize carrier).implementation.gateCount < carrier.implementation.gateCount then some ⟨smaller⟩ else none',
  ],'actual-whole-word-gain');
  return [...new Set(failures)];
}

test('M255 computes every unary observation and its actual shared minimum',async()=>{
  assert.deepEqual(validateSource0(await text0(SOURCE)),[]);
});

test('M255 root, exact theorem-name producers and axiom audit agree',async()=>{
  const [audit,inventorySource,root]=await Promise.all([
    text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean')]);
  for(const name of NAMES){
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item=>item===name).length,1,name);
    assert.equal(inventorySource.split(String.fromCharCode(96)+name+',').length-1,1,name);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),NAMES);
  assert.match(root,/^import PNP\.NANDWireUnaryRealization\s*$/mu);
});

function rejectMutations0(source,mutations) {
  for(const [before,after,category] of mutations){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
}

test('M255 rejects supplied tables, output-only scans and fixed observation dimensions',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['carrier.exposed.candidate.semantics (fun _ => value) observation',
      'suppliedTable value observation','actual-source-valuations'],
    ['(allFin (outputs + fields)).any (negatedAt carrier)',
      '(allFin outputs).any (negatedAt carrier)','complete-observation-scan'],
    ['bit carrier false observation && !(bit carrier true observation)',
      'bit carrier false observation','derived-negation-classifier'],
    ['theorem realize_field (carrier : WireCarrier 1 outputs fields)',
      'theorem realize_field (carrier : WireCarrier 1 2 fields)','signature:realize_field'],
    ['def implementation (carrier : WireCarrier 1 outputs fields)',
      'def implementation (carrier : WireCarrier 1 outputs fields) (suppliedResult : Implementation 1 (outputs + fields))',
      'source-only-computed-constructor'],
  ]);
});

test('M255 rejects free negation, duplicated physical gates and ambiguous Boolean premises',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['| true, false => .gate fin1Zero','| true, false => .input fin1Zero',
      'single-shared-negation-source'],
    ['(Candidate.ofDirectWireWord notProgram',
      '(Candidate.ofDirectWireWord (notProgram.snoc extraGate)','one-actual-not-program'],
    ['(notNegated : (low && (!high)) = false)',
      '(notNegated : low && !high = false)','explicit-boolean-no-negation-premise'],
    ['if needsNegation carrier then oneImplementation carrier else zeroImplementation carrier',
      'zeroImplementation carrier','source-only-computed-constructor'],
    ['WireCarrier.unpack (implementation carrier)',
      'WireObligationRestoration.masked carrier (fun _ => false)','actual-full-word-unpack'],
  ]);
});

test('M255 rejects ordinary-only minima, reversed bounds and finite comparison sets',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['(sameFull : Equivalent other.exposed.candidate.program',
      '(sameFull : Equivalent other.implementation.candidate.program','signature:realize_minimal'],
    ['(realize carrier).implementation.gateCount ≤ other.implementation.gateCount',
      'other.implementation.gateCount ≤ (realize carrier).implementation.gateCount',
      'signature:realize_minimal'],
    ['negation_requires_gate other.exposed observation',
      'negation_requires_gate carrier.exposed observation','full-word-minimum-lower-bound'],
    ['(carrier other : WireCarrier 1 outputs fields)',
      '(carrier other : WireCarrier 1 1 fields)','signature:realize_minimal'],
    ['(low : other.candidate.semantics (fun _ => false) observation = true)',
      '(low : True)','signature:negation_requires_gate'],
  ]);
});

test('M255 rejects padding, unrelated programs and caller-supplied R7 witnesses',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['sourceExact : actualSource = (realize carrier).source creation.coordinate',
      'sourceExact : True','source-exact-full-r7-witness'],
    ['fullWitness : ∀ valuation,','fullWitness : ∃ valuation,','source-exact-full-r7-witness'],
    ['actualSource := (realize carrier).source creation.coordinate',
      'actualSource := .constant false','derived-full-r7-witness'],
    ['exact realize_field carrier valuation creation.coordinate',
      'exact suppliedResult','derived-full-r7-witness'],
    ['(creation : WireObligationRestoration.R5Creation carrier keep) :\n    R7Discharge carrier keep creation :=',
      '(creation : WireObligationRestoration.R5Creation carrier keep) (same : True) :\n    R7Discharge carrier keep creation :=',
      'no-supplied-r7-agreement'],
  ]);
});

test('M255 rejects unpaid gains and weakened complete-word certificates',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['if smaller : (realize carrier).implementation.gateCount < carrier.implementation.gateCount',
      'if smaller : 0 < carrier.implementation.gateCount','actual-whole-word-gain'],
    ['(∀ valuation field, (realize carrier).fieldValue valuation field =',
      '(∃ valuation field, (realize carrier).fieldValue valuation field =',
      'signature:CheckedGain.checked'],
    ['(sameFull : Equivalent other.exposed.candidate.program',
      '(sameFull : Equivalent other.implementation.candidate.program','signature:checkedGain_complete'],
  ]);
});

test('M255 rejects assumptions, unaudited forms and exhaustive implementation search',async()=>{
  const source=await text0(SOURCE);
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n').includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n').includes('unaudited-form'));
  assert.ok(validateSource0(source+'\ndef extra := referenceMinimum\n').includes('no-implementation-enumeration'));
  assert.ok(validateSource0(source.replace('import PNP.NANDWireObligationRestoration',
    'import PNP.NANDWireObligationRestoration\nimport Unknown.Source')).includes('closed-imports'));
});

test('M255 theorem signatures retain dependent binders and dotted interface names',()=>{
  const declaration='theorem CheckedGain.checked (source : Carrier (fields := fields)) '+
    '(same : source = target) : target = source := same.symm';
  assert.equal(signature0(declaration),declaration.slice(0,declaration.lastIndexOf(' := ')));
  assert.equal(signature0(block0(declaration,'CheckedGain.checked')),signature0(declaration));
});

test('M255 regression checks cover full fields, repeated ownership and rejected ordinary-only replacement',async()=>{
  const regression=await text0(REGRESSION), clean=compact0(regression);
  for(const name of ['freeFields','singleNot','sharedNot','tautology','fieldOnlyNot',
    'paddedFields','unrelatedField','noOutputs','noFields','emptyWord','freeEmpty'])
    assert.match(clean,new RegExp('\\b'+name+'\\b','u'),name);
  assert.ok(clean.includes('¬Equivalent paddedFields.exposed.candidate.program'));
  assert.ok(clean.includes('for value in [false, true] do'));
  assert.ok(clean.includes('for field in allFin fields do'));
  assert.ok(clean.includes('if witness.actualSource ≠ actual.source field then'));
  assert.ok(clean.includes('(realize sharedNot).source 0 ≠ (realize sharedNot).source 3'));
  assert.ok(clean.includes('(realize sharedNot).implementation.candidate.directWireWord.source 0'));
  assert.ok(clean.includes('throw (IO.userError'));
  assert.ok(!/\b(?:native_decide|sorry|admit)\b/u.test(clean));
});

const M255_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-13-255';
const M255_MILESTONE = 'wire-unary-realization';
const M255_HASHES = Object.freeze({
  "PNP.DirectWire.WireUnaryRealization.observation_value": "0e33500a57b8014755eb324cb94a88a8003b72c517e85b6b7e9992dac62f186a",
  "PNP.DirectWire.WireUnaryRealization.needsNegation_iff": "83a83a00275421eb25c735e9f8f24785bc9f64ba58065c0bfe8be3340d4b696d",
  "PNP.DirectWire.WireUnaryRealization.implementation_value": "62a7a8db007388000aa40dc102f35ff142b1a810c3d490728bd4d1795a318f63",
  "PNP.DirectWire.WireUnaryRealization.realize_output": "092307fb96200f321c54e0765a5bb5cf31be1013de71bf3a708e70d9a51c92e0",
  "PNP.DirectWire.WireUnaryRealization.realize_field": "4ad51b9f8bb60af80b01543e78080aafbb42d0a5cf812e908ba90ca4233ca484",
  "PNP.DirectWire.WireUnaryRealization.realize_equivalent": "57b87868b12c3b735c89b6b006d160e423cf327024c5a6b2c3a34220e7b03718",
  "PNP.DirectWire.WireUnaryRealization.realize_full_equivalent": "cb77aa4f7f9b6269386b9d8fdf342c3bfc377b24e2f7e2d8e95d5b0fc72f4113",
  "PNP.DirectWire.WireUnaryRealization.realize_gateCount": "b4755d75e4153c374e4db394a5ec4bf6cd1dcce17168a45b796137b439c7bc0f",
  "PNP.DirectWire.WireUnaryRealization.negation_requires_gate": "0830bed847d01bcb5eb79ae2f6558568880e61075a5d5dc0dfc4e94ea7615214",
  "PNP.DirectWire.WireUnaryRealization.realize_minimal": "8687f6a8fcc08bcb32f606829cb3fc7758013acbee8d66fc69ad3ca0c1bc3430",
  "PNP.DirectWire.WireUnaryRealization.realize_nonincrease": "f23591915fb7fc1e714aeb1a108377802de42cc868ff8fe3af087e07e2a4acf6",
  "PNP.DirectWire.WireUnaryRealization.realize_gate_bound": "8fa89009a88967d4df395926dd7a1f7c4143d1223997b2b4bf62c63fbbd2cb5a",
  "PNP.DirectWire.WireUnaryRealization.R7Discharge.full_value": "9d0c1905736bf1019e6604996d70fefb515f1e137406ed5503ad0681c35b33ee",
  "PNP.DirectWire.WireUnaryRealization.dischargeR7_source_exact": "19945f8412e44faedfc91210ef4e83439d564a2824edfc1f90b1a1db07d59e61",
  "PNP.DirectWire.WireUnaryRealization.dischargeR7_full_value": "cffef514537ebcbd880834578e28877e24ba3c25394b490fab04b0045ca064aa",
  "PNP.DirectWire.WireUnaryRealization.checkedGain_isSome_iff": "7858c41c4efdbb472ae418a27f5d2329fff99241ac349df86b2feffd9d44b79a",
  "PNP.DirectWire.WireUnaryRealization.checkedGain_complete": "8a9b3ad847ac134d943f18e2247041be14b9042a8f4aa393bf2fe50a308223f2",
  "PNP.DirectWire.WireUnaryRealization.CheckedGain.checked": "785fbaa771e7477604ab00a32d2db483d958dade5d53f96e2c88ceea95ccbe75"
});
const M255_STATUS_FIELDS = Object.freeze({
  "leanWireUnaryRealizationFormalized": true,
  "leanWireUnaryRealizationAxiomAuditPassed": true,
  "leanWireUnaryRealizationAuditedDeclarationCount": 18,
  "leanWireUnaryRealizationObservationValueTheorem": "PNP.DirectWire.WireUnaryRealization.observation_value",
  "leanWireUnaryRealizationNegationIffTheorem": "PNP.DirectWire.WireUnaryRealization.needsNegation_iff",
  "leanWireUnaryRealizationImplementationValueTheorem": "PNP.DirectWire.WireUnaryRealization.implementation_value",
  "leanWireUnaryRealizationOutputTheorem": "PNP.DirectWire.WireUnaryRealization.realize_output",
  "leanWireUnaryRealizationFieldTheorem": "PNP.DirectWire.WireUnaryRealization.realize_field",
  "leanWireUnaryRealizationEquivalenceTheorem": "PNP.DirectWire.WireUnaryRealization.realize_equivalent",
  "leanWireUnaryRealizationFullEquivalenceTheorem": "PNP.DirectWire.WireUnaryRealization.realize_full_equivalent",
  "leanWireUnaryRealizationExactGateCountTheorem": "PNP.DirectWire.WireUnaryRealization.realize_gateCount",
  "leanWireUnaryRealizationNegationLowerBoundTheorem": "PNP.DirectWire.WireUnaryRealization.negation_requires_gate",
  "leanWireUnaryRealizationFullMinimumTheorem": "PNP.DirectWire.WireUnaryRealization.realize_minimal",
  "leanWireUnaryRealizationNonincreaseTheorem": "PNP.DirectWire.WireUnaryRealization.realize_nonincrease",
  "leanWireUnaryRealizationGateBoundTheorem": "PNP.DirectWire.WireUnaryRealization.realize_gate_bound",
  "leanWireUnaryRealizationR7WitnessFullValueTheorem": "PNP.DirectWire.WireUnaryRealization.R7Discharge.full_value",
  "leanWireUnaryRealizationR7SourceExactTheorem": "PNP.DirectWire.WireUnaryRealization.dischargeR7_source_exact",
  "leanWireUnaryRealizationComputedR7FullValueTheorem": "PNP.DirectWire.WireUnaryRealization.dischargeR7_full_value",
  "leanWireUnaryRealizationGainIffTheorem": "PNP.DirectWire.WireUnaryRealization.checkedGain_isSome_iff",
  "leanWireUnaryRealizationGainCompletenessTheorem": "PNP.DirectWire.WireUnaryRealization.checkedGain_complete",
  "leanWireUnaryRealizationCheckedGainTheorem": "PNP.DirectWire.WireUnaryRealization.CheckedGain.checked",
  "leanWireUnaryRealizationArbitraryAmbientCutsCovered": false,
  "leanWireUnaryRealizationAllR7CasesDerived": false,
  "leanWireUnaryRealizationArbitraryObligationDAGsCovered": false,
  "leanWireUnaryRealizationFullManuscriptCarrierProved": false,
  "leanWireUnaryRealizationCompleteObligationCalculusProved": false,
  "leanWireUnaryRealizationCompletePackageEProved": false,
  "leanWireUnaryRealizationPolynomialRuntimeProved": false,
  "leanWireUnaryRealizationScope": "all-unary-computational-wire-actual-two-source-valuations-arbitrary-gate-and-full-observation-counts-computed-zero-or-one-shared-not-complete-full-values-universal-full-word-minimum-source-exact-r7-discharge-complete-whole-word-gain-no-ambient-calculus-or-polynomial-runtime"
});
const M255_AXIOMS = Object.freeze({
  "PNP.DirectWire.WireUnaryRealization.observation_value": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryRealization.needsNegation_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryRealization.implementation_value": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryRealization.realize_output": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryRealization.realize_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryRealization.realize_equivalent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryRealization.realize_full_equivalent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryRealization.realize_gateCount": [],
  "PNP.DirectWire.WireUnaryRealization.negation_requires_gate": [],
  "PNP.DirectWire.WireUnaryRealization.realize_minimal": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryRealization.realize_nonincrease": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryRealization.realize_gate_bound": [],
  "PNP.DirectWire.WireUnaryRealization.R7Discharge.full_value": [],
  "PNP.DirectWire.WireUnaryRealization.dischargeR7_source_exact": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryRealization.dischargeR7_full_value": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryRealization.checkedGain_isSome_iff": [],
  "PNP.DirectWire.WireUnaryRealization.checkedGain_complete": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryRealization.CheckedGain.checked": [
    "Quot.sound",
    "propext"
  ]
});

const M255_MODULES = Object.freeze({
  "PNP.DirectWire.WireUnaryRealization.observation_value": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.needsNegation_iff": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.implementation_value": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.realize_output": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.realize_field": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.realize_equivalent": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.realize_full_equivalent": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.realize_gateCount": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.negation_requires_gate": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.realize_minimal": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.realize_nonincrease": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.realize_gate_bound": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.R7Discharge.full_value": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.dischargeR7_source_exact": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.dischargeR7_full_value": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.checkedGain_isSome_iff": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.checkedGain_complete": "PNP.NANDWireUnaryRealization",
  "PNP.DirectWire.WireUnaryRealization.CheckedGain.checked": "PNP.NANDWireUnaryRealization"
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

test('M255 compiled unary full-word realization interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M255_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M255_COORDINATE)
    assert.equal(map.coordinate, M255_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M255_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, M255_MODULES[name], name);
      assert.deepEqual(declaration.axioms, M255_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M255_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M255_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M255_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "not an arbitrary ambient-cut embedding",
  "not ordinary outputs alone",
  "whole-word strict gain is not a proper-support Package E certificate",
  "does not prove polynomial encoded runtime",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M255 publication rejects weakened, supplied, assumption-backed and widened complete-calculus substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M255_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M255_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = 'PNP.DirectWire.WireUnaryRealization.realize_field';
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M255_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M255_MILESTONE
    ? {...row, nonClaim:'The unary realization proves every ambient cut, the complete obligation calculus and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M255 adds computed unary realization coverage without complete-calculus, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M255_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "unary R7 realization component",
  "every equivalent full carrier rather than only ordinary outputs",
  "no supplied replacement, truth table, agreement or minimizer",
  "No fixed load-bearing checkpoint changes state",
  "40% proof estimate"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M255_COORDINATE) return;
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

test('M255 current summaries distinguish computed unary realization from complete-calculus and global completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_wire_unary_realization.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "One boundary input is the unary rule",
  "Full-word minimality is not ordinary-output-only minimality",
  "Whole-word gain is not proper-support Package E",
  "Runtime execution is test evidence, not theorem authority",
  "two unary valuations do not establish polynomial encoded runtime",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-13-computed-unary-full-word-realization.md'));
  assert.match(plan, /Publication decision: defer PNPLabs(?:[.,]|$)/u);
  if (progress.asOfCoordinate !== M255_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_wire_unary_realization.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
