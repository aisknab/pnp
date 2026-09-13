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

const SOURCE = 'lean/PNP/NANDWireUnaryFrontier.lean';
const AUDIT = 'lean-audit/PNPWireUnaryFrontierAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPWireUnaryFrontier.lean';
const NAMES = [
  "PNP.DirectWire.WireUnaryFrontier.constantWord_value",
  "PNP.DirectWire.WireUnaryFrontier.constantWord_gateCount",
  "PNP.DirectWire.WireUnaryFrontier.unaryWord_value",
  "PNP.DirectWire.WireUnaryFrontier.unaryWord_minimal",
  "PNP.DirectWire.WireUnaryFrontier.unaryWord_gate_bound",
  "PNP.DirectWire.WireUnaryFrontier.localWord_value",
  "PNP.DirectWire.WireUnaryFrontier.localWord_minimal",
  "PNP.DirectWire.WireUnaryFrontier.localWord_nonincrease",
  "PNP.DirectWire.WireUnaryFrontier.localWord_gate_bound",
  "PNP.DirectWire.WireUnaryFrontier.replacement_agreement",
  "PNP.DirectWire.WireUnaryFrontier.replacement_minimal",
  "PNP.DirectWire.WireUnaryFrontier.replacement_nonincrease",
  "PNP.DirectWire.WireUnaryFrontier.replacement_gate_bound",
  "PNP.DirectWire.WireUnaryFrontier.replacement_zero_gateCount",
  "PNP.DirectWire.WireUnaryFrontier.expanded_output",
  "PNP.DirectWire.WireUnaryFrontier.expanded_field",
  "PNP.DirectWire.WireUnaryFrontier.expanded_equivalent",
  "PNP.DirectWire.WireUnaryFrontier.expanded_charge",
  "PNP.DirectWire.WireUnaryFrontier.expanded_nonincrease",
  "PNP.DirectWire.WireUnaryFrontier.expanded_gain_iff",
  "PNP.DirectWire.WireUnaryFrontier.attempt_isSome_iff",
  "PNP.DirectWire.WireUnaryFrontier.attempt_output",
  "PNP.DirectWire.WireUnaryFrontier.attempt_field",
  "PNP.DirectWire.WireUnaryFrontier.attempt_nonincrease",
  "PNP.DirectWire.WireUnaryFrontier.attempt_charge",
  "PNP.DirectWire.WireUnaryFrontier.dischargeR7_source_exact",
  "PNP.DirectWire.WireUnaryFrontier.dischargeR7_full_value",
  "PNP.DirectWire.WireUnaryFrontier.checkedProperGain_isSome_iff",
  "PNP.DirectWire.WireUnaryFrontier.checkedProperGain_complete",
  "PNP.DirectWire.WireUnaryFrontier.ProperGain.checked"
];
const SIGNATURES = {
  "constantWord_value": "theorem constantWord_value (original : Implementation 0 width) (valuation : Valuation 0) (output : Fin width) : (constantWord original).candidate.semantics valuation output = original.candidate.semantics valuation output",
  "constantWord_gateCount": "theorem constantWord_gateCount (original : Implementation 0 width) : (constantWord original).gateCount = 0",
  "unaryWord_value": "theorem unaryWord_value (original : Implementation 1 width) (valuation : Valuation 1) (output : Fin width) : (unaryWord original).candidate.semantics valuation output = original.candidate.semantics valuation output",
  "unaryWord_minimal": "theorem unaryWord_minimal (original other : Implementation 1 width) (sameOpen : Equivalent other.candidate.program other.candidate.directWireWord original.candidate.program original.candidate.directWireWord) : (unaryWord original).gateCount ≤ other.gateCount",
  "unaryWord_gate_bound": "theorem unaryWord_gate_bound (original : Implementation 1 width) : (unaryWord original).gateCount ≤ 1",
  "localWord_value": "theorem localWord_value (original : Implementation inputs width) (small : inputs ≤ 1) (valuation : Valuation inputs) (output : Fin width) : (localWord original small).candidate.semantics valuation output = original.candidate.semantics valuation output",
  "localWord_minimal": "theorem localWord_minimal (original other : Implementation inputs width) (small : inputs ≤ 1) (sameOpen : Equivalent other.candidate.program other.candidate.directWireWord original.candidate.program original.candidate.directWireWord) : (localWord original small).gateCount ≤ other.gateCount",
  "localWord_nonincrease": "theorem localWord_nonincrease (original : Implementation inputs width) (small : inputs ≤ 1) : (localWord original small).gateCount ≤ original.gateCount",
  "localWord_gate_bound": "theorem localWord_gate_bound (original : Implementation inputs width) (small : inputs ≤ 1) : (localWord original small).gateCount ≤ 1",
  "replacement_agreement": "theorem replacement_agreement (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) : (replacement carrier keep small).candidate.semantics = (WireFrontierLift.pulled carrier keep).extractedCandidate.semantics",
  "replacement_minimal": "theorem replacement_minimal (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) (other : Implementation (WireFrontierLift.pulled carrier keep).boundary.length (WireFrontierLift.pulled carrier keep).interface.length) (sameOpen : other.candidate.semantics = (WireFrontierLift.pulled carrier keep).extractedCandidate.semantics) : (replacement carrier keep small).gateCount ≤ other.gateCount",
  "replacement_nonincrease": "theorem replacement_nonincrease (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) : (replacement carrier keep small).gateCount ≤ (WireFrontierLift.pulled carrier keep).gateCount",
  "replacement_gate_bound": "theorem replacement_gate_bound (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) : (replacement carrier keep small).gateCount ≤ 1",
  "replacement_zero_gateCount": "theorem replacement_zero_gateCount (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) (zero : (WireFrontierLift.pulled carrier keep).boundary.length = 0) : (replacement carrier keep small).gateCount = 0",
  "expanded_output": "theorem expanded_output (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) (valuation : Valuation inputs) (output : Fin outputs) : (expanded carrier keep small).implementation.candidate.semantics valuation output = carrier.implementation.candidate.semantics valuation output",
  "expanded_field": "theorem expanded_field (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) (valuation : Valuation inputs) (field : Fin fields) : (expanded carrier keep small).fieldValue valuation field = carrier.fieldValue valuation field",
  "expanded_equivalent": "theorem expanded_equivalent (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) : Equivalent (expanded carrier keep small).implementation.candidate.program (expanded carrier keep small).implementation.candidate.directWireWord carrier.implementation.candidate.program carrier.implementation.candidate.directWireWord",
  "expanded_charge": "theorem expanded_charge (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) : (expanded carrier keep small).implementation.gateCount = (replacement carrier keep small).gateCount + WireFrontierLift.exteriorCharge carrier keep",
  "expanded_nonincrease": "theorem expanded_nonincrease (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) : (expanded carrier keep small).implementation.gateCount ≤ carrier.implementation.gateCount",
  "expanded_gain_iff": "theorem expanded_gain_iff (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) : (expanded carrier keep small).implementation.gateCount < carrier.implementation.gateCount ↔ (replacement carrier keep small).gateCount < (WireFrontierLift.pulled carrier keep).gateCount",
  "attempt_isSome_iff": "theorem attempt_isSome_iff (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : (attempt carrier keep).isSome = true ↔ (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1",
  "attempt_output": "theorem attempt_output (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (result : WireCarrier inputs outputs fields) (accepted : attempt carrier keep = some result) (valuation : Valuation inputs) (output : Fin outputs) : result.implementation.candidate.semantics valuation output = carrier.implementation.candidate.semantics valuation output",
  "attempt_field": "theorem attempt_field (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (result : WireCarrier inputs outputs fields) (accepted : attempt carrier keep = some result) (valuation : Valuation inputs) (field : Fin fields) : result.fieldValue valuation field = carrier.fieldValue valuation field",
  "attempt_nonincrease": "theorem attempt_nonincrease (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (result : WireCarrier inputs outputs fields) (accepted : attempt carrier keep = some result) : result.implementation.gateCount ≤ carrier.implementation.gateCount",
  "attempt_charge": "theorem attempt_charge (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (result : WireCarrier inputs outputs fields) (accepted : attempt carrier keep = some result) : ∃ small, result.implementation.gateCount = (replacement carrier keep small).gateCount + WireFrontierLift.exteriorCharge carrier keep",
  "dischargeR7_source_exact": "theorem dischargeR7_source_exact (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) (creation : WireObligationRestoration.R5Creation carrier keep) : (dischargeR7 carrier keep small creation).actualSource = (expanded carrier keep small).source creation.coordinate",
  "dischargeR7_full_value": "theorem dischargeR7_full_value (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) (creation : WireObligationRestoration.R5Creation carrier keep) (valuation : Valuation inputs) : (dischargeR7 carrier keep small creation).actualSource.eval valuation ((expanded carrier keep small).implementation.candidate.program.eval valuation) = carrier.fieldValue valuation creation.coordinate",
  "checkedProperGain_isSome_iff": "theorem checkedProperGain_isSome_iff (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : (checkedProperGain carrier keep).isSome = true ↔ ∃ small, 0 < WireFrontierLift.exteriorCharge carrier keep ∧ (replacement carrier keep small).gateCount < (WireFrontierLift.pulled carrier keep).gateCount",
  "checkedProperGain_complete": "theorem checkedProperGain_complete (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) (proper : 0 < WireFrontierLift.exteriorCharge carrier keep) (other : Implementation (WireFrontierLift.pulled carrier keep).boundary.length (WireFrontierLift.pulled carrier keep).interface.length) (sameOpen : other.candidate.semantics = (WireFrontierLift.pulled carrier keep).extractedCandidate.semantics) (smaller : other.gateCount < (WireFrontierLift.pulled carrier keep).gateCount) : (checkedProperGain carrier keep).isSome = true",
  "ProperGain.checked": "theorem ProperGain.checked {carrier : WireCarrier inputs outputs fields} {keep : Fin fields → Bool} (gain : ProperGain carrier keep) : (WireFrontierLift.pulled carrier keep).gateCount < carrier.implementation.gateCount ∧ StrictEquivalentGain carrier.implementation (expanded carrier keep gain.small).implementation ∧ (∀ valuation field, (expanded carrier keep gain.small).fieldValue valuation field = carrier.fieldValue valuation field) ∧ (expanded carrier keep gain.small).implementation.gateCount = (replacement carrier keep gain.small).gateCount + WireFrontierLift.exteriorCharge carrier keep"
};
const HEADS = [
  "constantWord",
  "constantWord_value",
  "constantWord_gateCount",
  "unaryCarrier",
  "unaryWord",
  "unaryWord_value",
  "unaryWord_minimal",
  "unaryWord_gate_bound",
  "localWord",
  "localWord_value",
  "localWord_minimal",
  "localWord_nonincrease",
  "localWord_gate_bound",
  "replacement",
  "replacement_agreement",
  "replacement_minimal",
  "replacement_nonincrease",
  "replacement_gate_bound",
  "replacement_zero_gateCount",
  "expanded",
  "expanded_output",
  "expanded_field",
  "expanded_equivalent",
  "expanded_charge",
  "expanded_nonincrease",
  "expanded_gain_iff",
  "attempt",
  "attempt_isSome_iff",
  "attempt_output",
  "attempt_field",
  "attempt_nonincrease",
  "attempt_charge",
  "dischargeR7",
  "dischargeR7_source_exact",
  "dischargeR7_full_value",
  "ProperGain",
  "checkedProperGain",
  "checkedProperGain_isSome_iff",
  "checkedProperGain_complete",
  "ProperGain.strictGain",
  "ProperGain.checked"
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
    JSON.stringify(['PNP.NANDWireFrontierLift','PNP.NANDWireUnaryRealization']),'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name))===
    JSON.stringify(HEADS),'public-interface');
  require0(clean.includes('variable {inputs outputs fields width : Nat}'),'unbounded-ambient-dimensions');
  for(const [name,signature] of Object.entries(SIGNATURES))
    require0(signature0(block(name))===signature,'signature:'+name);
  includes('constantWord',[
    '(Candidate.ofDirectWireWord (.empty : Program 0 0)',
    'fun output => .constant (original.candidate.semantics Fin.elim0 output)',
  ],'source-derived-constant-word');
  require0(block('unaryCarrier')===
    'def unaryCarrier (original : Implementation 1 width) : WireCarrier 1 width 0 := WireCarrier.unpack original',
    'complete-frontier-as-unary-word');
  require0(block('unaryWord')===
    'def unaryWord (original : Implementation 1 width) : Implementation 1 width := (WireUnaryRealization.realize (unaryCarrier original)).implementation',
    'actual-shared-unary-constructor');
  includes('localWord',[
    'def localWord : {inputs : Nat} → Implementation inputs width → inputs ≤ 1 → Implementation inputs width',
    '| 0, original, _small => constantWord original',
    '| 1, original, _small => unaryWord original',
    '| _ + 2, _original, impossible => False.elim (by omega)',
  ],'checked-zero-unary-dimension-transport');
  require0(block('replacement').endsWith(
    'localWord (WireFrontierLift.pulled carrier keep).extractedCandidate.toImplementation small'),
    'actual-pulled-complete-source');
  includes('replacement_agreement',[
    'funext fun valuation => funext fun output => localWord_value _ small valuation output',
  ],'derived-all-open-valuations');
  require0(block('expanded')===
    'def expanded (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1) : WireCarrier inputs outputs fields := WireFrontierLift.expanded carrier keep (replacement carrier keep small).candidate',
    'actual-input-derived-compiler');
  includes('expanded_field',[
    'WireFrontierLift.expanded_field carrier keep _ (replacement_agreement carrier keep small) valuation field',
  ],'derived-full-field-preservation');
  require0(block('attempt')===
    'def attempt (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : Option (WireCarrier inputs outputs fields) := if small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1 then some (expanded carrier keep small) else none',
    'computed-boundary-only-query');
  includes('dischargeR7',[
    'WireFrontierLift.ExpandedDischarge carrier keep (replacement carrier keep small).candidate creation',
    'WireFrontierLift.discharge carrier keep _ (replacement_agreement carrier keep small) creation',
  ],'derived-source-bound-r7');
  includes('ProperGain',[
    'small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1',
    'proper : 0 < WireFrontierLift.exteriorCharge carrier keep',
    'smaller : (replacement carrier keep small).gateCount < (WireFrontierLift.pulled carrier keep).gateCount',
  ],'physical-proper-gain');
  includes('checkedProperGain',[
    'if small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1 then',
    'if proper : 0 < WireFrontierLift.exteriorCharge carrier keep then',
    'if smaller : (replacement carrier keep small).gateCount < (WireFrontierLift.pulled carrier keep).gateCount then',
    'some ⟨small, proper, smaller⟩',
  ],'computed-proper-gain');
  return [...new Set(failures)];
}

test('M256 derives the complete constant or unary frontier and actual ambient replacement',async()=>{
  assert.deepEqual(validateSource0(await text0(SOURCE)),[]);
});

test('M256 root, exact theorem-name producers and axiom audit agree',async()=>{
  const [audit,inventorySource,root]=await Promise.all([
    text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean')]);
  for(const name of NAMES){
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item=>item===name).length,1,name);
    assert.equal(inventorySource.split(String.fromCharCode(96)+name+',').length-1,1,name);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),NAMES);
  assert.match(root,/^import PNP\.NANDWireUnaryFrontier\s*$/mu);
});

function rejectMutations0(source,mutations) {
  for(const [before,after,category] of mutations){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
}

test('M256 rejects supplied replacements, incomplete words and substituted compiler results',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['fun output => .constant (original.candidate.semantics Fin.elim0 output)',
      'fun output => .constant (suppliedTable output)','source-derived-constant-word'],
    ['WireCarrier.unpack original','WireCarrier.unpack suppliedResult','complete-frontier-as-unary-word'],
    ['(WireUnaryRealization.realize (unaryCarrier original)).implementation',
      'suppliedResult','actual-shared-unary-constructor'],
    ['localWord (WireFrontierLift.pulled carrier keep).extractedCandidate.toImplementation small',
      'localWord suppliedResult small','actual-pulled-complete-source'],
    ['WireFrontierLift.expanded carrier keep (replacement carrier keep small).candidate',
      'suppliedResult','actual-input-derived-compiler'],
  ]);
});

test('M256 rejects wrong input dimensions, extra query certificates and multiboundary acceptance',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['variable {inputs outputs fields width : Nat}','variable {outputs fields width : Nat}',
      'unbounded-ambient-dimensions'],
    ['| 1, original, _small => unaryWord original','| 1, original, _small => constantWord original',
      'checked-zero-unary-dimension-transport'],
    ['def attempt (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)',
      'def attempt (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (callerCertificate : True)',
      'computed-boundary-only-query'],
    ['if small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1 then',
      'if small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 2 then',
      'computed-boundary-only-query'],
    ['theorem attempt_field (carrier : WireCarrier inputs outputs fields)',
      'theorem attempt_field (carrier : WireCarrier 1 outputs fields)','signature:attempt_field'],
  ]);
});

test('M256 rejects quotient-only fields, supplied agreement and duplicated exterior charge',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['funext fun valuation => funext fun output =>','funext fun output =>','derived-all-open-valuations'],
    ['(replacement_agreement carrier keep small) valuation field',
      'callerCertificate valuation field','derived-full-field-preservation'],
    ['result.fieldValue valuation field = carrier.fieldValue valuation field',
      'result.fieldValue valuation field = (WireObligationRestoration.masked carrier keep).fieldValue valuation field',
      'signature:attempt_field'],
    ['(replacement carrier keep small).gateCount +\n        WireFrontierLift.exteriorCharge carrier keep',
      '(replacement carrier keep small).gateCount +\n        2 * WireFrontierLift.exteriorCharge carrier keep',
      'signature:expanded_charge'],
  ]);
});

test('M256 rejects ordinary-only minima, reversed bounds and unbound R7 witnesses',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['(sameOpen : other.candidate.semantics =\n      (WireFrontierLift.pulled carrier keep).extractedCandidate.semantics)',
      '(sameOpen : True)','signature:replacement_minimal'],
    ['(replacement carrier keep small).gateCount ≤ other.gateCount',
      'other.gateCount ≤ (replacement carrier keep small).gateCount','signature:replacement_minimal'],
    ['WireFrontierLift.discharge carrier keep _ (replacement_agreement carrier keep small) creation',
      'WireFrontierLift.discharge carrier keep _ callerCertificate creation','derived-source-bound-r7'],
    ['(expanded carrier keep small).source creation.coordinate := rfl',
      '(expanded carrier keep small).source 0 := rfl','signature:dischargeR7_source_exact'],
    ['carrier.fieldValue valuation creation.coordinate :=\n  WireFrontierLift.discharge_full_value',
      '(WireObligationRestoration.masked carrier keep).fieldValue valuation creation.coordinate :=\n  WireFrontierLift.discharge_full_value',
      'signature:dischargeR7_full_value'],
  ]);
});

test('M256 rejects whole-support credit, nonstrict gains and weakened checked values',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['proper : 0 < WireFrontierLift.exteriorCharge carrier keep',
      'proper : 0 ≤ WireFrontierLift.exteriorCharge carrier keep','physical-proper-gain'],
    ['if smaller : (replacement carrier keep small).gateCount <',
      'if smaller : (replacement carrier keep small).gateCount ≤','computed-proper-gain'],
    ['(∀ valuation field, (expanded carrier keep gain.small).fieldValue valuation field =',
      '(∃ valuation field, (expanded carrier keep gain.small).fieldValue valuation field =',
      'signature:ProperGain.checked'],
  ]);
});

test('M256 rejects assumptions, unaudited forms and exhaustive implementation search',async()=>{
  const source=await text0(SOURCE);
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n').includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n').includes('unaudited-form'));
  assert.ok(validateSource0(source+'\ndef extra := referenceMinimum\n').includes('no-implementation-enumeration'));
  assert.ok(validateSource0(source.replace('import PNP.NANDWireFrontierLift',
    'import PNP.NANDWireFrontierLift\nimport Unknown.Source')).includes('closed-imports'));
});

test('M256 theorem signatures retain dependent binders and dotted interface names',()=>{
  const declaration='theorem ProperGain.checked (source : Carrier (fields := fields)) '+
    '(same : source = target) : target = source := same.symm';
  assert.equal(signature0(declaration),declaration.slice(0,declaration.lastIndexOf(' := ')));
  assert.equal(signature0(block0(declaration,'ProperGain.checked')),signature0(declaration));
});

test('M256 regressions guard nonzero input binding, complete fields and genuine proper savings',async()=>{
  const clean=compact0(await text0(REGRESSION));
  for(const name of ['properCarrier','hiddenNegation','repeated','constantCarrier','twoBoundary',
    'wholeCarrier','minimalCarrier','freeFields','fieldsOnly','empty'])
    assert.match(clean,new RegExp('\\b'+name+'\\b','u'),name);
  for(const token of ['inputs > 3 || outputs > 4 || fields > 5',
    'for mask in List.range (2 ^ inputs) do','for field in allFin fields do',
    'if witness.actualSource ≠ built.source field then','if index.val != 2 then',
    'result.source 1 ≠ result.source 3','throw (IO.userError',
    'checkFixture hiddenNegation dropAll 1 2 1 (some 1) (some 2) true',
    'checkFixture constantCarrier dropAll 0 1 1 (some 0) (some 1) true',
    'checkFixture wholeCarrier dropAll 1 2 0 (some 0) (some 0) false',
    'checkFixture twoBoundary dropAll 2 1 0 none none false'])
    assert.ok(clean.includes(token),token);
  assert.ok(!/\b(?:native_decide|sorry|admit)\b/u.test(clean));
});

const M256_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-13-256';
const M256_MILESTONE = 'wire-unary-frontier';
const M256_HASHES = Object.freeze({
  "PNP.DirectWire.WireUnaryFrontier.constantWord_value": "582c6c6da7e892847079603a2c1e999c56485675a943444c8b3ce863e41d5129",
  "PNP.DirectWire.WireUnaryFrontier.constantWord_gateCount": "02c30022268edc2f89c7ebdffe570f0d212a3dd21b63a796cacab6f49d47ef93",
  "PNP.DirectWire.WireUnaryFrontier.unaryWord_value": "095947adf6640b07f3284119fff23335824743c4e75f2adeebc1b070e5ebcff6",
  "PNP.DirectWire.WireUnaryFrontier.unaryWord_minimal": "9644515dbe2ccf8a8021425df0f39167e4cf22a038a1c2ad8c126011ba303796",
  "PNP.DirectWire.WireUnaryFrontier.unaryWord_gate_bound": "195c48ead6423dd5bcfc9bc200792004fab15abee61174b71b96ccace8529123",
  "PNP.DirectWire.WireUnaryFrontier.localWord_value": "bcdc116ead3fb88e37f646a064753ec35b5e3b1178a8df46dcc945e7cd7763ed",
  "PNP.DirectWire.WireUnaryFrontier.localWord_minimal": "9de87539b360cf8c0040e5d4768a2a55e97383687ca2414022916c4cc9a22183",
  "PNP.DirectWire.WireUnaryFrontier.localWord_nonincrease": "7a06ee455f9fad686535a2a5f4d8112080bf2c6baf994721eba3a74c8a69dc9a",
  "PNP.DirectWire.WireUnaryFrontier.localWord_gate_bound": "bf005c2e94935b87a0cd21dd610ddffc40623f6b3da8ef76b52df09d8747ad6e",
  "PNP.DirectWire.WireUnaryFrontier.replacement_agreement": "5a6ce39f55892427c9cfe2ece32206a856269003ea4bda810911bb5ab85893ef",
  "PNP.DirectWire.WireUnaryFrontier.replacement_minimal": "1ade002576afaf298c69d90c456ef5dcf632df1b05becd67531e1907e5ac02c2",
  "PNP.DirectWire.WireUnaryFrontier.replacement_nonincrease": "4b11aeb29500651f8c1dc09bb581bafc090f2a9acb51791ce3f64cc279c422f1",
  "PNP.DirectWire.WireUnaryFrontier.replacement_gate_bound": "aaae4b28519807c79aa38af67108af95ec1bc30e1d969f9e188cf8052afe1ab2",
  "PNP.DirectWire.WireUnaryFrontier.replacement_zero_gateCount": "e2777f23b123d0c48b7d0e42400e6014da1a9ffce5dc4995999854bdd58ee444",
  "PNP.DirectWire.WireUnaryFrontier.expanded_output": "7cf73ecff68ca9b077e40aa7dcbc504d02075a7a5211bcac5c57f54119209508",
  "PNP.DirectWire.WireUnaryFrontier.expanded_field": "c0ed63d53076dbe42cfcaffee3b4eb437882a597efeed79fb4fd4228c35fcc09",
  "PNP.DirectWire.WireUnaryFrontier.expanded_equivalent": "91e8aa94ca777f69bd55519d8edbdae015ac8145d978483c41aacb841ce420ab",
  "PNP.DirectWire.WireUnaryFrontier.expanded_charge": "3a064a55c067237139602b7293bc814d9502dd3f1da2fafc0cb523205816f24b",
  "PNP.DirectWire.WireUnaryFrontier.expanded_nonincrease": "aaedf60953e5cc274403a301d8dac0a256d840eb2bc45d5bad6c8953cb1336fa",
  "PNP.DirectWire.WireUnaryFrontier.expanded_gain_iff": "e5649fb91a1558e9051e72261560f136d0a2b2de40c1aa84f336f7882688de95",
  "PNP.DirectWire.WireUnaryFrontier.attempt_isSome_iff": "2ae8fcec0f69a026cb3401b20e819003fb80aae5a8fe31293aeeabdc60c659ea",
  "PNP.DirectWire.WireUnaryFrontier.attempt_output": "43115671e93b1bf19c367b8f8eb3a97ea31037b8a53666824101be7777d5124a",
  "PNP.DirectWire.WireUnaryFrontier.attempt_field": "55dc6f57b5361080f99936d93b325868b463b8c9269e90ab42e9e953f831bf21",
  "PNP.DirectWire.WireUnaryFrontier.attempt_nonincrease": "daa30772b0fb2b3c92d3772f171487a7644122cb8dd63618b857b24d3f49e521",
  "PNP.DirectWire.WireUnaryFrontier.attempt_charge": "c13da7ce02b9d415ce896effe5b499a9b2249bede31138071b8f3c162e851519",
  "PNP.DirectWire.WireUnaryFrontier.dischargeR7_source_exact": "07674631131aa34ff0ec625e1c1955d34fbeb54da913b397adb298da6cabaa40",
  "PNP.DirectWire.WireUnaryFrontier.dischargeR7_full_value": "b15b4a349ce8c1670d63d9cb844eedac3b76cd855e18f328cd95782a6c5618c8",
  "PNP.DirectWire.WireUnaryFrontier.checkedProperGain_isSome_iff": "a985b9427b18b7dd80fc8b442e23d5931780297c0743d36f051e3fafc0760769",
  "PNP.DirectWire.WireUnaryFrontier.checkedProperGain_complete": "b3a94c1864f51e3aa6295526c3435ad710721875c202426d39e40562b44a488f",
  "PNP.DirectWire.WireUnaryFrontier.ProperGain.checked": "27dfb2128a2da21e7d2b104627b9e7860979c1f3332580f7ac52e1db64948521"
});
const M256_STATUS_FIELDS = Object.freeze({
  "leanWireUnaryFrontierFormalized": true,
  "leanWireUnaryFrontierAxiomAuditPassed": true,
  "leanWireUnaryFrontierAuditedDeclarationCount": 30,
  "leanWireUnaryFrontierConstantValueTheorem": "PNP.DirectWire.WireUnaryFrontier.constantWord_value",
  "leanWireUnaryFrontierConstantGateCountTheorem": "PNP.DirectWire.WireUnaryFrontier.constantWord_gateCount",
  "leanWireUnaryFrontierUnaryValueTheorem": "PNP.DirectWire.WireUnaryFrontier.unaryWord_value",
  "leanWireUnaryFrontierUnaryMinimumTheorem": "PNP.DirectWire.WireUnaryFrontier.unaryWord_minimal",
  "leanWireUnaryFrontierUnaryGateBoundTheorem": "PNP.DirectWire.WireUnaryFrontier.unaryWord_gate_bound",
  "leanWireUnaryFrontierLocalValueTheorem": "PNP.DirectWire.WireUnaryFrontier.localWord_value",
  "leanWireUnaryFrontierLocalMinimumTheorem": "PNP.DirectWire.WireUnaryFrontier.localWord_minimal",
  "leanWireUnaryFrontierLocalNonincreaseTheorem": "PNP.DirectWire.WireUnaryFrontier.localWord_nonincrease",
  "leanWireUnaryFrontierLocalGateBoundTheorem": "PNP.DirectWire.WireUnaryFrontier.localWord_gate_bound",
  "leanWireUnaryFrontierReplacementAgreementTheorem": "PNP.DirectWire.WireUnaryFrontier.replacement_agreement",
  "leanWireUnaryFrontierReplacementMinimumTheorem": "PNP.DirectWire.WireUnaryFrontier.replacement_minimal",
  "leanWireUnaryFrontierReplacementNonincreaseTheorem": "PNP.DirectWire.WireUnaryFrontier.replacement_nonincrease",
  "leanWireUnaryFrontierReplacementGateBoundTheorem": "PNP.DirectWire.WireUnaryFrontier.replacement_gate_bound",
  "leanWireUnaryFrontierZeroBoundaryGateCountTheorem": "PNP.DirectWire.WireUnaryFrontier.replacement_zero_gateCount",
  "leanWireUnaryFrontierOutputTheorem": "PNP.DirectWire.WireUnaryFrontier.expanded_output",
  "leanWireUnaryFrontierFieldTheorem": "PNP.DirectWire.WireUnaryFrontier.expanded_field",
  "leanWireUnaryFrontierEquivalenceTheorem": "PNP.DirectWire.WireUnaryFrontier.expanded_equivalent",
  "leanWireUnaryFrontierExactChargeTheorem": "PNP.DirectWire.WireUnaryFrontier.expanded_charge",
  "leanWireUnaryFrontierNonincreaseTheorem": "PNP.DirectWire.WireUnaryFrontier.expanded_nonincrease",
  "leanWireUnaryFrontierGainIffTheorem": "PNP.DirectWire.WireUnaryFrontier.expanded_gain_iff",
  "leanWireUnaryFrontierAttemptIffTheorem": "PNP.DirectWire.WireUnaryFrontier.attempt_isSome_iff",
  "leanWireUnaryFrontierAttemptOutputTheorem": "PNP.DirectWire.WireUnaryFrontier.attempt_output",
  "leanWireUnaryFrontierAttemptFieldTheorem": "PNP.DirectWire.WireUnaryFrontier.attempt_field",
  "leanWireUnaryFrontierAttemptNonincreaseTheorem": "PNP.DirectWire.WireUnaryFrontier.attempt_nonincrease",
  "leanWireUnaryFrontierAttemptChargeTheorem": "PNP.DirectWire.WireUnaryFrontier.attempt_charge",
  "leanWireUnaryFrontierR7SourceExactTheorem": "PNP.DirectWire.WireUnaryFrontier.dischargeR7_source_exact",
  "leanWireUnaryFrontierR7FullValueTheorem": "PNP.DirectWire.WireUnaryFrontier.dischargeR7_full_value",
  "leanWireUnaryFrontierProperGainIffTheorem": "PNP.DirectWire.WireUnaryFrontier.checkedProperGain_isSome_iff",
  "leanWireUnaryFrontierProperGainCompletenessTheorem": "PNP.DirectWire.WireUnaryFrontier.checkedProperGain_complete",
  "leanWireUnaryFrontierCheckedProperGainTheorem": "PNP.DirectWire.WireUnaryFrontier.ProperGain.checked",
  "leanWireUnaryFrontierArbitraryAmbientCutsCovered": false,
  "leanWireUnaryFrontierAllR7CasesDerived": false,
  "leanWireUnaryFrontierArbitraryObligationDAGsCovered": false,
  "leanWireUnaryFrontierFullManuscriptCarrierProved": false,
  "leanWireUnaryFrontierCompleteObligationCalculusProved": false,
  "leanWireUnaryFrontierCompletePackageEProved": false,
  "leanWireUnaryFrontierPolynomialRuntimeProved": false,
  "leanWireUnaryFrontierScope": "all-finite-computational-wire-source-derived-visible-predecessor-cone-completed-frontier-zero-or-one-primary-boundary-computed-minimum-local-word-actual-original-exterior-once-full-field-preservation-source-exact-r7-proper-strict-gain-no-arbitrary-support-calculus-or-polynomial-runtime"
});
const M256_AXIOMS = Object.freeze({
  "PNP.DirectWire.WireUnaryFrontier.constantWord_value": [
    "Quot.sound"
  ],
  "PNP.DirectWire.WireUnaryFrontier.constantWord_gateCount": [],
  "PNP.DirectWire.WireUnaryFrontier.unaryWord_value": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.unaryWord_minimal": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.unaryWord_gate_bound": [],
  "PNP.DirectWire.WireUnaryFrontier.localWord_value": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.localWord_minimal": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.localWord_nonincrease": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.localWord_gate_bound": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.replacement_agreement": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.replacement_minimal": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.replacement_nonincrease": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.replacement_gate_bound": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.replacement_zero_gateCount": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.expanded_output": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.expanded_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.expanded_equivalent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.expanded_charge": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.expanded_nonincrease": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.expanded_gain_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.attempt_isSome_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.attempt_output": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.attempt_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.attempt_nonincrease": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.attempt_charge": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.dischargeR7_source_exact": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.dischargeR7_full_value": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.checkedProperGain_isSome_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.checkedProperGain_complete": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryFrontier.ProperGain.checked": [
    "Quot.sound",
    "propext"
  ]
});

const M256_MODULES = Object.freeze({
  "PNP.DirectWire.WireUnaryFrontier.constantWord_value": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.constantWord_gateCount": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.unaryWord_value": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.unaryWord_minimal": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.unaryWord_gate_bound": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.localWord_value": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.localWord_minimal": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.localWord_nonincrease": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.localWord_gate_bound": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.replacement_agreement": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.replacement_minimal": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.replacement_nonincrease": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.replacement_gate_bound": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.replacement_zero_gateCount": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.expanded_output": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.expanded_field": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.expanded_equivalent": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.expanded_charge": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.expanded_nonincrease": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.expanded_gain_iff": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.attempt_isSome_iff": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.attempt_output": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.attempt_field": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.attempt_nonincrease": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.attempt_charge": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.dischargeR7_source_exact": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.dischargeR7_full_value": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.checkedProperGain_isSome_iff": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.checkedProperGain_complete": "PNP.NANDWireUnaryFrontier",
  "PNP.DirectWire.WireUnaryFrontier.ProperGain.checked": "PNP.NANDWireUnaryFrontier"
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

test('M256 compiled unary frontier replacement interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M256_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M256_COORDINATE)
    assert.equal(map.coordinate, M256_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M256_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, M256_MODULES[name], name);
      assert.deepEqual(declaration.axioms, M256_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M256_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M256_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M256_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "not every arbitrary ambient support",
  "not all ambient circuits with different exteriors",
  "whole-support saving is not a proper-support Package E certificate",
  "not encoded-size polynomial runtime theorems",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M256 publication rejects weakened, supplied, assumption-backed and widened complete-calculus substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M256_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M256_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = 'PNP.DirectWire.WireUnaryFrontier.attempt_field';
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M256_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M256_MILESTONE
    ? {...row, nonClaim:'The unary frontier replacement proves every ambient support, the complete obligation calculus and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M256 adds computed unary frontier coverage without complete-calculus, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M256_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "constant/unary R7 frontier step",
  "proved rather than supplied",
  "positive original exterior and strict local saving",
  "No fixed load-bearing checkpoint changes state",
  "40% proof estimate"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M256_COORDINATE) return;
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

test('M256 current summaries distinguish computed unary frontier replacement from complete-calculus and global completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_wire_unary_frontier.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "Every recognized frontier compiles.",
  "local full-frontier minimality, not ordinary-output-only agreement",
  "Whole-support saving",
  "Runtime execution is test evidence, not theorem authority",
  "Publication decision: defer PNPLabs."
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-13-computed-unary-frontier-replacement.md'));
  assert.match(plan, /Publication decision: defer PNPLabs(?:[.,]|$)/u);
  if (progress.asOfCoordinate !== M256_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_wire_unary_frontier.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
