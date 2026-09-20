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

const SOURCE = 'lean/PNP/NANDWireQuotientLift.lean';
const AUDIT = 'lean-audit/PNPWireQuotientLiftAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPWireQuotientLift.lean';
const NAMES = [
  "PNP.DirectWire.WireQuotientLift.expanded_reference",
  "PNP.DirectWire.WireQuotientLift.referenceLift_charge",
  "PNP.DirectWire.WireQuotientLift.expanded_charge",
  "PNP.DirectWire.WireQuotientLift.referenceLift_charge_difference",
  "PNP.DirectWire.WireQuotientLift.expanded_charge_difference",
  "PNP.DirectWire.WireQuotientLift.matched_materializer_charge",
  "PNP.DirectWire.WireQuotientLift.relative_saving_iff",
  "PNP.DirectWire.WireQuotientLift.original_gain_iff",
  "PNP.DirectWire.WireQuotientLift.expanded_output",
  "PNP.DirectWire.WireQuotientLift.expanded_kept_field",
  "PNP.DirectWire.WireQuotientLift.expanded_forgotten_field",
  "PNP.DirectWire.WireQuotientLift.expanded_field",
  "PNP.DirectWire.WireQuotientLift.expanded_equivalent",
  "PNP.DirectWire.WireQuotientLift.discharge_source_exact",
  "PNP.DirectWire.WireQuotientLift.discharge_full_value",
  "PNP.DirectWire.WireQuotientLift.checkedGain_isSome_iff",
  "PNP.DirectWire.WireQuotientLift.CheckedGain.checked"
];
const SIGNATURES = {
  "expanded_reference": "theorem expanded_reference (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : expanded carrier keep (WireObligationRestoration.projected carrier keep) = referenceLift carrier keep",
  "referenceLift_charge": "theorem referenceLift_charge (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : (referenceLift carrier keep).implementation.gateCount = (WireObligationRestoration.projected carrier keep).implementation.gateCount + charge carrier keep",
  "expanded_charge": "theorem expanded_charge (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) : (expanded carrier keep replacement).implementation.gateCount = replacement.implementation.gateCount + charge carrier keep",
  "referenceLift_charge_difference": "theorem referenceLift_charge_difference (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : ((referenceLift carrier keep).implementation.gateCount : Int) - (WireObligationRestoration.projected carrier keep).implementation.gateCount = charge carrier keep",
  "expanded_charge_difference": "theorem expanded_charge_difference (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) : ((expanded carrier keep replacement).implementation.gateCount : Int) - replacement.implementation.gateCount = charge carrier keep",
  "matched_materializer_charge": "theorem matched_materializer_charge (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) : ((referenceLift carrier keep).implementation.gateCount : Int) - (WireObligationRestoration.projected carrier keep).implementation.gateCount = ((expanded carrier keep replacement).implementation.gateCount : Int) - replacement.implementation.gateCount",
  "relative_saving_iff": "theorem relative_saving_iff (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) : (expanded carrier keep replacement).implementation.gateCount < (referenceLift carrier keep).implementation.gateCount ↔ replacement.implementation.gateCount < (WireObligationRestoration.projected carrier keep).implementation.gateCount",
  "original_gain_iff": "theorem original_gain_iff (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) : (expanded carrier keep replacement).implementation.gateCount < carrier.implementation.gateCount ↔ replacement.implementation.gateCount + charge carrier keep < carrier.implementation.gateCount",
  "expanded_output": "theorem expanded_output (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : QuotientAgreement carrier keep replacement) (valuation : Valuation inputs) (output : Fin outputs) : (expanded carrier keep replacement).implementation.candidate.semantics valuation output = carrier.implementation.candidate.semantics valuation output",
  "expanded_kept_field": "theorem expanded_kept_field (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : QuotientAgreement carrier keep replacement) (valuation : Valuation inputs) (field : Fin fields) (kept : keep field = true) : (expanded carrier keep replacement).fieldValue valuation field = carrier.fieldValue valuation field",
  "expanded_forgotten_field": "theorem expanded_forgotten_field (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (valuation : Valuation inputs) (field : Fin fields) (forgotten : keep field = false) : (expanded carrier keep replacement).fieldValue valuation field = carrier.fieldValue valuation field",
  "expanded_field": "theorem expanded_field (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : QuotientAgreement carrier keep replacement) (valuation : Valuation inputs) (field : Fin fields) : (expanded carrier keep replacement).fieldValue valuation field = carrier.fieldValue valuation field",
  "expanded_equivalent": "theorem expanded_equivalent (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : QuotientAgreement carrier keep replacement) : Equivalent (expanded carrier keep replacement).implementation.candidate.program (expanded carrier keep replacement).implementation.candidate.directWireWord carrier.implementation.candidate.program carrier.implementation.candidate.directWireWord",
  "discharge_source_exact": "theorem discharge_source_exact (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (creation : WireObligationRestoration.R5Creation carrier keep) : (discharge carrier keep replacement creation).actualSource = (expanded carrier keep replacement).source creation.coordinate",
  "discharge_full_value": "theorem discharge_full_value (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (creation : WireObligationRestoration.R5Creation carrier keep) (valuation : Valuation inputs) : (discharge carrier keep replacement creation).actualSource.eval valuation ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) = carrier.fieldValue valuation creation.coordinate",
  "checkedGain_isSome_iff": "theorem checkedGain_isSome_iff (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : QuotientAgreement carrier keep replacement) : (checkedGain carrier keep replacement same).isSome = true ↔ replacement.implementation.gateCount + charge carrier keep < carrier.implementation.gateCount",
  "CheckedGain.checked": "theorem CheckedGain.checked {carrier : WireCarrier inputs outputs fields} {keep : Fin fields → Bool} {replacement : WireCarrier inputs outputs fields} (gain : CheckedGain carrier keep replacement) : StrictEquivalentGain carrier.implementation (expanded carrier keep replacement).implementation ∧ (∀ valuation field, (expanded carrier keep replacement).fieldValue valuation field = carrier.fieldValue valuation field) ∧ (expanded carrier keep replacement).implementation.gateCount = replacement.implementation.gateCount + charge carrier keep"
};
const HEADS = [
  "QuotientAgreement",
  "charge",
  "referenceLift",
  "expanded",
  "referenceAgreement",
  "expanded_reference",
  "referenceLift_charge",
  "expanded_charge",
  "referenceLift_charge_difference",
  "expanded_charge_difference",
  "matched_materializer_charge",
  "relative_saving_iff",
  "original_gain_iff",
  "expanded_output",
  "expanded_kept_field",
  "expanded_forgotten_field",
  "expanded_field",
  "expanded_equivalent",
  "ExpandedDischarge",
  "discharge",
  "discharge_source_exact",
  "discharge_full_value",
  "CheckedGain",
  "checkedGain",
  "checkedGain_isSome_iff",
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
// A named argument's := is not the top-level theorem proof separator.
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
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|callerCertificate|suppliedObserver|suppliedTrace|suppliedMaterializer|suppliedResult)\b/u.test(clean),'shortcut-or-certificate');
  require0(!/\b(?:allCandidates|allBoolTuples|allSubsets|equivalentBool|referenceMinimumWitness|scanEquivalentSizes|referenceMinimum|terminalFullProfileMinimum)\b/u.test(clean),'no-semantic-enumeration');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]))===
    JSON.stringify(['PNP.NANDWireObligationRestoration']),'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name))===
    JSON.stringify(HEADS),'public-interface');
  require0(clean.includes('variable {inputs outputs fields : Nat}'),'unbounded-dimensions');
  for(const [name,signature] of Object.entries(SIGNATURES))
    require0(signature0(block(name))===signature,'signature:'+name);
  includes('QuotientAgreement',[
    ': Prop where output : ∀ valuation output, replacement.implementation.candidate.semantics valuation output = (WireObligationRestoration.projected carrier keep).implementation.candidate.semantics valuation output',
    'keptField : ∀ valuation field, keep field = true → replacement.fieldValue valuation field = (WireObligationRestoration.projected carrier keep).fieldValue valuation field',
  ],'complete-local-quotient-agreement');
  require0(block('charge').endsWith(
    '(WireObligationRestoration.materializer carrier keep).implementation.gateCount'),'actual-materializer-charge');
  require0(block('referenceLift').endsWith(
    'WireObligationRestoration.restored carrier keep'),'honest-reference-lift');
  require0(block('expanded').endsWith(
    'WireObligationRestoration.join replacement (WireObligationRestoration.materializer carrier keep) keep'),'literal-shared-materializer-lift');
  includes('ExpandedDischarge',[
    '(creation : WireObligationRestoration.R5Creation carrier keep)',
    'actualSource : Source inputs (expanded carrier keep replacement).implementation.gateCount',
    'sourceExact : actualSource = (expanded carrier keep replacement).source creation.coordinate',
    'fullWitness : ∀ valuation, actualSource.eval valuation ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) = creation.originalSource.eval valuation (carrier.implementation.candidate.program.eval valuation)',
  ],'original-and-expanded-source-binding');
  includes('discharge',[
    'actualSource := (expanded carrier keep replacement).source creation.coordinate',
    'sourceExact := rfl','rw [creation.sourceExact]',
    'exact expanded_forgotten_field carrier keep replacement valuation creation.coordinate creation.forgotten',
  ],'derived-expanded-full-discharge');
  includes('CheckedGain',[
    ': Type where agreement : QuotientAgreement carrier keep replacement',
    'smaller : (expanded carrier keep replacement).implementation.gateCount < carrier.implementation.gateCount',
  ],'local-agreement-and-original-strict-gain');
  includes('checkedGain',[
    '(same : QuotientAgreement carrier keep replacement)',
    'if smaller : (expanded carrier keep replacement).implementation.gateCount < carrier.implementation.gateCount then some { agreement := same, smaller := smaller } else none',
  ],'fully-paid-original-gain-test');
  includes('CheckedGain.strictGain',[
    'StrictEquivalentGain carrier.implementation (expanded carrier keep replacement).implementation',
    'smaller := gain.smaller',
    'equivalent := expanded_equivalent carrier keep replacement gain.agreement',
  ],'full-equivalent-gain');
  return [...new Set(failures)];
}

test('M252 computes a general quotient replacement lift with actual matched costs',async()=>{
  assert.deepEqual(validateSource0(await text0(SOURCE)),[]);
});

test('M252 root, exact theorem-name producers and axiom audit agree',async()=>{
  const [audit,inventorySource,root]=await Promise.all([
    text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean')]);
  for(const name of NAMES){
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item=>item===name).length,1,name);
    assert.equal(inventorySource.split(String.fromCharCode(96)+name+',').length-1,1,name);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),NAMES);
  assert.match(root,/^import PNP\.NANDWireQuotientLift\s*$/mu);
});

function rejectMutations0(source,mutations) {
  for(const [before,after,category] of mutations){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
}

test('M252 rejects omitted costs and confusing the lifted reference with the original',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['(WireObligationRestoration.materializer carrier keep).implementation.gateCount',
      '0','actual-materializer-charge'],
    ['WireObligationRestoration.restored carrier keep',
      'carrier','honest-reference-lift'],
    ['WireObligationRestoration.join replacement\n    (WireObligationRestoration.materializer carrier keep) keep',
      'replacement','literal-shared-materializer-lift'],
    ['replacement.implementation.gateCount + charge carrier keep := rfl',
      'replacement.implementation.gateCount := rfl','signature:expanded_charge'],
    ['(referenceLift carrier keep).implementation.gateCount ↔',
      'carrier.implementation.gateCount ↔','signature:relative_saving_iff'],
    ['if smaller : (expanded carrier keep replacement).implementation.gateCount <',
      'if smaller : replacement.implementation.gateCount <','fully-paid-original-gain-test'],
    ['carrier.implementation.gateCount then\n    some { agreement := same, smaller := smaller }',
      '(referenceLift carrier keep).implementation.gateCount then\n    some { agreement := same, smaller := smaller }',
      'fully-paid-original-gain-test'],
    ['theorem expanded_field (carrier : WireCarrier inputs outputs fields)',
      'theorem expanded_field (carrier : WireCarrier 2 outputs fields)','signature:expanded_field'],
    ['theorem expanded_output (carrier : WireCarrier inputs outputs fields)',
      'theorem expanded_output (callerCertificate : True) (carrier : WireCarrier inputs outputs fields)',
      'signature:expanded_output'],
  ]);
});

test('M252 rejects weakened quotient agreement and unbound or reference-only discharges',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['output : ∀ valuation output,','output : ∃ valuation output,','complete-local-quotient-agreement'],
    ['keptField : ∀ valuation field, keep field = true →',
      'keptField : ∀ valuation field, keep field = false →','complete-local-quotient-agreement'],
    ['sourceExact : actualSource = (expanded carrier keep replacement).source creation.coordinate',
      'sourceExact : True','original-and-expanded-source-binding'],
    ['fullWitness : ∀ valuation,','fullWitness : ∃ valuation,','original-and-expanded-source-binding'],
    ['actualSource := (expanded carrier keep replacement).source creation.coordinate',
      'actualSource := (referenceLift carrier keep).source creation.coordinate','derived-expanded-full-discharge'],
    ['exact expanded_forgotten_field carrier keep replacement valuation',
      'exact WireObligationRestoration.restored_field carrier keep valuation','derived-expanded-full-discharge'],
    ['agreement : QuotientAgreement carrier keep replacement',
      'agreement : True','local-agreement-and-original-strict-gain'],
    ['equivalent := expanded_equivalent carrier keep replacement gain.agreement',
      'equivalent := suppliedResult','full-equivalent-gain'],
    ['(same : QuotientAgreement carrier keep replacement)',
      '(same : True)','signature:expanded_field'],
  ]);
});

test('M252 rejects new assumptions, unaudited declarations and exhaustive semantic shortcuts',async()=>{
  const source=await text0(SOURCE);
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n').includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n').includes('unaudited-form'));
  assert.ok(validateSource0(source+'\ndef extra := referenceMinimum\n').includes('no-semantic-enumeration'));
  assert.ok(validateSource0(source.replace('import PNP.NANDWireObligationRestoration',
    'import PNP.NANDWireObligationRestoration\nimport Unknown.Source')).includes('closed-imports'));
});

test('M252 theorem-head parsing preserves dependent binders and dotted names',()=>{
  const declaration='theorem CheckedGain.checked (source : Carrier (fields := fields)) '+
    '(same : source = target) : target = source := same.symm';
  assert.equal(signature0(declaration),declaration.slice(0,declaration.lastIndexOf(' := ')));
  assert.equal(signature0(block0(declaration,'CheckedGain.checked')),signature0(declaration));
  assert.notEqual(signature0(declaration.replace('(same :','(extra : True) (same :')),
    signature0(declaration));
});

test('M252 regressions distinguish relative savings, fully paid gains and complete observations',async()=>{
  const raw=await text0(REGRESSION),regression=compact0(raw);
  assert.deepEqual([...raw.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  for(const token of [
    '¬QuotientAgreement noNetGain (fun _ => false) wrongOutput',
    '¬QuotientAgreement noNetGain (fun _ => true) (trueReplacement 1)',
    'expanded_field carrier keep replacement same valuation field',
    'matched_materializer_charge carrier keep replacement',
    'checkedGain_isSome_iff carrier keep replacement same',
    'quotient.implementation.gateCount != 2',
    'charge noNetGain (fun _ => false) != 2',
    'reference.implementation.gateCount != 4',
    'restored.implementation.gateCount != 2',
    '(checkedGain noNetGain (fun _ => false) (trueReplacement 1) noNetAgreement).isSome',
    'charge nonzeroSuccess (fun _ => false) != 1',
    'paid.implementation.gateCount != 1',
    '!(checkedGain nonzeroSuccess (fun _ => false) (trueReplacement 1) successAgreement).isSome',
    'charge shared (fun _ => false) != 1',
    'repeated.implementation.gateCount != 1',
    'charge noNetGain (fun _ => true) != 0',
    'charge freeFields freeKeep != 0',
    'only.implementation.gateCount != 1',
    'emptyResult.implementation.gateCount != 0',
    'discharge noNetGain (fun _ => false) (trueReplacement 1) creation',
    '(trueReplacement 1).fieldValue valuation 0 != false',
    'restored.fieldValue valuation 0 != true',
    'witness.actualSource.eval valuation (restored.implementation.candidate.program.eval valuation) != true',
    'repeated.fieldValue valuation 1 != !value',
    'free.fieldValue valuation 3 != true',
    '#eval show IO Unit from do','throw (IO.userError',
  ])assert.ok(regression.includes(token),token);
  assert.equal([...raw.matchAll(/^#eval\b/gmu)].length,1);
  assert.doesNotMatch(regression,/\b(?:sorry|admit|native_decide|Classical|referenceMinimum|scanEquivalentSizes|allCandidates)\b/u);
});

test('M252 durable workflow retains source checks, exact audit and bounded regressions',async()=>{
  const [packageText,surface,verifier,workflow]=await Promise.all([
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),text0('.github/workflows/lean-bridge.yml')]);
  const auditPath='audits/lean-wire-quotient-lift0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m252'],'node --test '+auditPath);
  assert.ok(surface.includes("'audit:m252': 'node --test "+auditPath+"'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test '+auditPath));
  for(const path of [auditPath,'docs/lean_wire_quotient_lift.md'])
    assertLeanWorkflowPathCoverage0(workflow, path);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M252_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-12-252';
const M252_MILESTONE = 'wire-quotient-lift';
const M252_HASHES = Object.freeze({
  "PNP.DirectWire.WireQuotientLift.expanded_reference": "dad34b516523dd4761eed9fe0e51f4ea277af7b09f47963376a231f88769b9cd",
  "PNP.DirectWire.WireQuotientLift.referenceLift_charge": "8ef5fa5a1c3f72b8696d60b96ef30bf041e06d6e0118eddbd369e9724eff784e",
  "PNP.DirectWire.WireQuotientLift.expanded_charge": "2c390754add81c66fce0e7f06d9645887fe99f409f56ba5017ff019de0bddafe",
  "PNP.DirectWire.WireQuotientLift.referenceLift_charge_difference": "161d81be5eddf99fbe120d07fe2e28283f4f1ab98ea1f44bfca25d8008074f7c",
  "PNP.DirectWire.WireQuotientLift.expanded_charge_difference": "20cc0581c6b78bc09932db012b163951a02c5e74a768868d168ee7798d9ca5e7",
  "PNP.DirectWire.WireQuotientLift.matched_materializer_charge": "c406464ebafae4e77738d6900db05342b1eb36847dd4c16a949349a336dceba7",
  "PNP.DirectWire.WireQuotientLift.relative_saving_iff": "f01eace00b52eeaabe4b5144a8d72ae541387ecd4d6aa29b4e7b93ce11d96be8",
  "PNP.DirectWire.WireQuotientLift.original_gain_iff": "cd38b27471456bec443545e4111706f83a73acfeadc512c9bde1ceb01f6e4ff5",
  "PNP.DirectWire.WireQuotientLift.expanded_output": "e56816eefc3ae363d597a4f30f061a13912dbbfcc6bbbcdc7c563680de9264b6",
  "PNP.DirectWire.WireQuotientLift.expanded_kept_field": "68f9c76da6c2c6180c8093c20d9e72ad9e718ddd3bc5b632cfbb1624ba946969",
  "PNP.DirectWire.WireQuotientLift.expanded_forgotten_field": "1f311380a7b47553cc0b7c9e271589f1cb34ea176ae44f84850935604aff7191",
  "PNP.DirectWire.WireQuotientLift.expanded_field": "ad7fd204b29e8141d7942bfbed034296c89b8aea9996e92d2e915e6e8326c0af",
  "PNP.DirectWire.WireQuotientLift.expanded_equivalent": "39f297948af422b3a8643984303c0773bcea23dc75a1a4b834f31245346d6da1",
  "PNP.DirectWire.WireQuotientLift.discharge_source_exact": "4f253f28d63c4ef390842de5ec99c84a819d2fa3e69b0f67ecaecb5ac7d4547f",
  "PNP.DirectWire.WireQuotientLift.discharge_full_value": "7b121a128cf884fcad0435492949da493316ec268b54a558c1c5c89ff3745677",
  "PNP.DirectWire.WireQuotientLift.checkedGain_isSome_iff": "79cbe56d948918e2995435dee395b44858bc98bd351f66b8a341479318d7db93",
  "PNP.DirectWire.WireQuotientLift.CheckedGain.checked": "61ca863d7794e9ce01dd17ac5f76237d0c0d0019009f62d3c07decfe4f977fd7"
});
const M252_STATUS_FIELDS = Object.freeze({
  "leanWireQuotientLiftFormalized": true,
  "leanWireQuotientLiftAxiomAuditPassed": true,
  "leanWireQuotientLiftAuditedDeclarationCount": 17,
  "leanWireQuotientLiftExpandedReferenceTheorem": "PNP.DirectWire.WireQuotientLift.expanded_reference",
  "leanWireQuotientLiftReferenceChargeTheorem": "PNP.DirectWire.WireQuotientLift.referenceLift_charge",
  "leanWireQuotientLiftExpandedChargeTheorem": "PNP.DirectWire.WireQuotientLift.expanded_charge",
  "leanWireQuotientLiftReferenceChargeDifferenceTheorem": "PNP.DirectWire.WireQuotientLift.referenceLift_charge_difference",
  "leanWireQuotientLiftExpandedChargeDifferenceTheorem": "PNP.DirectWire.WireQuotientLift.expanded_charge_difference",
  "leanWireQuotientLiftMatchedMaterializerChargeTheorem": "PNP.DirectWire.WireQuotientLift.matched_materializer_charge",
  "leanWireQuotientLiftRelativeSavingIffTheorem": "PNP.DirectWire.WireQuotientLift.relative_saving_iff",
  "leanWireQuotientLiftOriginalGainIffTheorem": "PNP.DirectWire.WireQuotientLift.original_gain_iff",
  "leanWireQuotientLiftExpandedOutputTheorem": "PNP.DirectWire.WireQuotientLift.expanded_output",
  "leanWireQuotientLiftExpandedKeptFieldTheorem": "PNP.DirectWire.WireQuotientLift.expanded_kept_field",
  "leanWireQuotientLiftExpandedForgottenFieldTheorem": "PNP.DirectWire.WireQuotientLift.expanded_forgotten_field",
  "leanWireQuotientLiftExpandedFieldTheorem": "PNP.DirectWire.WireQuotientLift.expanded_field",
  "leanWireQuotientLiftExpandedEquivalenceTheorem": "PNP.DirectWire.WireQuotientLift.expanded_equivalent",
  "leanWireQuotientLiftDischargeSourceExactTheorem": "PNP.DirectWire.WireQuotientLift.discharge_source_exact",
  "leanWireQuotientLiftDischargeFullValueTheorem": "PNP.DirectWire.WireQuotientLift.discharge_full_value",
  "leanWireQuotientLiftGainIffTheorem": "PNP.DirectWire.WireQuotientLift.checkedGain_isSome_iff",
  "leanWireQuotientLiftCheckedGainTheorem": "PNP.DirectWire.WireQuotientLift.CheckedGain.checked",
  "leanWireQuotientLiftFullManuscriptPullExpandProved": false,
  "leanWireQuotientLiftReferenceLiftIdentifiedWithOriginal": false,
  "leanWireQuotientLiftAutomaticQuotientAgreementDerived": false,
  "leanWireQuotientLiftCompleteObligationCalculusProved": false,
  "leanWireQuotientLiftCompletePackageEProved": false,
  "leanWireQuotientLiftPolynomialRuntimeProved": false,
  "leanWireQuotientLiftScope": "all-finite-computational-wire-quotient-compatible-replacements-literal-shared-materializer-full-value-lift-exact-matched-integer-charges-original-cost-gain-test-expanded-source-bound-discharge-no-arbitrary-support-embedding-or-polynomial-runtime"
});
const M252_AXIOMS = Object.freeze({
  "PNP.DirectWire.WireQuotientLift.expanded_reference": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireQuotientLift.referenceLift_charge": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireQuotientLift.expanded_charge": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireQuotientLift.referenceLift_charge_difference": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireQuotientLift.expanded_charge_difference": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireQuotientLift.matched_materializer_charge": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireQuotientLift.relative_saving_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireQuotientLift.original_gain_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireQuotientLift.expanded_output": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireQuotientLift.expanded_kept_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireQuotientLift.expanded_forgotten_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireQuotientLift.expanded_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireQuotientLift.expanded_equivalent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireQuotientLift.discharge_source_exact": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireQuotientLift.discharge_full_value": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireQuotientLift.checkedGain_isSome_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireQuotientLift.CheckedGain.checked": [
    "Quot.sound",
    "propext"
  ]
});

const M252_MODULES = Object.freeze({
  "PNP.DirectWire.WireQuotientLift.expanded_reference": "PNP.NANDWireQuotientLift",
  "PNP.DirectWire.WireQuotientLift.referenceLift_charge": "PNP.NANDWireQuotientLift",
  "PNP.DirectWire.WireQuotientLift.expanded_charge": "PNP.NANDWireQuotientLift",
  "PNP.DirectWire.WireQuotientLift.referenceLift_charge_difference": "PNP.NANDWireQuotientLift",
  "PNP.DirectWire.WireQuotientLift.expanded_charge_difference": "PNP.NANDWireQuotientLift",
  "PNP.DirectWire.WireQuotientLift.matched_materializer_charge": "PNP.NANDWireQuotientLift",
  "PNP.DirectWire.WireQuotientLift.relative_saving_iff": "PNP.NANDWireQuotientLift",
  "PNP.DirectWire.WireQuotientLift.original_gain_iff": "PNP.NANDWireQuotientLift",
  "PNP.DirectWire.WireQuotientLift.expanded_output": "PNP.NANDWireQuotientLift",
  "PNP.DirectWire.WireQuotientLift.expanded_kept_field": "PNP.NANDWireQuotientLift",
  "PNP.DirectWire.WireQuotientLift.expanded_forgotten_field": "PNP.NANDWireQuotientLift",
  "PNP.DirectWire.WireQuotientLift.expanded_field": "PNP.NANDWireQuotientLift",
  "PNP.DirectWire.WireQuotientLift.expanded_equivalent": "PNP.NANDWireQuotientLift",
  "PNP.DirectWire.WireQuotientLift.discharge_source_exact": "PNP.NANDWireQuotientLift",
  "PNP.DirectWire.WireQuotientLift.discharge_full_value": "PNP.NANDWireQuotientLift",
  "PNP.DirectWire.WireQuotientLift.checkedGain_isSome_iff": "PNP.NANDWireQuotientLift",
  "PNP.DirectWire.WireQuotientLift.CheckedGain.checked": "PNP.NANDWireQuotientLift"
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

test('M252 compiled quotient replacement lift interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M252_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M252_COORDINATE)
    assert.equal(map.coordinate, M252_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M252_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, M252_MODULES[name], name);
      assert.deepEqual(declaration.axioms, M252_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M252_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M252_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M252_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "computational word-level quotient lift",
  "not arbitrary-support Pull/Expand",
  "local quotient agreement are inputs",
  "lifted reference can exceed the original gate count",
  "relative saving can leave no original gain",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M252 publication rejects weakened, supplied, assumption-backed and widened full-support-lift substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M252_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M252_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = 'PNP.DirectWire.WireQuotientLift.expanded_field';
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M252_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M252_MILESTONE
    ? {...row, nonClaim:'The quotient lift proves full arbitrary-support embedding, the complete obligation calculus and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M252 adds word-level lift coverage without full-support, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M252_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "word-level local quotient replacement",
  "actual expanded full-value sources",
  "does not supply arbitrary-support embedding",
  "No fixed load-bearing checkpoint changes state",
  "40% proof estimate"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M252_COORDINATE) return;
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

test('M252 current summaries distinguish word-level replacement lifting from full-support and global completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_wire_quotient_lift.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "computational word-level lift",
  "local quotient agreement is a premise",
  "not arbitrary-support Pull/Expand",
  "reference lift can exceed the original",
  "relative saving is not necessarily an original-circuit gain",
  "Runtime execution is test evidence, not theorem authority",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-12-computed-quotient-replacement-lift.md'));
  assert.match(plan, /Publication decision: defer PNPLabs(?:[.,]|$)/u);
  if (progress.asOfCoordinate !== M252_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_wire_quotient_lift.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
