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

const SOURCE = 'lean/PNP/NANDWireFrontierLift.lean';
const AUDIT = 'lean-audit/PNPWireFrontierLiftAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPWireFrontierLift.lean';
const NAMES = [
  "PNP.DirectWire.WireFrontierLift.ordinary_output_selected",
  "PNP.DirectWire.WireFrontierLift.kept_field_selected",
  "PNP.DirectWire.WireFrontierLift.records_predecessor_closed",
  "PNP.DirectWire.WireFrontierLift.selected_field_in_frontier",
  "PNP.DirectWire.WireFrontierLift.primary_boundary",
  "PNP.DirectWire.WireFrontierLift.original_charge",
  "PNP.DirectWire.WireFrontierLift.compile_isSome",
  "PNP.DirectWire.WireFrontierLift.expanded_charge",
  "PNP.DirectWire.WireFrontierLift.matched_original_charge",
  "PNP.DirectWire.WireFrontierLift.original_gain_iff",
  "PNP.DirectWire.WireFrontierLift.expanded_output",
  "PNP.DirectWire.WireFrontierLift.expanded_field",
  "PNP.DirectWire.WireFrontierLift.expanded_equivalent",
  "PNP.DirectWire.WireFrontierLift.discharge_source_exact",
  "PNP.DirectWire.WireFrontierLift.discharge_full_value",
  "PNP.DirectWire.WireFrontierLift.proper_iff_exterior_positive",
  "PNP.DirectWire.WireFrontierLift.checkedProperGain_isSome_iff",
  "PNP.DirectWire.WireFrontierLift.ProperGain.checked"
];
const SIGNATURES = {
  "ordinary_output_selected": "theorem ordinary_output_selected (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (output : Fin outputs) (producer : Fin carrier.implementation.gateCount) (sourceAt : carrier.implementation.candidate.directWireWord.source output = .gate producer) : TerminalPrimitiveRecord.gate producer ∈ records carrier keep",
  "kept_field_selected": "theorem kept_field_selected (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (field : Fin fields) (kept : keep field = true) (producer : Fin carrier.implementation.gateCount) (sourceAt : carrier.source field = .gate producer) : TerminalPrimitiveRecord.gate producer ∈ records carrier keep",
  "records_predecessor_closed": "theorem records_predecessor_closed (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (consumer producer : Fin carrier.implementation.gateCount) (selected : TerminalPrimitiveRecord.gate consumer ∈ records carrier keep) (uses : carrier.implementation.candidate.program.terminalGateUsesWire consumer (.gate producer) = true) : TerminalPrimitiveRecord.gate producer ∈ records carrier keep",
  "selected_field_in_frontier": "theorem selected_field_in_frontier (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (field : Fin fields) (producer : Fin carrier.implementation.gateCount) (sourceAt : carrier.source field = .gate producer) (selected : terminalGateSelected (records carrier keep) producer = true) : producer ∈ (pulled carrier keep).interface",
  "primary_boundary": "theorem primary_boundary (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : ArbitrarySupportSplice.PrimaryBoundary carrier.exposed.candidate (records carrier keep)",
  "original_charge": "theorem original_charge (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : carrier.implementation.gateCount = (pulled carrier keep).gateCount + exteriorCharge carrier keep",
  "compile_isSome": "theorem compile_isSome (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : Candidate (pulled carrier keep).boundary.length replacementGates (pulled carrier keep).interface.length) : (ArbitrarySupportSplice.compile carrier.exposed.candidate (records carrier keep) replacement).isSome = true",
  "expanded_charge": "theorem expanded_charge (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : Candidate (pulled carrier keep).boundary.length replacementGates (pulled carrier keep).interface.length) : (expanded carrier keep replacement).implementation.gateCount = replacementGates + exteriorCharge carrier keep",
  "matched_original_charge": "theorem matched_original_charge (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : Candidate (pulled carrier keep).boundary.length replacementGates (pulled carrier keep).interface.length) : (carrier.implementation.gateCount : Int) - (pulled carrier keep).gateCount = ((expanded carrier keep replacement).implementation.gateCount : Int) - replacementGates",
  "original_gain_iff": "theorem original_gain_iff (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : Candidate (pulled carrier keep).boundary.length replacementGates (pulled carrier keep).interface.length) : (expanded carrier keep replacement).implementation.gateCount < carrier.implementation.gateCount ↔ replacementGates < (pulled carrier keep).gateCount",
  "expanded_output": "theorem expanded_output (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : Candidate (pulled carrier keep).boundary.length replacementGates (pulled carrier keep).interface.length) (sameOpen : replacement.semantics = (pulled carrier keep).extractedCandidate.semantics) (valuation : Valuation inputs) (output : Fin outputs) : (expanded carrier keep replacement).implementation.candidate.semantics valuation output = carrier.implementation.candidate.semantics valuation output",
  "expanded_field": "theorem expanded_field (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : Candidate (pulled carrier keep).boundary.length replacementGates (pulled carrier keep).interface.length) (sameOpen : replacement.semantics = (pulled carrier keep).extractedCandidate.semantics) (valuation : Valuation inputs) (field : Fin fields) : (expanded carrier keep replacement).fieldValue valuation field = carrier.fieldValue valuation field",
  "expanded_equivalent": "theorem expanded_equivalent (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : Candidate (pulled carrier keep).boundary.length replacementGates (pulled carrier keep).interface.length) (sameOpen : replacement.semantics = (pulled carrier keep).extractedCandidate.semantics) : Equivalent (expanded carrier keep replacement).implementation.candidate.program (expanded carrier keep replacement).implementation.candidate.directWireWord carrier.implementation.candidate.program carrier.implementation.candidate.directWireWord",
  "discharge_source_exact": "theorem discharge_source_exact (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : Candidate (pulled carrier keep).boundary.length replacementGates (pulled carrier keep).interface.length) (sameOpen : replacement.semantics = (pulled carrier keep).extractedCandidate.semantics) (creation : WireObligationRestoration.R5Creation carrier keep) : (discharge carrier keep replacement sameOpen creation).actualSource = (expanded carrier keep replacement).source creation.coordinate",
  "discharge_full_value": "theorem discharge_full_value (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : Candidate (pulled carrier keep).boundary.length replacementGates (pulled carrier keep).interface.length) (sameOpen : replacement.semantics = (pulled carrier keep).extractedCandidate.semantics) (creation : WireObligationRestoration.R5Creation carrier keep) (valuation : Valuation inputs) : (discharge carrier keep replacement sameOpen creation).actualSource.eval valuation ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) = carrier.fieldValue valuation creation.coordinate",
  "proper_iff_exterior_positive": "theorem proper_iff_exterior_positive (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : (pulled carrier keep).gateCount < carrier.implementation.gateCount ↔ 0 < exteriorCharge carrier keep",
  "checkedProperGain_isSome_iff": "theorem checkedProperGain_isSome_iff (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : Candidate (pulled carrier keep).boundary.length replacementGates (pulled carrier keep).interface.length) (sameOpen : replacement.semantics = (pulled carrier keep).extractedCandidate.semantics) : (checkedProperGain carrier keep replacement sameOpen).isSome = true ↔ (pulled carrier keep).gateCount < carrier.implementation.gateCount ∧ replacementGates < (pulled carrier keep).gateCount",
  "ProperGain.checked": "theorem ProperGain.checked {carrier : WireCarrier inputs outputs fields} {keep : Fin fields → Bool} {replacement : Candidate (pulled carrier keep).boundary.length replacementGates (pulled carrier keep).interface.length} (gain : ProperGain carrier keep replacement) : (pulled carrier keep).gateCount < carrier.implementation.gateCount ∧ StrictEquivalentGain carrier.implementation (expanded carrier keep replacement).implementation ∧ (∀ valuation field, (expanded carrier keep replacement).fieldValue valuation field = carrier.fieldValue valuation field) ∧ (expanded carrier keep replacement).implementation.gateCount = replacementGates + exteriorCharge carrier keep"
};
const HEADS = [
  "records",
  "pulled",
  "exteriorCharge",
  "ordinary_output_selected",
  "kept_field_selected",
  "records_predecessor_closed",
  "selected_field_in_frontier",
  "primary_boundary",
  "original_charge",
  "compile_isSome",
  "compiled",
  "expanded",
  "expanded_charge",
  "matched_original_charge",
  "original_gain_iff",
  "expanded_output",
  "expanded_field",
  "expanded_equivalent",
  "ExpandedDischarge",
  "discharge",
  "discharge_source_exact",
  "discharge_full_value",
  "proper_iff_exterior_positive",
  "ProperGain",
  "checkedProperGain",
  "checkedProperGain_isSome_iff",
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
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|callerCertificate|suppliedSupport|suppliedOrder|suppliedWeight|suppliedResult)\b/u.test(clean),'shortcut-or-certificate');
  require0(!/\b(?:allCandidates|allBoolTuples|allSubsets|equivalentBool|referenceMinimumWitness|scanEquivalentSizes|referenceMinimum|terminalFullProfileMinimum)\b/u.test(clean),'no-semantic-enumeration');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]))===
    JSON.stringify(['PNP.NANDWireQuotientLift']),'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name))===
    JSON.stringify(HEADS),'public-interface');
  require0(clean.includes('variable {inputs outputs fields : Nat}') &&
    clean.includes('variable {replacementGates : Nat}'),'unbounded-dimensions');
  for(const [name,signature] of Object.entries(SIGNATURES))
    require0(signature0(block(name))===signature,'signature:'+name);
  require0(block('records').endsWith(
    'outputConeRecords (WireObligationRestoration.masked carrier keep).exposed.candidate'),
    'input-derived-visible-cone');
  require0(block('pulled').endsWith(
    'extractTerminalSupport carrier.exposed.candidate (records carrier keep)'),
    'complete-original-frontier');
  require0(block('exteriorCharge').endsWith(
    '(ArbitrarySupportSplice.exterior (records carrier keep)).length'),
    'actual-original-exterior-charge');
  includes('primary_boundary',[
    'cases wire with',
    'outputConeRecords_noExternalGate (WireObligationRestoration.masked carrier keep).exposed.candidate producer',
  ],'derived-primary-boundary');
  includes('compile_isSome',[
    'ArbitrarySupportSplice.compile_success_iff',
    'ArbitrarySupportSplice.graph_wellFounded_of_primaryBoundary',
    '(primary_boundary carrier keep)',
  ],'derived-compiler-success');
  require0(block('compiled').endsWith(
    '(ArbitrarySupportSplice.compile carrier.exposed.candidate (records carrier keep) replacement).get (compile_isSome carrier keep replacement)'),
    'actual-compiler-result');
  require0(block('expanded').endsWith(
    'carrier.spliceResult (records carrier keep) replacement (compiled carrier keep replacement)'),
    'original-exterior-substitution');
  includes('ExpandedDischarge',[
    '(creation : WireObligationRestoration.R5Creation carrier keep)',
    'actualSource : Source inputs (expanded carrier keep replacement).implementation.gateCount',
    'sourceExact : actualSource = (expanded carrier keep replacement).source creation.coordinate',
    'fullWitness : ∀ valuation, actualSource.eval valuation ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) = creation.originalSource.eval valuation (carrier.implementation.candidate.program.eval valuation)',
  ],'original-and-expanded-source-binding');
  includes('discharge',[
    '(sameOpen : replacement.semantics = (pulled carrier keep).extractedCandidate.semantics)',
    'actualSource := (expanded carrier keep replacement).source creation.coordinate',
    'sourceExact := rfl','rw [creation.sourceExact]',
    'exact expanded_field carrier keep replacement sameOpen valuation creation.coordinate',
  ],'derived-full-frontier-discharge');
  includes('ProperGain',[
    ': Type where agreement : replacement.semantics = (pulled carrier keep).extractedCandidate.semantics',
    'proper : (pulled carrier keep).gateCount < carrier.implementation.gateCount',
    'smaller : replacementGates < (pulled carrier keep).gateCount',
  ],'full-agreement-properness-and-saving');
  includes('checkedProperGain',[
    'if proper : (pulled carrier keep).gateCount < carrier.implementation.gateCount then',
    'if smaller : replacementGates < (pulled carrier keep).gateCount then',
    'some { agreement := sameOpen, proper := proper, smaller := smaller } else none else none',
  ],'two-actual-strict-tests');
  includes('ProperGain.strictGain',[
    'StrictEquivalentGain carrier.implementation (expanded carrier keep replacement).implementation',
    'smaller := (original_gain_iff carrier keep replacement).2 gain.smaller',
    'equivalent := expanded_equivalent carrier keep replacement gain.agreement',
  ],'actual-original-equivalent-gain');
  return [...new Set(failures)];
}

test('M253 computes an input-derived frontier lift charged against the actual original',async()=>{
  assert.deepEqual(validateSource0(await text0(SOURCE)),[]);
});

test('M253 root, exact theorem-name producers and axiom audit agree',async()=>{
  const [audit,inventorySource,root]=await Promise.all([
    text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean')]);
  for(const name of NAMES){
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item=>item===name).length,1,name);
    assert.equal(inventorySource.split(String.fromCharCode(96)+name+',').length-1,1,name);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),NAMES);
  assert.match(root,/^import PNP\.NANDWireFrontierLift\s*$/mu);
});

function rejectMutations0(source,mutations) {
  for(const [before,after,category] of mutations){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
}

test('M253 rejects supplied cones, duplicated charges and reference-only accounting',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['outputConeRecords (WireObligationRestoration.masked carrier keep).exposed.candidate',
      '[]','input-derived-visible-cone'],
    ['extractTerminalSupport carrier.exposed.candidate (records carrier keep)',
      'extractTerminalSupport (WireObligationRestoration.masked carrier keep).exposed.candidate (records carrier keep)',
      'complete-original-frontier'],
    ['(ArbitrarySupportSplice.exterior (records carrier keep)).length',
      '0','actual-original-exterior-charge'],
    ['replacementGates + exteriorCharge carrier keep := by',
      'replacementGates + 2 * exteriorCharge carrier keep := by','signature:expanded_charge'],
    ['(carrier.implementation.gateCount : Int) - (pulled carrier keep).gateCount',
      '((WireQuotientLift.referenceLift carrier keep).implementation.gateCount : Int) - (pulled carrier keep).gateCount',
      'signature:matched_original_charge'],
    ['(records carrier keep) replacement).get (compile_isSome carrier keep replacement)',
      '(records carrier keep) replacement).get suppliedResult','actual-compiler-result'],
    ['(ArbitrarySupportSplice.graph_wellFounded_of_primaryBoundary',
      '(suppliedOrder','derived-compiler-success'],
    ['carrier.spliceResult (records carrier keep) replacement (compiled carrier keep replacement)',
      'carrier','original-exterior-substitution'],
    ['theorem expanded_field (carrier : WireCarrier inputs outputs fields)',
      'theorem expanded_field (carrier : WireCarrier 2 outputs fields)','signature:expanded_field'],
  ]);
});

test('M253 rejects weak frontier agreement, improper gains and unbound full discharges',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['(sameOpen : replacement.semantics =\n      (pulled carrier keep).extractedCandidate.semantics)',
      '(sameOpen : True)','signature:expanded_field'],
    ['agreement : replacement.semantics = (pulled carrier keep).extractedCandidate.semantics',
      'agreement : True','full-agreement-properness-and-saving'],
    ['if proper : (pulled carrier keep).gateCount < carrier.implementation.gateCount then',
      'if proper : (pulled carrier keep).gateCount ≤ carrier.implementation.gateCount then',
      'two-actual-strict-tests'],
    ['if smaller : replacementGates < (pulled carrier keep).gateCount then',
      'if smaller : replacementGates ≤ (pulled carrier keep).gateCount then',
      'two-actual-strict-tests'],
    ['sourceExact : actualSource = (expanded carrier keep replacement).source creation.coordinate',
      'sourceExact : True','original-and-expanded-source-binding'],
    ['fullWitness : ∀ valuation,','fullWitness : ∃ valuation,','original-and-expanded-source-binding'],
    ['exact expanded_field carrier keep replacement sameOpen valuation creation.coordinate',
      'exact suppliedResult','derived-full-frontier-discharge'],
    ['equivalent := expanded_equivalent carrier keep replacement gain.agreement',
      'equivalent := suppliedResult','actual-original-equivalent-gain'],
  ]);
});

test('M253 rejects assumptions, unaudited forms and exhaustive semantic shortcuts',async()=>{
  const source=await text0(SOURCE);
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n').includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n').includes('unaudited-form'));
  assert.ok(validateSource0(source+'\ndef extra := referenceMinimum\n').includes('no-semantic-enumeration'));
  assert.ok(validateSource0(source.replace('import PNP.NANDWireQuotientLift',
    'import PNP.NANDWireQuotientLift\nimport Unknown.Source')).includes('closed-imports'));
});

test('M253 theorem signatures preserve dependent binders and dotted names',()=>{
  const declaration='theorem ProperGain.checked (source : Carrier (fields := fields)) '+
    '(same : source = target) : target = source := same.symm';
  assert.equal(signature0(declaration),declaration.slice(0,declaration.lastIndexOf(' := ')));
  assert.equal(signature0(block0(declaration,'ProperGain.checked')),signature0(declaration));
  assert.notEqual(signature0(declaration.replace('(same :','(extra : True) (same :')),
    signature0(declaration));
});

test('M253 regressions distinguish proper, whole-support and wrong-frontier replacements',async()=>{
  const raw=await text0(REGRESSION),regression=compact0(raw);
  assert.deepEqual([...raw.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  for(const token of [
    '¬(wrongFrontier.semantics = (pulled frontierCarrier (fun _ => false)).extractedCandidate.semantics)',
    '(pulled properCarrier (fun _ => false)).interface.map Fin.val = [1]',
    '(pulled frontierCarrier (fun _ => false)).interface.map Fin.val = [0, 1]',
    'expanded_field carrier keep replacement sameOpen valuation field',
    'matched_original_charge carrier keep replacement',
    'checkedProperGain_isSome_iff carrier keep replacement sameOpen',
    'support.gateCount != 2',
    'exteriorCharge properCarrier (fun _ => false) != 1',
    'saved.implementation.gateCount != 1',
    '!(checkedProperGain properCarrier (fun _ => false) properReplacement properAgreement).isSome',
    '(checkedProperGain properCarrier (fun _ => false) support.extractedCandidate rfl).isSome',
    'whole.implementation.gateCount != 0',
    '(checkedProperGain wholeCarrier (fun _ => false) wholeReplacement wholeAgreement).isSome',
    'keptSupport.gateCount != 3',
    'repeatedSupport.gateCount != 2',
    'repeatedResult.implementation.gateCount != 3',
    'free.implementation.gateCount != 0',
    '(pulled fieldsOnly (fun _ => false)).gateCount != 0',
    'exteriorCharge fieldsOnly (fun _ => false) != 1',
    'only.implementation.gateCount != 1',
    'emptyResult.implementation.gateCount != 0',
    'discharge properCarrier (fun _ => false) properReplacement properAgreement creation',
    'saved.fieldValue valuation 1 != !value',
    'witness.actualSource.eval valuation (saved.implementation.candidate.program.eval valuation) != true',
    '[!value, true, !value, true]',
    '[value, false, value, true]',
    '#eval show IO Unit from do','throw (IO.userError',
  ])assert.ok(regression.includes(token),token);
  assert.equal([...raw.matchAll(/^#eval\b/gmu)].length,1);
  assert.doesNotMatch(regression,/\b(?:sorry|admit|native_decide|Classical|referenceMinimum|scanEquivalentSizes|allCandidates)\b/u);
  assert.doesNotMatch(raw,/#eval!/u);
});

test('M253 durable workflow retains source checks, exact audit and bounded regressions',async()=>{
  const [packageText,surface,verifier,workflow]=await Promise.all([
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),text0('.github/workflows/lean-bridge.yml')]);
  const auditPath='audits/lean-wire-frontier-lift0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m253'],'node --test '+auditPath);
  assert.ok(surface.includes("'audit:m253': 'node --test "+auditPath+"'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test '+auditPath));
  for(const path of [auditPath,'docs/lean_wire_frontier_lift.md'])
    assert.equal(workflow.split("      - '"+path+"'").length-1,2);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M253_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-12-253';
const M253_MILESTONE = 'wire-frontier-lift';
const M253_HASHES = Object.freeze({
  "PNP.DirectWire.WireFrontierLift.ordinary_output_selected": "8931e68e92d35b11528e401a2794cd957f15aa680c3fc0d403792565c3877b60",
  "PNP.DirectWire.WireFrontierLift.kept_field_selected": "f1e883390878267faaeb4e079fe8a8e6b1beaa818ee6289321b290e4569fd7a3",
  "PNP.DirectWire.WireFrontierLift.records_predecessor_closed": "aaac754e3944140d3f9ab991fe42cc844199ca686b2df52f3853c289f980dc22",
  "PNP.DirectWire.WireFrontierLift.selected_field_in_frontier": "4562d68496b552354fc79fa2203f76209b5c82152af04989e379d7661041e2c6",
  "PNP.DirectWire.WireFrontierLift.primary_boundary": "5f646ed8a46cd2fa78f3546ae15d17d10c7885b90c986df52e58dfd81c92bacd",
  "PNP.DirectWire.WireFrontierLift.original_charge": "4eb5b3b2bea74fa2ef8f74430443fcf91703578efaa7c5bd240750acab1fe673",
  "PNP.DirectWire.WireFrontierLift.compile_isSome": "c7c54aca037e1809f3dc247e6b2fdd8400610a8534d0c13421fd92b7e1a68e9f",
  "PNP.DirectWire.WireFrontierLift.expanded_charge": "e1cd44f5181734485e18c9715033158ca360b888eda0f51e70b366d77760e88a",
  "PNP.DirectWire.WireFrontierLift.matched_original_charge": "3a44ac86b851eae886ec1c90d7f6a70b18873d9c25053910cf09fdd27c27b16a",
  "PNP.DirectWire.WireFrontierLift.original_gain_iff": "2f4fcc36271b2b7ccbc96c064df4296c60498f617f0e9a7b0335a2f727ce584b",
  "PNP.DirectWire.WireFrontierLift.expanded_output": "bf326f0b42446e9c7acb8321afdbba90d86db4221d2a49b46ab390dc6fdf82af",
  "PNP.DirectWire.WireFrontierLift.expanded_field": "d44019f1b34aea6e5192f1121e790d79176267f1a59f0a6d69153e4a38061378",
  "PNP.DirectWire.WireFrontierLift.expanded_equivalent": "71984fb9b72d71ad9ea78dd7d83d517064e2ec2a8f911fb1508962c71627c0ba",
  "PNP.DirectWire.WireFrontierLift.discharge_source_exact": "5648f9e263315b547073b009e005fbeb0dc23065179daa94744fabe0068bb945",
  "PNP.DirectWire.WireFrontierLift.discharge_full_value": "5f76bac96ea0779b49d2e6c7db6cdc3f3d6a953ba834835e0a449c951a741738",
  "PNP.DirectWire.WireFrontierLift.proper_iff_exterior_positive": "3ad5423b315def909a850c9f775b9bf51ced9833a9566b82978770b779319441",
  "PNP.DirectWire.WireFrontierLift.checkedProperGain_isSome_iff": "419ea770c1d5c32e79ec2f3bc59d1d4497d1b447f3e363a5e70e9e2326d5a01e",
  "PNP.DirectWire.WireFrontierLift.ProperGain.checked": "a3092c4aca64494c0ac7112cf82d000da02b4a4a61ae545f8b74719dc436a2a4"
});
const M253_STATUS_FIELDS = Object.freeze({
  "leanWireFrontierLiftFormalized": true,
  "leanWireFrontierLiftAxiomAuditPassed": true,
  "leanWireFrontierLiftAuditedDeclarationCount": 18,
  "leanWireFrontierLiftOrdinaryOutputSelectedTheorem": "PNP.DirectWire.WireFrontierLift.ordinary_output_selected",
  "leanWireFrontierLiftKeptFieldSelectedTheorem": "PNP.DirectWire.WireFrontierLift.kept_field_selected",
  "leanWireFrontierLiftPredecessorClosureTheorem": "PNP.DirectWire.WireFrontierLift.records_predecessor_closed",
  "leanWireFrontierLiftSelectedFieldFrontierTheorem": "PNP.DirectWire.WireFrontierLift.selected_field_in_frontier",
  "leanWireFrontierLiftPrimaryBoundaryTheorem": "PNP.DirectWire.WireFrontierLift.primary_boundary",
  "leanWireFrontierLiftOriginalChargeTheorem": "PNP.DirectWire.WireFrontierLift.original_charge",
  "leanWireFrontierLiftCompileIsSomeTheorem": "PNP.DirectWire.WireFrontierLift.compile_isSome",
  "leanWireFrontierLiftExpandedChargeTheorem": "PNP.DirectWire.WireFrontierLift.expanded_charge",
  "leanWireFrontierLiftMatchedOriginalChargeTheorem": "PNP.DirectWire.WireFrontierLift.matched_original_charge",
  "leanWireFrontierLiftOriginalGainIffTheorem": "PNP.DirectWire.WireFrontierLift.original_gain_iff",
  "leanWireFrontierLiftExpandedOutputTheorem": "PNP.DirectWire.WireFrontierLift.expanded_output",
  "leanWireFrontierLiftExpandedFieldTheorem": "PNP.DirectWire.WireFrontierLift.expanded_field",
  "leanWireFrontierLiftExpandedEquivalenceTheorem": "PNP.DirectWire.WireFrontierLift.expanded_equivalent",
  "leanWireFrontierLiftDischargeSourceExactTheorem": "PNP.DirectWire.WireFrontierLift.discharge_source_exact",
  "leanWireFrontierLiftDischargeFullValueTheorem": "PNP.DirectWire.WireFrontierLift.discharge_full_value",
  "leanWireFrontierLiftProperIffExteriorPositiveTheorem": "PNP.DirectWire.WireFrontierLift.proper_iff_exterior_positive",
  "leanWireFrontierLiftProperGainIffTheorem": "PNP.DirectWire.WireFrontierLift.checkedProperGain_isSome_iff",
  "leanWireFrontierLiftCheckedProperGainTheorem": "PNP.DirectWire.WireFrontierLift.ProperGain.checked",
  "leanWireFrontierLiftEveryArbitrarySupportCovered": false,
  "leanWireFrontierLiftAutomaticLocalAgreementDerived": false,
  "leanWireFrontierLiftFullManuscriptPullExpandProved": false,
  "leanWireFrontierLiftCompleteObligationCalculusProved": false,
  "leanWireFrontierLiftCompletePackageEProved": false,
  "leanWireFrontierLiftPolynomialRuntimeProved": false,
  "leanWireFrontierLiftScope": "all-finite-computational-wire-input-derived-quotient-visible-cone-completed-original-frontier-primary-boundary-actual-compiler-full-local-open-agreement-original-exterior-once-exact-integer-charges-strict-proper-gain-no-full-manuscript-calculus-or-polynomial-runtime"
});
const M253_AXIOMS = Object.freeze({
  "PNP.DirectWire.WireFrontierLift.ordinary_output_selected": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.kept_field_selected": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.records_predecessor_closed": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.selected_field_in_frontier": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.primary_boundary": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.original_charge": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.compile_isSome": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.expanded_charge": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.matched_original_charge": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.original_gain_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.expanded_output": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.expanded_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.expanded_equivalent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.discharge_source_exact": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.discharge_full_value": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.proper_iff_exterior_positive": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.checkedProperGain_isSome_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireFrontierLift.ProperGain.checked": [
    "Quot.sound",
    "propext"
  ]
});

const M253_MODULES = Object.freeze({
  "PNP.DirectWire.WireFrontierLift.ordinary_output_selected": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.kept_field_selected": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.records_predecessor_closed": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.selected_field_in_frontier": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.primary_boundary": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.original_charge": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.compile_isSome": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.expanded_charge": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.matched_original_charge": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.original_gain_iff": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.expanded_output": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.expanded_field": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.expanded_equivalent": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.discharge_source_exact": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.discharge_full_value": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.proper_iff_exterior_positive": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.checkedProperGain_isSome_iff": "PNP.NANDWireFrontierLift",
  "PNP.DirectWire.WireFrontierLift.ProperGain.checked": "PNP.NANDWireFrontierLift"
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

test('M253 compiled original-accounted frontier lift interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M253_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M253_COORDINATE)
    assert.equal(map.coordinate, M253_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M253_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, M253_MODULES[name], name);
      assert.deepEqual(declaration.axioms, M253_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M253_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M253_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M253_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "computational frontier lift",
  "not arbitrary-support Pull/Expand",
  "complete local open-function agreement are inputs",
  "quotient-only agreement does not imply",
  "whole-support saving is not a proper-support certificate",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M253 publication rejects weakened, supplied, assumption-backed and widened all-support substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M253_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M253_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = 'PNP.DirectWire.WireFrontierLift.expanded_field';
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M253_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M253_MILESTONE
    ? {...row, nonClaim:'The frontier lift proves every arbitrary-support trace, the complete obligation calculus and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M253 adds computed-cone frontier coverage without all-support, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M253_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "original-circuit matched-cost edge",
  "retains each exterior gate once",
  "not every arbitrary support",
  "No fixed load-bearing checkpoint changes state",
  "40% proof estimate"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M253_COORDINATE) return;
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

test('M253 current summaries distinguish computed-cone frontier lifting from all-support and global completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_wire_frontier_lift.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "computational frontier lift",
  "Complete local open-function agreement is a premise",
  "quotient-only agreement is insufficient",
  "actual original circuit",
  "whole-support saving is not a proper-support certificate",
  "Runtime execution is test evidence, not theorem authority",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-12-computed-original-accounted-frontier-lift.md'));
  assert.match(plan, /Publication decision: defer PNPLabs(?:[.,]|$)/u);
  if (progress.asOfCoordinate !== M253_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_wire_frontier_lift.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
