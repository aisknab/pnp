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

const SOURCE = 'lean/PNP/NANDWireMatchedCancellation.lean';
const AUDIT = 'lean-audit/PNPWireMatchedCancellationAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPWireMatchedCancellation.lean';
const NAMES = [
  "PNP.DirectWire.WireMatchedCancellation.representative_isSome_iff",
  "PNP.DirectWire.WireMatchedCancellation.observation_value",
  "PNP.DirectWire.WireMatchedCancellation.Representative.full_value",
  "PNP.DirectWire.WireMatchedCancellation.allResolved_sound",
  "PNP.DirectWire.WireMatchedCancellation.charge_allResolved",
  "PNP.DirectWire.WireMatchedCancellation.missing_unresolved_field",
  "PNP.DirectWire.WireMatchedCancellation.charge_bound",
  "PNP.DirectWire.WireMatchedCancellation.visible_resolved_field",
  "PNP.DirectWire.WireMatchedCancellation.expanded_charge",
  "PNP.DirectWire.WireMatchedCancellation.expanded_output",
  "PNP.DirectWire.WireMatchedCancellation.expanded_field",
  "PNP.DirectWire.WireMatchedCancellation.expanded_equivalent",
  "PNP.DirectWire.WireMatchedCancellation.Discharge.full_value",
  "PNP.DirectWire.WireMatchedCancellation.discharge_source_exact",
  "PNP.DirectWire.WireMatchedCancellation.discharge_isR6_iff",
  "PNP.DirectWire.WireMatchedCancellation.discharge_full_value",
  "PNP.DirectWire.WireMatchedCancellation.checkedGain_isSome_iff",
  "PNP.DirectWire.WireMatchedCancellation.CheckedGain.checked",
  "PNP.DirectWire.WireMatchedCancellation.created_exact",
  "PNP.DirectWire.WireMatchedCancellation.discharged_exact",
  "PNP.DirectWire.WireMatchedCancellation.creation_iff",
  "PNP.DirectWire.WireMatchedCancellation.discharge_iff",
  "PNP.DirectWire.WireMatchedCancellation.created_nodup",
  "PNP.DirectWire.WireMatchedCancellation.discharged_nodup",
  "PNP.DirectWire.WireMatchedCancellation.replay_closed",
  "PNP.DirectWire.WireMatchedCancellation.replay_rejects_duplicate_ids"
];
const SIGNATURES = {
  "representative_isSome_iff": "theorem representative_isSome_iff (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (field : Fin fields) : (representative carrier keep field).isSome = true ↔ ∃ observation, visibility keep observation = true ∧ carrier.exposed.candidate.directWireWord.source observation = carrier.source field",
  "observation_value": "theorem observation_value (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) (observation : Fin (outputs + fields)) (retained : visibility keep observation = true) (valuation : Valuation inputs) : replacement.exposed.candidate.semantics valuation observation = carrier.exposed.candidate.semantics valuation observation",
  "Representative.full_value": "theorem Representative.full_value {carrier : WireCarrier inputs outputs fields} {keep : Fin fields → Bool} {field : Fin fields} (alias : Representative carrier keep field) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) (valuation : Valuation inputs) : replacement.exposed.candidate.semantics valuation alias.observation = carrier.fieldValue valuation field",
  "allResolved_sound": "theorem allResolved_sound (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (complete : allResolved carrier keep = true) (field : Fin fields) : resolved carrier keep field = true",
  "charge_allResolved": "theorem charge_allResolved (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (complete : allResolved carrier keep = true) : charge carrier keep = 0",
  "missing_unresolved_field": "theorem missing_unresolved_field (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (field : Fin fields) (unresolved : resolved carrier keep field = false) (valuation : Valuation inputs) : (missing carrier keep).fieldValue valuation field = carrier.fieldValue valuation field",
  "charge_bound": "theorem charge_bound (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : charge carrier keep ≤ carrier.implementation.gateCount",
  "visible_resolved_field": "theorem visible_resolved_field (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) (field : Fin fields) (represented : resolved carrier keep field = true) (valuation : Valuation inputs) : (visibleReplacement carrier keep replacement).fieldValue valuation field = carrier.fieldValue valuation field",
  "expanded_charge": "theorem expanded_charge (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) : (expanded carrier keep replacement).implementation.gateCount = replacement.implementation.gateCount + charge carrier keep",
  "expanded_output": "theorem expanded_output (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) (valuation : Valuation inputs) (output : Fin outputs) : (expanded carrier keep replacement).implementation.candidate.semantics valuation output = carrier.implementation.candidate.semantics valuation output",
  "expanded_field": "theorem expanded_field (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) (valuation : Valuation inputs) (field : Fin fields) : (expanded carrier keep replacement).fieldValue valuation field = carrier.fieldValue valuation field",
  "expanded_equivalent": "theorem expanded_equivalent (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) : Equivalent (expanded carrier keep replacement).implementation.candidate.program (expanded carrier keep replacement).implementation.candidate.directWireWord carrier.implementation.candidate.program carrier.implementation.candidate.directWireWord",
  "Discharge.full_value": "theorem Discharge.full_value {carrier : WireCarrier inputs outputs fields} {keep : Fin fields → Bool} {replacement : WireCarrier inputs outputs fields} {creation : WireObligationRestoration.R5Creation carrier keep} (witness : Discharge carrier keep replacement creation) (valuation : Valuation inputs) : witness.actualSource.eval valuation ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) = carrier.fieldValue valuation creation.coordinate",
  "discharge_source_exact": "theorem discharge_source_exact (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) (creation : WireObligationRestoration.R5Creation carrier keep) : (discharge carrier keep replacement same creation).actualSource = (expanded carrier keep replacement).source creation.coordinate",
  "discharge_isR6_iff": "theorem discharge_isR6_iff (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) (creation : WireObligationRestoration.R5Creation carrier keep) : (discharge carrier keep replacement same creation).isR6 = true ↔ (representative carrier keep creation.coordinate).isSome = true",
  "discharge_full_value": "theorem discharge_full_value (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) (creation : WireObligationRestoration.R5Creation carrier keep) (valuation : Valuation inputs) : (discharge carrier keep replacement same creation).actualSource.eval valuation ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) = carrier.fieldValue valuation creation.coordinate",
  "checkedGain_isSome_iff": "theorem checkedGain_isSome_iff (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) : (checkedGain carrier keep replacement same).isSome = true ↔ replacement.implementation.gateCount + charge carrier keep < carrier.implementation.gateCount",
  "CheckedGain.checked": "theorem CheckedGain.checked {carrier : WireCarrier inputs outputs fields} {keep : Fin fields → Bool} {replacement : WireCarrier inputs outputs fields} (gain : CheckedGain carrier keep replacement) : StrictEquivalentGain carrier.implementation (expanded carrier keep replacement).implementation ∧ (∀ valuation field, (expanded carrier keep replacement).fieldValue valuation field = carrier.fieldValue valuation field) ∧ (expanded carrier keep replacement).implementation.gateCount = replacement.implementation.gateCount + charge carrier keep",
  "created_exact": "theorem created_exact (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) : createdCoordinates (events carrier keep replacement same) = WireObligationRestoration.forgottenCoordinates keep",
  "discharged_exact": "theorem discharged_exact (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) : dischargedCoordinates (events carrier keep replacement same) = WireObligationRestoration.forgottenCoordinates keep",
  "creation_iff": "theorem creation_iff (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) (field : Fin fields) : field ∈ createdCoordinates (events carrier keep replacement same) ↔ keep field = false",
  "discharge_iff": "theorem discharge_iff (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) (field : Fin fields) : field ∈ dischargedCoordinates (events carrier keep replacement same) ↔ keep field = false",
  "created_nodup": "theorem created_nodup (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) : (createdCoordinates (events carrier keep replacement same)).Nodup",
  "discharged_nodup": "theorem discharged_nodup (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) : (dischargedCoordinates (events carrier keep replacement same)).Nodup",
  "replay_closed": "theorem replay_closed (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (replacement : WireCarrier inputs outputs fields) (same : WireQuotientLift.QuotientAgreement carrier keep replacement) : replay [] (events carrier keep replacement same) = some []",
  "replay_rejects_duplicate_ids": "theorem replay_rejects_duplicate_ids {carrier : WireCarrier inputs outputs fields} {keep : Fin fields → Bool} {replacement : WireCarrier inputs outputs fields} (pending : List (Fin fields)) (transcript : List (Event carrier keep replacement)) (duplicate : ¬(pending ++ createdCoordinates transcript).Nodup) : replay pending transcript = none"
};
const HEADS = [
  "visibility",
  "Representative",
  "scan",
  "representative",
  "representative_isSome_iff",
  "observation_value",
  "Representative.full_value",
  "resolved",
  "allResolved",
  "allResolved_sound",
  "zeroMissing",
  "missing",
  "charge",
  "charge_allResolved",
  "missing_unresolved_field",
  "charge_bound",
  "visibleReplacement",
  "visible_resolved_field",
  "expanded",
  "expanded_charge",
  "expanded_output",
  "expanded_field",
  "expanded_equivalent",
  "R6Discharge",
  "R8Discharge",
  "Discharge",
  "discharge",
  "Discharge.actualSource",
  "Discharge.isR6",
  "Discharge.full_value",
  "discharge_source_exact",
  "discharge_isR6_iff",
  "discharge_full_value",
  "CheckedGain",
  "checkedGain",
  "checkedGain_isSome_iff",
  "CheckedGain.strictGain",
  "CheckedGain.checked",
  "Event",
  "eventsFor",
  "events",
  "createdCoordinates",
  "dischargedCoordinates",
  "replay",
  "created_exact",
  "discharged_exact",
  "creation_iff",
  "discharge_iff",
  "created_nodup",
  "discharged_nodup",
  "replay_closed",
  "replay_rejects_duplicate_ids"
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
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|suppliedRepresentative|suppliedWeight|suppliedResult|callerCertificate)\b/u.test(clean),'shortcut-or-certificate');
  require0(!/\b(?:allCandidates|allBoolTuples|allSubsets|equivalentBool|referenceMinimum|scanEquivalentSizes|terminalFullProfileMinimum)\b/u.test(clean),'no-semantic-enumeration');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]))===
    JSON.stringify(['PNP.NANDWireQuotientLift']),'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name))===
    JSON.stringify(HEADS),'public-interface');
  require0(clean.includes('variable {inputs outputs fields : Nat}'),'unbounded-dimensions');
  for(const [name,signature] of Object.entries(SIGNATURES))
    require0(signature0(block(name))===signature,'signature:'+name);
  require0(block('visibility').endsWith('splitFin (fun _ : Fin outputs => true) keep'),
    'actual-visible-observations');
  includes('Representative',[
    'observation : Fin (outputs + fields)',
    'visible : visibility keep observation = true',
    'sourceExact : carrier.exposed.candidate.directWireWord.source observation = carrier.source field',
  ],'original-visible-source-binding');
  includes('scan',[
    'if eligible : visibility keep observation = true ∧ carrier.exposed.candidate.directWireWord.source observation = carrier.source field then',
    'some ⟨observation, eligible.1, eligible.2⟩',
    'else scan carrier keep field remaining',
  ],'computed-literal-source-scan');
  require0(block('representative').endsWith(
    'scan carrier keep field (allFin (outputs + fields))'),'canonical-all-observation-scan');
  require0(block('resolved').endsWith('keep field || (representative carrier keep field).isSome'),
    'kept-or-computed-match');
  require0(block('allResolved').endsWith('(allFin fields).all (resolved carrier keep)'),
    'complete-resolution-mask');
  includes('zeroMissing',['(.empty : Program inputs 0)','source := fun _ => .constant false'],
    'actual-zero-program');
  require0(block('missing').endsWith(
    'if allResolved carrier keep then zeroMissing inputs fields else WireObligationRestoration.materializer carrier (resolved carrier keep)'),
    'actual-unresolved-materializer');
  require0(block('charge').endsWith('(missing carrier keep).implementation.gateCount'),
    'actual-materializer-charge');
  includes('visibleReplacement',[
    'implementation := replacement.implementation',
    'if keep field then replacement.source field else match representative carrier keep field with',
    '| none => .constant false',
    '| some alias => replacement.exposed.candidate.directWireWord.source alias.observation',
  ],'actual-replacement-observation');
  require0(block('expanded').endsWith(
    'WireObligationRestoration.join (visibleReplacement carrier keep replacement) (missing carrier keep) (resolved carrier keep)'),
    'single-actual-expansion');
  for(const name of ['R6Discharge','R8Discharge']) includes(name,[
    'actualSource : Source inputs (expanded carrier keep replacement).implementation.gateCount',
    'sourceExact : actualSource = (expanded carrier keep replacement).source creation.coordinate',
    'fullWitness : ∀ valuation, actualSource.eval valuation ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) = creation.originalSource.eval valuation (carrier.implementation.candidate.program.eval valuation)',
  ],'full-source-witness:'+name);
  includes('R6Discharge',[
    'alias : Representative carrier keep creation.coordinate',
    'aliasExact : representative carrier keep creation.coordinate = some alias',
  ],'computed-r6-match');
  includes('R8Discharge',[
    'unrepresented : representative carrier keep creation.coordinate = none',
    'unresolved : resolved carrier keep creation.coordinate = false',
  ],'unresolved-r8-boundary');
  includes('discharge',[
    '(same : WireQuotientLift.QuotientAgreement carrier keep replacement)',
    'match found : representative carrier keep creation.coordinate with',
    '.r6 { alias := alias, aliasExact := found',
    '.r8 { unrepresented := found',
    'fullWitness := constructed_full_value carrier keep replacement same creation',
  ],'derived-mixed-discharge');
  includes('constructed_full_value',[
    'rw [creation.sourceExact]',
    'exact expanded_field carrier keep replacement same valuation creation.coordinate',
  ],'derived-actual-full-value');
  includes('checkedGain',[
    'if smaller : (expanded carrier keep replacement).implementation.gateCount < carrier.implementation.gateCount then',
    'some ⟨same, smaller⟩ else none',
  ],'fully-paid-original-gain');
  includes('Event',[
    'createR5 (creation : WireObligationRestoration.R5Creation carrier keep)',
    'discharge (creation : WireObligationRestoration.R5Creation carrier keep)',
    '(witness : Discharge carrier keep replacement creation)',
  ],'typed-full-discharge-event');
  includes('eventsFor',[
    'let creation := WireObligationRestoration.createR5 carrier keep field forgotten .createR5 creation :: .discharge creation',
    'discharge carrier keep replacement same creation',
  ],'derived-mixed-events');
  require0(block('events').endsWith(
    'eventsFor carrier keep replacement same (List.finRange fields)'),'canonical-forgotten-events');
  includes('replay',[
    'if (pending ++ createdCoordinates transcript).Nodup then replayPending pending transcript else none',
  ],'whole-transcript-identity-uniqueness');
  includes('replayPending',[
    'if creation.coordinate ∈ pending then none',
    '| [] => none',
    'if first = creation.coordinate then replayPending rest remaining else none',
  ],'ordered-pending-lifecycle');
  return [...new Set(failures)];
}

test('M254 computes original-source representatives and complete full-mode discharges',async()=>{
  assert.deepEqual(validateSource0(await text0(SOURCE)),[]);
});

test('M254 root, exact theorem-name producers and axiom audit agree',async()=>{
  const [audit,inventorySource,root]=await Promise.all([
    text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean')]);
  for(const name of NAMES){
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item=>item===name).length,1,name);
    assert.equal(inventorySource.split(String.fromCharCode(96)+name+',').length-1,1,name);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),NAMES);
  assert.match(root,/^import PNP\.NANDWireMatchedCancellation\s*$/mu);
});

function rejectMutations0(source,mutations) {
  for(const [before,after,category] of mutations){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
}


test('M254 rejects hidden representatives, supplied scans and padding-only matches',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['splitFin (fun _ : Fin outputs => true) keep',
      'fun _ => true','actual-visible-observations'],
    ['visible : visibility keep observation = true',
      'visible : True','original-visible-source-binding'],
    ['if eligible : visibility keep observation = true ∧',
      'if eligible : True ∧','computed-literal-source-scan'],
    ['scan carrier keep field (allFin (outputs + fields))',
      'scan carrier keep field []','canonical-all-observation-scan'],
    ['keep field || (representative carrier keep field).isSome',
      'true','kept-or-computed-match'],
    ['(allFin fields).all (resolved carrier keep)',
      'true','complete-resolution-mask'],
    ['theorem expanded_field (carrier : WireCarrier inputs outputs fields)',
      'theorem expanded_field (carrier : WireCarrier 1 outputs fields)','signature:expanded_field'],
  ]);
});

test('M254 rejects free charges, wrong replacement sources and duplicated materializers',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['else WireObligationRestoration.materializer carrier (resolved carrier keep)',
      'else zeroMissing inputs fields','actual-unresolved-materializer'],
    ['(missing carrier keep).implementation.gateCount',
      '0','actual-materializer-charge'],
    ['| some alias => replacement.exposed.candidate.directWireWord.source alias.observation',
      '| some alias => replacement.source field','actual-replacement-observation'],
    ['(missing carrier keep) (resolved carrier keep)',
      '(zeroMissing inputs fields) (resolved carrier keep)','single-actual-expansion'],
    ['replacement.implementation.gateCount + charge carrier keep := rfl',
      'replacement.implementation.gateCount + 2 * charge carrier keep := rfl','signature:expanded_charge'],
    ['if smaller : (expanded carrier keep replacement).implementation.gateCount <',
      'if smaller : replacement.implementation.gateCount <','fully-paid-original-gain'],
  ]);
});

test('M254 rejects weak, unbound and supplied full cancellation witnesses',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['aliasExact : representative carrier keep creation.coordinate = some alias',
      'aliasExact : True','computed-r6-match'],
    ['unrepresented : representative carrier keep creation.coordinate = none',
      'unrepresented : True','unresolved-r8-boundary'],
    ['sourceExact : actualSource = (expanded carrier keep replacement).source creation.coordinate',
      'sourceExact : True','full-source-witness:R6Discharge'],
    ['fullWitness : ∀ valuation,','fullWitness : ∃ valuation,','full-source-witness:R8Discharge'],
    ['fullWitness := constructed_full_value carrier keep replacement same creation',
      'fullWitness := suppliedResult','derived-mixed-discharge'],
    ['exact expanded_field carrier keep replacement same valuation creation.coordinate',
      'exact suppliedResult','derived-actual-full-value'],
    ['(same : WireQuotientLift.QuotientAgreement carrier keep replacement)',
      '(same : True)','signature:expanded_field'],
  ]);
});

test('M254 rejects identity reuse, wrong ordering and untyped discharge events',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['(witness : Discharge carrier keep replacement creation)',
      '(witness : True)','typed-full-discharge-event'],
    ['.createR5 creation :: .discharge creation',
      '.createR5 creation :: .createR5 creation :: .discharge creation','derived-mixed-events'],
    ['eventsFor carrier keep replacement same (List.finRange fields)',
      'eventsFor carrier keep replacement same []','canonical-forgotten-events'],
    ['if (pending ++ createdCoordinates transcript).Nodup then',
      'if pending.Nodup then','whole-transcript-identity-uniqueness'],
    ['if first = creation.coordinate then replayPending rest remaining else none',
      'replayPending rest remaining','ordered-pending-lifecycle'],
    ['if creation.coordinate ∈ pending then none',
      'if False then none','ordered-pending-lifecycle'],
  ]);
});

test('M254 rejects assumptions, unaudited forms and exhaustive semantic shortcuts',async()=>{
  const source=await text0(SOURCE);
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n').includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n').includes('unaudited-form'));
  assert.ok(validateSource0(source+'\ndef extra := referenceMinimum\n').includes('no-semantic-enumeration'));
  assert.ok(validateSource0(source.replace('import PNP.NANDWireQuotientLift',
    'import PNP.NANDWireQuotientLift\nimport Unknown.Source')).includes('closed-imports'));
});

test('M254 theorem signatures preserve dependent binders and dotted names',()=>{
  const declaration='theorem CheckedGain.checked (source : Carrier (fields := fields)) '+
    '(same : source = target) : target = source := same.symm';
  assert.equal(signature0(declaration),declaration.slice(0,declaration.lastIndexOf(' := ')));
  assert.equal(signature0(block0(declaration,'CheckedGain.checked')),signature0(declaration));
  assert.notEqual(signature0(declaration.replace('(same :','(extra : True) (same :')),
    signature0(declaration));
});


test('M254 regressions separate R6, paid R8, retained sources and closed identities',async()=>{
  const raw=await text0(REGRESSION),regression=compact0(raw);
  assert.deepEqual([...raw.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  for(const token of [
    '¬WireQuotientLift.QuotientAgreement outputAlias dropAll unrelatedHidden',
    '¬WireQuotientLift.QuotientAgreement keptAlias keepFirst (trueReplacement 2)',
    '(representative noRetained dropAll 0).isSome = false := by decide',
    '(representative paddingCollision dropAll 0).isSome = false := by decide',
    'unrelatedHidden.fieldValue (fun _ => false) 0 ≠ paddingCollision.fieldValue (fun _ => false) 0',
    'expanded_field carrier keep replacement same valuation field',
    'discharge_full_value carrier keep replacement same creation valuation',
    'replay_closed carrier keep replacement same',
    'charge outputAlias dropAll != 0',
    'charge mixedAliases dropAll != 1',
    'charge repeatedAliases dropAll != 1',
    '[false, true, false, true]',
    'charge keptAlias keepFirst != 0',
    'charge noRetained dropAll != 1',
    'charge paddingCollision dropAll != 1',
    'charge freeFields freeKeep != 0',
    'charge empty dropAll != 0',
    '!firstWitness.isR6 || secondWitness.isR6',
    'replay [] (transcript ++ transcript) != none',
    'replay [] premature != none',
    'replay [] wrongCoordinate != none',
    'replay [] duplicatePending != none',
    'replay [0] transcript != none',
    'for output in allFin outputs do',
    'for field in allFin fields do',
    'witness.actualSource.eval valuation (actual.implementation.candidate.program.eval valuation)',
    '#eval show IO Unit from do','throw (IO.userError',
  ])assert.ok(regression.includes(token),token);
  assert.equal([...raw.matchAll(/^#eval\b/gmu)].length,1);
  assert.doesNotMatch(regression,/\b(?:sorry|admit|native_decide|Classical|referenceMinimum|scanEquivalentSizes|allCandidates)\b/u);
  assert.doesNotMatch(raw,/#eval!/u);
});

test('M254 durable workflow retains source checks, exact audit and bounded regressions',async()=>{
  const [packageText,surface,verifier,workflow]=await Promise.all([
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),text0('.github/workflows/lean-bridge.yml')]);
  const auditPath='audits/lean-wire-matched-cancellation0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m254'],'node --test '+auditPath);
  assert.ok(surface.includes("'audit:m254': 'node --test "+auditPath+"'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test '+auditPath));
  for(const path of [auditPath,'docs/lean_wire_matched_cancellation.md'])
    assert.equal(workflow.split("      - '"+path.replace(/^audits\/lean-[^/]+\.test\.mjs$/u,'audits/lean-*.test.mjs').replace(/^docs\/lean_[^/]+\.md$/u,'docs/lean_*.md').replace(/^lean\/.*$/u,'lean/**').replace(/^lean-audit\/.*$/u,'lean-audit/**').replace(/^lean-regression\/.*$/u,'lean-regression/**')+"'").length-1,2);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M254_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-13-254';
const M254_MILESTONE = 'wire-matched-cancellation';
const M254_HASHES = Object.freeze({
  "PNP.DirectWire.WireMatchedCancellation.representative_isSome_iff": "9a0ce14691f7d8efab0f371697999b2d067b00a5bfc9fcd44f862f21bcc4e6ba",
  "PNP.DirectWire.WireMatchedCancellation.observation_value": "f94cb4b0dc8e6c033764ada12c4f515a90797071f034c88ae12b3d823f08ec68",
  "PNP.DirectWire.WireMatchedCancellation.Representative.full_value": "b427980991225d6ec290732313658035f0423b39e96246f5f2cc3dcd3eca38f3",
  "PNP.DirectWire.WireMatchedCancellation.allResolved_sound": "b8d11d28fe4db2ec5cd7e0425e4151719df9a47c68eb71bdc4f36cdeab857cd6",
  "PNP.DirectWire.WireMatchedCancellation.charge_allResolved": "315efbe39ca329c5d4d6e122ace539f26c3f3d89dbd486cbff820cc4c52d5ae7",
  "PNP.DirectWire.WireMatchedCancellation.missing_unresolved_field": "66dd6694892b90af070b2842905361dcdd6f7aa20ecb4e9b3b96b44272b43b59",
  "PNP.DirectWire.WireMatchedCancellation.charge_bound": "1adaf4f65352bbcf5056894a1f581a8d4d2104e789f18e770823c90b6fffacde",
  "PNP.DirectWire.WireMatchedCancellation.visible_resolved_field": "11a959061c3465bb82fa0daaabc34c0b0af67467602e70fa8838e02910ebbc5b",
  "PNP.DirectWire.WireMatchedCancellation.expanded_charge": "5c010930b10c343eb99b555161171751238b45c577a7b2ef7a27675d9cb0b2ba",
  "PNP.DirectWire.WireMatchedCancellation.expanded_output": "50f302457ac646b61330aab04da7d1cdc0ac4ef53ba18b9ab1967c3d9f2c882c",
  "PNP.DirectWire.WireMatchedCancellation.expanded_field": "fd823a6e1a7a2eb2896ae0f86a9405acb41eb35d5a560e92ce5877157a5d2caa",
  "PNP.DirectWire.WireMatchedCancellation.expanded_equivalent": "d739a414f98686dfc8eacb28580976115794150dc2339039706874eb98e47488",
  "PNP.DirectWire.WireMatchedCancellation.Discharge.full_value": "9743c4ea11a1b3ef791893c7c4700e1dfd49d8d342f318241d92e5e104c353ab",
  "PNP.DirectWire.WireMatchedCancellation.discharge_source_exact": "527fa079d1da2264a7c958b78b3264c08e89da693cbc4d579471d8c0a91b8fd5",
  "PNP.DirectWire.WireMatchedCancellation.discharge_isR6_iff": "344e9293b8d23622e47cfc82a3d9f4a7311e085d78f1111a58a118c012a6478e",
  "PNP.DirectWire.WireMatchedCancellation.discharge_full_value": "b2f03c46a68b1d103f2bb60d2ffebcea476463787a73e138b7db27110d4b8398",
  "PNP.DirectWire.WireMatchedCancellation.checkedGain_isSome_iff": "75d6ee1639773cb2417ca3077af8011f6677d6c042f869b1d6691d7be3865b57",
  "PNP.DirectWire.WireMatchedCancellation.CheckedGain.checked": "7729efcecab7e56556163bdc2bcf218be41a062a6ee285b9807ae6bd3ac2dea7",
  "PNP.DirectWire.WireMatchedCancellation.created_exact": "e32e06f39dd7a79aeeb8194892b45d5bf39b86e9014f267b438e7613d26e03c9",
  "PNP.DirectWire.WireMatchedCancellation.discharged_exact": "485a37483687566eff84234d8322dce65af02f4614c43d62a1c3bcddb4643cc3",
  "PNP.DirectWire.WireMatchedCancellation.creation_iff": "213a77f56b3cf7580de96510516a7c919f1b983cf81c79d8547f639d754e2ba1",
  "PNP.DirectWire.WireMatchedCancellation.discharge_iff": "14291497e107583d0464ec07e6ad74851f49fcc1526ef0fd7dc6e5dd7199dbcf",
  "PNP.DirectWire.WireMatchedCancellation.created_nodup": "6768c54d50fa580f817703b0ebdd6ec8bccc1e149aefc968836a475bc6055986",
  "PNP.DirectWire.WireMatchedCancellation.discharged_nodup": "92d6396ff619ed082c562af3e0e469c7745091c66a916ff678ed6dd9cd0d4dae",
  "PNP.DirectWire.WireMatchedCancellation.replay_closed": "1abaf7da81590fa0607285d5e8576843119d5c2dd0c92e0862235f982aa4d53e",
  "PNP.DirectWire.WireMatchedCancellation.replay_rejects_duplicate_ids": "fbd380c2eb40962a25bccbbcd30b86d60ec182ca41ee71beb486532d92223602"
});
const M254_STATUS_FIELDS = Object.freeze({
  "leanWireMatchedCancellationFormalized": true,
  "leanWireMatchedCancellationAxiomAuditPassed": true,
  "leanWireMatchedCancellationAuditedDeclarationCount": 26,
  "leanWireMatchedCancellationRepresentativeAvailabilityTheorem": "PNP.DirectWire.WireMatchedCancellation.representative_isSome_iff",
  "leanWireMatchedCancellationRetainedObservationValueTheorem": "PNP.DirectWire.WireMatchedCancellation.observation_value",
  "leanWireMatchedCancellationRepresentativeFullValueTheorem": "PNP.DirectWire.WireMatchedCancellation.Representative.full_value",
  "leanWireMatchedCancellationAllResolvedSoundnessTheorem": "PNP.DirectWire.WireMatchedCancellation.allResolved_sound",
  "leanWireMatchedCancellationAllResolvedChargeTheorem": "PNP.DirectWire.WireMatchedCancellation.charge_allResolved",
  "leanWireMatchedCancellationUnresolvedMaterializerFieldTheorem": "PNP.DirectWire.WireMatchedCancellation.missing_unresolved_field",
  "leanWireMatchedCancellationMaterializerChargeBoundTheorem": "PNP.DirectWire.WireMatchedCancellation.charge_bound",
  "leanWireMatchedCancellationVisibleResolvedFieldTheorem": "PNP.DirectWire.WireMatchedCancellation.visible_resolved_field",
  "leanWireMatchedCancellationExpandedChargeTheorem": "PNP.DirectWire.WireMatchedCancellation.expanded_charge",
  "leanWireMatchedCancellationExpandedOutputTheorem": "PNP.DirectWire.WireMatchedCancellation.expanded_output",
  "leanWireMatchedCancellationExpandedFieldTheorem": "PNP.DirectWire.WireMatchedCancellation.expanded_field",
  "leanWireMatchedCancellationExpandedEquivalenceTheorem": "PNP.DirectWire.WireMatchedCancellation.expanded_equivalent",
  "leanWireMatchedCancellationDischargeWitnessFullValueTheorem": "PNP.DirectWire.WireMatchedCancellation.Discharge.full_value",
  "leanWireMatchedCancellationDischargeSourceExactTheorem": "PNP.DirectWire.WireMatchedCancellation.discharge_source_exact",
  "leanWireMatchedCancellationDischargeKindIffTheorem": "PNP.DirectWire.WireMatchedCancellation.discharge_isR6_iff",
  "leanWireMatchedCancellationComputedDischargeFullValueTheorem": "PNP.DirectWire.WireMatchedCancellation.discharge_full_value",
  "leanWireMatchedCancellationGainIffTheorem": "PNP.DirectWire.WireMatchedCancellation.checkedGain_isSome_iff",
  "leanWireMatchedCancellationCheckedGainTheorem": "PNP.DirectWire.WireMatchedCancellation.CheckedGain.checked",
  "leanWireMatchedCancellationCreatedExactTheorem": "PNP.DirectWire.WireMatchedCancellation.created_exact",
  "leanWireMatchedCancellationDischargedExactTheorem": "PNP.DirectWire.WireMatchedCancellation.discharged_exact",
  "leanWireMatchedCancellationCreationIffTheorem": "PNP.DirectWire.WireMatchedCancellation.creation_iff",
  "leanWireMatchedCancellationDischargeIffTheorem": "PNP.DirectWire.WireMatchedCancellation.discharge_iff",
  "leanWireMatchedCancellationCreatedNodupTheorem": "PNP.DirectWire.WireMatchedCancellation.created_nodup",
  "leanWireMatchedCancellationDischargedNodupTheorem": "PNP.DirectWire.WireMatchedCancellation.discharged_nodup",
  "leanWireMatchedCancellationReplayClosedTheorem": "PNP.DirectWire.WireMatchedCancellation.replay_closed",
  "leanWireMatchedCancellationRejectDuplicateIdsTheorem": "PNP.DirectWire.WireMatchedCancellation.replay_rejects_duplicate_ids",
  "leanWireMatchedCancellationAllSemanticCancellationsDerived": false,
  "leanWireMatchedCancellationArbitraryObligationDAGsCovered": false,
  "leanWireMatchedCancellationAutomaticLocalAgreementDerived": false,
  "leanWireMatchedCancellationFullManuscriptCarrierProved": false,
  "leanWireMatchedCancellationCompleteObligationCalculusProved": false,
  "leanWireMatchedCancellationCompletePackageEProved": false,
  "leanWireMatchedCancellationPolynomialRuntimeProved": false,
  "leanWireMatchedCancellationScope": "all-finite-computational-wire-original-visible-source-identity-scan-local-quotient-agreement-derived-full-r6-cancellation-unresolved-shared-r8-materializer-actual-expanded-source-exact-charge-whole-trace-unique-ids-no-complete-calculus-or-polynomial-runtime"
});
const M254_AXIOMS = Object.freeze({
  "PNP.DirectWire.WireMatchedCancellation.representative_isSome_iff": [
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.observation_value": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.Representative.full_value": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.allResolved_sound": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.charge_allResolved": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.missing_unresolved_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.charge_bound": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.visible_resolved_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.expanded_charge": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.expanded_output": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.expanded_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.expanded_equivalent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.Discharge.full_value": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.discharge_source_exact": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.discharge_isR6_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.discharge_full_value": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.checkedGain_isSome_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.CheckedGain.checked": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.created_exact": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.discharged_exact": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.creation_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.discharge_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.created_nodup": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.discharged_nodup": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.replay_closed": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireMatchedCancellation.replay_rejects_duplicate_ids": [
    "Quot.sound",
    "propext"
  ]
});

const M254_MODULES = Object.freeze({
  "PNP.DirectWire.WireMatchedCancellation.representative_isSome_iff": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.observation_value": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.Representative.full_value": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.allResolved_sound": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.charge_allResolved": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.missing_unresolved_field": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.charge_bound": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.visible_resolved_field": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.expanded_charge": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.expanded_output": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.expanded_field": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.expanded_equivalent": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.Discharge.full_value": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.discharge_source_exact": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.discharge_isR6_iff": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.discharge_full_value": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.checkedGain_isSome_iff": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.CheckedGain.checked": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.created_exact": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.discharged_exact": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.creation_iff": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.discharge_iff": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.created_nodup": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.discharged_nodup": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.replay_closed": "PNP.NANDWireMatchedCancellation",
  "PNP.DirectWire.WireMatchedCancellation.replay_rejects_duplicate_ids": "PNP.NANDWireMatchedCancellation"
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

test('M254 compiled full-mode wire cancellation interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M254_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M254_COORDINATE)
    assert.equal(map.coordinate, M254_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M254_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, M254_MODULES[name], name);
      assert.deepEqual(declaration.axioms, M254_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M254_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M254_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M254_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "original-source-identity computational R6 case",
  "not every semantic cancellation",
  "precise local quotient agreement are inputs",
  "No universal comparison",
  "whole-word strict gain is not a proper-support Package E certificate",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M254 publication rejects weakened, supplied, assumption-backed and widened complete-calculus substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M254_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M254_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = 'PNP.DirectWire.WireMatchedCancellation.expanded_field';
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M254_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M254_MILESTONE
    ? {...row, nonClaim:'The wire cancellation proves all semantic cancellations, the complete obligation calculus and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M254 adds computed wire cancellation coverage without complete-calculus, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M254_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "full-mode R6 dependency",
  "whole-transcript unique obligation identities",
  "not masked padding",
  "No fixed load-bearing checkpoint changes state",
  "40% proof estimate"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M254_COORDINATE) return;
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

test('M254 current summaries distinguish computed wire cancellation from complete-calculus and global completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_wire_matched_cancellation.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "Computational source identity, not arbitrary semantic equality",
  "Local quotient agreement is a premise",
  "not evidence for a forgotten field",
  "Whole-word gain is not proper-support Package E",
  "Runtime execution is test evidence, not theorem authority",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-13-computed-full-mode-wire-cancellation.md'));
  assert.match(plan, /Publication decision: defer PNPLabs(?:[.,]|$)/u);
  if (progress.asOfCoordinate !== M254_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_wire_matched_cancellation.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
