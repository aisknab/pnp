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

const SOURCE = 'lean/PNP/NANDWireObligationRestoration.lean';
const AUDIT = 'lean-audit/PNPWireObligationRestorationAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPWireObligationRestoration.lean';
const NAMES = [
  "PNP.DirectWire.WireObligationRestoration.projected_output",
  "PNP.DirectWire.WireObligationRestoration.projected_kept_field",
  "PNP.DirectWire.WireObligationRestoration.materializer_forgotten_field",
  "PNP.DirectWire.WireObligationRestoration.join_output",
  "PNP.DirectWire.WireObligationRestoration.join_kept_field",
  "PNP.DirectWire.WireObligationRestoration.join_forgotten_field",
  "PNP.DirectWire.WireObligationRestoration.restored_output",
  "PNP.DirectWire.WireObligationRestoration.restored_field",
  "PNP.DirectWire.WireObligationRestoration.restored_exact_gate_charge",
  "PNP.DirectWire.WireObligationRestoration.restored_gate_bound",
  "PNP.DirectWire.WireObligationRestoration.created_exact",
  "PNP.DirectWire.WireObligationRestoration.discharged_exact",
  "PNP.DirectWire.WireObligationRestoration.mem_forgottenCoordinates_iff",
  "PNP.DirectWire.WireObligationRestoration.creation_iff",
  "PNP.DirectWire.WireObligationRestoration.discharge_iff",
  "PNP.DirectWire.WireObligationRestoration.replay_closed",
  "PNP.DirectWire.WireObligationRestoration.dischargeR8_full_value",
  "PNP.DirectWire.WireObligationRestoration.gain?_isSome_iff",
  "PNP.DirectWire.WireObligationRestoration.gain_checked",
  "PNP.DirectWire.WireObligationRestoration.created_nodup",
  "PNP.DirectWire.WireObligationRestoration.discharged_nodup",
  "PNP.DirectWire.WireObligationRestoration.replay_rejects_duplicate_ids"
];
const SIGNATURES = {
  "projected_output": "theorem projected_output (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (valuation : Valuation inputs) (output : Fin outputs) : (projected carrier keep).implementation.candidate.semantics valuation output = carrier.implementation.candidate.semantics valuation output",
  "projected_kept_field": "theorem projected_kept_field (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (valuation : Valuation inputs) (field : Fin fields) (kept : keep field = true) : (projected carrier keep).fieldValue valuation field = carrier.fieldValue valuation field",
  "materializer_forgotten_field": "theorem materializer_forgotten_field (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (valuation : Valuation inputs) (field : Fin fields) (forgotten : keep field = false) : (materializer carrier keep).fieldValue valuation field = carrier.fieldValue valuation field",
  "join_output": "theorem join_output (visible : WireCarrier inputs outputs fields) (missing : WireCarrier inputs 0 fields) (keep : Fin fields → Bool) (valuation : Valuation inputs) (output : Fin outputs) : (join visible missing keep).implementation.candidate.semantics valuation output = visible.implementation.candidate.semantics valuation output",
  "join_kept_field": "theorem join_kept_field (visible : WireCarrier inputs outputs fields) (missing : WireCarrier inputs 0 fields) (keep : Fin fields → Bool) (valuation : Valuation inputs) (field : Fin fields) (kept : keep field = true) : (join visible missing keep).fieldValue valuation field = visible.fieldValue valuation field",
  "join_forgotten_field": "theorem join_forgotten_field (visible : WireCarrier inputs outputs fields) (missing : WireCarrier inputs 0 fields) (keep : Fin fields → Bool) (valuation : Valuation inputs) (field : Fin fields) (forgotten : keep field = false) : (join visible missing keep).fieldValue valuation field = missing.fieldValue valuation field",
  "restored_output": "theorem restored_output (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (valuation : Valuation inputs) (output : Fin outputs) : (restored carrier keep).implementation.candidate.semantics valuation output = carrier.implementation.candidate.semantics valuation output",
  "restored_field": "theorem restored_field (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (valuation : Valuation inputs) (field : Fin fields) : (restored carrier keep).fieldValue valuation field = carrier.fieldValue valuation field",
  "restored_exact_gate_charge": "theorem restored_exact_gate_charge (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : (restored carrier keep).implementation.gateCount = (projected carrier keep).implementation.gateCount + (materializer carrier keep).implementation.gateCount",
  "restored_gate_bound": "theorem restored_gate_bound (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : (restored carrier keep).implementation.gateCount ≤ carrier.implementation.gateCount + carrier.implementation.gateCount",
  "created_exact": "theorem created_exact (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : createdCoordinates (events carrier keep) = forgottenCoordinates keep",
  "discharged_exact": "theorem discharged_exact (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : dischargedCoordinates (events carrier keep) = forgottenCoordinates keep",
  "mem_forgottenCoordinates_iff": "theorem mem_forgottenCoordinates_iff (keep : Fin fields → Bool) (field : Fin fields) : field ∈ forgottenCoordinates keep ↔ keep field = false",
  "creation_iff": "theorem creation_iff (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (field : Fin fields) : field ∈ createdCoordinates (events carrier keep) ↔ keep field = false",
  "discharge_iff": "theorem discharge_iff (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (field : Fin fields) : field ∈ dischargedCoordinates (events carrier keep) ↔ keep field = false",
  "replay_closed": "theorem replay_closed (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : replay [] (events carrier keep) = some []",
  "dischargeR8_full_value": "theorem dischargeR8_full_value (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (creation : R5Creation carrier keep) (valuation : Valuation inputs) : (dischargeR8 carrier keep creation).restoredSource.eval valuation ((restored carrier keep).implementation.candidate.program.eval valuation) = carrier.fieldValue valuation creation.coordinate",
  "gain?_isSome_iff": "theorem gain?_isSome_iff (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : (gain? carrier keep).isSome = true ↔ (projected carrier keep).implementation.gateCount + (materializer carrier keep).implementation.gateCount < carrier.implementation.gateCount",
  "gain_checked": "theorem gain_checked (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) (gain : RestoredGain carrier keep) : (∀ valuation output, (restored carrier keep).implementation.candidate.semantics valuation output = carrier.implementation.candidate.semantics valuation output) ∧ (∀ valuation field, (restored carrier keep).fieldValue valuation field = carrier.fieldValue valuation field) ∧ (restored carrier keep).implementation.gateCount < carrier.implementation.gateCount ∧ (restored carrier keep).implementation.gateCount = (projected carrier keep).implementation.gateCount + (materializer carrier keep).implementation.gateCount",
  "created_nodup": "theorem created_nodup (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : (createdCoordinates (events carrier keep)).Nodup",
  "discharged_nodup": "theorem discharged_nodup (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) : (dischargedCoordinates (events carrier keep)).Nodup",
  "replay_rejects_duplicate_ids": "theorem replay_rejects_duplicate_ids {carrier : WireCarrier inputs outputs fields} {keep : Fin fields → Bool} (pending : List (Fin fields)) (transcript : List (Event carrier keep)) (duplicate : ¬(pending ++ createdCoordinates transcript).Nodup) : replay pending transcript = none"
};
const HEADS = [
  'masked','projected','hidden','materializer','projected_output',
  'projected_kept_field','materializer_forgotten_field','join','join_output',
  'join_kept_field','join_forgotten_field','restored','restored_output',
  'restored_field','restored_exact_gate_charge','restored_gate_bound',
  'R5Creation','createR5','R8Discharge','dischargeR8','Event','eventsFor','events',
  'forgottenCoordinates','createdCoordinates','dischargedCoordinates','replay',
  'created_exact','discharged_exact','mem_forgottenCoordinates_iff','creation_iff',
  'discharge_iff','dischargeR8_full_value','RestoredGain','gain?','gain?_isSome_iff',
  'gain_checked','created_nodup','discharged_nodup','replay_closed',
  'replay_rejects_duplicate_ids',
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
    JSON.stringify(['PNP.NANDWireCarrier']),'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name))===
    JSON.stringify(HEADS),'public-interface');
  require0(clean.includes('variable {inputs outputs fields : Nat}'),'unbounded-dimensions');
  for(const [name,signature] of Object.entries(SIGNATURES))
    require0(signature0(block(name))===signature,'signature:'+name);
  includes('masked',[
    'implementation := carrier.implementation',
    'if keep field then carrier.source field else .constant false',
  ],'quotient-only-mask');
  require0(block('projected').endsWith('(masked carrier keep).normalize'),'actual-projection');
  includes('hidden',[
    'WireCarrier inputs 0 fields',
    'Candidate.ofDirectWireWord carrier.implementation.candidate.program ⟨Fin.elim0⟩',
    'if keep field then .constant false else carrier.source field',
  ],'actual-hidden-wire-program');
  require0(block('materializer').endsWith('(hidden carrier keep).normalize'),'actual-shared-materializer');
  includes('join',[
    'visible.implementation.candidate.program.appendSubstituted (fun input => .input input) missing.implementation.candidate.program',
    '(visible.implementation.candidate.directWireWord.source output).weakenGates missing.implementation.gateCount',
    'if keep field then (visible.source field).weakenGates missing.implementation.gateCount else (missing.source field).substituteInputs (fun input => .input input)',
  ],'literal-paid-concatenation');
  require0(block('restored').endsWith(
    'join (projected carrier keep) (materializer carrier keep) keep'),'actual-full-restoration');
  includes('R5Creation',[
    'coordinate : Fin fields','forgotten : keep coordinate = false',
    'originalSource : Source inputs carrier.implementation.gateCount',
    'sourceExact : originalSource = carrier.source coordinate',
  ],'bound-creation');
  includes('createR5',[
    'coordinate := field','forgotten := forgotten',
    'originalSource := carrier.source field, sourceExact := rfl',
  ],'computed-creation');
  includes('R8Discharge',[
    'restoredSource : Source inputs (restored carrier keep).implementation.gateCount',
    'sourceExact : restoredSource = (restored carrier keep).source creation.coordinate',
    'fullWitness : ∀ valuation, restoredSource.eval valuation ((restored carrier keep).implementation.candidate.program.eval valuation) = creation.originalSource.eval valuation (carrier.implementation.candidate.program.eval valuation)',
  ],'bound-full-discharge');
  includes('dischargeR8',[
    'restoredSource := (restored carrier keep).source creation.coordinate',
    'sourceExact := rfl','rw [creation.sourceExact]',
    'exact restored_field carrier keep valuation creation.coordinate',
  ],'derived-full-witness');
  includes('Event',[
    '| createR5 (creation : R5Creation carrier keep)',
    '| dischargeR8 (creation : R5Creation carrier keep) (witness : R8Discharge carrier keep creation)',
  ],'full-witness-event');
  includes('eventsFor',[
    'if forgotten : keep field = false then',
    'let creation := createR5 carrier keep field forgotten',
    '.createR5 creation :: .dischargeR8 creation (dischargeR8 carrier keep creation) :: eventsFor carrier keep remaining',
    'else eventsFor carrier keep remaining',
  ],'computed-event-pairs');
  require0(block('events').endsWith('eventsFor carrier keep (List.finRange fields)'),'all-forgotten-coordinates');
  require0(block('forgottenCoordinates').endsWith(
    '(List.finRange fields).filter (fun field => !(keep field))'),'exact-forgotten-mask');
  includes('replay',[
    'if (pending ++ createdCoordinates transcript).Nodup then replayPending pending transcript else none',
  ],'whole-trace-unique-identities');
  includes('replayPending',[
    'private def replayPending','if creation.coordinate ∈ pending then none',
    '| [] => none','if first = creation.coordinate then replayPending rest remaining else none',
  ],'fail-closed-pending-order');
  includes('RestoredGain',[
    ': Type where smaller : (restored carrier keep).implementation.gateCount < carrier.implementation.gateCount',
  ],'fully-charged-gain-witness');
  require0(block('gain?').endsWith(
    'if smaller : (restored carrier keep).implementation.gateCount < carrier.implementation.gateCount then some ⟨smaller⟩ else none'),'actual-strict-gain');
  return [...new Set(failures)];
}

test('M251 computes general projection, physical restoration and full-value obligations',async()=>{
  assert.deepEqual(validateSource0(await text0(SOURCE)),[]);
});

test('M251 root, exact theorem-name producers and axiom audit agree',async()=>{
  const [audit,inventorySource,root]=await Promise.all([
    text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean')]);
  for(const name of NAMES){
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item=>item===name).length,1,name);
    assert.equal(inventorySource.split(String.fromCharCode(96)+name+',').length-1,1,name);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),NAMES);
  assert.match(root,/^import PNP\.NANDWireObligationRestoration\s*$/mu);
});

function rejectMutations0(source,mutations) {
  for(const [before,after,category] of mutations){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
}

test('M251 rejects fictional wire values, omitted materializers and weakened physical charge',async()=>{
  await rejectMutations0(await text0(SOURCE),[
    ['if keep field then carrier.source field else .constant false',
      'if keep field then .constant false else carrier.source field','quotient-only-mask'],
    ['(masked carrier keep).normalize','carrier','actual-projection'],
    ['if keep field then .constant false else carrier.source field',
      'if keep field then .constant false else .constant true','actual-hidden-wire-program'],
    ['(hidden carrier keep).normalize','suppliedMaterializer','actual-shared-materializer'],
    ['(missing.source field).substituteInputs (fun input => .input input)',
      '(Source.constant false).substituteInputs (fun input => .input input)','literal-paid-concatenation'],
    ['join (projected carrier keep) (materializer carrier keep) keep',
      'projected carrier keep','actual-full-restoration'],
    ['(materializer carrier keep).implementation.gateCount := rfl',
      '0 := rfl','signature:restored_exact_gate_charge'],
    ['theorem restored_field (carrier : WireCarrier inputs outputs fields)',
      'theorem restored_field (carrier : WireCarrier 2 outputs fields)','signature:restored_field'],
    ['theorem restored_output (carrier : WireCarrier inputs outputs fields)',
      'theorem restored_output (callerCertificate : True) (carrier : WireCarrier inputs outputs fields)',
      'signature:restored_output'],
    ['def materializer (carrier : WireCarrier inputs outputs fields)',
      'def materializer (suppliedObserver : True) (carrier : WireCarrier inputs outputs fields)',
      'shortcut-or-certificate'],
    ['(keep : Fin fields → Bool) : Option (RestoredGain carrier keep) :=\n  if smaller : (restored carrier keep).implementation.gateCount <',
      '(keep : Fin fields → Bool) : Option (RestoredGain carrier keep) :=\n  if smaller : (projected carrier keep).implementation.gateCount <',
      'actual-strict-gain'],
    ['carrier.implementation.gateCount then some ⟨smaller⟩ else none',
      'carrier.implementation.gateCount then none else some ⟨smaller⟩','actual-strict-gain'],
  ]);
});

test('M251 rejects unbound or quotient-only discharges, omitted IDs and reused identities',async()=>{
  await rejectMutations0(await text0(SOURCE),[
    ['forgotten : keep coordinate = false','forgotten : True','bound-creation'],
    ['sourceExact : originalSource = carrier.source coordinate','sourceExact : True','bound-creation'],
    ['originalSource := carrier.source field, sourceExact := rfl',
      'originalSource := .constant false, sourceExact := rfl','computed-creation'],
    ['sourceExact : restoredSource = (restored carrier keep).source creation.coordinate',
      'sourceExact : True','bound-full-discharge'],
    ['fullWitness : ∀ valuation,','fullWitness : ∃ valuation,','bound-full-discharge'],
    ['exact restored_field carrier keep valuation creation.coordinate',
      'exact projected_kept_field carrier keep valuation creation.coordinate','derived-full-witness'],
    ['(witness : R8Discharge carrier keep creation)','(witness : True)','full-witness-event'],
    ['.createR5 creation :: .dischargeR8 creation (dischargeR8 carrier keep creation) ::',
      '.createR5 creation ::','computed-event-pairs'],
    ['eventsFor carrier keep (List.finRange fields)','eventsFor carrier keep []','all-forgotten-coordinates'],
    ['(List.finRange fields).filter (fun field => !(keep field))',
      '(List.finRange fields).filter (fun field => keep field)','exact-forgotten-mask'],
    ['if (pending ++ createdCoordinates transcript).Nodup then',
      'if pending.Nodup then','whole-trace-unique-identities'],
    ['if first = creation.coordinate then replayPending rest remaining else none',
      'replayPending rest remaining','fail-closed-pending-order'],
    ['List (Event carrier keep) :=\n  eventsFor carrier keep (List.finRange fields)',
      'List (Event carrier keep) :=\n  suppliedTrace','all-forgotten-coordinates'],
  ]);
});

test('M251 rejects new assumptions, unaudited declarations and exhaustive semantic shortcuts',async()=>{
  const source=await text0(SOURCE);
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n').includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n').includes('unaudited-form'));
  assert.ok(validateSource0(source+'\ndef extra := referenceMinimum\n').includes('no-semantic-enumeration'));
  assert.ok(validateSource0(source.replace('import PNP.NANDWireCarrier','import PNP.NANDWireCarrier\nimport Unknown.Source')).includes('closed-imports'));
});

test('M251 theorem-head parsing includes complete dependent binders',()=>{
  const declaration='theorem restoration (source : Carrier (fields := fields)) '+
    '(same : source = target) : target = source := same.symm';
  assert.equal(signature0(declaration),declaration.slice(0,declaration.lastIndexOf(' := ')));
  assert.notEqual(signature0(declaration.replace('(same :','(extra : True) (same :')),
    signature0(declaration));
});

test('M251 regressions separate quotient padding, paid restoration and unique full discharge',async()=>{
  const raw=await text0(REGRESSION),regression=compact0(raw);
  assert.deepEqual([...raw.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  for(const token of [
    'single.fieldValue (fun _ => false) 0 = true',
    '(masked single (fun _ => false)).fieldValue (fun _ => false) 0 = false',
    'restored_output carrier keep valuation output','restored_field carrier keep valuation field',
    'restored_exact_gate_charge carrier keep','replay_closed carrier keep',
    'dischargeR8_full_value carrier keep creation valuation',
    'projected single (fun _ => false)','materializer single (fun _ => false)',
    'hiddenQ.implementation.gateCount != 0','hiddenM.implementation.gateCount != 1',
    'paidSingle.implementation.gateCount != 1','(gain? single (fun _ => false)).isSome',
    'sharedResult.implementation.gateCount != 1',
    '(createdCoordinates (events shared (fun _ => false))).map Fin.val != [0, 1]',
    '(dischargedCoordinates (events shared (fun _ => false))).map Fin.val != [0, 1]',
    '(restored duplicates (fun _ => false)).implementation.gateCount != 1',
    '(materializer shared (fun _ => true)).implementation.gateCount != 0',
    '(restored fieldsOnly (fun _ => false)).implementation.gateCount != 1',
    '(restored empty (fun _ => false)).implementation.gateCount != 0',
    'restored freeFields','restored mixed','reordered.fieldValue valuation 1 != !value',
    '(replay [] orphan).isSome','(replay [] duplicate).isSome',
    '(replay [] reused).isSome','(replay [] wrongOrder).isSome',
    '.createR5 first, .dischargeR8 first firstPaid, .createR5 first, .dischargeR8 first firstPaid',
    '#eval show IO Unit from do','throw (IO.userError',
  ])assert.ok(regression.includes(token),token);
  assert.equal([...raw.matchAll(/^#eval\b/gmu)].length,1);
  assert.doesNotMatch(regression,/\b(?:sorry|admit|native_decide|Classical|referenceMinimum|scanEquivalentSizes|allCandidates)\b/u);
});

test('M251 durable workflow retains source checks, exact audit and bounded regressions',async()=>{
  const [packageText,surface,verifier,workflow]=await Promise.all([
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),text0('.github/workflows/lean-bridge.yml')]);
  const auditPath='audits/lean-wire-obligation-restoration0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m251'],'node --test '+auditPath);
  assert.ok(surface.includes("'audit:m251': 'node --test "+auditPath+"'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test '+auditPath));
  for(const path of [auditPath,'docs/lean_wire_obligation_restoration.md'])
    assert.equal(workflow.split("      - '"+path+"'").length-1,2);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M251_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-12-251';
const M251_MILESTONE = 'wire-obligation-restoration';
const M251_HASHES = Object.freeze({
  "PNP.DirectWire.WireObligationRestoration.projected_output": "9db137ff572598f27b8978c1e20592987442afe9518444b13a1a82be7389eafe",
  "PNP.DirectWire.WireObligationRestoration.projected_kept_field": "18eb453392e344b669686f436529edc8eac10935796c5d660dadd58dae0dd27e",
  "PNP.DirectWire.WireObligationRestoration.materializer_forgotten_field": "443dd40f055b1440727c3b6bae6e475ed159bf3fbe5d61093d6730f33d7f5950",
  "PNP.DirectWire.WireObligationRestoration.join_output": "39bf1aac304078048078a936243756c731ef9e036aa97339424f1134457abab9",
  "PNP.DirectWire.WireObligationRestoration.join_kept_field": "2beb641b17d6f90f1029f1c56ea226ba65d1b4a59e8bc22f39c08f9b1cd671e3",
  "PNP.DirectWire.WireObligationRestoration.join_forgotten_field": "dbf92adf17c0520daefcd37b20bdae3868600663f73e69ccfd63479f6018b061",
  "PNP.DirectWire.WireObligationRestoration.restored_output": "f2700308348906c76b750ce766a97d50c2c3e1c59f590ddc475384824b87cd37",
  "PNP.DirectWire.WireObligationRestoration.restored_field": "64df896b2a0483021625f23df9f82a1b4d3316916a5b3e49acdc52fb3300ea24",
  "PNP.DirectWire.WireObligationRestoration.restored_exact_gate_charge": "1dce5aeceb99a472a85441e2e20f95970b141bc335e78f0c6cbf8914ae355196",
  "PNP.DirectWire.WireObligationRestoration.restored_gate_bound": "024165d580947e53951cc622e0da244a7b8b1c4073546afb4688274afa4bfb25",
  "PNP.DirectWire.WireObligationRestoration.created_exact": "4e4f8fd06ec135760827ee6c7912f228bacb3c130c6265ca4f6a613e24cf947b",
  "PNP.DirectWire.WireObligationRestoration.discharged_exact": "5768997e5f284d7fcd7f257d1c98475dd57c5c94c0183077411b26e656173b77",
  "PNP.DirectWire.WireObligationRestoration.mem_forgottenCoordinates_iff": "fd19fd4184326b9f8b1a2d2c366ae70cc639af00735742284e1027676d54a47a",
  "PNP.DirectWire.WireObligationRestoration.creation_iff": "f1b7532d0e888e57ce1b16f0ddce0fb03687dd335558c639939cde0654bcc0a0",
  "PNP.DirectWire.WireObligationRestoration.discharge_iff": "4ae3a648df20849a27c29b2ad75f4dc2493b20b56ee7a970431a22d427cd7bab",
  "PNP.DirectWire.WireObligationRestoration.replay_closed": "fe9eebebe76bf2c9468b1c74b8283cac786fe19c63c2b7e66eb11b38bbb2d842",
  "PNP.DirectWire.WireObligationRestoration.dischargeR8_full_value": "ece2b699fc6d36735d7a62f772db312386c33ff388e1c0ed2b2a1ecba9bac05f",
  "PNP.DirectWire.WireObligationRestoration.gain?_isSome_iff": "d0d8ddb1749b477af29863f43640eb7241a06445a9db2aa09f661b1fdaf0ad20",
  "PNP.DirectWire.WireObligationRestoration.gain_checked": "6371bbe19d03e7455d308a83c48154ad5a8e97f39508b74b05e040314d9d877c",
  "PNP.DirectWire.WireObligationRestoration.created_nodup": "c13d5f7f593ff543a7d6367f4513a07b09fac14a1bd804494d2b4f58418608ae",
  "PNP.DirectWire.WireObligationRestoration.discharged_nodup": "de37f4291ba5722db2e4309d9d837e4ed439a819ee82f6fb1fc131be2b87954e",
  "PNP.DirectWire.WireObligationRestoration.replay_rejects_duplicate_ids": "e946fbe19d83be47720897f76d693bace11654c868189c7bbf1ef43ddcf679e6"
});
const M251_STATUS_FIELDS = Object.freeze({
  "leanWireObligationRestorationFormalized": true,
  "leanWireObligationRestorationAxiomAuditPassed": true,
  "leanWireObligationRestorationAuditedDeclarationCount": 22,
  "leanWireObligationRestorationProjectedOutputTheorem": "PNP.DirectWire.WireObligationRestoration.projected_output",
  "leanWireObligationRestorationProjectedKeptFieldTheorem": "PNP.DirectWire.WireObligationRestoration.projected_kept_field",
  "leanWireObligationRestorationMaterializerForgottenFieldTheorem": "PNP.DirectWire.WireObligationRestoration.materializer_forgotten_field",
  "leanWireObligationRestorationJoinOutputTheorem": "PNP.DirectWire.WireObligationRestoration.join_output",
  "leanWireObligationRestorationJoinKeptFieldTheorem": "PNP.DirectWire.WireObligationRestoration.join_kept_field",
  "leanWireObligationRestorationJoinForgottenFieldTheorem": "PNP.DirectWire.WireObligationRestoration.join_forgotten_field",
  "leanWireObligationRestorationRestoredOutputTheorem": "PNP.DirectWire.WireObligationRestoration.restored_output",
  "leanWireObligationRestorationRestoredFieldTheorem": "PNP.DirectWire.WireObligationRestoration.restored_field",
  "leanWireObligationRestorationExactGateChargeTheorem": "PNP.DirectWire.WireObligationRestoration.restored_exact_gate_charge",
  "leanWireObligationRestorationGateBoundTheorem": "PNP.DirectWire.WireObligationRestoration.restored_gate_bound",
  "leanWireObligationRestorationCreatedCoordinatesTheorem": "PNP.DirectWire.WireObligationRestoration.created_exact",
  "leanWireObligationRestorationDischargedCoordinatesTheorem": "PNP.DirectWire.WireObligationRestoration.discharged_exact",
  "leanWireObligationRestorationForgottenMaskTheorem": "PNP.DirectWire.WireObligationRestoration.mem_forgottenCoordinates_iff",
  "leanWireObligationRestorationCreationMembershipTheorem": "PNP.DirectWire.WireObligationRestoration.creation_iff",
  "leanWireObligationRestorationDischargeMembershipTheorem": "PNP.DirectWire.WireObligationRestoration.discharge_iff",
  "leanWireObligationRestorationClosedReplayTheorem": "PNP.DirectWire.WireObligationRestoration.replay_closed",
  "leanWireObligationRestorationFullDischargeValueTheorem": "PNP.DirectWire.WireObligationRestoration.dischargeR8_full_value",
  "leanWireObligationRestorationGainIffTheorem": "PNP.DirectWire.WireObligationRestoration.gain?_isSome_iff",
  "leanWireObligationRestorationCheckedGainTheorem": "PNP.DirectWire.WireObligationRestoration.gain_checked",
  "leanWireObligationRestorationCreationUniquenessTheorem": "PNP.DirectWire.WireObligationRestoration.created_nodup",
  "leanWireObligationRestorationDischargeUniquenessTheorem": "PNP.DirectWire.WireObligationRestoration.discharged_nodup",
  "leanWireObligationRestorationDuplicateIdentityRejectionTheorem": "PNP.DirectWire.WireObligationRestoration.replay_rejects_duplicate_ids",
  "leanWireObligationRestorationFullManuscriptCarrierDerived": false,
  "leanWireObligationRestorationCompleteObligationCalculusProved": false,
  "leanWireObligationRestorationGeneralDependencyDAGProved": false,
  "leanWireObligationRestorationCompletePackageEProved": false,
  "leanWireObligationRestorationPolynomialRuntimeProved": false,
  "leanWireObligationRestorationScope": "all-finite-computational-wire-fields-actual-quotient-projection-shared-materializer-full-value-restoration-exact-gate-charge-derived-r5-full-r8-coordinate-ledger-whole-trace-unique-identities-no-full-manuscript-calculus-or-polynomial-runtime"
});
const M251_AXIOMS = Object.freeze({
  "PNP.DirectWire.WireObligationRestoration.projected_output": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.projected_kept_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.materializer_forgotten_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.join_output": [],
  "PNP.DirectWire.WireObligationRestoration.join_kept_field": [],
  "PNP.DirectWire.WireObligationRestoration.join_forgotten_field": [],
  "PNP.DirectWire.WireObligationRestoration.restored_output": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.restored_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.restored_exact_gate_charge": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.restored_gate_bound": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.created_exact": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.discharged_exact": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.mem_forgottenCoordinates_iff": [
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.creation_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.discharge_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.replay_closed": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.dischargeR8_full_value": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.gain?_isSome_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.gain_checked": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.created_nodup": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.discharged_nodup": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireObligationRestoration.replay_rejects_duplicate_ids": [
    "Quot.sound",
    "propext"
  ]
});

const M251_MODULES = Object.freeze({
  "PNP.DirectWire.WireObligationRestoration.projected_output": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.projected_kept_field": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.materializer_forgotten_field": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.join_output": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.join_kept_field": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.join_forgotten_field": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.restored_output": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.restored_field": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.restored_exact_gate_charge": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.restored_gate_bound": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.created_exact": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.discharged_exact": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.mem_forgottenCoordinates_iff": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.creation_iff": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.discharge_iff": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.replay_closed": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.dischargeR8_full_value": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.gain?_isSome_iff": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.gain_checked": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.created_nodup": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.discharged_nodup": "PNP.NANDWireObligationRestoration",
  "PNP.DirectWire.WireObligationRestoration.replay_rejects_duplicate_ids": "PNP.NANDWireObligationRestoration"
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

test('M251 compiled wire-obligation restoration interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M251_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M251_COORDINATE)
    assert.equal(map.coordinate, M251_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M251_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, M251_MODULES[name], name);
      assert.deepEqual(declaration.axioms, M251_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M251_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M251_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M251_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "computational lost-wire slice",
  "keep mask is an input",
  "Quotient padding is not full-field agreement",
  "output-size fact",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M251 publication rejects weakened, supplied, assumption-backed and widened restoration-calculus substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M251_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M251_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = 'PNP.DirectWire.WireObligationRestoration.restored_field';
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M251_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M251_MILESTONE
    ? {...row, nonClaim:'Restoration proves the complete obligation calculus, arbitrary dependency DAGs and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M251 adds computational restoration coverage without full-calculus, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M251_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "computational lost-wire restoration edge",
  "globally unique creation IDs",
  "does not complete the manuscript carrier",
  "not a total encoded-size polynomial execution theorem",
  "No fixed load-bearing checkpoint changes state"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M251_COORDINATE) return;
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

test('M251 current summaries distinguish lost-wire restoration from full-calculus and global completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_wire_obligation_restoration.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "No observer, materializer, discharge trace or correctness certificate is supplied",
  "Quotient padding is not full-field agreement",
  "A shared materializer is paid once",
  "an ID cannot be reused after it has been discharged",
  "Runtime execution is test evidence, not theorem authority",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-12-computed-wire-obligation-restoration.md'));
  assert.match(plan, /Publication decision: defer PNPLabs(?:[.,]|$)/u);
  if (progress.asOfCoordinate !== M251_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_wire_obligation_restoration.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
