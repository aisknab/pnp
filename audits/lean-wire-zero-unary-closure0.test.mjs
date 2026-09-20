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

const SOURCE = 'lean/PNP/NANDWireZeroUnaryClosure.lean';
const AUDIT = 'lean-audit/PNPWireZeroUnaryClosureAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPWireZeroUnaryClosure.lean';
const NAMES = [
  "PNP.DirectWire.WireZeroUnaryClosure.whole_selected",
  "PNP.DirectWire.WireZeroUnaryClosure.whole_exterior",
  "PNP.DirectWire.WireZeroUnaryClosure.whole_gateCount",
  "PNP.DirectWire.WireZeroUnaryClosure.whole_not_proper",
  "PNP.DirectWire.WireZeroUnaryClosure.all_gates_of_zero_exterior",
  "PNP.DirectWire.WireZeroUnaryClosure.WholeGain.checked",
  "PNP.DirectWire.WireZeroUnaryClosure.wholeGain_isSome_iff",
  "PNP.DirectWire.WireZeroUnaryClosure.wholeGain_complete",
  "PNP.DirectWire.WireZeroUnaryClosure.Gain.full_field",
  "PNP.DirectWire.WireZeroUnaryClosure.Gain.branch_boundary",
  "PNP.DirectWire.WireZeroUnaryClosure.Gain.exact_accounting",
  "PNP.DirectWire.WireZeroUnaryClosure.nextGain_isSome_iff",
  "PNP.DirectWire.WireZeroUnaryClosure.nextGain_none_iff",
  "PNP.DirectWire.WireZeroUnaryClosure.nextGain_complete",
  "PNP.DirectWire.WireZeroUnaryClosure.nextGain_none_excludes",
  "PNP.DirectWire.WireZeroUnaryClosure.normalization_accounting",
  "PNP.DirectWire.WireZeroUnaryClosure.normalization_iterations",
  "PNP.DirectWire.WireZeroUnaryClosure.Trace.checked",
  "PNP.DirectWire.WireZeroUnaryClosure.Trace.searchCalls_le",
  "PNP.DirectWire.WireZeroUnaryClosure.run_checked",
  "PNP.DirectWire.WireZeroUnaryClosure.run_of_stopped",
  "PNP.DirectWire.WireZeroUnaryClosure.run_idempotent",
  "PNP.DirectWire.WireZeroUnaryClosure.run_no_smaller_zeroUnary",
  "PNP.DirectWire.WireZeroUnaryClosure.run_referenceMinimum",
  "PNP.DirectWire.WireZeroUnaryClosure.run_residualSlack",
  "PNP.DirectWire.WireZeroUnaryClosure.run_gainIterations_le_residualSlack",
  "PNP.DirectWire.WireZeroUnaryClosure.run_searchCalls_le_residualSlack"
];
const SPECS = [
  {
    "kind": "main",
    "path": "lean/PNP/NANDWireZeroUnaryClosure.lean",
    "prefix": "PNP.DirectWire.WireZeroUnaryClosure.",
    "imports": [
      "PNP.NANDWireUnarySupportSearch"
    ],
    "signatures": {
      "whole_selected": "theorem whole_selected (carrier : WireCarrier inputs outputs fields) : terminalGateSelected (wholeRecords carrier) = (fun _ => true)",
      "whole_exterior": "theorem whole_exterior (carrier : WireCarrier inputs outputs fields) : exteriorCharge carrier (wholeRecords carrier) = 0",
      "whole_gateCount": "theorem whole_gateCount (carrier : WireCarrier inputs outputs fields) : (pulled carrier (wholeRecords carrier)).gateCount = carrier.implementation.gateCount",
      "whole_not_proper": "theorem whole_not_proper (carrier : WireCarrier inputs outputs fields) : ¬ (pulled carrier (wholeRecords carrier)).gateCount < carrier.implementation.gateCount",
      "all_gates_of_zero_exterior": "theorem all_gates_of_zero_exterior (carrier : WireCarrier inputs outputs fields) (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0)) (empty : exteriorCharge carrier records = 0) : terminalGateSelected records = (fun _ => true)",
      "WholeGain.checked": "theorem WholeGain.checked {carrier : WireCarrier inputs outputs fields} (gain : WholeGain carrier) : exteriorCharge carrier (wholeRecords carrier) = 0 ∧ StrictEquivalentGain carrier.implementation gain.expanded.implementation ∧ (∀ valuation field, gain.expanded.fieldValue valuation field = carrier.fieldValue valuation field) ∧ gain.expanded.implementation.gateCount = (replacement carrier (wholeRecords carrier) gain.small).gateCount",
      "wholeGain_isSome_iff": "theorem wholeGain_isSome_iff (carrier : WireCarrier inputs outputs fields) : (wholeGain carrier).isSome = true ↔ ∃ small : (pulled carrier (wholeRecords carrier)).boundary.length ≤ 1, (replacement carrier (wholeRecords carrier) small).gateCount < (pulled carrier (wholeRecords carrier)).gateCount",
      "wholeGain_complete": "theorem wholeGain_complete (carrier : WireCarrier inputs outputs fields) (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0)) (small : (pulled carrier records).boundary.length ≤ 1) (empty : exteriorCharge carrier records = 0) (other : Implementation (pulled carrier records).boundary.length (pulled carrier records).interface.length) (sameOpen : other.candidate.semantics = (pulled carrier records).extractedCandidate.semantics) (smaller : other.gateCount < (pulled carrier records).gateCount) : (wholeGain carrier).isSome = true",
      "Gain.full_field": "theorem Gain.full_field {carrier : WireCarrier inputs outputs fields} (gain : Gain carrier) (valuation : Valuation inputs) (field : Fin fields) : gain.expanded.fieldValue valuation field = carrier.fieldValue valuation field",
      "Gain.branch_boundary": "theorem Gain.branch_boundary {carrier : WireCarrier inputs outputs fields} (gain : Gain carrier) : match gain with | .proper result => 0 < exteriorCharge carrier result.records | .wholeSpan _ => exteriorCharge carrier (wholeRecords carrier) = 0",
      "Gain.exact_accounting": "theorem Gain.exact_accounting {carrier : WireCarrier inputs outputs fields} (gain : Gain carrier) : gain.expanded.implementation.gateCount + gain.savedGates = carrier.implementation.gateCount ∧ 0 < gain.savedGates",
      "nextGain_isSome_iff": "theorem nextGain_isSome_iff (carrier : WireCarrier inputs outputs fields) : (nextGain carrier).isSome = true ↔ (WireUnarySupportSearch.findGain carrier).isSome = true ∨ (wholeGain carrier).isSome = true",
      "nextGain_none_iff": "theorem nextGain_none_iff (carrier : WireCarrier inputs outputs fields) : nextGain carrier = none ↔ WireUnarySupportSearch.findGain carrier = none ∧ wholeGain carrier = none",
      "nextGain_complete": "theorem nextGain_complete (carrier : WireCarrier inputs outputs fields) (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0)) (small : (pulled carrier records).boundary.length ≤ 1) (other : Implementation (pulled carrier records).boundary.length (pulled carrier records).interface.length) (sameOpen : other.candidate.semantics = (pulled carrier records).extractedCandidate.semantics) (smaller : other.gateCount < (pulled carrier records).gateCount) : (nextGain carrier).isSome = true",
      "nextGain_none_excludes": "theorem nextGain_none_excludes (carrier : WireCarrier inputs outputs fields) (notFound : nextGain carrier = none) (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0)) (small : (pulled carrier records).boundary.length ≤ 1) (other : Implementation (pulled carrier records).boundary.length (pulled carrier records).interface.length) (sameOpen : other.candidate.semantics = (pulled carrier records).extractedCandidate.semantics) : (pulled carrier records).gateCount ≤ other.gateCount",
      "normalization_accounting": "theorem normalization_accounting (carrier : WireCarrier inputs outputs fields) : carrier.normalize.implementation.gateCount + normalizationSaved carrier = carrier.implementation.gateCount",
      "normalization_iterations": "theorem normalization_iterations (carrier : WireCarrier inputs outputs fields) : normalizationIterations carrier ≤ normalizationSaved carrier",
      "Trace.checked": "theorem Trace.checked {current final : WireCarrier inputs outputs fields} (trace : Trace current final) : Equivalent final.implementation.candidate.program final.implementation.candidate.directWireWord current.implementation.candidate.program current.implementation.candidate.directWireWord ∧ (∀ valuation field, final.fieldValue valuation field = current.fieldValue valuation field) ∧ PhysicalNormalizationQuiescent final.exposed ∧ nextGain final = none ∧ final.implementation.gateCount + trace.savedGates = current.implementation.gateCount ∧ trace.gainIterations ≤ trace.savedGates",
      "Trace.searchCalls_le": "theorem Trace.searchCalls_le {current final : WireCarrier inputs outputs fields} (trace : Trace current final) : trace.searchCalls ≤ trace.gainIterations + 1",
      "run_checked": "theorem run_checked (carrier : WireCarrier inputs outputs fields) : let execution := run carrier Equivalent execution.result.implementation.candidate.program execution.result.implementation.candidate.directWireWord carrier.implementation.candidate.program carrier.implementation.candidate.directWireWord ∧ (∀ valuation field, execution.result.fieldValue valuation field = carrier.fieldValue valuation field) ∧ PhysicalNormalizationQuiescent execution.result.exposed ∧ nextGain execution.result = none ∧ execution.result.implementation.gateCount + execution.trace.savedGates = carrier.implementation.gateCount ∧ execution.trace.gainIterations ≤ execution.trace.savedGates",
      "run_of_stopped": "theorem run_of_stopped (carrier : WireCarrier inputs outputs fields) (quiet : PhysicalNormalizationQuiescent carrier.exposed) (absent : nextGain carrier = none) : (run carrier).result = carrier",
      "run_idempotent": "theorem run_idempotent (carrier : WireCarrier inputs outputs fields) : (run (run carrier).result).result = (run carrier).result",
      "run_no_smaller_zeroUnary": "theorem run_no_smaller_zeroUnary (carrier : WireCarrier inputs outputs fields) (records : List (TerminalPrimitiveRecord inputs (run carrier).result.implementation.gateCount (outputs + fields) 0)) (small : (pulled (run carrier).result records).boundary.length ≤ 1) (other : Implementation (pulled (run carrier).result records).boundary.length (pulled (run carrier).result records).interface.length) (sameOpen : other.candidate.semantics = (pulled (run carrier).result records).extractedCandidate.semantics) : (pulled (run carrier).result records).gateCount ≤ other.gateCount",
      "run_referenceMinimum": "theorem run_referenceMinimum (carrier : WireCarrier inputs outputs fields) : referenceMinimum (run carrier).result.implementation = referenceMinimum carrier.implementation",
      "run_residualSlack": "theorem run_residualSlack (carrier : WireCarrier inputs outputs fields) : residualSlack carrier.implementation = residualSlack (run carrier).result.implementation + (run carrier).trace.savedGates",
      "run_gainIterations_le_residualSlack": "theorem run_gainIterations_le_residualSlack (carrier : WireCarrier inputs outputs fields) : (run carrier).trace.gainIterations ≤ residualSlack carrier.implementation",
      "run_searchCalls_le_residualSlack": "theorem run_searchCalls_le_residualSlack (carrier : WireCarrier inputs outputs fields) : (run carrier).trace.searchCalls ≤ residualSlack carrier.implementation + 1"
    },
    "heads": [
      "wholeRecords",
      "whole_selected",
      "whole_exterior",
      "whole_gateCount",
      "whole_not_proper",
      "all_gates_of_zero_exterior",
      "WholeGain",
      "WholeGain.expanded",
      "WholeGain.strictGain",
      "WholeGain.checked",
      "wholeGain",
      "wholeGain_isSome_iff",
      "wholeGain_complete",
      "Gain",
      "Gain.expanded",
      "Gain.strictGain",
      "Gain.full_field",
      "Gain.branch_boundary",
      "Gain.savedGates",
      "Gain.exact_accounting",
      "nextGain",
      "nextGain_isSome_iff",
      "nextGain_none_iff",
      "nextGain_complete",
      "nextGain_none_excludes",
      "normalizationSaved",
      "normalizationIterations",
      "normalization_accounting",
      "normalization_iterations",
      "Trace",
      "Trace.savedGates",
      "Trace.gainIterations",
      "Trace.searchCalls",
      "Trace.checked",
      "Trace.searchCalls_le",
      "Execution",
      "run",
      "run_checked",
      "run_of_stopped",
      "run_idempotent",
      "run_no_smaller_zeroUnary",
      "run_referenceMinimum",
      "run_residualSlack",
      "run_gainIterations_le_residualSlack",
      "run_searchCalls_le_residualSlack"
    ]
  }
];
const SIGNATURES = SPECS[0].signatures;
const HEADS = SPECS[0].heads;

const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = value => stripLeanCommentsAndStrings0(value).replace(/\s+/gu,' ').trim();
function block0(source,name) {
  const stripped=stripLeanCommentsAndStrings0(source);
  const boundaries=[...stripped.matchAll(/^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*(?:(?:def|theorem|inductive|structure|abbrev)[ \t]+([^\s({:]+)|variable\b|namespace\b|end\b)/gmu)];
  const index=boundaries.findIndex(item=>item[1]===name);
  return index<0?'':compact0(source.slice(boundaries[index].index,boundaries[index+1]?.index??source.length));
}
function signature0(block) {
  let depth=0, pendingLets=0;
  for(let index=0;index<block.length-1;index++){
    if('({['.includes(block[index]))depth++;
    else if(')}]'.includes(block[index]))depth--;
    if(depth!==0)continue;
    // A let assignment in the theorem type is not its proof separator.
    if(block.startsWith('let ',index) &&
        (index===0 || !/[\p{L}\p{N}_'.]/u.test(block[index-1])))pendingLets++;
    if(block.slice(index,index+2)===':='){
      if(pendingLets>0){pendingLets--;index++;continue;}
      return block.slice(0,index).trim();
    }
  }
  return '';
}
function validateSource0(source,spec) {
  const failures=[], require0=(condition,category)=>{if(!condition)failures.push(category);};
  const clean=compact0(source),block=name=>block0(source,name);
  const includes=(name,tokens,category)=>require0(tokens.every(token=>block(name).includes(token)),category);
  require0(!hasLeanAssumptionDeclaration0(source),'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source),'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|callerCertificate|suppliedFamily|suppliedResult|suppliedOptimizer)\b/u.test(clean),'shortcut-or-certificate');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]))===
    JSON.stringify(spec.imports),'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name))===
    JSON.stringify(spec.heads),'public-interface');
  for(const [name,signature] of Object.entries(spec.signatures))
    require0(signature0(block(name))===signature,'signature:'+name);
  require0(clean.includes('variable {inputs outputs fields : Nat}'),'unbounded-dimensions');
  for(const match of stripLeanCommentsAndStrings0(source).matchAll(/^def ([A-Za-z0-9_'.]+)/gmu))
    require0(!/\b(?:allSubsets|allCandidates|allBoolTuples|referenceMinimum|scanEquivalentSizes|terminalFullProfileMinimum)\b/u.test(block(match[1])),
      'no-executable-reference-minimum');
  require0(block('wholeRecords').endsWith('WireUnarySupportSearch.gateRecords (fun _ => true)'),
    'source-derived-whole-support');
  includes('wholeGain',[
    'def wholeGain (carrier : WireCarrier inputs outputs fields) : Option (WholeGain carrier) :=',
    'if small : (pulled carrier (wholeRecords carrier)).boundary.length ≤ 1 then',
    'if smaller : (replacement carrier (wholeRecords carrier) small).gateCount <',
    '(pulled carrier (wholeRecords carrier)).gateCount then some ⟨small, smaller⟩ else none else none',
  ],'actual-strict-whole-search');
  require0(block('WholeGain.expanded').endsWith(
    'WireUnaryArbitrarySupport.expanded carrier (wholeRecords carrier) gain.small'),
    'actual-whole-expansion');
  includes('wholeGain_complete',[
    'replacement_minimal carrier records small other sameOpen',
    'all_gates_of_zero_exterior carrier records empty',
    'extractTerminalSupport_eq_of_gateSelected_eq',
    '(wholeGain_isSome_iff carrier).2 wholeProperty',
  ],'whole-completeness');
  includes('Gain',[
    '| proper (result : WireUnarySupportSearch.GainResult carrier)',
    '| wholeSpan (result : WholeGain carrier)',
  ],'typed-branch-distinction');
  includes('Gain.branch_boundary',[
    '| .proper result => 0 < exteriorCharge carrier result.records',
    '| .wholeSpan _ => exteriorCharge carrier (wholeRecords carrier) = 0',
  ],'proper-whole-boundary');
  require0(block('nextGain')===
    'def nextGain (carrier : WireCarrier inputs outputs fields) : Option (Gain carrier) := match WireUnarySupportSearch.findGain carrier with | some result => some (.proper result) | none => (wholeGain carrier).map Gain.wholeSpan',
    'carrier-only-combined-search');
  includes('nextGain_complete',[
    'by_cases proper : 0 < exteriorCharge carrier records',
    'WireUnarySupportSearch.findGain_complete',
    'wholeGain_complete carrier records small empty other sameOpen smaller',
  ],'all-support-completeness');
  includes('normalizationSaved',['runPhysicalNormalization carrier.exposed','trace.savedGates'],
    'actual-normalization-saving');
  includes('Trace',[
    '| done (current : WireCarrier inputs outputs fields)',
    '(stopped : nextGain current.normalize = none)',
    '| step (current : WireCarrier inputs outputs fields)',
    '(gain : Gain current.normalize)',
    '(found : nextGain current.normalize = some gain)',
    '(tail : Trace gain.expanded final)',
  ],'actual-typed-trace');
  includes('Trace.savedGates',[
    'normalizationSaved current','gain.savedGates','tail.savedGates',
  ],'exact-trace-saving');
  includes('Trace.gainIterations',[
    'normalizationIterations current','1 + tail.gainIterations',
  ],'actual-trace-iterations');
  includes('Trace.checked',[
    'gain.full_field valuation field','normalization_accounting current',
    'normalization_iterations current',
  ],'composed-trace-evidence');
  includes('run',[
    'def run (current : WireCarrier inputs outputs fields) : Execution current :=',
    'match found : nextGain current.normalize with',
    'result := current.normalize','trace := .done current found',
    'let tail := run gain.expanded','result := tail.result',
    'trace := .step current gain found tail.trace',
    'termination_by current.implementation.gateCount',
    'Nat.lt_of_lt_of_le gain.strictGain.smaller normalBound',
  ],'computed-restarting-closure');
  require0(block('run_checked').endsWith('(run carrier).trace.checked'),'actual-final-trace');
  includes('run_idempotent',[
    'run_of_stopped _ (run_checked carrier).2.2.1 (run_checked carrier).2.2.2.1',
  ],'common-fixed-point');
  includes('run_no_smaller_zeroUnary',[
    'nextGain_none_excludes _ (run_checked carrier).2.2.2.1 records small other sameOpen',
  ],'scoped-final-absence');
  includes('run_referenceMinimum',[
    'referenceMinimum_invariant _ _ (run_checked carrier).1',
  ],'semantic-only-reference');
  includes('run_residualSlack',[
    '(run_checked carrier).2.2.2.2.1','referenceMinimum_le_target',
    'run_referenceMinimum carrier','unfold residualSlack',
  ],'exact-slack-accounting');
  return [...new Set(failures)];
}
const mainSpec=SPECS.find(spec=>spec.kind==='main');
function rejectMutations0(source,mutations) {
  for(const [before,after,category] of mutations) {
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after),mainSpec).includes(category),category);
  }
}
test('M259 source signatures retain the full let-bound theorem target',async()=>{
  const target='theorem probe (defaulted : Nat := 0) : let witness := (let inner := defaulted; inner); witness = defaulted';
  assert.equal(signature0(target+' := by rfl'),target);
  const chained='theorem probe : let left := 0; let right := left; right = left';
  assert.equal(signature0(chained+' := by let ignored := 0; rfl'),chained);
  assert.equal(signature0('theorem incomplete : let witness := 0'),'');
  const actual=signature0(block0(await text0(SOURCE),'run_checked'));
  for(const token of ['let execution := run carrier','∀ valuation field',
    'PhysicalNormalizationQuiescent execution.result.exposed','nextGain execution.result = none',
    'execution.trace.gainIterations ≤ execution.trace.savedGates'])assert.ok(actual.includes(token),token);
});

test('M259 has closed general computed zero/unary descent-closure interfaces',async()=>{
  assert.deepEqual(validateSource0(await text0(SOURCE),mainSpec),[]);
});
test('M259 root, exact theorem-name producers and axiom audit agree',async()=>{
  const [audit,inventory,root]=await Promise.all([
    text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean')]);
  for(const name of NAMES) {
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item=>item===name).length,1,name);
    assert.equal(inventory.split(String.fromCharCode(96)+name+',').length-1,1,name);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),NAMES);
  assert.match(root,/^import PNP\.NANDWireZeroUnaryClosure\s*$/mu);
});
test('M259 rejects supplied whole supports, nonstrict descent and invented expansion',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['WireUnarySupportSearch.gateRecords (fun _ => true)','suppliedFamily','source-derived-whole-support'],
    ['if smaller : (replacement carrier (wholeRecords carrier) small).gateCount <',
      'if smaller : (replacement carrier (wholeRecords carrier) small).gateCount ≤','actual-strict-whole-search'],
    ['WireUnaryArbitrarySupport.expanded carrier (wholeRecords carrier) gain.small',
      'suppliedResult','actual-whole-expansion'],
    ['all_gates_of_zero_exterior carrier records empty','callerCertificate','whole-completeness'],
  ]);
});
test('M259 rejects conflating proper R7 gains with whole-span residual descents',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['| wholeSpan (result : WholeGain carrier)','| wholeSpan (result : WireUnarySupportSearch.GainResult carrier)',
      'typed-branch-distinction'],
    ['| .wholeSpan _ => exteriorCharge carrier (wholeRecords carrier) = 0',
      '| .wholeSpan _ => 0 < exteriorCharge carrier (wholeRecords carrier)','proper-whole-boundary'],
    ['| none => (wholeGain carrier).map Gain.wholeSpan','| none => none','carrier-only-combined-search'],
    ['wholeGain_complete carrier records small empty other sameOpen smaller',
      'callerCertificate','all-support-completeness'],
  ]);
});
test('M259 rejects supplied stopping, fabricated traces and one-pass execution',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['(stopped : nextGain current.normalize = none)','(stopped : True)','actual-typed-trace'],
    ['(found : nextGain current.normalize = some gain)','(found : True)','actual-typed-trace'],
    ['let tail := run gain.expanded','let tail := suppliedResult','computed-restarting-closure'],
    ['trace := .step current gain found tail.trace','trace := suppliedResult','computed-restarting-closure'],
    ['termination_by current.implementation.gateCount','termination_by 0','computed-restarting-closure'],
    ['Nat.lt_of_lt_of_le gain.strictGain.smaller normalBound','callerCertificate','computed-restarting-closure'],
  ]);
});
test('M259 rejects weakened full fields, incorrect charge and unbound final evidence',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['(∀ valuation field, execution.result.fieldValue valuation field =',
      '(∃ valuation field, execution.result.fieldValue valuation field =','signature:run_checked'],
    ['execution.result.implementation.gateCount + execution.trace.savedGates =',
      'execution.result.implementation.gateCount + 2 * execution.trace.savedGates =','signature:run_checked'],
    ['(run carrier).trace.checked','callerCertificate','actual-final-trace'],
    ['run_of_stopped _ (run_checked carrier).2.2.1 (run_checked carrier).2.2.2.1',
      'callerCertificate','common-fixed-point'],
  ]);
});
test('M259 rejects globalizing the scoped absence or executing a reference minimum',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['(pulled (run carrier).result records).gateCount ≤ other.gateCount',
      'other.gateCount ≤ (pulled (run carrier).result records).gateCount','signature:run_no_smaller_zeroUnary'],
    ['nextGain_none_excludes _ (run_checked carrier).2.2.2.1 records small other sameOpen',
      'callerCertificate','scoped-final-absence'],
    ['referenceMinimum_invariant _ _ (run_checked carrier).1',
      'callerCertificate','semantic-only-reference'],
  ]);
  const source=await text0(SOURCE);
  assert.ok(validateSource0(source+'\ndef unauthorized := referenceMinimum\n',mainSpec)
    .includes('no-executable-reference-minimum'));
  assert.ok(validateSource0(source+'\ndef unauthorized := allSubsets\n',mainSpec)
    .includes('no-executable-reference-minimum'));
});
test('M259 rejects assumptions, unaudited declarations and caller supplied optimizers',async()=>{
  const source=await text0(SOURCE);
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n',mainSpec).includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n',mainSpec).includes('unaudited-form'));
  assert.ok(validateSource0(source+'\ndef unauthorized := suppliedOptimizer\n',mainSpec)
    .includes('shortcut-or-certificate'));
});
test('M259 regression retains bounded restart, full-field and nonminimum stopping cases',async()=>{
  const source=await text0(REGRESSION);
  assert.match(source,/^import PNP\s*$/mu);
  for(const name of ['empty-dimensions','free-ordered-fields','two-boundary-nand','minimal-negation',
    'whole-span-tautology','whole-span-double-negation','proper-tautology-exterior-field',
    'hidden-selected-negation','sharing-then-proper-gain','proper-then-whole-span',
    'gain-restarts-constant-propagation','no-ordinary-outputs','constant-normalization-only',
    'dead-support-normalization-only','nonminimum-common-fixed-point'])
    assert.ok(source.includes('"'+name+'"'),name);
  for(const token of ['inputs > 3 || outputs > 2 || fields > 3 || gates > 4',
    'List.range (2 ^ finalGates)','strictEquivalentGainBool_sound (by decide)',
    '0 < residualSlack nonminimum.implementation','assertQuiet final',
    'def unusedInputs : WireCarrier 64 1 0','for value in [false, true]',
    'execution.trace.searchCalls != expectedBranches.length + 1',
    'M259_COMPUTED_ZERO_UNARY_CLOSURE_RUNTIME_FIXTURES_GREEN'])
    assert.ok(source.includes(token),token);
  assert.doesNotMatch(source,/#eval!|\bnative_decide\b/u);
});
test('M259 durable workflow retains explicit-root audit, bounded regressions and compact triggers',async()=>{
  const workflow=await text0('.github/workflows/lean-bridge.yml');
  assert.ok(workflow.includes('Audit computed full-field zero/unary descent closure'));
  assert.ok(workflow.includes('node --test audits/lean-wire-zero-unary-closure0.test.mjs'));
  assert.ok(workflow.includes('lake env lean -DwarningAsError=true '+AUDIT));
  assert.ok(workflow.includes('lake env lean -DwarningAsError=true '+REGRESSION));
  for(const name of NAMES)assert.ok(workflow.includes('"'+name+'"'),name);
  for(const pattern of ['audits/lean-*.test.mjs','docs/lean_*.md'])
    assertLeanWorkflowPathCoverage0(workflow, pattern);
});

const M259_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-13-259';
const M259_MILESTONE = 'wire-zero-unary-closure';
const M259_HASHES = Object.freeze({
  "PNP.DirectWire.WireZeroUnaryClosure.whole_selected": "627ed2af0a291160959dfdfdffef55c50e37a7cfd105a90ad442f14a6a3316b3",
  "PNP.DirectWire.WireZeroUnaryClosure.whole_exterior": "7708c145c0c2744c9e1ffad5ae437c6cbb5c3c25e41106882e907d314f02920a",
  "PNP.DirectWire.WireZeroUnaryClosure.whole_gateCount": "8ba65817e6cd4204b11dea40084855a5d206734a7936074da29009a21e5b89dd",
  "PNP.DirectWire.WireZeroUnaryClosure.whole_not_proper": "9261edea78fb386bb0d9f2a27d289ee811466240faabeac73edd53b304e252b1",
  "PNP.DirectWire.WireZeroUnaryClosure.all_gates_of_zero_exterior": "f6e0a6a8c942babe9a6c4a2c122847d9c0cb579c0a95f39cf641d0ed35ee8c8c",
  "PNP.DirectWire.WireZeroUnaryClosure.WholeGain.checked": "49101e38b6bd44729b79970b09a8dbbbdbb9f08e2ab737bed58fd85c6899343e",
  "PNP.DirectWire.WireZeroUnaryClosure.wholeGain_isSome_iff": "b076fb85cd52e4ef7e1c9912fafea8239292188b40c94d3a0be83f5f6c258170",
  "PNP.DirectWire.WireZeroUnaryClosure.wholeGain_complete": "4a1e1926b4822cac53144d8eeb605e573a784bd563d1693c57365923dfada977",
  "PNP.DirectWire.WireZeroUnaryClosure.Gain.full_field": "6ca0493b38ac572fb200f5f755a2c0d8f66335b2bd1c0c7e21ec0930cfd8986f",
  "PNP.DirectWire.WireZeroUnaryClosure.Gain.branch_boundary": "304254a14f540976f80afefa4e1a04b95dd2faecb6793057552f47cd6a4d6248",
  "PNP.DirectWire.WireZeroUnaryClosure.Gain.exact_accounting": "a2292c1a2c0688d37e617bac3347667c187b65179ada4da9a5d042367ab3266a",
  "PNP.DirectWire.WireZeroUnaryClosure.nextGain_isSome_iff": "c290308e2dd1315e8681c2a7cb6f2eb9435d84a201da37b9e4d1056e9c78b1f5",
  "PNP.DirectWire.WireZeroUnaryClosure.nextGain_none_iff": "5fe27147e0c3bf33ad3565f8263260e91fc515a107e54ff61c19cb25ff828977",
  "PNP.DirectWire.WireZeroUnaryClosure.nextGain_complete": "46f73860393736f9c448a7da052e81f1d28a55a5ab2eb0df6de72899583e5c1a",
  "PNP.DirectWire.WireZeroUnaryClosure.nextGain_none_excludes": "03ff2bbcd0acd7ec0490130890ff65f1f080370b54cf1ee7f463d1ada3133ed5",
  "PNP.DirectWire.WireZeroUnaryClosure.normalization_accounting": "2819cb214714b32bb4ff397ce796ce0eec804851fccd8c00888ef435db0d8acc",
  "PNP.DirectWire.WireZeroUnaryClosure.normalization_iterations": "a51bb1c4dc17ff26218541339352535154dc686b8abe9dde6eedc6af47db80a2",
  "PNP.DirectWire.WireZeroUnaryClosure.Trace.checked": "1335284c1871dddfc16326dd24c100b5295b995f1ff0824f9dcdcc2b86ece17d",
  "PNP.DirectWire.WireZeroUnaryClosure.Trace.searchCalls_le": "effa524e072458b489d5b0b63bfbfda80c6ed36bef9c994bab20b55abc2bcf92",
  "PNP.DirectWire.WireZeroUnaryClosure.run_checked": "40d101b370ac4db92988e9f7afd0bf2a89659d9dbd499239541267967eb40336",
  "PNP.DirectWire.WireZeroUnaryClosure.run_of_stopped": "07f7ad369df6552ab65d2df57f78e12b768199d8305db05e17803ca7d961c981",
  "PNP.DirectWire.WireZeroUnaryClosure.run_idempotent": "87532d20fc451bed56d7de417756ab0bfacf20cbff130e1b7a311fbb1ff52f27",
  "PNP.DirectWire.WireZeroUnaryClosure.run_no_smaller_zeroUnary": "27f009d236e975d9363719387fae52b4fbbdd9eca95c1002415364b40839a8b9",
  "PNP.DirectWire.WireZeroUnaryClosure.run_referenceMinimum": "b0f2d9158f66326d240a45af3878debf5f3887af50f584972921fa58958b7c72",
  "PNP.DirectWire.WireZeroUnaryClosure.run_residualSlack": "264c9273a5c13179bd7c8a454ed997ba20671e6349811d5c55e19874c93c996f",
  "PNP.DirectWire.WireZeroUnaryClosure.run_gainIterations_le_residualSlack": "8011c9319b179a0b46b5cb0a0685c77d3adecbda8068bd8cba6b34cf6b887a5f",
  "PNP.DirectWire.WireZeroUnaryClosure.run_searchCalls_le_residualSlack": "e70efefdebc4db243493e6e6a5eb3309cf1205d93cc92486ebab313842372cc9"
});
const M259_STATUS_FIELDS = Object.freeze({
  "leanWireZeroUnaryClosureFormalized": true,
  "leanWireZeroUnaryClosureAxiomAuditPassed": true,
  "leanWireZeroUnaryClosureAuditedDeclarationCount": 27,
  "leanWireZeroUnaryClosureWholeSelectionTheorem": "PNP.DirectWire.WireZeroUnaryClosure.whole_selected",
  "leanWireZeroUnaryClosureWholeExteriorTheorem": "PNP.DirectWire.WireZeroUnaryClosure.whole_exterior",
  "leanWireZeroUnaryClosureWholeGateCountTheorem": "PNP.DirectWire.WireZeroUnaryClosure.whole_gateCount",
  "leanWireZeroUnaryClosureWholeNotProperTheorem": "PNP.DirectWire.WireZeroUnaryClosure.whole_not_proper",
  "leanWireZeroUnaryClosureZeroExteriorSelectionTheorem": "PNP.DirectWire.WireZeroUnaryClosure.all_gates_of_zero_exterior",
  "leanWireZeroUnaryClosureWholeGainCheckedTheorem": "PNP.DirectWire.WireZeroUnaryClosure.WholeGain.checked",
  "leanWireZeroUnaryClosureWholeRecognitionTheorem": "PNP.DirectWire.WireZeroUnaryClosure.wholeGain_isSome_iff",
  "leanWireZeroUnaryClosureWholeCompletenessTheorem": "PNP.DirectWire.WireZeroUnaryClosure.wholeGain_complete",
  "leanWireZeroUnaryClosureGainFullFieldTheorem": "PNP.DirectWire.WireZeroUnaryClosure.Gain.full_field",
  "leanWireZeroUnaryClosureGainBranchBoundaryTheorem": "PNP.DirectWire.WireZeroUnaryClosure.Gain.branch_boundary",
  "leanWireZeroUnaryClosureGainExactAccountingTheorem": "PNP.DirectWire.WireZeroUnaryClosure.Gain.exact_accounting",
  "leanWireZeroUnaryClosureCombinedRecognitionTheorem": "PNP.DirectWire.WireZeroUnaryClosure.nextGain_isSome_iff",
  "leanWireZeroUnaryClosureCombinedNoResultTheorem": "PNP.DirectWire.WireZeroUnaryClosure.nextGain_none_iff",
  "leanWireZeroUnaryClosureCombinedCompletenessTheorem": "PNP.DirectWire.WireZeroUnaryClosure.nextGain_complete",
  "leanWireZeroUnaryClosureCombinedNoGainExclusionTheorem": "PNP.DirectWire.WireZeroUnaryClosure.nextGain_none_excludes",
  "leanWireZeroUnaryClosureNormalizationAccountingTheorem": "PNP.DirectWire.WireZeroUnaryClosure.normalization_accounting",
  "leanWireZeroUnaryClosureNormalizationIterationBoundTheorem": "PNP.DirectWire.WireZeroUnaryClosure.normalization_iterations",
  "leanWireZeroUnaryClosureTraceCheckedTheorem": "PNP.DirectWire.WireZeroUnaryClosure.Trace.checked",
  "leanWireZeroUnaryClosureTraceSearchCallBoundTheorem": "PNP.DirectWire.WireZeroUnaryClosure.Trace.searchCalls_le",
  "leanWireZeroUnaryClosureClosureCheckedTheorem": "PNP.DirectWire.WireZeroUnaryClosure.run_checked",
  "leanWireZeroUnaryClosureStoppedClosureTheorem": "PNP.DirectWire.WireZeroUnaryClosure.run_of_stopped",
  "leanWireZeroUnaryClosureClosureIdempotenceTheorem": "PNP.DirectWire.WireZeroUnaryClosure.run_idempotent",
  "leanWireZeroUnaryClosureScopedTerminalNoGainTheorem": "PNP.DirectWire.WireZeroUnaryClosure.run_no_smaller_zeroUnary",
  "leanWireZeroUnaryClosureReferenceMinimumInvarianceTheorem": "PNP.DirectWire.WireZeroUnaryClosure.run_referenceMinimum",
  "leanWireZeroUnaryClosureResidualSlackAccountingTheorem": "PNP.DirectWire.WireZeroUnaryClosure.run_residualSlack",
  "leanWireZeroUnaryClosureResidualSlackIterationBoundTheorem": "PNP.DirectWire.WireZeroUnaryClosure.run_gainIterations_le_residualSlack",
  "leanWireZeroUnaryClosureResidualSlackSearchCallBoundTheorem": "PNP.DirectWire.WireZeroUnaryClosure.run_searchCalls_le_residualSlack",
  "leanWireZeroUnaryClosureWholeSpanBranchDerived": true,
  "leanWireZeroUnaryClosureProperAndWholeZeroUnaryCompletenessProved": true,
  "leanWireZeroUnaryClosureActualGainRestartClosureProved": true,
  "leanWireZeroUnaryClosureFullComputationalFieldPreservationProved": true,
  "leanWireZeroUnaryClosureCommonPhysicalAndScopedQuiescenceProved": true,
  "leanWireZeroUnaryClosureExactGateAndResidualSlackAccountingProved": true,
  "leanWireZeroUnaryClosureIdempotenceProved": true,
  "leanWireZeroUnaryClosureCallerSuppliedFamilyRequired": false,
  "leanWireZeroUnaryClosureReferenceMinimumUsedInExecution": false,
  "leanWireZeroUnaryClosureAllBoundaryWidthsCovered": false,
  "leanWireZeroUnaryClosureNoResultProvesGlobalMinimality": false,
  "leanWireZeroUnaryClosureArbitraryObligationDAGsCovered": false,
  "leanWireZeroUnaryClosureFullManuscriptCarrierProved": false,
  "leanWireZeroUnaryClosureCompleteObligationCalculusProved": false,
  "leanWireZeroUnaryClosureCompletePackageEProved": false,
  "leanWireZeroUnaryClosurePolynomialRuntimeProved": false,
  "leanWireZeroUnaryClosureScope": "all-finite-computational-wire-derived-proper-and-whole-zero-or-one-actual-boundary-search-full-field-gain-normalization-restart-closure-common-scoped-quiescence-idempotence-exact-gate-and-residual-slack-accounting-no-global-minimum-or-total-encoded-polynomial-runtime"
});
const M259_AXIOMS = Object.freeze({
  "PNP.DirectWire.WireZeroUnaryClosure.whole_selected": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.whole_exterior": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.whole_gateCount": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.whole_not_proper": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.all_gates_of_zero_exterior": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.WholeGain.checked": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.wholeGain_isSome_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.wholeGain_complete": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.Gain.full_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.Gain.branch_boundary": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.Gain.exact_accounting": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.nextGain_isSome_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.nextGain_none_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.nextGain_complete": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.nextGain_none_excludes": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.normalization_accounting": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.normalization_iterations": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.Trace.checked": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.Trace.searchCalls_le": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.run_checked": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.run_of_stopped": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.run_idempotent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.run_no_smaller_zeroUnary": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.run_referenceMinimum": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.run_residualSlack": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.run_gainIterations_le_residualSlack": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireZeroUnaryClosure.run_searchCalls_le_residualSlack": [
    "Quot.sound",
    "propext"
  ]
});

const M259_MODULES = Object.freeze({
  "PNP.DirectWire.WireZeroUnaryClosure.whole_selected": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.whole_exterior": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.whole_gateCount": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.whole_not_proper": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.all_gates_of_zero_exterior": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.WholeGain.checked": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.wholeGain_isSome_iff": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.wholeGain_complete": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.Gain.full_field": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.Gain.branch_boundary": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.Gain.exact_accounting": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.nextGain_isSome_iff": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.nextGain_none_iff": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.nextGain_complete": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.nextGain_none_excludes": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.normalization_accounting": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.normalization_iterations": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.Trace.checked": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.Trace.searchCalls_le": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.run_checked": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.run_of_stopped": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.run_idempotent": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.run_no_smaller_zeroUnary": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.run_referenceMinimum": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.run_residualSlack": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.run_gainIterations_le_residualSlack": "PNP.NANDWireZeroUnaryClosure",
  "PNP.DirectWire.WireZeroUnaryClosure.run_searchCalls_le_residualSlack": "PNP.NANDWireZeroUnaryClosure"
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

test('M259 compiled zero/unary closure interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M259_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M259_COORDINATE)
    assert.equal(map.coordinate, M259_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M259_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, M259_MODULES[name], name);
      assert.deepEqual(declaration.axioms, M259_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M259_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M259_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M259_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "not global minimality",
  "Whole-span descent is not relabelled as a proper-support Package E certificate",
  "A gate-decrease or search-call bound is not a total polynomial execution theorem",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M259 publication rejects weakened, supplied, assumption-backed and widened complete-calculus substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M259_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M259_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = 'PNP.DirectWire.WireZeroUnaryClosure.run_checked';
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M259_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M259_MILESTONE
    ? {...row, nonClaim:'The zero/unary closure proves global minimality, all boundary widths and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M259 adds computed zero/unary restart-closure coverage without complete-calculus, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M259_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "whole-span descent and NormalizeOrGain restart edge",
  "without a supplied family, trajectory or completeness certificate",
  "common fixed point need not be globally minimal",
  "No fixed load-bearing checkpoint changes state",
  "40% proof estimate"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M259_COORDINATE) return;
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

test('M259 current summaries distinguish scoped zero/unary common stopping from complete-calculus and global completion and retain metrics and separate-site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_wire_zero_unary_closure.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "Whole-span descent is not a proper-support Package E certificate.",
  "Reference minima occur only in specifications and proofs, not execution.",
  "An iteration or search-call bound is not a total polynomial runtime theorem.",
  "Runtime execution is test evidence, not theorem authority.",
  "Publication decision: defer a separate PNPLabs cycle for M259."
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-13-computed-zero-unary-descent-closure.md'));
  assert.match(plan, /Publication decision: defer a separate PNPLabs cycle for M259\./u);
  if (progress.asOfCoordinate !== M259_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_wire_zero_unary_closure.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
