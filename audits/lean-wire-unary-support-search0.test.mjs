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

const SOURCE = 'lean/PNP/NANDWireUnarySupportSearch.lean';
const AUDIT = 'lean-audit/PNPWireUnarySupportSearchAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPWireUnarySupportSearch.lean';
const NAMES = [
  "PNP.DirectWire.WireUnarySupportSearch.maximalSelection_admissible",
  "PNP.DirectWire.WireUnarySupportSearch.maximalSelection_contains",
  "PNP.DirectWire.WireUnarySupportSearch.gateRecords_selected_iff",
  "PNP.DirectWire.WireUnarySupportSearch.gateRecords_selected",
  "PNP.DirectWire.WireUnarySupportSearch.admissible_boundary",
  "PNP.DirectWire.WireUnarySupportSearch.admissible_boundary_small",
  "PNP.DirectWire.WireUnarySupportSearch.candidateRecords_boundary",
  "PNP.DirectWire.WireUnarySupportSearch.candidateRecords_proper",
  "PNP.DirectWire.WireUnarySupportSearch.consumedWires_length",
  "PNP.DirectWire.WireUnarySupportSearch.boundary_mem_consumedWires",
  "PNP.DirectWire.WireUnarySupportSearch.boundaryChoices_length",
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_length",
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_maximal_mem",
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_singleton_mem",
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_wire_mem",
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_of_mem",
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_external",
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_mem",
  "PNP.DirectWire.WireUnarySupportSearch.support_admissible",
  "PNP.DirectWire.WireUnarySupportSearch.support_contained_in_candidate",
  "PNP.DirectWire.WireUnarySupportSearch.selected_length_mono",
  "PNP.DirectWire.WireUnarySupportSearch.selected_length_le",
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_entry_length",
  "PNP.DirectWire.WireUnarySupportSearch.extracted_gateCount_mono",
  "PNP.DirectWire.WireUnarySupportSearch.singleton_selection",
  "PNP.DirectWire.WireUnarySupportSearch.checkedGain_selection_invariant",
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_complete",
  "PNP.DirectWire.WireUnarySupportSearch.findGain_complete",
  "PNP.DirectWire.WireUnarySupportSearch.findGain_member",
  "PNP.DirectWire.WireUnarySupportSearch.findGain_records_bound",
  "PNP.DirectWire.WireUnarySupportSearch.GainResult.checked",
  "PNP.DirectWire.WireUnarySupportSearch.findGain_none_excludes",
  "PNP.DirectWire.WireUnarySupportSearch.GainResult.dischargeR7_source_exact",
  "PNP.DirectWire.WireUnarySupportSearch.GainResult.dischargeR7_full_value",
  "PNP.DirectWire.WireUnarySupportSearch.findReplacement_isSome",
  "PNP.DirectWire.WireUnarySupportSearch.findReplacement_sound"
];
const SPECS = [
  {
    "kind": "main",
    "path": "lean/PNP/NANDWireUnarySupportSearch.lean",
    "prefix": "PNP.DirectWire.WireUnarySupportSearch.",
    "imports": [
      "PNP.NANDWireUnaryArbitrarySupport",
      "PNP.ResidualTerminalFrontierPushout"
    ],
    "signatures": {
      "maximalSelection_admissible": "theorem maximalSelection_admissible (program : Program inputs gates) (choice : BoundaryChoice inputs total) (omitted : Nat) : Admissible program choice omitted (maximalSelection program choice omitted)",
      "maximalSelection_contains": "theorem maximalSelection_contains (program : Program inputs gates) (choice : BoundaryChoice inputs total) (omitted : Nat) : ∀ selected : Valuation gates, Admissible program choice omitted selected → ∀ index, selected index = true → maximalSelection program choice omitted index = true",
      "gateRecords_selected_iff": "theorem gateRecords_selected_iff (selected : Valuation gates) (index : Fin gates) : terminalGateSelected (gateRecords (inputs := inputs) (outputs := outputs) (profileWidth := profileWidth) selected) index = true ↔ selected index = true",
      "gateRecords_selected": "theorem gateRecords_selected (selected : Valuation gates) : terminalGateSelected (gateRecords (inputs := inputs) (outputs := outputs) (profileWidth := profileWidth) selected) = selected",
      "admissible_boundary": "theorem admissible_boundary (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (choice : BoundaryChoice inputs gates) (omitted : Nat) (lawful : Admissible program choice omitted (terminalGateSelected records)) (wire : TerminalSupportWire inputs gates) (member : wire ∈ terminalBoundaryPorts program records) : choice = some wire",
      "admissible_boundary_small": "theorem admissible_boundary_small (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (choice : BoundaryChoice inputs gates) (omitted : Nat) (lawful : Admissible program choice omitted (terminalGateSelected records)) : (terminalBoundaryPorts program records).length ≤ 1",
      "candidateRecords_boundary": "theorem candidateRecords_boundary (program : Program inputs gates) (choice : BoundaryChoice inputs gates) (omitted : Fin gates) : (terminalBoundaryPorts program (candidateRecords (outputs := outputs) (profileWidth := profileWidth) program choice omitted)).length ≤ 1",
      "candidateRecords_proper": "theorem candidateRecords_proper (program : Program inputs gates) (choice : BoundaryChoice inputs gates) (omitted : Fin gates) : 0 < (ArbitrarySupportSplice.exterior (candidateRecords (outputs := outputs) (profileWidth := profileWidth) program choice omitted)).length",
      "consumedWires_length": "theorem consumedWires_length (program : Program inputs gates) : (consumedWires program).length ≤ 2 * gates",
      "boundary_mem_consumedWires": "theorem boundary_mem_consumedWires (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (wire : TerminalSupportWire inputs gates) (member : wire ∈ terminalBoundaryPorts program records) : wire ∈ consumedWires program",
      "boundaryChoices_length": "theorem boundaryChoices_length (program : Program inputs gates) : (boundaryChoices program).length ≤ 2 * gates + 1",
      "candidateFamily_length": "theorem candidateFamily_length (program : Program inputs gates) : (candidateFamily (outputs := outputs) (profileWidth := profileWidth) program).length ≤ (2 * gates + 1) * gates + gates",
      "candidateFamily_maximal_mem": "theorem candidateFamily_maximal_mem (program : Program inputs gates) (choice : BoundaryChoice inputs gates) (chosen : choice ∈ boundaryChoices program) (omitted : Fin gates) : candidateRecords (outputs := outputs) (profileWidth := profileWidth) program choice omitted ∈ candidateFamily program",
      "candidateFamily_singleton_mem": "theorem candidateFamily_singleton_mem (program : Program inputs gates) (index : Fin gates) : [TerminalPrimitiveRecord.gate index] ∈ candidateFamily (outputs := outputs) (profileWidth := profileWidth) program",
      "supportChoice_wire_mem": "theorem supportChoice_wire_mem (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (wire : TerminalSupportWire inputs gates) (chosen : supportChoice program records = some wire) : wire ∈ terminalBoundaryPorts program records",
      "supportChoice_of_mem": "theorem supportChoice_of_mem (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (small : (terminalBoundaryPorts program records).length ≤ 1) (wire : TerminalSupportWire inputs gates) (member : wire ∈ terminalBoundaryPorts program records) : supportChoice program records = some wire",
      "supportChoice_external": "theorem supportChoice_external (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (wire : TerminalSupportWire inputs gates) (chosen : supportChoice program records = some wire) : terminalWireExternal records wire = true",
      "supportChoice_mem": "theorem supportChoice_mem (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : supportChoice program records ∈ boundaryChoices program",
      "support_admissible": "theorem support_admissible (candidate : Candidate inputs gates outputs) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (small : (terminalBoundaryPorts candidate.program records).length ≤ 1) (omitted : Fin gates) (outside : terminalGateSelected records omitted = false) : Admissible candidate.program (supportChoice candidate.program records) omitted.val (terminalGateSelected records)",
      "support_contained_in_candidate": "theorem support_contained_in_candidate (candidate : Candidate inputs gates outputs) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (small : (terminalBoundaryPorts candidate.program records).length ≤ 1) (omitted : Fin gates) (outside : terminalGateSelected records omitted = false) (index : Fin gates) (selected : terminalGateSelected records index = true) : terminalGateSelected (candidateRecords (outputs := outputs) (profileWidth := profileWidth) candidate.program (supportChoice candidate.program records) omitted) index = true",
      "selected_length_mono": "theorem selected_length_mono (left right : Valuation gates) (included : ∀ index, left index = true → right index = true) : (terminalSelectedGateIndices left).length ≤ (terminalSelectedGateIndices right).length",
      "selected_length_le": "theorem selected_length_le (selected : Valuation gates) : (terminalSelectedGateIndices selected).length ≤ gates",
      "candidateFamily_entry_length": "theorem candidateFamily_entry_length (program : Program inputs gates) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (member : records ∈ candidateFamily program) : records.length ≤ gates",
      "extracted_gateCount_mono": "theorem extracted_gateCount_mono (candidate : Candidate inputs gates outputs) (left right : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (included : ∀ index, terminalGateSelected left index = true → terminalGateSelected right index = true) : (extractTerminalSupport candidate left).gateCount ≤ (extractTerminalSupport candidate right).gateCount",
      "singleton_selection": "theorem singleton_selection (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (one : (terminalSelectedGates records).length = 1) : ∃ picked : Fin gates, terminalGateSelected ([.gate picked] : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) = terminalGateSelected records",
      "checkedGain_selection_invariant": "theorem checkedGain_selection_invariant (carrier : WireCarrier inputs outputs fields) (left right : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0)) (sameSelection : terminalGateSelected left = terminalGateSelected right) (accepted : (WireUnaryArbitrarySupport.checkedProperGain carrier left).isSome = true) : (WireUnaryArbitrarySupport.checkedProperGain carrier right).isSome = true",
      "candidateFamily_complete": "theorem candidateFamily_complete (carrier : WireCarrier inputs outputs fields) (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0)) (accepted : (WireUnaryArbitrarySupport.checkedProperGain carrier records).isSome = true) : ∃ generated : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0), generated ∈ candidateFamily carrier.exposed.candidate.program ∧ (WireUnaryArbitrarySupport.checkedProperGain carrier generated).isSome = true",
      "findGain_complete": "theorem findGain_complete (carrier : WireCarrier inputs outputs fields) (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0)) (small : (WireUnaryArbitrarySupport.pulled carrier records).boundary.length ≤ 1) (proper : 0 < WireUnaryArbitrarySupport.exteriorCharge carrier records) (other : Implementation (WireUnaryArbitrarySupport.pulled carrier records).boundary.length (WireUnaryArbitrarySupport.pulled carrier records).interface.length) (sameOpen : other.candidate.semantics = (WireUnaryArbitrarySupport.pulled carrier records).extractedCandidate.semantics) (smaller : other.gateCount < (WireUnaryArbitrarySupport.pulled carrier records).gateCount) : (findGain carrier).isSome = true",
      "findGain_member": "theorem findGain_member (carrier : WireCarrier inputs outputs fields) (result : GainResult carrier) (found : findGain carrier = some result) : result.records ∈ candidateFamily carrier.exposed.candidate.program",
      "findGain_records_bound": "theorem findGain_records_bound (carrier : WireCarrier inputs outputs fields) (result : GainResult carrier) (found : findGain carrier = some result) : result.records.length ≤ carrier.implementation.gateCount",
      "GainResult.checked": "theorem GainResult.checked {carrier : WireCarrier inputs outputs fields} (result : GainResult carrier) : (WireUnaryArbitrarySupport.pulled carrier result.records).boundary.length ≤ 1 ∧ (WireUnaryArbitrarySupport.pulled carrier result.records).gateCount < carrier.implementation.gateCount ∧ StrictEquivalentGain carrier.implementation result.expanded.implementation ∧ (∀ valuation field, result.expanded.fieldValue valuation field = carrier.fieldValue valuation field) ∧ result.expanded.implementation.gateCount = (WireUnaryArbitrarySupport.replacement carrier result.records result.gain.small).gateCount + WireUnaryArbitrarySupport.exteriorCharge carrier result.records",
      "findGain_none_excludes": "theorem findGain_none_excludes (carrier : WireCarrier inputs outputs fields) (notFound : findGain carrier = none) (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0)) (small : (WireUnaryArbitrarySupport.pulled carrier records).boundary.length ≤ 1) (proper : 0 < WireUnaryArbitrarySupport.exteriorCharge carrier records) (other : Implementation (WireUnaryArbitrarySupport.pulled carrier records).boundary.length (WireUnaryArbitrarySupport.pulled carrier records).interface.length) (sameOpen : other.candidate.semantics = (WireUnaryArbitrarySupport.pulled carrier records).extractedCandidate.semantics) : (WireUnaryArbitrarySupport.pulled carrier records).gateCount ≤ other.gateCount",
      "GainResult.dischargeR7_source_exact": "theorem GainResult.dischargeR7_source_exact {carrier : WireCarrier inputs outputs fields} (result : GainResult carrier) (keep : Fin fields → Bool) (creation : WireObligationRestoration.R5Creation carrier keep) : (result.dischargeR7 keep creation).actualSource = result.expanded.source creation.coordinate",
      "GainResult.dischargeR7_full_value": "theorem GainResult.dischargeR7_full_value {carrier : WireCarrier inputs outputs fields} (result : GainResult carrier) (keep : Fin fields → Bool) (creation : WireObligationRestoration.R5Creation carrier keep) (valuation : Valuation inputs) : (result.dischargeR7 keep creation).actualSource.eval valuation (result.expanded.implementation.candidate.program.eval valuation) = carrier.fieldValue valuation creation.coordinate",
      "findReplacement_isSome": "theorem findReplacement_isSome (carrier : WireCarrier inputs outputs fields) : (findReplacement carrier).isSome = (findGain carrier).isSome",
      "findReplacement_sound": "theorem findReplacement_sound (carrier : WireCarrier inputs outputs fields) (replacement : WireCarrier inputs outputs fields) (found : findReplacement carrier = some replacement) : StrictEquivalentGain carrier.implementation replacement.implementation ∧ (∀ valuation field, replacement.fieldValue valuation field = carrier.fieldValue valuation field)"
    },
    "heads": [
      "BoundaryChoice",
      "maximalSelection",
      "Admissible",
      "maximalSelection_admissible",
      "maximalSelection_contains",
      "gateRecords",
      "gateRecords_selected_iff",
      "gateRecords_selected",
      "admissible_boundary",
      "admissible_boundary_small",
      "candidateRecords",
      "candidateRecords_boundary",
      "candidateRecords_proper",
      "sourceWires",
      "consumedWires",
      "consumedWires_length",
      "boundary_mem_consumedWires",
      "boundaryChoices",
      "boundaryChoices_length",
      "candidateFamily",
      "candidateFamily_length",
      "candidateFamily_maximal_mem",
      "candidateFamily_singleton_mem",
      "supportChoice",
      "supportChoice_wire_mem",
      "supportChoice_of_mem",
      "supportChoice_external",
      "supportChoice_mem",
      "support_admissible",
      "support_contained_in_candidate",
      "selected_length_mono",
      "selected_length_le",
      "candidateFamily_entry_length",
      "extracted_gateCount_mono",
      "singleton_selection",
      "checkedGain_selection_invariant",
      "candidateFamily_complete",
      "GainResult",
      "findGain",
      "GainResult.expanded",
      "findReplacement",
      "findGain_complete",
      "findGain_member",
      "findGain_records_bound",
      "GainResult.checked",
      "findGain_none_excludes",
      "GainResult.dischargeR7",
      "GainResult.dischargeR7_source_exact",
      "GainResult.dischargeR7_full_value",
      "findReplacement_isSome",
      "findReplacement_sound"
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
  let depth=0;
  for(let index=0;index<block.length-1;index++){
    if('({['.includes(block[index]))depth++;
    else if(')}]'.includes(block[index]))depth--;
    if(depth===0 && block.slice(index,index+2)===':=')return block.slice(0,index).trim();
  }
  return '';
}
function validateSource0(source,spec) {
  const failures=[], require0=(condition,category)=>{if(!condition)failures.push(category);};
  const clean=compact0(source),block=name=>block0(source,name);
  const includes=(name,tokens,category)=>require0(tokens.every(token=>block(name).includes(token)),category);
  require0(!hasLeanAssumptionDeclaration0(source),'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source),'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|callerCertificate|suppliedFamily|suppliedResult|suppliedOrder)\b/u.test(clean),'shortcut-or-certificate');
  require0(!/\b(?:allSubsets|allCandidates|allBoolTuples|referenceMinimum|scanEquivalentSizes|terminalFullProfileMinimum)\b/u.test(clean),'no-production-exhaustion');
  require0(!/\ballFin\s+inputs\b/u.test(clean),'no-unused-input-enumeration');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]))===
    JSON.stringify(spec.imports),'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name))===
    JSON.stringify(spec.heads),'public-interface');
  for(const [name,signature] of Object.entries(spec.signatures))
    require0(signature0(block(name))===signature,'signature:'+name);
  require0(clean.includes('variable {inputs gates total outputs profileWidth : Nat}')&&
    clean.includes('variable {fields : Nat}'),'unbounded-dimensions');
  includes('maximalSelection',[
    'maximalSelection initial choice omitted','gates ≠ omitted',
    'boundaryGate choice gates = false','sourceAdmitted choice earlier gate.left',
    'sourceAdmitted choice earlier gate.right','else false',
  ],'actual-maximal-scan');
  includes('consumedWires',[
    '(allFin gates).flatMap','program.terminalGateSources consumer',
    'sourceWires (program.terminalGateSources consumer).1 ++',
    'sourceWires (program.terminalGateSources consumer).2',
  ],'actual-consumed-wires');
  require0(block('boundaryChoices').endsWith(
    'none :: (consumedWires program).map Option.some'),'source-derived-boundary-choices');
  includes('candidateFamily',[
    '(boundaryChoices program).flatMap','(allFin gates).map (candidateRecords program choice)',
    '(allFin gates).map (fun index => [TerminalPrimitiveRecord.gate index])',
  ],'complete-generated-family');
  includes('candidateFamily_length',[
    'flatMap_length_le','boundaryChoices_length program',
  ],'proved-family-count');
  includes('candidateRecords_proper',[
    'maximalSelection_admissible program choice omitted.val',
    'ArbitrarySupportSplice.mem_exterior_iff','omittedFalse',
  ],'actual-nonempty-exterior');
  includes('support_admissible',[
    'supportChoice_external candidate.program records',
    'completeTerminalPhysicalSupport_incoming_complete',
    'supportChoice_of_mem candidate.program records small',
  ],'derived-support-admissibility');
  includes('support_contained_in_candidate',[
    'maximalSelection_contains','support_admissible candidate records small omitted outside',
  ],'arbitrary-support-containment');
  includes('checkedGain_selection_invariant',[
    'extractTerminalSupport_eq_of_gateSelected_eq',
    'carrier.exposed.candidate left right sameSelection','rightProperty',
  ],'complete-extraction-invariance');
  includes('candidateFamily_complete',[
    'singleton_selection records oneSelected','sameSelection.symm accepted',
    'support_contained_in_candidate','extracted_gateCount_mono',
    'WireUnaryArbitrarySupport.replacement_gate_bound',
    'candidateFamily_maximal_mem','supportChoice_mem',
  ],'all-support-completeness-cases');
  includes('firstGain',[
    'WireUnaryArbitrarySupport.checkedProperGain carrier records',
    'some gain => some ⟨records, gain⟩','none => firstGain carrier rest',
  ],'actual-gain-query');
  require0(block('findGain')===
    'def findGain (carrier : WireCarrier inputs outputs fields) : Option (GainResult carrier) := firstGain carrier (candidateFamily carrier.exposed.candidate.program)',
    'carrier-only-search');
  require0(block('GainResult.expanded').endsWith(
    'WireUnaryArbitrarySupport.expanded carrier result.records result.gain.small'),
    'actual-expanded-result');
  require0(block('findReplacement').endsWith('(findGain carrier).map GainResult.expanded'),
    'public-computed-replacement');
  includes('findGain_complete',[
    'WireUnaryArbitrarySupport.checkedProperGain_complete',
    'candidateFamily_complete carrier records accepted',
    'firstGain_complete carrier _ generated member checked',
  ],'general-complete-search');
  includes('findGain_none_excludes',[
    'findGain_complete carrier records small proper other sameOpen smaller',
    'rw [notFound] at accepted',
  ],'scoped-negative-result');
  require0(block('GainResult.dischargeR7').endsWith(
    'WireUnaryArbitrarySupport.dischargeR7 carrier result.records result.gain.small keep creation'),
    'source-exact-r7-result');
  return [...new Set(failures)];
}
const mainSpec=SPECS.find(spec=>spec.kind==='main');
function rejectMutations0(source,mutations) {
  for(const [before,after,category] of mutations) {
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after),mainSpec).includes(category),category);
  }
}
test('M258 has closed general computed support-search interfaces',async()=>{
  assert.deepEqual(validateSource0(await text0(SOURCE),mainSpec),[]);
});
test('M258 root, exact theorem-name producers and axiom audit agree',async()=>{
  const [audit,inventory,root]=await Promise.all([
    text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean')]);
  for(const name of NAMES) {
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item=>item===name).length,1,name);
    assert.equal(inventory.split(String.fromCharCode(96)+name+',').length-1,1,name);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),NAMES);
  assert.match(root,/^import PNP\.NANDWireUnarySupportSearch\s*$/mu);
});
test('M258 rejects invented boundaries, unused-input scans and omitted singleton candidates',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['none :: (consumedWires program).map Option.some','none :: suppliedFamily','source-derived-boundary-choices'],
    ['(allFin gates).flatMap fun consumer','(allFin inputs).flatMap fun consumer','no-unused-input-enumeration'],
    ['sourceWires (program.terminalGateSources consumer).2','sourceWires (.constant false)','actual-consumed-wires'],
    ['(allFin gates).map (fun index => [TerminalPrimitiveRecord.gate index])','[]','complete-generated-family'],
  ]);
});
test('M258 rejects selecting the omitted or boundary gate and losing source closure',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['if gates ≠ omitted ∧ boundaryGate choice gates = false then','if True then','actual-maximal-scan'],
    ['sourceAdmitted choice earlier gate.right','true','actual-maximal-scan'],
    ['ArbitrarySupportSplice.mem_exterior_iff _ omitted','callerCertificate','actual-nonempty-exterior'],
    ['completeTerminalPhysicalSupport_incoming_complete','callerCertificate','derived-support-admissibility'],
  ]);
});
test('M258 rejects incomplete support coverage and record-sensitive canonicalization',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['singleton_selection records oneSelected','callerCertificate','all-support-completeness-cases'],
    ['support_contained_in_candidate carrier.exposed.candidate records small omitted outside','callerCertificate','all-support-completeness-cases'],
    ['extractTerminalSupport_eq_of_gateSelected_eq','callerCertificate','complete-extraction-invariance'],
    ['(support_admissible candidate records small omitted outside)','callerCertificate','arbitrary-support-containment'],
  ]);
});
test('M258 rejects supplied search families, fabricated witnesses and expanded results',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['def findGain (carrier : WireCarrier inputs outputs fields)',
      'def findGain (carrier : WireCarrier inputs outputs fields) (suppliedFamily : List Nat)','carrier-only-search'],
    ['WireUnaryArbitrarySupport.checkedProperGain carrier records with','WireUnaryArbitrarySupport.checkedProperGain carrier [] with','actual-gain-query'],
    ['WireUnaryArbitrarySupport.expanded carrier result.records result.gain.small',
      'suppliedResult','actual-expanded-result'],
    ['(findGain carrier).map GainResult.expanded','none','public-computed-replacement'],
  ]);
});
test('M258 rejects weakened complete theorem, one-sided agreement and mislabelled negative bounds',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['(small : (WireUnaryArbitrarySupport.pulled carrier records).boundary.length ≤ 1)',
      '(small : True)','signature:findGain_complete'],
    ['(sameOpen : other.candidate.semantics =\n      (WireUnaryArbitrarySupport.pulled carrier records).extractedCandidate.semantics)',
      '(sameOpen : True)','signature:findGain_complete'],
    ['(smaller : other.gateCount < (WireUnaryArbitrarySupport.pulled carrier records).gateCount)',
      '(smaller : other.gateCount ≤ (WireUnaryArbitrarySupport.pulled carrier records).gateCount)',
      'signature:findGain_complete'],
    ['(WireUnaryArbitrarySupport.pulled carrier records).gateCount ≤ other.gateCount',
      'other.gateCount ≤ (WireUnaryArbitrarySupport.pulled carrier records).gateCount',
      'signature:findGain_none_excludes'],
  ]);
});
test('M258 rejects hidden-field loss, extra exterior charges and padding discharges',async()=>{
  rejectMutations0(await text0(SOURCE),[
    ['(∀ valuation field, result.expanded.fieldValue valuation field =',
      '(∃ valuation field, result.expanded.fieldValue valuation field =','signature:GainResult.checked'],
    ['WireUnaryArbitrarySupport.exteriorCharge carrier result.records :=',
      '2 * WireUnaryArbitrarySupport.exteriorCharge carrier result.records :=','signature:GainResult.checked'],
    ['WireUnaryArbitrarySupport.dischargeR7 carrier result.records result.gain.small keep creation',
      'suppliedResult','source-exact-r7-result'],
    ['(2 * gates + 1) * gates + gates','gates','signature:candidateFamily_length'],
  ]);
});
test('M258 rejects assumptions, unaudited declarations and production powersets',async()=>{
  const source=await text0(SOURCE);
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n',mainSpec).includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n',mainSpec).includes('unaudited-form'));
  assert.ok(validateSource0(source+'\ndef unauthorized := allSubsets\n',mainSpec).includes('no-production-exhaustion'));
});
test('M258 regression retains guarded exhaustive comparisons and scoped negative cases',async()=>{
  const source=await text0(REGRESSION);
  assert.match(source,/^import PNP\s*$/mu);
  for(const name of ['empty-dimensions','free-input-and-constant-fields','single-two-input-nand',
    'whole-support-only-gain','singleton-constant-gain','primary-boundary-and-omitted-gate',
    'hidden-selected-and-exterior-fields','sole-external-gate-boundary',
    'interleaved-live-boundary','interleaved-unrealizable-bit','fields-without-ordinary-outputs',
    'two-boundary-no-eligible-gain']) assert.ok(source.includes('"'+name+'"'),name);
  for(const token of ['inputs > 3 || outputs > 2 || fields > 3 || gates > 4',
    'List.range (2 ^ gates)','checkEarlyConstant true','checkEarlyConstant false',
    'checkRepeatedRecords','checkUnusedInputs','checkOutOfScopeSaving','checkPublicReplacement',
    'witness.actualSource ≠ built.source field','def unusedInputs : WireCarrier 64 1 0',
    'M258_COMPUTED_UNARY_SUPPORT_SEARCH_RUNTIME_FIXTURES_GREEN']) assert.ok(source.includes(token),token);
});
test('M258 durable workflow retains explicit-root audit and guarded runtime regression',async()=>{
  const workflow=await text0('.github/workflows/lean-bridge.yml');
  assert.ok(workflow.includes('Audit computed unary support search'));
  assert.ok(workflow.includes('node --test audits/lean-wire-unary-support-search0.test.mjs'));
  assert.ok(workflow.includes('lake env lean -DwarningAsError=true '+AUDIT));
  assert.ok(workflow.includes('lake env lean -DwarningAsError=true '+REGRESSION));
  for(const name of NAMES)assert.ok(workflow.includes('"'+name+'"'),name);
});

const M258_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-13-258';
const M258_MILESTONE = 'wire-unary-support-search';
const M258_HASHES = Object.freeze({
  "PNP.DirectWire.WireUnarySupportSearch.maximalSelection_admissible": "70718895c2c12e9a1b2af6e777e6117f87418fa2b0462269f7545c516502d7cf",
  "PNP.DirectWire.WireUnarySupportSearch.maximalSelection_contains": "f88938f8c16b9e730c9bbe267d4f8c89ee5cadfbc0045afdc70ad3999383d22e",
  "PNP.DirectWire.WireUnarySupportSearch.gateRecords_selected_iff": "8c1966ce09ff72f86c881dd7f8d03cde5b6532909f13ba4b2bda0171069737d5",
  "PNP.DirectWire.WireUnarySupportSearch.gateRecords_selected": "28310bf0e776eb00c6ddab4969e490171a045f6381b0280d7ca5cfcba8b6b39a",
  "PNP.DirectWire.WireUnarySupportSearch.admissible_boundary": "c485b8b5321f2d1fa7d8bbec9e8c6c8dafaaeaea118e2531571578f0484d3181",
  "PNP.DirectWire.WireUnarySupportSearch.admissible_boundary_small": "5fee27f35b298617410c0bb3f73c1b2ba6903840661f08032877aa243a0fc5c9",
  "PNP.DirectWire.WireUnarySupportSearch.candidateRecords_boundary": "45ea7f1d043b44229e95a189f531c40ca12462ff49e977e06846165473859910",
  "PNP.DirectWire.WireUnarySupportSearch.candidateRecords_proper": "6c086a77b1c970c1866350cd6b71c59404f725aa71a441ddeb54019d5827091d",
  "PNP.DirectWire.WireUnarySupportSearch.consumedWires_length": "030e909521cdbb6875562dde63d2d1a1e879440fd034c32e5a32ce79df396d04",
  "PNP.DirectWire.WireUnarySupportSearch.boundary_mem_consumedWires": "e07d702982967607422305510ad6bd38c998d9c4194f5a122c64ff25afa1b8b4",
  "PNP.DirectWire.WireUnarySupportSearch.boundaryChoices_length": "6c3daa4bbe197385783bf050624d6941da972ed3dca1c09ea203b62c1ab1ead1",
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_length": "5ce4eb7077f3268b4fa8f7325d231721bff04ac3f601adee25463b6d46a2a272",
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_maximal_mem": "a5a638feff27bbcf22136a6e3f3fe99e258d9bbae8d563dc276b5795979991a6",
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_singleton_mem": "4af1de31fd4bf4d201e49818b9c1e0b9036ac6b530ee3eaa595f90d110912adf",
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_wire_mem": "e5a7155113a150e4aaf7b68426b1e90b908c19d2ef957df26e5b91f0893b8717",
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_of_mem": "150fae8fa479784aa8b872ee5ee64e33e7ffa0977b0842a74a4c8083a2cef015",
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_external": "021b77ef9449c5607058ebe310fc6ca6a4dde395583092f1495482dd3120b571",
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_mem": "33c62ed28a83b297c5c587ea70cef6d79ac6bbb6d29be514466fbc83b77a8a9a",
  "PNP.DirectWire.WireUnarySupportSearch.support_admissible": "6a2f0d90b9e1a74a0bd4978489f13438b4e0d47b2caf32d86d2514292354dac2",
  "PNP.DirectWire.WireUnarySupportSearch.support_contained_in_candidate": "bdf998053acbc7c9b0ffb39d091d7354c2d67e389bf909fede832f4755e8b6e9",
  "PNP.DirectWire.WireUnarySupportSearch.selected_length_mono": "458a84c5f76b84a54aba3ea5dd87967669fda126c21624f20a860d6c7aee424e",
  "PNP.DirectWire.WireUnarySupportSearch.selected_length_le": "eec3020b2c61f8352307c58580448422619506f4b6f007a4792f33eb0a402d57",
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_entry_length": "78bb59833db65bb63a805949322c55631c163ff4a419a3512227e60a2a169b8e",
  "PNP.DirectWire.WireUnarySupportSearch.extracted_gateCount_mono": "567c07c22d6bf483761fdf3f2064e21a35c0041cfa2b975e2df6560bc6128714",
  "PNP.DirectWire.WireUnarySupportSearch.singleton_selection": "4ebcad2581a27e2d0a261fcdc656f874fc61f088c8c97c70bf39a77d124e097b",
  "PNP.DirectWire.WireUnarySupportSearch.checkedGain_selection_invariant": "66cc45fcb13c84e7b8069467b95dc2a0f79bd4dd78f65727b7c0698e7b36adab",
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_complete": "80e9036cfa4a719acd036e4a33a52dcff6ef6ca5e8c91733e761f8fac5394b7c",
  "PNP.DirectWire.WireUnarySupportSearch.findGain_complete": "2a680bd477e64a55707a1f892fa3567ec338de4762b201287e4b13601728653c",
  "PNP.DirectWire.WireUnarySupportSearch.findGain_member": "688799871ec61a8a9962bf3c1cfc47793194efe5842cec84a62cbedd9599ae78",
  "PNP.DirectWire.WireUnarySupportSearch.findGain_records_bound": "995f1f43b1064187a69323a68140af8b49d4526774b38a4f598e9fd50afc560a",
  "PNP.DirectWire.WireUnarySupportSearch.GainResult.checked": "4d4132cd01b501b8f103399b3c57c47e45342692e0e6054fd3814448326180ba",
  "PNP.DirectWire.WireUnarySupportSearch.findGain_none_excludes": "7e9d9d59b2ce85081194c5ab4fb513ebfd1c4e62017889c5fd3b7774e769fd1b",
  "PNP.DirectWire.WireUnarySupportSearch.GainResult.dischargeR7_source_exact": "dc48bbffd059b2660b83265da71e67eb8891cee01bb97f2a69c2a7f210cacb9c",
  "PNP.DirectWire.WireUnarySupportSearch.GainResult.dischargeR7_full_value": "96904c09e21b42e091484c33a93aa8cb2949f6992410fcdce7f524ca36bd1b53",
  "PNP.DirectWire.WireUnarySupportSearch.findReplacement_isSome": "c5b472a9d7dba978e4fc789aae984d010d13d659da7054cb5ed8d88b3fc67435",
  "PNP.DirectWire.WireUnarySupportSearch.findReplacement_sound": "1fb66b7bb02ed8dab6d84d4dc001e8fcdf6b07f39a61c7bf95c3105ae850d3c7"
});
const M258_STATUS_FIELDS = Object.freeze({
  "leanWireUnarySupportSearchFormalized": true,
  "leanWireUnarySupportSearchAxiomAuditPassed": true,
  "leanWireUnarySupportSearchAuditedDeclarationCount": 36,
  "leanWireUnarySupportSearchMaximalAdmissibilityTheorem": "PNP.DirectWire.WireUnarySupportSearch.maximalSelection_admissible",
  "leanWireUnarySupportSearchMaximalContainmentTheorem": "PNP.DirectWire.WireUnarySupportSearch.maximalSelection_contains",
  "leanWireUnarySupportSearchCanonicalSelectionIffTheorem": "PNP.DirectWire.WireUnarySupportSearch.gateRecords_selected_iff",
  "leanWireUnarySupportSearchCanonicalSelectionTheorem": "PNP.DirectWire.WireUnarySupportSearch.gateRecords_selected",
  "leanWireUnarySupportSearchActualBoundaryTheorem": "PNP.DirectWire.WireUnarySupportSearch.admissible_boundary",
  "leanWireUnarySupportSearchUnaryBoundaryTheorem": "PNP.DirectWire.WireUnarySupportSearch.admissible_boundary_small",
  "leanWireUnarySupportSearchCandidateBoundaryTheorem": "PNP.DirectWire.WireUnarySupportSearch.candidateRecords_boundary",
  "leanWireUnarySupportSearchCandidatePropernessTheorem": "PNP.DirectWire.WireUnarySupportSearch.candidateRecords_proper",
  "leanWireUnarySupportSearchConsumedWireCountTheorem": "PNP.DirectWire.WireUnarySupportSearch.consumedWires_length",
  "leanWireUnarySupportSearchBoundaryEnumerationCompletenessTheorem": "PNP.DirectWire.WireUnarySupportSearch.boundary_mem_consumedWires",
  "leanWireUnarySupportSearchBoundaryChoiceCountTheorem": "PNP.DirectWire.WireUnarySupportSearch.boundaryChoices_length",
  "leanWireUnarySupportSearchCandidateFamilyCountTheorem": "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_length",
  "leanWireUnarySupportSearchMaximalFamilyMembershipTheorem": "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_maximal_mem",
  "leanWireUnarySupportSearchSingletonFamilyMembershipTheorem": "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_singleton_mem",
  "leanWireUnarySupportSearchActualChoiceMembershipTheorem": "PNP.DirectWire.WireUnarySupportSearch.supportChoice_wire_mem",
  "leanWireUnarySupportSearchActualChoiceCompletenessTheorem": "PNP.DirectWire.WireUnarySupportSearch.supportChoice_of_mem",
  "leanWireUnarySupportSearchActualChoiceExteriorTheorem": "PNP.DirectWire.WireUnarySupportSearch.supportChoice_external",
  "leanWireUnarySupportSearchChoiceFamilyMembershipTheorem": "PNP.DirectWire.WireUnarySupportSearch.supportChoice_mem",
  "leanWireUnarySupportSearchGeneralSupportAdmissibilityTheorem": "PNP.DirectWire.WireUnarySupportSearch.support_admissible",
  "leanWireUnarySupportSearchGeneralSupportContainmentTheorem": "PNP.DirectWire.WireUnarySupportSearch.support_contained_in_candidate",
  "leanWireUnarySupportSearchSelectionCountMonotonicityTheorem": "PNP.DirectWire.WireUnarySupportSearch.selected_length_mono",
  "leanWireUnarySupportSearchSelectionCountBoundTheorem": "PNP.DirectWire.WireUnarySupportSearch.selected_length_le",
  "leanWireUnarySupportSearchCandidateRecordBoundTheorem": "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_entry_length",
  "leanWireUnarySupportSearchExtractedCountMonotonicityTheorem": "PNP.DirectWire.WireUnarySupportSearch.extracted_gateCount_mono",
  "leanWireUnarySupportSearchSingletonCanonicalizationTheorem": "PNP.DirectWire.WireUnarySupportSearch.singleton_selection",
  "leanWireUnarySupportSearchGainCanonicalizationTheorem": "PNP.DirectWire.WireUnarySupportSearch.checkedGain_selection_invariant",
  "leanWireUnarySupportSearchCandidateFamilyCompletenessTheorem": "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_complete",
  "leanWireUnarySupportSearchSearchCompletenessTheorem": "PNP.DirectWire.WireUnarySupportSearch.findGain_complete",
  "leanWireUnarySupportSearchSearchFamilyMembershipTheorem": "PNP.DirectWire.WireUnarySupportSearch.findGain_member",
  "leanWireUnarySupportSearchSearchRecordBoundTheorem": "PNP.DirectWire.WireUnarySupportSearch.findGain_records_bound",
  "leanWireUnarySupportSearchCheckedResultTheorem": "PNP.DirectWire.WireUnarySupportSearch.GainResult.checked",
  "leanWireUnarySupportSearchNoResultExclusionTheorem": "PNP.DirectWire.WireUnarySupportSearch.findGain_none_excludes",
  "leanWireUnarySupportSearchR7SourceExactTheorem": "PNP.DirectWire.WireUnarySupportSearch.GainResult.dischargeR7_source_exact",
  "leanWireUnarySupportSearchR7FullValueTheorem": "PNP.DirectWire.WireUnarySupportSearch.GainResult.dischargeR7_full_value",
  "leanWireUnarySupportSearchReplacementRecognitionTheorem": "PNP.DirectWire.WireUnarySupportSearch.findReplacement_isSome",
  "leanWireUnarySupportSearchReplacementSoundnessTheorem": "PNP.DirectWire.WireUnarySupportSearch.findReplacement_sound",
  "leanWireUnarySupportSearchProperZeroUnaryCompletenessProved": true,
  "leanWireUnarySupportSearchPhysicalCandidateCountBoundProved": true,
  "leanWireUnarySupportSearchPhysicalRecordCountBoundProved": true,
  "leanWireUnarySupportSearchCallerSuppliedFamilyRequired": false,
  "leanWireUnarySupportSearchAllBoundaryWidthsCovered": false,
  "leanWireUnarySupportSearchAllR7CasesDerived": false,
  "leanWireUnarySupportSearchNoResultProvesGlobalMinimality": false,
  "leanWireUnarySupportSearchArbitraryObligationDAGsCovered": false,
  "leanWireUnarySupportSearchFullManuscriptCarrierProved": false,
  "leanWireUnarySupportSearchCompleteObligationCalculusProved": false,
  "leanWireUnarySupportSearchCompletePackageEProved": false,
  "leanWireUnarySupportSearchPolynomialRuntimeProved": false,
  "leanWireUnarySupportSearchScope": "all-finite-computational-wire-source-derived-proper-zero-or-one-actual-boundary-support-search-complete-maximal-and-singleton-candidates-physical-count-bounds-full-field-actual-replacement-source-exact-r7-no-global-minimum-or-total-encoded-polynomial-runtime"
});
const M258_AXIOMS = Object.freeze({
  "PNP.DirectWire.WireUnarySupportSearch.maximalSelection_admissible": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.maximalSelection_contains": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.gateRecords_selected_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.gateRecords_selected": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.admissible_boundary": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.admissible_boundary_small": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.candidateRecords_boundary": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.candidateRecords_proper": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.consumedWires_length": [
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.boundary_mem_consumedWires": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.boundaryChoices_length": [
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_length": [
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_maximal_mem": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_singleton_mem": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_wire_mem": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_of_mem": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_external": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_mem": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.support_admissible": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.support_contained_in_candidate": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.selected_length_mono": [
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.selected_length_le": [
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_entry_length": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.extracted_gateCount_mono": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.singleton_selection": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.checkedGain_selection_invariant": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_complete": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.findGain_complete": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.findGain_member": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.findGain_records_bound": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.GainResult.checked": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.findGain_none_excludes": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.GainResult.dischargeR7_source_exact": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.GainResult.dischargeR7_full_value": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.findReplacement_isSome": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnarySupportSearch.findReplacement_sound": [
    "Quot.sound",
    "propext"
  ]
});

const M258_MODULES = Object.freeze({
  "PNP.DirectWire.WireUnarySupportSearch.maximalSelection_admissible": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.maximalSelection_contains": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.gateRecords_selected_iff": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.gateRecords_selected": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.admissible_boundary": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.admissible_boundary_small": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.candidateRecords_boundary": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.candidateRecords_proper": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.consumedWires_length": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.boundary_mem_consumedWires": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.boundaryChoices_length": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_length": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_maximal_mem": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_singleton_mem": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_wire_mem": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_of_mem": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_external": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.supportChoice_mem": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.support_admissible": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.support_contained_in_candidate": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.selected_length_mono": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.selected_length_le": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_entry_length": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.extracted_gateCount_mono": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.singleton_selection": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.checkedGain_selection_invariant": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.candidateFamily_complete": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.findGain_complete": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.findGain_member": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.findGain_records_bound": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.GainResult.checked": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.findGain_none_excludes": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.GainResult.dischargeR7_source_exact": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.GainResult.dischargeR7_full_value": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.findReplacement_isSome": "PNP.NANDWireUnarySupportSearch",
  "PNP.DirectWire.WireUnarySupportSearch.findReplacement_sound": "PNP.NANDWireUnarySupportSearch"
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

test('M258 compiled unary support-search interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M258_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M258_COORDINATE)
    assert.equal(map.coordinate, M258_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M258_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, M258_MODULES[name], name);
      assert.deepEqual(declaration.axioms, M258_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M258_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M258_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M258_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "not completeness for all boundary widths",
  "not global minimality or unconditional ZeroSlack",
  "Boundary-choice enumeration excludes unused declared inputs",
  "inherited physical-port extraction and compilation retain their own execution costs",
  "not a theorem of total uniformly polynomial encoded-input-size execution",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M258 publication rejects weakened, supplied, assumption-backed and widened complete-calculus substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M258_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M258_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = 'PNP.DirectWire.WireUnarySupportSearch.findGain_complete';
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M258_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M258_MILESTONE
    ? {...row, nonClaim:'The unary support search proves global minimality, all boundary widths and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M258 adds complete scoped unary support-search coverage without complete-calculus, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M258_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "support-discovery edge for proper zero/unary computational R7 gains",
  "completeness for every eligible arbitrary physical support",
  "inherited physical extraction has independent costs",
  "No fixed load-bearing checkpoint changes state",
  "40% proof estimate"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M258_COORDINATE) return;
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

test('M258 current summaries distinguish scoped unary support discovery from complete-calculus and global completion and retain metrics and conditional batch publication', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_wire_unary_support_search.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "The production search does not enumerate all supports or all implementations.",
  "It is not global minimality or unconditional ZeroSlack.",
  "Whole-support saving is not a proper-support Package E certificate.",
  "Runtime execution is test evidence, not theorem authority.",
  "Publication decision: publish a batched PNPLabs update only after"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-13-computed-unary-support-search.md'));
  assert.match(plan, /Publication decision: publish a batched PNPLabs update if this complete/u);
  assert.ok(plan.includes("source-derived support-search-and-rewrite capability is earned and released."));
  if (progress.asOfCoordinate !== M258_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_wire_unary_support_search.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
