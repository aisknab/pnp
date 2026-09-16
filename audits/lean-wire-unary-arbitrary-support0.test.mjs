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

const SOURCE = 'lean/PNP/NANDWireUnaryArbitrarySupport.lean';
const AUDIT = 'lean-audit/PNPWireUnaryArbitrarySupportAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPWireUnaryArbitrarySupport.lean';
const NAMES = [
  "PNP.DirectWire.terminalOpenGateEvaluation_prefix_congr",
  "PNP.DirectWire.terminalOpenGateEvaluation_single_gate_prefix",
  "PNP.DirectWire.ArbitrarySupportSplice.graph_wellFounded_of_singleGateBoundary",
  "PNP.DirectWire.WireUnaryArbitrarySupport.constantWord_source",
  "PNP.DirectWire.WireUnaryArbitrarySupport.unaryWord_source_of_constant",
  "PNP.DirectWire.WireUnaryArbitrarySupport.localWord_source_of_constant",
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_agreement",
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_gate_bound",
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_minimal",
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_nonincrease",
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_early_constant",
  "PNP.DirectWire.WireUnaryArbitrarySupport.graph_wellFounded",
  "PNP.DirectWire.WireUnaryArbitrarySupport.compile_isSome",
  "PNP.DirectWire.WireUnaryArbitrarySupport.original_charge",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_output",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_field",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_equivalent",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_charge",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_nonincrease",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_gain_iff",
  "PNP.DirectWire.WireUnaryArbitrarySupport.proper_iff_exterior_positive",
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_isSome_iff",
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_output",
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_field",
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_nonincrease",
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_charge",
  "PNP.DirectWire.WireUnaryArbitrarySupport.dischargeR7_source_exact",
  "PNP.DirectWire.WireUnaryArbitrarySupport.dischargeR7_full_value",
  "PNP.DirectWire.WireUnaryArbitrarySupport.checkedProperGain_isSome_iff",
  "PNP.DirectWire.WireUnaryArbitrarySupport.checkedProperGain_complete",
  "PNP.DirectWire.WireUnaryArbitrarySupport.ProperGain.checked"
];
const SPECS = [
  {
    "kind": "main",
    "path": "lean/PNP/NANDWireUnaryArbitrarySupport.lean",
    "prefix": "PNP.DirectWire.WireUnaryArbitrarySupport.",
    "imports": [
      "PNP.NANDWireUnaryFrontier"
    ],
    "signatures": {
      "constantWord_source": "theorem constantWord_source (original : Implementation 0 width) (output : Fin width) : ∃ value, (WireUnaryFrontier.constantWord original).candidate.directWireWord.source output = .constant value",
      "unaryWord_source_of_constant": "theorem unaryWord_source_of_constant (original : Implementation 1 width) (output : Fin width) (constant : ∀ left right : Valuation 1, original.candidate.semantics left output = original.candidate.semantics right output) : ∃ value, (WireUnaryFrontier.unaryWord original).candidate.directWireWord.source output = .constant value",
      "localWord_source_of_constant": "theorem localWord_source_of_constant (original : Implementation inputs width) (small : inputs ≤ 1) (output : Fin width) (constant : ∀ left right : Valuation inputs, original.candidate.semantics left output = original.candidate.semantics right output) : ∃ value, (WireUnaryFrontier.localWord original small).candidate.directWireWord.source output = .constant value",
      "replacement_agreement": "theorem replacement_agreement (small : (pulled carrier records).boundary.length ≤ 1) : (replacement carrier records small).candidate.semantics = (pulled carrier records).extractedCandidate.semantics",
      "replacement_gate_bound": "theorem replacement_gate_bound (small : (pulled carrier records).boundary.length ≤ 1) : (replacement carrier records small).gateCount ≤ 1",
      "replacement_minimal": "theorem replacement_minimal (small : (pulled carrier records).boundary.length ≤ 1) (other : Implementation (pulled carrier records).boundary.length (pulled carrier records).interface.length) (sameOpen : other.candidate.semantics = (pulled carrier records).extractedCandidate.semantics) : (replacement carrier records small).gateCount ≤ other.gateCount",
      "replacement_nonincrease": "theorem replacement_nonincrease (small : (pulled carrier records).boundary.length ≤ 1) : (replacement carrier records small).gateCount ≤ (pulled carrier records).gateCount",
      "replacement_early_constant": "theorem replacement_early_constant (small : (pulled carrier records).boundary.length ≤ 1) (boundaryGate : Fin carrier.implementation.gateCount) (single : terminalBoundaryPorts carrier.exposed.candidate.program records = [.gate boundaryGate]) (port : Fin (pulled carrier records).interface.length) (before : ((pulled carrier records).interface.get port).val < boundaryGate.val) : ∃ value, (replacement carrier records small).candidate.directWireWord.source port = .constant value",
      "graph_wellFounded": "theorem graph_wellFounded (small : (pulled carrier records).boundary.length ≤ 1) : WellFounded (ArbitrarySupportSplice.graph carrier.exposed.candidate records (replacement carrier records small).candidate).Depends",
      "compile_isSome": "theorem compile_isSome (small : (pulled carrier records).boundary.length ≤ 1) : (ArbitrarySupportSplice.compile carrier.exposed.candidate records (replacement carrier records small).candidate).isSome = true",
      "original_charge": "theorem original_charge : carrier.implementation.gateCount = (pulled carrier records).gateCount + exteriorCharge carrier records",
      "expanded_output": "theorem expanded_output (small : (pulled carrier records).boundary.length ≤ 1) (valuation : Valuation inputs) (output : Fin outputs) : (expanded carrier records small).implementation.candidate.semantics valuation output = carrier.implementation.candidate.semantics valuation output",
      "expanded_field": "theorem expanded_field (small : (pulled carrier records).boundary.length ≤ 1) (valuation : Valuation inputs) (field : Fin fields) : (expanded carrier records small).fieldValue valuation field = carrier.fieldValue valuation field",
      "expanded_equivalent": "theorem expanded_equivalent (small : (pulled carrier records).boundary.length ≤ 1) : Equivalent (expanded carrier records small).implementation.candidate.program (expanded carrier records small).implementation.candidate.directWireWord carrier.implementation.candidate.program carrier.implementation.candidate.directWireWord",
      "expanded_charge": "theorem expanded_charge (small : (pulled carrier records).boundary.length ≤ 1) : (expanded carrier records small).implementation.gateCount = (replacement carrier records small).gateCount + exteriorCharge carrier records",
      "expanded_nonincrease": "theorem expanded_nonincrease (small : (pulled carrier records).boundary.length ≤ 1) : (expanded carrier records small).implementation.gateCount ≤ carrier.implementation.gateCount",
      "expanded_gain_iff": "theorem expanded_gain_iff (small : (pulled carrier records).boundary.length ≤ 1) : (expanded carrier records small).implementation.gateCount < carrier.implementation.gateCount ↔ (replacement carrier records small).gateCount < (pulled carrier records).gateCount",
      "proper_iff_exterior_positive": "theorem proper_iff_exterior_positive : (pulled carrier records).gateCount < carrier.implementation.gateCount ↔ 0 < exteriorCharge carrier records",
      "attempt_isSome_iff": "theorem attempt_isSome_iff : (attempt carrier records).isSome = true ↔ (pulled carrier records).boundary.length ≤ 1",
      "attempt_output": "theorem attempt_output (result : WireCarrier inputs outputs fields) (accepted : attempt carrier records = some result) (valuation : Valuation inputs) (output : Fin outputs) : result.implementation.candidate.semantics valuation output = carrier.implementation.candidate.semantics valuation output",
      "attempt_field": "theorem attempt_field (result : WireCarrier inputs outputs fields) (accepted : attempt carrier records = some result) (valuation : Valuation inputs) (field : Fin fields) : result.fieldValue valuation field = carrier.fieldValue valuation field",
      "attempt_nonincrease": "theorem attempt_nonincrease (result : WireCarrier inputs outputs fields) (accepted : attempt carrier records = some result) : result.implementation.gateCount ≤ carrier.implementation.gateCount",
      "attempt_charge": "theorem attempt_charge (result : WireCarrier inputs outputs fields) (accepted : attempt carrier records = some result) : ∃ small, result.implementation.gateCount = (replacement carrier records small).gateCount + exteriorCharge carrier records",
      "dischargeR7_source_exact": "theorem dischargeR7_source_exact (small : (pulled carrier records).boundary.length ≤ 1) (keep : Fin fields → Bool) (creation : WireObligationRestoration.R5Creation carrier keep) : (dischargeR7 carrier records small keep creation).actualSource = (expanded carrier records small).source creation.coordinate",
      "dischargeR7_full_value": "theorem dischargeR7_full_value (small : (pulled carrier records).boundary.length ≤ 1) (keep : Fin fields → Bool) (creation : WireObligationRestoration.R5Creation carrier keep) (valuation : Valuation inputs) : (dischargeR7 carrier records small keep creation).actualSource.eval valuation ((expanded carrier records small).implementation.candidate.program.eval valuation) = carrier.fieldValue valuation creation.coordinate",
      "checkedProperGain_isSome_iff": "theorem checkedProperGain_isSome_iff : (checkedProperGain carrier records).isSome = true ↔ ∃ small, 0 < exteriorCharge carrier records ∧ (replacement carrier records small).gateCount < (pulled carrier records).gateCount",
      "checkedProperGain_complete": "theorem checkedProperGain_complete (small : (pulled carrier records).boundary.length ≤ 1) (proper : 0 < exteriorCharge carrier records) (other : Implementation (pulled carrier records).boundary.length (pulled carrier records).interface.length) (sameOpen : other.candidate.semantics = (pulled carrier records).extractedCandidate.semantics) (smaller : other.gateCount < (pulled carrier records).gateCount) : (checkedProperGain carrier records).isSome = true",
      "ProperGain.checked": "theorem ProperGain.checked {carrier : WireCarrier inputs outputs fields} {records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0)} (gain : ProperGain carrier records) : (pulled carrier records).gateCount < carrier.implementation.gateCount ∧ StrictEquivalentGain carrier.implementation (expanded carrier records gain.small).implementation ∧ (∀ valuation field, (expanded carrier records gain.small).fieldValue valuation field = carrier.fieldValue valuation field) ∧ (expanded carrier records gain.small).implementation.gateCount = (replacement carrier records gain.small).gateCount + exteriorCharge carrier records"
    },
    "heads": [
      "constantWord_source",
      "unaryWord_source_of_constant",
      "localWord_source_of_constant",
      "pulled",
      "exteriorCharge",
      "replacement",
      "replacement_agreement",
      "replacement_gate_bound",
      "replacement_minimal",
      "replacement_nonincrease",
      "replacement_early_constant",
      "graph_wellFounded",
      "compile_isSome",
      "compiled",
      "expanded",
      "original_charge",
      "expanded_output",
      "expanded_field",
      "expanded_equivalent",
      "expanded_charge",
      "expanded_nonincrease",
      "expanded_gain_iff",
      "proper_iff_exterior_positive",
      "attempt",
      "attempt_isSome_iff",
      "attempt_output",
      "attempt_field",
      "attempt_nonincrease",
      "attempt_charge",
      "ExpandedDischarge",
      "dischargeR7",
      "dischargeR7_source_exact",
      "dischargeR7_full_value",
      "ProperGain",
      "checkedProperGain",
      "checkedProperGain_isSome_iff",
      "checkedProperGain_complete",
      "ProperGain.strictGain",
      "ProperGain.checked"
    ]
  },
  {
    "kind": "splice",
    "path": "lean/PNP/NANDArbitrarySupportSplice.lean",
    "prefix": "PNP.DirectWire.ArbitrarySupportSplice.",
    "imports": [
      "PNP.NANDTopologicalCompiler",
      "PNP.NANDTopologicalCausalBounds",
      "PNP.ResidualTerminalSaturatedSupportContext",
      "PNP.NANDNormalizationCausalBounds"
    ],
    "signatures": {
      "graph_wellFounded_of_singleGateBoundary": "theorem graph_wellFounded_of_singleGateBoundary (boundaryGate : Fin gates) (single : terminalBoundaryPorts candidate.program records = [.gate boundaryGate]) (small : replacementGates ≤ 1) (early : ∀ port : Fin (terminalInterfacePorts candidate records).length, ((terminalInterfacePorts candidate records).get port).val < boundaryGate.val → ∃ value, replacement.directWireWord.source port = .constant value) : WellFounded (graph candidate records replacement).Depends"
    },
    "heads": [
      "sources_eval",
      "sources_ordered",
      "exterior",
      "mem_exterior_iff",
      "boundarySource",
      "replacementSource",
      "Visible",
      "originalSource",
      "exteriorSource_visible",
      "output_visible",
      "exteriorGate",
      "replacementGate",
      "graph",
      "word",
      "compile",
      "result",
      "result_gateCount",
      "compile_success_iff",
      "compile_failure_iff",
      "values",
      "replacementSource_eval",
      "originalSource_eval",
      "values_solution",
      "result_semantics",
      "exterior_accounting",
      "result_exact_accounting",
      "result_strict_gain",
      "PrimaryBoundary",
      "rank",
      "graph_rank_decreases",
      "graph_wellFounded_of_primaryBoundary",
      "production_compiles",
      "production_agreement",
      "graph_wellFounded_of_singleGateBoundary",
      "causalBoundaryLabels",
      "CausalInterfaceBound",
      "causalRank",
      "graph_causal_rank_decreases",
      "graph_wellFounded_of_causalInterfaceBound",
      "compile_of_causalInterfaceBound",
      "dependencyBoundaryLabels",
      "dependencyCaps",
      "DependencyInterfaceBound",
      "graph_dependency_bounds",
      "result_output_dependency_bound"
    ]
  },
  {
    "kind": "extraction",
    "path": "lean/PNP/ResidualTerminalSupportExtraction.lean",
    "prefix": "PNP.DirectWire.",
    "imports": [
      "PNP.ResidualTerminalPhysicalSupportCompletion",
      "PNP.NANDCausalBounds"
    ],
    "signatures": {
      "terminalOpenGateEvaluation_prefix_congr": "theorem terminalOpenGateEvaluation_prefix_congr {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (left right : Valuation (terminalBoundaryPorts candidate.program records).length) (cutoff : Nat) (agreement : forall port : Fin (terminalBoundaryPorts candidate.program records).length, (match (terminalBoundaryPorts candidate.program records).get port with | .input _ => True | .gate boundaryGate => boundaryGate.val < cutoff) -> left port = right port) (gate : Fin gates) (before : gate.val < cutoff) : terminalOpenGateEvaluation candidate records left gate = terminalOpenGateEvaluation candidate records right gate",
      "terminalOpenGateEvaluation_single_gate_prefix": "theorem terminalOpenGateEvaluation_single_gate_prefix {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (boundaryGate : Fin gates) (single : terminalBoundaryPorts candidate.program records = [.gate boundaryGate]) (left right : Valuation (terminalBoundaryPorts candidate.program records).length) (gate : Fin gates) (before : gate.val < boundaryGate.val) : terminalOpenGateEvaluation candidate records left gate = terminalOpenGateEvaluation candidate records right gate"
    },
    "heads": [
      "terminalSelectedGateIndices",
      "terminalSelectedGates",
      "mem_terminalSelectedGateIndices_iff",
      "mem_terminalSelectedGates_iff",
      "terminalSelectedGateIndices_nodup",
      "terminalSelectedGates_nodup",
      "TerminalExtractedSupport",
      "extractTerminalSupport",
      "extractTerminalSupport_records",
      "extractTerminalSupport_boundary",
      "extractTerminalSupport_selectedGates",
      "extractTerminalSupport_interface",
      "extractTerminalSupport_gateCount",
      "terminalExtractionGateIndex",
      "terminalExtractionOrigin",
      "terminalExtractionOrigin_selected",
      "terminalExtractionGateIndex_origin",
      "terminalExtractionOrigin_gateIndex",
      "terminalExtractionOrigin_injective",
      "terminalOpenGateEvaluation",
      "terminalOpenSupportSemantics",
      "TerminalSupportWire.candidateValue",
      "TerminalSupportWire.causalLevel",
      "terminalBoundaryCausalLabels",
      "terminalExtractedInterfaceCausalLevel",
      "extractTerminalSupport_causal_levels",
      "extractTerminalSupport_causal_index",
      "terminalInducedBoundaryValuation",
      "terminalOpenGateEvaluation_induced_selected",
      "terminalOpenSupportSemantics_induced",
      "extractTerminalSupport_semantics",
      "extractTerminalSupport_induced",
      "extractSaturatedTerminalSupport",
      "extractSaturatedTerminalSupport_records",
      "extractSaturatedTerminalSupport_gateCount",
      "extractSaturatedTerminalSupport_semantics",
      "extractSaturatedTerminalSupport_induced",
      "extractTerminalSupport_eq_of_gateSelected_eq",
      "terminalOpenGateEvaluation_prefix_congr",
      "terminalOpenGateEvaluation_single_gate_prefix",
      "terminalOpenWireValue",
      "terminalBoundaryPullback",
      "terminalOpenGateEvaluation_pullback",
      "terminalOpenSupportSemantics_pullback",
      "terminalBoundaryPullback_identity",
      "terminalBoundaryPullback_compose"
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
  const clean=compact0(source), block=name=>block0(source,name);
  const includes=(name,tokens,category)=>require0(tokens.every(token=>block(name).includes(token)),category);
  require0(!hasLeanAssumptionDeclaration0(source),'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source),'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|suppliedTable|suppliedResult|callerCertificate|suppliedOrder)\b/u.test(clean),'shortcut-or-certificate');
  require0(!/\b(?:allCandidates|allBoolTuples|allSubsets|equivalentBool|referenceMinimum|scanEquivalentSizes|terminalFullProfileMinimum)\b/u.test(clean),'no-implementation-enumeration');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]))===
    JSON.stringify(spec.imports),'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name))===
    JSON.stringify(spec.heads),'public-interface');
  for(const [name,signature] of Object.entries(spec.signatures))
    require0(signature0(block(name))===signature,'signature:'+name);
  if(spec.kind==='extraction'){
    includes('Program.evalTerminalOpenAux_prefix_congr',[
      'induction program','Nat.lt_trans prior.isLt before',
    ],'actual-program-prefix-causality');
    includes('terminalOpenGateEvaluation_prefix_congr',[
      'candidate.program.evalTerminalOpenAux_prefix_congr','wireEqual (.input index)',
      'wireEqual (.gate index)',
    ],'all-open-boundary-values');
    includes('terminalOpenGateEvaluation_single_gate_prefix',[
      'terminalOpenGateEvaluation_prefix_congr candidate records left right',
      'boundaryGate.val','List.mem_singleton.mp',
    ],'sole-external-boundary-prefix');
    return [...new Set(failures)];
  }
  if(spec.kind==='splice'){
    includes('singleGateRank',[
      '2 * ((exterior records).get index).val','2 * boundaryGate.val + 1',
    ],'derived-original-rank');
    includes('singleGateOriginalSource_rank_lt',[
      'early (memberIndex (visible producer rfl selected))','rw [literal] at same',
      'singleGateReplacementSource_rank_bound','get_memberIndex',
    ],'literal-early-outputs-remove-backward-edges');
    includes('graph_wellFounded_of_singleGateBoundary',[
      'rank_accessible _ (singleGateRank records boundaryGate)',
      'singleGateGraph_rank_decreases candidate records replacement boundaryGate single small early',
    ],'actual-graph-well-founded');
    return [...new Set(failures)];
  }
  require0(clean.includes('variable {inputs outputs fields width : Nat}'),'unbounded-dimensions');
  require0(clean.includes('variable (carrier : WireCarrier inputs outputs fields) (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0))'),
    'arbitrary-input-support');
  require0(block('pulled').endsWith('extractTerminalSupport carrier.exposed.candidate records'),
    'actual-full-support-extraction');
  require0(block('exteriorCharge').endsWith('(ArbitrarySupportSplice.exterior records).length'),
    'actual-exterior-count');
  require0(block('replacement').endsWith('WireUnaryFrontier.localWord (pulled carrier records).extractedCandidate.toImplementation small'),
    'source-derived-local-word');
  includes('unaryWord_source_of_constant',[
    'WireUnaryRealization.implementation carrier','WireUnaryRealization.oneImplementation carrier',
    'WireUnaryRealization.zeroImplementation carrier','unpack_source','literalAt',
  ],'literal-source-not-semantic-promise');
  includes('replacement_agreement',[
    'funext valuation output','WireUnaryFrontier.localWord_value _ small valuation output',
  ],'all-open-agreement');
  includes('replacement_early_constant',[
    'localWord_source_of_constant _ small port','extractTerminalSupport_semantics',
    'terminalOpenGateEvaluation_single_gate_prefix',
  ],'derived-early-constant');
  includes('graph_wellFounded',[
    'shortList (terminalBoundaryPorts carrier.exposed.candidate.program records) small',
    'ArbitrarySupportSplice.graph_wellFounded_of_primaryBoundary',
    'ArbitrarySupportSplice.graph_wellFounded_of_singleGateBoundary',
    'replacement_gate_bound carrier records small',
    'replacement_early_constant carrier records small boundaryGate single',
  ],'all-computed-boundary-cases');
  includes('compile_isSome',[
    'ArbitrarySupportSplice.compile_success_iff','graph_wellFounded carrier records small',
  ],'derived-compiler-success');
  require0(block('compiled').endsWith(
    '(ArbitrarySupportSplice.compile carrier.exposed.candidate records (replacement carrier records small).candidate).get (compile_isSome carrier records small)'),
    'actual-compiler-result');
  require0(block('expanded').endsWith(
    'carrier.spliceResult records (replacement carrier records small).candidate (compiled carrier records small)'),
    'actual-expanded-carrier');
  require0(block('attempt')===
    'def attempt : Option (WireCarrier inputs outputs fields) := if small : (pulled carrier records).boundary.length ≤ 1 then some (expanded carrier records small) else none',
    'boundary-only-query');
  includes('expanded_field',[
    'carrier.splice_field records _ (replacement_agreement carrier records small)',
    '(compiled carrier records small) valuation field',
  ],'full-field-value-preservation');
  includes('dischargeR7',[
    'actualSource := (expanded carrier records small).source creation.coordinate',
    'rw [creation.sourceExact]','expanded_field carrier records small valuation creation.coordinate',
  ],'source-exact-full-r7');
  includes('ProperGain',[
    'small : (pulled carrier records).boundary.length ≤ 1',
    'proper : 0 < exteriorCharge carrier records',
    'smaller : (replacement carrier records small).gateCount < (pulled carrier records).gateCount',
  ],'physical-proper-gain');
  includes('checkedProperGain',[
    'if small : (pulled carrier records).boundary.length ≤ 1 then',
    'if proper : 0 < exteriorCharge carrier records then',
    'if smaller : (replacement carrier records small).gateCount < (pulled carrier records).gateCount then',
    'some ⟨small, proper, smaller⟩',
  ],'computed-strict-gain');
  return [...new Set(failures)];
}
const mainSpec=SPECS.find(spec=>spec.kind==='main');
function rejectMutations0(source,spec,mutations) {
  for(const [before,after,category] of mutations){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after),spec).includes(category),category);
  }
}
test('M257 has closed general source, prefix-causality and literal-splice interfaces',async()=>{
  for(const spec of SPECS)assert.deepEqual(validateSource0(await text0(spec.path),spec),[],spec.path);
});
test('M257 root, exact theorem-name producers and axiom audit agree',async()=>{
  const [audit,inventory,root]=await Promise.all([
    text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean')]);
  for(const name of NAMES){
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item=>item===name).length,1,name);
    assert.equal(inventory.split(String.fromCharCode(96)+name+',').length-1,1,name);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),NAMES);
  assert.match(root,/^import PNP\.NANDWireUnaryArbitrarySupport\s*$/mu);
});
test('M257 rejects substituted support, replacement, compiler and expanded result',async()=>{
  rejectMutations0(await text0(SOURCE),mainSpec,[
    ['extractTerminalSupport carrier.exposed.candidate records','extractTerminalSupport carrier.exposed.candidate []','actual-full-support-extraction'],
    ['WireUnaryFrontier.localWord (pulled carrier records).extractedCandidate.toImplementation small','WireUnaryFrontier.localWord suppliedResult small','source-derived-local-word'],
    ['(ArbitrarySupportSplice.compile carrier.exposed.candidate records\n    (replacement carrier records small).candidate).get (compile_isSome carrier records small)','suppliedResult','actual-compiler-result'],
    ['carrier.spliceResult records (replacement carrier records small).candidate\n    (compiled carrier records small)','suppliedResult','actual-expanded-carrier'],
  ]);
});
test('M257 rejects finite dimensions, extra query premises and unsupported boundaries',async()=>{
  rejectMutations0(await text0(SOURCE),mainSpec,[
    ['variable {inputs outputs fields width : Nat}','variable {outputs fields width : Nat}','unbounded-dimensions'],
    ['def attempt : Option (WireCarrier inputs outputs fields)','def attempt (callerCertificate : True) : Option (WireCarrier inputs outputs fields)','boundary-only-query'],
    ['if small : (pulled carrier records).boundary.length ≤ 1 then','if small : (pulled carrier records).boundary.length ≤ 2 then','boundary-only-query'],
    ['theorem compile_isSome (small : (pulled carrier records).boundary.length ≤ 1)',
      'theorem compile_isSome (small : (pulled carrier records).boundary.length ≤ 1) (suppliedOrder : True)','signature:compile_isSome'],
  ]);
});
test('M257 rejects induced-only semantics and unproved earlier constants',async()=>{
  rejectMutations0(await text0(SOURCE),mainSpec,[
    ['funext valuation output','funext output','all-open-agreement'],
    ['terminalOpenGateEvaluation_single_gate_prefix carrier.exposed.candidate records',
      'callerCertificate carrier.exposed.candidate records','derived-early-constant'],
    ['(replacement_early_constant carrier records small boundaryGate single)',
      'callerCertificate','all-computed-boundary-cases'],
  ]);
  const spec=SPECS.find(item=>item.kind==='extraction');
  rejectMutations0(await text0(spec.path),spec,[
    ['candidate.program.evalTerminalOpenAux_prefix_congr','callerCertificate','all-open-boundary-values'],
    ['(left right : Valuation (terminalBoundaryPorts candidate.program records).length)',
      '(left : Valuation (terminalBoundaryPorts candidate.program records).length)','signature:terminalOpenGateEvaluation_prefix_congr'],
  ]);
});
test('M257 rejects cyclic ranks, nonliteral earlier outputs and removed smallness',async()=>{
  const spec=SPECS.find(item=>item.kind==='splice');
  rejectMutations0(await text0(spec.path),spec,[
    ['2 * boundaryGate.val + 1','2 * boundaryGate.val - 1','derived-original-rank'],
    ['rw [literal] at same','skip','literal-early-outputs-remove-backward-edges'],
    ['(small : replacementGates ≤ 1)','(small : True)','signature:graph_wellFounded_of_singleGateBoundary'],
  ]);
});
test('M257 rejects incomplete fields, ambient-only minima and wrong exterior accounting',async()=>{
  rejectMutations0(await text0(SOURCE),mainSpec,[
    ['carrier.splice_field records _ (replacement_agreement carrier records small)','carrier.splice_field records _ callerCertificate','full-field-value-preservation'],
    ['(sameOpen : other.candidate.semantics =\n      (pulled carrier records).extractedCandidate.semantics)','(sameOpen : True)','signature:replacement_minimal'],
    ['(replacement carrier records small).gateCount + exteriorCharge carrier records',
      '(replacement carrier records small).gateCount + 2 * exteriorCharge carrier records','signature:expanded_charge'],
    ['(replacement carrier records small).gateCount ≤ other.gateCount',
      'other.gateCount ≤ (replacement carrier records small).gateCount','signature:replacement_minimal'],
  ]);
});
test('M257 rejects padding discharges, whole-support properness and nonstrict gains',async()=>{
  rejectMutations0(await text0(SOURCE),mainSpec,[
    ['actualSource := (expanded carrier records small).source creation.coordinate','actualSource := .constant false','source-exact-full-r7'],
    ['proper : 0 < exteriorCharge carrier records','proper : 0 ≤ exteriorCharge carrier records','physical-proper-gain'],
    ['if smaller : (replacement carrier records small).gateCount <','if smaller : (replacement carrier records small).gateCount ≤','computed-strict-gain'],
    ['(∀ valuation field, (expanded carrier records gain.small).fieldValue valuation field =',
      '(∃ valuation field, (expanded carrier records gain.small).fieldValue valuation field =','signature:ProperGain.checked'],
  ]);
});
test('M257 rejects assumptions, unaudited forms and exhaustive implementation search',async()=>{
  const source=await text0(SOURCE);
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n',mainSpec).includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n',mainSpec).includes('unaudited-form'));
  assert.ok(validateSource0(source+'\ndef unauthorized := allSubsets\n',mainSpec).includes('no-implementation-enumeration'));
});
test('M257 regression retains general signatures and guarded hostile arbitrary supports',async()=>{
  const source=await text0(REGRESSION);
  assert.match(source,/^import PNP\s*$/mu);
  for(const name of ['external-gate-cycle-prevention','unrealizable-boundary-bit',
    'repeated-nonprefix-support','constant-support','external-gate-no-saving',
    'whole-support-is-not-proper','input-plus-exterior-boundary-rejected',
    'empty-selected-support','nonzero-primary-input','hidden-selected-negation',
    'one-shared-negation','two-primary-inputs-rejected','field-only-selected',
    'field-only-exterior','free-input-and-constant-fields','empty-dimensions'])
    assert.ok(source.includes('"'+name+'"'),name);
  assert.ok(source.includes('inputs > 3 || outputs > 4 || fields > 5 || carrier.implementation.gateCount > 3'));
  assert.ok(source.includes('records.length > 6'));
  assert.ok(source.includes('for mask in List.range (2 ^ support.boundary.length)'));
  assert.ok(source.includes('witness.actualSource ≠ built.source field'));
  assert.ok(source.includes('M257_COMPUTED_UNARY_ARBITRARY_SUPPORT_RUNTIME_FIXTURES_GREEN'));
});
test('M257 durable workflow retains explicit-root audit and bounded regression',async()=>{
  const workflow=await text0('.github/workflows/lean-bridge.yml');
  assert.ok(workflow.includes('Audit computed unary arbitrary-support replacement'));
  assert.ok(workflow.includes('node --test audits/lean-wire-unary-arbitrary-support0.test.mjs'));
  assert.ok(workflow.includes('lake env lean -DwarningAsError=true '+AUDIT));
  assert.ok(workflow.includes('lake env lean -DwarningAsError=true '+REGRESSION));
  for(const name of NAMES)assert.ok(workflow.includes('"'+name+'"'),name);
});

const M257_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-13-257';
const M257_MILESTONE = 'wire-unary-arbitrary-support';
const M257_HASHES = Object.freeze({
  "PNP.DirectWire.terminalOpenGateEvaluation_prefix_congr": "0061f7c437b7e27d395569d35d48fe9855416854bdfb7cd22e4c78821cebff01",
  "PNP.DirectWire.terminalOpenGateEvaluation_single_gate_prefix": "d245e3b3e3315e77d7e1f0ca38c2bc9ac0ad8bc60ce4d85eb6fbb61dc628dc7f",
  "PNP.DirectWire.ArbitrarySupportSplice.graph_wellFounded_of_singleGateBoundary": "131ac4d4b954bfccdfb334f7592d63c49f7b0f8cbef14dfbd9708672f0622d9b",
  "PNP.DirectWire.WireUnaryArbitrarySupport.constantWord_source": "b18c68167c2cf5438f22a797e59049c228249a41db1df94fb3c68f4a255963cc",
  "PNP.DirectWire.WireUnaryArbitrarySupport.unaryWord_source_of_constant": "60d8adc847127db61ed6db043d02138664e66b9a200bc99b9b1b3f0510fdeace",
  "PNP.DirectWire.WireUnaryArbitrarySupport.localWord_source_of_constant": "4b8ba04460c91c0e6ee0f01e22d3c0be608d2ea54dd0224826f961d937f5965b",
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_agreement": "74d4b769ab2f48a65f221ba3e8811d4bc83b47ee8d4e49f70ceefacbda5f5cfd",
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_gate_bound": "ef7907c6929e65f812aa3844e922101642a88044dbcdc1136626452789aa8fef",
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_minimal": "3418c00e0587573e9846fe69fe66c478ed027632bf7d0f50cd3d1485106967d1",
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_nonincrease": "9a691e352f9e7e2343d297c759286c8cee0962cd9a15e4bcf8a890f8027530ac",
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_early_constant": "3220d6d9eda3f54ad07c5fb7db7f0bf00b44327d56638164662a08dbe56e4bfb",
  "PNP.DirectWire.WireUnaryArbitrarySupport.graph_wellFounded": "657338f0205eadf7e6f37e70791da590374f199c08f737cd117ecfd42b819fb0",
  "PNP.DirectWire.WireUnaryArbitrarySupport.compile_isSome": "0b40032fd8e0e14732dac199a115ec61ef9290c916860bd70bd3b15f42d92e61",
  "PNP.DirectWire.WireUnaryArbitrarySupport.original_charge": "9c1feaa37b5a1fef557510998992eb40d5e5da7dde9b473b0b01868cd9cfabe3",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_output": "ef4023d873287ec9b791acd9fc6756f06f96f287cbc0944dbe960b80c6b21e67",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_field": "292b86e2253a9767a078cce964dd0896d49a644dd64a322bd85fff531ecf7481",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_equivalent": "e28606e602cc080a5d5a140f2101ecf705212c55372cedc7d96b63857af0c8b6",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_charge": "55ec202abef861068266ee283243cfe5064fcf6378328f4df87e59c39f9e278d",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_nonincrease": "29f691ff3546ab68f504a9d1afa7e6d320ad8c486061be0eff2c5a287dadafe7",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_gain_iff": "a30977882e20c40433ceafe9b8c2a6c1766563afe36815f233e25c5ddd2fddfd",
  "PNP.DirectWire.WireUnaryArbitrarySupport.proper_iff_exterior_positive": "59d8d725ad98e586da3887e5ffbdc7f8dba0c98a209dd9d6c1fbb41fb23dca43",
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_isSome_iff": "b3fd2f73e6aa15a4f4f5eee75d4261473c49a1d994ef023bd12e74f9950cebff",
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_output": "c3f76011dd727f6e2479a1074dc8cf1b9f5c2ab4b85306dd038c0fdb1126b881",
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_field": "82d5498fcea1f4c0e8fbdbbc3f0f74cee2a44c97d84ad9b5e987301d5ab30924",
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_nonincrease": "10a5d687494ddb4e1b7f549b0d5de87af50285e7c753b2e63a4f720ef6bdcfb9",
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_charge": "9c3d33ffd1e0e2506aba7e7b4303991bda2bbb8b5f2cb685a7345ff1a8a5544a",
  "PNP.DirectWire.WireUnaryArbitrarySupport.dischargeR7_source_exact": "17e1f9fe0e9e1ab2675094cb0ac78aef910bd5874ac89abd74fa24f564335764",
  "PNP.DirectWire.WireUnaryArbitrarySupport.dischargeR7_full_value": "aa59004c5807cf81b93fee7ba5b990c274d19760237740386541a96ad82b587b",
  "PNP.DirectWire.WireUnaryArbitrarySupport.checkedProperGain_isSome_iff": "b5b5fcf8e6bfcc58f1fa6350972dbc222bd0219cad0409163191075f333f39b6",
  "PNP.DirectWire.WireUnaryArbitrarySupport.checkedProperGain_complete": "d6a6a6ab8f1b05050a450e078a96abf2fdd9b1e23557191928fc6ec00603bd41",
  "PNP.DirectWire.WireUnaryArbitrarySupport.ProperGain.checked": "0b9d4a813bdd0931dc63942366a1e181a2f7d13a84aaf796aeda9b75b6687961"
});
const M257_STATUS_FIELDS = Object.freeze({
  "leanWireUnaryArbitrarySupportFormalized": true,
  "leanWireUnaryArbitrarySupportAxiomAuditPassed": true,
  "leanWireUnaryArbitrarySupportAuditedDeclarationCount": 31,
  "leanWireUnaryArbitrarySupportPrefixCausalityTheorem": "PNP.DirectWire.terminalOpenGateEvaluation_prefix_congr",
  "leanWireUnaryArbitrarySupportSingleBoundaryCausalityTheorem": "PNP.DirectWire.terminalOpenGateEvaluation_single_gate_prefix",
  "leanWireUnaryArbitrarySupportSingleBoundaryRankTheorem": "PNP.DirectWire.ArbitrarySupportSplice.graph_wellFounded_of_singleGateBoundary",
  "leanWireUnaryArbitrarySupportConstantSourceTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.constantWord_source",
  "leanWireUnaryArbitrarySupportUnaryLiteralConstantTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.unaryWord_source_of_constant",
  "leanWireUnaryArbitrarySupportLocalLiteralConstantTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.localWord_source_of_constant",
  "leanWireUnaryArbitrarySupportReplacementAgreementTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_agreement",
  "leanWireUnaryArbitrarySupportReplacementGateBoundTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_gate_bound",
  "leanWireUnaryArbitrarySupportReplacementMinimumTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_minimal",
  "leanWireUnaryArbitrarySupportReplacementNonincreaseTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_nonincrease",
  "leanWireUnaryArbitrarySupportEarlyFrontierConstantTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_early_constant",
  "leanWireUnaryArbitrarySupportWellFoundedTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.graph_wellFounded",
  "leanWireUnaryArbitrarySupportCompilerSuccessTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.compile_isSome",
  "leanWireUnaryArbitrarySupportOriginalChargeTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.original_charge",
  "leanWireUnaryArbitrarySupportOutputTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_output",
  "leanWireUnaryArbitrarySupportFieldTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_field",
  "leanWireUnaryArbitrarySupportEquivalenceTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_equivalent",
  "leanWireUnaryArbitrarySupportExactChargeTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_charge",
  "leanWireUnaryArbitrarySupportNonincreaseTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_nonincrease",
  "leanWireUnaryArbitrarySupportGainIffTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_gain_iff",
  "leanWireUnaryArbitrarySupportProperExteriorIffTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.proper_iff_exterior_positive",
  "leanWireUnaryArbitrarySupportAttemptIffTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_isSome_iff",
  "leanWireUnaryArbitrarySupportAttemptOutputTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_output",
  "leanWireUnaryArbitrarySupportAttemptFieldTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_field",
  "leanWireUnaryArbitrarySupportAttemptNonincreaseTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_nonincrease",
  "leanWireUnaryArbitrarySupportAttemptChargeTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_charge",
  "leanWireUnaryArbitrarySupportR7SourceExactTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.dischargeR7_source_exact",
  "leanWireUnaryArbitrarySupportR7FullValueTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.dischargeR7_full_value",
  "leanWireUnaryArbitrarySupportProperGainIffTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.checkedProperGain_isSome_iff",
  "leanWireUnaryArbitrarySupportProperGainCompletenessTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.checkedProperGain_complete",
  "leanWireUnaryArbitrarySupportCheckedProperGainTheorem": "PNP.DirectWire.WireUnaryArbitrarySupport.ProperGain.checked",
  "leanWireUnaryArbitrarySupportAllBoundaryWidthsCovered": false,
  "leanWireUnaryArbitrarySupportAllR7CasesDerived": false,
  "leanWireUnaryArbitrarySupportArbitraryObligationDAGsCovered": false,
  "leanWireUnaryArbitrarySupportFullManuscriptCarrierProved": false,
  "leanWireUnaryArbitrarySupportCompleteObligationCalculusProved": false,
  "leanWireUnaryArbitrarySupportCompletePackageEProved": false,
  "leanWireUnaryArbitrarySupportPolynomialRuntimeProved": false,
  "leanWireUnaryArbitrarySupportScope": "all-finite-computational-wire-arbitrary-physical-support-completed-frontier-zero-or-one-actual-boundary-including-external-gate-source-derived-prefix-causality-minimum-local-word-ranked-actual-compiler-original-exterior-once-full-fields-source-exact-r7-proper-gain-no-general-calculus-or-polynomial-runtime"
});
const M257_AXIOMS = Object.freeze({
  "PNP.DirectWire.terminalOpenGateEvaluation_prefix_congr": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalOpenGateEvaluation_single_gate_prefix": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.ArbitrarySupportSplice.graph_wellFounded_of_singleGateBoundary": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.constantWord_source": [],
  "PNP.DirectWire.WireUnaryArbitrarySupport.unaryWord_source_of_constant": [
    "Quot.sound"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.localWord_source_of_constant": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_agreement": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_gate_bound": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_minimal": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_nonincrease": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_early_constant": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.graph_wellFounded": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.compile_isSome": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.original_charge": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_output": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_equivalent": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_charge": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_nonincrease": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_gain_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.proper_iff_exterior_positive": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_isSome_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_output": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_field": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_nonincrease": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_charge": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.dischargeR7_source_exact": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.dischargeR7_full_value": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.checkedProperGain_isSome_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.checkedProperGain_complete": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.WireUnaryArbitrarySupport.ProperGain.checked": [
    "Quot.sound",
    "propext"
  ]
});

const M257_MODULES = Object.freeze({
  "PNP.DirectWire.WireUnaryArbitrarySupport.constantWord_source": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.unaryWord_source_of_constant": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.localWord_source_of_constant": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_agreement": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_gate_bound": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_minimal": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_nonincrease": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.replacement_early_constant": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.graph_wellFounded": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.compile_isSome": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.original_charge": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_output": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_field": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_equivalent": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_charge": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_nonincrease": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.expanded_gain_iff": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.proper_iff_exterior_positive": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_isSome_iff": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_output": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_field": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_nonincrease": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.attempt_charge": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.dischargeR7_source_exact": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.dischargeR7_full_value": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.checkedProperGain_isSome_iff": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.checkedProperGain_complete": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.WireUnaryArbitrarySupport.ProperGain.checked": "PNP.NANDWireUnaryArbitrarySupport",
  "PNP.DirectWire.ArbitrarySupportSplice.graph_wellFounded_of_singleGateBoundary": "PNP.NANDArbitrarySupportSplice",
  "PNP.DirectWire.terminalOpenGateEvaluation_prefix_congr": "PNP.ResidualTerminalSupportExtraction",
  "PNP.DirectWire.terminalOpenGateEvaluation_single_gate_prefix": "PNP.ResidualTerminalSupportExtraction"
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

test('M257 compiled unary arbitrary-support interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M257_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M257_COORDINATE)
    assert.equal(map.coordinate, M257_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M257_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, M257_MODULES[name], name);
      assert.deepEqual(declaration.axioms, M257_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M257_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M257_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M257_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "not arbitrary boundary width",
  "not over all ambient circuits or different exteriors",
  "whole-support saving is not a proper-support Package E certificate",
  "not uniformly polynomial encoded-size execution",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M257 publication rejects weakened, supplied, assumption-backed and widened complete-calculus substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M257_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M257_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = 'PNP.DirectWire.WireUnaryArbitrarySupport.attempt_field';
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M257_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M257_MILESTONE
    ? {...row, nonClaim:'The arbitrary-support unary replacement proves all boundary widths, the complete obligation calculus and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M257 adds computed unary arbitrary-support coverage without complete-calculus, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M257_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "arbitrary completed computational supports",
  "derived from the source rather than supplied",
  "positive exterior and strict local saving",
  "No fixed load-bearing checkpoint changes state",
  "40% proof estimate"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M257_COORDINATE) return;
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

test('M257 current summaries distinguish computed unary arbitrary-support replacement from complete-calculus and global completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_wire_unary_arbitrary_support.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "Every recognized arbitrary support compiles.",
  "not ordinary-output-only agreement",
  "Whole-support saving",
  "Runtime execution is test evidence, not theorem authority",
  "Publication decision: defer PNPLabs."
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-13-computed-unary-arbitrary-support.md'));
  assert.match(plan, /Publication decision: defer PNPLabs(?:[.,]|$)/u);
  if (progress.asOfCoordinate !== M257_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_wire_unary_arbitrary_support.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
