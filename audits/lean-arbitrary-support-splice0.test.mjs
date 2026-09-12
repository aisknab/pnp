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

const SOURCES = [
  {
    "kind": "compiler",
    "path": "lean/PNP/NANDTopologicalCompiler.lean",
    "prefix": "PNP.DirectWire.",
    "imports": [
      "PNP.NANDSlack",
      "Init.Data.List.FinRange",
      "Init.Data.List.Erase"
    ],
    "signatures": {
      "RawNandCompilationState.readSource_sound": "theorem RawNandCompilationState.readSource_sound {inputs nodes : Nat} {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph) (source : Source inputs nodes) (translated : Source inputs state.count) (found : state.readSource source = some translated) (input : Valuation inputs) (values : Valuation nodes) (equations : graph.Solution input values) : translated.eval input (state.program.eval input) = source.eval input values",
      "RawNandCompilationState.readGate_sound": "theorem RawNandCompilationState.readGate_sound {inputs nodes : Nat} {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph) (node : Fin nodes) (translated : Gate inputs state.count) (found : state.readGate node = some translated) (input : Valuation inputs) (values : Valuation nodes) (equations : graph.Solution input values) : translated.eval input (state.program.eval input) = values node",
      "RawNandReadyStep.apply_remaining_lt": "theorem RawNandReadyStep.apply_remaining_lt {inputs nodes : Nat} {graph : RawNandGraph inputs nodes} {state : RawNandCompilationState graph} (step : RawNandReadyStep state) : step.apply.remaining.length < state.remaining.length",
      "RawNandCompilationStop.unresolved_predecessor": "theorem RawNandCompilationStop.unresolved_predecessor {inputs nodes : Nat} {graph : RawNandGraph inputs nodes} (stop : RawNandCompilationStop graph) (node : Fin nodes) (member : node ∈ stop.state.remaining) : ∃ producer, producer ∈ stop.state.remaining ∧ graph.Depends producer node",
      "RawNandCompilationStop.complete_of_wellFounded": "theorem RawNandCompilationStop.complete_of_wellFounded {inputs nodes : Nat} {graph : RawNandGraph inputs nodes} (stop : RawNandCompilationStop graph) (acyclic : WellFounded graph.Depends) : stop.state.remaining = []",
      "CompiledRawNandGraph.wellFounded": "theorem CompiledRawNandGraph.wellFounded {inputs nodes : Nat} {graph : RawNandGraph inputs nodes} (compiled : CompiledRawNandGraph graph) : WellFounded graph.Depends",
      "compileRawNandGraph_success_iff": "theorem compileRawNandGraph_success_iff {inputs nodes : Nat} (graph : RawNandGraph inputs nodes) : (∃ compiled, compileRawNandGraph graph = some compiled) ↔ WellFounded graph.Depends",
      "compileRawNandGraph_failure_iff": "theorem compileRawNandGraph_failure_iff {inputs nodes : Nat} (graph : RawNandGraph inputs nodes) : compileRawNandGraph graph = none ↔ ¬WellFounded graph.Depends",
      "CompiledRawNandGraph.candidate_gateCount": "theorem CompiledRawNandGraph.candidate_gateCount {inputs nodes outputs : Nat} {graph : RawNandGraph inputs nodes} (compiled : CompiledRawNandGraph graph) (word : DirectWireWord inputs nodes outputs) : (compiled.candidate word).toImplementation.gateCount = nodes",
      "CompiledRawNandGraph.candidate_semantics": "theorem CompiledRawNandGraph.candidate_semantics {inputs nodes outputs : Nat} {graph : RawNandGraph inputs nodes} (compiled : CompiledRawNandGraph graph) (word : DirectWireWord inputs nodes outputs) (input : Valuation inputs) (values : Valuation nodes) (equations : graph.Solution input values) (output : Fin outputs) : (compiled.candidate word).semantics input output = (word.source output).eval input values"
    },
    "publicHeads": [
      "RawNandGraph",
      "RawNandGraph.Depends",
      "RawNandGraph.Solution",
      "RawNandCompilationState",
      "RawNandCompilationState.initial",
      "RawNandCompilationState.readSource",
      "RawNandCompilationState.readGate",
      "RawNandCompilationState.readSource_sound",
      "RawNandCompilationState.readGate_sound",
      "RawNandCompilationState.readGate_predecessor",
      "RawNandReadyStep",
      "RawNandReadyStep.apply",
      "RawNandReadyStep.apply_remaining_lt",
      "RawNandCompilationStop",
      "runRawNandCompilation",
      "RawNandCompilationState.readSource_none",
      "RawNandCompilationStop.unresolved_predecessor",
      "RawNandCompilationStop.complete_of_wellFounded",
      "CompiledRawNandGraph",
      "RawNandCompilationState.finish",
      "CompiledRawNandGraph.wellFounded",
      "compileRawNandGraph",
      "compileRawNandGraph_success_iff",
      "compileRawNandGraph_failure_iff",
      "CompiledRawNandGraph.translateSource",
      "CompiledRawNandGraph.translateSource_sound",
      "CompiledRawNandGraph.candidate",
      "CompiledRawNandGraph.candidate_gateCount",
      "CompiledRawNandGraph.candidate_semantics"
    ]
  },
  {
    "kind": "splice",
    "path": "lean/PNP/NANDArbitrarySupportSplice.lean",
    "prefix": "PNP.DirectWire.ArbitrarySupportSplice.",
    "imports": [
      "PNP.NANDTopologicalCompiler",
      "PNP.ResidualTerminalSaturatedSupportContext"
    ],
    "signatures": {
      "result_gateCount": "theorem result_gateCount (compiled : CompiledRawNandGraph (graph candidate records replacement)) : (result candidate records replacement compiled).toImplementation.gateCount = (exterior records).length + replacementGates",
      "compile_success_iff": "theorem compile_success_iff : (∃ compiled, compile candidate records replacement = some compiled) ↔ WellFounded (graph candidate records replacement).Depends",
      "compile_failure_iff": "theorem compile_failure_iff : compile candidate records replacement = none ↔ ¬WellFounded (graph candidate records replacement).Depends",
      "replacementSource_eval": "theorem replacementSource_eval (source : Source (terminalBoundaryPorts candidate.program records).length replacementGates) (input : Valuation inputs) : (replacementSource candidate records source).eval input (values candidate records replacement input) = source.eval (terminalInducedBoundaryValuation candidate records input) (replacement.program.eval (terminalInducedBoundaryValuation candidate records input))",
      "originalSource_eval": "theorem originalSource_eval (equivalent : replacement.semantics = (extractTerminalSupport candidate records).extractedCandidate.semantics) (source : Source inputs gates) (visible : Visible candidate records source) (input : Valuation inputs) : (originalSource candidate records replacement source visible).eval input (values candidate records replacement input) = source.eval input (candidate.program.eval input)",
      "values_solution": "theorem values_solution (equivalent : replacement.semantics = (extractTerminalSupport candidate records).extractedCandidate.semantics) (input : Valuation inputs) : (graph candidate records replacement).Solution input (values candidate records replacement input)",
      "result_semantics": "theorem result_semantics (equivalent : replacement.semantics = (extractTerminalSupport candidate records).extractedCandidate.semantics) (compiled : CompiledRawNandGraph (graph candidate records replacement)) (input : Valuation inputs) (output : Fin outputs) : (result candidate records replacement compiled).semantics input output = candidate.semantics input output",
      "exterior_accounting": "theorem exterior_accounting : (extractTerminalSupport candidate records).gateCount + (exterior records).length = gates",
      "result_exact_accounting": "theorem result_exact_accounting (compiled : CompiledRawNandGraph (graph candidate records replacement)) : (result candidate records replacement compiled).toImplementation.gateCount + (extractTerminalSupport candidate records).gateCount = gates + replacementGates",
      "result_strict_gain": "theorem result_strict_gain (smaller : replacementGates < (extractTerminalSupport candidate records).gateCount) (compiled : CompiledRawNandGraph (graph candidate records replacement)) : (result candidate records replacement compiled).toImplementation.gateCount < gates",
      "graph_rank_decreases": "theorem graph_rank_decreases (primary : PrimaryBoundary candidate records) (producer consumer : Fin ((exterior records).length + replacementGates)) (edge : (graph candidate records replacement).Depends producer consumer) : rank records producer < rank records consumer",
      "graph_wellFounded_of_primaryBoundary": "theorem graph_wellFounded_of_primaryBoundary (primary : PrimaryBoundary candidate records) : WellFounded (graph candidate records replacement).Depends",
      "production_compiles": "theorem production_compiles (model : TerminalCandidateSaturationModel (profileWidth",
      "production_agreement": "theorem production_agreement (model : TerminalCandidateSaturationModel (profileWidth"
    },
    "publicHeads": [
      "exterior",
      "mem_exterior_iff",
      "boundarySource",
      "replacementSource",
      "Visible",
      "originalSource",
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
      "graph_wellFounded_of_singleGateBoundary"
    ]
  }
];
const NAMES = [
  "PNP.DirectWire.RawNandCompilationState.readSource_sound",
  "PNP.DirectWire.RawNandCompilationState.readGate_sound",
  "PNP.DirectWire.RawNandReadyStep.apply_remaining_lt",
  "PNP.DirectWire.RawNandCompilationStop.unresolved_predecessor",
  "PNP.DirectWire.RawNandCompilationStop.complete_of_wellFounded",
  "PNP.DirectWire.CompiledRawNandGraph.wellFounded",
  "PNP.DirectWire.compileRawNandGraph_success_iff",
  "PNP.DirectWire.compileRawNandGraph_failure_iff",
  "PNP.DirectWire.CompiledRawNandGraph.candidate_gateCount",
  "PNP.DirectWire.CompiledRawNandGraph.candidate_semantics",
  "PNP.DirectWire.ArbitrarySupportSplice.result_gateCount",
  "PNP.DirectWire.ArbitrarySupportSplice.compile_success_iff",
  "PNP.DirectWire.ArbitrarySupportSplice.compile_failure_iff",
  "PNP.DirectWire.ArbitrarySupportSplice.replacementSource_eval",
  "PNP.DirectWire.ArbitrarySupportSplice.originalSource_eval",
  "PNP.DirectWire.ArbitrarySupportSplice.values_solution",
  "PNP.DirectWire.ArbitrarySupportSplice.result_semantics",
  "PNP.DirectWire.ArbitrarySupportSplice.exterior_accounting",
  "PNP.DirectWire.ArbitrarySupportSplice.result_exact_accounting",
  "PNP.DirectWire.ArbitrarySupportSplice.result_strict_gain",
  "PNP.DirectWire.ArbitrarySupportSplice.graph_rank_decreases",
  "PNP.DirectWire.ArbitrarySupportSplice.graph_wellFounded_of_primaryBoundary",
  "PNP.DirectWire.ArbitrarySupportSplice.production_compiles",
  "PNP.DirectWire.ArbitrarySupportSplice.production_agreement"
];
const AUDIT = 'lean-audit/PNPArbitrarySupportSpliceAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPArbitrarySupportSplice.lean';
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = value => stripLeanCommentsAndStrings0(value).replace(/\s+/gu,' ').trim();
function block0(source,name) {
  const stripped=stripLeanCommentsAndStrings0(source);
  const boundaries=[...stripped.matchAll(/^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*(?:(?:def|theorem|inductive|structure|abbrev)[ \t]+([^\s({:]+)|variable\b|namespace\b|end\b)/gmu)];
  const index=boundaries.findIndex(item=>item[1]===name);
  return index<0?'':source.slice(boundaries[index].index,boundaries[index+1]?.index??source.length);
}
function validateSource0(source,spec) {
  const failures=[], require0=(condition,category)=>{if(!condition)failures.push(category);};
  const clean=compact0(source), block=name=>compact0(block0(source,name));
  require0(!hasLeanAssumptionDeclaration0(source),'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source),'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|callerCertificate|suppliedOrder|suppliedFrame|suppliedMap)\b/u.test(clean),'shortcut-or-certificate');
  require0(!/\b(?:allCandidates|allBoolTuples|allSubsets|equivalentBool|referenceMinimumWitness|scanEquivalentSizes|referenceMinimum|terminalFullProfileMinimum)\b/u.test(clean),'no-semantic-enumeration');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]))===
    JSON.stringify(spec.imports),'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name))===
    JSON.stringify(spec.publicHeads),'public-interface');
  for(const [name,signature] of Object.entries(spec.signatures))
    require0(block(name).startsWith(signature+' := '),'signature:'+name);
  const includes=(name,tokens,category)=>{
    const value=block(name);
    require0(tokens.every(token=>value.includes(token)),category);
  };
  if(spec.kind==='compiler'){
    require0(block('RawNandGraph.Depends').endsWith(
      '(graph.gate consumer).left = .gate producer ∨ (graph.gate consumer).right = .gate producer'),
      'actual-source-dependencies');
    includes('RawNandCompilationState',[
      'position : Fin nodes → Option (Fin count)','remaining : List (Fin nodes)',
      'remainingNodup : remaining.Nodup','count + remaining.length = nodes',
      'positionInjective : ∀ left right leftIndex rightIndex,',
      'ordered : ∀ node index, position node = some index →',
      'sound : ∀ input values, graph.Solution input values →',
    ],'complete-partial-state-invariants');
    includes('RawNandCompilationState.initial',[
      'remaining := List.finRange nodes','count := 0','position := fun _ => none',
    ],'actual-initial-node-set');
    require0(block('RawNandCompilationState.readSource').endsWith(
      '| .gate node => (state.position node).map Source.gate'),'no-unresolved-source-default');
    includes('RawNandReadyStep.apply',[
      'program := state.program.snoc step.gate','remaining := state.remaining.erase step.node',
    ],'emit-and-remove-exact-node');
    includes('runRawNandCompilation',[
      'findRawNandReadyIn state state.remaining','| some step => runRawNandCompilation step.apply',
      'termination_by state.remaining.length',
    ],'actual-node-bounded-recursion');
    includes('compileRawNandGraph',[
      'runRawNandCompilation (RawNandCompilationState.initial graph)',
      'if complete : stop.state.remaining = [] then some (stop.state.finish complete) else none',
    ],'computed-complete-or-reject');
    includes('CompiledRawNandGraph',[
      'count_eq : count = nodes','position_injective : ∀ left right,',
      'ordered : ∀ producer consumer, graph.Depends producer consumer →',
    ],'complete-injective-ordered-result');
    require0(block('CompiledRawNandGraph.candidate').endsWith(
      '⟨fun output => compiled.translateSource (word.source output)⟩'),'complete-output-reconnection');
  }else{
    for(const token of [
      'variable {inputs gates outputs profileWidth replacementGates : Nat}',
      'variable (candidate : Candidate inputs gates outputs)',
      'variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))',
      'variable (replacement : Candidate (terminalBoundaryPorts candidate.program records).length replacementGates (terminalInterfacePorts candidate records).length)',
    ])require0(clean.includes(token),'general-exact-frontier-parameters');
    require0(block('exterior').endsWith(
      'terminalSelectedGateIndices (fun gate => !(terminalGateSelected records gate))'),
      'actual-exterior-partition');
    includes('boundarySource',[
      'match found : (terminalBoundaryPorts candidate.program records).get port with',
      '| .input index => .input index','boundaryGate_unselected candidate records gate',
      'Fin.castAdd replacementGates (memberIndex',
    ],'actual-boundary-wiring');
    require0(!block('boundarySource').includes('.constant'),'no-boundary-default');
    includes('replacementSource',[
      '| .input port => boundarySource candidate records port',
      '| .constant value => .constant value',
      '| .gate index => .gate (Fin.natAdd (exterior records).length index)',
    ],'actual-replacement-wiring');
    includes('originalSource',[
      'if selected : terminalGateSelected records gate = true then',
      'replacement.directWireWord.source (memberIndex (visible gate rfl selected))',
      'else .gate (Fin.castAdd replacementGates (memberIndex',
    ],'actual-selected-interface-rebinding');
    require0(block('graph').endsWith(
      '⟨splitFin (exteriorGate candidate records replacement) (replacementGate candidate records replacement)⟩'),
      'actual-literal-graph');
    require0(block('word').endsWith(
      '(candidate.directWireWord.source output) (output_visible candidate records output)⟩'),
      'all-original-ordered-outputs');
    require0(block('compile').endsWith('compileRawNandGraph (graph candidate records replacement)'),
      'computed-splice-compiler');
    includes('production_compiles',[
      'apply (compile_success_iff candidate _ replacement).2',
      'exact terminalCandidateSaturate_boundary_isInput candidate model seed wire member',
    ],'derived-production-order');
  }
  return [...new Set(failures)];
}

test('M249 computes arbitrary raw graphs and actual support splices with general interfaces',async()=>{
  for(const spec of SOURCES)assert.deepEqual(validateSource0(await text0(spec.path),spec),[],spec.path);
});

test('M249 root, exact theorem-name producers and axiom audit agree',async()=>{
  const [audit,inventorySource,root]=await Promise.all([
    text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean')]);
  for(const name of NAMES){
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item=>item===name).length,1,name);
    assert.equal(inventorySource.split(String.fromCharCode(96)+name+',').length-1,1,name);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),NAMES);
  assert.match(root,/^import PNP\.NANDArbitrarySupportSplice\s*$/mu);
});

test('M249 rejects supplied, finite-only and weakened universal boundaries',async()=>{
  const compiler=await text0(SOURCES[0].path), splice=await text0(SOURCES[1].path);
  for(const [source,spec,before,after,category] of [
    [compiler,SOURCES[0],'(graph : RawNandGraph inputs nodes) :\n    (∃ compiled,',
      '(graph : RawNandGraph 1 nodes) :\n    (∃ compiled,','signature:compileRawNandGraph_success_iff'],
    [splice,SOURCES[1],'variable (candidate : Candidate inputs gates outputs)',
      'variable (candidate : Candidate 1 gates outputs)','general-exact-frontier-parameters'],
    [splice,SOURCES[1],'def compile : Option',
      'def compile (suppliedOrder : List Nat) : Option','shortcut-or-certificate'],
    [splice,SOURCES[1],'(model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)',
      '(callerCertificate : True) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)',
      'signature:production_compiles'],
    [splice,SOURCES[1],').toImplementation.gateCount < gates :=',
      ').toImplementation.gateCount ≤ gates :=','signature:result_strict_gain'],
    [splice,SOURCES[1],'gateCount =\n      (exterior records).length + replacementGates :=',
      'gateCount =\n      (exterior records).length + replacementGates + 1 :=','signature:result_gateCount'],
  ]){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after),spec).includes(category),category);
  }
});

test('M249 rejects dropped edges, default wires, fake nodes, partial success and wrong outputs',async()=>{
  const compiler=await text0(SOURCES[0].path), splice=await text0(SOURCES[1].path);
  for(const [source,spec,before,after,category] of [
    [compiler,SOURCES[0],"(graph.gate consumer).right = .gate producer","False",'actual-source-dependencies'],
    [compiler,SOURCES[0],'remaining := List.finRange nodes','remaining := []','actual-initial-node-set'],
    [compiler,SOURCES[0],'| .gate node => (state.position node).map Source.gate',
      '| .gate node => some (.constant false)','no-unresolved-source-default'],
    [compiler,SOURCES[0],'remaining := state.remaining.erase step.node',
      'remaining := state.remaining','emit-and-remove-exact-node'],
    [compiler,SOURCES[0],'if complete : stop.state.remaining = [] then',
      'if complete : True then','computed-complete-or-reject'],
    [compiler,SOURCES[0],'compiled.translateSource (word.source output)',
      '.constant false','complete-output-reconnection'],
    [splice,SOURCES[1],'terminalSelectedGateIndices (fun gate => !(terminalGateSelected records gate))',
      'terminalSelectedGateIndices (terminalGateSelected records)','actual-exterior-partition'],
    [splice,SOURCES[1],'| .input port => boundarySource candidate records port',
      '| .input port => .constant false','actual-replacement-wiring'],
    [splice,SOURCES[1],'(replacementGate candidate records replacement)⟩',
      '(exteriorGate candidate records replacement)⟩','actual-literal-graph'],
    [splice,SOURCES[1],'(candidate.directWireWord.source output) (output_visible candidate records output)',
      '(.constant false) (output_visible candidate records output)','all-original-ordered-outputs'],
    [splice,SOURCES[1],'compileRawNandGraph (graph candidate records replacement)',
      'none','computed-splice-compiler'],
  ]){
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after),spec).includes(category),category);
  }
  for(const [source,spec] of [[compiler,SOURCES[0]],[splice,SOURCES[1]]]){
    assert.ok(validateSource0(source+'\naxiom unauthorized : False\n',spec).includes('assumption'));
    assert.ok(validateSource0(source+'\nexample : True := by trivial\n',spec).includes('unaudited-form'));
  }
});

test('M249 regressions distinguish raw solutions from acyclic literal programs',async()=>{
  const raw=await text0(REGRESSION), regression=compact0(raw);
  for(const token of [
    'compileRawNandGraph_success_iff graph','compileRawNandGraph_failure_iff graph',
    'compiled.position_injective left right same','compiled.candidate_semantics',
    'result_semantics candidate records replacement equivalent compiled input output',
    'result_exact_accounting candidate records replacement compiled',
    'production_compiles candidate model seed replacement',
    'selfCycleGraph.Solution','cyclicGraph.Solution',
    'safe_equivalent','cyclic_equivalent','smaller_equivalent',
    'checkSplice chain interleaved safeReplacement 3 (some [1, 0, 2])',
    'checkSplice savingCandidate savingRecords smallerReplacement 3 (some [0, 2, 1])',
    'checkSplice chain productionRecords productionLarger 4',
    'checkSplice chain emptyRecords emptySupport.extractedCandidate 3',
    'checkSplice zeroCandidate zeroRecords zeroSupport.extractedCandidate 0',
    'checkSplice constantsCandidate constantsRecords constantsSupport.extractedCandidate 0',
    'checkSplice unusedCandidate unusedRecords unusedReplacement 0',
    'compile_failure_iff chain interleaved cyclicReplacement',
    'actual == expected','throw (IO.userError',
  ])assert.ok(regression.includes(token),token);
  assert.equal([...raw.matchAll(/^#eval\b/gmu)].length,2);
  assert.doesNotMatch(regression,/\b(?:sorry|admit|native_decide|Classical|referenceMinimum|scanEquivalentSizes|allCandidates)\b/u);
});

test('M249 durable workflow retains source checks, exact audit and bounded regressions',async()=>{
  const [packageText,surface,verifier,workflow]=await Promise.all([
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),text0('.github/workflows/lean-bridge.yml')]);
  const auditPath='audits/lean-arbitrary-support-splice0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m249'],'node --test '+auditPath);
  assert.ok(surface.includes("'audit:m249': 'node --test "+auditPath+"'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test '+auditPath));
  for(const path of [auditPath,'docs/lean_arbitrary_support_splice.md'])
    assert.equal(workflow.split("      - '"+path+"'").length-1,2);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M249_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-12-249';
const M249_MILESTONE = 'arbitrary-support-splice';
const M249_HASHES = Object.freeze({
  "PNP.DirectWire.RawNandCompilationState.readSource_sound": "249ab589fff275624335e93a95c3b2862e7571861f602a9a70b13a65f877b61c",
  "PNP.DirectWire.RawNandCompilationState.readGate_sound": "2122df5770802861ba07cdbd547afc012daaae5702e26b0ed87181952af491cb",
  "PNP.DirectWire.RawNandReadyStep.apply_remaining_lt": "a167205196de2bd40e72deecb2cf8d099f4c3e64fc9b638a866d324547db644e",
  "PNP.DirectWire.RawNandCompilationStop.unresolved_predecessor": "05ebc6f9f02d6a05eeca50202e1cb0b913b033ecfe8e548b43569b8aeb033959",
  "PNP.DirectWire.RawNandCompilationStop.complete_of_wellFounded": "1bb645c9e89c90ce8195e4185efc1bb97909240430e67450da59cf4087748d0c",
  "PNP.DirectWire.CompiledRawNandGraph.wellFounded": "4e407ec0b1b11c26e305f4b6933706dbafecb931aee26181165cb570de6e2353",
  "PNP.DirectWire.compileRawNandGraph_success_iff": "93307f1d06f33a85af1e05f01ec9cb33db389877e5c9f7bd1838b989ae1100b7",
  "PNP.DirectWire.compileRawNandGraph_failure_iff": "5c942c77b078d5717609c444cea6c87b8bdbd45d707659bccad6c810dabc1d66",
  "PNP.DirectWire.CompiledRawNandGraph.candidate_gateCount": "e8190898d052060480bd4856f59cc987c79c8f0127fdfbaced645bce19e40156",
  "PNP.DirectWire.CompiledRawNandGraph.candidate_semantics": "cc989aa0ce66ace1cf344b38d9f00f6cd0c7057f5bddae614e2d4c0c9913aaa1",
  "PNP.DirectWire.ArbitrarySupportSplice.result_gateCount": "e54d5da539b9ee0e0d8334b9bca202caaea0d91c02a040ca33773eda06c0efe4",
  "PNP.DirectWire.ArbitrarySupportSplice.compile_success_iff": "50d8a57ea6ec2910278d2f8d31b8b580d18486f4bef6a051ee0bf546e534df8b",
  "PNP.DirectWire.ArbitrarySupportSplice.compile_failure_iff": "3ccc9106581f2cae3f36f17be8f58d78c0071aa0c39f3d4863f3144970ce558e",
  "PNP.DirectWire.ArbitrarySupportSplice.replacementSource_eval": "6e1004ed4845279079fee1f84c482fdeb9bad1c0b34174b94215098871f0f553",
  "PNP.DirectWire.ArbitrarySupportSplice.originalSource_eval": "a78632aaf6fd18c70508d245380e821a57d1961c728ffca10021a3327560042a",
  "PNP.DirectWire.ArbitrarySupportSplice.values_solution": "510b56c2ce6bb2e14b51d6b5921d6cac369c5b88e127bf54b6ddad1e156af91d",
  "PNP.DirectWire.ArbitrarySupportSplice.result_semantics": "6940158e70561f97abcff887d83b2ee27c06864ea746b60c80fa4a06b6324200",
  "PNP.DirectWire.ArbitrarySupportSplice.exterior_accounting": "cfc111a947f4eb06bd738d6258c46e598a3bfcfc7fccabe13aef8a8bb8a8c994",
  "PNP.DirectWire.ArbitrarySupportSplice.result_exact_accounting": "6da5b36305b6fd26bfb41c1554e744f5c6dd11308b5e20ea9df7829b657ea763",
  "PNP.DirectWire.ArbitrarySupportSplice.result_strict_gain": "acc58cbe89243294ea56091b30ffa196725aeb3ba18c3577923ba033711b06f3",
  "PNP.DirectWire.ArbitrarySupportSplice.graph_rank_decreases": "67c8f06262ace5918cb8e3f61c626b82fc4ef041148c7cac0b553fff6238e7ec",
  "PNP.DirectWire.ArbitrarySupportSplice.graph_wellFounded_of_primaryBoundary": "f3976f6579060f445aefe21487ac307efdcc929f9b469af1f56fc92cb2a9fb86",
  "PNP.DirectWire.ArbitrarySupportSplice.production_compiles": "900469aefe05cde3d9a9976d31672a502e532ee629545d7392785b2db9e3a00c",
  "PNP.DirectWire.ArbitrarySupportSplice.production_agreement": "4184ac9ce3304d128becafaeeaeb180ab9a96b5431e4a3fb3ad7280bf99b6846"
});
const M249_STATUS_FIELDS = Object.freeze({
  "leanArbitrarySupportSpliceFormalized": true,
  "leanArbitrarySupportSpliceAxiomAuditPassed": true,
  "leanArbitrarySupportSpliceAuditedDeclarationCount": 24,
  "leanArbitrarySupportSpliceCompilerSuccessTheorem": "PNP.DirectWire.compileRawNandGraph_success_iff",
  "leanArbitrarySupportSpliceCompilerFailureTheorem": "PNP.DirectWire.compileRawNandGraph_failure_iff",
  "leanArbitrarySupportSpliceRawOutputSemanticsTheorem": "PNP.DirectWire.CompiledRawNandGraph.candidate_semantics",
  "leanArbitrarySupportSpliceExactGateCountTheorem": "PNP.DirectWire.ArbitrarySupportSplice.result_gateCount",
  "leanArbitrarySupportSpliceGraphEquationsTheorem": "PNP.DirectWire.ArbitrarySupportSplice.values_solution",
  "leanArbitrarySupportSpliceGlobalSemanticsTheorem": "PNP.DirectWire.ArbitrarySupportSplice.result_semantics",
  "leanArbitrarySupportSplicePartitionTheorem": "PNP.DirectWire.ArbitrarySupportSplice.exterior_accounting",
  "leanArbitrarySupportSpliceExactAccountingTheorem": "PNP.DirectWire.ArbitrarySupportSplice.result_exact_accounting",
  "leanArbitrarySupportSpliceStrictGainTheorem": "PNP.DirectWire.ArbitrarySupportSplice.result_strict_gain",
  "leanArbitrarySupportSpliceProductionOrderTheorem": "PNP.DirectWire.ArbitrarySupportSplice.graph_rank_decreases",
  "leanArbitrarySupportSpliceProductionSuccessTheorem": "PNP.DirectWire.ArbitrarySupportSplice.production_compiles",
  "leanArbitrarySupportSpliceProductionAgreementTheorem": "PNP.DirectWire.ArbitrarySupportSplice.production_agreement",
  "leanArbitrarySupportSpliceUnrestrictedReplacementSuccessProved": false,
  "leanArbitrarySupportSpliceFullProfilePreservationProved": false,
  "leanArbitrarySupportSpliceCompletePackageEProved": false,
  "leanArbitrarySupportSplicePolynomialRuntimeProved": false,
  "leanArbitrarySupportSpliceScope": "all-finite-actual-supports-computed-literal-exterior-replacement-graph-derived-topological-order-complete-ordered-output-semantics-exact-accounting-cyclic-rejection-production-saturation-success-physical-only"
});
const M249_AXIOMS = Object.freeze({
  "PNP.DirectWire.RawNandCompilationState.readSource_sound": [
    "propext"
  ],
  "PNP.DirectWire.RawNandCompilationState.readGate_sound": [
    "propext"
  ],
  "PNP.DirectWire.RawNandReadyStep.apply_remaining_lt": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.RawNandCompilationStop.unresolved_predecessor": [
    "propext"
  ],
  "PNP.DirectWire.RawNandCompilationStop.complete_of_wellFounded": [
    "propext"
  ],
  "PNP.DirectWire.CompiledRawNandGraph.wellFounded": [],
  "PNP.DirectWire.compileRawNandGraph_success_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.compileRawNandGraph_failure_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.CompiledRawNandGraph.candidate_gateCount": [],
  "PNP.DirectWire.CompiledRawNandGraph.candidate_semantics": [],
  "PNP.DirectWire.ArbitrarySupportSplice.result_gateCount": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.ArbitrarySupportSplice.compile_success_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.ArbitrarySupportSplice.compile_failure_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.ArbitrarySupportSplice.replacementSource_eval": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.ArbitrarySupportSplice.originalSource_eval": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.ArbitrarySupportSplice.values_solution": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.ArbitrarySupportSplice.result_semantics": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.ArbitrarySupportSplice.exterior_accounting": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.ArbitrarySupportSplice.result_exact_accounting": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.ArbitrarySupportSplice.result_strict_gain": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.ArbitrarySupportSplice.graph_rank_decreases": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.ArbitrarySupportSplice.graph_wellFounded_of_primaryBoundary": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.ArbitrarySupportSplice.production_compiles": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.ArbitrarySupportSplice.production_agreement": [
    "Quot.sound",
    "propext"
  ]
});

const M249_MODULES = Object.freeze({
  "PNP.DirectWire.RawNandCompilationState.readSource_sound": "PNP.NANDTopologicalCompiler",
  "PNP.DirectWire.RawNandCompilationState.readGate_sound": "PNP.NANDTopologicalCompiler",
  "PNP.DirectWire.RawNandReadyStep.apply_remaining_lt": "PNP.NANDTopologicalCompiler",
  "PNP.DirectWire.RawNandCompilationStop.unresolved_predecessor": "PNP.NANDTopologicalCompiler",
  "PNP.DirectWire.RawNandCompilationStop.complete_of_wellFounded": "PNP.NANDTopologicalCompiler",
  "PNP.DirectWire.CompiledRawNandGraph.wellFounded": "PNP.NANDTopologicalCompiler",
  "PNP.DirectWire.compileRawNandGraph_success_iff": "PNP.NANDTopologicalCompiler",
  "PNP.DirectWire.compileRawNandGraph_failure_iff": "PNP.NANDTopologicalCompiler",
  "PNP.DirectWire.CompiledRawNandGraph.candidate_gateCount": "PNP.NANDTopologicalCompiler",
  "PNP.DirectWire.CompiledRawNandGraph.candidate_semantics": "PNP.NANDTopologicalCompiler",
  "PNP.DirectWire.ArbitrarySupportSplice.result_gateCount": "PNP.NANDArbitrarySupportSplice",
  "PNP.DirectWire.ArbitrarySupportSplice.compile_success_iff": "PNP.NANDArbitrarySupportSplice",
  "PNP.DirectWire.ArbitrarySupportSplice.compile_failure_iff": "PNP.NANDArbitrarySupportSplice",
  "PNP.DirectWire.ArbitrarySupportSplice.replacementSource_eval": "PNP.NANDArbitrarySupportSplice",
  "PNP.DirectWire.ArbitrarySupportSplice.originalSource_eval": "PNP.NANDArbitrarySupportSplice",
  "PNP.DirectWire.ArbitrarySupportSplice.values_solution": "PNP.NANDArbitrarySupportSplice",
  "PNP.DirectWire.ArbitrarySupportSplice.result_semantics": "PNP.NANDArbitrarySupportSplice",
  "PNP.DirectWire.ArbitrarySupportSplice.exterior_accounting": "PNP.NANDArbitrarySupportSplice",
  "PNP.DirectWire.ArbitrarySupportSplice.result_exact_accounting": "PNP.NANDArbitrarySupportSplice",
  "PNP.DirectWire.ArbitrarySupportSplice.result_strict_gain": "PNP.NANDArbitrarySupportSplice",
  "PNP.DirectWire.ArbitrarySupportSplice.graph_rank_decreases": "PNP.NANDArbitrarySupportSplice",
  "PNP.DirectWire.ArbitrarySupportSplice.graph_wellFounded_of_primaryBoundary": "PNP.NANDArbitrarySupportSplice",
  "PNP.DirectWire.ArbitrarySupportSplice.production_compiles": "PNP.NANDArbitrarySupportSplice",
  "PNP.DirectWire.ArbitrarySupportSplice.production_agreement": "PNP.NANDArbitrarySupportSplice"
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

test('M249 compiled arbitrary-support splice interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M249_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M249_COORDINATE)
    assert.equal(map.coordinate, M249_COORDINATE.replace(
      'FORMAL-RECONSTRUCTION-STATUS', 'FORMAL-PUBLICATION-MAP'));
  assert.deepEqual(row.requiredTheorems, Object.keys(M249_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, M249_MODULES[name], name);
      assert.deepEqual(declaration.axioms, M249_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M249_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M249_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M249_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "Arbitrary raw port compatibility and equal open Boolean functions do not by themselves guarantee acyclic literal wiring",
  "Full-profile preservation",
  "No semantic minimum is computed",
  "finite node-count termination argument is not a total encoded-size polynomial runtime theorem",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M249 publication rejects weakened, supplied, assumption-backed and widened literal-splice substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M249_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M249_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = NAMES[16];
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M249_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M249_MILESTONE
    ? {...row, nonClaim:'All equal replacements are acyclic and prove complete Package E and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M249 adds physical substitution coverage without unrestricted acyclicity, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M249_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "physical arbitrary-support substitution and topological well-formedness edge",
  "literal graph and its order are computed from actual data",
  "Cyclic raw splices are rejected",
  "No fixed load-bearing checkpoint changes state"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M249_COORDINATE) return;
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

test('M249 current summaries distinguish physical substitution from full-profile and global completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_arbitrary_support_splice.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "No frame, order, wiring map or acyclicity certificate is supplied to the constructor",
  "The equivalence premise constrains the replacement's open function",
  "Equal open Boolean functions do not by themselves guarantee acyclic literal wiring",
  "Runtime execution is test evidence, not theorem authority",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-12-computed-arbitrary-support-splice.md'));
  assert.match(plan, /Publication decision: defer PNPLabs(?:[.,]|$)/u);
  if (progress.asOfCoordinate !== M249_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_arbitrary_support_splice.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
