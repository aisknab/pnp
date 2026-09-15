import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Source contracts catch altered inputs before the compiled type/axiom audit.
// The literal compiler result, complete observations and source-derived labels
// are essential: Boolean agreement alone does not prove dependency bounds.
const SPECS = [
  {
    id:'compiler', path:'lean/PNP/NANDTopologicalCausalBounds.lean',
    imports:['PNP.NANDTopologicalCompiler','PNP.NANDCausalBounds'],
    heads:['GraphBounds','StateBounds','initial_bounds','readSource_bound','readGate_bound',
      'apply_bounds','run_bounds','finish_bounds','compile_bounds','translateSource_bound','candidate_bound'],
    signatures:[
      'theorem compile_bounds {inputs nodes : Nat} (graph : RawNandGraph inputs nodes) (compiled : CompiledRawNandGraph graph) (accepted : compileRawNandGraph graph = some compiled) (labels : Fin inputs → Nat) (caps : Fin nodes → Nat) (bounded : GraphBounds graph labels caps) (node : Fin nodes) : CausalBound.levels compiled.program labels (compiled.position node) ≤ caps node',
      'theorem candidate_bound {inputs nodes outputs : Nat} (graph : RawNandGraph inputs nodes) (compiled : CompiledRawNandGraph graph) (accepted : compileRawNandGraph graph = some compiled) (labels : Fin inputs → Nat) (caps : Fin nodes → Nat) (bounded : GraphBounds graph labels caps) (word : DirectWireWord inputs nodes outputs) (output : Fin outputs) : CausalBound.outputLevel (compiled.candidate word) labels output ≤ CausalBound.source (word.source output) labels caps',
    ],
    fragments:[
      ['namespace PNP.DirectWire.RawNandCausalBound','namespace'],
      ['∀ node, max (CausalBound.source (graph.gate node).left labels caps) (CausalBound.source (graph.gate node).right labels caps) ≤ caps node','actual-graph-caps'],
      ['∀ node index, state.position node = some index → CausalBound.levels state.program labels index ≤ caps node','actual-state-positions'],
      ['checked node _ (state.finish_position complete node)','actual-finish-position'],
      ['let stop := runRawNandCompilation (RawNandCompilationState.initial graph)','actual-compiler-run'],
      ['(if complete : stop.state.remaining = [] then some (stop.state.finish complete) else none) = some compiled at accepted','actual-accepted-result'],
      ['termination_by state.remaining.length','finite-compiler-measure'],
    ],
  },
  {
    id:'unary', path:'lean/PNP/NANDWireUnaryCausalBounds.lean',
    imports:['PNP.NANDWireUnaryArbitrarySupport','PNP.NANDWireCausalBounds'],
    heads:['input_label_le_of_bit_ne','zero_implementation_bound','one_implementation_bound',
      'implementation_output_bound','realize_causalBounds','constantWord_output_bound',
      'unaryCarrier_output_level','unaryWord_output_bound','localWord_output_bound',
      'arbitrary_replacement_output_bound','compiled_spec','replacement_dependency_bound',
      'expanded_exposed_bound','expanded_causalBounds','attempt_causalBounds'],
    signatures:[
      'theorem implementation_output_bound (carrier : WireCarrier 1 outputs fields) (labels : Fin 1 → Nat) (observation : Fin (outputs + fields)) : CausalBound.outputLevel (WireUnaryRealization.implementation carrier).candidate labels observation ≤ CausalBound.outputLevel carrier.exposed.candidate labels observation',
      'theorem localWord_output_bound (original : Implementation inputs width) (small : inputs ≤ 1) (labels : Fin inputs → Nat) (output : Fin width) : CausalBound.outputLevel (WireUnaryFrontier.localWord original small).candidate labels output ≤ CausalBound.outputLevel original.candidate labels output',
      'theorem compiled_spec (small : (WireUnaryArbitrarySupport.pulled carrier records).boundary.length ≤ 1) : ArbitrarySupportSplice.compile carrier.exposed.candidate records (WireUnaryArbitrarySupport.replacement carrier records small).candidate = some (WireUnaryArbitrarySupport.compiled carrier records small)',
      'theorem replacement_dependency_bound (small : (WireUnaryArbitrarySupport.pulled carrier records).boundary.length ≤ 1) (labels : Fin inputs → Nat) : ArbitrarySupportSplice.DependencyInterfaceBound carrier.exposed.candidate records (WireUnaryArbitrarySupport.replacement carrier records small).candidate labels',
      'theorem expanded_causalBounds (small : (WireUnaryArbitrarySupport.pulled carrier records).boundary.length ≤ 1) (labels : Fin inputs → Nat) : (WireUnaryArbitrarySupport.expanded carrier records small).CausalBounds labels (CausalBound.outputLevel carrier.implementation.candidate labels) (carrier.fieldLevel labels)',
    ],
    fragments:[
      ['namespace PNP.DirectWire.WireUnaryCausalBound','namespace'],
      ['variable {outputs fields : Nat}','general-observations'],
      ['variable {inputs width : Nat}','general-inputs'],
      ['variable (carrier : WireCarrier inputs outputs fields) (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0))','actual-computational-records'],
      ['CausalBound.source_sound carrier.exposed.candidate.program','actual-observation-dependency'],
      ['cases needed : WireUnaryRealization.needsNegation carrier with','computed-unary-constructor'],
      ['(ArbitrarySupportSplice.dependencyBoundaryLabels carrier.exposed.candidate records labels) port','actual-boundary-labels'],
      ['extractTerminalSupport_causal_levels carrier.exposed.candidate records labels port','derived-extraction-bound'],
      ['(replacement_dependency_bound carrier records small labels) (WireUnaryArbitrarySupport.compiled carrier records small) (compiled_spec carrier records small) observation','literal-splice-and-compiler'],
      ['expanded_exposed_bound carrier records small labels (Fin.castAdd fields output)','all-ordinary-outputs'],
      ['expanded_exposed_bound carrier records small labels (Fin.natAdd outputs field)','all-full-fields'],
    ],
  },
  {
    id:'splice', path:'lean/PNP/NANDArbitrarySupportSplice.lean',
    signatures:[
      'theorem graph_dependency_bounds (interfaceBound : DependencyInterfaceBound candidate records replacement labels) : RawNandCausalBound.GraphBounds (graph candidate records replacement) labels (dependencyCaps candidate records replacement labels)',
      'theorem result_output_dependency_bound (interfaceBound : DependencyInterfaceBound candidate records replacement labels) (compiled : CompiledRawNandGraph (graph candidate records replacement)) (accepted : compile candidate records replacement = some compiled) (output : Fin outputs) : CausalBound.outputLevel (result candidate records replacement compiled) labels output ≤ CausalBound.outputLevel candidate labels output',
    ],
    fragments:[
      ['variable (labels : Fin inputs → Nat)','arbitrary-primary-labels'],
      ['terminalBoundaryCausalLabels candidate records labels (CausalBound.levels candidate.program labels)','literal-boundary-labels'],
      ['splitFin (fun index => CausalBound.levels candidate.program labels ((exterior records).get index)) (CausalBound.levels replacement.program (dependencyBoundaryLabels candidate records labels))','exterior-and-replacement-caps'],
      ['∀ port, CausalBound.outputLevel replacement (dependencyBoundaryLabels candidate records labels) port ≤ CausalBound.levels candidate.program labels ((terminalInterfacePorts candidate records).get port)','complete-interface-bound'],
      ['RawNandCausalBound.candidate_bound (graph candidate records replacement) compiled accepted','actual-accepted-compiler'],
    ],
  },
];

const compact = source => stripLeanCommentsAndStrings0(source).replace(/\s+/gu,' ').trim();
function inspect(source,spec) {
  const failures = [], text = compact(source);
  const require = (condition,label) => { if (!condition) failures.push(label); };
  require(!hasLeanAssumptionDeclaration0(source),'no-assumptions');
  require(!hasUnauditedLeanDeclarationForm0(source),'audited-declarations');
  require(!/\b(?:sorry|admit|unsafe|native_decide|noncomputable|Classical|implemented_by|csimp|callerCertificate|suppliedTable|suppliedResult|suppliedOrder)\b/u.test(text),'no-shortcuts-or-certificates');
  if (spec.imports) require(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1])) === JSON.stringify(spec.imports),'closed-imports');
  if (spec.heads) require(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name)) === JSON.stringify(spec.heads),'closed-declarations');
  for (const signature of spec.signatures) require(text.includes(signature + ' :='),'signature:' + signature.split(' ')[1]);
  for (const [fragment,label] of spec.fragments) require(text.includes(fragment),label);
  return failures;
}
let inputs;
function sources() {
  inputs ??= Promise.all(SPECS.map(async spec => ({spec,source:await readFile(new URL('../' + spec.path,import.meta.url),'utf8')})));
  return inputs;
}

test('M265 dependency contracts bind the actual compiler, unary source and complete carrier',async()=>{
  for (const {spec,source} of await sources()) assert.deepEqual(inspect(source,spec),[],spec.path);
});

test('M265 dependency contracts reject Boolean-only compilers, supplied bounds and incomplete observations',async()=>{
  const byId = new Map((await sources()).map(row=>[row.spec.id,row]));
  for (const [id,before,after,category] of [
    ['compiler','(accepted : compileRawNandGraph graph = some compiled)','(accepted : True)','signature:compile_bounds'],
    ['compiler','{inputs nodes : Nat}','{nodes : Nat}','signature:compile_bounds'],
    ['compiler','state.position node = some index','True','actual-state-positions'],
    ['compiler','state.finish_position complete node','suppliedPosition','actual-finish-position'],
    ['unary','theorem expanded_causalBounds','theorem expanded_causalBounds (supplied : True)','signature:expanded_causalBounds'],
    ['unary','(observation : Fin (outputs + fields))','(observation : Fin outputs)','signature:implementation_output_bound'],
    ['unary','(small : inputs ≤ 1)','(small : True)','signature:localWord_output_bound'],
    ['unary','extractTerminalSupport_causal_levels carrier.exposed.candidate','unprovedExtractionBound carrier.exposed.candidate','derived-extraction-bound'],
    ['unary','(compiled_spec carrier records small) observation','suppliedCompiler observation','literal-splice-and-compiler'],
    ['unary','(Fin.natAdd outputs field)','(Fin.castAdd outputs field)','all-full-fields'],
    ['splice','(accepted : compile candidate records replacement = some compiled)','(accepted : True)','signature:result_output_dependency_bound'],
    ['splice','CausalBound.levels candidate.program labels ((exterior records).get index)','0','exterior-and-replacement-caps'],
  ]) {
    const {spec,source} = byId.get(id);
    assert.ok(source.includes(before),'mutation anchor: ' + category);
    assert.ok(inspect(source.replaceAll(before,after),spec).includes(category),category);
  }
  for (const {spec,source} of await sources()) {
    assert.ok(inspect(source + '\naxiom assumedDependencyBound : False\n',spec).includes('no-assumptions'));
    if (spec.heads) assert.ok(inspect(source + '\ndef ignoredBoundary : Bool := true\n',spec).includes('closed-declarations'));
  }
});
