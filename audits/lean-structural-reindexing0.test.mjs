import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Frozen from the reviewed general construction, not recomputed by these tests.
const SPECS = [
  {"part":"TopologicalWireStructure","path":"lean/PNP/NANDTopologicalWireStructure.lean","module":"PNP.NANDTopologicalWireStructure","sourceContractSha256":"34fdb37429bf3af3176375eaec7d6eded1f011d4a4b97c78641e26f8eea8f242","heads":[{"kind":"def","name":"StateFaithful"},{"kind":"theorem","name":"initial_faithful"},{"kind":"theorem","name":"apply_faithful"},{"kind":"theorem","name":"run_faithful"},{"kind":"theorem","name":"finish_sources"},{"kind":"theorem","name":"compile_sources"},{"kind":"theorem","name":"physicalOrigin_sources"}],"theorems":["PNP.DirectWire.RawNandWireStructure.initial_faithful","PNP.DirectWire.RawNandWireStructure.apply_faithful","PNP.DirectWire.RawNandWireStructure.run_faithful","PNP.DirectWire.RawNandWireStructure.finish_sources","PNP.DirectWire.RawNandWireStructure.compile_sources","PNP.DirectWire.RawNandWireStructure.physicalOrigin_sources"]},
  {"part":"GateRenaming","path":"lean/PNP/NANDGateRenaming.lean","module":"PNP.NANDGateRenaming","sourceContractSha256":"31f7bcc50d706e51c56782ca5d0d94d8d8e2980145d2f588f2bc9b592a258dab","heads":[{"kind":"structure","name":"GateRenaming"},{"kind":"def","name":"identity"},{"kind":"def","name":"compose"},{"kind":"def","name":"swap"},{"kind":"theorem","name":"forward_injective"},{"kind":"theorem","name":"backward_injective"},{"kind":"def","name":"decode"},{"kind":"def","name":"validCode"},{"kind":"theorem","name":"decode_isSome"},{"kind":"def","name":"sourceMap"},{"kind":"theorem","name":"sourceMap_compose"},{"kind":"theorem","name":"sourceMap_eq_gate_iff"},{"kind":"theorem","name":"sourceMap_eval"}],"theorems":["PNP.DirectWire.StructuralReindexing.GateRenaming.forward_injective","PNP.DirectWire.StructuralReindexing.GateRenaming.backward_injective","PNP.DirectWire.StructuralReindexing.GateRenaming.decode_isSome","PNP.DirectWire.StructuralReindexing.sourceMap_compose","PNP.DirectWire.StructuralReindexing.sourceMap_eq_gate_iff","PNP.DirectWire.StructuralReindexing.sourceMap_eval"]},
  {"part":"StructuralReindexing","path":"lean/PNP/NANDStructuralReindexing.lean","module":"PNP.NANDStructuralReindexing","sourceContractSha256":"81a0801a4028fc50a0a60860340186043c24b3576bff4205a00aa2f4fd5fe556","heads":[{"kind":"def","name":"graph"},{"kind":"theorem","name":"graph_edge_ordered"},{"kind":"theorem","name":"graph_wellFounded"},{"kind":"theorem","name":"compile_isSome"},{"kind":"def","name":"compiled"},{"kind":"theorem","name":"compiled_accepted"},{"kind":"def","name":"renamedWord"},{"kind":"def","name":"result"},{"kind":"def","name":"forwardGate"},{"kind":"def","name":"backwardGate"},{"kind":"theorem","name":"backward_forward"},{"kind":"theorem","name":"forward_backward"},{"kind":"theorem","name":"forwardGate_injective"},{"kind":"theorem","name":"backwardGate_injective"},{"kind":"theorem","name":"translated_source"},{"kind":"theorem","name":"result_sources"},{"kind":"theorem","name":"result_output_source"},{"kind":"theorem","name":"result_gateCount"},{"kind":"theorem","name":"graph_solution"},{"kind":"theorem","name":"result_semantics"},{"kind":"def","name":"attempt"},{"kind":"theorem","name":"attempt_isSome"},{"kind":"theorem","name":"attempt_semantics"},{"kind":"theorem","name":"attempt_gateCount"}],"theorems":["PNP.DirectWire.StructuralReindexing.graph_edge_ordered","PNP.DirectWire.StructuralReindexing.graph_wellFounded","PNP.DirectWire.StructuralReindexing.compile_isSome","PNP.DirectWire.StructuralReindexing.compiled_accepted","PNP.DirectWire.StructuralReindexing.backward_forward","PNP.DirectWire.StructuralReindexing.forward_backward","PNP.DirectWire.StructuralReindexing.forwardGate_injective","PNP.DirectWire.StructuralReindexing.backwardGate_injective","PNP.DirectWire.StructuralReindexing.translated_source","PNP.DirectWire.StructuralReindexing.result_sources","PNP.DirectWire.StructuralReindexing.result_output_source","PNP.DirectWire.StructuralReindexing.result_gateCount","PNP.DirectWire.StructuralReindexing.graph_solution","PNP.DirectWire.StructuralReindexing.result_semantics","PNP.DirectWire.StructuralReindexing.attempt_isSome","PNP.DirectWire.StructuralReindexing.attempt_semantics","PNP.DirectWire.StructuralReindexing.attempt_gateCount"]},
  {"part":"ReindexedSupport","path":"lean/PNP/NANDReindexedSupport.lean","module":"PNP.NANDReindexedSupport","sourceContractSha256":"5a3845ea217af6d70db59d7273e912c4701e300a5bd00155ddbeda417ae85f38","heads":[{"kind":"def","name":"forwardWire"},{"kind":"def","name":"backwardWire"},{"kind":"theorem","name":"backward_forward_wire"},{"kind":"theorem","name":"forward_backward_wire"},{"kind":"def","name":"forwardRecord"},{"kind":"def","name":"backwardRecord"},{"kind":"theorem","name":"backward_forward_record"},{"kind":"theorem","name":"forward_backward_record"},{"kind":"theorem","name":"forwardRecord_injective"},{"kind":"def","name":"forwardRecords"},{"kind":"def","name":"backwardRecords"},{"kind":"theorem","name":"backward_forward_records"},{"kind":"theorem","name":"forward_backward_records"},{"kind":"theorem","name":"forwardRecord_mem"},{"kind":"theorem","name":"selected_forward"},{"kind":"theorem","name":"external_forward"},{"kind":"theorem","name":"backward_forward_source"},{"kind":"theorem","name":"sourceMap_forward_injective"},{"kind":"theorem","name":"source_wire_map"},{"kind":"theorem","name":"source_wire_iff"},{"kind":"theorem","name":"uses_forward"},{"kind":"theorem","name":"boundary_forward"},{"kind":"theorem","name":"externalConsumer_forward"},{"kind":"theorem","name":"globalOutput_forward"},{"kind":"theorem","name":"interface_forward"},{"kind":"theorem","name":"boundary_ports_forward"},{"kind":"theorem","name":"interface_ports_forward"},{"kind":"theorem","name":"descendant_boundary"},{"kind":"theorem","name":"descendant_interface"}],"theorems":["PNP.DirectWire.StructuralReindexing.backward_forward_wire","PNP.DirectWire.StructuralReindexing.forward_backward_wire","PNP.DirectWire.StructuralReindexing.backward_forward_record","PNP.DirectWire.StructuralReindexing.forward_backward_record","PNP.DirectWire.StructuralReindexing.forwardRecord_injective","PNP.DirectWire.StructuralReindexing.backward_forward_records","PNP.DirectWire.StructuralReindexing.forward_backward_records","PNP.DirectWire.StructuralReindexing.forwardRecord_mem","PNP.DirectWire.StructuralReindexing.selected_forward","PNP.DirectWire.StructuralReindexing.external_forward","PNP.DirectWire.StructuralReindexing.backward_forward_source","PNP.DirectWire.StructuralReindexing.sourceMap_forward_injective","PNP.DirectWire.StructuralReindexing.source_wire_map","PNP.DirectWire.StructuralReindexing.source_wire_iff","PNP.DirectWire.StructuralReindexing.uses_forward","PNP.DirectWire.StructuralReindexing.boundary_forward","PNP.DirectWire.StructuralReindexing.externalConsumer_forward","PNP.DirectWire.StructuralReindexing.globalOutput_forward","PNP.DirectWire.StructuralReindexing.interface_forward","PNP.DirectWire.StructuralReindexing.boundary_ports_forward","PNP.DirectWire.StructuralReindexing.interface_ports_forward","PNP.DirectWire.StructuralReindexing.descendant_boundary","PNP.DirectWire.StructuralReindexing.descendant_interface"]},
  {"part":"ReindexedPorts","path":"lean/PNP/NANDReindexedPorts.lean","module":"PNP.NANDReindexedPorts","sourceContractSha256":"2c1f2d55b9ed2feeae4cc6a6dce81361af1a58824830bdc9303f878f8953d6a7","heads":[{"kind":"structure","name":"OrderedPortBijection"},{"kind":"def","name":"boundaryPorts"},{"kind":"def","name":"interfacePorts"},{"kind":"theorem","name":"selected_backward"},{"kind":"def","name":"selectedPorts"},{"kind":"def","name":"exteriorPorts"},{"kind":"def","name":"pushBoundaryValuation"},{"kind":"def","name":"pullBoundaryValuation"},{"kind":"theorem","name":"pull_push_boundary_valuation"},{"kind":"theorem","name":"push_pull_boundary_valuation"},{"kind":"theorem","name":"selected_gate_count"},{"kind":"theorem","name":"exterior_gate_count"}],"theorems":["PNP.DirectWire.StructuralReindexing.selected_backward","PNP.DirectWire.StructuralReindexing.pull_push_boundary_valuation","PNP.DirectWire.StructuralReindexing.push_pull_boundary_valuation","PNP.DirectWire.StructuralReindexing.selected_gate_count","PNP.DirectWire.StructuralReindexing.exterior_gate_count"]},
  {"part":"ReindexedOpenSemantics","path":"lean/PNP/NANDReindexedOpenSemantics.lean","module":"PNP.NANDReindexedOpenSemantics","sourceContractSha256":"5ebcc1d64772d524ac6acb4232e793f8e50478e68ac4326c67f247a330d10975","heads":[{"kind":"theorem","name":"external_wire_value_preserved"},{"kind":"theorem","name":"open_gate_preserved"},{"kind":"theorem","name":"open_support_preserved"},{"kind":"theorem","name":"open_support_pullback"},{"kind":"theorem","name":"extracted_support_preserved"}],"theorems":["PNP.DirectWire.StructuralReindexing.external_wire_value_preserved","PNP.DirectWire.StructuralReindexing.open_gate_preserved","PNP.DirectWire.StructuralReindexing.open_support_preserved","PNP.DirectWire.StructuralReindexing.open_support_pullback","PNP.DirectWire.StructuralReindexing.extracted_support_preserved"]},
  {"part":"ReindexedReplacement","path":"lean/PNP/NANDReindexedReplacement.lean","module":"PNP.NANDReindexedReplacement","sourceContractSha256":"9e8e3980d2d9e6abf8decadd7021499797b88db3afafd2aa972e25e03fae57f0","heads":[{"kind":"theorem","name":"renameInputs_gateSources"},{"kind":"def","name":"pullReplacement"},{"kind":"theorem","name":"pullReplacement_program"},{"kind":"theorem","name":"pullReplacement_gate_sources"},{"kind":"theorem","name":"pullReplacement_output_source"},{"kind":"theorem","name":"pullReplacement_gate_count"},{"kind":"theorem","name":"pullReplacement_semantics"},{"kind":"theorem","name":"pullReplacement_compatible"},{"kind":"theorem","name":"support_gate_count"},{"kind":"theorem","name":"support_surcharge_zero"},{"kind":"theorem","name":"replacement_surcharge_zero"},{"kind":"theorem","name":"matched_surcharge"},{"kind":"theorem","name":"replacement_saving_preserved"},{"kind":"theorem","name":"strict_gain_pullback"}],"theorems":["PNP.DirectWire.StructuralReindexing.renameInputs_gateSources","PNP.DirectWire.StructuralReindexing.pullReplacement_program","PNP.DirectWire.StructuralReindexing.pullReplacement_gate_sources","PNP.DirectWire.StructuralReindexing.pullReplacement_output_source","PNP.DirectWire.StructuralReindexing.pullReplacement_gate_count","PNP.DirectWire.StructuralReindexing.pullReplacement_semantics","PNP.DirectWire.StructuralReindexing.pullReplacement_compatible","PNP.DirectWire.StructuralReindexing.support_gate_count","PNP.DirectWire.StructuralReindexing.support_surcharge_zero","PNP.DirectWire.StructuralReindexing.replacement_surcharge_zero","PNP.DirectWire.StructuralReindexing.matched_surcharge","PNP.DirectWire.StructuralReindexing.replacement_saving_preserved","PNP.DirectWire.StructuralReindexing.strict_gain_pullback"]},
  {"part":"ReindexedSplice","path":"lean/PNP/NANDReindexedSplice.lean","module":"PNP.NANDReindexedSplice","sourceContractSha256":"a86d4947551a2b657e8afbc27e690892e884561dbc7981598e4b90023793b41e","heads":[{"kind":"def","name":"spliceForward"},{"kind":"def","name":"spliceBackward"},{"kind":"theorem","name":"spliceForward_exterior"},{"kind":"theorem","name":"spliceForward_replacement"},{"kind":"theorem","name":"spliceBackward_exterior"},{"kind":"theorem","name":"spliceBackward_replacement"},{"kind":"theorem","name":"splice_backward_forward"},{"kind":"theorem","name":"splice_forward_backward"},{"kind":"theorem","name":"splice_boundarySource_forward"},{"kind":"theorem","name":"splice_replacementSource_forward"},{"kind":"theorem","name":"splice_sources"},{"kind":"theorem","name":"splice_output_source"},{"kind":"theorem","name":"splice_dependencies"},{"kind":"theorem","name":"splice_wellFounded_iff"},{"kind":"theorem","name":"splice_compile_success_iff"},{"kind":"theorem","name":"splice_compile_failure_iff"}],"theorems":["PNP.DirectWire.StructuralReindexing.spliceForward_exterior","PNP.DirectWire.StructuralReindexing.spliceForward_replacement","PNP.DirectWire.StructuralReindexing.spliceBackward_exterior","PNP.DirectWire.StructuralReindexing.spliceBackward_replacement","PNP.DirectWire.StructuralReindexing.splice_backward_forward","PNP.DirectWire.StructuralReindexing.splice_forward_backward","PNP.DirectWire.StructuralReindexing.splice_boundarySource_forward","PNP.DirectWire.StructuralReindexing.splice_replacementSource_forward","PNP.DirectWire.StructuralReindexing.splice_sources","PNP.DirectWire.StructuralReindexing.splice_output_source","PNP.DirectWire.StructuralReindexing.splice_dependencies","PNP.DirectWire.StructuralReindexing.splice_wellFounded_iff","PNP.DirectWire.StructuralReindexing.splice_compile_success_iff","PNP.DirectWire.StructuralReindexing.splice_compile_failure_iff"]},
  {"part":"ReindexedCompiledSplice","path":"lean/PNP/NANDReindexedCompiledSplice.lean","module":"PNP.NANDReindexedCompiledSplice","sourceContractSha256":"5b2f26faef05b049ab45e8ac663604150049d45bd71135d3b9726bcb0bd1a1e1","heads":[{"kind":"def","name":"splicePhysicalForward"},{"kind":"def","name":"splicePhysicalBackward"},{"kind":"theorem","name":"splice_physical_backward_forward"},{"kind":"theorem","name":"splice_physical_forward_backward"},{"kind":"theorem","name":"splice_physical_position"},{"kind":"theorem","name":"splice_physical_exterior"},{"kind":"theorem","name":"splice_physical_replacement"},{"kind":"theorem","name":"splice_compiled_sources"},{"kind":"theorem","name":"splice_compiled_output_source"},{"kind":"theorem","name":"splice_compiled_gate_count"},{"kind":"theorem","name":"splice_compiled_semantics"},{"kind":"theorem","name":"pull_splice_isSome"},{"kind":"def","name":"pullCompiledSplice"},{"kind":"theorem","name":"pullCompiledSplice_accepted"},{"kind":"theorem","name":"literal_replacement_transport"}],"theorems":["PNP.DirectWire.StructuralReindexing.splice_physical_backward_forward","PNP.DirectWire.StructuralReindexing.splice_physical_forward_backward","PNP.DirectWire.StructuralReindexing.splice_physical_position","PNP.DirectWire.StructuralReindexing.splice_physical_exterior","PNP.DirectWire.StructuralReindexing.splice_physical_replacement","PNP.DirectWire.StructuralReindexing.splice_compiled_sources","PNP.DirectWire.StructuralReindexing.splice_compiled_output_source","PNP.DirectWire.StructuralReindexing.splice_compiled_gate_count","PNP.DirectWire.StructuralReindexing.splice_compiled_semantics","PNP.DirectWire.StructuralReindexing.pull_splice_isSome","PNP.DirectWire.StructuralReindexing.pullCompiledSplice_accepted","PNP.DirectWire.StructuralReindexing.literal_replacement_transport"]},
];
const REGRESSIONS = [
  {"path":"lean-regression/PNPTopologicalWireStructure.lean","imports":["PNP.NANDTopologicalWireStructure"],"printedNames":["PNP.DirectWire.RawNandWireStructure.compile_sources","PNP.DirectWire.RawNandWireStructure.physicalOrigin_sources"],"sourceContractSha256":"c40e66f9b921e4d9e9205a0862eb489d947b2b96c95d80a2c798f5ad921ef871"},
  {"path":"lean-regression/PNPStructuralReindexing.lean","imports":["PNP.NANDStructuralReindexing"],"printedNames":["PNP.DirectWire.StructuralReindexing.GateRenaming.decode_isSome","PNP.DirectWire.StructuralReindexing.result_sources","PNP.DirectWire.StructuralReindexing.backward_forward","PNP.DirectWire.StructuralReindexing.forward_backward","PNP.DirectWire.StructuralReindexing.attempt_semantics","PNP.DirectWire.StructuralReindexing.attempt_gateCount"],"sourceContractSha256":"2dcda11ab02860be427af616fa9637325e2e7edd032e3e1e192b30b0c3af2fe6"},
  {"path":"lean-regression/PNPReindexedSupport.lean","imports":["PNP.NANDReindexedSupport"],"printedNames":["PNP.DirectWire.StructuralReindexing.backward_forward_records","PNP.DirectWire.StructuralReindexing.forward_backward_records","PNP.DirectWire.StructuralReindexing.uses_forward","PNP.DirectWire.StructuralReindexing.descendant_boundary","PNP.DirectWire.StructuralReindexing.descendant_interface"],"sourceContractSha256":"cd19b789233b937c3a054f4407155f58d98dd9df53a8c7bbd38d17ddb8faff32"},
  {"path":"lean-regression/PNPReindexedPorts.lean","imports":["PNP.NANDReindexedPorts"],"printedNames":["PNP.DirectWire.StructuralReindexing.boundaryPorts","PNP.DirectWire.StructuralReindexing.interfacePorts","PNP.DirectWire.StructuralReindexing.selectedPorts","PNP.DirectWire.StructuralReindexing.exteriorPorts","PNP.DirectWire.StructuralReindexing.pull_push_boundary_valuation","PNP.DirectWire.StructuralReindexing.push_pull_boundary_valuation","PNP.DirectWire.StructuralReindexing.selected_gate_count","PNP.DirectWire.StructuralReindexing.exterior_gate_count"],"sourceContractSha256":"0dd46fc401a5fdd73316a498df231e9d42459838912947ce7b1349625426947b"},
  {"path":"lean-regression/PNPTerminalOpenEquations.lean","imports":["PNP.ResidualTerminalSupportExtraction"],"printedNames":["PNP.DirectWire.terminalOpenSourceValue","PNP.DirectWire.terminalOpenGateEvaluation_sourceEquation","PNP.DirectWire.terminalOpenWireValue_boundary_get","PNP.DirectWire.terminalOpenWireValue_external_absent"],"sourceContractSha256":"4e7f5d46bb8ef4a875761751b01075814831740c8627fe9c98f60fdd10e8fca0"},
  {"path":"lean-regression/PNPReindexedOpenSemantics.lean","imports":["PNP.NANDReindexedOpenSemantics"],"printedNames":["PNP.DirectWire.StructuralReindexing.external_wire_value_preserved","PNP.DirectWire.StructuralReindexing.open_gate_preserved","PNP.DirectWire.StructuralReindexing.open_support_preserved","PNP.DirectWire.StructuralReindexing.open_support_pullback","PNP.DirectWire.StructuralReindexing.extracted_support_preserved"],"sourceContractSha256":"7a2ca6df92e02b14bcbc0b886ad4f258c9ea397b291599c4976e049350a0f518"},
  {"path":"lean-regression/PNPReindexedReplacement.lean","imports":["PNP.NANDReindexedReplacement"],"printedNames":["PNP.DirectWire.StructuralReindexing.renameInputs_gateSources","PNP.DirectWire.StructuralReindexing.pullReplacement_gate_sources","PNP.DirectWire.StructuralReindexing.pullReplacement_output_source","PNP.DirectWire.StructuralReindexing.pullReplacement_semantics","PNP.DirectWire.StructuralReindexing.pullReplacement_compatible","PNP.DirectWire.StructuralReindexing.support_surcharge_zero","PNP.DirectWire.StructuralReindexing.replacement_surcharge_zero","PNP.DirectWire.StructuralReindexing.matched_surcharge","PNP.DirectWire.StructuralReindexing.replacement_saving_preserved","PNP.DirectWire.StructuralReindexing.strict_gain_pullback"],"sourceContractSha256":"1b9fcd39b13b4651d3f56cf23b7a859a05a3c00747b39db0873470626917bd7f"},
  {"path":"lean-regression/PNPSpliceWireEquations.lean","imports":["PNP.NANDArbitrarySupportSplice"],"printedNames":["PNP.DirectWire.ArbitrarySupportSplice.boundarySource_input","PNP.DirectWire.ArbitrarySupportSplice.boundarySource_gate","PNP.DirectWire.ArbitrarySupportSplice.originalSource_exterior","PNP.DirectWire.ArbitrarySupportSplice.originalSource_interface"],"sourceContractSha256":"cd83e508550b92ab5505798d16da8862a2baa871d342937856ec5a54974c6905"},
  {"path":"lean-regression/PNPReindexedSplice.lean","imports":["PNP.NANDReindexedSplice"],"printedNames":["PNP.DirectWire.StructuralReindexing.splice_backward_forward","PNP.DirectWire.StructuralReindexing.splice_forward_backward","PNP.DirectWire.StructuralReindexing.splice_boundarySource_forward","PNP.DirectWire.StructuralReindexing.splice_replacementSource_forward","PNP.DirectWire.StructuralReindexing.splice_sources","PNP.DirectWire.StructuralReindexing.splice_output_source","PNP.DirectWire.StructuralReindexing.splice_dependencies","PNP.DirectWire.StructuralReindexing.splice_wellFounded_iff","PNP.DirectWire.StructuralReindexing.splice_compile_success_iff","PNP.DirectWire.StructuralReindexing.splice_compile_failure_iff"],"sourceContractSha256":"0cce0638ce20cfba307e3778b155137a8c94ff7f7b0d5a05c67f12c7a95fb63c"},
  {"path":"lean-regression/PNPReindexedCompiledSplice.lean","imports":["PNP.NANDReindexedCompiledSplice"],"printedNames":["PNP.DirectWire.StructuralReindexing.splice_physical_backward_forward","PNP.DirectWire.StructuralReindexing.splice_physical_forward_backward","PNP.DirectWire.StructuralReindexing.splice_physical_position","PNP.DirectWire.StructuralReindexing.splice_physical_exterior","PNP.DirectWire.StructuralReindexing.splice_physical_replacement","PNP.DirectWire.StructuralReindexing.splice_compiled_sources","PNP.DirectWire.StructuralReindexing.splice_compiled_output_source","PNP.DirectWire.StructuralReindexing.splice_compiled_gate_count","PNP.DirectWire.StructuralReindexing.splice_compiled_semantics","PNP.DirectWire.StructuralReindexing.pull_splice_isSome","PNP.DirectWire.StructuralReindexing.pullCompiledSplice_accepted","PNP.DirectWire.StructuralReindexing.literal_replacement_transport"],"sourceContractSha256":"db3af95faa36d10c0d888a14eef80da56c3f977a58671c7093e339aad8641869"},
];
const ADDITIVE = [
  {"name":"PNP.DirectWire.terminalOpenSourceValue","kind":"def","path":"lean/PNP/ResidualTerminalSupportExtraction.lean","module":"PNP.ResidualTerminalSupportExtraction"},
  {"name":"PNP.DirectWire.terminalOpenGateEvaluation_sourceEquation","kind":"theorem","path":"lean/PNP/ResidualTerminalSupportExtraction.lean","module":"PNP.ResidualTerminalSupportExtraction"},
  {"name":"PNP.DirectWire.terminalOpenWireValue_boundary_get","kind":"theorem","path":"lean/PNP/ResidualTerminalSupportExtraction.lean","module":"PNP.ResidualTerminalSupportExtraction"},
  {"name":"PNP.DirectWire.terminalOpenWireValue_external_absent","kind":"theorem","path":"lean/PNP/ResidualTerminalSupportExtraction.lean","module":"PNP.ResidualTerminalSupportExtraction"},
  {"name":"PNP.DirectWire.ArbitrarySupportSplice.boundarySource_input","kind":"theorem","path":"lean/PNP/NANDArbitrarySupportSplice.lean","module":"PNP.NANDArbitrarySupportSplice"},
  {"name":"PNP.DirectWire.ArbitrarySupportSplice.boundarySource_gate","kind":"theorem","path":"lean/PNP/NANDArbitrarySupportSplice.lean","module":"PNP.NANDArbitrarySupportSplice"},
  {"name":"PNP.DirectWire.ArbitrarySupportSplice.originalSource_exterior","kind":"theorem","path":"lean/PNP/NANDArbitrarySupportSplice.lean","module":"PNP.NANDArbitrarySupportSplice"},
  {"name":"PNP.DirectWire.ArbitrarySupportSplice.originalSource_interface","kind":"theorem","path":"lean/PNP/NANDArbitrarySupportSplice.lean","module":"PNP.NANDArbitrarySupportSplice"},
];
const AXIOM_NAMES = [
  ...SPECS.flatMap(spec => spec.theorems),
  ...ADDITIVE.filter(row => row.kind === 'theorem').map(row => row.name),
];
const text0 = file => readFile(new URL('../' + file, import.meta.url), 'utf8');
const compact0 = source => stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
const digest0 = source => createHash('sha256').update(compact0(source)).digest('hex');
const printed0 = source => [...source.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(row => row[1]);
function inspect0(source, spec) {
  const failures = [], clean = compact0(source);
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('unaudited-form');
  if (/\b(?:sorry|admit|unsafe|native_decide|noncomputable|Classical|implemented_by|csimp)\b|#(?:eval|reduce|guard|synth)\b/u.test(clean))
    failures.push('shortcut');
  if (JSON.stringify(explicitLeanDeclarationHeads0(source).map(({kind, name}) => ({kind, name}))) !==
      JSON.stringify(spec.heads)) failures.push('closed-declarations');
  if (digest0(source) !== spec.sourceContractSha256) failures.push('reviewed-source-contract');
  return failures;
}
let loaded;
function sources0() {
  loaded ??= Promise.all(SPECS.map(async spec => ({spec, source: await text0(spec.path)})));
  return loaded;
}
async function rejectMutations0(part, mutations) {
  const found = (await sources0()).find(row => row.spec.part === part);
  assert.ok(found, part);
  for (const [label, from, to] of mutations) {
    assert.ok(found.source.includes(from), part + ': mutation target exists: ' + label);
    const changed = found.source.replace(from, to);
    assert.notEqual(changed, found.source, label);
    assert.ok(inspect0(changed, found.spec).length > 0, part + ': ' + label);
  }
}

test('M270 source: all arbitrary-dimension implementations have closed reviewed contracts', async () => {
  assert.deepEqual(SPECS.map(row => row.part), [
    'TopologicalWireStructure', 'GateRenaming', 'StructuralReindexing', 'ReindexedSupport',
    'ReindexedPorts', 'ReindexedOpenSemantics', 'ReindexedReplacement', 'ReindexedSplice',
    'ReindexedCompiledSplice',
  ]);
  assert.equal(AXIOM_NAMES.length, 108);
  assert.equal(new Set(AXIOM_NAMES).size, 108);
  assert.deepEqual(ADDITIVE.filter(row => row.kind !== 'theorem').map(row => row.name),
    ['PNP.DirectWire.terminalOpenSourceValue']);
  for (const {spec, source} of await sources0()) assert.deepEqual(inspect0(source, spec), [], spec.path);
});

test('M270 source: hidden premises, private authority and unaudited declarations reject', async () => {
  for (const {spec, source} of await sources0()) {
    for (const extra of [
      'axiom hiddenAuthority : True', 'private axiom hiddenAuthority : True',
      'opaque hiddenAuthority : True', 'variable (suppliedCorrectness : Prop)',
      'variable (suppliedOwnership : Nat)', 'import PNP.Main',
      'unsafe def hiddenAuthority : Nat := 0', 'private theorem hiddenAuthority : True := by trivial',
      'example : True := by trivial', 'def hiddenAuthority : Nat := 0',
    ]) assert.ok(inspect0(source + '\n' + extra + '\n', spec).length > 0, spec.path + ': ' + extra);
    assert.deepEqual(inspect0(source + '\n/- prose: axiom hiddenAuthority : True -/\n', spec), []);
  }
});

test('M270 source: literal fidelity belongs to the actual compiler, not a supplied result', async () => {
  await rejectMutations0('TopologicalWireStructure', [
    ['actual acceptance equation', '(accepted : compileRawNandGraph graph = some compiled)',
      '(accepted : True)'],
    ['every emitted source pair', 'compiled.program.terminalGateSources (compiled.position node)',
      'suppliedSourcePair node'],
    ['actual inverse placement', '(compiled.physicalOrigin position)', '(suppliedOrigin position)'],
  ]);
  await rejectMutations0('StructuralReindexing', [
    ['source-derived raw gate', 'program.terminalGateSources (relabeling.backward node)',
      'suppliedGateSources node'],
    ['actual compiled position', '(compiled program relabeling).position (relabeling.forward node)',
      'suppliedPosition node'],
    ['whole ordered output word', 'sourceMap relabeling.forward (word.source output)',
      'sourceMap relabeling.forward (.constant false)'],
  ]);
});

test('M270 source: raw decoding checks both bounds and the entire instruction sequence', async () => {
  await rejectMutations0('GateRenaming', [
    ['first bound', 'if leftValid : left < nodes then', 'if leftValid : left <= nodes then'],
    ['second bound', 'if rightValid : right < nodes then', 'if rightValid : right <= nodes then'],
    ['complete sequence', '(decode nodes remaining).map', '(decode nodes []).map'],
    ['ordered inverse composition', 'first.backward (second.backward node)',
      'second.backward (first.backward node)'],
    ['literal constants', '| .constant value => .constant value', '| .constant value => .constant false'],
  ]);
});

test('M270 source: arbitrary descendant supports and canonical independent ports are computed', async () => {
  await rejectMutations0('ReindexedSupport', [
    ['all descendant records', 'records.map (backwardRecord program relabeling)',
      '(records.take 1).map (backwardRecord program relabeling)'],
    ['all forward records', 'records.map (forwardRecord program relabeling)',
      '(records.take 1).map (forwardRecord program relabeling)'],
    ['actual inverse gate', '| .gate position => .gate (backwardGate program relabeling position)',
      '| .gate position => .gate (suppliedGate position)'],
  ]);
  await rejectMutations0('ReindexedPorts', [
    ['derived canonical indices', 'computedBijection _ _ _ _', 'suppliedPortBijection'],
    ['input permutation direction', 'valuation ((boundaryPorts original relabeling records).backward index)',
      'valuation ((boundaryPorts original relabeling records).forward index)'],
    ['output permutation direction', 'valuation ((boundaryPorts original relabeling records).forward index)',
      'valuation ((boundaryPorts original relabeling records).backward index)'],
  ]);
  await rejectMutations0('ReindexedOpenSemantics', [
    ['independent boundary inputs', 'pushBoundaryValuation original relabeling records valuation',
      'terminalInducedBoundaryValuation (result original relabeling) records (fun _ => false)'],
    ['literal causal source proof', 'result_sources, selectedSame', 'suppliedSources, selectedSame'],
  ]);
});

test('M270 source: literal replacement preserves both port directions and exact signed savings', async () => {
  await rejectMutations0('ReindexedReplacement', [
    ['actual offered program', 'offered.program.renameInputs (boundaryPorts original relabeling records).backward',
      'suppliedReplacementProgram'],
    ['input direction', '(boundaryPorts original relabeling records).backward',
      '(boundaryPorts original relabeling records).forward'],
    ['output direction', '(interfacePorts original relabeling records).forward output',
      '(interfacePorts original relabeling records).backward output'],
    ['signed cost difference', '.gateCount : Int) -', '.gateCount : Int) +'],
    ['strict local saving', '(smaller : offered.toImplementation.gateCount <',
      '(smaller : offered.toImplementation.gateCount <='],
  ]);
});

test('M270 source: raw splice retains exact ownership, both edges and bidirectional rejection', async () => {
  await rejectMutations0('ReindexedSplice', [
    ['computed exterior map', '(exteriorPorts original relabeling records).forward outside',
      '(exteriorPorts original relabeling records).backward outside'],
    ['same replacement coordinate', 'Fin.natAdd (ArbitrarySupportSplice.exterior records).length inside',
      'Fin.natAdd (ArbitrarySupportSplice.exterior records).length (Fin.rev inside)'],
    ['both source edges', 'exact Or.inr (splice_source_injective original relabeling records right)',
      'exact Or.inl (splice_source_injective original relabeling records right)'],
    ['both rejection directions', '= none ↔', '= none →'],
    ['actual compiler acceptance', 'rw [ArbitrarySupportSplice.compile_success_iff, ArbitrarySupportSplice.compile_success_iff]',
      'exact suppliedCompilerAcceptance'],
  ]);
});

test('M270 source: emitted physical wiring and the computed predecessor cannot be substituted', async () => {
  await rejectMutations0('ReindexedCompiledSplice', [
    ['actual inverse physical position',
      'after.position (spliceForward original relabeling records (before.physicalOrigin position))',
      'after.position (spliceForward original relabeling records (suppliedOrigin position))'],
    ['actual old compiler equation', '(beforeAccepted : ArbitrarySupportSplice.compile original',
      '(beforeAccepted : SuppliedCompilation original'],
    ['actual new compiler equation', '(afterAccepted : ArbitrarySupportSplice.compile (result original relabeling) records offered =',
      '(afterAccepted : suppliedCompilation ='],
    ['derived actual predecessor', 'def pullCompiledSplice : CompiledRawNandGraph',
      'def pullCompiledSplice (suppliedResult : Nat) : CompiledRawNandGraph'],
    ['actual independent compatibility', '(equivalent : offered.semantics =',
      '(equivalent : suppliedSemantics ='],
    ['strict final saving', 'before.count < gates)', 'before.count <= gates)'],
  ]);
});

test('M270 preflight: explicit root, exact theorem audit and reviewed regressions agree', async () => {
  const root = await text0('lean/PNP.lean');
  const audit = await text0('lean-audit/PNPStructuralReindexingAxiomAudit.lean');
  assert.match(audit, /^import PNP$/mu);
  assert.deepEqual(printed0(audit), AXIOM_NAMES);
  for (const spec of SPECS) assert.ok(root.split('\n').includes('import ' + spec.module), spec.path);
  for (const spec of REGRESSIONS) {
    const source = await text0(spec.path);
    assert.equal(digest0(source), spec.sourceContractSha256, spec.path);
    assert.deepEqual(printed0(source), spec.printedNames, spec.path);
    assert.deepEqual([...source.matchAll(/^import (\S+)\s*$/gmu)].map(row => row[1]), spec.imports, spec.path);
    assert.doesNotMatch(stripLeanCommentsAndStrings0(source), /\b(?:sorry|admit|native_decide|unsafe)\b|#eval!/u);
  }
  for (const row of ADDITIVE) {
    const leaf = row.name.split('.').at(-1);
    const heads = explicitLeanDeclarationHeads0(await text0(row.path)).filter(head => head.name === leaf);
    assert.equal(heads.length, 1, row.name);
    assert.equal(heads[0].kind, row.kind, row.name);
  }
});
