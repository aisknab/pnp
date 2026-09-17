import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  DeriveFormalPublication0, MilestoneTheoremKernelTypeSha2560,
  REQUIRED_MILESTONE_THEOREMS0, stableStringify0,
} from '../formal-publication0.mjs';
import {CheckFormalReconstructionStatus0} from '../pcc-formal-reconstruction-status0.mjs';
import {validateProofProgress0} from '../pcc-proof-progress0.mjs';

// Exact compiled type, module and axiom pins frozen after component review.
// The independent explicit-root inventory must match these expectations.
const REVIEWED = [
  ["PNP.DirectWire.RawNandWireStructure.initial_faithful","e7042f7084f9f6041f83b01963bf2030de0acc306654e9e2ab3d4e0cb8d0b285","PNP.NANDTopologicalWireStructure",["Quot.sound","propext"]],
  ["PNP.DirectWire.RawNandWireStructure.apply_faithful","f60df4d336d71a0c71c724985145147576843d0b53320b5e06fefe3655aeecda","PNP.NANDTopologicalWireStructure",["Quot.sound","propext"]],
  ["PNP.DirectWire.RawNandWireStructure.run_faithful","847686fee173489bf2754901e7b62ad529541016c09f92ccd15bc579c7187aab","PNP.NANDTopologicalWireStructure",["Quot.sound","propext"]],
  ["PNP.DirectWire.RawNandWireStructure.finish_sources","c2db6b1569ad4f93208f71419227ea4f4dbed991a277ffcbed3fa2de33769d3b","PNP.NANDTopologicalWireStructure",["propext"]],
  ["PNP.DirectWire.RawNandWireStructure.compile_sources","4e81fb4afae8047b603eb8e8fa6c71fc8d3bfc03eb41afe531e828c5728f4d17","PNP.NANDTopologicalWireStructure",["Quot.sound","propext"]],
  ["PNP.DirectWire.RawNandWireStructure.physicalOrigin_sources","128dd1544dfc0db8828c2c62f6c8e3a139debf689c83221f663457b033e2278c","PNP.NANDTopologicalWireStructure",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.GateRenaming.forward_injective","46795fdf8ea3cb0a0dbe2fd9b1421469b4dfa74f0eb936b91bd8813040213c0c","PNP.NANDGateRenaming",[]],
  ["PNP.DirectWire.StructuralReindexing.GateRenaming.backward_injective","a93f902c001902de91c95cb5083c3d5c62d3131dba83942c974b28599199afba","PNP.NANDGateRenaming",[]],
  ["PNP.DirectWire.StructuralReindexing.GateRenaming.decode_isSome","dc4bbe912dfce7f42cc3ded9ad5c49e82e0337b04f084715bfc55ad035b75de5","PNP.NANDGateRenaming",["propext"]],
  ["PNP.DirectWire.StructuralReindexing.sourceMap_compose","7150ce62f2c984229655e3e4e5f3b0a9ad8769bbcfbaee91b25065cd97342125","PNP.NANDGateRenaming",[]],
  ["PNP.DirectWire.StructuralReindexing.sourceMap_eq_gate_iff","41d41b2b29c23ab74cda42f3738d4c1083b2a22207d55e97b4743f9ef8bab259","PNP.NANDGateRenaming",[]],
  ["PNP.DirectWire.StructuralReindexing.sourceMap_eval","20dcb0abc64f34dad88fe5746f37ace6766de74e02c78948842d951830b7dcaf","PNP.NANDGateRenaming",[]],
  ["PNP.DirectWire.StructuralReindexing.graph_edge_ordered","e922690df23889b47b32454331d6f2ac6fd186604b225e4a83cdcaf044923de4","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.graph_wellFounded","3916a452b6de280e882251327b4f0cac30cb98ea4715947698b640dd4f070dc8","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.compile_isSome","d1e7e9933005ef4cda798225dbd870fe057d46f632f241eaca6bcd4a99d102d4","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.compiled_accepted","4db9d5d92345462dc6b8186158f095ff8c820b33366398dd1acbd9c076f89ee0","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.backward_forward","5d8e64d9dcbff4e127216c2a08222267b43f64541a75b204a41f8a0db0115331","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.forward_backward","2ad0353f06419392412f85f15b4d9347e0e01bde948c9d9731ceb5f3069327fd","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.forwardGate_injective","92483d0d095663d8ad4f5a3269a6eecfb07bbeeb74841a326de604e2a3357987","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.backwardGate_injective","e7f1a1f40a81db0da6df33edaa55890cdddceb54b35c650287bd6c19e03faa36","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.translated_source","509c5e335bf5c68a2a8b80e60833aebab89df68f6eaeac6308adbc4948a803c4","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.result_sources","0e615487098bb6b4019ce2b5da4c423f61c35f6925b528e23aeb47b4b6d4e5ad","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.result_output_source","23f3ce57ea33cb389a0cbb9001892775ebba92f9f0e2bdf748feed95b1e57006","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.result_gateCount","5ac11c5f8710bdb849333ea6446f3a2c34042d42670f61ca75653e4605434148","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.graph_solution","90da8fd6211b4b5f634eb0d4fdcaccd55fe3140cee75d6c8faebec10f9e86c50","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.result_semantics","924d51731ad7a297bae72b26493211d87e7dac5340603ff92356c24e37a87424","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.attempt_isSome","4cb44888349c66b54fe9590a9fbb1962c9ff1265e9284a4c065ce1ededaf6696","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.attempt_semantics","032d59d05b9e3e4c9bbedfd0090c3eb414301dec843175c7381c47baa23c3b9b","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.attempt_gateCount","95705049635aaaa1357a0cd6bb5bef9ce4e730aae593ce64943f3fe8b482a03f","PNP.NANDStructuralReindexing",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.backward_forward_wire","eb7159ac249a8498365c26a9e97bfa5448182d99daef8f9a3ad8b5843350dbb8","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.forward_backward_wire","90e371d50b055069a0dd2ef55f4e3a08728096d14fcd6935966f9598de84fb80","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.backward_forward_record","f4c3d8c381b25a75b852fa7923cca57e91783dba1a740b5cd348f88d33e61225","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.forward_backward_record","dead7770b1c74dd93d953789eb0e8f425c0cfa0880c9a900ca867832a890d405","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.forwardRecord_injective","99ec264636589c6210ae638a5d6f0bf919c89bb477023f6159fab7a7a5d5aed8","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.backward_forward_records","07874381bc467203411021e2cfc5543f9cc2ebab2b091b6ea4306473801190c7","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.forward_backward_records","3c06792d39643bb83524aa1228dad3a4c3272701b3608ab242941ae94934e903","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.forwardRecord_mem","a76c5b872877ca1e8355c467fe63e352c18b7e290a1d7cb01be548774782d3f0","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.selected_forward","58d8587bc13ef48f0bbd66d65b404871f46ef3dcf6b4f281a9fbed18a160f13e","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.external_forward","d8f7f158b8a90b1ba7382d75a8a2eb6e282700729325bf3983d5be45b3c7b24a","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.backward_forward_source","a29fbf30df1336c90904034dd1bff6d24f041094211c0b19dcab69e46b189956","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.sourceMap_forward_injective","c2376929f530cfe83a534b40f0a43a6571571187579e2dec5caffe50ed2ca9fd","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.source_wire_map","94a647635c683860bfb6ad4a90cbacf976fa499a7bc7df705594200f78ce83e5","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.source_wire_iff","d8e721b4bfd824df2087838d95ad96401d986dd4ec4efa15eb5e06a7baba1174","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.uses_forward","f67c46b240f493be0f322cca3ef004658946c8b9cb350e90d910af6e56ed0eda","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.boundary_forward","723b781158e13d90de889815029368e36d4b958d02e3f5adbf8d731e8c174325","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.externalConsumer_forward","128d0cb68767dbbc48c1955df5d8baec0f22e4556dbb73f22300fe8962a65cad","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.globalOutput_forward","0409980ab919d9b2973e4b9198414a13698f68ed49d9beca4973102bf3288820","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.interface_forward","062045cda54a5d7598a892222963c39e9ee1e48449455e2a16ed8ac6899db3c7","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.boundary_ports_forward","8f3f86c756b0aaaa0a4ba7c7a30d2bd88adc449cb9cca730c263c1f142bdbc36","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.interface_ports_forward","3ec95440966ec8b7ebdeb44ca59bfe8d3359093e9845bb0c20456ec46bacdc13","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.descendant_boundary","27dd51223f61fd631968bc87de4b7fb069b6ac46b8063c996f83fbb8856b7bd9","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.descendant_interface","ea0552de68842ff4d9ee798cb650f89d30502cb4bc920e08aabc5f0e29045480","PNP.NANDReindexedSupport",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.selected_backward","be5d80099cfa8602d0c46f3859da6220f3519d669058c6aa7871fd1b45c66d3e","PNP.NANDReindexedPorts",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.pull_push_boundary_valuation","143f6453fd47d0a9ea1e41b256a23bc6591ac7ad645dfbdc33eec9e1a04ed68f","PNP.NANDReindexedPorts",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.push_pull_boundary_valuation","b4c3905c60c563c21469dc4691154691421076023f60f2ead0166cd2483ab89c","PNP.NANDReindexedPorts",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.selected_gate_count","07ab1af3b7fe20f7739c49ee35e9399eb1c8db75052021240f19c9e417931a8b","PNP.NANDReindexedPorts",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.exterior_gate_count","359b51d69f5c902f6750efc088d49ec4ef9c2c3b0b5571c9f0f429a46adce3d3","PNP.NANDReindexedPorts",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.external_wire_value_preserved","5eb90d625a7e6ac30d72edba27f374488406cb7f8b6b84ecaa060018e85ad5a2","PNP.NANDReindexedOpenSemantics",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.open_gate_preserved","ad0e2b076d35f8c5d28e8c44c86d4aa8ec09b5d465810cdb2a0cb7950f666648","PNP.NANDReindexedOpenSemantics",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.open_support_preserved","9ec61bf9e82d444bd4108130417146ec73bce8ed0883de1aee13288d1659e247","PNP.NANDReindexedOpenSemantics",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.open_support_pullback","a7330e1af6e14c91be065a79aa1317898b846c8d9e4756d4525b98949919809f","PNP.NANDReindexedOpenSemantics",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.extracted_support_preserved","7e677b708368c972a3bb9778bf1b6b08282e91391e60cb033086d7b892a0641a","PNP.NANDReindexedOpenSemantics",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.renameInputs_gateSources","7c2b79875b3014941c1cb70f4d4bb9ff3531ccb9b4afe7232734a43350575daf","PNP.NANDReindexedReplacement",["propext"]],
  ["PNP.DirectWire.StructuralReindexing.pullReplacement_program","d0b640bffbbac6ce33de15c15facf281402620f33adff8c18bdb86e666397fab","PNP.NANDReindexedReplacement",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.pullReplacement_gate_sources","95d11fcc9118932d356f35169b64d9aec82547fa4f95b3ae72bfcff75dc2ec83","PNP.NANDReindexedReplacement",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.pullReplacement_output_source","166c4efde4ee7855073c61b0a5c0cc482dab7be72d68aed33c035c10f134bc75","PNP.NANDReindexedReplacement",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.pullReplacement_gate_count","6fe3453c732cea767625b5a372f70b97d30774ba8b04a11c207227f4e32e8634","PNP.NANDReindexedReplacement",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.pullReplacement_semantics","c79477c9d2248387ba8021c9e6551b1dd2450b49ac947052984b9f869456b954","PNP.NANDReindexedReplacement",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.pullReplacement_compatible","e9d11580c29ae3d633f89feaca7f4392251417cc5e2a03954e1dc0a8b748dbe8","PNP.NANDReindexedReplacement",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.support_gate_count","f6f179fbfed857a9caf8ecf83c786bb7419e413f410540aff77330dac64a596d","PNP.NANDReindexedReplacement",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.support_surcharge_zero","2e9876d2ca2e890f20308774fd7914c42bbb07787283e12fa844151b5d244dd7","PNP.NANDReindexedReplacement",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.replacement_surcharge_zero","be1b0c722779c52ce98a41590b086e37a03b69fe25985373587fe3d8a3e9979f","PNP.NANDReindexedReplacement",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.matched_surcharge","5debfaf49afaaaded71c9c92822fcf35bfd3cff7a4333af813c5fb1c00079810","PNP.NANDReindexedReplacement",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.replacement_saving_preserved","67c63a654277c26ab473f29958980cda3bf3e67ed81c2f35bacd402f686a24f0","PNP.NANDReindexedReplacement",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.strict_gain_pullback","5523c388a39ab17052f8ac414b69d0105e0136a1e82555ffc837b07e943ef4ad","PNP.NANDReindexedReplacement",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.spliceForward_exterior","90915ac28eb2912f792dae1ecfd9e61c80e116a92af8d11714c906e4279634f7","PNP.NANDReindexedSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.spliceForward_replacement","8aa2927657a840be6ecd60ee44a30bf037ba46f63548eaeffdea0c53bb206285","PNP.NANDReindexedSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.spliceBackward_exterior","b20348a3a6c9967b8656276c131adceb9a464989d4353a012d7ca09c9019bcf2","PNP.NANDReindexedSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.spliceBackward_replacement","5be5229fcb3289084e3539dd4b808944fdfbbf250e884bce646c2270e7f72d1a","PNP.NANDReindexedSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_backward_forward","21cec0f9e436b3ece57c6253f3521c706cffe62e2352474b504feddea5227cce","PNP.NANDReindexedSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_forward_backward","6ec84c3a81fa3292fc7cbb803d3284a2d28136bf139a6e40a21963671093fab5","PNP.NANDReindexedSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_boundarySource_forward","1fae075fa580f6f7b52e6610a526069143a214884f91fba72106b803db22fb75","PNP.NANDReindexedSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_replacementSource_forward","9fb8d0cd2f06110d8b3b2ba028dbcae6828e85c39b8a2cdffa756af17cb08283","PNP.NANDReindexedSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_sources","8e95574ad082037a66bdeb2e4fd2dc0cd5b72f3da7942154e33fa43f02fe4df1","PNP.NANDReindexedSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_output_source","5f2a5c908e4f243398cb27e92fadfe7d994acf184d66a5f3b6028804d83e55ff","PNP.NANDReindexedSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_dependencies","23879156aba4bd540245543e502bdf642914997e5ce839e79ed9c3ba55a75111","PNP.NANDReindexedSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_wellFounded_iff","f6213cb37d4cf14b07ed34318c1d3afbd7ddff24fa278288d1812a6fdbee9bab","PNP.NANDReindexedSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_compile_success_iff","57b4c35d17108248d835e6c5ec191892febcd62e5c26e90a861d0bca5747c3e2","PNP.NANDReindexedSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_compile_failure_iff","b0fb5032ee35a49b8cf3280f22089559dbcdb10060ee99721a294afe5c255e24","PNP.NANDReindexedSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_physical_backward_forward","1a107e1f4e019ea3d23b2ce82d179640c6131cc526c0d1e562487025e989667c","PNP.NANDReindexedCompiledSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_physical_forward_backward","6616f0bfc12af01b2355c00b739648c88c4dbc5ada89fc15e660ec177d152fd4","PNP.NANDReindexedCompiledSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_physical_position","ba6a049ef22466b4ed633b72bd122c012c153c2ffd8f7c4ec21c25798ddafa20","PNP.NANDReindexedCompiledSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_physical_exterior","94ef27d3a0d86ed7864eccca2627adbb9791b873d3fd0473f2842bac32018020","PNP.NANDReindexedCompiledSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_physical_replacement","33a5ec92de9e78280eea7e0fe498695c94e33db6b7fbf4b6a38e47746a275071","PNP.NANDReindexedCompiledSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_compiled_sources","b5d8ea1ed268f9b85b5a7113936cf714aecd03796a74dc9a3e439bd777ca1014","PNP.NANDReindexedCompiledSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_compiled_output_source","39b559176c54d63583f72cb73092e59fe2c9baa4573ce466162acd3027f21999","PNP.NANDReindexedCompiledSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_compiled_gate_count","2f949b88ca9475a55b12c54c653a0c080945cd5f0451c21dd4a9f851d4ac547e","PNP.NANDReindexedCompiledSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.splice_compiled_semantics","a1e9bf9938337fcef53f595b9c03e1b5ecf1cc94a28e41a5db9fedd3f29e697d","PNP.NANDReindexedCompiledSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.pull_splice_isSome","2052b46d2ed1b72774821fb8b12b1f660eb4f50dc2ee214a73358b625b83859f","PNP.NANDReindexedCompiledSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.pullCompiledSplice_accepted","d2c8151aa777fcc563ed5692a587449e65de7e51ddfa73b7fd4afc0f9c9a5bd8","PNP.NANDReindexedCompiledSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.StructuralReindexing.literal_replacement_transport","6f6ba6fd10ae2025274a65566740f5f230222c092badfc6ceb17eb00b116b7f5","PNP.NANDReindexedCompiledSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.terminalOpenGateEvaluation_sourceEquation","d3c53e7e15227c609b625667699798e5f151715bef508d181575f265b8402764","PNP.ResidualTerminalSupportExtraction",["propext"]],
  ["PNP.DirectWire.terminalOpenWireValue_boundary_get","87a7979757248c52077a0b0400846e4d8a295a863bd99c933dc3f7161c0ec9b6","PNP.ResidualTerminalSupportExtraction",["Quot.sound","propext"]],
  ["PNP.DirectWire.terminalOpenWireValue_external_absent","466fa8b9f64fef0ba0769d78b981f0e35c890ed20dd8fdbf897315a653c95ad7","PNP.ResidualTerminalSupportExtraction",["propext"]],
  ["PNP.DirectWire.ArbitrarySupportSplice.boundarySource_input","6756b4ea8cadeacc264dbc2e956df0bffe34980cdf8bb07ba5830e0a6c135195","PNP.NANDArbitrarySupportSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.ArbitrarySupportSplice.boundarySource_gate","7ac4e0b759c4cad50eb22be05168881e77fe1f0a0ed6eba7d64f006f76a0f49d","PNP.NANDArbitrarySupportSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.ArbitrarySupportSplice.originalSource_exterior","506c4ff0744cc8dc5328c013f1c8437f90b45bc0c4812b835cfcb3a75df309f5","PNP.NANDArbitrarySupportSplice",["Quot.sound","propext"]],
  ["PNP.DirectWire.ArbitrarySupportSplice.originalSource_interface","93ff230f571633713e0da734a4b3795d4cd069c5e411c953ca07ea9281a2c049","PNP.NANDArbitrarySupportSplice",["Quot.sound","propext"]]
];
const META = {
  "coordinate": "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-17-270",
  "milestone": {
    "classification": "formalized-foundation-only",
    "id": "structural-reindexing-support-transport",
    "title": "Structural reordering and arbitrary-support replacement transport",
    "scope": "For arbitrary finite computational wire candidates and checked finite raw index-swap sequences, structural reindexing constructs the raw graph and its successful compilation from the original circuit. Actual compiler placement and inverse placement determine literal gate-source pairs and ordered output references. For every descendant primitive-record list, including empty, full and duplicate-bearing lists, the construction derives the predecessor records and canonical boundary, interface, selected-gate and exterior bijections. Open support functions agree for every independent boundary valuation. A replacement is pulled back by literal input and output rewiring without padding; support and replacement counts agree, both matched signed surcharges are zero, and exact signed saving and strict gain are preserved. Complete raw splices have corresponding source pairs, outputs and dependency edges, with equivalent acyclicity and compiler success or rejection in both directions. Actual compiled-position maps preserve exterior and replacement ownership and literal sources. An actually accepted compatible descendant splice computes an accepted predecessor splice preserving whole-circuit semantics and exact local and whole signed savings. No predecessor compilation, order, transport map or source-fidelity witness is supplied.",
    "nonClaim": "This closes the computational structural-reordering component of arbitrary-support replacement transport, not full manuscript profile semantics: transported profile labels are not a proof of profile semantics. It does not establish completeness of the raw-swap encoding for every abstract permutation, all R1-R9 or N1-N10 rules, or the remaining normalization and materializer transport. Open replacement compatibility is required for semantic preservation, and actual descendant compiler acceptance is required for compiled pullback; a compatible arbitrary replacement need not be acyclic. Full manuscript VerifyDW, ChargeSoundness and Package E, global certificate discovery, terminal-family derivation and global route coverage remain open. There is no encoded-input polynomial runtime, output-size or certificate-size theorem for the complete construction. Unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin, deterministic CNFSAT in P and the eligible root remain open. Finite execution fixtures are regression evidence, not theorem authority. No fixed weighted checkpoint or global gate closes, and P = NP is not proved.",
    "requiredTheorems": [
      "PNP.DirectWire.RawNandWireStructure.initial_faithful",
      "PNP.DirectWire.RawNandWireStructure.apply_faithful",
      "PNP.DirectWire.RawNandWireStructure.run_faithful",
      "PNP.DirectWire.RawNandWireStructure.finish_sources",
      "PNP.DirectWire.RawNandWireStructure.compile_sources",
      "PNP.DirectWire.RawNandWireStructure.physicalOrigin_sources",
      "PNP.DirectWire.StructuralReindexing.GateRenaming.forward_injective",
      "PNP.DirectWire.StructuralReindexing.GateRenaming.backward_injective",
      "PNP.DirectWire.StructuralReindexing.GateRenaming.decode_isSome",
      "PNP.DirectWire.StructuralReindexing.sourceMap_compose",
      "PNP.DirectWire.StructuralReindexing.sourceMap_eq_gate_iff",
      "PNP.DirectWire.StructuralReindexing.sourceMap_eval",
      "PNP.DirectWire.StructuralReindexing.graph_edge_ordered",
      "PNP.DirectWire.StructuralReindexing.graph_wellFounded",
      "PNP.DirectWire.StructuralReindexing.compile_isSome",
      "PNP.DirectWire.StructuralReindexing.compiled_accepted",
      "PNP.DirectWire.StructuralReindexing.backward_forward",
      "PNP.DirectWire.StructuralReindexing.forward_backward",
      "PNP.DirectWire.StructuralReindexing.forwardGate_injective",
      "PNP.DirectWire.StructuralReindexing.backwardGate_injective",
      "PNP.DirectWire.StructuralReindexing.translated_source",
      "PNP.DirectWire.StructuralReindexing.result_sources",
      "PNP.DirectWire.StructuralReindexing.result_output_source",
      "PNP.DirectWire.StructuralReindexing.result_gateCount",
      "PNP.DirectWire.StructuralReindexing.graph_solution",
      "PNP.DirectWire.StructuralReindexing.result_semantics",
      "PNP.DirectWire.StructuralReindexing.attempt_isSome",
      "PNP.DirectWire.StructuralReindexing.attempt_semantics",
      "PNP.DirectWire.StructuralReindexing.attempt_gateCount",
      "PNP.DirectWire.StructuralReindexing.backward_forward_wire",
      "PNP.DirectWire.StructuralReindexing.forward_backward_wire",
      "PNP.DirectWire.StructuralReindexing.backward_forward_record",
      "PNP.DirectWire.StructuralReindexing.forward_backward_record",
      "PNP.DirectWire.StructuralReindexing.forwardRecord_injective",
      "PNP.DirectWire.StructuralReindexing.backward_forward_records",
      "PNP.DirectWire.StructuralReindexing.forward_backward_records",
      "PNP.DirectWire.StructuralReindexing.forwardRecord_mem",
      "PNP.DirectWire.StructuralReindexing.selected_forward",
      "PNP.DirectWire.StructuralReindexing.external_forward",
      "PNP.DirectWire.StructuralReindexing.backward_forward_source",
      "PNP.DirectWire.StructuralReindexing.sourceMap_forward_injective",
      "PNP.DirectWire.StructuralReindexing.source_wire_map",
      "PNP.DirectWire.StructuralReindexing.source_wire_iff",
      "PNP.DirectWire.StructuralReindexing.uses_forward",
      "PNP.DirectWire.StructuralReindexing.boundary_forward",
      "PNP.DirectWire.StructuralReindexing.externalConsumer_forward",
      "PNP.DirectWire.StructuralReindexing.globalOutput_forward",
      "PNP.DirectWire.StructuralReindexing.interface_forward",
      "PNP.DirectWire.StructuralReindexing.boundary_ports_forward",
      "PNP.DirectWire.StructuralReindexing.interface_ports_forward",
      "PNP.DirectWire.StructuralReindexing.descendant_boundary",
      "PNP.DirectWire.StructuralReindexing.descendant_interface",
      "PNP.DirectWire.StructuralReindexing.selected_backward",
      "PNP.DirectWire.StructuralReindexing.pull_push_boundary_valuation",
      "PNP.DirectWire.StructuralReindexing.push_pull_boundary_valuation",
      "PNP.DirectWire.StructuralReindexing.selected_gate_count",
      "PNP.DirectWire.StructuralReindexing.exterior_gate_count",
      "PNP.DirectWire.StructuralReindexing.external_wire_value_preserved",
      "PNP.DirectWire.StructuralReindexing.open_gate_preserved",
      "PNP.DirectWire.StructuralReindexing.open_support_preserved",
      "PNP.DirectWire.StructuralReindexing.open_support_pullback",
      "PNP.DirectWire.StructuralReindexing.extracted_support_preserved",
      "PNP.DirectWire.StructuralReindexing.renameInputs_gateSources",
      "PNP.DirectWire.StructuralReindexing.pullReplacement_program",
      "PNP.DirectWire.StructuralReindexing.pullReplacement_gate_sources",
      "PNP.DirectWire.StructuralReindexing.pullReplacement_output_source",
      "PNP.DirectWire.StructuralReindexing.pullReplacement_gate_count",
      "PNP.DirectWire.StructuralReindexing.pullReplacement_semantics",
      "PNP.DirectWire.StructuralReindexing.pullReplacement_compatible",
      "PNP.DirectWire.StructuralReindexing.support_gate_count",
      "PNP.DirectWire.StructuralReindexing.support_surcharge_zero",
      "PNP.DirectWire.StructuralReindexing.replacement_surcharge_zero",
      "PNP.DirectWire.StructuralReindexing.matched_surcharge",
      "PNP.DirectWire.StructuralReindexing.replacement_saving_preserved",
      "PNP.DirectWire.StructuralReindexing.strict_gain_pullback",
      "PNP.DirectWire.StructuralReindexing.spliceForward_exterior",
      "PNP.DirectWire.StructuralReindexing.spliceForward_replacement",
      "PNP.DirectWire.StructuralReindexing.spliceBackward_exterior",
      "PNP.DirectWire.StructuralReindexing.spliceBackward_replacement",
      "PNP.DirectWire.StructuralReindexing.splice_backward_forward",
      "PNP.DirectWire.StructuralReindexing.splice_forward_backward",
      "PNP.DirectWire.StructuralReindexing.splice_boundarySource_forward",
      "PNP.DirectWire.StructuralReindexing.splice_replacementSource_forward",
      "PNP.DirectWire.StructuralReindexing.splice_sources",
      "PNP.DirectWire.StructuralReindexing.splice_output_source",
      "PNP.DirectWire.StructuralReindexing.splice_dependencies",
      "PNP.DirectWire.StructuralReindexing.splice_wellFounded_iff",
      "PNP.DirectWire.StructuralReindexing.splice_compile_success_iff",
      "PNP.DirectWire.StructuralReindexing.splice_compile_failure_iff",
      "PNP.DirectWire.StructuralReindexing.splice_physical_backward_forward",
      "PNP.DirectWire.StructuralReindexing.splice_physical_forward_backward",
      "PNP.DirectWire.StructuralReindexing.splice_physical_position",
      "PNP.DirectWire.StructuralReindexing.splice_physical_exterior",
      "PNP.DirectWire.StructuralReindexing.splice_physical_replacement",
      "PNP.DirectWire.StructuralReindexing.splice_compiled_sources",
      "PNP.DirectWire.StructuralReindexing.splice_compiled_output_source",
      "PNP.DirectWire.StructuralReindexing.splice_compiled_gate_count",
      "PNP.DirectWire.StructuralReindexing.splice_compiled_semantics",
      "PNP.DirectWire.StructuralReindexing.pull_splice_isSome",
      "PNP.DirectWire.StructuralReindexing.pullCompiledSplice_accepted",
      "PNP.DirectWire.StructuralReindexing.literal_replacement_transport",
      "PNP.DirectWire.terminalOpenGateEvaluation_sourceEquation",
      "PNP.DirectWire.terminalOpenWireValue_boundary_get",
      "PNP.DirectWire.terminalOpenWireValue_external_absent",
      "PNP.DirectWire.ArbitrarySupportSplice.boundarySource_input",
      "PNP.DirectWire.ArbitrarySupportSplice.boundarySource_gate",
      "PNP.DirectWire.ArbitrarySupportSplice.originalSource_exterior",
      "PNP.DirectWire.ArbitrarySupportSplice.originalSource_interface"
    ]
  },
  "statusFields": {
    "leanStructuralReindexingFormalized": true,
    "leanStructuralReindexingAxiomAuditPassed": true,
    "leanStructuralReindexingAuditedDeclarationCount": 108,
    "leanStructuralReindexingActualCompilerSourceFidelityTheorem": "PNP.DirectWire.RawNandWireStructure.compile_sources",
    "leanStructuralReindexingRawSwapDecodeTheorem": "PNP.DirectWire.StructuralReindexing.GateRenaming.decode_isSome",
    "leanStructuralReindexingDerivedCompilationTheorem": "PNP.DirectWire.StructuralReindexing.compiled_accepted",
    "leanStructuralReindexingLiteralSourceTheorem": "PNP.DirectWire.StructuralReindexing.result_sources",
    "leanStructuralReindexingLiteralOutputTheorem": "PNP.DirectWire.StructuralReindexing.result_output_source",
    "leanStructuralReindexingArbitraryRecordRoundTripTheorem": "PNP.DirectWire.StructuralReindexing.forward_backward_records",
    "leanStructuralReindexingBoundaryCorrespondenceTheorem": "PNP.DirectWire.StructuralReindexing.descendant_boundary",
    "leanStructuralReindexingInterfaceCorrespondenceTheorem": "PNP.DirectWire.StructuralReindexing.descendant_interface",
    "leanStructuralReindexingIndependentOpenSemanticsTheorem": "PNP.DirectWire.StructuralReindexing.open_support_pullback",
    "leanStructuralReindexingReplacementCompatibilityTheorem": "PNP.DirectWire.StructuralReindexing.pullReplacement_compatible",
    "leanStructuralReindexingMatchedSurchargeTheorem": "PNP.DirectWire.StructuralReindexing.matched_surcharge",
    "leanStructuralReindexingExactSignedSavingTheorem": "PNP.DirectWire.StructuralReindexing.replacement_saving_preserved",
    "leanStructuralReindexingRawDependencyCorrespondenceTheorem": "PNP.DirectWire.StructuralReindexing.splice_dependencies",
    "leanStructuralReindexingAcyclicityEquivalenceTheorem": "PNP.DirectWire.StructuralReindexing.splice_wellFounded_iff",
    "leanStructuralReindexingCompilationEquivalenceTheorem": "PNP.DirectWire.StructuralReindexing.splice_compile_success_iff",
    "leanStructuralReindexingRejectionEquivalenceTheorem": "PNP.DirectWire.StructuralReindexing.splice_compile_failure_iff",
    "leanStructuralReindexingActualPhysicalPositionTheorem": "PNP.DirectWire.StructuralReindexing.splice_physical_position",
    "leanStructuralReindexingCompiledLiteralSourcesTheorem": "PNP.DirectWire.StructuralReindexing.splice_compiled_sources",
    "leanStructuralReindexingCompiledLiteralOutputTheorem": "PNP.DirectWire.StructuralReindexing.splice_compiled_output_source",
    "leanStructuralReindexingComputedPredecessorAcceptanceTheorem": "PNP.DirectWire.StructuralReindexing.pullCompiledSplice_accepted",
    "leanStructuralReindexingCompleteReplacementTransportTheorem": "PNP.DirectWire.StructuralReindexing.literal_replacement_transport",
    "leanStructuralReindexingArbitraryFiniteDimensionsAndDescendantRecordsCovered": true,
    "leanStructuralReindexingCompleteCheckedRawSwapSequenceRequired": true,
    "leanStructuralReindexingActualCompilerPlacementAndInverseUsed": true,
    "leanStructuralReindexingCanonicalPortAndOwnershipBijectionsDerived": true,
    "leanStructuralReindexingAllIndependentBoundaryValuationsCovered": true,
    "leanStructuralReindexingLiteralInputAndOutputReplacementRewiring": true,
    "leanStructuralReindexingBothMatchedSignedSurchargesZero": true,
    "leanStructuralReindexingExactLocalAndWholeSignedSavingPreserved": true,
    "leanStructuralReindexingBothDependencyAndRejectionDirectionsProved": true,
    "leanStructuralReindexingAcceptedDescendantSpliceRequiredForCompiledPullback": true,
    "leanStructuralReindexingOpenReplacementCompatibilityRequiredForSemantics": true,
    "leanStructuralReindexingCallerSuppliedPredecessorCompilerOrOrderRequired": false,
    "leanStructuralReindexingCallerSuppliedTransportMapsRequired": false,
    "leanStructuralReindexingCallerSuppliedSourceFidelityRequired": false,
    "leanStructuralReindexingPaddingUsed": false,
    "leanStructuralReindexingAllCompatibleSplicesAcyclicProved": false,
    "leanStructuralReindexingArbitraryPermutationEncodingComplete": false,
    "leanStructuralReindexingFullManuscriptProfileSemanticsProved": false,
    "leanStructuralReindexingAllNormalizationAndMaterializerRulesProved": false,
    "leanStructuralReindexingFullManuscriptVerifyDWProved": false,
    "leanStructuralReindexingCompleteChargeSoundnessAndPackageEProved": false,
    "leanStructuralReindexingGlobalCertificateDiscoveryProved": false,
    "leanStructuralReindexingTerminalFamiliesDerived": false,
    "leanStructuralReindexingGlobalRouteCoverageProved": false,
    "leanStructuralReindexingUnconditionalSaturatePositiveProved": false,
    "leanStructuralReindexingUnconditionalBCELReadyProved": false,
    "leanStructuralReindexingUnconditionalZeroSlackProved": false,
    "leanStructuralReindexingExactGeneralPCCMinProved": false,
    "leanStructuralReindexingPolynomialRuntimeOutputAndCertificateBoundsProved": false,
    "leanStructuralReindexingRuntimeExecutionIsProofAuthority": false,
    "leanStructuralReindexingScope": "arbitrary-finite-checked-raw-swaps-and-descendant-records-derived-canonical-port-and-ownership-bijections-independent-open-semantics-literal-replacement-rewiring-zero-matched-surcharge-exact-signed-saving-bidirectional-raw-dependency-and-acceptance-actual-compiled-physical-transport-no-full-profiles-or-materializers-or-global-or-polynomial-claim"
  },
  "audit": "lean-audit/PNPStructuralReindexingAxiomAudit.lean",
  "testFiles": [
    "audits/lean-structural-reindexing0.test.mjs",
    "audits/lean-structural-reindexing-publication0.test.mjs"
  ],
  "doc": "docs/lean_structural_reindexing.md",
  "plan": "docs/plans/2026-09-17-structural-normalization-support-transport.md",
  "command": "node --test audits/lean-structural-reindexing0.test.mjs audits/lean-structural-reindexing-publication0.test.mjs",
  "workflowCommands": "set -euo pipefail\nnode scripts/check-lean-axioms.mjs lean-audit/PNPStructuralReindexingAxiomAudit.lean\nfor part in TopologicalWireStructure StructuralReindexing ReindexedSupport ReindexedPorts TerminalOpenEquations ReindexedOpenSemantics ReindexedReplacement SpliceWireEquations ReindexedSplice ReindexedCompiledSplice; do\n  lake env lean -DwarningAsError=true \"lean-regression/PNP${part}.lean\"\ndone\n",
  "publicationDecision": "Publication decision: defer. This closes the computational structural-reordering and literal arbitrary-support replacement-transport edge, but not full manuscript profiles, materializer transport or a global proof obligation. No fixed weighted checkpoint or global gate changes, and the published global bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication."
};
const MODULES = ["PNP.NANDTopologicalWireStructure","PNP.NANDGateRenaming","PNP.NANDStructuralReindexing","PNP.NANDReindexedSupport","PNP.NANDReindexedPorts","PNP.NANDReindexedOpenSemantics","PNP.NANDReindexedReplacement","PNP.NANDReindexedSplice","PNP.NANDReindexedCompiledSplice"];
const text0 = file=>readFile(new URL('../'+file,import.meta.url),'utf8');
const canonical0 = value=>Buffer.from(stableStringify0(value)+'\n');
const prose0 = value=>value.replaceAll('**','').replace(/\s+/gu,' ').trim();
let loaded;
function sources0() {
  loaded??=Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),text0('status/LEAN_THEOREM_INVENTORY.json'),
    text0('status/PROOF_PROGRESS.json'),text0('publication/FORMAL_PUBLICATION_MAP.json'),
  ]).then(([status,inventory,progress,map])=>({
    status:JSON.parse(status),inventory:JSON.parse(inventory),inventoryBytes:Buffer.from(inventory),
    progress:JSON.parse(progress),map:JSON.parse(map),
  }));
  return loaded;
}

test('M270 preflight: exact root, names, scripts and durable workflow share one boundary',async()=>{
  const [root,audit,probe,pkg,surface,verifier,workflow,mapText]=await Promise.all([
    text0('lean/PNP.lean'),text0(META.audit),text0('lean-audit/PNPTheoremInventory.lean'),
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'),text0('publication/FORMAL_PUBLICATION_MAP.json'),
  ]);
  assert.equal(REVIEWED.length,108);
  const names=REVIEWED.map(row=>row[0]);
  assert.equal(new Set(names).size,108);
  assert.deepEqual(names,META.milestone.requiredTheorems);
  assert.match(audit,/^import PNP$/mu);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),names);
  for(const module of MODULES)assert.ok(root.split('\n').includes('import '+module),module);
  for(const name of names) {
    assert.equal(probe.split(String.fromCharCode(96)+name+',').length-1,1,name);
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(value=>value===name).length,1,name);
  }
  assert.equal(JSON.parse(pkg).scripts['audit:m270'],META.command);
  assert.ok(surface.includes("'audit:m270': '"+META.command+"'"));
  for(const file of META.testFiles)assert.ok(verifier.includes("'"+file+"'"),file);
  assert.ok(workflow.includes('run: npm run audit:m270'));
  const steps=workflow.split(/^      - name:/mu).filter(step=>
    step.includes('node scripts/check-lean-axioms.mjs '+META.audit));
  assert.equal(steps.length,1);
  const block=steps[0].split('        run: |\n')[1];
  assert.ok(block);
  assert.equal(block.trimEnd().split('\n').map(line=>line.slice(10)).join('\n')+'\n',META.workflowCommands);
  assert.ok(workflow.includes('node --test audits/lean-axiom-transcript0.test.mjs'));
  const map=JSON.parse(mapText),row=map.milestones.find(item=>item.id===META.milestone.id);
  const coordinateGuard=(await text0('formal-publication0.mjs'))
    .match(/if \(map\.coordinate !== '([^']+)'\)/u);
  assert.equal(coordinateGuard?.[1],map.coordinate,'map coordinate guard must precede generated-status validation');
  assert.deepEqual(row,META.milestone);
  for(const [name,hash] of REVIEWED) {
    assert.match(hash,/^[0-9a-f]{64}$/u);
    assert.notEqual(hash,'0'.repeat(64),name);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name],hash,name);
  }
});

test('M270 release: compiled theorem types and exact axiom closures support only reviewed claims',async()=>{
  const {status,inventory,inventoryBytes,map}=await sources0();
  assert.ok(canonical0(inventory).equals(inventoryBytes));
  const publication=DeriveFormalPublication0(inventory,map,inventoryBytes,status.leanSourceClosureSha256);
  const row=publication.milestones.find(item=>item.id===META.milestone.id);
  assert.equal(row?.earned,true);
  for(const field of ['classification','requiredTheorems','scope','nonClaim'])
    assert.deepEqual(row[field],META.milestone[field],field);
  for(const [name,hash,module,axioms] of REVIEWED) {
    for(const collection of [inventory.declarations,inventory.milestoneCandidates]) {
      const found=collection.filter(item=>item.name===name);
      assert.equal(found.length,1,name);
      assert.equal(found[0].kind,'theorem',name);
      assert.equal(found[0].module,module,name);
      assert.deepEqual(found[0].axioms,axioms,name);
    }
    assert.ok(axioms.every(value=>['propext','Quot.sound'].includes(value)),name);
    const candidate=inventory.milestoneCandidates.find(item=>item.name===name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name,candidate.kernelType),hash,name);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name],hash,name);
  }
  for(const [field,value] of Object.entries(META.statusFields))
    assert.deepEqual(status[field],value,field);
});

test('M270 release: weakened types and supplied authority cannot retain earned credit',async()=>{
  const {status,inventory,map}=await sources0();
  const alternatives=new Map();
  for(const [name,hash] of REVIEWED) {
    const current=inventory.milestoneCandidates.find(row=>row.name===name).kernelType;
    const changed=[
      'Lean.Expr.const '+String.fromCharCode(96)+'True []',
      'Lean.Expr.forallE '+String.fromCharCode(96)+'supplied ('+current+') ('+current+') (Lean.BinderInfo.default)',
    ];
    for(const type of changed)assert.notEqual(MilestoneTheoremKernelTypeSha2560(name,type),hash,name);
    alternatives.set(name,changed);
  }
  // Exercise every pin above; serialize the large inventory only for one
  // representative of each affected module and each distinct mutation kind.
  for(const name of new Map(REVIEWED.map(row=>[row[2],row[0]])).values())
    for(const type of alternatives.get(name)) {
      const mutation={...inventory,milestoneCandidates:inventory.milestoneCandidates.map(row=>
        row.name===name?{...row,kernelType:type}:row)};
      const result=DeriveFormalPublication0(mutation,map,canonical0(mutation),status.leanSourceClosureSha256);
      assert.equal(result.milestones.find(row=>row.id===META.milestone.id).earned,false,name);
      assert.equal(result.gate.passed,false);
    }
});

test('M270 release: missing evidence, project axioms and widened scope reject',async()=>{
  const {status,inventory,inventoryBytes,map}=await sources0();
  const name='PNP.DirectWire.StructuralReindexing.literal_replacement_transport';
  const addAuthority=row=>row.name===name?{...row,axioms:['PNP.UnauthorizedAuthority','Quot.sound','propext']}:row;
  const mutation={...inventory,declarations:inventory.declarations.map(addAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(addAuthority)};
  const result=DeriveFormalPublication0(mutation,map,canonical0(mutation),status.leanSourceClosureSha256);
  assert.equal(result.milestones.find(row=>row.id===META.milestone.id).earned,false);
  assert.equal(result.gate.passed,false);
  const missing={...inventory,milestoneCandidates:inventory.milestoneCandidates.filter(row=>row.name!==name)};
  assert.throws(()=>DeriveFormalPublication0(missing,map,canonical0(missing),status.leanSourceClosureSha256),
    /reviewed milestone theorem candidate inventory mismatch/u);
  for(const field of ['scope','nonClaim']) {
    const widened={...map,milestones:map.milestones.map(row=>row.id===META.milestone.id
      ?{...row,[field]:'Every compatible splice is acyclic and the complete manuscript construction is uniformly polynomial.'}:row)};
    assert.throws(()=>DeriveFormalPublication0(inventory,widened,inventoryBytes,status.leanSourceClosureSha256),
      /map drifted from the reviewed specification/u);
  }
  const changedPin={...map,earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256,[name]:'0'.repeat(64)}};
  assert.throws(()=>DeriveFormalPublication0(inventory,changedPin,inventoryBytes,status.leanSourceClosureSha256),
    /map drifted from the reviewed specification/u);
});

test('M270 release: status rejects widened acceptance, full-scope and complexity claims',async()=>{
  const {status}=await sources0();
  for(const suffix of [
    "CompleteReplacementTransportTheorem",
    "AuditedDeclarationCount",
    "AllIndependentBoundaryValuationsCovered",
    "CanonicalPortAndOwnershipBijectionsDerived",
    "BothMatchedSignedSurchargesZero",
    "ExactLocalAndWholeSignedSavingPreserved",
    "BothDependencyAndRejectionDirectionsProved",
    "AcceptedDescendantSpliceRequiredForCompiledPullback",
    "OpenReplacementCompatibilityRequiredForSemantics",
    "CallerSuppliedPredecessorCompilerOrOrderRequired",
    "CallerSuppliedTransportMapsRequired",
    "CallerSuppliedSourceFidelityRequired",
    "PaddingUsed",
    "AllCompatibleSplicesAcyclicProved",
    "ArbitraryPermutationEncodingComplete",
    "FullManuscriptProfileSemanticsProved",
    "AllNormalizationAndMaterializerRulesProved",
    "GlobalCertificateDiscoveryProved",
    "PolynomialRuntimeOutputAndCertificateBoundsProved",
    "Scope"
]) {
    const field='leanStructuralReindexing'+suffix,value=META.statusFields[field];
    assert.notEqual(value,undefined,field);
    const mutation={...status,[field]:typeof value==='boolean'?!value:
      typeof value==='number'?value+1:value+':unreviewed'};
    const result=await CheckFormalReconstructionStatus0({writeOutput:false,statusOverride:mutation,siteOverride:mutation});
    assert.equal(result.tag,'reject',field);
    assert.equal(result.coord,'FormalReconstructionStatus.Field',field);
    assert.deepEqual(result.path,['status/FORMAL_RECONSTRUCTION_STATUS.json',field],field);
  }
});

test('M270 release: structural transport does not earn an unconditional checkpoint',async()=>{
  const {status,inventory,progress}=await sources0();
  assert.equal(validateProofProgress0(progress,status,inventory).tag,'accept');
  const reviews=progress.history.filter(row=>row.asOfCoordinate===META.coordinate);
  assert.equal(reviews.length,1);
  const review=reviews[0];
  assert.equal(review.scoreChanged,false);
  assert.deepEqual(review.changedCheckpointIds,[]);
  assert.deepEqual(review.changeRecords,[]);
  assert.equal(review.riskWeightedProofCompletionPercent,40);
  assert.equal(review.uncertaintyLowPercent,20);
  assert.equal(review.uncertaintyHighPercent,40);
  assert.equal(review.globalGatesClosed,0);
  assert.equal(review.globalGatesAvailable,5);
  assert.ok(prose0(review.rationale).includes('No fixed load-bearing checkpoint changes state'));
  if(progress.asOfCoordinate!==META.coordinate)return;
  assert.deepEqual(review.formalArtefactCoverage,{
    earnedRows:status.formalPublicationMilestones.filter(row=>row.earned).length,
    totalRows:status.formalPublicationMilestones.length,
  });
  assert.deepEqual(progress.tracks.map(track=>track.pointsEarned),[13,20,2,1,4]);
  assert.equal(progress.proofCompletion.percent,40);
  assert.equal(progress.globalGates.length,5);
  assert.ok(progress.globalGates.every(gate=>gate.status==='open'));
  assert.deepEqual(inventory.projectAxioms,[]);
  assert.deepEqual(progress.projectSpecificAxiomsRemaining,[]);
  assert.equal(inventory.declarations.some(row=>row.name==='PNP.Main.p_eq_np'),false);
  assert.equal(status.leanConcreteCNFSATInPFormalized,false);
  assert.equal(status.concretePublicationGate.passed,false);
  assert.equal(progress.publicationGate.passed,false);
  assert.deepEqual(progress.rootTheorem,{name:'PNP.Main.p_eq_np',present:false,built:false,axiomAuditPassed:false});
  const inflated=structuredClone(progress);
  inflated.proofCompletion.pointsEarned+=1;
  inflated.proofCompletion.percent+=1;
  assert.throws(()=>validateProofProgress0(inflated,status,inventory),error=>error.code==='ProofCompletion.StoredEarned');
});

test('M270 release: current documentation separates coverage, estimate and publication decision',async()=>{
  const {progress}=await sources0();
  const doc=prose0(await text0(META.doc)),plan=prose0(await text0(META.plan));
  assert.ok(doc.includes(META.coordinate));
  assert.ok(doc.includes(prose0(META.milestone.scope)));
  assert.ok(doc.includes(prose0(META.milestone.nonClaim)));
  assert.ok(doc.includes(prose0(META.publicationDecision)));
  assert.ok(plan.includes('Publication decision: defer'));
  if(progress.asOfCoordinate!==META.coordinate)return;
  const p=progress.proofCompletion,a=progress.formalArtefactCoverage;
  const metrics=[
    'Formal artefact coverage: '+a.earnedRows+' of '+a.totalRows+' current scoped publication rows earned.',
    'Risk-weighted proof completion estimate: '+p.percent+'%.',
    'Uncertainty range: '+p.uncertaintyLowPercent+'% to '+p.uncertaintyHighPercent+'%.',
    'Global gates closed: '+progress.globalGates.filter(gate=>gate.status==='closed').length+' of 5.',
  ];
  for(const file of ['README.md','docs/FORMAL_RECONSTRUCTION.md','docs/lean_bridge.md',
    'docs/proof_pipeline.md','docs/audit_questions.md','docs/proof_progress.md',META.doc]) {
    const text=await text0(file),current=prose0(text);
    for(const metric of metrics)assert.ok(current.includes(metric),file+': '+metric);
    if(file==='README.md') {
      const rows=text.split('\n');
      const progressRow=rows.find(row=>row.startsWith('| **How is progress measured?** |'));
      assert.ok(progressRow,'README current progress table is present');
      for(const metric of metrics)assert.ok(prose0(progressRow).includes(metric),
        'README current progress table: '+metric);
      const verificationRow=rows.find(row=>row.startsWith('| **What is the current verification status?** |'));
      assert.ok(verificationRow,'README current verification table is present');
      assert.ok(verificationRow.includes('M'+META.coordinate.split('-').at(-1)),
        'README current verification table names the current milestone');
      assert.ok(verificationRow.includes('actual descendant acceptance'));
    }
  }
});
