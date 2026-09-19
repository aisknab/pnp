import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {fileURLToPath} from 'node:url';
import {test} from 'node:test';
import {CheckFormalReconstructionStatus0} from '../pcc-formal-reconstruction-status0.mjs';
import {validateProofProgress0} from '../pcc-proof-progress0.mjs';
import {
  ComputeLeanSourceClosureSha2560, DeriveFormalPublication0,
  MilestoneTheoremKernelTypeSha2560, stableStringify0,
} from '../formal-publication0.mjs';

// Frozen after the explicit-root build and exact compiled axiom audit.
// Runtime tests may not regenerate these pins from their own observed result.
const REVIEWED = [
  [
    "PNP.DirectWire.ComputedWireProfileCost.full_minimum",
    "b52b8497022d4804c1d52f1e43be42a3daf247fac6747a1e6372932478db8c8b",
    "PNP.NANDComputedWireProfileCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ComputedWireProfileCost.minimum_gap",
    "8c138e3dc31739a19207aceca1da03cb668300e13a9f9af1e7d0d07e1d3173a2",
    "PNP.NANDComputedWireProfileCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ComputedWireProfileCost.quotient_minimum",
    "200e81442a22988a98144c8f2f7cc4e6c97e031e7bd5967807ba9d7d6198ee65",
    "PNP.NANDComputedWireProfileCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.erased_constant",
    "c6a041cb0387b83ff67dfae4a5341fdf2a429defe1ec273c1b3e66d9c0452fb5",
    "PNP.NANDFreshFieldCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.erased_count_lower_bound",
    "acc7567090cd30e6f6c7e4eaf70c2dee8850238f39be11aa599f9d85ca79d076",
    "PNP.NANDFreshFieldCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.extend_gateCount",
    "7ba17ec951c7ac5ca2acace870cf5096cb00e45c2a05d674e3441f57eb986719",
    "PNP.NANDFreshFieldExtension",
    []
  ],
  [
    "PNP.DirectWire.FreshNandCost.extended_equivalent",
    "ed3cdf90bdfddc252781d110c336a93bd3740ae147d8b49168615544ca9c4bae",
    "PNP.NANDFreshFieldExtension",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.extended_fresh",
    "a437a65c0fd94dd753eadb24ccddec958a40cc5314cb69eef5a78cac086728cc",
    "PNP.NANDFreshFieldExtension",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.extended_old",
    "6564d883d285624b6a7ad574e689bffa1b2586b2a3ce547edfa3eba0781e7f0b",
    "PNP.NANDFreshFieldExtension",
    []
  ],
  [
    "PNP.DirectWire.FreshNandCost.freshCandidate_semantics",
    "2d4b2ce857b4598392b4f89e572d6f8db577cd84bdb15b58969eade200f8a017",
    "PNP.NANDFreshFieldCost",
    []
  ],
  [
    "PNP.DirectWire.FreshNandCost.freshConditions",
    "b4a431b08524929fda03b7cd1c742e55fb012d34c21031ce1abc62260ca35ef2",
    "PNP.NANDFreshFieldCost",
    []
  ],
  [
    "PNP.DirectWire.FreshNandCost.freshGate_injective",
    "3885732d9169cebcf904a42e0358653fc2d32963d06d5d08617bd2bd173896d8",
    "PNP.NANDFreshFieldCost",
    []
  ],
  [
    "PNP.DirectWire.FreshNandCost.freshGate_selected",
    "5422faadf8e9bfe8c9df7ebbb6216422241bb6682c374f3597d58c6126975811",
    "PNP.NANDFreshFieldCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.freshGate_source",
    "8f0b27868cf4811abeab31661aa5b279bb58431f76eec65b9bafceee80157a38",
    "PNP.NANDFreshFieldCost",
    []
  ],
  [
    "PNP.DirectWire.FreshNandCost.freshGate_value",
    "825e1cd37fb0d50c3ae1e87f1037a546b0654085453b0669498b3a75ca64885b",
    "PNP.NANDFreshFieldCost",
    []
  ],
  [
    "PNP.DirectWire.FreshNandCost.freshValue_joinInput",
    "77177bc59f0356e9d54bad1ae1891e4a6e469875be37ceb0a34fb60f812e5680",
    "PNP.NANDFreshFieldCost",
    []
  ],
  [
    "PNP.DirectWire.FreshNandCost.freshValue_restricted",
    "95f5b81b6c8c3dbe8f70efb50f541172f5a0da6304bcdd24a8906d03f48e3c15",
    "PNP.NANDFreshFieldCost",
    []
  ],
  [
    "PNP.DirectWire.FreshNandCost.gateCount_lower_bound",
    "f1ad49c531301e6a13cc796e8a481add4e7eec14de36c9d4cc048a621267245b",
    "PNP.NANDFreshFieldCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.inputNands_eval",
    "d26026dd26393870d4c796678a56872ca4b0b219d0010fe7548e317ad0a839c3",
    "PNP.NANDFreshFieldExtension",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.oldCandidate_semantics",
    "2f3d44870d6c08335a5c9d775684c40561a1248d36f2d8656fffaa3dd63c686e",
    "PNP.NANDFreshFieldCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.padInputs_semantics",
    "1e461912370c3f90ab89397e2b88b66344cf540042a5e182311781a8af65d961",
    "PNP.NANDFreshFieldProfile",
    []
  ],
  [
    "PNP.DirectWire.FreshNandCost.profile_field",
    "ee6d3fd3233ad2bb36a097a9945e25b5c7dffd8bfc286d594b17b304be05d22e",
    "PNP.NANDFreshFieldProfile",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.profile_fullMinimum",
    "cf93680e838511c7c078fbcaed9b6aeb53867039ab3acf5cda82b0a842f7a60b",
    "PNP.NANDFreshFieldProfile",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.profile_fullSlack",
    "2f64766bc1ccd6954c573e65f1fa1b28e29668f20c5cbd22a3d09c91c714557b",
    "PNP.NANDFreshFieldProfile",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.profile_gateCount",
    "d5f17e98292da1c70e7ddfa2b578981790f1f7072475fbfd59e5bc386e5e3b5b",
    "PNP.NANDFreshFieldProfile",
    []
  ],
  [
    "PNP.DirectWire.FreshNandCost.profile_materializer_charge_lower_bound",
    "bb29f4c44b6ce0ec8e53aa1e460788124c7f593bdbdca8a3c4f658430f6c5488",
    "PNP.NANDFreshFieldProfile",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.profile_output",
    "36c60f9c2f31a5e5375fd200422b46f3c061362bcc257066fba059eac4d1cd9f",
    "PNP.NANDFreshFieldProfile",
    []
  ],
  [
    "PNP.DirectWire.FreshNandCost.profile_projectionDefect",
    "847b187796ec9c30984ff6782e76539de6f0319fda9b41c8fd9261fa82c6e8ef",
    "PNP.NANDFreshFieldProfile",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.profile_quotientMinimum",
    "0c1f3918b7d381d81cc731ea46df8613b55f41dc240348d08d08babb3789881a",
    "PNP.NANDFreshFieldProfile",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.referenceMinimum_extend",
    "b78d74a197672a827d9aa75ba4849a03d75446ca4dec8d2b636180521019062a",
    "PNP.NANDFreshFieldExtension",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.referenceMinimum_padInputs",
    "9170275bafb42cbf8fa6cf58d5af8281dfb8dff62abe7f0eb4c1542083759b7b",
    "PNP.NANDFreshFieldProfile",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.FreshNandCost.restricted_oldInput",
    "6780d73f9bef82748611d3da261775a79b2fa52da0c2dc0a6d60fa5032d3662b",
    "PNP.NANDFreshFieldCost",
    []
  ],
  [
    "PNP.DirectWire.SemanticGateRetraction.gateCount_eq_sub",
    "d27131884b06c36cc340d8a11790af2452b24403b4d022561459ffd7d0565ff0",
    "PNP.NANDSemanticGateRetraction",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.SemanticGateRetraction.gateCount_partition",
    "f450b43aa37fdd27917199c8cefdd3b199d05771d054d0b243a51061788f923b",
    "PNP.NANDSemanticGateRetraction",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.SemanticGateRetraction.kept_gate_value",
    "4db4c08736e999203d9bf231ba6c14687f0ac66872c9e604e16d1c295105feb8",
    "PNP.NANDSemanticGateRetraction",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.SemanticGateRetraction.reboundSource_value",
    "105fbd89ff70d73deabe3a55a25c4aef5637aced180bd1621882f33f9dcbfe86",
    "PNP.NANDSemanticGateRetraction",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.SemanticGateRetraction.semantics",
    "ac67118b00ec5fd47e5c8227fc79e48ec31e4e986eb50156a580101e39d7ae18",
    "PNP.NANDSemanticGateRetraction",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAmbient.available_iff_exists",
    "d7929c5ff6dceb114bbfe3bbdc5f999266bd6853b33b6e94d85f682a25d31956",
    "PNP.NANDWireProfileAmbient",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAmbient.available_pad",
    "58c4f4bdde950973886711ec919effbb063002d9d6222f7e1bfb20aceb9edbfc",
    "PNP.NANDWireProfileAmbient",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAmbient.available_pad_iff",
    "a3408729098856e173a1671061cb59eb83e1830e6ed827161d51e70e80fc81c7",
    "PNP.NANDWireProfileAmbient",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAmbient.available_reword",
    "563a3a7d05874992b7a41cbd28944917374ae7839971bb407d6ca705779c73c4",
    "PNP.NANDWireProfileAmbient",
    []
  ],
  [
    "PNP.DirectWire.WireProfileAmbient.eval_paddedSource",
    "44f649f15ec7a89400d24a6aeed4a7bc90808823a335fc18e8486e2b0d08d3b4",
    "PNP.NANDWireProfileAmbient",
    []
  ],
  [
    "PNP.DirectWire.WireProfileAmbient.eval_retractSource",
    "958eded91369714457e24411bc582cb52985fa788254b86e5a42b8f6d153e02b",
    "PNP.NANDWireProfileAmbient",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAmbient.model_observe_coherent",
    "e883989b1a9ca0205c799b45d8e3f2e9b0d0d2a6ecb15a10800f03aab54fab6d",
    "PNP.NANDWireProfileAmbient",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAmbient.pad_fieldValue",
    "b352f9b13086e15bed18b4f3ec9104e6464263f6ddb96b4d07ec7f556aebdbd9",
    "PNP.NANDWireProfileAmbient",
    []
  ],
  [
    "PNP.DirectWire.WireProfileAmbient.pad_gateCount",
    "619b844fbb3db3b8537685ffb48aae8db008be9c7935de3609135f83b08bb5be",
    "PNP.NANDWireProfileAmbient",
    []
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.available_of_source",
    "0156c31ae5c2b88e8c4c8995d72ca868aaf49a331cf275b3ac29c6c0c9994567",
    "PNP.NANDWireProfileAvailability",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.bind_fieldValue",
    "fc1d8de8f433323969a63570fabaddad9f6a07e8f3c38ef5c6be32e11c0764ba",
    "PNP.NANDWireProfileAvailability",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.bind_full",
    "6222d9745db83ae95ce24b279cd9c75d0e4334e761e7c26b56ebcef736dd94c0",
    "PNP.NANDWireProfileAvailability",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.bind_gateCount",
    "adeca6dea6897cc8c24815ce7b0a6c2f5d49253f2ecfb523782225a21f033db1",
    "PNP.NANDWireProfileAvailability",
    []
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.bind_implementation",
    "5aec5074d1ae9811ef406ebfe65b5a16892a5e737b9eae31117fc02e7a171f25",
    "PNP.NANDWireProfileAvailability",
    []
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.bind_quotient",
    "d9ecb9e8cd6967f4fcdd709207dff17cb28e7a855fe1498a82b50cab110066bd",
    "PNP.NANDWireProfileAvailability",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.current_available",
    "d17af8c16c7f6acc4f185c06197389a9a215166db468fc8e092a360ffe53aebb",
    "PNP.NANDWireProfileAvailability",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.findSource_congr",
    "3ad9d76c26034ee6b7416ec578b7d45afb327ce51f309259489b0a7d049ed1a8",
    "PNP.NANDWireProfileAvailability",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.findSource_sound",
    "8ef5fa5509b46d2b451056e9e5e23f2cfcd11443525951036590bd42fa3007cf",
    "PNP.NANDWireProfileAvailability",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.full_match_iff",
    "2e2ed497ad51ae1af9bf68269e7e5d82ce263e2b9458d7fe88ff162f04e48e98",
    "PNP.NANDWireProfileAvailability",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.full_minimum",
    "d894275b1596e32a841b9edca7a8366d66398516aebf4fa80fa2ff386139c2ee",
    "PNP.NANDWireProfileAvailability",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.quotient_match_iff",
    "ff9e227eb1f99143430fd9829e206ba69202827ea06c08d9a88580def849acf4",
    "PNP.NANDWireProfileAvailability",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.quotient_minimum",
    "2e659a60e2ebf934d5384f8a3ad9ef26c350f92840ee3d8bcb1f67d9578af987",
    "PNP.NANDWireProfileAvailability",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.sourceMatches_congr",
    "407014c882536a90f49d4c5db0b639e9ec7f974bc02229590f3ce54d2aabd351",
    "PNP.NANDWireProfileAvailability",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.sourceMatches_iff",
    "03c35ad97050635551a840a885ac918212a922973ce35989b79c95f8e86bb1ca",
    "PNP.NANDWireProfileAvailability",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.system_congr",
    "d13fbc9331e548e2a1bda401ebd6984de3b395f3a20765457de589213ffdfd2c",
    "PNP.NANDWireProfileAvailability",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileAvailability.system_fullEquivalent",
    "c16848517baf9ededf5937d54cbbcf052de7ac48452a6b4e4c44bb35b0937132",
    "PNP.NANDWireProfileAvailability",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileFieldClosed.ambient_fieldValue",
    "10b95b00b6ab4c76b23c8f165b8891130dfb7f4ed2613e9d0bb282f5f61f8c80",
    "PNP.NANDWireProfileFieldClosed",
    []
  ],
  [
    "PNP.DirectWire.WireProfileFieldClosed.available",
    "c57a279b278e284dc9a085e7f8ba378dfb8e625812e0c2c8e326f4c84448dfab",
    "PNP.NANDWireProfileFieldClosed",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileFieldClosed.boundary_isInput",
    "e5d7b3065a5612cf1f2ad4130f23cdc2d65ca2262dd4cf3e0bf2c8b1acc7fb84",
    "PNP.NANDWireProfileFieldClosed",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileFieldClosed.gate_value",
    "45bf7c61525b1b7f5a5c8ce2fffbdfc6e97aec8dacfbf019c962a2a80052e8e9",
    "PNP.NANDWireProfileFieldClosed",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileFieldClosed.source_selected",
    "fa08a70951298605688abe6dcf162fb1c87e75586092326d5597acc82a922c99",
    "PNP.NANDWireProfileFieldClosed",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.extractTerminalSupport_gate_evaluation",
    "67afb92512e21b56382fc07e40361c3343368d68cff986f44d108aa370cb416c",
    "PNP.ResidualTerminalSupportExtraction",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.extractTerminalSupport_gate_induced",
    "e7585986519237a1ab0fa177facb398a2492d97957998f328089123c6da72e5a",
    "PNP.ResidualTerminalSupportExtraction",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.terminalPhysicalComplementRecords_gateCount_partition",
    "a07ed66527b70b6c939c62e98dbc4779df2062a11b006d376f354ae5ed60257a",
    "PNP.ResidualTerminalSaturatedSupportContext",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.terminalPhysicalComplementRecords_selected",
    "a70e440b1ba6a74878e4d7de1ca00b2b3fedcf55c49853f1b9586bf01dfc84b2",
    "PNP.ResidualTerminalSaturatedSupportContext",
    [
      "Quot.sound",
      "propext"
    ]
  ]
];
const MILESTONE = {
  "classification": "formalized-foundation-only",
  "id": "computed-wire-profile-exact-field-cost",
  "title": "Computed wire-profile models and exact independent-field cost",
  "requiredTheorems": [
    "PNP.DirectWire.ComputedWireProfileCost.full_minimum",
    "PNP.DirectWire.ComputedWireProfileCost.minimum_gap",
    "PNP.DirectWire.ComputedWireProfileCost.quotient_minimum",
    "PNP.DirectWire.FreshNandCost.erased_constant",
    "PNP.DirectWire.FreshNandCost.erased_count_lower_bound",
    "PNP.DirectWire.FreshNandCost.extend_gateCount",
    "PNP.DirectWire.FreshNandCost.extended_equivalent",
    "PNP.DirectWire.FreshNandCost.extended_fresh",
    "PNP.DirectWire.FreshNandCost.extended_old",
    "PNP.DirectWire.FreshNandCost.freshCandidate_semantics",
    "PNP.DirectWire.FreshNandCost.freshConditions",
    "PNP.DirectWire.FreshNandCost.freshGate_injective",
    "PNP.DirectWire.FreshNandCost.freshGate_selected",
    "PNP.DirectWire.FreshNandCost.freshGate_source",
    "PNP.DirectWire.FreshNandCost.freshGate_value",
    "PNP.DirectWire.FreshNandCost.freshValue_joinInput",
    "PNP.DirectWire.FreshNandCost.freshValue_restricted",
    "PNP.DirectWire.FreshNandCost.gateCount_lower_bound",
    "PNP.DirectWire.FreshNandCost.inputNands_eval",
    "PNP.DirectWire.FreshNandCost.oldCandidate_semantics",
    "PNP.DirectWire.FreshNandCost.padInputs_semantics",
    "PNP.DirectWire.FreshNandCost.profile_field",
    "PNP.DirectWire.FreshNandCost.profile_fullMinimum",
    "PNP.DirectWire.FreshNandCost.profile_fullSlack",
    "PNP.DirectWire.FreshNandCost.profile_gateCount",
    "PNP.DirectWire.FreshNandCost.profile_materializer_charge_lower_bound",
    "PNP.DirectWire.FreshNandCost.profile_output",
    "PNP.DirectWire.FreshNandCost.profile_projectionDefect",
    "PNP.DirectWire.FreshNandCost.profile_quotientMinimum",
    "PNP.DirectWire.FreshNandCost.referenceMinimum_extend",
    "PNP.DirectWire.FreshNandCost.referenceMinimum_padInputs",
    "PNP.DirectWire.FreshNandCost.restricted_oldInput",
    "PNP.DirectWire.SemanticGateRetraction.gateCount_eq_sub",
    "PNP.DirectWire.SemanticGateRetraction.gateCount_partition",
    "PNP.DirectWire.SemanticGateRetraction.kept_gate_value",
    "PNP.DirectWire.SemanticGateRetraction.reboundSource_value",
    "PNP.DirectWire.SemanticGateRetraction.semantics",
    "PNP.DirectWire.WireProfileAmbient.available_iff_exists",
    "PNP.DirectWire.WireProfileAmbient.available_pad",
    "PNP.DirectWire.WireProfileAmbient.available_pad_iff",
    "PNP.DirectWire.WireProfileAmbient.available_reword",
    "PNP.DirectWire.WireProfileAmbient.eval_paddedSource",
    "PNP.DirectWire.WireProfileAmbient.eval_retractSource",
    "PNP.DirectWire.WireProfileAmbient.model_observe_coherent",
    "PNP.DirectWire.WireProfileAmbient.pad_fieldValue",
    "PNP.DirectWire.WireProfileAmbient.pad_gateCount",
    "PNP.DirectWire.WireProfileAvailability.available_of_source",
    "PNP.DirectWire.WireProfileAvailability.bind_fieldValue",
    "PNP.DirectWire.WireProfileAvailability.bind_full",
    "PNP.DirectWire.WireProfileAvailability.bind_gateCount",
    "PNP.DirectWire.WireProfileAvailability.bind_implementation",
    "PNP.DirectWire.WireProfileAvailability.bind_quotient",
    "PNP.DirectWire.WireProfileAvailability.current_available",
    "PNP.DirectWire.WireProfileAvailability.findSource_congr",
    "PNP.DirectWire.WireProfileAvailability.findSource_sound",
    "PNP.DirectWire.WireProfileAvailability.full_match_iff",
    "PNP.DirectWire.WireProfileAvailability.full_minimum",
    "PNP.DirectWire.WireProfileAvailability.quotient_match_iff",
    "PNP.DirectWire.WireProfileAvailability.quotient_minimum",
    "PNP.DirectWire.WireProfileAvailability.sourceMatches_congr",
    "PNP.DirectWire.WireProfileAvailability.sourceMatches_iff",
    "PNP.DirectWire.WireProfileAvailability.system_congr",
    "PNP.DirectWire.WireProfileAvailability.system_fullEquivalent",
    "PNP.DirectWire.WireProfileFieldClosed.ambient_fieldValue",
    "PNP.DirectWire.WireProfileFieldClosed.available",
    "PNP.DirectWire.WireProfileFieldClosed.boundary_isInput",
    "PNP.DirectWire.WireProfileFieldClosed.gate_value",
    "PNP.DirectWire.WireProfileFieldClosed.source_selected",
    "PNP.DirectWire.extractTerminalSupport_gate_evaluation",
    "PNP.DirectWire.extractTerminalSupport_gate_induced",
    "PNP.DirectWire.terminalPhysicalComplementRecords_gateCount_partition",
    "PNP.DirectWire.terminalPhysicalComplementRecords_selected"
  ],
  "scope": "For arbitrary finite input, ordinary-output and computational-field widths, target-relative availability computes one actual constant, input or gate source that realizes a field uniformly over every input valuation. Rebinding constructs a carrier without adding gates and identifies terminal full and quotient profile minima with the corresponding wire-profile minima. The model constructor proves coherence between its base and ambient observers under unused-input padding and output rewording. A source-derived field seed and physical dependency closure yield an actual extracted support preserving every field at all ambient input valuations. For any old implementation with semantic minimum F and any natural width k, an explicit extension appends k independent NAND fields on disjoint fresh input pairs. Semantic gate retraction proves that every equivalent implementation needs at least F + k gates; the matching construction attains that bound. Its actual wire profile therefore has full minimum F + k, all-forgotten quotient minimum F, projection defect k and unchanged full slack. Three general coupling theorems establish these same exact minima and their difference inside the constructed terminal profile model, without a supplied model, minimum, field support or correctness certificate.",
  "nonClaim": "This is a computed model for actual computational wire fields, not the complete manuscript profile grammar or a terminal-derived governed family. The extracted support is field-preserving but is not asserted to be proper, smaller or optimal. The exact additive cost theorem concerns the explicit independent fresh-input NAND family, not arbitrary correlated, duplicated or supplied manuscript fields. The semantic retraction helper has an explicit uniform constant-value hypothesis, discharged for that family; it is not a general polynomial semantic-constant detector. The existing shared materializer charge is only bounded below by the family's projection defect, not proved equal to it. Availability checks enumerate valuations and reference minima remain exhaustive; no complete polynomial minimizer follows. Complete Package E, global route coverage and rank decrease, unconditional SaturatePositive, BCELReady and ZeroSlack, exact polynomial PCCMin, encoded runtime, output and certificate bounds, deterministic CNFSAT in P and the eligible root remain open. No fixed weighted checkpoint or global proof gate closes, and P = NP is not proved."
};
const canonical0 = value => Buffer.from(stableStringify0(value) + '\n');
const text0 = file => readFile(new URL('../' + file, import.meta.url), 'utf8');
let loaded;
function sources0() {
  loaded ??= Promise.all([
    text0('status/LEAN_THEOREM_INVENTORY.json'),
    text0('publication/FORMAL_PUBLICATION_MAP.json'),
  ]).then(async ([inventoryText, mapText]) => {
    const inventory = JSON.parse(inventoryText), map = JSON.parse(mapText);
    const sourceClosure = await ComputeLeanSourceClosureSha2560(
      fileURLToPath(new URL('..', import.meta.url)), inventory);
    return {inventory, map, inventoryBytes: Buffer.from(inventoryText), sourceClosure};
  });
  return loaded;
}

test('M276 compiled interface: exact types, modules and axiom closures earn only the reviewed row', async () => {
  const {inventory, map, inventoryBytes, sourceClosure} = await sources0();
  assert.ok(canonical0(inventory).equals(inventoryBytes));
  const names = REVIEWED.map(row => row[0]);
  assert.equal(names.length, 72);
  assert.equal(new Set(names).size, names.length);
  assert.deepEqual(names, MILESTONE.requiredTheorems);
  assert.deepEqual(map.milestones.find(row => row.id === MILESTONE.id), MILESTONE);
  assert.equal(sourceClosure, map.milestoneSourceClosureSha256);
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes, sourceClosure);
  const row = publication.milestones.find(item => item.id === MILESTONE.id);
  assert.equal(row?.earned, true);
  assert.equal(row.classification, 'formalized-foundation-only');
  assert.equal(publication.gate.passed, false);
  for (const [name, hash, module, axioms] of REVIEWED) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const found = collection.filter(item => item.name === name);
      assert.equal(found.length, 1, name);
      assert.equal(found[0].kind, 'theorem', name);
      assert.equal(found[0].module, module, name);
      assert.deepEqual(found[0].axioms, axioms, name);
    }
    assert.ok(axioms.every(value => ['propext', 'Quot.sound'].includes(value)), name);
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), hash, name);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], hash, name);
  }
});

test('M276 compiled interface: weakening or supplying a conclusion cannot retain credit', async () => {
  const {inventory, map, sourceClosure} = await sources0();
  const alternatives = new Map();
  for (const [name, hash] of REVIEWED) {
    const current = inventory.milestoneCandidates.find(row => row.name === name).kernelType;
    const changed = [
      'Lean.Expr.const ' + String.fromCharCode(96) + 'True []',
      'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + current + ') (' + current + ') (Lean.BinderInfo.default)',
    ];
    for (const type of changed) assert.notEqual(MilestoneTheoremKernelTypeSha2560(name, type), hash, name);
    alternatives.set(name, changed);
  }
  // Check every pin cheaply above; exercise the large publication boundary at
  // the computed model bridge, exact independent-field minimum and their coupling.
  for (const name of [
    'PNP.DirectWire.WireProfileAvailability.full_minimum',
    'PNP.DirectWire.FreshNandCost.referenceMinimum_extend',
    'PNP.DirectWire.ComputedWireProfileCost.minimum_gap',
  ]) for (const kernelType of alternatives.get(name)) {
    const mutation = {...inventory, milestoneCandidates: inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), sourceClosure);
    assert.equal(result.milestones.find(row => row.id === MILESTONE.id).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
});

test('M276 compiled interface: missing evidence, added authority and widened scope reject', async () => {
  const {inventory, inventoryBytes, map, sourceClosure} = await sources0();
  const name = 'PNP.DirectWire.FreshNandCost.referenceMinimum_extend';
  const addAuthority = row => row.name === name
    ? {...row, axioms: ['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const mutation = {...inventory, declarations: inventory.declarations.map(addAuthority),
    milestoneCandidates: inventory.milestoneCandidates.map(addAuthority)};
  const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), sourceClosure);
  assert.equal(result.milestones.find(row => row.id === MILESTONE.id).earned, false);
  assert.equal(result.gate.passed, false);
  const missing = {...inventory, milestoneCandidates: inventory.milestoneCandidates.filter(row => row.name !== name)};
  assert.throws(() => DeriveFormalPublication0(missing, map, canonical0(missing), sourceClosure),
    /reviewed milestone theorem candidate inventory mismatch/u);
  for (const field of ['scope', 'nonClaim']) {
    const widened = {...map, milestones: map.milestones.map(row => row.id === MILESTONE.id
      ? {...row, [field]: 'Computed profiles for arbitrary manuscript fields yield a polynomial exact minimizer and unconditional global ZeroSlack.'} : row)};
    assert.throws(() => DeriveFormalPublication0(inventory, widened, inventoryBytes, sourceClosure),
      /map drifted from the reviewed specification/u);
  }
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256: {
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]: '0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, inventoryBytes, sourceClosure),
    /map drifted from the reviewed specification/u);
});

const META = {
  "coordinate": "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-19-276",
  "id": "computed-wire-profile-exact-field-cost",
  "title": "Computed wire-profile models and exact independent-field cost",
  "classification": "formalized-foundation-only",
  "scope": "For arbitrary finite input, ordinary-output and computational-field widths, target-relative availability computes one actual constant, input or gate source that realizes a field uniformly over every input valuation. Rebinding constructs a carrier without adding gates and identifies terminal full and quotient profile minima with the corresponding wire-profile minima. The model constructor proves coherence between its base and ambient observers under unused-input padding and output rewording. A source-derived field seed and physical dependency closure yield an actual extracted support preserving every field at all ambient input valuations. For any old implementation with semantic minimum F and any natural width k, an explicit extension appends k independent NAND fields on disjoint fresh input pairs. Semantic gate retraction proves that every equivalent implementation needs at least F + k gates; the matching construction attains that bound. Its actual wire profile therefore has full minimum F + k, all-forgotten quotient minimum F, projection defect k and unchanged full slack. Three general coupling theorems establish these same exact minima and their difference inside the constructed terminal profile model, without a supplied model, minimum, field support or correctness certificate.",
  "nonClaim": "This is a computed model for actual computational wire fields, not the complete manuscript profile grammar or a terminal-derived governed family. The extracted support is field-preserving but is not asserted to be proper, smaller or optimal. The exact additive cost theorem concerns the explicit independent fresh-input NAND family, not arbitrary correlated, duplicated or supplied manuscript fields. The semantic retraction helper has an explicit uniform constant-value hypothesis, discharged for that family; it is not a general polynomial semantic-constant detector. The existing shared materializer charge is only bounded below by the family's projection defect, not proved equal to it. Availability checks enumerate valuations and reference minima remain exhaustive; no complete polynomial minimizer follows. Complete Package E, global route coverage and rank decrease, unconditional SaturatePositive, BCELReady and ZeroSlack, exact polynomial PCCMin, encoded runtime, output and certificate bounds, deterministic CNFSAT in P and the eligible root remain open. No fixed weighted checkpoint or global proof gate closes, and P = NP is not proved.",
  "doc": "docs/lean_computed_wire_profile.md",
  "plan": "docs/plans/2026-09-19-computed-wire-profile-exact-field-cost.md",
  "publicationDecision": "Publication decision: defer. This supplies a computed computational-profile model and exact costs for an explicit independent-field family, not the complete manuscript profile grammar, terminal-derived families, complete Package E or global route coverage. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.",
  "rationale": "M276 combines the source-derived computational-profile model with an exact independent-field cost family, then proves their general coupling. One uniformly valid actual source is computed for each available field; arbitrary input padding and output rewording preserve the observer, and actual field seeds derive a preserving support. A semantic gate-retraction argument and matching extension prove the exact additional cost for arbitrary old implementations and arbitrary widths of independent fresh NAND fields. This retires those bounded model and cost interfaces, not arbitrary manuscript-field transparency, proper-support discovery, terminal-family derivation, global routing or polynomial minimization. The two prepared components are integrated and reviewed as one milestone rather than separate release cycles. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.",
  "statusFields": {
    "leanComputedWireProfileFormalized": true,
    "leanComputedWireProfileAxiomAuditPassed": true,
    "leanComputedWireProfileAuditedDeclarationCount": 72,
    "leanComputedWireProfileUniformSourceTheorem": "PNP.DirectWire.WireProfileAvailability.sourceMatches_iff",
    "leanComputedWireProfileFullMinimumBridgeTheorem": "PNP.DirectWire.WireProfileAvailability.full_minimum",
    "leanComputedWireProfileQuotientMinimumBridgeTheorem": "PNP.DirectWire.WireProfileAvailability.quotient_minimum",
    "leanComputedWireProfileAmbientCoherenceTheorem": "PNP.DirectWire.WireProfileAmbient.model_observe_coherent",
    "leanComputedWireProfileDerivedFieldSupportTheorem": "PNP.DirectWire.WireProfileFieldClosed.available",
    "leanComputedWireProfileSemanticRetractionTheorem": "PNP.DirectWire.SemanticGateRetraction.semantics",
    "leanComputedWireProfileIndependentFieldLowerBoundTheorem": "PNP.DirectWire.FreshNandCost.gateCount_lower_bound",
    "leanComputedWireProfileIndependentFieldMinimumTheorem": "PNP.DirectWire.FreshNandCost.referenceMinimum_extend",
    "leanComputedWireProfileCoupledFullMinimumTheorem": "PNP.DirectWire.ComputedWireProfileCost.full_minimum",
    "leanComputedWireProfileCoupledQuotientMinimumTheorem": "PNP.DirectWire.ComputedWireProfileCost.quotient_minimum",
    "leanComputedWireProfileCoupledMinimumGapTheorem": "PNP.DirectWire.ComputedWireProfileCost.minimum_gap",
    "leanComputedWireProfileArbitraryFiniteDimensionsCovered": true,
    "leanComputedWireProfileOneSourceUniformAcrossAllValuationsRequired": true,
    "leanComputedWireProfileModelAndFieldPreservingSupportComputed": true,
    "leanComputedWireProfileObserverPaddingAndRewordingCoherenceProved": true,
    "leanComputedWireProfileExactCostForArbitraryIndependentFreshFieldWidthsProved": true,
    "leanComputedWireProfileCallerSuppliedModelMinimumSupportOrCorrectnessRequired": false,
    "leanComputedWireProfileSemanticRetractionHasExplicitUniformConstantHypothesis": true,
    "leanComputedWireProfileRetractionHypothesisDischargedForIndependentFieldFamily": true,
    "leanComputedWireProfileExtractedSupportIsProperSmallerOrOptimalProved": false,
    "leanComputedWireProfileArbitraryManuscriptFieldAdditivityProved": false,
    "leanComputedWireProfileSharedMaterializerChargeEqualsProjectionDefectProved": false,
    "leanComputedWireProfileCompleteManuscriptProfileGrammarProved": false,
    "leanComputedWireProfileTerminalFamiliesDerived": false,
    "leanComputedWireProfileCompletePackageEOrGlobalRoutesProved": false,
    "leanComputedWireProfileUnconditionalSaturatePositiveProved": false,
    "leanComputedWireProfileUnconditionalBCELReadyProved": false,
    "leanComputedWireProfileUnconditionalZeroSlackProved": false,
    "leanComputedWireProfileExactPolynomialPCCMinProved": false,
    "leanComputedWireProfilePolynomialRuntimeOutputAndCertificateBoundsProved": false,
    "leanComputedWireProfileAvailabilityAndReferenceMinimizationAreExhaustive": true,
    "leanComputedWireProfileRuntimeExecutionIsProofAuthority": false,
    "leanComputedWireProfileScope": "arbitrary-finite-computed-uniform-wire-availability-ambient-observer-coherence-source-derived-field-preserving-support-exact-independent-fresh-nand-cost-and-terminal-model-coupling-no-arbitrary-field-additivity-global-route-or-polynomial-claim"
  },
  "milestone": {
    "classification": "formalized-foundation-only",
    "id": "computed-wire-profile-exact-field-cost",
    "title": "Computed wire-profile models and exact independent-field cost",
    "requiredTheorems": [
      "PNP.DirectWire.ComputedWireProfileCost.full_minimum",
      "PNP.DirectWire.ComputedWireProfileCost.minimum_gap",
      "PNP.DirectWire.ComputedWireProfileCost.quotient_minimum",
      "PNP.DirectWire.FreshNandCost.erased_constant",
      "PNP.DirectWire.FreshNandCost.erased_count_lower_bound",
      "PNP.DirectWire.FreshNandCost.extend_gateCount",
      "PNP.DirectWire.FreshNandCost.extended_equivalent",
      "PNP.DirectWire.FreshNandCost.extended_fresh",
      "PNP.DirectWire.FreshNandCost.extended_old",
      "PNP.DirectWire.FreshNandCost.freshCandidate_semantics",
      "PNP.DirectWire.FreshNandCost.freshConditions",
      "PNP.DirectWire.FreshNandCost.freshGate_injective",
      "PNP.DirectWire.FreshNandCost.freshGate_selected",
      "PNP.DirectWire.FreshNandCost.freshGate_source",
      "PNP.DirectWire.FreshNandCost.freshGate_value",
      "PNP.DirectWire.FreshNandCost.freshValue_joinInput",
      "PNP.DirectWire.FreshNandCost.freshValue_restricted",
      "PNP.DirectWire.FreshNandCost.gateCount_lower_bound",
      "PNP.DirectWire.FreshNandCost.inputNands_eval",
      "PNP.DirectWire.FreshNandCost.oldCandidate_semantics",
      "PNP.DirectWire.FreshNandCost.padInputs_semantics",
      "PNP.DirectWire.FreshNandCost.profile_field",
      "PNP.DirectWire.FreshNandCost.profile_fullMinimum",
      "PNP.DirectWire.FreshNandCost.profile_fullSlack",
      "PNP.DirectWire.FreshNandCost.profile_gateCount",
      "PNP.DirectWire.FreshNandCost.profile_materializer_charge_lower_bound",
      "PNP.DirectWire.FreshNandCost.profile_output",
      "PNP.DirectWire.FreshNandCost.profile_projectionDefect",
      "PNP.DirectWire.FreshNandCost.profile_quotientMinimum",
      "PNP.DirectWire.FreshNandCost.referenceMinimum_extend",
      "PNP.DirectWire.FreshNandCost.referenceMinimum_padInputs",
      "PNP.DirectWire.FreshNandCost.restricted_oldInput",
      "PNP.DirectWire.SemanticGateRetraction.gateCount_eq_sub",
      "PNP.DirectWire.SemanticGateRetraction.gateCount_partition",
      "PNP.DirectWire.SemanticGateRetraction.kept_gate_value",
      "PNP.DirectWire.SemanticGateRetraction.reboundSource_value",
      "PNP.DirectWire.SemanticGateRetraction.semantics",
      "PNP.DirectWire.WireProfileAmbient.available_iff_exists",
      "PNP.DirectWire.WireProfileAmbient.available_pad",
      "PNP.DirectWire.WireProfileAmbient.available_pad_iff",
      "PNP.DirectWire.WireProfileAmbient.available_reword",
      "PNP.DirectWire.WireProfileAmbient.eval_paddedSource",
      "PNP.DirectWire.WireProfileAmbient.eval_retractSource",
      "PNP.DirectWire.WireProfileAmbient.model_observe_coherent",
      "PNP.DirectWire.WireProfileAmbient.pad_fieldValue",
      "PNP.DirectWire.WireProfileAmbient.pad_gateCount",
      "PNP.DirectWire.WireProfileAvailability.available_of_source",
      "PNP.DirectWire.WireProfileAvailability.bind_fieldValue",
      "PNP.DirectWire.WireProfileAvailability.bind_full",
      "PNP.DirectWire.WireProfileAvailability.bind_gateCount",
      "PNP.DirectWire.WireProfileAvailability.bind_implementation",
      "PNP.DirectWire.WireProfileAvailability.bind_quotient",
      "PNP.DirectWire.WireProfileAvailability.current_available",
      "PNP.DirectWire.WireProfileAvailability.findSource_congr",
      "PNP.DirectWire.WireProfileAvailability.findSource_sound",
      "PNP.DirectWire.WireProfileAvailability.full_match_iff",
      "PNP.DirectWire.WireProfileAvailability.full_minimum",
      "PNP.DirectWire.WireProfileAvailability.quotient_match_iff",
      "PNP.DirectWire.WireProfileAvailability.quotient_minimum",
      "PNP.DirectWire.WireProfileAvailability.sourceMatches_congr",
      "PNP.DirectWire.WireProfileAvailability.sourceMatches_iff",
      "PNP.DirectWire.WireProfileAvailability.system_congr",
      "PNP.DirectWire.WireProfileAvailability.system_fullEquivalent",
      "PNP.DirectWire.WireProfileFieldClosed.ambient_fieldValue",
      "PNP.DirectWire.WireProfileFieldClosed.available",
      "PNP.DirectWire.WireProfileFieldClosed.boundary_isInput",
      "PNP.DirectWire.WireProfileFieldClosed.gate_value",
      "PNP.DirectWire.WireProfileFieldClosed.source_selected",
      "PNP.DirectWire.extractTerminalSupport_gate_evaluation",
      "PNP.DirectWire.extractTerminalSupport_gate_induced",
      "PNP.DirectWire.terminalPhysicalComplementRecords_gateCount_partition",
      "PNP.DirectWire.terminalPhysicalComplementRecords_selected"
    ],
    "scope": "For arbitrary finite input, ordinary-output and computational-field widths, target-relative availability computes one actual constant, input or gate source that realizes a field uniformly over every input valuation. Rebinding constructs a carrier without adding gates and identifies terminal full and quotient profile minima with the corresponding wire-profile minima. The model constructor proves coherence between its base and ambient observers under unused-input padding and output rewording. A source-derived field seed and physical dependency closure yield an actual extracted support preserving every field at all ambient input valuations. For any old implementation with semantic minimum F and any natural width k, an explicit extension appends k independent NAND fields on disjoint fresh input pairs. Semantic gate retraction proves that every equivalent implementation needs at least F + k gates; the matching construction attains that bound. Its actual wire profile therefore has full minimum F + k, all-forgotten quotient minimum F, projection defect k and unchanged full slack. Three general coupling theorems establish these same exact minima and their difference inside the constructed terminal profile model, without a supplied model, minimum, field support or correctness certificate.",
    "nonClaim": "This is a computed model for actual computational wire fields, not the complete manuscript profile grammar or a terminal-derived governed family. The extracted support is field-preserving but is not asserted to be proper, smaller or optimal. The exact additive cost theorem concerns the explicit independent fresh-input NAND family, not arbitrary correlated, duplicated or supplied manuscript fields. The semantic retraction helper has an explicit uniform constant-value hypothesis, discharged for that family; it is not a general polynomial semantic-constant detector. The existing shared materializer charge is only bounded below by the family's projection defect, not proved equal to it. Availability checks enumerate valuations and reference minima remain exhaustive; no complete polynomial minimizer follows. Complete Package E, global route coverage and rank decrease, unconditional SaturatePositive, BCELReady and ZeroSlack, exact polynomial PCCMin, encoded runtime, output and certificate bounds, deterministic CNFSAT in P and the eligible root remain open. No fixed weighted checkpoint or global proof gate closes, and P = NP is not proved."
  },
  "audit": "lean-audit/PNPComputedWireProfileAxiomAudit.lean",
  "command": "node --test audits/lean-computed-wire-profile0.test.mjs audits/lean-computed-wire-profile-publication0.test.mjs",
  "testFiles": [
    "audits/lean-computed-wire-profile0.test.mjs",
    "audits/lean-computed-wire-profile-publication0.test.mjs"
  ],
  "regressionCommands": [
    "lake env lean -DwarningAsError=true --run lean-regression/PNPWireProfileAvailability.lean",
    "lake env lean -DwarningAsError=true lean-regression/PNPWireProfileObserverBoundary.lean",
    "lake env lean -DwarningAsError=true --run lean-regression/PNPWireProfileAmbient.lean",
    "lake env lean -DwarningAsError=true --run lean-regression/PNPWireProfileFieldClosed.lean",
    "lake env lean -DwarningAsError=true --run lean-regression/PNPSemanticGateRetraction.lean",
    "lake env lean -DwarningAsError=true --run lean-regression/PNPFreshFieldCost.lean",
    "lake env lean -DwarningAsError=true --run lean-regression/PNPFreshFieldProfile.lean",
    "lake env lean -DwarningAsError=true lean-regression/PNPComputedWireProfileCost.lean"
  ],
  "workflowCommands": "set -euo pipefail\nnode scripts/check-lean-axioms.mjs lean-audit/PNPComputedWireProfileAxiomAudit.lean\nlake env lean -DwarningAsError=true --run lean-regression/PNPWireProfileAvailability.lean\nlake env lean -DwarningAsError=true lean-regression/PNPWireProfileObserverBoundary.lean\nlake env lean -DwarningAsError=true --run lean-regression/PNPWireProfileAmbient.lean\nlake env lean -DwarningAsError=true --run lean-regression/PNPWireProfileFieldClosed.lean\nlake env lean -DwarningAsError=true --run lean-regression/PNPSemanticGateRetraction.lean\nlake env lean -DwarningAsError=true --run lean-regression/PNPFreshFieldCost.lean\nlake env lean -DwarningAsError=true --run lean-regression/PNPFreshFieldProfile.lean\nlake env lean -DwarningAsError=true lean-regression/PNPComputedWireProfileCost.lean\n"
};
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();
async function release0() {
  const [statusText, progressText] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('status/PROOF_PROGRESS.json'),
  ]);
  return {status: JSON.parse(statusText), progress: JSON.parse(progressText)};
}

test('M276 release preflight: package, exact workflow and status commands share one interface', async () => {
  const [pkg, surface, verifier, workflow, statusSource, statusText] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'), text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'), text0('pcc-formal-reconstruction-status0.mjs'),
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  ]);
  assert.equal(JSON.parse(pkg).scripts['audit:m276'], META.command);
  assert.ok(surface.includes("'audit:m276': '" + META.command + "'"));
  for (const file of META.testFiles) assert.ok(verifier.includes("'" + file + "'"), file);
  assert.ok(workflow.includes('run: npm run audit:m276'));
  const steps = workflow.split(/^      - name:/mu).filter(step =>
    step.includes('node scripts/check-lean-axioms.mjs ' + META.audit));
  assert.equal(steps.length, 1);
  const block = steps[0].split('        run: |\n')[1];
  assert.ok(block);
  assert.equal(block.trimEnd().split('\n').map(line => line.slice(10)).join('\n') + '\n', META.workflowCommands);
  const status = JSON.parse(statusText);
  for (const command of [
    'npm run audit:m276', 'node scripts/check-lean-axioms.mjs ' + META.audit,
    ...META.regressionCommands,
  ]) assert.ok(status.verificationCommands.includes(command), command);
  for (const field of Object.keys(META.statusFields))
    assert.equal(statusSource.split(field + ':').length - 1, 2, field);
});

test('M276 release: status pins the exact bounded claims and rejects every changed field', async () => {
  const {status} = await release0();
  for (const [field, value] of Object.entries(META.statusFields)) {
    assert.deepEqual(status[field], value, field);
    const mutation = {...status, [field]: typeof value === 'boolean' ? !value :
      typeof value === 'number' ? value + 1 : value + ':unreviewed'};
    const result = await CheckFormalReconstructionStatus0({writeOutput: false, statusOverride: mutation, siteOverride: mutation});
    assert.equal(result.tag, 'reject', field);
    assert.equal(result.coord, 'FormalReconstructionStatus.Field', field);
    assert.deepEqual(result.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
  }
});

test('M276 release: computed independent-field compatibility earns no unconditional checkpoint', async () => {
  const {status, progress} = await release0(), {inventory} = await sources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const reviews = progress.history.filter(row => row.asOfCoordinate === META.coordinate);
  assert.equal(reviews.length, 1);
  const review = reviews[0];
  assert.equal(review.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  assert.equal(review.globalGatesAvailable, 5);
  assert.ok(prose0(review.rationale).includes('No fixed load-bearing checkpoint changes state'));
  if (progress.asOfCoordinate !== META.coordinate) return;
  assert.deepEqual(review.formalArtefactCoverage, {
    earnedRows: status.formalPublicationMilestones.filter(row => row.earned).length,
    totalRows: status.formalPublicationMilestones.length,
  });
  assert.deepEqual(progress.tracks.map(track => track.pointsEarned), [13, 20, 2, 1, 4]);
  assert.equal(progress.proofCompletion.percent, 40);
  assert.equal(progress.globalGates.length, 5);
  assert.ok(progress.globalGates.every(gate => gate.status === 'open'));
  assert.deepEqual(inventory.projectAxioms, []);
  assert.deepEqual(progress.projectSpecificAxiomsRemaining, []);
  assert.equal(inventory.declarations.some(row => row.name === 'PNP.Main.p_eq_np'), false);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.equal(progress.publicationGate.passed, false);
  assert.deepEqual(progress.rootTheorem, {name: 'PNP.Main.p_eq_np', present: false, built: false, axiomAuditPassed: false});
  const inflated = structuredClone(progress);
  inflated.proofCompletion.pointsEarned += 1;
  inflated.proofCompletion.percent += 1;
  assert.throws(() => validateProofProgress0(inflated, status, inventory),
    error => error.code === 'ProofCompletion.StoredEarned');
});

test('M276 release: every current summary and FAQ uses the canonical independent metrics', async () => {
  const {progress} = await release0();
  const doc = prose0(await text0(META.doc)), plan = prose0(await text0(META.plan));
  assert.ok(doc.includes(META.coordinate));
  assert.ok(doc.includes(prose0(MILESTONE.scope)));
  assert.ok(doc.includes(prose0(MILESTONE.nonClaim)));
  assert.ok(doc.includes(prose0(META.publicationDecision)));
  assert.ok(plan.includes('Publication decision: defer'));
  if (progress.asOfCoordinate !== META.coordinate) return;
  const p = progress.proofCompletion, a = progress.formalArtefactCoverage;
  const metrics = [
    'Formal artefact coverage: ' + a.earnedRows + ' of ' + a.totalRows + ' current scoped publication rows earned.',
    'Risk-weighted proof completion estimate: ' + p.percent + '%.',
    'Uncertainty range: ' + p.uncertaintyLowPercent + '% to ' + p.uncertaintyHighPercent + '%.',
    'Global gates closed: ' + progress.globalGates.filter(gate => gate.status === 'closed').length + ' of 5.',
  ];
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md', META.doc]) {
    const text = await text0(file), current = prose0(text);
    for (const metric of metrics) assert.ok(current.includes(metric), file + ': ' + metric);
    if (file === 'docs/proof_progress.md') {
      const currentIntro = prose0(text.split('## Risk-weighted proof completion estimate')[0]);
      for (const metric of metrics) assert.ok(currentIntro.includes(metric), file + ': current introduction ' + metric);
      assert.ok(currentIntro.includes(META.coordinate));
    }
    if (file === 'README.md') {
      const row = text.split('\n').find(line => line.startsWith('| **How is progress measured?** |'));
      assert.ok(row);
      for (const metric of metrics) assert.ok(prose0(row).includes(metric), 'FAQ: ' + metric);
      const boundary = text.split('\n').find(line => line.startsWith('| **What is the current verification status?** |'));
      assert.ok(boundary?.includes('M276'));
      assert.ok(boundary.includes('global route coverage'));
    }
    if (['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
      'docs/proof_pipeline.md', 'docs/audit_questions.md'].includes(file)) {
      const region = text.split('<!-- M276-CURRENT-SUMMARY:BEGIN -->')[1]?.split('<!-- M276-CURRENT-SUMMARY:END -->')[0];
      assert.ok(region, file + ': current summary');
      for (const metric of metrics) assert.ok(prose0(region).includes(metric), file + ': summary ' + metric);
      assert.doesNotMatch(region, /\d+[ -]pages?|PDF[^\n]*page count/iu);
    }
  }
  const report = await text0('canonical_proof_report.tex');
  const cover = prose0(report.split('\\end{titlepage}')[0]);
  assert.doesNotMatch(cover, /Latest earned evidence:/u);
  assert.ok(cover.includes('Formal artefact coverage: ' + a.earnedRows + ' of ' + a.totalRows));
  assert.ok(cover.includes('Risk-weighted proof completion estimate: ' + p.percent + ' percent.'));
});
