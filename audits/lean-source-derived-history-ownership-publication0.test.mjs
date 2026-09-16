import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  DeriveFormalPublication0, MilestoneTheoremKernelTypeSha2560, stableStringify0, REQUIRED_MILESTONE_THEOREMS0,
} from '../formal-publication0.mjs';
import {CheckFormalReconstructionStatus0} from '../pcc-formal-reconstruction-status0.mjs';
import {validateProofProgress0} from '../pcc-proof-progress0.mjs';

// These frozen type fingerprints and exact axiom closures were reviewed against
// the compiled M266 dependency closure; the explicit-root audit must agree. Tests must not regenerate their own expectations.
const REVIEWED = [
  [
    "PNP.DirectWire.PhysicalGateProvenance.constantOrigins_positions",
    "14202cb776a0455c81fcba3d15fea773506814911656848a6cc8636189e749d1",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.sharingOrigins_positions",
    "60f68297d2d2a96a4360598a88c458f8e86b23f670c78258abb0f85727446b50",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.constantOrigin_alias",
    "ce323ad0fc1ce93cc3535dcd40d83378d998210dec0eec0cf3e4ee2d51d5f102",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.constantOrigin_injective",
    "cb2bf5bfb8f7cccda8ee66ee5639fe74778ee3f9952af0065b9be0ce712cb86b",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.sharingOrigin_alias",
    "f4de2ba242509a73f549d1a6b3a6767c8cd574e25ff544ccee2c4dbafcb90756",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.sharingOrigin_injective",
    "6e84cf7a936dc3bd08a2daedcbe0cffe5a3ba43e2cfb82f0e805b9ad83a21a6d",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.terminalExtractionOrigin_selected",
    "839fde82c63708bf97d462e79abe862e52c5ae551a65b697c7dd992dc083879f",
    "PNP.ResidualTerminalSupportExtraction",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.terminalExtractionGateIndex_origin",
    "fed7cf03f9dd9ad13a924cdb9d5fe5398186ac89b377ce95980bb9306ab72d5f",
    "PNP.ResidualTerminalSupportExtraction",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.terminalExtractionOrigin_gateIndex",
    "3bb4a9dabdb287a3ebbd786c2e776f052eb1e32c3515a249d1b21bd2bf268970",
    "PNP.ResidualTerminalSupportExtraction",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.terminalExtractionOrigin_injective",
    "a021628c5016dfaca32528378af5b64ebdf2c5827b930d60f050b545ced48291",
    "PNP.ResidualTerminalSupportExtraction",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.coneOrigin_selected",
    "d1dd2a206525ba86886b904026e84b0e2e575b07838a5aa1e045ea373636a45c",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.coneOrigin_position",
    "353b4b4a6af3c9ac90d65d085709bf22832664df2705a9c855624fc168ca4714",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.coneOrigin_injective",
    "6dcab94ea386cd755e5b09e00afff57ebda0849ff4ca0d8ba00fc419034400cf",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.coneOrigin_image",
    "732d80b8c647b23629e4a15c40cba9b2eee8b7324932d67636116f919215cc7b",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.passOrigin_injective",
    "66a710bb11e3c2683bff24e48750eefbddf5c9fd4bbc35a3bbc97cd3e2f070e4",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.traceOrigin_injective",
    "f565982503263918e495a550d3975589e1c4913427ef318f4243838ebe698450",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.normalizedOrigin_injective",
    "9ea63eb2862976756911032e5c7e341e78969ce1ca7239906820be806464f4f0",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.constantOrigins_length",
    "ff6f57ceb130fd5c7afb04483a71dd35d6c0901d1c273cb818524955d09ead78",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.constantOrigins_nodup",
    "d460767c424f353e4fa55a4c69ed2b894cbb67a019fdfe1a6301803ee9b9d123",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.sharingOrigins_length",
    "5d32f12f05b8d74e2189dac203a5884ffcf2901718d8df9be24197419293d6f5",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.sharingOrigins_nodup",
    "6ae2028ce506d17b29a4cae3a95608b39d08f6bcc6a6fc0c54dfac799b1d0372",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.passRemoved_iff",
    "70ee616a83cc3c5616a1d45debdc66a6158d5d6f3e1609b3ac142527d03baf8c",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.pass_partition",
    "19e08cbec0920fb3a42b3f5410df0c3c3c8d00091d171cd2e7ccc34de44cb89f",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.traceRemoved_iff",
    "2ff537494358c31414be32cd8eaa58b43f9ea67405dd26b311796a7e1e624d20",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.trace_partition",
    "0d582bd2528fd7cb1173fb65774e3da5243e8829a111de69ffb8e23cc295aaab",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.normalizedRemoved_iff",
    "94869e335fb1d5ccd4028d042f58947445fb81f8ec723c60f04e8c5475f0ed2b",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.PhysicalGateProvenance.normalized_partition",
    "a3bfc555871bbf9b68392988b2da985cfe197e5cee9a0160cd80a5ff9d21c7ca",
    "PNP.NANDPhysicalGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.PhysicalOwnership.append_origin_left",
    "9afdba03ec2436ac542988b0f652e1ec07fee4279ebac2a634d0f0f49727aada",
    "PNP.NANDWireHistoryPhysicalOwnership",
    []
  ],
  [
    "PNP.DirectWire.WireObligationHistory.PhysicalOwnership.append_origin_right",
    "8a444e72d3f991426deaddd21d998616fc0575df54f9ea01b2cde84388cf9e67",
    "PNP.NANDWireHistoryPhysicalOwnership",
    []
  ],
  [
    "PNP.DirectWire.WireObligationHistory.PhysicalOwnership.append_live",
    "257ae4df34d79ec42e4a44327a3b4c618c3d5f2d11e382373f342d1b1ed5a071",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.PhysicalOwnership.normalize_partition",
    "e33b6b1465b29d1addb15ce74b5635bc01dbb2b87246d175759f4f3992b08868",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.PhysicalOwnership.normalize_removed_length",
    "b33839398a6c2036a65e9d574186230707c14aa13d9d5347d23e0875f7a7dc63",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.Transition.restore_physical_positions",
    "1956f45e49b044f0e47363773cb20232bc111f537dd5e8c3b4d2253518e728f4",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.Transition.realize_physical_positions",
    "b8ee4c2c2ab33f0846988fffe23fad6dd769b50d3e273c81cc6076e2b163af4d",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.Transition.allocations_nodup",
    "1cc162937cabc1604fac30a36d0e05242f00184b8047a6a9384229c71be48c6e",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.Transition.physical_charged",
    "b2467ea4d5c663e9363d8353f0bb574a80d4efe248407114087ceeef518c93fa",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.Transition.physical_removed_length",
    "ed90185d1c2b9b66735c8962d8a546e5c7e6d3ffaf62e4608cbe71007dd1cea6",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.Transition.physical_conservation",
    "931de16d0241abcd7856537a0c00ebbc51c0feb3c19da74ba2cb33599c82c5bb",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.Execution.allocations_length",
    "caaa1736988fc0acf1727ca6df8976ebbd52039a1af02bf5315fa57c5810bc04",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.Execution.physical_charged",
    "aa253a544d843c2599c5cfea7c7e4361a0c6a36a8c6e54ef119fcb8f5197a213",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.Execution.physical_removed_length",
    "885e29a7bb392140823615432d7bbc334d98fc330243be94a9c7da535dcdb1f3",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.Execution.physical_conservation",
    "26d8b9abec293a82e70f3133767e18713595e0fc368743a2958312519344621b",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.Execution.allocations_member",
    "ca85c7c84c8f0fb2c202aa70897f0ac49ffe907608dfef9c523a24430e438686",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.Execution.allocations_nodup",
    "1da81f73d09754139d6dd1153d98bcc824f19cd8617d3cccea7ce4048d41c469",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.ClosedHistory.physical_charged",
    "11d34b18ad00bfe232492981b2657aaa38448d29a69b02d34c3521bbea0a3ac4",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.ClosedHistory.physical_partition",
    "69a4fe153f6498b15ad42cd396d9a4ccb9689868282a83bae7a2c62825e34b33",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.ClosedHistory.physical_ownership",
    "47e0d3740795b0ac6c3d2206c7e7f67ffe871129ecab9b086a7aa20e4469cbab",
    "PNP.NANDWireHistoryPhysicalOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.CompiledRawNandGraph.position_surjective",
    "bdb90efec30abbae02e40e5fdf44e2937615b4043eacc53238fdd5d1469b1df2",
    "PNP.NANDCompiledGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.CompiledRawNandGraph.position_physicalOrigin",
    "17bd5509874417c33e0209722107889ccf84448981fc0ac806bac5fab7e44128",
    "PNP.NANDCompiledGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.CompiledRawNandGraph.physicalOrigin_position",
    "d5e36b792ea2bde2728df0bcdbfe33ec33c00944495f092370aeaed6e0ea5ec2",
    "PNP.NANDCompiledGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.CompiledRawNandGraph.physicalOrigin_injective",
    "fc5f39e92480ba6f1db32b33ef71e6e536d504fccee0d46142b466f45d8fe933",
    "PNP.NANDCompiledGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.CompiledRawNandGraph.physicalOrigin_surjective",
    "6121060d68bacbcf7d7dd071175266c583036e6b96444358a070ce30ce49af78",
    "PNP.NANDCompiledGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.CompiledRawNandGraph.physicalOrigins_nodup",
    "f18a162a7b8d0a2a4b757528cfc8a5367c344dc8723d0b05ca319ee32ad26932",
    "PNP.NANDCompiledGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.CompiledRawNandGraph.physicalOrigins_perm",
    "af788ac5330f1a9894e5d23fd9fac6716d2889bb55a5c0a39b18fc4c144c53e6",
    "PNP.NANDCompiledGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.RawNandCompilationState.finish_physicalOrigin",
    "841a12140fa8ca58f426d2b749a41c61d174f5c4118442d42ce217239a80be81",
    "PNP.NANDCompiledGateProvenance",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.liftOrigin_injective",
    "a411a824f5daea7541095b83555c2f5bb3ec28a3ca93b4902058d8aa13e28858",
    "PNP.NANDWireHistoryAmbientOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.original_coordinate_partition",
    "19ab4f02338c163a8eeddf389c907c77ff6cb346374e1d6ad779f373e772a350",
    "PNP.NANDWireHistoryAmbientOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.rawNodeOrigin_exterior",
    "7efc06d7e7cdf0fa3651d5cbe32e6b83a890c9deae953225f2eec26c1e3c5478",
    "PNP.NANDWireHistoryAmbientOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.rawNodeOrigin_history",
    "6240b96751e2a302b9f580ba7147ebd7a7b9674f696f09981a5b713092309dfd",
    "PNP.NANDWireHistoryAmbientOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.physicalOrigin_position",
    "951a09ce7a6c0dc86125ef5cceb8509bee4a0a31c69387cd26c3ddd4ede7e6ae",
    "PNP.NANDWireHistoryAmbientOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.physical_partition",
    "08d79b70a6af3f0235c82fe4359effc9926474256122ad1e87621205a3e01804",
    "PNP.NANDWireHistoryAmbientOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.physical_ownership",
    "ff59796a5c35fe19e783817f2c8ea1610bf71bf9592e8b788bd568d77549672e",
    "PNP.NANDWireHistoryAmbientOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.ownership",
    "fc89ddf7524a58178d19a3eed329a3f065749dab8e18a2f25479ba235ad2ec90",
    "PNP.NANDWireHistoryAmbientOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.semantics",
    "6b5a693f097241f0052d6850ec8432a541d396efd4815e73504e82efffc8f560",
    "PNP.NANDWireHistoryAmbientOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.compileOwned_result",
    "3bb87cf64974e0183dfc93e1165a4001c056272f6192db69348776cc1d1dc904",
    "PNP.NANDWireHistoryAmbientOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.eventRequests_member",
    "c870ed67933c7046c7f0e6a3f7caad17ff5efab92a994030a87b5e37942fad19",
    "PNP.NANDWireHistoryOwnershipCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.eventRequests_disjoint",
    "93875722c5ad6d4de59221bfcfc358d5f54f530710b03c825b0a15d40c1181c4",
    "PNP.NANDWireHistoryOwnershipCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.eventOwner_some_iff",
    "740e60277424d0d613588ebbbd5dae9da97faf7455071d7fe86b11fd5938718b",
    "PNP.NANDWireHistoryOwnershipCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.charged_origin",
    "0110c36cb44124fa20f9df5e06624f4a5c4d0f98b478adc28f68716b5a64ba83",
    "PNP.NANDWireHistoryOwnershipCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.live_allocated_event",
    "880f9a64edab53563ad11ffd5106141ec93382ef98a262bffb3735b107e94ac6",
    "PNP.NANDWireHistoryOwnershipCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.eventOwner_none_iff",
    "44e30563a74c0498db9ed3f3b9695a054fdbe9d723dd27a702548a41678ad973",
    "PNP.NANDWireHistoryOwnershipCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.support_membership",
    "c97c0c701f73ec13c324995db71f5dc416f0e9125a2c547401528cafd1a5ef04",
    "PNP.NANDWireHistoryOwnershipCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.support_restrict",
    "2bc506ad56be16661b29a289e812f0191df18d6d8dc2c4f32b875b102e023441",
    "PNP.NANDWireHistoryOwnershipCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.materializer_gateCount",
    "3bd6d2569d30d2551daf928ee38946dd8a97ecb8d535db76e5f67e113afbac55",
    "PNP.NANDWireHistoryOwnershipCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.materializer_chargeIdentity",
    "e2a7325d41ee818ba8af3312e37ebd04063d120ff374f4aded29849d87be08a4",
    "PNP.NANDWireHistoryOwnershipCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.materializer_wholeCharge",
    "6d45667f0679b22ab40dc76cd7659fc2910fdd15894420f0544fbc0ba1db17fb",
    "PNP.NANDWireHistoryOwnershipCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.materializer_semantics",
    "3f169574895f1e4073b50191f7a9cc91ebbb6e0420518abaf7e09983b7d4e134",
    "PNP.NANDWireHistoryOwnershipCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.materializer_induced",
    "e1cf5862c73cef7279c68ee5fd011ac0ce7ac018e324b1085a966b716bebf82b",
    "PNP.NANDWireHistoryOwnershipCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ]
];
const STATUS_FIELDS = {
  "leanSourceDerivedHistoryOwnershipFormalized": true,
  "leanSourceDerivedHistoryOwnershipAxiomAuditPassed": true,
  "leanSourceDerivedHistoryOwnershipAuditedDeclarationCount": 78,
  "leanSourceDerivedHistoryOwnershipTerminalExtractionPhysicalOriginTheorem": "PNP.DirectWire.terminalExtractionOrigin_gateIndex",
  "leanSourceDerivedHistoryOwnershipNormalizationPhysicalPartitionTheorem": "PNP.DirectWire.PhysicalGateProvenance.normalized_partition",
  "leanSourceDerivedHistoryOwnershipClosedHistoryPhysicalOwnershipTheorem": "PNP.DirectWire.WireObligationHistory.ClosedHistory.physical_ownership",
  "leanSourceDerivedHistoryOwnershipCompilerPhysicalOriginInverseTheorem": "PNP.DirectWire.CompiledRawNandGraph.position_physicalOrigin",
  "leanSourceDerivedHistoryOwnershipCompilerPhysicalOriginPermutationTheorem": "PNP.DirectWire.CompiledRawNandGraph.physicalOrigins_perm",
  "leanSourceDerivedHistoryOwnershipAmbientOriginalCoordinatePartitionTheorem": "PNP.DirectWire.WireHistoryAmbientOwnership.original_coordinate_partition",
  "leanSourceDerivedHistoryOwnershipAmbientPhysicalOwnershipTheorem": "PNP.DirectWire.WireHistoryAmbientOwnership.physical_ownership",
  "leanSourceDerivedHistoryOwnershipSourceOnlyConstructorProjectionTheorem": "PNP.DirectWire.WireHistoryAmbientOwnership.compileOwned_result",
  "leanSourceDerivedHistoryOwnershipSourceOnlyConstructorSemanticsTheorem": "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.semantics",
  "leanSourceDerivedHistoryOwnershipDerivedEventRequestsDisjointTheorem": "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.eventRequests_disjoint",
  "leanSourceDerivedHistoryOwnershipActualRawEventOwnershipTheorem": "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.eventOwner_some_iff",
  "leanSourceDerivedHistoryOwnershipFixedRemainderTheorem": "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.eventOwner_none_iff",
  "leanSourceDerivedHistoryOwnershipHistoricalChargeCompletenessTheorem": "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.charged_origin",
  "leanSourceDerivedHistoryOwnershipSurvivingAllocationCompletenessTheorem": "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.live_allocated_event",
  "leanSourceDerivedHistoryOwnershipSupportRestrictionTheorem": "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.support_restrict",
  "leanSourceDerivedHistoryOwnershipActualExtractedGateCountTheorem": "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.materializer_gateCount",
  "leanSourceDerivedHistoryOwnershipActualChargeIdentityTheorem": "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.materializer_chargeIdentity",
  "leanSourceDerivedHistoryOwnershipWholeChargeTheorem": "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.materializer_wholeCharge",
  "leanSourceDerivedHistoryOwnershipIndependentOpenSemanticsTheorem": "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.materializer_semantics",
  "leanSourceDerivedHistoryOwnershipInducedBoundaryTheorem": "PNP.DirectWire.WireHistoryAmbientOwnership.OwnedCompilation.materializer_induced",
  "leanSourceDerivedHistoryOwnershipArbitraryFiniteCarrierSupportAndEventDimensionsCovered": true,
  "leanSourceDerivedHistoryOwnershipLiteralNormalizerRetainedOriginsDerived": true,
  "leanSourceDerivedHistoryOwnershipRemovedOriginsAreExactComplement": true,
  "leanSourceDerivedHistoryOwnershipExecutingEventAndLocalGateAllocationLabelsDerived": true,
  "leanSourceDerivedHistoryOwnershipHistoricalChargesSurviveLaterRemoval": true,
  "leanSourceDerivedHistoryOwnershipActualTopologicalCompilerPositionsUsed": true,
  "leanSourceDerivedHistoryOwnershipExteriorPhysicalGatesRetainedExactlyOnce": true,
  "leanSourceDerivedHistoryOwnershipDerivedEventRequestsDisjoint": true,
  "leanSourceDerivedHistoryOwnershipSupportRestrictionPreservesOwners": true,
  "leanSourceDerivedHistoryOwnershipExistingConstructorAcceptanceAndResultPreserved": true,
  "leanSourceDerivedHistoryOwnershipCallerSuppliedOwnerFamilyRequired": false,
  "leanSourceDerivedHistoryOwnershipCallerSuppliedProvenanceOrPartitionRequired": false,
  "leanSourceDerivedHistoryOwnershipCallerSuppliedChargeOrTopologicalOrderRequired": false,
  "leanSourceDerivedHistoryOwnershipCallerSuppliedSuccessfulSpliceCertificateRequired": false,
  "leanSourceDerivedHistoryOwnershipArbitraryCountPreservingPermutationIsProvenance": false,
  "leanSourceDerivedHistoryOwnershipHistoricalChargesEqualSurvivingOwnedSize": false,
  "leanSourceDerivedHistoryOwnershipSupportRecordsAndRawEventsDerivedFromEveryInput": false,
  "leanSourceDerivedHistoryOwnershipCompleteManuscriptCarrierAndRewriteCalculusProved": false,
  "leanSourceDerivedHistoryOwnershipArbitraryObserverOrFullProfileTransportProved": false,
  "leanSourceDerivedHistoryOwnershipMatchedKappaArbitrarySupportPullExpandProved": false,
  "leanSourceDerivedHistoryOwnershipCompletePackageEProved": false,
  "leanSourceDerivedHistoryOwnershipTerminalFamiliesDerived": false,
  "leanSourceDerivedHistoryOwnershipGloballySuccessfulRewriteStrategyDerived": false,
  "leanSourceDerivedHistoryOwnershipGlobalRouteCoverageProved": false,
  "leanSourceDerivedHistoryOwnershipUnconditionalSaturatePositiveProved": false,
  "leanSourceDerivedHistoryOwnershipUnconditionalBCELReadyProved": false,
  "leanSourceDerivedHistoryOwnershipUnconditionalZeroSlackProved": false,
  "leanSourceDerivedHistoryOwnershipExactGeneralPCCMinProved": false,
  "leanSourceDerivedHistoryOwnershipPolynomialRuntimeOutputAndCertificateBoundsProved": false,
  "leanSourceDerivedHistoryOwnershipRuntimeExecutionIsProofAuthority": false,
  "leanSourceDerivedHistoryOwnershipScope": "arbitrary-finite-computational-histories-source-derived-literal-normalization-origins-executing-event-local-allocation-labels-live-removed-charged-nodup-partition-actual-topological-splice-positions-one-copy-exterior-disjoint-derived-requests-support-stable-extracted-charges-no-supplied-owner-or-partition-no-global-strategy-or-complete-manuscript-calculus-or-polynomial-runtime"
};
const COORDINATE = "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-16-266";
const MILESTONE = "source-derived-history-ownership";
const SCOPE = "For arbitrary finite computational carriers, selected support lists and raw-event dimensions, physical origins follow the actual constant, sharing and cone compiler branches and compose through the existing normalization trace. Every initial gate retains its source coordinate; every R7/R8 appended gate is labelled by its executing event identity and local allocation coordinate. Creation, cancellation and reads allocate no gates. The complete closed history computes a duplicate-free partition of live and removed origins into original gates and all historical charges, including allocations later removed. The actual topological compiler's computed two-sided position inverse carries those labels into the literal ambient splice, with every exterior gate present once and extracted coordinates restored to ambient positions. A source-only ownership constructor returns exactly the existing constructor's result. Its disjoint raw-event requests and fixed original-gate remainder reuse the existing ownership kernel for support-stable membership, actual extracted piece sizes and charge identities, independent open semantics and induced-boundary reconnection. No owner family, provenance map, partition proof, charge amount, topological order or successful-splice certificate is supplied.";
const NON_CLAIM = "This is source-derived physical ownership for the existing computational history language, not the complete manuscript carrier/profile universe, all R1-R9 or N1-N10 routes, arbitrary observers, matched-kappa arbitrary-support Pull/Expand or complete Package E. Support coordinates and raw events remain input data; no terminal-derived family or globally successful history is constructed. Historical allocated size and surviving owned size are distinct, and physical identity or integer accounting does not prove a runtime bound. Global route coverage, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin and complete encoded-input polynomial runtime, output and certificate bounds remain open. Finite runtime fixtures are regression evidence, not proof authority. No fixed weighted checkpoint or global gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.";
const TEST_FILES = [
  "audits/lean-source-derived-history-ownership0.test.mjs",
  "audits/lean-source-derived-history-ownership-publication0.test.mjs"
];
const AUDIT = "lean-audit/PNPSourceDerivedHistoryOwnershipAxiomAudit.lean";
const REGRESSIONS = [
  "lean-regression/PNPPhysicalGateProvenance.lean",
  "lean-regression/PNPWireHistoryPhysicalOwnership.lean",
  "lean-regression/PNPCompiledGateProvenance.lean",
  "lean-regression/PNPWireHistoryAmbientOwnership.lean"
];
const DOCUMENTATION = "docs/lean_source_derived_history_ownership.md";
const PLAN = "docs/plans/2026-09-16-source-derived-history-ownership.md";
const COMMAND = 'node --test ' + TEST_FILES.join(' ');
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const canonical0 = value => Buffer.from(stableStringify0(value) + '\n');
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();

test('M266 preflight: package, verifier and durable CI share the exact audited boundary', async () => {
  const [pkg,surface,verifier,workflow,root] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'), text0('.github/workflows/lean-bridge.yml'),
    text0('lean/PNP.lean'),
  ]);
  assert.equal(REVIEWED.length,78);
  assert.equal(new Set(REVIEWED.map(row=>row[0])).size,78);
  assert.equal(JSON.parse(pkg).scripts['audit:m266'],COMMAND);
  assert.ok(surface.includes("'audit:m266': '"+COMMAND+"'"));
  for(const file of TEST_FILES) assert.ok(verifier.includes("'"+file+"'"),file);
  assert.ok(workflow.includes('run: npm run audit:m266'));
  for(const file of REGRESSIONS)
    assert.ok(workflow.includes('lake env lean -DwarningAsError=true '+file),file);
  const steps=workflow.split(/^      - name:/mu).filter(step=>
    step.includes('node scripts/check-lean-axioms.mjs '+AUDIT));
  assert.equal(steps.length,1);
  assert.match(root,/^import PNP\.NANDWireHistoryOwnershipCharges$/mu);
  assert.ok(workflow.includes('node --test audits/lean-axiom-transcript0.test.mjs'));
  assert.ok(verifier.includes("'audits/lean-axiom-transcript0.test.mjs'"));
});

let sourcesPromise;
function sources0() {
  sourcesPromise ??= Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('status/LEAN_THEOREM_INVENTORY.json'),
    text0('status/PROOF_PROGRESS.json'), text0('publication/FORMAL_PUBLICATION_MAP.json'),
  ]).then(([status,inventory,progress,map]) => ({
    status:JSON.parse(status), inventory:JSON.parse(inventory), inventoryBytes:Buffer.from(inventory),
    progress:JSON.parse(progress), map:JSON.parse(map),
  }));
  return sourcesPromise;
}

test('M266 release: exact compiled types, axiom closures and limited claims match review', async () => {
  const {status,inventory,inventoryBytes,map} = await sources0();
  assert.ok(canonical0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory,map,inventoryBytes,status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === MILESTONE);
  assert.equal(row?.earned, true);
  assert.equal(row.classification, 'formalized-foundation-only');
  assert.deepEqual(row.requiredTheorems, REVIEWED.map(item => item[0]));
  assert.equal(row.scope, SCOPE);
  assert.equal(row.nonClaim, NON_CLAIM);
  for (const [name,typeHash,module,axioms] of REVIEWED) {
    for (const collection of [inventory.declarations,inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind,'theorem',name);
      assert.equal(declaration.module,module,name);
      assert.deepEqual(declaration.axioms,axioms,name);
      assert.ok(axioms.every(value => ['Quot.sound','propext'].includes(value)),name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name,candidate.kernelType),typeHash,name);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name],typeHash,name);
  }
  for (const [field,value] of Object.entries(STATUS_FIELDS)) assert.deepEqual(status[field],value,field);
});

test('M266 release: every reviewed type rejects weakening and supplied proof authority', async () => {
  const {status,inventory,map} = await sources0();
  const alternatives = new Map();
  for (const [name,expected] of REVIEWED) {
    const current = inventory.milestoneCandidates.find(row => row.name === name).kernelType;
    const changed = ['Lean.Expr.const ' + String.fromCharCode(96) + 'True []',
      'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + current + ') (' + current
        + ') (Lean.BinderInfo.default)'];
    for (const type of changed) assert.notEqual(MilestoneTheoremKernelTypeSha2560(name,type),expected,name);
    alternatives.set(name,changed);
  }
  // All pins are tested above; exercise the shared derivation once per affected
  // module and mutation kind instead of repeatedly serializing identical data.
  const representatives = new Map(REVIEWED.map(row => [row[2],row[0]]));
  for (const name of representatives.values()) for (const type of alternatives.get(name)) {
    const mutation = {...inventory,milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row,kernelType:type} : row)};
    const result = DeriveFormalPublication0(mutation,map,canonical0(mutation),status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === MILESTONE).earned,false,name);
    assert.equal(result.gate.passed,false);
  }
});

test('M266 release: hidden authority, absent evidence and widened publication claims reject', async () => {
  const {status,inventory,inventoryBytes,map} = await sources0();
  const name = 'PNP.DirectWire.WireHistoryAmbientOwnership.compileOwned_result';
  const addAuthority = row => row.name === name
    ? {...row,axioms:['PNP.UnauthorizedAuthority','Quot.sound','propext']} : row;
  const mutation = {...inventory,declarations:inventory.declarations.map(addAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(addAuthority)};
  const result = DeriveFormalPublication0(mutation,map,canonical0(mutation),status.leanSourceClosureSha256);
  assert.equal(result.milestones.find(row => row.id === MILESTONE).earned,false);
  assert.equal(result.gate.passed,false);
  const missing = {...inventory,milestoneCandidates:inventory.milestoneCandidates.filter(row => row.name !== name)};
  assert.throws(() => DeriveFormalPublication0(missing,map,canonical0(missing),status.leanSourceClosureSha256),
    /reviewed milestone theorem candidate inventory mismatch/u);
  for (const field of ['scope','nonClaim']) {
    const widened = {...map,milestones:map.milestones.map(row => row.id === MILESTONE
      ? {...row,[field]:'Physical ownership proves unconditional polynomial ZeroSlack and erases removed charges.'} : row)};
    assert.throws(() => DeriveFormalPublication0(inventory,widened,inventoryBytes,status.leanSourceClosureSha256),
      /map drifted from the reviewed specification/u);
  }
  const changedPin = {...map,earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256,[name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory,changedPin,inventoryBytes,status.leanSourceClosureSha256),
    /map drifted from the reviewed specification/u);
});

test('M266 release: status rejects changed construction, accounting and runtime claims', async () => {
  const {status} = await sources0();
  for (const suffix of ['ClosedHistoryPhysicalOwnershipTheorem','AmbientPhysicalOwnershipTheorem','AuditedDeclarationCount',
    'HistoricalChargesEqualSurvivingOwnedSize','CallerSuppliedOwnerFamilyRequired',
    'SupportRecordsAndRawEventsDerivedFromEveryInput','PolynomialRuntimeOutputAndCertificateBoundsProved','Scope']) {
    const field = 'leanSourceDerivedHistoryOwnership' + suffix;
    const value = STATUS_FIELDS[field];
    const mutation = {...status,[field]:typeof value === 'boolean' ? !value
      : typeof value === 'number' ? value + 1 : value + ':unreviewed'};
    const result = await CheckFormalReconstructionStatus0({
      writeOutput:false,statusOverride:mutation,siteOverride:mutation,
    });
    assert.equal(result.tag,'reject',field);
    assert.equal(result.coord,'FormalReconstructionStatus.Field',field);
    assert.deepEqual(result.path,['status/FORMAL_RECONSTRUCTION_STATUS.json',field],field);
  }
});

test('M266 release: source-derived physical ownership earns no unconditional checkpoint', async () => {
  const {status,inventory,progress} = await sources0();
  assert.equal(validateProofProgress0(progress,status,inventory).tag,'accept');
  const reviews = progress.history.filter(row => row.asOfCoordinate === COORDINATE);
  assert.equal(reviews.length,1);
  const review = reviews[0];
  assert.equal(review.scoreChanged,false);
  assert.deepEqual(review.changedCheckpointIds,[]);
  assert.deepEqual(review.changeRecords,[]);
  assert.equal(review.riskWeightedProofCompletionPercent,40);
  assert.equal(review.uncertaintyLowPercent,20);
  assert.equal(review.uncertaintyHighPercent,40);
  assert.equal(review.globalGatesClosed,0);
  assert.equal(review.globalGatesAvailable,5);
  assert.ok(prose0(review.rationale).includes('No fixed load-bearing checkpoint changes state'));
  if (progress.asOfCoordinate !== COORDINATE) return;
  assert.deepEqual(review.formalArtefactCoverage,{
    earnedRows:status.formalPublicationMilestones.filter(row => row.earned).length,
    totalRows:status.formalPublicationMilestones.length,
  });
  assert.deepEqual(progress.tracks.map(track => track.pointsEarned),[13,20,2,1,4]);
  assert.equal(progress.proofCompletion.percent,40);
  assert.equal(progress.globalGates.length,5);
  assert.ok(progress.globalGates.every(gate => gate.status === 'open'));
  assert.deepEqual(inventory.projectAxioms,[]);
  assert.deepEqual(progress.projectSpecificAxiomsRemaining,[]);
  assert.equal(inventory.declarations.some(row => row.name === 'PNP.Main.p_eq_np'),false);
  assert.equal(status.leanConcreteCNFSATInPFormalized,false);
  assert.equal(status.concretePublicationGate.passed,false);
  assert.equal(progress.publicationGate.passed,false);
  assert.deepEqual(progress.rootTheorem,{name:'PNP.Main.p_eq_np',present:false,built:false,axiomAuditPassed:false});
  const inflated = structuredClone(progress);
  inflated.proofCompletion.pointsEarned += 1;
  inflated.proofCompletion.percent += 1;
  assert.throws(() => validateProofProgress0(inflated,status,inventory),error => error.code === 'ProofCompletion.StoredEarned');
});

test('M266 release: current documentation reports separate metrics and justified publication', async () => {
  const {progress} = await sources0();
  const documentation = prose0(await text0(DOCUMENTATION));
  const plan = prose0(await text0(PLAN));
  assert.ok(documentation.includes(COORDINATE));
  assert.ok(documentation.includes(prose0(SCOPE)));
  assert.ok(documentation.includes(prose0(NON_CLAIM)));
  assert.ok(documentation.includes('Publication decision: defer'));
  assert.ok(plan.includes('Publication decision: defer'));
  if (progress.asOfCoordinate !== COORDINATE) return;
  const p = progress.proofCompletion, a = progress.formalArtefactCoverage;
  const metrics = [
    'Formal artefact coverage: ' + a.earnedRows + ' of ' + a.totalRows + ' current scoped publication rows earned.',
    'Risk-weighted proof completion estimate: ' + p.percent + '%.',
    'Uncertainty range: ' + p.uncertaintyLowPercent + '% to ' + p.uncertaintyHighPercent + '%.',
    'Global gates closed: ' + progress.globalGates.filter(gate => gate.status === 'closed').length + ' of 5.',
  ];
  for (const file of ['README.md','docs/FORMAL_RECONSTRUCTION.md','docs/lean_bridge.md',
    'docs/proof_pipeline.md','docs/audit_questions.md','docs/proof_progress.md',DOCUMENTATION]) {
    const current = prose0(await text0(file));
    for (const metric of metrics) assert.ok(current.includes(metric),file + ': ' + metric);
  }
});

test('M266 preflight: explicit-root audit and both inventory producers retain every reviewed name',async()=>{
  const [audit,probe] = await Promise.all([text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean')]);
  assert.match(audit,/^import PNP$/mu);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),REVIEWED.map(row=>row[0]));
  for (const [name] of REVIEWED) {
    assert.equal(probe.split(String.fromCharCode(96)+name+',').length-1,1,name);
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(value=>value===name).length,1,name);
  }
  const map=JSON.parse(await text0('publication/FORMAL_PUBLICATION_MAP.json'));
  const row=map.milestones.find(item=>item.id===MILESTONE);
  assert.deepEqual(row.requiredTheorems,REVIEWED.map(item=>item[0]));
  assert.equal(row.scope,SCOPE);
  assert.equal(row.nonClaim,NON_CLAIM);
  assert.equal(row.classification,'formalized-foundation-only');
  for(const [name] of REVIEWED)assert.ok(Object.hasOwn(map.earnedMilestoneTheoremKernelTypeSha256,name),name);
});
