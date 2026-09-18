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
    "PNP.DirectWire.StructuralReindexing.GateRenaming.decode_encode",
    "6660efe22c09761b56b9f6868aecb0d5999fb0293e6d24651c9af3f597d8fccc",
    "PNP.NANDGateRenamingEncoding",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.StructuralReindexing.GateRenaming.encode_length_le",
    "40e8aa3e2cafa08891074bb9146c43e7b245a630ab6a02e735d94055842172fd",
    "PNP.NANDGateRenamingEncoding",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.StructuralReindexing.GateRenaming.validCode_encode",
    "86c582cc582c38d6ace241f6b588e092cbca557c25e2edeb08d2585afd4f33e1",
    "PNP.NANDGateRenamingEncoding",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.roundTripCheck_iff",
    "032eb300149ce2abaf6977b5e973fd3f46b12b0150f64c9bb72023c2c716ff1b",
    "PNP.NANDWireCarrierRecoding",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.check_iff",
    "b8428c4919ec8ff68924f61a6fd39bdd107997cd1a158112f547ad72671bd9a1",
    "PNP.NANDWireCarrierRecoding",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.compile_success_iff",
    "c252a271b9a546e07bea6ee0dc4fd26de8ed615c73fc60e84797f38e5753eb1a",
    "PNP.NANDWireCarrierRecoding",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.appendMap_gateCount",
    "eb6fa751827131872c833b142841a94f168e0c803fda35ceb0663e4b87d475ac",
    "PNP.NANDWireCarrierRecoding",
    []
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.appendMap_output",
    "9f8dc75c0ab8e91fecfc6ce9406063ab912094b9957d167d5a9b2d259a6aedfc",
    "PNP.NANDWireCarrierRecoding",
    []
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.appendMap_field",
    "d3c3093bfd6ceb0fc8bd69723e948ce185e03f8c64d898c1d3f5deee91bdd512",
    "PNP.NANDWireCarrierRecoding",
    []
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.encoded_output",
    "c7ca6dec5879b620506628e240fba74fbdf6667d14989dab7ccd1c8bd649c39e",
    "PNP.NANDWireCarrierRecoding",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.encoded_field",
    "d94d62958eb4f782f0692bfadda25d7512c6310f2d83ccc5872acfc27a0a09ad",
    "PNP.NANDWireCarrierRecoding",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.result_output",
    "f33da5b5ebefd1113e056b6e47aea7e23a291deef7b8a8d03e53f31faba88e86",
    "PNP.NANDWireCarrierRecoding",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.result_field",
    "8ab7ae4e6e2e7d43d68793c565dc74f2e9dfaa6786f5c05844d4806e48d46d44",
    "PNP.NANDWireCarrierRecoding",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.result_gate_balance",
    "7b07f5a4f35d636ffc64f8f8ff18fe992b3a5ddcd6ed3f48e5169997988fc920",
    "PNP.NANDWireCarrierRecoding",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.CausalBound.levels_bounded_iff",
    "ebbd048bd7305b05f887b0f38fe0a8558ff3c75f1f45e5dc05c0e699fea1ab3b",
    "PNP.NANDCausalGuard",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.CausalBound.source_bounded_iff",
    "9d414f1e1ee5f72ad11ec4cd652f4f8abcaea66dea4730bce6fbfd4c6938e3ba",
    "PNP.NANDCausalGuard",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.CausalBound.sourceDependencyGuard_iff",
    "bbc0960840ffc1d4ac5d0f0a37df41ffadca0cca93da82e54b2022a045fde04c",
    "PNP.NANDCausalGuard",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.CausalBound.candidateDependencyGuard_iff",
    "4ec22d9a6690ce9b4806807fb76f566a7867a92348870b0b312fe22eaed350f6",
    "PNP.NANDCausalGuard",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrier.dependencyGuard_iff",
    "1e98d48243e129b1f266728ecdb55e9772ad9cb0438a15a4a15923136ccf8c44",
    "PNP.NANDCausalGuard",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.State.recode_pending",
    "7c1beb6c753f0df3e0b0bf1f38118dd98f17aa879a2e852d3c98821188eb1e1f",
    "PNP.NANDWireRecodingState",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.State.recode_charged",
    "b4aef62d364b7c4c6245f0e8ca8bed41a05464e2ce230a9d000928fd78255a64",
    "PNP.NANDWireRecodingState",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.State.recode_removed",
    "77b196818890ebefe25898ac14af4cf46939c89dac367989b8de0c7343de2e5e",
    "PNP.NANDWireRecodingState",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.State.recode_causalInvariant",
    "e4fea440709b30d81dcee0c486755763594e3365ca54804d350283017cb5bc78",
    "PNP.NANDWireRecodingState",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireRecodingState.execute_success_iff",
    "163a20967daa234a938ed706f4589614e6f7a7a6b4c50617e7b27f016004ef67",
    "PNP.NANDWireRecodingState",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireRecodingState.execute_failure_iff",
    "6267b7e4cbba64143b2dfae86f1bea5d19f3ab0b5eaf9bd449139e5c96e45da0",
    "PNP.NANDWireRecodingState",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireRecodingState.Receipt.pending",
    "06e2fb27322a3af09bfe49347dada9112574cc40c1fbf9cb76012029a1e64295",
    "PNP.NANDWireRecodingState",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireRecodingState.Receipt.causalInvariant",
    "bc8cd87f7609392854afd1faf6e146905ab74ed6d464cade9e0e3e68d56b9657",
    "PNP.NANDWireRecodingState",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireRecodingState.Receipt.gate_balance",
    "1e6c6b94e24fcff4c2b9a18f85066b7a2705fa257dae1bdb63eb690d4be6ff86",
    "PNP.NANDWireRecodingState",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.encoder_positions",
    "6d89fcd3e581a501e3e527a69e8657eeb7436bf5a461994e3db75dfb949de272",
    "PNP.NANDWireRecodingOwnership",
    []
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.encoded_origin",
    "91e43da2e83bfadc32a72a6c33bc18d997a04c89d60f9f32c70996c33963b6af",
    "PNP.NANDWireRecodingOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.decoder_positions",
    "2c004056d1bcee2aae311e9da8de9f4bb905479e0245fbf859a99c66b5749ba4",
    "PNP.NANDWireRecodingOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.ledger_origin",
    "fd73735bdfbd7090574471bfe761c22f73dc15b710234b6c768cf64b52667237",
    "PNP.NANDWireRecodingOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.ledger_charged",
    "ac0136ab5f53d55cf3261e7f551d4bc8939b7ebf9c45d4db40406c042f9d6852",
    "PNP.NANDWireRecodingOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.ledger_removed_length",
    "920379da36b7bda0a59d43b00178cd7ad1cb4e359cd376975578a9cceb6ec2a6",
    "PNP.NANDWireRecodingOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.ledger_partition",
    "9df0c1ff67ea10307421dbc671a69d40d14574f8bfddb1825bc535a22568b891",
    "PNP.NANDWireRecodingOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.allocation_phases_nodup",
    "ad233c47fc6d4bc001a3bca2b580b932bda58fa0f9a690c1d717314243c170f8",
    "PNP.NANDWireRecodingOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.physical_ownership",
    "287e316a38d92876f3dd036c3030d8f9e6e737d4b4ca3f75ee6d906578552855",
    "PNP.NANDWireRecodingOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.labelled_live",
    "c12e4e6094a3e2d9ad3de90152006415fd71caf1e9d8bf4e0031523d72fa6a62",
    "PNP.NANDWireRecodingOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.labelled_physical_ownership",
    "d03fd71b704320f0f35fbfebe9190485d93ee5d15cc51b525e01a9f8b79d337b",
    "PNP.NANDWireRecodingOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireRecodingState.Receipt.physical_ownership",
    "1ebfc373a28ff6745659553facfee02c25b8de30ce65a455d5a9f10d0b5e61f0",
    "PNP.NANDWireRecodingOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireRecodingInput.decode_encode",
    "e92256250c309c1f4f00db703ba20064341335f7c635db2d8b31d20c8e0f0410",
    "PNP.NANDWireRecodingInput",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireRecodingInput.decode_elaboration_none",
    "00dc4032e7ad2ad068d9d9f0e5f1ff527ad2d1b1185e77c9440588efafd68d20",
    "PNP.NANDWireRecodingInput",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireRecodingInput.decode_success_iff",
    "55446d2b69fe0cfe75b6ab50ec814c47e26be72f941e6cb3ca198f8de5026750",
    "PNP.NANDWireRecodingInput",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireRecodingInput.execute_success_iff",
    "65eb3ce7bcf01ef30132102bbc072a72b91830806d9e7484657f64e505c98e04",
    "PNP.NANDWireRecodingInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireRecodingInput.execute_encoder_none",
    "feb8050014d9ab99386ccaf89e4aba6346890e198e7dd31f255d3440dffb62b6",
    "PNP.NANDWireRecodingInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireRecodingInput.execute_decoder_none",
    "0e5627a266dfdb1572d0bb12dae49c511c94b741a24e6c49f000735a21a926ab",
    "PNP.NANDWireRecodingInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireRecodingInput.Receipt.pending",
    "3c072c2c7bce589939d52436812277a7d12ce4ac94dfffddd9cb27e068268877",
    "PNP.NANDWireRecodingInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireRecodingInput.Receipt.charged_eq",
    "7e9181ee0fcf90a9fb29963d279ab8a45437318748bb5eef59e63b781c5c8613",
    "PNP.NANDWireRecodingInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireRecodingInput.Receipt.removed_eq",
    "1415c929619344b454b432c5f79407b5c03b3bbedf1fa2c5362adfb66cc12f2a",
    "PNP.NANDWireRecodingInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireRecodingInput.Receipt.causalInvariant",
    "46b915d04524543f69ebe8a94b8690e6759396b5a2d702ba9cb0ffe659813072",
    "PNP.NANDWireRecodingInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_origin",
    "e92c140a15b6a707bafcaaadb2a9a25eef3768908749814d35c26e08c02cb979",
    "PNP.NANDWireStructuralProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_charged",
    "88cea4855d7a80e52fb1ef445208021ad6babff0a45d2f993f6fef31d0ff4a6a",
    "PNP.NANDWireStructuralProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_removed",
    "12169fcda0c9ce0a4c4d421f867f039406516295425022212b8e06be0749c22a",
    "PNP.NANDWireStructuralProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.orderEvents_success_iff",
    "e1b2b9787c19111793f9f90668214efb7c6eff4d421e77aa91f3476f3fc89d72",
    "PNP.NANDWireOpenProgramInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.orderEvents_failure_iff",
    "8d3ebe6d609705e5320540cdcf174fb14bfcaf8aae8595d70ed1893c8dedc95a",
    "PNP.NANDWireOpenProgramInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.execute_failed_tail",
    "c852f45d97e5d2309875f6ba6f2a62aa22f4293c81781f6d7df84cae93f2bb72",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.full_output",
    "9cea32cc78cee0b2c900d6de17291ab5a16954b5b0bcc3cc13c7966bb8002990",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.full_field",
    "f7f2e0b981060c9871f68d80e139e2cd1035d277449dead2f13c9c5881518bef",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.creation_lifecycle",
    "9669cc796d490317f08119fd24b916dda275ff271609709f0ffe92e057a8fb2d",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.executed_count",
    "45c2da7f85d2cf6b15e999f771315afdd40b625fc3443eca9a715f768594202b",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.executed_identities_nodup",
    "35b434faefbe1677549ab531bffc512dc5a55890aec21d3ad8d43ec198101168",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.causalInvariant",
    "93a3cdc341e0720cc8327ae38b59cf4a0e419540c23ac76916af0fac7fc557ad",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.physical_ownership",
    "15204bb313e0909e10d02a1b740d478b508ce7d129322a15015f90648e12e562",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_origin_injective",
    "7be2e11b1cce85296ad1dfd57f1ef683118d51ea34962fbaf7b56163241cea8d",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_charge_origin",
    "3d637bfdf13b74e29f7d946f218bb8aa0ff6873271eccfc1ab546da6027b1fe0",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.compile_exists_iff",
    "1e58bf5b50338a0b30d0fe144e44e7c1a2b000c78e460d0a25a72efa4398da75",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.compile_none_iff",
    "7682645460be03c064cbc89ad7d53075275e646683bf6395d7749f8cc2ab72a5",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.records_source",
    "437a61a53cd319f887eda93378e0f109fd709c1d9747deb8fd4e77c0e463f326",
    "PNP.NANDWireOpenCertificate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.proper_support",
    "5c6f2e9d804360f72b08750c57d10d96f9512522c6fba908887347c5ac83d067",
    "PNP.NANDWireOpenCertificate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.output",
    "5f046bbe098419e59655fce686ee1bfd685ba68791cc61e8c7dca3a35e0c1dc2",
    "PNP.NANDWireOpenCertificate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.field",
    "cc8f761bd78a436e5b62f69e746761285b29662707461d4060366e94c3a607b6",
    "PNP.NANDWireOpenCertificate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.charge_accounting",
    "2264e7418f8b4391813ad064cbb043a4d2e27480fbb091497a4602d1d6206cce",
    "PNP.NANDWireOpenCertificate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictGain",
    "2f7d4f8fcdd07d5f5d87cdbd71bfa6b741458bb71a57152549a2dc4089b9848e",
    "PNP.NANDWireOpenCertificate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictResidualDescent",
    "47f9cc054c7a8c2c40750548184fc3c5c32ad95f3ed5872d9945af8cc7f6f21d",
    "PNP.NANDWireOpenCertificate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.physical_ownership",
    "3ed94e0bc4fff18f80da2ed5a796492e2c320c3cf028ac18cc6a6f61e18cdaed",
    "PNP.NANDWireOpenCertificate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.closed_ledger",
    "052af36b3ec051738c97181fbfe929297367ef4a5fa2066056b7299fceb0a461",
    "PNP.NANDWireOpenCertificate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.creation_lifecycle",
    "150b92266e1ffaff1bc2c238a570e17dcf21c2f1ffeba8912edab47fc0f68786",
    "PNP.NANDWireOpenCertificate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenCertificate.verify_exists_iff",
    "607dd11f68d99c899559f22b3de54a7da719c006b7bf5f6c31980c9a082b36b0",
    "PNP.NANDWireOpenCertificate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenCertificate.verify_sound",
    "614ff8c704c825a45e251875ff486386ac4e7c9c968a8da47a213bf8ce071994",
    "PNP.NANDWireOpenCertificate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenCertificate.verify_decode_none",
    "98f44c362e63209904315e4cb49ab0888848f3354629b75e38b89a6ee853ec41",
    "PNP.NANDWireOpenCertificate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenCertificate.verify_program_none",
    "590354c6341019bdcf9ed9d6dc48f45d703a8cc7dc4825820714a1cbb46d73aa",
    "PNP.NANDWireOpenCertificate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenCertificate.verify_not_proper",
    "38f9ab062e770785bfd5f6ea282de7061e1dd1b1a8d2a787e51f52cbe212be62",
    "PNP.NANDWireOpenCertificate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenCertificate.verify_no_gain",
    "e4b610ddb95904ac15f56a5426179f601c7bbda8394423a0b6a8ee5d99ebeb49",
    "PNP.NANDWireOpenCertificate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.Transition.charged_eq",
    "582b965b392cbc1cf45464dca92b57b3a2d6f4f60df828d2587f4e290c73134e",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.Transition.removed_eq",
    "4984f8ac769eb86a56fe34136572428de242317a17b8b407150f7ebe4d49c8e2",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.Transition.causalInvariant",
    "2983a548ee9035eecf6401bb87dbb74eed55ba77c8470dbfa596155e65c833f7",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.Transition.local_physical_ownership",
    "058766b012a2a8c0127b27d8da2cbc11b9d5b1dc246a05d2a3932d1bab773f31",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.gate_balance",
    "7a8f96270f3ca4f981f6bb2f38f5af353346b02300932f5b24ee05e5f8804c71",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ]
];
const MILESTONE = {
  "classification": "formalized-foundation-only",
  "id": "computational-recoding-program-integration",
  "nonClaim": "This checks offered computational programs, not a successful certificate-discovery strategy for every input. The inverse checker enumerates all field valuations; finite termination and a bounded structural swap list do not establish uniformly polynomial encoded runtime or certificate size. Semantic reversibility does not imply physical cancellation or strict saving. Full manuscript profiles, all R1-R9 and N1-N10 rules, full VerifyDW, ChargeSoundness and Package E remain open. Terminal-family derivation, global route coverage, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin, deterministic CNFSAT in P and the eligible root remain open. No fixed weighted checkpoint or global proof gate closes, and P = NP is not proved.",
  "requiredTheorems": [
    "PNP.DirectWire.StructuralReindexing.GateRenaming.decode_encode",
    "PNP.DirectWire.StructuralReindexing.GateRenaming.encode_length_le",
    "PNP.DirectWire.StructuralReindexing.GateRenaming.validCode_encode",
    "PNP.DirectWire.WireCarrierRecoding.roundTripCheck_iff",
    "PNP.DirectWire.WireCarrierRecoding.check_iff",
    "PNP.DirectWire.WireCarrierRecoding.compile_success_iff",
    "PNP.DirectWire.WireCarrierRecoding.appendMap_gateCount",
    "PNP.DirectWire.WireCarrierRecoding.appendMap_output",
    "PNP.DirectWire.WireCarrierRecoding.appendMap_field",
    "PNP.DirectWire.WireCarrierRecoding.encoded_output",
    "PNP.DirectWire.WireCarrierRecoding.encoded_field",
    "PNP.DirectWire.WireCarrierRecoding.result_output",
    "PNP.DirectWire.WireCarrierRecoding.result_field",
    "PNP.DirectWire.WireCarrierRecoding.result_gate_balance",
    "PNP.DirectWire.CausalBound.levels_bounded_iff",
    "PNP.DirectWire.CausalBound.source_bounded_iff",
    "PNP.DirectWire.CausalBound.sourceDependencyGuard_iff",
    "PNP.DirectWire.CausalBound.candidateDependencyGuard_iff",
    "PNP.DirectWire.WireCarrier.dependencyGuard_iff",
    "PNP.DirectWire.WireObligationHistory.State.recode_pending",
    "PNP.DirectWire.WireObligationHistory.State.recode_charged",
    "PNP.DirectWire.WireObligationHistory.State.recode_removed",
    "PNP.DirectWire.WireObligationHistory.State.recode_causalInvariant",
    "PNP.DirectWire.WireRecodingState.execute_success_iff",
    "PNP.DirectWire.WireRecodingState.execute_failure_iff",
    "PNP.DirectWire.WireRecodingState.Receipt.pending",
    "PNP.DirectWire.WireRecodingState.Receipt.causalInvariant",
    "PNP.DirectWire.WireRecodingState.Receipt.gate_balance",
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.encoder_positions",
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.encoded_origin",
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.decoder_positions",
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.ledger_origin",
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.ledger_charged",
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.ledger_removed_length",
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.ledger_partition",
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.allocation_phases_nodup",
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.physical_ownership",
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.labelled_live",
    "PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.labelled_physical_ownership",
    "PNP.DirectWire.WireRecodingState.Receipt.physical_ownership",
    "PNP.DirectWire.WireRecodingInput.decode_encode",
    "PNP.DirectWire.WireRecodingInput.decode_elaboration_none",
    "PNP.DirectWire.WireRecodingInput.decode_success_iff",
    "PNP.DirectWire.WireRecodingInput.execute_success_iff",
    "PNP.DirectWire.WireRecodingInput.execute_encoder_none",
    "PNP.DirectWire.WireRecodingInput.execute_decoder_none",
    "PNP.DirectWire.WireRecodingInput.Receipt.pending",
    "PNP.DirectWire.WireRecodingInput.Receipt.charged_eq",
    "PNP.DirectWire.WireRecodingInput.Receipt.removed_eq",
    "PNP.DirectWire.WireRecodingInput.Receipt.causalInvariant",
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_origin",
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_charged",
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_removed",
    "PNP.DirectWire.WireOpenProgram.orderEvents_success_iff",
    "PNP.DirectWire.WireOpenProgram.orderEvents_failure_iff",
    "PNP.DirectWire.WireOpenProgram.execute_failed_tail",
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.full_output",
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.full_field",
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.creation_lifecycle",
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.executed_count",
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.executed_identities_nodup",
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.causalInvariant",
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.physical_ownership",
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_origin_injective",
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_charge_origin",
    "PNP.DirectWire.WireOpenProgram.compile_exists_iff",
    "PNP.DirectWire.WireOpenProgram.compile_none_iff",
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.records_source",
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.proper_support",
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.output",
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.field",
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.charge_accounting",
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictGain",
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictResidualDescent",
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.physical_ownership",
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.closed_ledger",
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.creation_lifecycle",
    "PNP.DirectWire.WireOpenCertificate.verify_exists_iff",
    "PNP.DirectWire.WireOpenCertificate.verify_sound",
    "PNP.DirectWire.WireOpenCertificate.verify_decode_none",
    "PNP.DirectWire.WireOpenCertificate.verify_program_none",
    "PNP.DirectWire.WireOpenCertificate.verify_not_proper",
    "PNP.DirectWire.WireOpenCertificate.verify_no_gain",
    "PNP.DirectWire.WireOpenProgram.Transition.charged_eq",
    "PNP.DirectWire.WireOpenProgram.Transition.removed_eq",
    "PNP.DirectWire.WireOpenProgram.Transition.causalInvariant",
    "PNP.DirectWire.WireOpenProgram.Transition.local_physical_ownership",
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.gate_balance"
  ],
  "scope": "For arbitrary finite computational wire carriers, literal NAND encoder and decoder circuits, dependency graphs and complete offered replacement programs, raw recoding actions reuse the existing circuit format and validate both dimensions and every gate and output reference. A complete finite check derives both inverse equations. An independent exact syntactic dependency guard covers all ordinary outputs and hidden fields for every natural-valued input labelling. Actual encoder and decoder gates are appended, normalized and charged; actual compiler maps determine deletions and disjoint allocation identities. Recoding retains the entire pending snapshot function and cannot create or discharge an obligation. Complete-program execution lifts those physical identities through prior history, preserves full semantics, costs, causal invariants and creation-to-discharge bindings, and rejects an invalid later action rather than accepting a prefix. The proper-support certificate verifier still requires complete execution, a closed final ledger and strict actual saving. The existing structural decoder also has a constructive exact encoding of every finite gate bijection with at most one swap per gate. Callers supply raw data, not correctness, causal, ordering, ownership or cost authority.",
  "title": "Computational recoding in complete source-only replacement programs"
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

test('M272 compiled interface: exact types, modules and axiom closures earn only the reviewed row', async () => {
  const {inventory, map, inventoryBytes, sourceClosure} = await sources0();
  assert.ok(canonical0(inventory).equals(inventoryBytes));
  const names = REVIEWED.map(row => row[0]);
  assert.equal(names.length, 88);
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

test('M272 compiled interface: weakening or supplying a conclusion cannot retain credit', async () => {
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
  // causal semantics, global physical accounting and complete verification.
  for (const name of [
    'PNP.DirectWire.WireCarrier.dependencyGuard_iff',
    'PNP.DirectWire.WireRecodingState.Receipt.physical_ownership',
    'PNP.DirectWire.WireOpenCertificate.verify_sound',
  ]) for (const kernelType of alternatives.get(name)) {
    const mutation = {...inventory, milestoneCandidates: inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), sourceClosure);
    assert.equal(result.milestones.find(row => row.id === MILESTONE.id).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
});

test('M272 compiled interface: missing evidence, added authority and widened scope reject', async () => {
  const {inventory, inventoryBytes, map, sourceClosure} = await sources0();
  const name = 'PNP.DirectWire.WireRecodingState.Receipt.physical_ownership';
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
      ? {...row, [field]: 'The verifier discovers a successful uniformly polynomial certificate for every input.'} : row)};
    assert.throws(() => DeriveFormalPublication0(inventory, widened, inventoryBytes, sourceClosure),
      /map drifted from the reviewed specification/u);
  }
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256: {
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]: '0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, inventoryBytes, sourceClosure),
    /map drifted from the reviewed specification/u);
});

const META = {
  "coordinate": "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-18-272",
  "statusFields": {
    "leanComputationalRecodingFormalized": true,
    "leanComputationalRecodingAxiomAuditPassed": true,
    "leanComputationalRecodingAuditedDeclarationCount": 88,
    "leanComputationalRecodingStructuralExactEncodingTheorem": "PNP.DirectWire.StructuralReindexing.GateRenaming.decode_encode",
    "leanComputationalRecodingStructuralEncodingLengthTheorem": "PNP.DirectWire.StructuralReindexing.GateRenaming.encode_length_le",
    "leanComputationalRecodingLiteralInverseCheckTheorem": "PNP.DirectWire.WireCarrierRecoding.check_iff",
    "leanComputationalRecodingLiteralGateBalanceTheorem": "PNP.DirectWire.WireCarrierRecoding.result_gate_balance",
    "leanComputationalRecodingCausalGuardTheorem": "PNP.DirectWire.WireCarrier.dependencyGuard_iff",
    "leanComputationalRecodingPendingSnapshotTheorem": "PNP.DirectWire.WireObligationHistory.State.recode_pending",
    "leanComputationalRecodingLocalPhysicalOwnershipTheorem": "PNP.DirectWire.WireRecodingState.Receipt.physical_ownership",
    "leanComputationalRecodingRawDecodeRoundTripTheorem": "PNP.DirectWire.WireRecodingInput.decode_encode",
    "leanComputationalRecodingRawAcceptanceTheorem": "PNP.DirectWire.WireRecodingInput.execute_success_iff",
    "leanComputationalRecodingCompleteProgramGateBalanceTheorem": "PNP.DirectWire.WireOpenProgram.CompiledProgram.gate_balance",
    "leanComputationalRecodingCompleteProgramLifecycleTheorem": "PNP.DirectWire.WireOpenProgram.CompiledProgram.creation_lifecycle",
    "leanComputationalRecodingCompleteProgramPhysicalOwnershipTheorem": "PNP.DirectWire.WireOpenProgram.CompiledProgram.physical_ownership",
    "leanComputationalRecodingCompleteCertificateSoundnessTheorem": "PNP.DirectWire.WireOpenCertificate.verify_sound",
    "leanComputationalRecodingStrictResidualDescentTheorem": "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictResidualDescent",
    "leanComputationalRecodingExistingRawCodecReused": true,
    "leanComputationalRecodingBothDimensionsChecked": true,
    "leanComputationalRecodingCompleteLiteralRecodersRequired": true,
    "leanComputationalRecodingBothFullInverseEquationsChecked": true,
    "leanComputationalRecodingAllInputCausalLabelsChecked": true,
    "leanComputationalRecodingOrdinaryOutputsAndHiddenFieldsCovered": true,
    "leanComputationalRecodingExactPendingSnapshotsPreserved": true,
    "leanComputationalRecodingLiteralEncoderDecoderGatesCharged": true,
    "leanComputationalRecodingActualNormalizerDeletionMapsUsed": true,
    "leanComputationalRecodingDerivedEncoderDecoderAllocationPhases": true,
    "leanComputationalRecodingHistoricalChargesAndOwnersPreserved": true,
    "leanComputationalRecodingCompleteAcceptedProgramRequired": true,
    "leanComputationalRecodingClosedFinalLedgerRequired": true,
    "leanComputationalRecodingProperSupportRequired": true,
    "leanComputationalRecodingStrictSignedSavingRequired": true,
    "leanComputationalRecodingCallerSuppliedCorrectnessOrderCausalOrOwnerWitnessRequired": false,
    "leanComputationalRecodingRecodingDischargesOpenObligations": false,
    "leanComputationalRecodingSemanticReversibilityImpliesPhysicalCancellation": false,
    "leanComputationalRecodingSemanticReversibilityAloneEarnsSaving": false,
    "leanComputationalRecodingInverseCheckEnumeratesAllFieldValuations": true,
    "leanComputationalRecodingFullManuscriptProfileSemanticsProved": false,
    "leanComputationalRecodingAllRecodingAndNormalizationRulesProved": false,
    "leanComputationalRecodingFullManuscriptVerifyDWProved": false,
    "leanComputationalRecodingCompleteChargeSoundnessAndPackageEProved": false,
    "leanComputationalRecodingGlobalCertificateDiscoveryProved": false,
    "leanComputationalRecodingTerminalFamiliesDerived": false,
    "leanComputationalRecodingGlobalRouteCoverageProved": false,
    "leanComputationalRecodingUnconditionalSaturatePositiveProved": false,
    "leanComputationalRecodingUnconditionalBCELReadyProved": false,
    "leanComputationalRecodingUnconditionalZeroSlackProved": false,
    "leanComputationalRecodingExactGeneralPCCMinProved": false,
    "leanComputationalRecodingPolynomialRuntimeOutputAndCertificateBoundsProved": false,
    "leanComputationalRecodingRuntimeExecutionIsProofAuthority": false,
    "leanComputationalRecodingScope": "arbitrary-finite-source-only-complete-programs-existing-raw-codec-both-literal-recoders-exact-inverse-and-syntactic-causal-checks-pending-snapshots-actual-allocations-deletions-and-global-ownership-closed-ledger-proper-support-strict-saving-no-global-discovery-full-manuscript-or-polynomial-claim"
  },
  "command": "node --test audits/lean-computational-recoding0.test.mjs audits/lean-computational-recoding-publication0.test.mjs",
  "testFiles": [
    "audits/lean-computational-recoding0.test.mjs",
    "audits/lean-computational-recoding-publication0.test.mjs"
  ],
  "audit": "lean-audit/PNPComputationalRecodingAxiomAudit.lean",
  "parts": [
    "GateRenamingEncoding",
    "WireCarrierRecoding",
    "WireRecodingState",
    "WireRecodingOwnership",
    "WireRecodingInput",
    "WireRecodingProgram",
    "WireRecodingCertificate"
  ],
  "workflowCommands": "set -euo pipefail\nnode scripts/check-lean-axioms.mjs lean-audit/PNPComputationalRecodingAxiomAudit.lean\nfor part in GateRenamingEncoding WireCarrierRecoding WireRecodingState WireRecodingOwnership WireRecodingInput WireRecodingProgram WireRecodingCertificate; do\n  lake env lean -DwarningAsError=true \"lean-regression/PNP${part}.lean\"\ndone\n",
  "publicationDecision": "Publication decision: defer. This extends checked offered computational replacement programs with literal recoding, but does not establish global certificate discovery, full manuscript profiles or a polynomial algorithm. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.",
  "rationale": "M272 integrates literal computational recoding into complete source-only replacement programs and proper-support verification. The existing raw codec checks both actual circuits and dimensions; computed inverse and syntactic dependency checks cover full fields and arbitrary causal labels. Real additions, deletions and derived encoder/decoder allocation identities remain in the complete historical ledger, and pending snapshots survive until actual restoration. Complete execution, final closure and strict saving remain mandatory. A constructive structural-code completeness theorem supports the existing route. This retires a computational integration edge, not full manuscript profiles, all rules, global discovery, unconditional residual theorems or polynomial bounds. The inverse check remains exhaustive over field valuations. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.",
  "doc": "docs/lean_computational_recoding.md",
  "plan": "docs/plans/2026-09-18-computational-recoding-integration.md"
};
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();
async function release0() {
  const [statusText, progressText] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('status/PROOF_PROGRESS.json'),
  ]);
  return {status: JSON.parse(statusText), progress: JSON.parse(progressText)};
}

test('M272 release preflight: package, exact workflow and status commands share one interface', async () => {
  const [pkg, surface, verifier, workflow, statusSource, statusText] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'), text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'), text0('pcc-formal-reconstruction-status0.mjs'),
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  ]);
  assert.equal(JSON.parse(pkg).scripts['audit:m272'], META.command);
  assert.ok(surface.includes("'audit:m272': '" + META.command + "'"));
  for (const file of META.testFiles) assert.ok(verifier.includes("'" + file + "'"), file);
  assert.ok(workflow.includes('run: npm run audit:m272'));
  const steps = workflow.split(/^      - name:/mu).filter(step =>
    step.includes('node scripts/check-lean-axioms.mjs ' + META.audit));
  assert.equal(steps.length, 1);
  const block = steps[0].split('        run: |\n')[1];
  assert.ok(block);
  assert.equal(block.trimEnd().split('\n').map(line => line.slice(10)).join('\n') + '\n', META.workflowCommands);
  const status = JSON.parse(statusText);
  for (const command of [
    'npm run audit:m272', 'node scripts/check-lean-axioms.mjs ' + META.audit,
    ...META.parts.map(part => 'lake env lean -DwarningAsError=true lean-regression/PNP' + part + '.lean'),
  ]) assert.ok(status.verificationCommands.includes(command), command);
  for (const field of Object.keys(META.statusFields))
    assert.equal(statusSource.split(field + ':').length - 1, 2, field);
});

test('M272 release: status pins the exact bounded claims and rejects every changed field', async () => {
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

test('M272 release: computational integration earns no unconditional checkpoint', async () => {
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

test('M272 release: every current summary and FAQ uses the canonical independent metrics', async () => {
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
      assert.ok(boundary?.includes('M272'));
      assert.ok(boundary.includes('global certificate discovery'));
    }
    if (['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
      'docs/proof_pipeline.md', 'docs/audit_questions.md'].includes(file)) {
      const region = text.split('<!-- M272-CURRENT-SUMMARY:BEGIN -->')[1]?.split('<!-- M272-CURRENT-SUMMARY:END -->')[0];
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
