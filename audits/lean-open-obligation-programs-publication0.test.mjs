import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  DeriveFormalPublication0, MilestoneTheoremKernelTypeSha2560,
  REQUIRED_MILESTONE_THEOREMS0, stableStringify0,
} from '../formal-publication0.mjs';
import {CheckFormalReconstructionStatus0} from '../pcc-formal-reconstruction-status0.mjs';
import {validateProofProgress0} from '../pcc-proof-progress0.mjs';

// Exact compiled type, module and axiom pins frozen after root review.
// These expectations are never recomputed by the tests being run.
const REVIEWED = [
  [
    "PNP.DirectWire.WireOpenSupportSplice.transfer_pending",
    "f372417d21745a89b9fe060a0bb5e7f94293cea45e5110523db2d4c13e25197a",
    "PNP.NANDWireOpenSupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.transfer_keep",
    "f4d1ebc59477a545c6cd2b2f515e48c351bc67520e95074526933444e85d8bfa",
    "PNP.NANDWireOpenSupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.transfer_snapshot",
    "a3452719777d8c5629dbd41665e8a04ed60a7bdff93dc74ed58ee0b950f9e417",
    "PNP.NANDWireOpenSupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.transfer_charge",
    "db627ea92a89b3c7884615ffeab0f9d7f284d340f0ad4448156e7577c68e6968",
    "PNP.NANDWireOpenSupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.transfer_removal",
    "a4b880c172be2674e8af5454f6ea02223ca41883cfe3cb4f732830b0cfdfdb50",
    "PNP.NANDWireOpenSupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.transfer_output",
    "f8b7dc12ec7b3924e040c3d2ca45c056cd7535240071a6cd26ebd2386c8d5110",
    "PNP.NANDWireOpenSupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.transfer_available",
    "eeabd992f318656b0f9025943e3d89965be898046177f351f2c82a648edd5147",
    "PNP.NANDWireOpenSupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.transfer_balance",
    "415774cc05f6e62627165a12c8efca6b29bc49c70724c5e25bd67c342d679386",
    "PNP.NANDWireOpenSupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.replacement_dependency_bound",
    "1229d727b2d0ef3cb00585f0471b4adcfd6bd1ca89cacc985f21a4c5dad88f9e",
    "PNP.NANDWireOpenSupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.result_exposed_dependency_bound",
    "f9c5feb923940e0a9e50dc5d12805ea506f3914c5e2c8fca7ad3f311206c42df",
    "PNP.NANDWireOpenSupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.result_causal_bounds",
    "93eda0ab5098dc003f718864eca040b42241ad22ab71a7505dade0535b617c7f",
    "PNP.NANDWireOpenSupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.transfer_causal_invariant",
    "c53a9094b0d744a8b49e1ac8a1ee4a5e32ee602cd31a93e9c1d15d74ff259037",
    "PNP.NANDWireOpenSupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.Receipt.pending",
    "7ddac25e74caf583040e4ccb1912d6db3dd4c952ea4056287d24f575ad4dfd45",
    "PNP.NANDWireOpenSupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.Receipt.records_source",
    "10d6e44867eff3915845ffac22c3a343f6f0a65ea11c686a62c6299d7a9673f6",
    "PNP.NANDWireOpenSupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.execute_of_compiled",
    "05922b248891616eff08fd765b5f9a767a985b85274170e23a06aa9d46e0b621",
    "PNP.NANDWireOpenSupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.execute_exists_iff",
    "3fd039ec2a4f844c4b70efe4470702b8dca68971f2f627272cdaaddfcd2074f9",
    "PNP.NANDWireOpenSupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.uniqueIDs_iff",
    "c71214b5ee8b3df62bea207eae053840d658c6d347f89d2b50f5abdd7ee4ef76",
    "PNP.NANDWireOpenProgramInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.completeReferences_iff",
    "78ad2da547dcdf0ab8b5b7e79f7028a70d9741f41459e65e9a605ca756f6f030",
    "PNP.NANDWireOpenProgramInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.graph_dependency_iff",
    "56b89269cc7546658ffa4f4851b39fa69d239b3e09d53f97574f5a3c0f165697",
    "PNP.NANDWireOpenProgramInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.OrderedEvents.order_complete",
    "a7cc293b2886172a144d5829a620b1b71b4b47da4684c00495e61c7d6eea5ee3",
    "PNP.NANDWireOpenProgramInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.OrderedEvents.order_nodup",
    "e103f022f41d712d4e8bed2e28de6ffcebbe9302ad723abb6822a7449b93b3b7",
    "PNP.NANDWireOpenProgramInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.OrderedEvents.order_length",
    "7c48b4c7e7d4371bd310d01d3439c1f47c9e29def61e88b985e6a04e20af16d7",
    "PNP.NANDWireOpenProgramInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.OrderedEvents.identities_nodup",
    "daabddde5a7c7413c681e6665d0439bbeebdc5bd54521d472f2a17be84759e10",
    "PNP.NANDWireOpenProgramInput",
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
    "PNP.DirectWire.WireOpenProgram.Transition.dischargeRecord_binding",
    "a4eaacd84ac35fe897205f2c097c29b34c456bc71ca1b2c0302c7a60b50d027d",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.Transition.pending_persists_or_discharged",
    "b3fcc96b8e3aff3cf491ba2b9117fcc3831f833aa02245f17a71b580477824d8",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.Transition.created_pending",
    "967058b875d619d926a8d9999915517441ae84d3a5bde0acb22b97cbb1223b9c",
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
    "PNP.DirectWire.WireOpenProgram.execute_failed_tail",
    "c852f45d97e5d2309875f6ba6f2a62aa22f4293c81781f6d7df84cae93f2bb72",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.Execution.total_charge",
    "0c1b5faf2041cf7f8ff151ac6e640c57f1c5b0eea97faabe3c37a1a4dcd58a72",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.Execution.total_removed",
    "99cad8313b84834312ea8134fbffe072ef5915daf487d1a7fd658905a110b3a1",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.Execution.record_identities",
    "a216f913c1d3336159ba0a569016311638a0d4bf0bc8ece7237085abfa42fe9c",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.Execution.pending_persists_or_discharged",
    "030586def8ed0c04b78ef370eb374c29d80828c4e5adbd0e2b47cf99ca8e652a",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.Execution.creationsClosed_of_finalClosed",
    "432a30f13d8db52b91fea97fd2b602b25d7976144df1f2f24d3b49213d8866e6",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.Execution.causalInvariant",
    "6164f04d9db3b241b5be62fac65b7e2ed3492495c13687d47107645c028c5491",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.closed",
    "7b26384b374bbc5553bb704731398cd8d0d55acfa4080ac2538ea6d4a0120c1b",
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
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.gate_balance",
    "7a8f96270f3ca4f981f6bb2f38f5af353346b02300932f5b24ee05e5f8804c71",
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
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.dependency_before",
    "4be753b9b631255f74322b73bb8040366356630761f975e5a0eb4ddf08ce4f6f",
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
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.output_causal_bound",
    "dd90ee103df10fd0c8608b36b5acf2f05aa4ee4226b2e97741f42dd543d9977e",
    "PNP.NANDWireOpenProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.field_causal_bound",
    "685e7317438c9f54dfb261ac77516aa574341059718d1f31ccf2af1f802c8e25",
    "PNP.NANDWireOpenProgram",
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
    "PNP.DirectWire.WireOpenSupportSplice.ownershipLift_original",
    "0b669f52b59c9716599f175f9a4f27eae3c0286542100b22caf0b4c5d3884dd2",
    "PNP.NANDWireOpenSupportOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.ownershipLift_allocated",
    "0c7bee0cf6f1cd8a64587d2433e0ccb455d36ff6cf71a6de4a07d800cfbdbfdf",
    "PNP.NANDWireOpenSupportOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.ownershipLift_injective",
    "61c989236791367321894954f89e6c73d994d7c87bf81e51b2ced3eda992f54a",
    "PNP.NANDWireOpenSupportOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.ownershipRawNode_exterior",
    "db8cdcf39188fca68478a037f57eb00ee7304d346bd6db2b4cebe571ff47d552",
    "PNP.NANDWireOpenSupportOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.ownershipRawNode_nested",
    "662f92996388bf47107cf532453da1b008f31377ed985c98651472fb9e3f5345",
    "PNP.NANDWireOpenSupportOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.ownership_compiled_position",
    "6de0fd62d4b50f5d1495c6fa3813760bbefbe407e72c0148b191c0ad59f6bf0c",
    "PNP.NANDWireOpenSupportOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.ownership_partition",
    "fc28ded9671c32b471adab23c27486cf919dfeb9a9625705d15d78e7462f8d5c",
    "PNP.NANDWireOpenSupportOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.ownership_charged_origin",
    "4eb89c2011b53d30390d8440a9076e176918947330e63d9f66b8d25a82cdba0f",
    "PNP.NANDWireOpenSupportOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.ownership_distinct",
    "f77f828a20951b51cff548fa9c326baaada397eb04a8ee33e900fc5b9af79eb3",
    "PNP.NANDWireOpenSupportOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.physical_ownership",
    "d30dab26939ac05fe1d2f639aa558b97f6d69fb05173c385b3683bea39618010",
    "PNP.NANDWireOpenSupportOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenSupportSplice.Receipt.physical_ownership",
    "2810be93835d937edd3875e1ccb1aa1bf147c2808d3937b62e0be97228f0976f",
    "PNP.NANDWireOpenSupportOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.allocations_nodup",
    "e83d36b50dd0758b773d24e3d6cb3031282a5204875817d5d392ee23f72b3a2a",
    "PNP.NANDWireOpenPrimitiveOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.advance_charged",
    "28648d85742cf32a94a05b70580e47f99c897b51b03d015a754255d964e0b41b",
    "PNP.NANDWireOpenPrimitiveOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.advance_removed_length",
    "d5f6020268922f937b3a6cfba269609d0fbbc8b4a03f2a703d6ed49ad54fb475",
    "PNP.NANDWireOpenPrimitiveOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.advance_conservation",
    "936b1571f8c7ce40b79baa5697f5e62256a1d5a709559241601e3eb3e15ddfda",
    "PNP.NANDWireOpenPrimitiveOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.ledger_charged",
    "df2b4ca6a19d0e93687eddef7feaa1a638372450d89958a399b8041ec6d02ac3",
    "PNP.NANDWireOpenPrimitiveOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.ledger_removed_length",
    "d0ea00e4f88913156fa0cb36279e50c5ae3d852a22fa5f58525705a0a2f832cd",
    "PNP.NANDWireOpenPrimitiveOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.ledger_partition",
    "2b47c63a27b4350495055444272787dc31367b2bf9e7199e925ba6d8644bca67",
    "PNP.NANDWireOpenPrimitiveOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.physical_ownership",
    "adb103128984ee8af09e808a8cf7814cdb2043e151d211ad93041635ef99ef47",
    "PNP.NANDWireOpenPrimitiveOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.lift_injective",
    "3c84c3607b489f321b269bec75f7e73471435d0d7d8734ddf9b1a9e1fa3799e3",
    "PNP.NANDWireOpenPrimitiveOwnership",
    []
  ],
  [
    "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.labelled_live",
    "82c1e2ed984a1cdd7d37c4d835f018282f3be9c8b767de1a4339a50ef1c13433",
    "PNP.NANDWireOpenPrimitiveOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.labelled_physical_ownership",
    "64b2fa619414d0ed84eec3a7c76701c2487158a8a0a776ae132dc75552cbbc94",
    "PNP.NANDWireOpenPrimitiveOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.labelled_charged_origin",
    "aa224c8b37dfc598434568994620be9b35c926656bad7f9e935f533cc91525fb",
    "PNP.NANDWireOpenPrimitiveOwnership",
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
    "PNP.DirectWire.WireOpenProgram.Transition.local_charged_origin",
    "2b1fad4a1389d5321b9e46e05a427b876c3cd95679dde6ec0a21093ad60fcc8d",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.bornBefore_mono",
    "113e782017300543ccf29c041154005e84a564b8ff7f68191da3103940f81235",
    "PNP.NANDWireOpenProgramOwnership",
    []
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.initial_wellFormed",
    "71768c17fb01c0a2ac9d4bf7d69572018d2de166eb090153df3dcb3f2efba065",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.accounted_before",
    "9759187eae9c674eae632d7140873ca0ee09aec3966f53354ca0cd3aa63446a5",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.origin_before",
    "7552a9e3fe16f3b742277ce89e10160cbf9690bc1975c694efd703de92f2def1",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.origin_injective",
    "145541d9f7fd6003f09a01056f7334589373bdd3cc88a5417af297d9c41f507d",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.liftOrigin_original",
    "089007a53df8b1f264f8f6448b413b270152c4708c246685a5ae3387d4bff5a2",
    "PNP.NANDWireOpenProgramOwnership",
    []
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.liftOrigin_allocated",
    "d4eaaeca8d1521b2d8abbaa4f153c0cb1f0a03c31df3db75eb52af6baa80de8e",
    "PNP.NANDWireOpenProgramOwnership",
    []
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.liftOrigin_injective",
    "367310a8716209063a8e9b09ca4df0cc3a60a42a7b0dc4e5fb66bf31a0a96fc2",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.lift_originals",
    "76409c5fe4b3e22497b6f73add0db4f454b217ded953e088c6e48ae13c2cb7f8",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_live",
    "eae14dc1a26ab11f4f657d2fa980f37c7160a271528f2cee5d002f00995dd563",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_charged_length",
    "56b57e7d723b0668224f8ebc24d9fb85535fbfa9187554b8e8ab167154051bee",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_removed_length",
    "f2a48a407b7a01330842a28a8452708cd0c535826b201dbfaf0fb40176e0a689",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_charge_origin",
    "61bf2fbdc9228936c06cb598a240476f7869f801310f11c1023d715731b64430",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_physical_position",
    "1f231b2c4cab4e26c4ed41b7ab6b4d60262c71249d0267d9c76cd4fcc1ffae26",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_support_compiled_position",
    "187d053258a8f2580077a5d63d927dc26463ca797b792665cd1c03605461f714",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_partition",
    "fdb3d1165f6986ae6f34ed985f184e57f84f8b36095667c5c7b5d36b66ef73fc",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_wellFormed",
    "b5c19467ce706bff313f7b956c0ce3cc85efe11c826437e1acf813cfb492ab8e",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_wellFormed",
    "a764a54155bd274991b0a1611fd906046f9ce8cc1ff9660a9dd005aa6972c07a",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_charged_length",
    "138a8a70adf31232ee58f1d9772ef84cd1e2a2ecd299b688aea0e3c7b19b1377",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_removed_length",
    "8f571745e46861b8dea5a5a9fb8d558af05b79141f0d851512dbf70756923807",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_charge_survives",
    "a6b83b7cc6f0dbc1c3834716a7942181bd331d3e4469601a9e9d71c7d0b7b81d",
    "PNP.NANDWireOpenProgramOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_wellFormed",
    "6c8728ec7154bb43063b51c20659ae4cd3aa9d0a495be0cb2c185afebd2f6ed8",
    "PNP.NANDWireOpenProgramOwnership",
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
    "PNP.DirectWire.WireOpenProgram.allocation_namespaces_disjoint",
    "505f7d85f2015e6988170ed47086be92e79c86e05650449ac3ae10752f2e5b14",
    "PNP.NANDWireOpenProgramOwnership",
    []
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.program_equivalent",
    "b8cbc4d9581543d1aa7a4604cdea171771dab8e771ba29005022623b917c68f4",
    "PNP.NANDWireOpenProperSupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.program_causalInterfaceBound",
    "2bddfaab20e7d8d5844559e4c368150692ea31fdcae67c2e5fddb341c9f51e4a",
    "PNP.NANDWireOpenProperSupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.program_compiles",
    "ed19fffb06005d66aafaf666a1d1cc12bf15b4743a812652e413d1defca5907f",
    "PNP.NANDWireOpenProperSupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.output",
    "f0951e07ccc9142df3eb23939ba79b60f7a1cf3c45fa8547c8e01daf67a06e87",
    "PNP.NANDWireOpenProperSupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.field",
    "32eec426117db30e6bbaff70656ea85d841e077a917cdfa98408c5cb1e0ed83a",
    "PNP.NANDWireOpenProperSupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.gateCount",
    "74b75b7429c832bc793e730356ba4ea4805bb061e8414787d337fed61b6253ba",
    "PNP.NANDWireOpenProperSupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.charge_accounting",
    "c6d88e093af61a052a5c41b351d86bfcb4ae7de1b35430611f30c0bce21fde82",
    "PNP.NANDWireOpenProperSupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.gain_iff_local_gain",
    "ba3714c9b14162e3b048013ec3dd1f2ea8adeff4eace64738f8148a1185777ed",
    "PNP.NANDWireOpenProperSupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.gain_iff_net_charges",
    "a79883157d9d1ee41553fc81fc57181c76220fbbcd480661d8ed73de1dbf8819",
    "PNP.NANDWireOpenProperSupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.strictGain",
    "e5ad464ee1ad8959aad168d83d5b3ffdff6c0cdca60a07c62f050e8eac95f900",
    "PNP.NANDWireOpenProperSupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.strictResidualDescent",
    "fdccf1d460287438df33f6219bc51fd213599a75fdd6005dadee2b702eceaf6e",
    "PNP.NANDWireOpenProperSupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.compile_complete",
    "36aecca96533d3f2d287eac8e19d27862d419199e46721f818e5f8b0793870ac",
    "PNP.NANDWireOpenProperSupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.compile_exists_iff",
    "a9999609bd80ecf99878cbb8240fa23aa15160d9810c59ae070e52553e1ff824",
    "PNP.NANDWireOpenProperSupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.compile_none_iff",
    "ce3305941b2274389db4ca531b8a3914972ba80abaf1ddc746d9049ba49d8adb",
    "PNP.NANDWireOpenProperSupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.ownershipLift_original",
    "6c22c92f022cdf84f78bb4deb2421eec8d0941ff035725100b1b06e775647e7d",
    "PNP.NANDWireOpenProperOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.ownershipLift_allocated",
    "7599b1d46112b3db063e3c96a4f2b4f2053ea42a235231fcd6b70a308328047a",
    "PNP.NANDWireOpenProperOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.ownershipLift_injective",
    "e4b64c1e38eef48978a7d440b438a0ab3f1681475744e9903568c04c40621b94",
    "PNP.NANDWireOpenProperOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.ownershipRawNode_exterior",
    "c414f9cc4cd89e86a9f54a08670eb8c8f3e9b22610f7b7d9b2aca87538c66d19",
    "PNP.NANDWireOpenProperOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.ownershipRawNode_program",
    "7c2d8f1110e45c103b34f3f634b6023f4ffdfc5da625e39b757ede62a927b364",
    "PNP.NANDWireOpenProperOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.ownership_compiled_position",
    "4abe62f2e981cde7f65bbb5e2892d54c9bd9437e1e1550bba7b9f8951a0d8fe2",
    "PNP.NANDWireOpenProperOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.ownership_partition",
    "a9ea76a2fb6679f71a8c213e3fe9fbfd39db8315478ca81bd7936492ee9f2b7f",
    "PNP.NANDWireOpenProperOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.ownership_charged_origin",
    "58519cdb8933f1fae512f96d0e31e46a844b7ad5c838d14876d215874937f23d",
    "PNP.NANDWireOpenProperOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.ownership_distinct",
    "34e80f1c5e9e2380e14e996ec395a245883673174344cc4bf858ac6aaefc086d",
    "PNP.NANDWireOpenProperOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireOpenProperSupport.physical_ownership",
    "f6d2776fa9f728a235ee3a9b6390754b6a3dabdc0cc3a675f2dc0475bc5777c6",
    "PNP.NANDWireOpenProperOwnership",
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
    "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.gateCount",
    "4fb6d4c3d7404d438d05a46814fbb8795c9ca21aea0fcd216bb537d393a90fe4",
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
    "PNP.DirectWire.WireOpenCertificate.verify_complete",
    "b1821ca8840e2117ba56d88abb4560d1a2cc1edd22bec2da09f03aed6130c929",
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
  ]
];

const META = {
  "coordinate": "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-17-269",
  "milestone": {
    "classification": "formalized-foundation-only",
    "id": "open-obligation-programs",
    "title": "Open obligations across complete descendant-support programs",
    "requiredTheorems": [
      "PNP.DirectWire.WireOpenSupportSplice.transfer_pending",
      "PNP.DirectWire.WireOpenSupportSplice.transfer_keep",
      "PNP.DirectWire.WireOpenSupportSplice.transfer_snapshot",
      "PNP.DirectWire.WireOpenSupportSplice.transfer_charge",
      "PNP.DirectWire.WireOpenSupportSplice.transfer_removal",
      "PNP.DirectWire.WireOpenSupportSplice.transfer_output",
      "PNP.DirectWire.WireOpenSupportSplice.transfer_available",
      "PNP.DirectWire.WireOpenSupportSplice.transfer_balance",
      "PNP.DirectWire.WireOpenSupportSplice.replacement_dependency_bound",
      "PNP.DirectWire.WireOpenSupportSplice.result_exposed_dependency_bound",
      "PNP.DirectWire.WireOpenSupportSplice.result_causal_bounds",
      "PNP.DirectWire.WireOpenSupportSplice.transfer_causal_invariant",
      "PNP.DirectWire.WireOpenSupportSplice.Receipt.pending",
      "PNP.DirectWire.WireOpenSupportSplice.Receipt.records_source",
      "PNP.DirectWire.WireOpenSupportSplice.execute_of_compiled",
      "PNP.DirectWire.WireOpenSupportSplice.execute_exists_iff",
      "PNP.DirectWire.WireOpenProgram.uniqueIDs_iff",
      "PNP.DirectWire.WireOpenProgram.completeReferences_iff",
      "PNP.DirectWire.WireOpenProgram.graph_dependency_iff",
      "PNP.DirectWire.WireOpenProgram.OrderedEvents.order_complete",
      "PNP.DirectWire.WireOpenProgram.OrderedEvents.order_nodup",
      "PNP.DirectWire.WireOpenProgram.OrderedEvents.order_length",
      "PNP.DirectWire.WireOpenProgram.OrderedEvents.identities_nodup",
      "PNP.DirectWire.WireOpenProgram.orderEvents_success_iff",
      "PNP.DirectWire.WireOpenProgram.orderEvents_failure_iff",
      "PNP.DirectWire.WireOpenProgram.Transition.charged_eq",
      "PNP.DirectWire.WireOpenProgram.Transition.removed_eq",
      "PNP.DirectWire.WireOpenProgram.Transition.dischargeRecord_binding",
      "PNP.DirectWire.WireOpenProgram.Transition.pending_persists_or_discharged",
      "PNP.DirectWire.WireOpenProgram.Transition.created_pending",
      "PNP.DirectWire.WireOpenProgram.Transition.causalInvariant",
      "PNP.DirectWire.WireOpenProgram.execute_failed_tail",
      "PNP.DirectWire.WireOpenProgram.Execution.total_charge",
      "PNP.DirectWire.WireOpenProgram.Execution.total_removed",
      "PNP.DirectWire.WireOpenProgram.Execution.record_identities",
      "PNP.DirectWire.WireOpenProgram.Execution.pending_persists_or_discharged",
      "PNP.DirectWire.WireOpenProgram.Execution.creationsClosed_of_finalClosed",
      "PNP.DirectWire.WireOpenProgram.Execution.causalInvariant",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.closed",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.full_output",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.full_field",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.gate_balance",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.creation_lifecycle",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.executed_count",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.executed_identities_nodup",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.dependency_before",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.causalInvariant",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.output_causal_bound",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.field_causal_bound",
      "PNP.DirectWire.WireOpenProgram.compile_exists_iff",
      "PNP.DirectWire.WireOpenProgram.compile_none_iff",
      "PNP.DirectWire.WireOpenSupportSplice.ownershipLift_original",
      "PNP.DirectWire.WireOpenSupportSplice.ownershipLift_allocated",
      "PNP.DirectWire.WireOpenSupportSplice.ownershipLift_injective",
      "PNP.DirectWire.WireOpenSupportSplice.ownershipRawNode_exterior",
      "PNP.DirectWire.WireOpenSupportSplice.ownershipRawNode_nested",
      "PNP.DirectWire.WireOpenSupportSplice.ownership_compiled_position",
      "PNP.DirectWire.WireOpenSupportSplice.ownership_partition",
      "PNP.DirectWire.WireOpenSupportSplice.ownership_charged_origin",
      "PNP.DirectWire.WireOpenSupportSplice.ownership_distinct",
      "PNP.DirectWire.WireOpenSupportSplice.physical_ownership",
      "PNP.DirectWire.WireOpenSupportSplice.Receipt.physical_ownership",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.allocations_nodup",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.advance_charged",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.advance_removed_length",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.advance_conservation",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.ledger_charged",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.ledger_removed_length",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.ledger_partition",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.physical_ownership",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.lift_injective",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.labelled_live",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.labelled_physical_ownership",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.labelled_charged_origin",
      "PNP.DirectWire.WireOpenProgram.Transition.local_physical_ownership",
      "PNP.DirectWire.WireOpenProgram.Transition.local_charged_origin",
      "PNP.DirectWire.WireOpenProgram.bornBefore_mono",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.initial_wellFormed",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.accounted_before",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.origin_before",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.origin_injective",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.liftOrigin_original",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.liftOrigin_allocated",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.liftOrigin_injective",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.lift_originals",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_live",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_charged_length",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_removed_length",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_charge_origin",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_physical_position",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_support_compiled_position",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_partition",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_wellFormed",
      "PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_wellFormed",
      "PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_charged_length",
      "PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_removed_length",
      "PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_charge_survives",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_wellFormed",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.physical_ownership",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_origin_injective",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_charge_origin",
      "PNP.DirectWire.WireOpenProgram.allocation_namespaces_disjoint",
      "PNP.DirectWire.WireOpenProperSupport.program_equivalent",
      "PNP.DirectWire.WireOpenProperSupport.program_causalInterfaceBound",
      "PNP.DirectWire.WireOpenProperSupport.program_compiles",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.output",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.field",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.gateCount",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.charge_accounting",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.gain_iff_local_gain",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.gain_iff_net_charges",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.strictGain",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.strictResidualDescent",
      "PNP.DirectWire.WireOpenProperSupport.compile_complete",
      "PNP.DirectWire.WireOpenProperSupport.compile_exists_iff",
      "PNP.DirectWire.WireOpenProperSupport.compile_none_iff",
      "PNP.DirectWire.WireOpenProperSupport.ownershipLift_original",
      "PNP.DirectWire.WireOpenProperSupport.ownershipLift_allocated",
      "PNP.DirectWire.WireOpenProperSupport.ownershipLift_injective",
      "PNP.DirectWire.WireOpenProperSupport.ownershipRawNode_exterior",
      "PNP.DirectWire.WireOpenProperSupport.ownershipRawNode_program",
      "PNP.DirectWire.WireOpenProperSupport.ownership_compiled_position",
      "PNP.DirectWire.WireOpenProperSupport.ownership_partition",
      "PNP.DirectWire.WireOpenProperSupport.ownership_charged_origin",
      "PNP.DirectWire.WireOpenProperSupport.ownership_distinct",
      "PNP.DirectWire.WireOpenProperSupport.physical_ownership",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.records_source",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.proper_support",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.output",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.field",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.gateCount",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.charge_accounting",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictGain",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictResidualDescent",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.physical_ownership",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.closed_ledger",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.creation_lifecycle",
      "PNP.DirectWire.WireOpenCertificate.verify_complete",
      "PNP.DirectWire.WireOpenCertificate.verify_exists_iff",
      "PNP.DirectWire.WireOpenCertificate.verify_sound",
      "PNP.DirectWire.WireOpenCertificate.verify_decode_none",
      "PNP.DirectWire.WireOpenCertificate.verify_program_none",
      "PNP.DirectWire.WireOpenCertificate.verify_not_proper",
      "PNP.DirectWire.WireOpenCertificate.verify_no_gain"
    ],
    "scope": "For arbitrary finite computational wire carriers, raw outer support records and raw mixed programs, source-only verification computes the complete dependency order, including intrinsic creation references, and executes every primitive or actual descendant-support splice from its internally constructed initial state. The same pending creations and captured full-value snapshots persist across intervening support changes until genuine full-mode R6, R7 or R8 discharge; final ambient closure is required. Execution-derived causal bounds construct the literal outer splice. Acceptance is exactly complete decoding and finally closed execution on a proper physical support with strict final saving. The result preserves all ordinary outputs and literal fields, includes the exterior once, and reconstructs unique original/allocation ownership through the actual compiler positions. Computed outer-position namespaces distinguish nested event identities; historical charges and removals survive later allocation deletion. Temporary expansion is allowed; malformed, cyclic, missing or duplicate references, unfinished ledgers, failed tails, whole supports and final nondecrease reject. No intermediate carrier, schedule, snapshot, correctness, cost, owner, rank or splice witness is supplied.",
    "nonClaim": "This verifies offered arbitrary finite mixed programs in the computational wire-carrier language; inner descendant histories retain their existing closed-history boundary. It does not find an accepted certificate for every nonminimal input, establish local minimality after rejection, or construct a globally successful strategy. Full manuscript profiles and all R1-R9 and N1-N10 rule families, matched-kappa arbitrary-support Pull/Expand, full manuscript VerifyDW, ChargeSoundness and Package E, and terminal-family derivation remain open. There is no bound on temporary growth or encoded-input polynomial runtime, output size or certificate size. Global route coverage, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin, deterministic CNFSAT in P and the eligible root remain open. Finite runtime fixtures are regression evidence, not theorem authority. No fixed weighted checkpoint or global gate closes, and P = NP is not proved."
  },
  "statusFields": {
    "leanOpenObligationProgramsFormalized": true,
    "leanOpenObligationProgramsAxiomAuditPassed": true,
    "leanOpenObligationProgramsAuditedDeclarationCount": 144,
    "leanOpenObligationProgramsPendingSnapshotPreservationTheorem": "PNP.DirectWire.WireOpenSupportSplice.transfer_pending",
    "leanOpenObligationProgramsCompleteDependencyOrderTheorem": "PNP.DirectWire.WireOpenProgram.orderEvents_success_iff",
    "leanOpenObligationProgramsCompleteExecutionAcceptanceTheorem": "PNP.DirectWire.WireOpenProgram.compile_exists_iff",
    "leanOpenObligationProgramsFinalClosureTheorem": "PNP.DirectWire.WireOpenProgram.CompiledProgram.closed",
    "leanOpenObligationProgramsCreationLifecycleTheorem": "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.creation_lifecycle",
    "leanOpenObligationProgramsFullFieldRestorationTheorem": "PNP.DirectWire.WireOpenProgram.CompiledProgram.full_field",
    "leanOpenObligationProgramsCompleteOuterCompilationTheorem": "PNP.DirectWire.WireOpenProperSupport.compile_complete",
    "leanOpenObligationProgramsActualCompilerOwnershipTheorem": "PNP.DirectWire.WireOpenProperSupport.ownership_compiled_position",
    "leanOpenObligationProgramsCompleteAcceptanceIffTheorem": "PNP.DirectWire.WireOpenCertificate.verify_exists_iff",
    "leanOpenObligationProgramsSourceRoundTripTheorem": "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.records_source",
    "leanOpenObligationProgramsOrdinaryOutputPreservationTheorem": "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.output",
    "leanOpenObligationProgramsLiteralFieldPreservationTheorem": "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.field",
    "leanOpenObligationProgramsHistoricalAccountingTheorem": "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.charge_accounting",
    "leanOpenObligationProgramsPhysicalOwnershipTheorem": "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.physical_ownership",
    "leanOpenObligationProgramsStrictGainTheorem": "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictGain",
    "leanOpenObligationProgramsStrictResidualDescentTheorem": "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictResidualDescent",
    "leanOpenObligationProgramsFailedCompleteProgramRejectionTheorem": "PNP.DirectWire.WireOpenCertificate.verify_program_none",
    "leanOpenObligationProgramsWholeSupportRejectionTheorem": "PNP.DirectWire.WireOpenCertificate.verify_not_proper",
    "leanOpenObligationProgramsNondecreaseRejectionTheorem": "PNP.DirectWire.WireOpenCertificate.verify_no_gain",
    "leanOpenObligationProgramsArbitraryFiniteDimensionsAndProgramsCovered": true,
    "leanOpenObligationProgramsRawSourceOnlyCertificate": true,
    "leanOpenObligationProgramsInitialStateInternallyDerived": true,
    "leanOpenObligationProgramsCompleteRawMixedProgramRequired": true,
    "leanOpenObligationProgramsComputedDependencyOrderRequired": true,
    "leanOpenObligationProgramsIntrinsicCreationReferencesRequired": true,
    "leanOpenObligationProgramsSamePendingSnapshotsPreserved": true,
    "leanOpenObligationProgramsOpenObligationsTransportedAcrossSupports": true,
    "leanOpenObligationProgramsFullModeR6R7R8DischargeRequired": true,
    "leanOpenObligationProgramsFinalAmbientLedgerClosureRequired": true,
    "leanOpenObligationProgramsOuterAcyclicityDerivedFromExecution": true,
    "leanOpenObligationProgramsProperPhysicalSupportRequired": true,
    "leanOpenObligationProgramsStrictFinalLocalSavingRequired": true,
    "leanOpenObligationProgramsAllOrdinaryOutputsAndLiteralFieldsPreserved": true,
    "leanOpenObligationProgramsExteriorOccursExactlyOnce": true,
    "leanOpenObligationProgramsActualHistoricalChargeRemovalBalancePreserved": true,
    "leanOpenObligationProgramsPhysicalOwnershipComputed": true,
    "leanOpenObligationProgramsActualCompilerPositionMapsUsed": true,
    "leanOpenObligationProgramsComputedOuterPositionNamespaces": true,
    "leanOpenObligationProgramsLaterRemovedAllocationChargesRetained": true,
    "leanOpenObligationProgramsIntermediateExpansionAllowed": true,
    "leanOpenObligationProgramsInnerClosedHistoryLanguagePreserved": true,
    "leanOpenObligationProgramsCallerSuppliedCorrectnessOrIntermediateCircuitRequired": false,
    "leanOpenObligationProgramsCallerSuppliedInitialStateOrSnapshotRequired": false,
    "leanOpenObligationProgramsCallerSuppliedOrderOrSuccessfulSpliceRequired": false,
    "leanOpenObligationProgramsCallerSuppliedCostsOrOwnersRequired": false,
    "leanOpenObligationProgramsAcceptedPrefixReturnedAfterLaterRejection": false,
    "leanOpenObligationProgramsRejectedCertificateProvesLocalMinimality": false,
    "leanOpenObligationProgramsAcceptedCertificateForEveryNonminimalInputProved": false,
    "leanOpenObligationProgramsGloballySuccessfulStrategyDerived": false,
    "leanOpenObligationProgramsFullManuscriptVerifyDWProved": false,
    "leanOpenObligationProgramsFullManuscriptProfilesAndRuleFamiliesProved": false,
    "leanOpenObligationProgramsCompleteChargeSoundnessProved": false,
    "leanOpenObligationProgramsCompletePackageEProved": false,
    "leanOpenObligationProgramsTerminalFamiliesDerived": false,
    "leanOpenObligationProgramsGlobalRouteCoverageProved": false,
    "leanOpenObligationProgramsUnconditionalSaturatePositiveProved": false,
    "leanOpenObligationProgramsUnconditionalBCELReadyProved": false,
    "leanOpenObligationProgramsUnconditionalZeroSlackProved": false,
    "leanOpenObligationProgramsExactGeneralPCCMinProved": false,
    "leanOpenObligationProgramsPolynomialRuntimeOutputAndCertificateBoundsProved": false,
    "leanOpenObligationProgramsRuntimeExecutionIsProofAuthority": false,
    "leanOpenObligationProgramsScope": "arbitrary-finite-source-only-complete-mixed-programs-computed-order-open-snapshot-transport-full-mode-discharge-final-closure-derived-proper-literal-splice-strict-saving-all-observations-actual-physical-ownership-and-historical-costs-no-global-discovery-or-full-manuscript-profiles-or-polynomial-runtime"
  },
  "audit": "lean-audit/PNPOpenObligationProgramAxiomAudit.lean",
  "testFiles": [
    "audits/lean-open-obligation-programs0.test.mjs",
    "audits/lean-open-obligation-programs-publication0.test.mjs"
  ],
  "doc": "docs/lean_open_obligation_programs.md",
  "plan": "docs/plans/2026-09-17-open-obligations-across-descendant-supports.md",
  "command": "node --test audits/lean-open-obligation-programs0.test.mjs audits/lean-open-obligation-programs-publication0.test.mjs",
  "workflowCommands": "set -euo pipefail\nnode scripts/check-lean-axioms.mjs lean-audit/PNPOpenObligationProgramAxiomAudit.lean\nfor part in SupportSplice Program SupportOwnership PrimitiveOwnership ProgramOwnership ProperSupport ProperOwnership Certificate; do\n  lake env lean -DwarningAsError=true \"lean-regression/PNPWireOpen${part}.lean\"\ndone\n",
  "publicationDecision": "Publication decision: defer. This closes the computational mixed-program obligation-lifecycle and physical-accounting edge for offered certificates, but does not establish full manuscript VerifyDW, global certificate discovery or an unconditional checkpoint. No global proof gate or fixed weighted checkpoint changes, and the published global bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication."
};
const PARTS = ["SupportSplice","ProgramInput","Program","SupportOwnership","PrimitiveOwnership","ProgramOwnership","ProperSupport","ProperOwnership","Certificate"];
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

test('M269 preflight: exact root, names, scripts and durable workflow share one boundary',async()=>{
  const [root,audit,probe,pkg,surface,verifier,workflow,mapText]=await Promise.all([
    text0('lean/PNP.lean'),text0(META.audit),text0('lean-audit/PNPTheoremInventory.lean'),
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'),text0('publication/FORMAL_PUBLICATION_MAP.json'),
  ]);
  assert.equal(REVIEWED.length,144);
  const names=REVIEWED.map(row=>row[0]);
  assert.equal(new Set(names).size,144);
  assert.deepEqual(names,META.milestone.requiredTheorems);
  assert.match(audit,/^import PNP$/mu);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),names);
  for(const part of PARTS)assert.ok(root.includes('import PNP.NANDWireOpen'+part));
  for(const name of names) {
    assert.equal(probe.split(String.fromCharCode(96)+name+',').length-1,1,name);
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(value=>value===name).length,1,name);
  }
  assert.equal(JSON.parse(pkg).scripts['audit:m269'],META.command);
  assert.ok(surface.includes("'audit:m269': '"+META.command+"'"));
  for(const file of META.testFiles)assert.ok(verifier.includes("'"+file+"'"),file);
  assert.ok(workflow.includes('run: npm run audit:m269'));
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

test('M269 release: compiled theorem types and exact axiom closures support only reviewed claims',async()=>{
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

test('M269 release: weakened types and supplied authority cannot retain earned credit',async()=>{
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

test('M269 release: missing evidence, project axioms and widened scope reject',async()=>{
  const {status,inventory,inventoryBytes,map}=await sources0();
  const name='PNP.DirectWire.WireOpenCertificate.verify_exists_iff';
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
      ?{...row,[field]:'Every nonminimal input has a polynomially discoverable full manuscript certificate.'}:row)};
    assert.throws(()=>DeriveFormalPublication0(inventory,widened,inventoryBytes,status.leanSourceClosureSha256),
      /map drifted from the reviewed specification/u);
  }
  const changedPin={...map,earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256,[name]:'0'.repeat(64)}};
  assert.throws(()=>DeriveFormalPublication0(inventory,changedPin,inventoryBytes,status.leanSourceClosureSha256),
    /map drifted from the reviewed specification/u);
});

test('M269 release: status rejects widened acceptance, full-scope and complexity claims',async()=>{
  const {status}=await sources0();
  for(const suffix of [
    'CompleteAcceptanceIffTheorem','AuditedDeclarationCount','ProperPhysicalSupportRequired',
    'CallerSuppliedOrderOrSuccessfulSpliceRequired','AcceptedCertificateForEveryNonminimalInputProved',
    'SamePendingSnapshotsPreserved','FinalAmbientLedgerClosureRequired','PhysicalOwnershipComputed',
    'ComputedOuterPositionNamespaces','CallerSuppliedInitialStateOrSnapshotRequired',
    'ActualCompilerPositionMapsUsed','LaterRemovedAllocationChargesRetained',
    'FullManuscriptVerifyDWProved','PolynomialRuntimeOutputAndCertificateBoundsProved','Scope',
  ]) {
    const field='leanOpenObligationPrograms'+suffix,value=META.statusFields[field];
    assert.notEqual(value,undefined,field);
    const mutation={...status,[field]:typeof value==='boolean'?!value:
      typeof value==='number'?value+1:value+':unreviewed'};
    const result=await CheckFormalReconstructionStatus0({writeOutput:false,statusOverride:mutation,siteOverride:mutation});
    assert.equal(result.tag,'reject',field);
    assert.equal(result.coord,'FormalReconstructionStatus.Field',field);
    assert.deepEqual(result.path,['status/FORMAL_RECONSTRUCTION_STATUS.json',field],field);
  }
});

test('M269 release: offered-program verification does not earn an unconditional checkpoint',async()=>{
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

test('M269 release: current documentation separates coverage, estimate and publication decision',async()=>{
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
    const current=prose0(await text0(file));
    for(const metric of metrics)assert.ok(current.includes(metric),file+': '+metric);
  }
});
