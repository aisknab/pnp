import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  DeriveFormalPublication0, MilestoneTheoremKernelTypeSha2560, stableStringify0, REQUIRED_MILESTONE_THEOREMS0,
} from '../formal-publication0.mjs';
import {CheckFormalReconstructionStatus0} from '../pcc-formal-reconstruction-status0.mjs';
import {validateProofProgress0} from '../pcc-proof-progress0.mjs';

// Frozen M267 compiled type and axiom review; tests must not regenerate their own expectations.
const REVIEWED = [
  [
    "PNP.DirectWire.WireDescendantHistory.decodeRecord_encode",
    "fc87b5800aec8b69970acee761f33a36668c50afe06a23065b35de69a9fc13b6",
    "PNP.NANDWireDescendantInput",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.decodeRecord_source",
    "524aabfc523f01ff901772f580fe2572ee8652710291e521eb5e1d0f646e4266",
    "PNP.NANDWireDescendantInput",
    []
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.decodeRecords_encode",
    "af9320bf79a0e272e5d82718b03be61d75713317e23303efcc3ced204b4a899b",
    "PNP.NANDWireDescendantInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.decodeRecords_source",
    "f61ca4c313bb9c030560ccd740f3141b4523bd9f500fe0fb034a07197c4beeb6",
    "PNP.NANDWireDescendantInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.decodeAction_encode",
    "7118d17b2141ba336b0ff7eb33272abe6ee256ba62cf4824b8c76af40286d127",
    "PNP.NANDWireDescendantInput",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.decodeAction_source",
    "331ede205b8f1d5decfc7794f2ba5e1f950dd8bf56ac94182ed7abe87c5c3dc8",
    "PNP.NANDWireDescendantInput",
    []
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.decodeEvent_encode",
    "6600dea5f53aee5f9657161733ca79507baebd020c2499a2ec41efa7fa4c1837",
    "PNP.NANDWireDescendantInput",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.decodeEvent_source",
    "235feb55ebc78c5ac4c6103b3b05e9c9b119a4a7fe0fd1f5720e0ac62be6cc24",
    "PNP.NANDWireDescendantInput",
    []
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.decodeEvents_encode",
    "e00db58968ba9cff4faecb7ee91711fde646deebd3869be7b4d309641356fa76",
    "PNP.NANDWireDescendantInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.decodeEvents_source",
    "41aee7665f59825f17bfe4520e535cc0e04a052958dd4ed4c4ebb47e4efdc27c",
    "PNP.NANDWireDescendantInput",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.StageCompilation.records_source",
    "36347236b5cef75095e073072c6f73b92ad3d44eecd843a02a42a4430b4a2541",
    "PNP.NANDWireDescendantStage",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.StageCompilation.events_source",
    "90e872ca617b279c954a74b13db9e8dcf9a00a2c48636e983f839b1eb4f7bc17",
    "PNP.NANDWireDescendantStage",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.StageCompilation.existing_result",
    "01fd8d8b2fe21c4b673c71205d517e7de85a3be33c8fb2102ec35aa89ab6be05",
    "PNP.NANDWireDescendantStage",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.StageCompilation.semantics",
    "3b9d5e6d3092ad74b1fa1685ae5ea5777bd2b191ed2ad3dd177878110b827ac0",
    "PNP.NANDWireDescendantStage",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.StageCompilation.physicalOrigin_position",
    "9b7b74a32b1de6db94f2b2368df9c11105bb8e3b931552ab9c3ddb134db3dbd0",
    "PNP.NANDWireDescendantStage",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.StageCompilation.physical_ownership",
    "c62e396630543446c2ebed0880845c7ce9b32e2e22779ade3af1aecef6d76367",
    "PNP.NANDWireDescendantStage",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.StageCompilation.gate_balance",
    "cf6d933a7dd0bd138116a566272a2726eda4af9f68be1795d628918b93f35d33",
    "PNP.NANDWireDescendantStage",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.StageCompilation.charged_origin",
    "abbdc18e2e8a43df7d518be54c01b127dd41188f11c09c57af237ad6b5125b28",
    "PNP.NANDWireDescendantStage",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.StageCompilation.event_identity_unique",
    "474aa00f7c0b139e23d753e62817df722983c32689d964ba4d65dbd2e6f44c72",
    "PNP.NANDWireDescendantStage",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.compileStage_records_none",
    "92f268195aac2fd63720dcbf3f8109e998a421f6f19ca7475243eb4d0569e546",
    "PNP.NANDWireDescendantStage",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.compileStage_events_none",
    "1629b93a589c5131a0ed5ded6fab4b1f9b08eb00b21a68eaac44e085e88286ed",
    "PNP.NANDWireDescendantStage",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.compileStage_history_none",
    "d6d047d7d01bbcd776d23969daa4ce4adcd9acbc8fdb9f73086e455536dac9d1",
    "PNP.NANDWireDescendantStage",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.semantics",
    "730f70381e9dfcdecb39cfab21318604d57468ae1180e0ce23295616d578317f",
    "PNP.NANDWireDescendantRun",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.gate_balance",
    "925aeb15068172113d8d968acbe2766e58ea48905ff0c901ef139fc1dfb17e6c",
    "PNP.NANDWireDescendantRun",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.compile_nil",
    "f7219d283f13a96eee20c390f9fc0e487fa09b3a9f4f00f6eb7240cef0c54cb7",
    "PNP.NANDWireDescendantRun",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.compile_cons",
    "2ff609883376b3563e4d6119ee3d2c3a5387b4bd18deb3c2ac3e02aa34fcd354",
    "PNP.NANDWireDescendantRun",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.compile_stage_none",
    "929efbcbea66a78fcc4c59744c6056ee1f3720b05903059ef7bd26566ee0e8ed",
    "PNP.NANDWireDescendantRun",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.compile_tail_none",
    "b5fc4eb08f60243aa40b2e97b2215545346b56be83b5468aacc5e8c87b143185",
    "PNP.NANDWireDescendantRun",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.compile_cons_some",
    "442d0dee6af88fe660f5b5a7751cfdccf40e77831899e0fb23cfeb03ee28dfa8",
    "PNP.NANDWireDescendantRun",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.compile_sound",
    "3e95f253885642c3746abf72e3c186e7e2f0cf53675e5258d3c0b7ca12052f6b",
    "PNP.NANDWireDescendantRun",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.createdBefore_mono",
    "13f07d18ac80c19d0b241d6ffe1fe26305924c603d3fdd3c82f4ba472477fe37",
    "PNP.NANDWireDescendantLedger",
    []
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.initial_wellFormed",
    "dd894a15bc64f4dd81d0df6aa398a68aeabac5e83f6e4484bfd6a91a1cc28e09",
    "PNP.NANDWireDescendantLedger",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.accounted_before",
    "43927ed921138038ad6da128a9eea71cf6faa67f4d146c75e7df63246e7dc856",
    "PNP.NANDWireDescendantLedger",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.origin_before",
    "00c913d1e9e87d4a0a4762e487294591fe5a476e5c99bcbb6892984087847b36",
    "PNP.NANDWireDescendantLedger",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.origin_injective",
    "3edbbc3ac6b52912b944507bc19a35f242f2529379cc0f8bafff404a242b17b7",
    "PNP.NANDWireDescendantLedger",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.liftOrigin_original",
    "d99ead70d3072eb2f9948dec43972423df587b84ef5ac6cbfef6bd2f1dea1dc8",
    "PNP.NANDWireDescendantLedger",
    []
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.liftOrigin_allocated",
    "73c0a3a43ae86b009db7e572bfe07c7f9e49b8b5c6ac359b1fc1592f28f44098",
    "PNP.NANDWireDescendantLedger",
    []
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.liftOrigin_injective",
    "0547e812fc266943a45c28ded8e29542edb7a482c7fc61756027dae953e84484",
    "PNP.NANDWireDescendantLedger",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.lift_originals",
    "3159515d4078ec4e63aa6223e4e8ddf7cb4cb762141daa6592fce708749a4bce",
    "PNP.NANDWireDescendantLedger",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.advance_live",
    "a1c794ca85ab26ebbcd2be03b5111f2274f6ac12a3595aa2775b086a7fbf4933",
    "PNP.NANDWireDescendantLedger",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.advance_charged_length",
    "1ac4e5601de2682e4efb1233f4ade2f0e55a9a49dbd5e69bf8dd671c0742fcc5",
    "PNP.NANDWireDescendantLedger",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.advance_removed_length",
    "52f5d335b40ad5a794adcec1dced975629358970020c237c7d34b7846a669a25",
    "PNP.NANDWireDescendantLedger",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.advance_physicalOrigin_position",
    "3c3ca3f5f6c6bdef9f3aa5a5cc1cefa5388e84864efa4db4e8a0c20ec6db3142",
    "PNP.NANDWireDescendantLedger",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.advance_charge_origin",
    "7d8d16e149d8dd7e72910c552b12e7c4b8b3b40a07945fe02c60a7165c79cf31",
    "PNP.NANDWireDescendantLedger",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.advance_partition",
    "bf6a2dd629f7424797e9e9588365196d1429d09f14c1c938d8cf5b5fc7628828",
    "PNP.NANDWireDescendantLedger",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.advance_wellFormed",
    "f6527741ef6c8d30f23b9e917101e407e50b3b578be1c477e38051b1144e0c3d",
    "PNP.NANDWireDescendantLedger",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.carry_nil",
    "d877925aee3c87c1408b207be8e7385719475bf4703e666313484be02e5f624d",
    "PNP.NANDWireDescendantOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.carry_cons",
    "5f9a901ad4e5d8df4fadbca20c7d7d9bbbbb75a0b18fb9d344ffb14ca1817d22",
    "PNP.NANDWireDescendantOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.carry_wellFormed",
    "98f9be704ed7ab5d90de5693f3b31d3c1c4efbc0cf1feea3815f33b044e5096d",
    "PNP.NANDWireDescendantOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.carry_charged_length",
    "03df662f19a68bad4aa47aec373def4f9b64ba582a8cb687ed4d6b636ca1c955",
    "PNP.NANDWireDescendantOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.carry_removed_length",
    "08410ef75059f09ccae0bf8b7a09ff88844446347c6b06693e27b38b1660e9b6",
    "PNP.NANDWireDescendantOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.carry_charge_survives",
    "d096142fb80cd50728403e56b1b0104599d20a4846dac0f4e57cb8dcb0b24cd2",
    "PNP.NANDWireDescendantOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.ledger_nil",
    "c177a84e815346750b7b93f58ff2e4932f490c8711358b19889f0cc9b4d96b2b",
    "PNP.NANDWireDescendantOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.ledger_wellFormed",
    "c41a54ae47f84cc41a738f7af179897d79688d982c8723c6320e26fe9397680b",
    "PNP.NANDWireDescendantOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.physical_ownership",
    "9fe1e0da4c0adb147eac76a4283e506e71cde17393f3258941654d71e0f7823f",
    "PNP.NANDWireDescendantOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.ledger_origin_injective",
    "b2bd68e066dfae7cbba93d921ee22fa8b22f1a33db1c913750d3f93ce322c98a",
    "PNP.NANDWireDescendantOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.ledger_charged_before",
    "e31f65471e410fa25453118ce7a14a9846eaeefdafbbf719f54f166e65bff004",
    "PNP.NANDWireDescendantOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.inputEventKeys_nil",
    "13c92c7368cbc976ffcffe28c5ffe3fdb1c9ac81ec9be362c9cd5eddb205b140",
    "PNP.NANDWireDescendantEvents",
    []
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.inputEventKeys_cons",
    "6548868619c1a8cc22baf1304c2068efdd051982fe23a52cb0ace70034f07a18",
    "PNP.NANDWireDescendantEvents",
    []
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.inputEventKeys_bounds",
    "92391bd1516635d0c2f45261e8afb43653930539afa6ff39b6705a1f8358bbf1",
    "PNP.NANDWireDescendantEvents",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.StageCompilation.rawEventIdentities_nodup",
    "7bdfcdda7c4bb6194f7ac860ad6c315a4b1362e905f8eb0b498be024c418e2e6",
    "PNP.NANDWireDescendantEvents",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.inputEventKeys_nodup",
    "6e5f481c35560bf2256f0bd4e8739cd9a9b5dcceabd559adb7e90dc3bf914a96",
    "PNP.NANDWireDescendantEvents",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.inputEventKeys_unique",
    "c547f1853997fda210326a1dd7395f8ca923fc81bfe8f62ce7f063c8b78e6453",
    "PNP.NANDWireDescendantEvents",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.carry_charged_origin",
    "f50528d8be5f6b54c10466374694365ac6b8952fab52bf39ec6ed32cd8d1fb1e",
    "PNP.NANDWireDescendantEvents",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.ledger_charged_origin",
    "75f504cf821f4ac027256314bc0b5a9b3b9e7e019a23d9ac342894df35dd0de0",
    "PNP.NANDWireDescendantEvents",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.ledger_live_allocated_event",
    "91b824e0cabe19db7e9aca3d8fbf139ecd1e70d5d247c8442e07c3e55ba47113",
    "PNP.NANDWireDescendantEvents",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.eventRequests_member",
    "8b02d4215e37b742343b5b7b0f55cb9619140844c0f694ccf227d07be14815b7",
    "PNP.NANDWireDescendantCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.eventRequests_disjoint",
    "5b6d5e4ed8ebea8319891543abd014f7110d69afc3605f1665d8e71b0c6bff19",
    "PNP.NANDWireDescendantCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.eventOwner_some_iff",
    "778aed23652cd249f9052e1457bcd1698941e24a6ffbc1457ecc1789d62c5fa2",
    "PNP.NANDWireDescendantCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.eventOwner_none_iff",
    "35fce1d6ac4087184a18b3da528db87d2553f95378243932324a50fb7df3ea85",
    "PNP.NANDWireDescendantCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.support_membership",
    "ceb66e2bee62c16542d89e71752e0bb3e35f970eb5381a8fbae8fe446983f069",
    "PNP.NANDWireDescendantCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.support_restrict",
    "3cb9cf5a272f2c489ca6e69407068ff73ee4a42974c1ee0b40b765f421e071b5",
    "PNP.NANDWireDescendantCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.materializer_gateCount",
    "08af9b94b4a9a24a828227835e5e0503f7a908fe7c5e508e54ea1e96dcddaeae",
    "PNP.NANDWireDescendantCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.materializer_chargeIdentity",
    "fc6b95d4523f3f285fc1deac9b0f8b86a3e1c6649a2e74a1d8a84cf90816d91d",
    "PNP.NANDWireDescendantCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.materializer_wholeCharge",
    "326ddb712dcf0c91269ad0b8ac75fc8e3f0ae01137af1f4c2f4560ab38c09f6f",
    "PNP.NANDWireDescendantCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.materializer_semantics",
    "7857613a7b0a40c3435ac240be62e98dad90a916d6fe591d9680272b5e505cd0",
    "PNP.NANDWireDescendantCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.materializer_induced",
    "26da7a1ed7507ac461ee2d1ce1d917fa6ca73122db872ab20c830fedcc713a0e",
    "PNP.NANDWireDescendantCharges",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.CompiledRun.strictGain",
    "d42ce2640b1a7f5881c7efc846365047d84c7f63ddd4e5629e4b4d2f45c32872",
    "PNP.NANDWireDescendantGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.GainResult.strictGain",
    "a39fe16e118191baf32ff61fd7abc2d0657024634156b1306bd83072bd06bf08",
    "PNP.NANDWireDescendantGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.GainResult.strictResidualDescent",
    "e4a0a30f2560efd0dea139ef89fb35feffab6efa11adf500369d9ca3cf7f9d65",
    "PNP.NANDWireDescendantGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.compileGain_compile_none",
    "d11fe443478ffdd979f08205e96c6879ea9555c49fa4926cc69efe4bfb0ce3b8",
    "PNP.NANDWireDescendantGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.compileGain_no_gain",
    "5cbb7812dc8e1b5ffdbecc9e88230e1f02dcabfe64d41f9cd423970ecb0a2f63",
    "PNP.NANDWireDescendantGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.compileGain_complete",
    "c5e568e7077d2fa367476cac0c996c87be3d1ade4d4b00cb9c1d80ef40d163e1",
    "PNP.NANDWireDescendantGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireDescendantHistory.compileGain_exists_iff",
    "502966e15396548e91df5737beba0e5a8a06aca59914b77cbcb28849d65ae666",
    "PNP.NANDWireDescendantGain",
    [
      "Quot.sound",
      "propext"
    ]
  ]
];
const STATUS_FIELDS = {
  "leanDescendantHistoryOwnershipFormalized": true,
  "leanDescendantHistoryOwnershipAxiomAuditPassed": true,
  "leanDescendantHistoryOwnershipAuditedDeclarationCount": 84,
  "leanDescendantHistoryOwnershipRawRecordRoundTripTheorem": "PNP.DirectWire.WireDescendantHistory.decodeRecords_encode",
  "leanDescendantHistoryOwnershipRawRecordSourceTheorem": "PNP.DirectWire.WireDescendantHistory.decodeRecords_source",
  "leanDescendantHistoryOwnershipRawEventRoundTripTheorem": "PNP.DirectWire.WireDescendantHistory.decodeEvents_encode",
  "leanDescendantHistoryOwnershipRawEventSourceTheorem": "PNP.DirectWire.WireDescendantHistory.decodeEvents_source",
  "leanDescendantHistoryOwnershipActualStageResultTheorem": "PNP.DirectWire.WireDescendantHistory.StageCompilation.existing_result",
  "leanDescendantHistoryOwnershipLiteralPhysicalPositionTheorem": "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.advance_physicalOrigin_position",
  "leanDescendantHistoryOwnershipOriginalCoordinateLiftTheorem": "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.liftOrigin_original",
  "leanDescendantHistoryOwnershipAllocatedCoordinateLiftTheorem": "PNP.DirectWire.WireDescendantHistory.PersistentOwnership.liftOrigin_allocated",
  "leanDescendantHistoryOwnershipPhysicalOwnershipTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.physical_ownership",
  "leanDescendantHistoryOwnershipPhysicalOriginInjectiveTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.ledger_origin_injective",
  "leanDescendantHistoryOwnershipCompleteProgramSemanticsTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.semantics",
  "leanDescendantHistoryOwnershipActualExecutionSizeBalanceTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.gate_balance",
  "leanDescendantHistoryOwnershipHistoricalChargePersistenceTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.carry_charge_survives",
  "leanDescendantHistoryOwnershipInvalidLaterStagePropagationTheorem": "PNP.DirectWire.WireDescendantHistory.compile_tail_none",
  "leanDescendantHistoryOwnershipRawEventKeyDistinctnessTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.inputEventKeys_nodup",
  "leanDescendantHistoryOwnershipHistoricalChargeRawEventTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.ledger_charged_origin",
  "leanDescendantHistoryOwnershipSurvivingAllocationRawEventTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.ledger_live_allocated_event",
  "leanDescendantHistoryOwnershipDerivedEventRequestsDisjointTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.eventRequests_disjoint",
  "leanDescendantHistoryOwnershipActualRawEventOwnershipTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.eventOwner_some_iff",
  "leanDescendantHistoryOwnershipFixedOriginalRemainderTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.eventOwner_none_iff",
  "leanDescendantHistoryOwnershipSupportRestrictionTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.support_restrict",
  "leanDescendantHistoryOwnershipExtractedGateCountTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.materializer_gateCount",
  "leanDescendantHistoryOwnershipExtractedChargeIdentityTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.materializer_chargeIdentity",
  "leanDescendantHistoryOwnershipWholeSurvivingChargeTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.materializer_wholeCharge",
  "leanDescendantHistoryOwnershipOpenPieceSemanticsTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.materializer_semantics",
  "leanDescendantHistoryOwnershipInducedPieceBoundaryTheorem": "PNP.DirectWire.WireDescendantHistory.CompiledRun.materializer_induced",
  "leanDescendantHistoryOwnershipFinalNetGainTheorem": "PNP.DirectWire.WireDescendantHistory.GainResult.strictGain",
  "leanDescendantHistoryOwnershipFinalResidualDescentTheorem": "PNP.DirectWire.WireDescendantHistory.GainResult.strictResidualDescent",
  "leanDescendantHistoryOwnershipFinalGainAcceptanceIffTheorem": "PNP.DirectWire.WireDescendantHistory.compileGain_exists_iff",
  "leanDescendantHistoryOwnershipArbitraryFiniteDimensionsAndStageListsCovered": true,
  "leanDescendantHistoryOwnershipCurrentDescendantCoordinatesDecodedFromRawInput": true,
  "leanDescendantHistoryOwnershipActualLiteralCompilerPositionsCompose": true,
  "leanDescendantHistoryOwnershipStageEventAndLocalAllocationIdentitiesDerived": true,
  "leanDescendantHistoryOwnershipHistoricalChargesSurviveLaterRemoval": true,
  "leanDescendantHistoryOwnershipActualExecutionTotalsMatchPersistentLedger": true,
  "leanDescendantHistoryOwnershipLiveRemovedPartitionHasNoDuplicateIdentities": true,
  "leanDescendantHistoryOwnershipReusedLocalEventNumbersRemainStageDistinct": true,
  "leanDescendantHistoryOwnershipAllAllocationsTraceToActualInputEvents": true,
  "leanDescendantHistoryOwnershipDerivedEventRequestsDisjoint": true,
  "leanDescendantHistoryOwnershipSupportRestrictionPreservesOwners": true,
  "leanDescendantHistoryOwnershipMalformedLaterStageRejectsCompleteProgram": true,
  "leanDescendantHistoryOwnershipFinalNetGainAllowsIntermediateExpansion": true,
  "leanDescendantHistoryOwnershipExistingClosedLocalHistoryLanguagePreserved": true,
  "leanDescendantHistoryOwnershipCallerSuppliedIntermediateImplementationsRequired": false,
  "leanDescendantHistoryOwnershipCallerSuppliedOwnerFamilyRequired": false,
  "leanDescendantHistoryOwnershipCallerSuppliedProvenanceOrPartitionRequired": false,
  "leanDescendantHistoryOwnershipCallerSuppliedChargeOrRankRequired": false,
  "leanDescendantHistoryOwnershipCallerSuppliedSuccessfulHistoryCertificateRequired": false,
  "leanDescendantHistoryOwnershipSemanticOracleUsedByFinalGainAdapter": false,
  "leanDescendantHistoryOwnershipHistoricalChargesEqualSurvivingOwnedSize": false,
  "leanDescendantHistoryOwnershipEachIntermediateStageMustStrictlyDecrease": false,
  "leanDescendantHistoryOwnershipAcceptedPrefixReturnedAfterLaterRejection": false,
  "leanDescendantHistoryOwnershipRawStagesDerivedFromEveryInput": false,
  "leanDescendantHistoryOwnershipOpenObligationsTransportedAcrossSupports": false,
  "leanDescendantHistoryOwnershipCompleteManuscriptCarrierAndRewriteCalculusProved": false,
  "leanDescendantHistoryOwnershipMatchedKappaArbitrarySupportPullExpandProved": false,
  "leanDescendantHistoryOwnershipProperSupportVerifyDWProved": false,
  "leanDescendantHistoryOwnershipCompleteChargeSoundnessProved": false,
  "leanDescendantHistoryOwnershipCompletePackageEProved": false,
  "leanDescendantHistoryOwnershipTerminalFamiliesDerived": false,
  "leanDescendantHistoryOwnershipGloballySuccessfulRewriteStrategyDerived": false,
  "leanDescendantHistoryOwnershipGlobalRouteCoverageProved": false,
  "leanDescendantHistoryOwnershipUnconditionalSaturatePositiveProved": false,
  "leanDescendantHistoryOwnershipUnconditionalBCELReadyProved": false,
  "leanDescendantHistoryOwnershipUnconditionalZeroSlackProved": false,
  "leanDescendantHistoryOwnershipExactGeneralPCCMinProved": false,
  "leanDescendantHistoryOwnershipPolynomialRuntimeOutputAndCertificateBoundsProved": false,
  "leanDescendantHistoryOwnershipRuntimeExecutionIsProofAuthority": false,
  "leanDescendantHistoryOwnershipScope": "arbitrary-finite-raw-stage-sequences-actual-descendant-decoding-persistent-stage-event-local-physical-origins-exact-live-removed-historical-charge-partition-derived-input-event-owners-support-stable-extracted-charges-final-net-gain-with-intermediate-expansion-no-supplied-intermediates-or-owners-or-oracles-no-open-obligation-transport-or-global-strategy-or-polynomial-runtime"
};
const COORDINATE = "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-16-267";
const MILESTONE = "descendant-history-ownership";
const SCOPE = "For arbitrary finite source dimensions and raw stage/event lists, a source-only decoder and compiler traverse the complete list using each actual preceding descendant. Persistent physical origins relabel original positions through the existing literal ambient compiler and label allocations by computed stage position, executing raw event and local gate. The arbitrary-program theorem conserves original gates and every historical charge as a duplicate-free live/removed permutation with exact actual execution totals; later removal never erases an earlier charge. Accepted input-event keys are distinct across stages, even when local event numbers are reused, and every historical or surviving allocation traces to that raw family. Derived final owner requests are disjoint before support selection and reuse the existing extraction kernel for support-stable ownership, exact piece sizes and charges, open semantics and induced reconnection. Whole-program Boolean semantics and physical size accounting yield an optional final StrictEquivalentGain through a computed final-size comparison, permitting intermediate expansion and propagating every rejected stage. No intermediate implementation, owner family, provenance map, charge amount, rank, successful-history certificate or semantic oracle is supplied.";
const NON_CLAIM = "This covers arbitrary finite sequences of the existing closed computational-history compilations, not the full manuscript carrier/profile universe, cross-support transport of open obligations, all R1-R9 or N1-N10 rules, matched-kappa arbitrary-support Pull/Expand, proper-support VerifyDW, full ChargeSoundness or complete Package E. Raw supports and events remain inputs; no terminal-derived family or globally successful strategy is constructed. Final net gain does not require each stage to decrease, prove local minimality after rejection, bound temporary growth or establish encoded-input polynomial runtime. Global route coverage, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin and complete polynomial runtime, output and certificate bounds remain open. Runtime fixtures are regression evidence, not theorem authority. No fixed weighted checkpoint or global gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.";
const TEST_FILES = [
  "audits/lean-descendant-history-ownership0.test.mjs",
  "audits/lean-descendant-history-ownership-publication0.test.mjs"
];
const AUDIT = "lean-audit/PNPDescendantHistoryOwnershipAxiomAudit.lean";
const REGRESSIONS = [
  "lean-regression/PNPWireDescendantInput.lean",
  "lean-regression/PNPWireDescendantStage.lean",
  "lean-regression/PNPWireDescendantRun.lean",
  "lean-regression/PNPWireDescendantLedger.lean",
  "lean-regression/PNPWireDescendantOwnership.lean",
  "lean-regression/PNPWireDescendantEvents.lean",
  "lean-regression/PNPWireDescendantCharges.lean",
  "lean-regression/PNPWireDescendantGain.lean"
];
const DOCUMENTATION = "docs/lean_descendant_history_ownership.md";
const PLAN = "docs/plans/2026-09-16-descendant-history-ownership.md";
const PARTS = [
  "Input",
  "Stage",
  "Run",
  "Ledger",
  "Ownership",
  "Events",
  "Charges",
  "Gain"
];
const WORKFLOW_AUDIT_COMMANDS = "set -euo pipefail\nnode scripts/check-lean-axioms.mjs lean-audit/PNPDescendantHistoryOwnershipAxiomAudit.lean\nfor part in Input Stage Run Ledger Ownership Events Charges Gain; do\n  lake env lean -DwarningAsError=true \"lean-regression/PNPWireDescendant${part}.lean\"\ndone\n";

const COMMAND = 'node --test ' + TEST_FILES.join(' ');
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const canonical0 = value => Buffer.from(stableStringify0(value) + '\n');
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();

test('M267 preflight: package, verifier and durable CI share the exact audited boundary', async () => {
  const [pkg,surface,verifier,workflow,root] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'), text0('.github/workflows/lean-bridge.yml'),
    text0('lean/PNP.lean'),
  ]);
  assert.equal(REVIEWED.length,84);
  assert.equal(new Set(REVIEWED.map(row=>row[0])).size,84);
  assert.equal(JSON.parse(pkg).scripts['audit:m267'],COMMAND);
  assert.ok(surface.includes("'audit:m267': '"+COMMAND+"'"));
  for(const file of TEST_FILES) assert.ok(verifier.includes("'"+file+"'"),file);
  assert.ok(workflow.includes('run: npm run audit:m267'));
  assert.deepEqual(REGRESSIONS, PARTS.map(part=>'lean-regression/PNPWireDescendant'+part+'.lean'));
  const steps=workflow.split(/^      - name:/mu).filter(step=>
    step.includes('node scripts/check-lean-axioms.mjs '+AUDIT));
  assert.equal(steps.length,1);
  const block=steps[0].split('        run: |\n')[1];
  assert.ok(block,'literal audit block required');
  assert.equal(block.trimEnd().split('\n').map(line=>line.slice(10)).join('\n')+'\n',WORKFLOW_AUDIT_COMMANDS);
  assert.match(root,/^import PNP\.NANDWireDescendantGain$/mu);
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

test('M267 release: exact compiled types, axiom closures and limited claims match review', async () => {
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

test('M267 release: every reviewed type rejects weakening and supplied proof authority', async () => {
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

test('M267 release: hidden authority, absent evidence and widened publication claims reject', async () => {
  const {status,inventory,inventoryBytes,map} = await sources0();
  const name = 'PNP.DirectWire.WireDescendantHistory.CompiledRun.physical_ownership';
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

test('M267 release: status rejects changed construction, accounting and runtime claims', async () => {
  const {status} = await sources0();
  for (const suffix of ["PhysicalOwnershipTheorem","FinalGainAcceptanceIffTheorem","AuditedDeclarationCount","HistoricalChargesEqualSurvivingOwnedSize","CallerSuppliedOwnerFamilyRequired","RawStagesDerivedFromEveryInput","PolynomialRuntimeOutputAndCertificateBoundsProved","Scope"]) {
    const field = 'leanDescendantHistoryOwnership' + suffix;
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

test('M267 release: descendant ownership earns no unconditional checkpoint', async () => {
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

test('M267 release: current documentation reports separate metrics and justified publication', async () => {
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

test('M267 preflight: explicit-root audit and both inventory producers retain every reviewed name',async()=>{
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
