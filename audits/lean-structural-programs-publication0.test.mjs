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
    "PNP.DirectWire.StructuralReindexing.result_gate_level",
    "a50c0086d15fbd4074b697f5d2ee0a2cc4a3c560b6a897cf4b7d428f6b923147",
    "PNP.NANDReindexingCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.StructuralReindexing.result_source_level",
    "ab67b74a2c57b018dbd7a0e0d8c87bba4879f725e29d2e8d349f46a909a3752f",
    "PNP.NANDReindexingCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.StructuralReindexing.result_output_level",
    "0ed0ad0cbc5890423ea42d55462642efdab463ad9dd1c140fe676fb0a118091c",
    "PNP.NANDReindexingCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrier.reindex_exposed",
    "9dedb06fca17bd740917e249b8cea30323d0231377bf46cad60dc391863fd75f",
    "PNP.NANDWireStructuralReindexing",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrier.reindex_gateCount",
    "0d947c176309c42bf07dbecf927a7b8d98d522647e9ef37f5800f7d833347e09",
    "PNP.NANDWireStructuralReindexing",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrier.reindex_backward_forward",
    "e7020fbef713b2c69e5836482cf13b749a97795e147b01bf8f2fd32ef28ac619",
    "PNP.NANDWireStructuralReindexing",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrier.reindex_forward_backward",
    "9078f22fd69aa63d2673a856d3322e82cc1dd15392917a9e6f2a9b5533add29a",
    "PNP.NANDWireStructuralReindexing",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrier.reindex_output",
    "cf09ed635d35b9cd9552ec65eb1ae014ca8bb05414823cab5dc75ffb7579ea79",
    "PNP.NANDWireStructuralReindexing",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrier.reindex_field",
    "4612b606e7507e946f29548e3970060804ac6adcf0df141759023d91661407e6",
    "PNP.NANDWireStructuralReindexing",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrier.reindex_field_source",
    "4b052def21f902eae394a407393e26c5b0e97383909175a8b630fef6b8dfd6f7",
    "PNP.NANDWireStructuralReindexing",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrier.reindex_exposed_level",
    "d6a1f8cddc0bcb52ad1cb75b4c47ba4012f780e5e91c61e9a99b6bff2e7614b7",
    "PNP.NANDWireStructuralReindexing",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrier.reindex_output_level",
    "1eff3d5235aa20f4143d929928e6aaac7bbbbbd3036937bedecfdb9019228bfd",
    "PNP.NANDWireStructuralReindexing",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrier.reindex_field_level",
    "a4f2a92d2d54f64d54afc354e3b5d1fa89956729c517a9e9a94a37b2f31972c6",
    "PNP.NANDWireStructuralReindexing",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrier.reindex_causalBounds",
    "9a740ded5a4cd5450f45e36b76ec58c424d1f66ac143c3dcfa49af71838d4fb2",
    "PNP.NANDWireStructuralReindexing",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.State.reindex_pending",
    "6858e7c2cb1d0d1c8fa9d5a8b0450b2c43b30e63f189f6aea40d2df5443904b3",
    "PNP.NANDWireStructuralState",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.State.reindex_charged",
    "3278b0893f6fcfb33cb9ac19e3ad546142dfe3bcf241b1e8333cebbd6a775217",
    "PNP.NANDWireStructuralState",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.State.reindex_removed",
    "45128e8072c56c21232374f0726840652ef9ae56017b29f1c6deecf61094b843",
    "PNP.NANDWireStructuralState",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.State.reindex_gateCount",
    "c8dd434a6e1b1f51b4814a2615bb6c4c1baa921798c60eaa86ad3592549ac3ec",
    "PNP.NANDWireStructuralState",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.State.reindex_causalInvariant",
    "e8de8997cc2dec275f6d660c0ccc3edac2611801728268f621bf2fd7d8c72d7b",
    "PNP.NANDWireStructuralState",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireStructuralState.execute_isSome",
    "4035c397504a98fa0dfec573d7b3d6b24c8202b1b02d6a5dc4af9a0112935012",
    "PNP.NANDWireStructuralState",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireStructuralState.execute_failure_iff",
    "c07429575f8c1aa7e0e81ca4040f14d70f72946450f9fc9109f98ab397854ec0",
    "PNP.NANDWireStructuralState",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireStructuralState.Receipt.ownership_origin",
    "4092333a17356c304128b3f2e0a7e28203538f6eccf21065545a97d5bc3277bd",
    "PNP.NANDWireStructuralOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireStructuralState.Receipt.ownership_origin_forward",
    "e603acdc3c620f7162b839f84eccdd7f7b1567769d226eaa7b2ab7bf0f6a5bda",
    "PNP.NANDWireStructuralOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireStructuralState.Receipt.ownership_origin_injective",
    "1e22876ed58d059f7df324d13f989c964f9f0deac5ad3019a08c9e057cfff529",
    "PNP.NANDWireStructuralOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireStructuralState.Receipt.ownership_live_members",
    "ccb499ea94d177c368edec9e3fd18fc0ef3e9edbd71bee3d6523b9a1fd97baae",
    "PNP.NANDWireStructuralOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireStructuralState.Receipt.ownership_not_allocated",
    "2ed955adbb23fe72e448ffc1cb1cccd479e2c47a79d722d4a0d56c794cfc5485",
    "PNP.NANDWireStructuralOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireStructuralState.Receipt.ownership_charged",
    "b3a38a8a73eea8ab001c4b22f4f6966900a9bedfe7856af3bc96b1f24d8fd60b",
    "PNP.NANDWireStructuralOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireStructuralState.Receipt.ownership_removed",
    "228b4fcbbcbeb56497770b0c5b40e6d70ae73d8230b940bf0cac4f6ca4f96af4",
    "PNP.NANDWireStructuralOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireStructuralState.Receipt.ownership_wellFormed",
    "f9fef5f8077cd879ed5c275ddc21b46ab741ea12052d20bc939cf996d45c8a0f",
    "PNP.NANDWireStructuralOwnership",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireStructuralState.Receipt.physical_ownership",
    "3ccd99b194af7c85675e7d978e91c68be26394005f26001b9c9a19400f276dee",
    "PNP.NANDWireStructuralOwnership",
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
  ]
];
const MILESTONE = {
  "id": "structural-open-program-integration",
  "title": "Structural reordering in complete source-only replacement programs",
  "scope": "For arbitrary finite computational wire carriers, raw swap sequences, dependency graphs and complete offered replacement programs, computed structural actions preserve the literal exposed field sources, ordered output values and exact syntactic causal labels. The raw decoder validates the entire sequence against the current carrier, not the initial gate count. The exact pending snapshot function, charge count and removal count are preserved. Local physical ownership comes from the actual backward gate bijection, and the complete program lifts it through the prior ledger without resetting earlier allocations or removals. Structural actions interleave with primitive obligations and descendant-support programs while preserving full output and field semantics, creation-to-discharge bindings, unique event identities, causal invariants and physical ownership. The existing proper-support certificate verifier over this expanded action language still requires a complete accepted program, a closed final ledger and actual strict signed saving. Invalid later operations reject the whole program rather than returning a successful prefix; reordering alone earns no strict saving. Callers supply raw data, not correctness, transport, order, causality or ownership witnesses.",
  "nonClaim": "This is integration of checked offered programs, not a successful certificate-discovery strategy for every input. Finite executions are regression evidence, not theorem authority. The computational carrier does not establish full manuscript profile semantics or all R1-R9 and N1-N10 rules. Full manuscript VerifyDW, ChargeSoundness and Package E, global certificate discovery, terminal-family derivation and global route coverage remain open. There is no encoded-input polynomial runtime, output-size or certificate-size theorem for the complete construction. Unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin, deterministic CNFSAT in P and the eligible root remain open. No fixed weighted checkpoint or global gate closes, and P = NP is not proved.",
  "requiredTheorems": [
    "PNP.DirectWire.StructuralReindexing.result_gate_level",
    "PNP.DirectWire.StructuralReindexing.result_source_level",
    "PNP.DirectWire.StructuralReindexing.result_output_level",
    "PNP.DirectWire.WireCarrier.reindex_exposed",
    "PNP.DirectWire.WireCarrier.reindex_gateCount",
    "PNP.DirectWire.WireCarrier.reindex_backward_forward",
    "PNP.DirectWire.WireCarrier.reindex_forward_backward",
    "PNP.DirectWire.WireCarrier.reindex_output",
    "PNP.DirectWire.WireCarrier.reindex_field",
    "PNP.DirectWire.WireCarrier.reindex_field_source",
    "PNP.DirectWire.WireCarrier.reindex_exposed_level",
    "PNP.DirectWire.WireCarrier.reindex_output_level",
    "PNP.DirectWire.WireCarrier.reindex_field_level",
    "PNP.DirectWire.WireCarrier.reindex_causalBounds",
    "PNP.DirectWire.WireObligationHistory.State.reindex_pending",
    "PNP.DirectWire.WireObligationHistory.State.reindex_charged",
    "PNP.DirectWire.WireObligationHistory.State.reindex_removed",
    "PNP.DirectWire.WireObligationHistory.State.reindex_gateCount",
    "PNP.DirectWire.WireObligationHistory.State.reindex_causalInvariant",
    "PNP.DirectWire.WireStructuralState.execute_isSome",
    "PNP.DirectWire.WireStructuralState.execute_failure_iff",
    "PNP.DirectWire.WireStructuralState.Receipt.ownership_origin",
    "PNP.DirectWire.WireStructuralState.Receipt.ownership_origin_forward",
    "PNP.DirectWire.WireStructuralState.Receipt.ownership_origin_injective",
    "PNP.DirectWire.WireStructuralState.Receipt.ownership_live_members",
    "PNP.DirectWire.WireStructuralState.Receipt.ownership_not_allocated",
    "PNP.DirectWire.WireStructuralState.Receipt.ownership_charged",
    "PNP.DirectWire.WireStructuralState.Receipt.ownership_removed",
    "PNP.DirectWire.WireStructuralState.Receipt.ownership_wellFormed",
    "PNP.DirectWire.WireStructuralState.Receipt.physical_ownership",
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
    "PNP.DirectWire.WireOpenCertificate.verify_no_gain"
  ],
  "classification": "formalized-foundation-only"
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

test('M271 compiled interface: exact types, modules and axiom closures earn only the reviewed row', async () => {
  const {inventory, map, inventoryBytes, sourceClosure} = await sources0();
  assert.ok(canonical0(inventory).equals(inventoryBytes));
  const names = REVIEWED.map(row => row[0]);
  assert.equal(names.length, 63);
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

test('M271 compiled interface: weakening or supplying a conclusion cannot retain credit', async () => {
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
    'PNP.DirectWire.StructuralReindexing.result_source_level',
    'PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_origin',
    'PNP.DirectWire.WireOpenCertificate.verify_sound',
  ]) for (const kernelType of alternatives.get(name)) {
    const mutation = {...inventory, milestoneCandidates: inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), sourceClosure);
    assert.equal(result.milestones.find(row => row.id === MILESTONE.id).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
});

test('M271 compiled interface: missing evidence, added authority and widened scope reject', async () => {
  const {inventory, inventoryBytes, map, sourceClosure} = await sources0();
  const name = 'PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_origin';
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
  "coordinate": "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-17-271",
  "statusFields": {
    "leanStructuralProgramsFormalized": true,
    "leanStructuralProgramsAxiomAuditPassed": true,
    "leanStructuralProgramsAuditedDeclarationCount": 63,
    "leanStructuralProgramsGateCausalLabelTheorem": "PNP.DirectWire.StructuralReindexing.result_gate_level",
    "leanStructuralProgramsLiteralFieldSourceTheorem": "PNP.DirectWire.WireCarrier.reindex_field_source",
    "leanStructuralProgramsPendingSnapshotTheorem": "PNP.DirectWire.WireObligationHistory.State.reindex_pending",
    "leanStructuralProgramsRawCurrentCarrierDecodeTheorem": "PNP.DirectWire.WireStructuralState.execute_isSome",
    "leanStructuralProgramsRawRejectionTheorem": "PNP.DirectWire.WireStructuralState.execute_failure_iff",
    "leanStructuralProgramsLocalPhysicalOwnershipTheorem": "PNP.DirectWire.WireStructuralState.Receipt.physical_ownership",
    "leanStructuralProgramsHistoricalOriginTheorem": "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_origin",
    "leanStructuralProgramsHistoricalChargesTheorem": "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_charged",
    "leanStructuralProgramsHistoricalRemovalsTheorem": "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_removed",
    "leanStructuralProgramsCompleteProgramLifecycleTheorem": "PNP.DirectWire.WireOpenProgram.CompiledProgram.creation_lifecycle",
    "leanStructuralProgramsCompleteProgramCausalInvariantTheorem": "PNP.DirectWire.WireOpenProgram.CompiledProgram.causalInvariant",
    "leanStructuralProgramsCompleteProgramPhysicalOwnershipTheorem": "PNP.DirectWire.WireOpenProgram.CompiledProgram.physical_ownership",
    "leanStructuralProgramsCompleteCertificateSoundnessTheorem": "PNP.DirectWire.WireOpenCertificate.verify_sound",
    "leanStructuralProgramsStrictResidualDescentTheorem": "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictResidualDescent",
    "leanStructuralProgramsCheckedRawStructuralActionsDerived": true,
    "leanStructuralProgramsCurrentCarrierBoundsUsed": true,
    "leanStructuralProgramsCompleteRawSwapSequenceRequired": true,
    "leanStructuralProgramsExactPendingSnapshotsPreserved": true,
    "leanStructuralProgramsLiteralFieldSourcesPreserved": true,
    "leanStructuralProgramsWholeOutputAndFieldSemanticsPreserved": true,
    "leanStructuralProgramsAllInputCausalLabelsPreserved": true,
    "leanStructuralProgramsStructuralAllocationsAndRemovalsZero": true,
    "leanStructuralProgramsPreviousGlobalOwnersPreserved": true,
    "leanStructuralProgramsCompleteChargeAndRemovalHistoryPreserved": true,
    "leanStructuralProgramsCompleteAcceptedProgramRequired": true,
    "leanStructuralProgramsClosedFinalLedgerRequired": true,
    "leanStructuralProgramsProperSupportRequired": true,
    "leanStructuralProgramsStrictSignedSavingRequired": true,
    "leanStructuralProgramsCallerSuppliedOrderingOrMapsRequired": false,
    "leanStructuralProgramsCallerSuppliedCausalOrOwnershipWitnessRequired": false,
    "leanStructuralProgramsReorderingAloneEarnsStrictSaving": false,
    "leanStructuralProgramsAcceptsSuccessfulPrefixAfterFailedTail": false,
    "leanStructuralProgramsFullManuscriptProfileSemanticsProved": false,
    "leanStructuralProgramsAllNormalizationAndMaterializerRulesProved": false,
    "leanStructuralProgramsFullManuscriptVerifyDWProved": false,
    "leanStructuralProgramsCompleteChargeSoundnessAndPackageEProved": false,
    "leanStructuralProgramsGlobalCertificateDiscoveryProved": false,
    "leanStructuralProgramsTerminalFamiliesDerived": false,
    "leanStructuralProgramsGlobalRouteCoverageProved": false,
    "leanStructuralProgramsUnconditionalSaturatePositiveProved": false,
    "leanStructuralProgramsUnconditionalBCELReadyProved": false,
    "leanStructuralProgramsUnconditionalZeroSlackProved": false,
    "leanStructuralProgramsExactGeneralPCCMinProved": false,
    "leanStructuralProgramsPolynomialRuntimeOutputAndCertificateBoundsProved": false,
    "leanStructuralProgramsRuntimeExecutionIsProofAuthority": false,
    "leanStructuralProgramsScope": "arbitrary-finite-source-only-complete-programs-computed-current-carrier-raw-structural-actions-literal-field-wires-exact-causal-labels-pending-snapshots-zero-local-cost-prior-global-owners-and-history-closed-ledger-proper-support-strict-saving-no-global-discovery-or-full-manuscript-or-polynomial-claim"
  },
  "command": "node --test audits/lean-structural-programs0.test.mjs audits/lean-structural-programs-publication0.test.mjs",
  "testFiles": [
    "audits/lean-structural-programs0.test.mjs",
    "audits/lean-structural-programs-publication0.test.mjs"
  ],
  "audit": "lean-audit/PNPStructuralProgramsAxiomAudit.lean",
  "parts": [
    "ReindexingCausalBounds",
    "WireStructuralState",
    "WireStructuralOwnership",
    "WireStructuralProgram",
    "WireStructuralCertificate"
  ],
  "workflowCommands": "set -euo pipefail\nnode scripts/check-lean-axioms.mjs lean-audit/PNPStructuralProgramsAxiomAudit.lean\nfor part in ReindexingCausalBounds WireStructuralState WireStructuralOwnership WireStructuralProgram WireStructuralCertificate; do\n  lake env lean -DwarningAsError=true \"lean-regression/PNP${part}.lean\"\ndone\n",
  "publicationDecision": "Publication decision: defer. This integrates computed structural actions into complete offered replacement programs, but does not establish a global discovery strategy, full manuscript profiles or a polynomial algorithm. No fixed weighted checkpoint or global gate changes, and the published global bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.",
  "rationale": "M271 integrates computed structural reordering into complete source-only replacement programs. Literal field wires, exact causal labels and pending snapshots are preserved. Local physical ownership uses the actual backward bijection with no allocation or removal, and the complete ledger retains earlier global identities and charge/removal history. Proper-support verification still requires complete acceptance, a closed final ledger and actual strict saving; invalid tails and reordering without gain receive no certificate. This retires a computational integration edge, not full manuscript profiles, all normalization/materializer rules, global certificate discovery, unconditional residual theorems or polynomial bounds. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.",
  "doc": "docs/lean_structural_programs.md",
  "plan": "docs/plans/2026-09-17-structural-program-integration.md"
};
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();
async function release0() {
  const [statusText, progressText] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('status/PROOF_PROGRESS.json'),
  ]);
  return {status: JSON.parse(statusText), progress: JSON.parse(progressText)};
}

test('M271 release preflight: package, exact workflow and status commands share one interface', async () => {
  const [pkg, surface, verifier, workflow, statusSource, statusText] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'), text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'), text0('pcc-formal-reconstruction-status0.mjs'),
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  ]);
  assert.equal(JSON.parse(pkg).scripts['audit:m271'], META.command);
  assert.ok(surface.includes("'audit:m271': '" + META.command + "'"));
  for (const file of META.testFiles) assert.ok(verifier.includes("'" + file + "'"), file);
  assert.ok(workflow.includes('run: npm run audit:m271'));
  const steps = workflow.split(/^      - name:/mu).filter(step =>
    step.includes('node scripts/check-lean-axioms.mjs ' + META.audit));
  assert.equal(steps.length, 1);
  const block = steps[0].split('        run: |\n')[1];
  assert.ok(block);
  assert.equal(block.trimEnd().split('\n').map(line => line.slice(10)).join('\n') + '\n', META.workflowCommands);
  const status = JSON.parse(statusText);
  for (const command of [
    'npm run audit:m271', 'node scripts/check-lean-axioms.mjs ' + META.audit,
    ...META.parts.map(part => 'lake env lean -DwarningAsError=true lean-regression/PNP' + part + '.lean'),
  ]) assert.ok(status.verificationCommands.includes(command), command);
  for (const field of Object.keys(META.statusFields))
    assert.equal(statusSource.split(field + ':').length - 1, 2, field);
});

test('M271 release: status pins the exact bounded claims and rejects every changed field', async () => {
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

test('M271 release: computational integration earns no unconditional checkpoint', async () => {
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

test('M271 release: every current summary and FAQ uses the canonical independent metrics', async () => {
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
      assert.ok(boundary?.includes('M271'));
      assert.ok(boundary.includes('global certificate discovery'));
    }
    if (['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
      'docs/proof_pipeline.md', 'docs/audit_questions.md'].includes(file)) {
      const region = text.split('<!-- M271-CURRENT-SUMMARY:BEGIN -->')[1]?.split('<!-- M271-CURRENT-SUMMARY:END -->')[0];
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
