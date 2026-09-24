import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  DeriveFormalPublication0, MilestoneTheoremKernelTypeSha2560, stableStringify0, REQUIRED_MILESTONE_THEOREMS0,
} from '../formal-publication0.mjs';
import {CheckFormalReconstructionStatus0} from '../pcc-formal-reconstruction-status0.mjs';
import {validateProofProgress0} from '../pcc-proof-progress0.mjs';

// These frozen type fingerprints and exact axiom closures were reviewed against
// the compiled M265 dependency closure; the explicit-root audit must agree. Tests must not regenerate their own expectations.
const REVIEWED = [
  [
    "PNP.DirectWire.RawNandCompilationState.finish_position",
    "d132e92cc600951248a7c4d18ccd2536f545fb5d637d63901fe5884e22a78e99",
    "PNP.NANDTopologicalCompiler",
    []
  ],
  [
    "PNP.DirectWire.RawNandCausalBound.compile_bounds",
    "6d644822bc7e6a5a5a86b5ba70e882dd3bb62616ad979df6462bad85e5a2273b",
    "PNP.NANDTopologicalCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.RawNandCausalBound.candidate_bound",
    "b4bcf059257172153564d9ad29ab2c7d5b689469ab3e48974667f80cf6cc5ba6",
    "PNP.NANDTopologicalCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ArbitrarySupportSplice.graph_dependency_bounds",
    "e55461cefebaf2cce8759494d7894d57cd953c21a29f377c6eb8f5ae94fa87cf",
    "PNP.NANDArbitrarySupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ArbitrarySupportSplice.result_output_dependency_bound",
    "0bb8f943b2343b78770051263c7cbf575d5fac297e15fb5f5fa7f35ccdf34006",
    "PNP.NANDArbitrarySupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireUnaryCausalBound.implementation_output_bound",
    "a498c50f7907bc63d7de888a5055f6a59a7c1a31fe59a596855f1a5e95af7f68",
    "PNP.NANDWireUnaryCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireUnaryCausalBound.constantWord_output_bound",
    "6d8fbf7f8d2490aaa8e0d1ed8c4a19fa3d6c4c3e4a1ee38659907a7c980373d5",
    "PNP.NANDWireUnaryCausalBounds",
    []
  ],
  [
    "PNP.DirectWire.WireUnaryCausalBound.localWord_output_bound",
    "3a1a2b6d7ff7e15070ed812ed62d0cfec00883d78001d1fdef272391807996cd",
    "PNP.NANDWireUnaryCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireUnaryCausalBound.arbitrary_replacement_output_bound",
    "cfda0022edafc82313990497df2a60e3fa9d8a719157700cb89be2722fb8a263",
    "PNP.NANDWireUnaryCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireUnaryCausalBound.compiled_spec",
    "d4d6651356de9cf54f61e97387ea2ff19fdc85a78ee619f4c998828a25811765",
    "PNP.NANDWireUnaryCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireUnaryCausalBound.replacement_dependency_bound",
    "db56391c15729c5acf6174ae0832aec317ce7073f46eb95eb69ecb4912f141ba",
    "PNP.NANDWireUnaryCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireUnaryCausalBound.expanded_exposed_bound",
    "808d3b5c4ea0f2dcf19d291734763344fdad5f318aad9383d0d674e4992cda8f",
    "PNP.NANDWireUnaryCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireUnaryCausalBound.expanded_causalBounds",
    "ff684b781c2202031f4c0a68b677fe598fe7b176df45488c5aaf65fabfabcfe7",
    "PNP.NANDWireUnaryCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireUnaryCausalBound.attempt_causalBounds",
    "e9d2762c2330932afec39766a12d19b088ee74fc0f12671edf734f06d980f22f",
    "PNP.NANDWireUnaryCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.decodeRecord_encode",
    "c1c1fc876e31185204ecee23a6e7b19013726a825ba08fb2a9b0ec5f045715ce",
    "PNP.NANDWireObligationHistoryR7",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.decodeRecord_source",
    "08275451007126789a96f6997f750ecc028d5052524aca2ea8fc44013f381090",
    "PNP.NANDWireObligationHistoryR7",
    []
  ],
  [
    "PNP.DirectWire.WireObligationHistory.decodeRecords_encode",
    "b04faf388a4c7a24baa0ae7aa1d0ec33c1608a5bbb859b3ff166a0b07f1338ac",
    "PNP.NANDWireObligationHistoryR7",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.decodeRecords_source",
    "4a14bb1202417fa4aa25e238d7677571d88fb29fe13b7afb110b440eadacd245",
    "PNP.NANDWireObligationHistoryR7",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.computeR7_isSome_iff",
    "3903b0ad1fbbf870510cb9c7fb35ff32ec3bee103f80ec06fa6a2f67e178fe08",
    "PNP.NANDWireObligationHistoryR7",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.R7Realization.full_field",
    "7699f8e957edbd66a9bc5c13240e992e05a399071c6c40bbffced57240455f19",
    "PNP.NANDWireObligationHistoryR7",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.R7Realization.exact_charge",
    "3e3cd9fba51b50d94bf57a05e2ba8720a9db4283a6a8559e1863a0e28771d62d",
    "PNP.NANDWireObligationHistoryR7",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.R7Realization.causalBounds",
    "3ed206f861600cca01fa52d00a7494bb45615a7fb7f5a00851d8129fea8f0268",
    "PNP.NANDWireObligationHistoryR7",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.State.restoreR7_gate_charge",
    "cb3ffbc194c947db003584bcb22fb2c956ad0b9e28ffe0153d5f352dcbbfe4de",
    "PNP.NANDWireObligationHistoryR7",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.State.restoreR7_full_value",
    "a26fa69df0f4160df11ab52c810ee9f4f8cebc0df437f6dc25ffb1e199fce0c0",
    "PNP.NANDWireObligationHistoryR7",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.State.restoreR7_other_pending",
    "aa65f63e76312b2484bea839b25d493f8d4976695f5e9de8443e8697939a5fff",
    "PNP.NANDWireObligationHistoryR7",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.State.restoreR7_causalInvariant",
    "f1a777649c0537a2e5d5bc5a638fd50460e249bb8860bc286003816278397557",
    "PNP.NANDWireHistoryCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.Transition.causalInvariant",
    "5e8e6b3008a3ae5e6eae219e5642bd71496d4c78a6fe24cc00f06d8579bc25c1",
    "PNP.NANDWireHistoryCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.ClosedHistory.causalInvariant",
    "d766a4d18cd18b8fc41844f5862a1db0293043ad3be6711bf2f183584391b9b7",
    "PNP.NANDWireHistoryCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.ClosedHistory.field_causal_bound",
    "aa051739783a3bcf78c4cfd030bda11ebb4191071367ac5a9cd09d2f63f2dcb8",
    "PNP.NANDWireHistoryCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.ClosedHistory.full_output",
    "b424d42f293c35731c15c87699685a7276d36f6535dc9df10d94038525f92c63",
    "PNP.NANDWireObligationHistoryExecution",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.ClosedHistory.full_field",
    "c693beecbd081a97a4cbb69a8d352963830e1ef59577d90930adbc208a3f111f",
    "PNP.NANDWireObligationHistoryExecution",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.ClosedHistory.gate_balance",
    "1f6a44c3ae70e9bd68aa2f4c27ee53ca15d367bf7537504601368e758bc05207",
    "PNP.NANDWireObligationHistoryExecution",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.ClosedHistory.creation_lifecycle",
    "931d176535e4d513f8d0c55154d78e8ceb5046c4f00de10429bcaba5e91bbc66",
    "PNP.NANDWireObligationHistoryExecution",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationHistory.ClosedHistory.dependency_before",
    "eb9fd5eeb6da03880e4e567c1150d9f788db315013c32ec064dc78c0e551010d",
    "PNP.NANDWireObligationHistoryExecution",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_compiles",
    "24628ba7c42242ba62325ae3a02a86c5da4afa69372ee4a8db95369cb2c54177",
    "PNP.NANDWireHistoryArbitrarySupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_result_semantics",
    "3ff01612253857a44f687e7850d60a8c0895046ef5ab7a5bd4190dab27453031",
    "PNP.NANDWireHistoryArbitrarySupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_result_exact_accounting",
    "ba21db1c802ed21d062b78b1a28939a1cac493aba356401f9981e460e076f323",
    "PNP.NANDWireHistoryArbitrarySupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_result_strict_gain",
    "e6abcd11b0d7e89b0c908788f665a71b2d7576be1ff9a7396e36821647e91770",
    "PNP.NANDWireHistoryArbitrarySupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.compile_complete",
    "e4dbaa109b94d8d0704c04d90f776e755c079b7c6e303cb5097cc985df6a6756",
    "PNP.NANDWireHistoryArbitrarySupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.compile_sound",
    "7f2ab5eee8236bc96b3ab1f3d1a0edb44631fef986b0c8f0a67f0f7668ba3def",
    "PNP.NANDWireHistoryArbitrarySupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.compile_none_iff",
    "b83a398e1ac68926f820d96f95b7e9e21042f8fabcecbbd0fad685a544eeaffb",
    "PNP.NANDWireHistoryArbitrarySupport",
    [
      "Quot.sound",
      "propext"
    ]
  ]
];
const STATUS_FIELDS = {
  "leanComputedR7HistoryFormalized": true,
  "leanComputedR7HistoryAxiomAuditPassed": true,
  "leanComputedR7HistoryAuditedDeclarationCount": 41,
  "leanComputedR7HistoryActualCompilerDependencyBoundTheorem": "PNP.DirectWire.RawNandCausalBound.compile_bounds",
  "leanComputedR7HistoryWholeCarrierDependencyBoundTheorem": "PNP.DirectWire.WireUnaryCausalBound.expanded_causalBounds",
  "leanComputedR7HistoryRawRecordRoundTripTheorem": "PNP.DirectWire.WireObligationHistory.decodeRecord_encode",
  "leanComputedR7HistoryRawRecordSourceTheorem": "PNP.DirectWire.WireObligationHistory.decodeRecord_source",
  "leanComputedR7HistoryRawListRoundTripTheorem": "PNP.DirectWire.WireObligationHistory.decodeRecords_encode",
  "leanComputedR7HistoryRawListSourceTheorem": "PNP.DirectWire.WireObligationHistory.decodeRecords_source",
  "leanComputedR7HistoryRecognitionIffTheorem": "PNP.DirectWire.WireObligationHistory.computeR7_isSome_iff",
  "leanComputedR7HistoryCapturedFullValueTheorem": "PNP.DirectWire.WireObligationHistory.State.restoreR7_full_value",
  "leanComputedR7HistoryActualMaterializerChargeTheorem": "PNP.DirectWire.WireObligationHistory.State.restoreR7_gate_charge",
  "leanComputedR7HistoryOtherPendingSnapshotsTheorem": "PNP.DirectWire.WireObligationHistory.State.restoreR7_other_pending",
  "leanComputedR7HistoryTransitionCausalInvariantTheorem": "PNP.DirectWire.WireObligationHistory.State.restoreR7_causalInvariant",
  "leanComputedR7HistorySourceCreationLifecycleTheorem": "PNP.DirectWire.WireObligationHistory.ClosedHistory.creation_lifecycle",
  "leanComputedR7HistoryClosedHistoryCompilationTheorem": "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_compiles",
  "leanComputedR7HistoryCompletePhysicalAccountingTheorem": "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_result_exact_accounting",
  "leanComputedR7HistoryNoAdditionalRejectionTheorem": "PNP.DirectWire.WireHistoryArbitrarySupport.compile_none_iff",
  "leanComputedR7HistoryArbitraryFiniteCarrierSupportAndEventDimensionsCovered": true,
  "leanComputedR7HistoryWholeListCoordinatesPreserved": true,
  "leanComputedR7HistoryExactZeroUnaryRecognitionDerived": true,
  "leanComputedR7HistoryCapturedCreationIdentityRequired": true,
  "leanComputedR7HistoryActualComputedReplacementAndMaterializerUsed": true,
  "leanComputedR7HistoryCurrentAndPendingSnapshotCausalBoundsDerived": true,
  "leanComputedR7HistoryCompleteMaterializerChargesIncluded": true,
  "leanComputedR7HistoryLiteralOneCopySpliceAddsNoRejection": true,
  "leanComputedR7HistoryCallerSuppliedReplacementRequired": false,
  "leanComputedR7HistoryCallerSuppliedTruthTableRequired": false,
  "leanComputedR7HistoryCallerSuppliedRankOrOrderRequired": false,
  "leanComputedR7HistoryCallerSuppliedSemanticCertificateRequired": false,
  "leanComputedR7HistoryBooleanEquivalenceAloneBoundsDependencies": false,
  "leanComputedR7HistorySupportRecordsAndRawEventsDerivedFromEveryInput": false,
  "leanComputedR7HistoryFullManuscriptR7SemanticsProved": false,
  "leanComputedR7HistoryAllManuscriptRewriteAndNormalizationFamiliesProved": false,
  "leanComputedR7HistoryArbitraryObserverOrFullProfileTransportProved": false,
  "leanComputedR7HistoryCompletePackageEProved": false,
  "leanComputedR7HistoryTerminalFamiliesDerived": false,
  "leanComputedR7HistoryGloballySuccessfulRewriteStrategyDerived": false,
  "leanComputedR7HistoryGlobalRouteCoverageProved": false,
  "leanComputedR7HistoryUnconditionalSaturatePositiveProved": false,
  "leanComputedR7HistoryUnconditionalBCELReadyProved": false,
  "leanComputedR7HistoryUnconditionalZeroSlackProved": false,
  "leanComputedR7HistoryExactGeneralPCCMinProved": false,
  "leanComputedR7HistoryPolynomialRuntimeOutputAndCertificateBoundsProved": false,
  "leanComputedR7HistoryRuntimeExecutionIsProofAuthority": false,
  "leanComputedR7HistoryScope": "arbitrary-finite-computational-carriers-raw-record-lists-exact-zero-unary-recognition-source-derived-R7-captured-creation-full-discharge-actual-materializer-charges-derived-causality-closed-R5-R6-R7-R8-histories-literal-one-copy-splice-no-new-rejection-no-derived-global-strategy-or-complete-manuscript-calculus-or-polynomial-runtime"
};
const COORDINATE = "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-16-265";
const MILESTONE = "computed-r7-history";
const SCOPE = "For arbitrary finite computational carriers, support lists and raw-event dimensions, R7 decodes every gate, boundary and interface coordinate against the immutable carrier of the identified open creation. Whole lists round-trip without dropping or substituting coordinates. Recognition succeeds exactly when decoding succeeds and the actual completed boundary has at most one port. The replacement is computed from that source's complete zero/unary open function, never from a supplied implementation, truth table or correctness certificate. Labelled dependency bounds follow the actual topological compiler and the literal replacement, not Boolean equivalence alone. The resulting full-field materializer discharges the exact captured creation, charges every appended gate, preserves ordinary outputs and other pending snapshots, and preserves the current-and-snapshot causal invariant. The extended raw R5/R6/R7/R8 history retains full lifecycle closure and exact physical accounting. Every accepted closed history still admits the literal one-copy ambient splice without an additional supplied rank, order, agreement or successful-compilation premise; strict gain requires actual removals to exceed all charges.";
const NON_CLAIM = "This is the zero/unary R7 extension of the computational history language, not the complete manuscript R1-R9 or N1-N10 calculus, arbitrary observers, noncomputational carriers, full-profile compatibility, matched-kappa Pull/Expand or complete Package E. Support coordinates and raw events remain input data; the result does not derive terminal families or a globally successful rewrite strategy. Global route coverage, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin and complete encoded-input polynomial runtime, output and certificate bounds remain open. Boolean soundness alone does not bound syntactic dependencies. Materialization can increase physical size, and finite runtime fixtures are regression evidence, not proof authority. No fixed weighted checkpoint or global gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.";
const TEST_FILES = [
  "audits/lean-computed-r7-causal-contracts0.test.mjs",
  "audits/lean-computed-r7-history0.test.mjs",
  "audits/lean-computed-r7-history-publication0.test.mjs"
];
const AUDIT = "lean-audit/PNPComputedR7HistoryAxiomAudit.lean";
const REGRESSION = "lean-regression/PNPComputedR7History.lean";
const DOCUMENTATION = "docs/lean_computed_r7_history.md";
const PLAN = "docs/plans/2026-09-15-computed-r7-history-discharge.md";
const COMMAND = 'node --test ' + TEST_FILES.join(' ');
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const canonical0 = value => Buffer.from(stableStringify0(value) + '\n');
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();

test('M265 preflight: package, verifier and durable CI share the exact audited boundary', async () => {
  const [pkg,surface,verifier,workflow] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  assert.equal(REVIEWED.length, 41);
  assert.equal(new Set(REVIEWED.map(row => row[0])).size, 41);
  assert.equal(JSON.parse(pkg).scripts['audit:m265'], COMMAND);
  assert.ok(surface.includes("'audit:m265': '" + COMMAND + "'"));
  for (const file of TEST_FILES) assert.ok(verifier.includes("'" + file + "'"), file);
  assert.ok(workflow.includes(COMMAND));
  for (const file of [REGRESSION, "lean-regression/PNPComputedR7CausalBounds.lean"])
    assert.ok(workflow.includes('lake env lean -DwarningAsError=true ' + file), file);
  const auditSteps = workflow.split(/^      - name:/mu).filter(step =>
    step.includes('node scripts/check-lean-axioms.mjs ' + AUDIT));
  assert.equal(auditSteps.length, 1);
  const helper = await text0('scripts/check-lean-axioms.mjs');
  for (const fragment of ["'status/LEAN_THEOREM_INVENTORY.json'", '.declarations',
    'const expected=names.map(name=>{', 'inventory.filter(row=>row.name===name)',
    "assert.equal(row.kind,'theorem',name);", 'return [name,row.axioms];',
    "spawnSync('lake',['env','lean','-DwarningAsError=true',audit]",
    'CheckLeanAxiomTranscript0(result.stdout,auditSource,inventory)'])
    assert.ok(helper.includes(fragment), fragment);
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

test('M265 release: exact compiled types, axiom closures and limited claims match review', async () => {
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

test('M265 release: every reviewed type rejects weakening and supplied proof authority', async () => {
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

test('M265 release: hidden authority, absent evidence and widened publication claims reject', async () => {
  const {status,inventory,inventoryBytes,map} = await sources0();
  const name = 'PNP.DirectWire.WireHistoryArbitrarySupport.compile_sound';
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
      ? {...row,[field]:'Boolean equivalence proves unconditional polynomial ZeroSlack with free restoration.'} : row)};
    assert.throws(() => DeriveFormalPublication0(inventory,widened,inventoryBytes,status.leanSourceClosureSha256),
      /map drifted from the reviewed specification/u);
  }
  const changedPin = {...map,earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256,[name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory,changedPin,inventoryBytes,status.leanSourceClosureSha256),
    /map drifted from the reviewed specification/u);
});

test('M265 release: status rejects changed construction, accounting and runtime claims', async () => {
  const {status} = await sources0();
  for (const suffix of ['CompletePhysicalAccountingTheorem','AuditedDeclarationCount',
    'BooleanEquivalenceAloneBoundsDependencies','SupportRecordsAndRawEventsDerivedFromEveryInput',
    'PolynomialRuntimeOutputAndCertificateBoundsProved','Scope']) {
    const field = 'leanComputedR7History' + suffix;
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

test('M265 release: source-derived literal replacement earns no unconditional checkpoint', async () => {
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

test('M265 release: current documentation reports separate metrics and justified publication', async () => {
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

test('M265 preflight: explicit-root audit and both inventory producers retain every reviewed name',async()=>{
  const [audit,probe] = await Promise.all([text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean')]);
  assert.match(audit,/^import PNP$/mu);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),REVIEWED.map(row=>row[0]));
  for (const [name] of REVIEWED) {
    assert.equal(probe.split(String.fromCharCode(96)+name+',').length-1,1,name);
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(value=>value===name).length,1,name);
  }
});
