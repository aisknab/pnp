import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  DeriveFormalPublication0, MilestoneTheoremKernelTypeSha2560, stableStringify0,
} from '../formal-publication0.mjs';
import {CheckFormalReconstructionStatus0} from '../pcc-formal-reconstruction-status0.mjs';
import {validateProofProgress0} from '../pcc-proof-progress0.mjs';

// These frozen type fingerprints and exact axiom closures were reviewed against
// the compiled M264 root. Tests must not regenerate their own expectations.
const REVIEWED = [
  [
    "PNP.DirectWire.extractTerminalSupport_causal_levels",
    "123e68b3b62bd7450cceb874b37e9133aa7f5bef061c5fd3a7b86006ab209b36",
    "PNP.ResidualTerminalSupportExtraction",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.extractTerminalSupport_causal_index",
    "266f2d202c756ac3d535808efc7288371be039b7bd6f3334471a4eb4a09126dc",
    "PNP.ResidualTerminalSupportExtraction",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.CausalBound.physical_normalization_output_bound",
    "a6fb41b87c15347278653ccabf0f339b0021e1ff7f00aaf2a6ae3593f5ff8ab8",
    "PNP.NANDNormalizationCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrier.normalize_causalBounds",
    "62d2b55983b9459d9c8a4ec3729e24b6757e22aa464e831b36f780edc19534c0",
    "PNP.NANDWireCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireObligationRestoration.join_causalBounds",
    "96a57b1e39fa62e703469131981a9464a954c6e6ef93a968c9363130492cdfef",
    "PNP.NANDWireCausalBounds",
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
    "PNP.DirectWire.WireObligationHistory.Execution.causalInvariant",
    "7eeda6beaebe55aefa689012673e7b2aad279c3a1f98270a8c045d149109de1d",
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
    "PNP.DirectWire.WireObligationHistory.compileHistory_causal_bounds",
    "d85cb81dde3ff4b72e81c8fd56bbfd521031f13dc86cad93f30a84b5888f452e",
    "PNP.NANDWireHistoryCausalBounds",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ArbitrarySupportSplice.graph_causal_rank_decreases",
    "401cb888e0fdd3fffd02d24c5f5a46d0ec23a3370a61e1c298b3efa086a83f1a",
    "PNP.NANDArbitrarySupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ArbitrarySupportSplice.graph_wellFounded_of_causalInterfaceBound",
    "47cf35847af614649c6e8f5d929c8447d2a3fcd036119a9cbdb98ca5f9a12e38",
    "PNP.NANDArbitrarySupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ArbitrarySupportSplice.compile_of_causalInterfaceBound",
    "66036c51abd18c65462094db35c49f463b6e40944fb0f40f06bc4ecdb9a63c79",
    "PNP.NANDArbitrarySupportSplice",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.extractedCarrier_gateCount",
    "5b11e6ffa16f80744a224cc5fcaad6a3d2132ca68567e8e0a1b9aeda0e45eae2",
    "PNP.NANDWireHistoryArbitrarySupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.extractedCarrier_fieldValue",
    "c4513e607a0d66901d00b788ed6c1884105fb8e2d8d6bc6d9c96df55583250c5",
    "PNP.NANDWireHistoryArbitrarySupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_equivalent",
    "b949f2d62101de6687ded05b81d36f3b11b48ebdd722a7d69a8a2d4eb158124d",
    "PNP.NANDWireHistoryArbitrarySupport",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_causalInterfaceBound",
    "bb37db6c982b6fc8e1a879a0c2c5e8a1669fec6d7939d8ff024b205dcd546903",
    "PNP.NANDWireHistoryArbitrarySupport",
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
  "leanWireHistoryArbitrarySupportFormalized": true,
  "leanWireHistoryArbitrarySupportAxiomAuditPassed": true,
  "leanWireHistoryArbitrarySupportAuditedDeclarationCount": 24,
  "leanWireHistoryArbitrarySupportExtractionCausalLevelsTheorem": "PNP.DirectWire.extractTerminalSupport_causal_levels",
  "leanWireHistoryArbitrarySupportExtractionCausalIndexTheorem": "PNP.DirectWire.extractTerminalSupport_causal_index",
  "leanWireHistoryArbitrarySupportPhysicalNormalizationCausalBoundTheorem": "PNP.DirectWire.CausalBound.physical_normalization_output_bound",
  "leanWireHistoryArbitrarySupportCapturedRestorationCausalBoundTheorem": "PNP.DirectWire.WireObligationRestoration.join_causalBounds",
  "leanWireHistoryArbitrarySupportClosedHistoryCausalInvariantTheorem": "PNP.DirectWire.WireObligationHistory.ClosedHistory.causalInvariant",
  "leanWireHistoryArbitrarySupportClosedHistoryFieldCausalBoundTheorem": "PNP.DirectWire.WireObligationHistory.ClosedHistory.field_causal_bound",
  "leanWireHistoryArbitrarySupportLiteralGraphRankDecreaseTheorem": "PNP.DirectWire.ArbitrarySupportSplice.graph_causal_rank_decreases",
  "leanWireHistoryArbitrarySupportLiteralGraphWellFoundedTheorem": "PNP.DirectWire.ArbitrarySupportSplice.graph_wellFounded_of_causalInterfaceBound",
  "leanWireHistoryArbitrarySupportClosedHistoryEquivalentTheorem": "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_equivalent",
  "leanWireHistoryArbitrarySupportDerivedInterfaceBoundTheorem": "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_causalInterfaceBound",
  "leanWireHistoryArbitrarySupportClosedHistoryCompilationTheorem": "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_compiles",
  "leanWireHistoryArbitrarySupportOrderedOutputSemanticsTheorem": "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_result_semantics",
  "leanWireHistoryArbitrarySupportCompletePhysicalAccountingTheorem": "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_result_exact_accounting",
  "leanWireHistoryArbitrarySupportStrictGainTheorem": "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_result_strict_gain",
  "leanWireHistoryArbitrarySupportRawConstructorCompleteTheorem": "PNP.DirectWire.WireHistoryArbitrarySupport.compile_complete",
  "leanWireHistoryArbitrarySupportRawConstructorSoundTheorem": "PNP.DirectWire.WireHistoryArbitrarySupport.compile_sound",
  "leanWireHistoryArbitrarySupportNoAdditionalRejectionTheorem": "PNP.DirectWire.WireHistoryArbitrarySupport.compile_none_iff",
  "leanWireHistoryArbitrarySupportArbitraryFiniteCandidateSupportAndEventDimensionsCovered": true,
  "leanWireHistoryArbitrarySupportZeroDuplicateOrdinaryOutputsInExtractedCarrier": true,
  "leanWireHistoryArbitrarySupportCurrentAndPendingSnapshotCausalBoundsDerived": true,
  "leanWireHistoryArbitrarySupportActualPhysicalNormalizerAndCapturedMaterializerUsed": true,
  "leanWireHistoryArbitrarySupportSourceIdentityCancellationPreserved": true,
  "leanWireHistoryArbitrarySupportLiteralOneCopySpliceAfterEveryAcceptedClosedHistory": true,
  "leanWireHistoryArbitrarySupportEveryOrderedOriginalOutputPreserved": true,
  "leanWireHistoryArbitrarySupportCompleteMaterializerChargesIncluded": true,
  "leanWireHistoryArbitrarySupportStrictGainRequiresRemovalsExceedCharges": true,
  "leanWireHistoryArbitrarySupportSpliceStageAddsNoRejection": true,
  "leanWireHistoryArbitrarySupportCallerSuppliedReplacementRequired": false,
  "leanWireHistoryArbitrarySupportCallerSuppliedRankOrOrderRequired": false,
  "leanWireHistoryArbitrarySupportCallerSuppliedSemanticCertificateRequired": false,
  "leanWireHistoryArbitrarySupportBooleanEquivalenceAloneEnsuresAcyclicity": false,
  "leanWireHistoryArbitrarySupportSupportRecordsAndRawEventsDerivedFromEveryInput": false,
  "leanWireHistoryArbitrarySupportFullR7SemanticsProved": false,
  "leanWireHistoryArbitrarySupportAllManuscriptRewriteAndNormalizationFamiliesProved": false,
  "leanWireHistoryArbitrarySupportArbitraryObserverOrFullProfileTransportProved": false,
  "leanWireHistoryArbitrarySupportMatchedKappaPullExpandProved": false,
  "leanWireHistoryArbitrarySupportFullManuscriptCarrierProved": false,
  "leanWireHistoryArbitrarySupportCompletePackageEProved": false,
  "leanWireHistoryArbitrarySupportTerminalFamiliesDerived": false,
  "leanWireHistoryArbitrarySupportGloballySuccessfulRewriteStrategyDerived": false,
  "leanWireHistoryArbitrarySupportGlobalRouteCoverageProved": false,
  "leanWireHistoryArbitrarySupportUnconditionalSaturatePositiveProved": false,
  "leanWireHistoryArbitrarySupportUnconditionalBCELReadyProved": false,
  "leanWireHistoryArbitrarySupportUnconditionalZeroSlackProved": false,
  "leanWireHistoryArbitrarySupportExactGeneralPCCMinProved": false,
  "leanWireHistoryArbitrarySupportPolynomialRuntimeOutputAndCertificateBoundsProved": false,
  "leanWireHistoryArbitrarySupportRuntimeExecutionIsProofAuthority": false,
  "leanWireHistoryArbitrarySupportScope": "arbitrary-finite-source-extraction-closed-R5-R6-R8-history-derived-current-and-snapshot-causality-literal-one-copy-splice-all-ordered-outputs-complete-removal-charge-equation-no-additional-rejection-no-derived-terminal-family-global-route-or-polynomial-runtime"
};
const COORDINATE = "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-15-264";
const MILESTONE = "wire-history-arbitrary-support";
const SCOPE = "For arbitrary finite candidate, support and raw-event dimensions, the constructor extracts actual computational fields with zero duplicate ordinary outputs, executes the existing closed R5/R6/R8 history, and derives literal-splice acyclicity from original gate labels and actual causal bounds. The current carrier and every pending snapshot preserve those bounds through actual normalization, source-identity cancellation and paid captured restoration. The existing literal graph compiler then succeeds for every accepted closed history without a caller-supplied replacement, rank, order or semantic certificate. All ordered original outputs are preserved; every exterior gate occurs once; final gates plus actual removals equal original gates plus all actual materializer charges. Strict gain follows when removals exceed charges. The splice stage introduces no rejection beyond the actual history compiler.";
const NON_CLAIM = "This covers the existing computational R5/R6/R8 language and three-pass physical normalizer, not all manuscript R1-R9 or N1-N10 rules, full R7, arbitrary observers, noncomputational carriers, full-profile compatibility, matched-kappa Pull/Expand or complete Package E. The support records and raw history remain input data. It does not derive terminal families, a globally successful rewrite strategy, global route coverage, unconditional SaturatePositive, BCELReady or ZeroSlack, exact general PCCMin or complete encoded-input polynomial runtime/output/certificate bounds. Boolean equivalence alone is not a causal certificate. Runtime fixtures are regression evidence, not proof authority. No fixed weighted checkpoint or global gate closes; deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.";
const TEST_FILES = [
  "audits/lean-wire-history-arbitrary-support0.test.mjs",
  "audits/lean-wire-history-arbitrary-support-publication0.test.mjs"
];
const AUDIT = "lean-audit/PNPWireHistoryArbitrarySupportAxiomAudit.lean";
const REGRESSION = "lean-regression/PNPWireHistoryArbitrarySupport.lean";
const DOCUMENTATION = "docs/lean_wire_history_arbitrary_support.md";
const PLAN = "docs/plans/2026-09-15-source-derived-history-arbitrary-support.md";
const COMMAND = 'node --test ' + TEST_FILES.join(' ');
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const canonical0 = value => Buffer.from(stableStringify0(value) + '\n');
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();

test('M264 preflight: package, verifier and durable CI share the exact audited boundary', async () => {
  const [pkg,surface,verifier,workflow] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  assert.equal(REVIEWED.length, 24);
  assert.equal(new Set(REVIEWED.map(row => row[0])).size, 24);
  assert.equal(JSON.parse(pkg).scripts['audit:m264'], COMMAND);
  assert.ok(surface.includes("'audit:m264': '" + COMMAND + "'"));
  for (const file of TEST_FILES) assert.ok(verifier.includes("'" + file + "'"), file);
  assert.ok(workflow.includes(COMMAND));
  for (const file of [AUDIT, REGRESSION])
    assert.ok(workflow.includes('lake env lean -DwarningAsError=true ' + file), file);
  for (const [name] of REVIEWED)
    assert.equal(workflow.split('"' + name + '"').length - 1, 1, name);
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

test('M264 release: exact compiled types, axiom closures and limited claims match review', async () => {
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

test('M264 release: every reviewed type rejects weakening and supplied proof authority', async () => {
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

test('M264 release: hidden authority, absent evidence and widened publication claims reject', async () => {
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

test('M264 release: status rejects changed construction, accounting and runtime claims', async () => {
  const {status} = await sources0();
  for (const suffix of ['CompletePhysicalAccountingTheorem','AuditedDeclarationCount',
    'BooleanEquivalenceAloneEnsuresAcyclicity','SupportRecordsAndRawEventsDerivedFromEveryInput',
    'PolynomialRuntimeOutputAndCertificateBoundsProved','Scope']) {
    const field = 'leanWireHistoryArbitrarySupport' + suffix;
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

test('M264 release: source-derived literal replacement earns no unconditional checkpoint', async () => {
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

test('M264 release: current documentation reports separate metrics and justified publication', async () => {
  const {progress} = await sources0();
  const documentation = prose0(await text0(DOCUMENTATION));
  const plan = prose0(await text0(PLAN));
  assert.ok(documentation.includes(COORDINATE));
  assert.ok(documentation.includes(prose0(SCOPE)));
  assert.ok(documentation.includes(prose0(NON_CLAIM)));
  assert.ok(documentation.includes('Publication decision: publish'));
  assert.ok(plan.includes('Publication decision: publish'));
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
