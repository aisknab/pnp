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
    "PNP.Concrete.ResidualReducer.decision_false_sound",
    "7659aa89dcd884cfd824bf2068bf0457f81331e8c03eda0942448fde04a63b5b",
    "PNP.Concrete.ResidualReducer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReducer.decision_packet",
    "bd6c2ff99b86af77f392a8664964622be25c76f1dbc3e1f3dbd691a939ba1c62",
    "PNP.Concrete.ResidualReducer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReducer.decision_true_sound",
    "063c912d84958f6e49e7dad9c9c8db6a91135a26bc341908fa1ec3f578b556a5",
    "PNP.Concrete.ResidualReducer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReducer.decision_unknown",
    "b715ecc4a0aabab250a2bd5c4742fbc4678d625d4abbfc81aaca9861605c8cdb",
    "PNP.Concrete.ResidualReducer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReducer.dimension_accounting",
    "80b578136995d510d349ab0fbc21e90108d2c3c7e374bb3a97db88e51d761e9d",
    "PNP.Concrete.ResidualReducer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReducer.model_preservation",
    "3fb80e01e0a01c66c4230d3650fc5153ef9b1648c68ceab5b5753e78dcfab7ec",
    "PNP.Concrete.ResidualReducer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReducer.parameter_roundtrip",
    "038ddd83c7cabd1af77ffbbbdbf4eb564f52a16c9a2dc47ed5c478234c5b10db",
    "PNP.Concrete.ResidualReducer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReducer.recover_certificate",
    "644da333dc86f56baab0e379a0addbdba57d7a48b52a7650ba813720fd78872b",
    "PNP.Concrete.ResidualReducer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReducer.residual_source_iff",
    "8c126421d3ceaf637cb0581d8fb3a6547f8e3cb190a4a19b60bc3b4772efecb0",
    "PNP.Concrete.ResidualReducer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReducer.result_rows",
    "bc62e431ee82348ea56998d66e35ba11dc58aa8ba04b4d51377cb9a4f3777f81",
    "PNP.Concrete.ResidualReducer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReducer.source_family_iff",
    "258e2dd888772eb844d2a8a589b48d91e3890ca9ce11d4e581312c5c6c4d2139",
    "PNP.Concrete.ResidualReducer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReducer.source_family_rows",
    "8557f69a67b37eee88c41368dd399d3bd4005c07627de2b7adee007ea331fd9c",
    "PNP.Concrete.ResidualReducer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReducer.source_model_roundtrip",
    "4cb8f56cc8b6c1b7fc7465a82da6c3c87722e35cda3572f252f72152dd6d65b5",
    "PNP.Concrete.ResidualReducer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReducer.step_bound",
    "901e5420db235aa2c64892dd1748387c48cd4579adf5f8ac86aca4b8a77a4775",
    "PNP.Concrete.ResidualReducer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReducer.terminal",
    "62c8f8b85053c98535224719e82641fcd018fd23f59bee77ae5676dd94c9328b",
    "PNP.Concrete.ResidualReducer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReducer.trace_linked",
    "2da8089f4b90238d8f535053f1bbf75f371eb358643e22a85d740cf735956797",
    "PNP.Concrete.ResidualReducer",
    [
      "Quot.sound",
      "propext"
    ]
  ]
];
const MILESTONE = {
  "classification": "formalized-foundation-only",
  "id": "source-bound-partial-residual-reducer",
  "nonClaim": "Stopping exhausts the computed finite affine/line/plane selector menu, not the whole class of possible contractions. An unknown core can be satisfiable or unsatisfiable; useful reduction on every instance and all-input decision are not proved. The chain-length bound is not a polynomial bound on total encoded construction, storage or runtime. This is not the completed manuscript residual-band minimizer, unconditional SaturatePositive, BCELReady or ZeroSlack, exact polynomial PCCMin, deterministic CNFSAT membership in P, or the eligible root theorem. P = NP is not proved.",
  "requiredTheorems": [
    "PNP.Concrete.ResidualReducer.decision_false_sound",
    "PNP.Concrete.ResidualReducer.decision_packet",
    "PNP.Concrete.ResidualReducer.decision_true_sound",
    "PNP.Concrete.ResidualReducer.decision_unknown",
    "PNP.Concrete.ResidualReducer.dimension_accounting",
    "PNP.Concrete.ResidualReducer.model_preservation",
    "PNP.Concrete.ResidualReducer.parameter_roundtrip",
    "PNP.Concrete.ResidualReducer.recover_certificate",
    "PNP.Concrete.ResidualReducer.residual_source_iff",
    "PNP.Concrete.ResidualReducer.result_rows",
    "PNP.Concrete.ResidualReducer.source_family_iff",
    "PNP.Concrete.ResidualReducer.source_family_rows",
    "PNP.Concrete.ResidualReducer.source_model_roundtrip",
    "PNP.Concrete.ResidualReducer.step_bound",
    "PNP.Concrete.ResidualReducer.terminal",
    "PNP.Concrete.ResidualReducer.trace_linked"
  ],
  "scope": "For every native sparse residual system, a computed translation retains all positive, linear and product constraints, including duplicate-term parity and coordinate order. A dimension-decreasing source-derived chain preserves models, links every step to its preceding residual, preserves the row count, and supplies inverse parameter and satisfying-source maps. For every original bitstring whose actual serialized normalizer output decodes to a system, the remaining core is satisfiable exactly when that original input is in CNFSAT; a remaining model reconstructs a correctly sized encoded certificate accepted by the actual output checker. The original-input partial verdict is sound for both true and false answers and returns unknown when positive dimension remains. At most 30 times the source bitstring length plus 12 reductions occur; this bounds steps, not execution work. No chosen contraction, family, route coverage certificate or correctness premise is supplied by a caller.",
  "title": "Source-bound partial residual reduction and certificate recovery"
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

test('M282 compiled interface: exact types, modules and axiom closures earn only the reviewed row', async () => {
  const {inventory, map, inventoryBytes, sourceClosure} = await sources0();
  assert.ok(canonical0(inventory).equals(inventoryBytes));
  const names = REVIEWED.map(row => row[0]);
  assert.equal(names.length, 16);
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

test('M282 compiled interface: weakening or supplying a conclusion cannot retain credit', async () => {
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
  // the step-bound, complete-system and original-input verdict boundaries.
  for (const name of [
    'PNP.Concrete.ResidualReducer.step_bound',
    'PNP.Concrete.ResidualReducer.residual_source_iff',
    'PNP.Concrete.ResidualReducer.decision_true_sound',
  ]) for (const kernelType of alternatives.get(name)) {
    const mutation = {...inventory, milestoneCandidates: inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), sourceClosure);
    assert.equal(result.milestones.find(row => row.id === MILESTONE.id).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
});

test('M282 compiled interface: missing evidence, added authority and widened scope reject', async () => {
  const {inventory, inventoryBytes, map, sourceClosure} = await sources0();
  const name = 'PNP.Concrete.ResidualReducer.residual_source_iff';
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
      ? {...row, [field]: 'An unknown residual core is an unsatisfiability verdict and proves total polynomial SAT decision, unconditional ZeroSlack and exact polynomial minimization.'} : row)};
    assert.throws(() => DeriveFormalPublication0(inventory, widened, inventoryBytes, sourceClosure),
      /map drifted from the reviewed specification/u);
  }
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256: {
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]: '0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, inventoryBytes, sourceClosure),
    /map drifted from the reviewed specification/u);
});

const META = {
  "coordinate": "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-10-15-282",
  "doc": "docs/lean_residual_reducer.md",
  "plan": "docs/plans/2026-10-15-source-bound-partial-residual-reducer.md",
  "audit": "lean-audit/PNPResidualReducerAxiomAudit.lean",
  "testFiles": [
    "audits/lean-residual-reducer0.test.mjs",
    "audits/lean-residual-reducer-publication0.test.mjs"
  ],
  "command": "node --test audits/lean-residual-reducer0.test.mjs audits/lean-residual-reducer-publication0.test.mjs",
  "workflowCommands": "set -euo pipefail\nnpm run audit:m282\nnode scripts/check-lean-axioms.mjs lean-audit/PNPResidualReducerAxiomAudit.lean\nlake env lean -DwarningAsError=true lean-regression/PNPResidualReducer.lean\n",
  "publicationDecision": "Publication decision: publish after verified core merge. The complete source-bound partial reduction and certificate recovery form a substantial general capability beyond a local lemma or fixed instance. Publish one batch from the exact core merge, preserve prior corrections and show unknown outcomes and unresolved solver/runtime obligations explicitly. This does not change the risk-weighted proof estimate.",
  "regressionCommands": [
    "lake env lean -DwarningAsError=true lean-regression/PNPResidualReducer.lean"
  ],
  "statusFields": {
    "leanSourceBoundResidualReducerFormalized": true,
    "leanSourceBoundResidualReducerAxiomAuditPassed": true,
    "leanSourceBoundResidualReducerAuditedDeclarationCount": 16,
    "leanSourceBoundResidualReducerCompleteSystemTheorem": "PNP.Concrete.ResidualReducer.source_family_iff",
    "leanSourceBoundResidualReducerSourceRowCountTheorem": "PNP.Concrete.ResidualReducer.source_family_rows",
    "leanSourceBoundResidualReducerResidualRowCountTheorem": "PNP.Concrete.ResidualReducer.result_rows",
    "leanSourceBoundResidualReducerModelPreservationTheorem": "PNP.Concrete.ResidualReducer.model_preservation",
    "leanSourceBoundResidualReducerParameterInverseTheorem": "PNP.Concrete.ResidualReducer.parameter_roundtrip",
    "leanSourceBoundResidualReducerSourceModelInverseTheorem": "PNP.Concrete.ResidualReducer.source_model_roundtrip",
    "leanSourceBoundResidualReducerLinkedTraceTheorem": "PNP.Concrete.ResidualReducer.trace_linked",
    "leanSourceBoundResidualReducerDimensionAccountingTheorem": "PNP.Concrete.ResidualReducer.dimension_accounting",
    "leanSourceBoundResidualReducerSelectorStoppingTheorem": "PNP.Concrete.ResidualReducer.terminal",
    "leanSourceBoundResidualReducerSourceSatisfiabilityTheorem": "PNP.Concrete.ResidualReducer.residual_source_iff",
    "leanSourceBoundResidualReducerEncodedCertificateRecoveryTheorem": "PNP.Concrete.ResidualReducer.recover_certificate",
    "leanSourceBoundResidualReducerSourceStepBoundTheorem": "PNP.Concrete.ResidualReducer.step_bound",
    "leanSourceBoundResidualReducerActualPacketDecisionTheorem": "PNP.Concrete.ResidualReducer.decision_packet",
    "leanSourceBoundResidualReducerTrueSoundnessTheorem": "PNP.Concrete.ResidualReducer.decision_true_sound",
    "leanSourceBoundResidualReducerFalseSoundnessTheorem": "PNP.Concrete.ResidualReducer.decision_false_sound",
    "leanSourceBoundResidualReducerUnknownTheorem": "PNP.Concrete.ResidualReducer.decision_unknown",
    "leanSourceBoundResidualReducerAllSourceBitstringsCovered": true,
    "leanSourceBoundResidualReducerCompleteNativeConstraintsRetained": true,
    "leanSourceBoundResidualReducerDataDerivedFromSource": true,
    "leanSourceBoundResidualReducerLinkedRepeatedReductionProved": true,
    "leanSourceBoundResidualReducerSatisfyingModelCertificateRecoveryProved": true,
    "leanSourceBoundResidualReducerSourceEncodedStepCountBoundProved": true,
    "leanSourceBoundResidualReducerCallerSuppliedConstructionOrCorrectnessRequired": false,
    "leanSourceBoundResidualReducerPositiveDimensionRemainsUnknown": true,
    "leanSourceBoundResidualReducerWholeContractionClassCompletenessProved": false,
    "leanSourceBoundResidualReducerAllInputResidualDecisionProved": false,
    "leanSourceBoundResidualReducerGeneralPolynomialRuntimeProved": false,
    "leanSourceBoundResidualReducerGeneralEncodedSizeBoundProved": false,
    "leanSourceBoundResidualReducerManuscriptResidualMinimizerProved": false,
    "leanSourceBoundResidualReducerGlobalRouteCoverageProved": false,
    "leanSourceBoundResidualReducerUnconditionalZeroSlackProved": false,
    "leanSourceBoundResidualReducerExactPolynomialPCCMinProved": false,
    "leanSourceBoundResidualReducerConcreteCNFSATInPProved": false,
    "leanSourceBoundResidualReducerRuntimeExecutionIsProofAuthority": false,
    "leanSourceBoundResidualReducerScope": "all-source-bitstrings-complete-native-constraints-source-derived-model-preserving-chain-linked-history-certificate-recovery-sound-partial-verdict-explicit-unknown-source-step-count-only-no-complete-residual-decision-whole-class-coverage-or-polynomial-runtime"
  }
};
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();
async function release0() {
  const [statusText, progressText] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('status/PROOF_PROGRESS.json'),
  ]);
  return {status: JSON.parse(statusText), progress: JSON.parse(progressText)};
}

test('M282 release preflight: package, exact workflow and status commands share one interface', async () => {
  const [pkg, surface, verifier, workflow, statusSource, statusText] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'), text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'), text0('pcc-formal-reconstruction-status0.mjs'),
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  ]);
  assert.equal(JSON.parse(pkg).scripts['audit:m282'], META.command);
  assert.ok(surface.includes("'audit:m282': '" + META.command + "'"));
  for (const file of META.testFiles) assert.ok(verifier.includes("'" + file + "'"), file);
  assert.match(workflow, /^          npm run audit:m282$/mu);
  const steps = workflow.split(/^      - name:/mu).filter(step =>
    step.includes('node scripts/check-lean-axioms.mjs ' + META.audit));
  assert.equal(steps.length, 1);
  const block = steps[0].split('        run: |\n')[1];
  assert.ok(block);
  assert.equal(block.trimEnd().split('\n').map(line => line.slice(10)).join('\n') + '\n', META.workflowCommands);
  const status = JSON.parse(statusText);
  for (const command of [
    'npm run audit:m282', 'node scripts/check-lean-axioms.mjs ' + META.audit,
    ...META.regressionCommands,
  ]) assert.ok(status.verificationCommands.includes(command), command);
  for (const field of Object.keys(META.statusFields))
    assert.equal(statusSource.split(field + ':').length - 1, 2, field);
});

test('M282 release: status pins the exact bounded claims and rejects every changed field', async () => {
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

test('M282 release: partial residual reduction earns no unconditional checkpoint', async () => {
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

test('M282 release: every current summary and FAQ uses the canonical independent metrics', async () => {
  const {progress} = await release0();
  const doc = prose0(await text0(META.doc)), plan = prose0(await text0(META.plan));
  assert.ok(doc.includes(META.coordinate));
  assert.ok(doc.includes(prose0(MILESTONE.scope)));
  assert.ok(doc.includes(prose0(MILESTONE.nonClaim)));
  assert.ok(doc.includes(prose0(META.publicationDecision)));
  assert.ok(plan.includes('Publication decision: publish after verified core merge'));
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
      assert.ok(boundary?.includes('M282'));
      assert.ok(boundary.includes('global route coverage'));
    }
    if (['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
      'docs/proof_pipeline.md', 'docs/audit_questions.md'].includes(file)) {
      const region = text.split('<!-- M282-CURRENT-SUMMARY:BEGIN -->')[1]?.split('<!-- M282-CURRENT-SUMMARY:END -->')[0];
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
