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
    "PNP.Concrete.SerializedNormalizer.certificate_bound",
    "656bbbe55cd7255d0872c586a6ed36d5d109df6f392dd3c116ffa4b39822b7d1",
    "PNP.Concrete.SerializedNormalizer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.SerializedNormalizer.decode_output",
    "7f3dafa95c79e7c7022025d22e6cac37279dacc0204185bdfca7b98d161cad52",
    "PNP.Concrete.SerializedNormalizer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.SerializedNormalizer.halts",
    "fd65f0cfea9b32bc1c710a159344869e569f5bd15233efbdd77aaaa700ab7361",
    "PNP.Concrete.SerializedNormalizer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.SerializedNormalizer.malformed_output",
    "3a8ae268d526f5b8135f3f7fed8e416b65552d98396d566907d9558066469437",
    "PNP.Concrete.SerializedNormalizer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.SerializedNormalizer.model_sound",
    "096788fa93b78b5c9c56ff979747ad8507c4f346f9d948916d7b454e876c85b3",
    "PNP.Concrete.SerializedNormalizer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.SerializedNormalizer.output_eq",
    "bbc924774cc8542e63b4d46ace598eb0029f00bc423a10f5830419f2f00de860",
    "PNP.Concrete.SerializedNormalizer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.SerializedNormalizer.output_size",
    "da55366f36cef5ad1bb917c377e7a68b4e9497773c544be2fe2ee74e9697d7fa",
    "PNP.Concrete.SerializedNormalizer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.SerializedNormalizer.reduction_correct",
    "5085e9b0fc9be9894b78e6c84da5c2995d40d7352edeabb12857d999199bc078",
    "PNP.Concrete.SerializedNormalizer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.SerializedNormalizer.reduction_output",
    "50cd8db031d4e01f16259750f15a0b685d520cc1328415f3bc7e33e0ad411777",
    "PNP.Concrete.SerializedNormalizer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.SerializedNormalizer.residual_system_iff",
    "9b037e351a17b5d6fd8b1f3e6bd053bacd98602314cd717778555ceeb2ee064b",
    "PNP.Concrete.SerializedNormalizer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.SerializedNormalizer.satisfiability_iff",
    "936aa81b54397bb6a89b928b28c67babaca208f1334687c25f599c68721f72ce",
    "PNP.Concrete.SerializedNormalizer",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.SerializedNormalizer.sparse_output_size",
    "847c715bb6396f60bf652a09c127becc897d5b25f6280e0228fa6e217c86ac00",
    "PNP.Concrete.SerializedNormalizer",
    [
      "Quot.sound",
      "propext"
    ]
  ]
];
const MILESTONE = {
  "classification": "formalized-foundation-only",
  "id": "complete-serialized-source-normalizer",
  "nonClaim": "This constructs and encodes an equivalent residual problem; a system packet is not an unsatisfiability verdict. Short certificate existence does not provide certificate discovery. The result does not implement the manuscript NormalizeOrGain minimizer, solve all residual systems, establish global route coverage or unconditional ZeroSlack, or prove exact polynomial PCCMin. Its polynomial bounds cover the complete normalizer, not a complete SAT solver. Deterministic CNFSAT membership in P and the eligible root theorem remain absent; P = NP is not proved.",
  "requiredTheorems": [
    "PNP.Concrete.SerializedNormalizer.certificate_bound",
    "PNP.Concrete.SerializedNormalizer.decode_output",
    "PNP.Concrete.SerializedNormalizer.halts",
    "PNP.Concrete.SerializedNormalizer.malformed_output",
    "PNP.Concrete.SerializedNormalizer.model_sound",
    "PNP.Concrete.SerializedNormalizer.output_eq",
    "PNP.Concrete.SerializedNormalizer.output_size",
    "PNP.Concrete.SerializedNormalizer.reduction_correct",
    "PNP.Concrete.SerializedNormalizer.reduction_output",
    "PNP.Concrete.SerializedNormalizer.residual_system_iff",
    "PNP.Concrete.SerializedNormalizer.satisfiability_iff",
    "PNP.Concrete.SerializedNormalizer.sparse_output_size"
  ],
  "scope": "For every source bitstring, a concrete finite-machine refinement computes the complete source-derived serialized normalization packet and halts within a polynomial in the encoded input length. The packet has a polynomial encoded-size bound, strict decode roundtrip and malformed-input convention. Its encoded certificate language is equivalent to CNFSAT on that same input; satisfiable inputs have a certificate of at most 30 times the input length plus 12 bits. Every system packet retains all residual equations, and every model packet yields a satisfying source assignment. The packaged polynomial reduction uses the actual serialized machine output. No construction, completeness or correctness certificate is supplied by a caller.",
  "title": "Complete polynomial source-derived serialized normalizer"
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

test('M281 compiled interface: exact types, modules and axiom closures earn only the reviewed row', async () => {
  const {inventory, map, inventoryBytes, sourceClosure} = await sources0();
  assert.ok(canonical0(inventory).equals(inventoryBytes));
  const names = REVIEWED.map(row => row[0]);
  assert.equal(names.length, 12);
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

test('M281 compiled interface: weakening or supplying a conclusion cannot retain credit', async () => {
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
  // the halting, complete-system and source-language boundaries.
  for (const name of [
    'PNP.Concrete.SerializedNormalizer.halts',
    'PNP.Concrete.SerializedNormalizer.residual_system_iff',
    'PNP.Concrete.SerializedNormalizer.reduction_correct',
  ]) for (const kernelType of alternatives.get(name)) {
    const mutation = {...inventory, milestoneCandidates: inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), sourceClosure);
    assert.equal(result.milestones.find(row => row.id === MILESTONE.id).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
});

test('M281 compiled interface: missing evidence, added authority and widened scope reject', async () => {
  const {inventory, inventoryBytes, map, sourceClosure} = await sources0();
  const name = 'PNP.Concrete.SerializedNormalizer.residual_system_iff';
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
      ? {...row, [field]: 'A residual packet is an unsatisfiability verdict and proves polynomial SAT decision, unconditional ZeroSlack and exact polynomial minimization.'} : row)};
    assert.throws(() => DeriveFormalPublication0(inventory, widened, inventoryBytes, sourceClosure),
      /map drifted from the reviewed specification/u);
  }
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256: {
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]: '0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, inventoryBytes, sourceClosure),
    /map drifted from the reviewed specification/u);
});

const META = {
  "coordinate": "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-10-13-281",
  "doc": "docs/lean_serialized_normalizer.md",
  "plan": "docs/plans/2026-10-13-complete-serialized-normalizer.md",
  "audit": "lean-audit/PNPSerializedNormalizerAxiomAudit.lean",
  "testFiles": [
    "audits/lean-serialized-normalizer0.test.mjs",
    "audits/lean-serialized-normalizer-publication0.test.mjs"
  ],
  "command": "node --test audits/lean-serialized-normalizer0.test.mjs audits/lean-serialized-normalizer-publication0.test.mjs",
  "workflowCommands": "set -euo pipefail\nnode scripts/check-lean-axioms.mjs lean-audit/PNPSerializedNormalizerAxiomAudit.lean\nlake env lean -DwarningAsError=true lean-regression/PNPSerializedNormalizer.lean\n",
  "publicationDecision": "Publication decision: publish after verified core merge. This is one complete all-input construction with literal-machine runtime and encoding guarantees, not another fixed prefix or local sidecar. Batch pending core evidence and preserve the published corrections. The website must distinguish this new general capability from the still-open solver and retain the unchanged risk-weighted estimate.",
  "regressionCommands": [
    "lake env lean -DwarningAsError=true lean-regression/PNPSerializedNormalizer.lean"
  ],
  "statusFields": {
    "leanSerializedNormalizerFormalized": true,
    "leanSerializedNormalizerAxiomAuditPassed": true,
    "leanSerializedNormalizerAuditedDeclarationCount": 12,
    "leanSerializedNormalizerExactMachineOutputTheorem": "PNP.Concrete.SerializedNormalizer.output_eq",
    "leanSerializedNormalizerPolynomialHaltingTheorem": "PNP.Concrete.SerializedNormalizer.halts",
    "leanSerializedNormalizerOutputSizeTheorem": "PNP.Concrete.SerializedNormalizer.output_size",
    "leanSerializedNormalizerSparseEncodedSizeTheorem": "PNP.Concrete.SerializedNormalizer.sparse_output_size",
    "leanSerializedNormalizerStrictPacketRoundtripTheorem": "PNP.Concrete.SerializedNormalizer.decode_output",
    "leanSerializedNormalizerSatisfiabilityTheorem": "PNP.Concrete.SerializedNormalizer.satisfiability_iff",
    "leanSerializedNormalizerShortCertificateTheorem": "PNP.Concrete.SerializedNormalizer.certificate_bound",
    "leanSerializedNormalizerMalformedInputsTheorem": "PNP.Concrete.SerializedNormalizer.malformed_output",
    "leanSerializedNormalizerCompleteSystemTheorem": "PNP.Concrete.SerializedNormalizer.residual_system_iff",
    "leanSerializedNormalizerSourceModelTheorem": "PNP.Concrete.SerializedNormalizer.model_sound",
    "leanSerializedNormalizerReductionMachineCorrespondenceTheorem": "PNP.Concrete.SerializedNormalizer.reduction_output",
    "leanSerializedNormalizerConcreteReductionTheorem": "PNP.Concrete.SerializedNormalizer.reduction_correct",
    "leanSerializedNormalizerAllSourceBitstringsCovered": true,
    "leanSerializedNormalizerDataDerivedFromSource": true,
    "leanSerializedNormalizerCompletePacketSerialized": true,
    "leanSerializedNormalizerLiteralFiniteMachineRefinement": true,
    "leanSerializedNormalizerEncodedInputPolynomialRuntimeProved": true,
    "leanSerializedNormalizerEncodedOutputBoundProved": true,
    "leanSerializedNormalizerShortCertificateExistenceProved": true,
    "leanSerializedNormalizerCertificateDiscoveryAlgorithmProved": false,
    "leanSerializedNormalizerCallerSuppliedConstructionOrCorrectnessRequired": false,
    "leanSerializedNormalizerGeneralResidualSolverProved": false,
    "leanSerializedNormalizerManuscriptResidualMinimizerProved": false,
    "leanSerializedNormalizerUnconditionalZeroSlackProved": false,
    "leanSerializedNormalizerExactPolynomialPCCMinProved": false,
    "leanSerializedNormalizerConcreteCNFSATInPProved": false,
    "leanSerializedNormalizerRuntimeExecutionIsProofAuthority": false,
    "leanSerializedNormalizerScope": "all-source-bitstrings-complete-derived-serialized-packet-literal-machine-encoded-polynomial-runtime-output-bound-exact-sat-certificate-language-no-certificate-discovery-residual-solver-manuscript-minimization-or-p-equals-np"
  }
};
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();
async function release0() {
  const [statusText, progressText] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('status/PROOF_PROGRESS.json'),
  ]);
  return {status: JSON.parse(statusText), progress: JSON.parse(progressText)};
}

test('M281 release preflight: package, exact workflow and status commands share one interface', async () => {
  const [pkg, surface, verifier, workflow, statusSource, statusText] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'), text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'), text0('pcc-formal-reconstruction-status0.mjs'),
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  ]);
  assert.equal(JSON.parse(pkg).scripts['audit:m281'], META.command);
  assert.ok(surface.includes("'audit:m281': '" + META.command + "'"));
  for (const file of META.testFiles) assert.ok(verifier.includes("'" + file + "'"), file);
  assert.ok(workflow.includes('run: npm run audit:m281'));
  const steps = workflow.split(/^      - name:/mu).filter(step =>
    step.includes('node scripts/check-lean-axioms.mjs ' + META.audit));
  assert.equal(steps.length, 1);
  const block = steps[0].split('        run: |\n')[1];
  assert.ok(block);
  assert.equal(block.trimEnd().split('\n').map(line => line.slice(10)).join('\n') + '\n', META.workflowCommands);
  const status = JSON.parse(statusText);
  for (const command of [
    'npm run audit:m281', 'node scripts/check-lean-axioms.mjs ' + META.audit,
    ...META.regressionCommands,
  ]) assert.ok(status.verificationCommands.includes(command), command);
  for (const field of Object.keys(META.statusFields))
    assert.equal(statusSource.split(field + ':').length - 1, 2, field);
});

test('M281 release: status pins the exact bounded claims and rejects every changed field', async () => {
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

test('M281 release: complete serialized normalization earns no unconditional checkpoint', async () => {
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

test('M281 release: every current summary and FAQ uses the canonical independent metrics', async () => {
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
      assert.ok(boundary?.includes('M281'));
      assert.ok(boundary.includes('global route coverage'));
    }
    if (['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
      'docs/proof_pipeline.md', 'docs/audit_questions.md'].includes(file)) {
      const region = text.split('<!-- M281-CURRENT-SUMMARY:BEGIN -->')[1]?.split('<!-- M281-CURRENT-SUMMARY:END -->')[0];
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
