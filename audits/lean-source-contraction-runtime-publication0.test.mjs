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

// Frozen only after the explicit-root build and compiled type/axiom review.
// Never regenerate these expected fingerprints inside a running test.
const REVIEWED = [
  [
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.recover_certificate",
    "a320c05a80a4a0951b93009b95e4179ea06e6bd7c51c9cabdda58637a104edff",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.recover_certificate_runtime",
    "432a767ef7b68c01ec9e3a3fd8114cbbfdc1a59b5a3d92c0dcf6d683d838184e",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.recovery_output",
    "7248717e1a262de13d38d8e4525a5d780165c6b48f179b4a1ec126e432866c8c",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.replay_halts",
    "b89c2d653dd54aa82a501f7d5726fd4126e1f463c88b55705dd1daddeec398aa",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.replay_output",
    "9c8849c7e1383e69c088202e27e046276f1493e2adb710b43c203ec0d41e2778",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.replay_output_size",
    "791644b399d0d0bc3922e56ad1a0399a1fa93f11f3829bb24b2349c59a066830",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_halts",
    "e7bd6b0d619294076503501f19431027cb065e69038d5ccc198de5cc5fb6e917",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_output",
    "d8ed882a97b60325d2b48e78eb82fd73e22b7d5253153784f6b93b9a9b202d1c",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_output_size",
    "6637fc136f9c081fba0212f73ff0e77767365261d9734fdedcc4d429d19616ed",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_satisfiability",
    "2a60146e38b983c759bdd0e4c0cb79086e4486edb7e10aaf2f0090898f1c754e",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_system_output",
    "1cf01fea09426013082e253bd429b7e06e2145e4ea1fa92741c3ec0bf347de7a",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.unresolved_remains_unknown",
    "f8feb147b0cd20db911718ab0519586fae037b6d608c7127869304a49101eb5b",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReduction.SourceReplayEndpointBudget.native_project_run",
    "b1c471fb2a905880ac629544415c5813ca3c7241e057a18fe9071712924059ab",
    "PNP.Concrete.ResidualReduction.SourceReplayEndpointBudget",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.Concrete.ResidualReduction.SourceReplayEndpointGenerated.project_recover_model",
    "4d5e8455bd030e23244cba096222fffe33af60c033049ddd4e44923e0b5c411c",
    "PNP.Concrete.ResidualReduction.SourceReplayEndpointGenerated",
    [
      "Quot.sound",
      "propext"
    ]
  ]
];
const MILESTONE = {
  "classification": "formalized-foundation-only",
  "id": "source-contraction-phase-polynomial-runtime-and-witness-replay",
  "nonClaim": "A genuine model of the remaining core is still required for certificate recovery; this work does not find that model. A positive-dimensional stopped core remains unknown and may be satisfiable or unsatisfiable. The replay runtime bound starts from the canonical encoded request; a further finite-machine request assembler is not claimed. These are polynomial source-construction and witness-replay endpoints, not a complete residual decision procedure, manuscript residual-band minimizer, unconditional SaturatePositive, BCELReady or ZeroSlack, exact polynomial PCCMin, concrete CNFSAT membership in P, or eligible root theorem. P = NP is not proved.",
  "requiredTheorems": [
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.recover_certificate",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.recover_certificate_runtime",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.recovery_output",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.replay_halts",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.replay_output",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.replay_output_size",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_halts",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_output",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_output_size",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_satisfiability",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_system_output",
    "PNP.Concrete.ResidualReduction.SourceReductionRuntime.unresolved_remains_unknown",
    "PNP.Concrete.ResidualReduction.SourceReplayEndpointBudget.native_project_run",
    "PNP.Concrete.ResidualReduction.SourceReplayEndpointGenerated.project_recover_model"
  ],
  "scope": "For every raw input bitstring, the closed source-construction finite machine halts within its encoded-input polynomial bound and emits exactly the canonical source-derived contraction packet, with polynomial output size. On a decoded source system, the actual remaining core is satisfiable exactly when the original input is in CNFSAT. A separate closed finite-machine replay endpoint returns the exact canonical optional answer on every raw request. For the history generated from the actual source system, it lifts any genuine remaining-core model to a certificate accepted by the original source checker, with physical replay time bounded polynomially in the original input length. Projection and recovery preserve original models; source-generated history is not a caller-supplied correctness certificate.",
  "title": "Polynomial source-contraction phase and complete witness replay"
};
const META = {
  "coordinate": "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-10-18-284",
  "doc": "docs/lean_source_contraction_runtime.md",
  "plan": "docs/plans/2026-10-18-source-contraction-runtime.md",
  "audit": "lean-audit/PNPSourceContractionRuntimeAxiomAudit.lean",
  "testFiles": [
    "audits/lean-source-contraction-runtime0.test.mjs",
    "audits/lean-source-contraction-runtime-publication0.test.mjs"
  ],
  "command": "node --test audits/lean-source-contraction-runtime0.test.mjs audits/lean-source-contraction-runtime-publication0.test.mjs",
  "workflowCommands": "set -euo pipefail\nnpm run audit:m284\nnode scripts/check-lean-axioms.mjs lean-audit/PNPSourceContractionRuntimeAxiomAudit.lean\n",
  "publicationDecision": "Publication decision: publish one major PNPLabs batch after the exact core merge passes verification. The source-construction and witness-replay endpoints now have complete finite-machine polynomial runtime contracts, a substantial general capability beyond a count of local milestones. Include pending earned M283 evidence in the same source-pinned site update. No fixed load-bearing checkpoint changes state, and no global gate closes.",
  "statusFields": {
    "leanSourceContractionPhaseRuntimeFormalized": true,
    "leanSourceContractionPhaseRuntimeAxiomAuditPassed": true,
    "leanSourceContractionPhaseRuntimeAuditedDeclarationCount": 14,
    "leanSourceContractionPhaseRuntimeSourceOutputTheorem": "PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_output",
    "leanSourceContractionPhaseRuntimeSourceHaltingTheorem": "PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_halts",
    "leanSourceContractionPhaseRuntimeSourceSizeTheorem": "PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_output_size",
    "leanSourceContractionPhaseRuntimeSatisfiabilityTheorem": "PNP.Concrete.ResidualReduction.SourceReductionRuntime.source_satisfiability",
    "leanSourceContractionPhaseRuntimeReplayOutputTheorem": "PNP.Concrete.ResidualReduction.SourceReductionRuntime.replay_output",
    "leanSourceContractionPhaseRuntimeCertificateTheorem": "PNP.Concrete.ResidualReduction.SourceReductionRuntime.recover_certificate",
    "leanSourceContractionPhaseRuntimeOriginalInputBoundTheorem": "PNP.Concrete.ResidualReduction.SourceReductionRuntime.recover_certificate_runtime",
    "leanSourceContractionPhaseRuntimeProjectBoundTheorem": "PNP.Concrete.ResidualReduction.SourceReplayEndpointBudget.native_project_run",
    "leanSourceContractionPhaseRuntimeModelRoundtripTheorem": "PNP.Concrete.ResidualReduction.SourceReplayEndpointGenerated.project_recover_model",
    "leanSourceContractionPhaseRuntimeUnknownBoundaryTheorem": "PNP.Concrete.ResidualReduction.SourceReductionRuntime.unresolved_remains_unknown",
    "leanSourceContractionPhaseRuntimeAllRawInputsCovered": true,
    "leanSourceContractionPhaseRuntimeActualSourceHistoryDerived": true,
    "leanSourceContractionPhaseRuntimePhysicalFiniteMachinesProved": true,
    "leanSourceContractionPhaseRuntimeOriginalEncodedInputBoundsProved": true,
    "leanSourceContractionPhaseRuntimeTerminalModelStillRequired": true,
    "leanSourceContractionPhaseRuntimeAdditionalRequestAssemblerProved": false,
    "leanSourceContractionPhaseRuntimeAllInputResidualDecisionProved": false,
    "leanSourceContractionPhaseRuntimeUnconditionalZeroSlackProved": false,
    "leanSourceContractionPhaseRuntimeExactPolynomialPCCMinProved": false,
    "leanSourceContractionPhaseRuntimeScope": "all-bitstring-closed-source-construction-polynomial-physical-time-and-output-source-derived-history-exact-closed-replay-original-input-runtime-source-checker-accepted-recovered-certificate-terminal-model-still-required-unknown-preserved-no-complete-solver"
  },
  "rootContractModule": "PNP.Concrete.ResidualReduction.SourceReductionRuntimeRegression",
  "rootContractSource": "lean/PNP/Concrete/ResidualReduction/SourceReductionRuntimeRegression.lean"
};
const root0 = fileURLToPath(new URL('../', import.meta.url));
const text0 = file => readFile(new URL('../' + file, import.meta.url), 'utf8');
const canonical0 = value => Buffer.from(stableStringify0(value) + '\n');
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();
let loaded0;
async function sources0() {
  loaded0 ??= Promise.all([
    text0('status/LEAN_THEOREM_INVENTORY.json'), text0('publication/FORMAL_PUBLICATION_MAP.json'),
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('status/PROOF_PROGRESS.json'),
  ]).then(async ([inventoryText, mapText, statusText, progressText]) => {
    const inventory = JSON.parse(inventoryText);
    return {inventory, inventoryBytes: Buffer.from(inventoryText), map: JSON.parse(mapText),
      status: JSON.parse(statusText), progress: JSON.parse(progressText),
      sourceClosure: await ComputeLeanSourceClosureSha2560(root0, inventory)};
  });
  return loaded0;
}

test('M284 runtime: exact compiled endpoint types and axioms earn one reviewed row', async () => {
  const {inventory, inventoryBytes, map, sourceClosure} = await sources0();
  assert.ok(canonical0(inventory).equals(inventoryBytes));
  const names = REVIEWED.map(row => row[0]);
  assert.equal(names.length, 14);
  assert.equal(new Set(names).size, 14);
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

test('M284 runtime: weakened conclusions or supplied correctness cannot retain credit', async () => {
  const {inventory, map, sourceClosure} = await sources0();
  const alternatives = new Map();
  for (const [name, hash] of REVIEWED) {
    const current = inventory.milestoneCandidates.find(row => row.name === name).kernelType;
    const changed = [
      'Lean.Expr.const ' + String.fromCharCode(96) + 'True []',
      'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + current + ') (' + current + ') (Lean.BinderInfo.default)',
    ];
    for (const type of changed)
      assert.notEqual(MilestoneTheoremKernelTypeSha2560(name, type), hash, name);
    alternatives.set(name, changed);
  }
  for (const suffix of ['source_halts', 'recover_certificate_runtime', 'unresolved_remains_unknown']) {
    const name = 'PNP.Concrete.ResidualReduction.SourceReductionRuntime.' + suffix;
    for (const kernelType of alternatives.get(name)) {
      const mutation = {...inventory, milestoneCandidates: inventory.milestoneCandidates.map(row =>
        row.name === name ? {...row, kernelType} : row)};
      const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), sourceClosure);
      assert.equal(result.milestones.find(row => row.id === MILESTONE.id).earned, false, name);
      assert.equal(result.gate.passed, false);
    }
  }
});

test('M284 runtime: missing evidence, added axioms and complete-solver claims reject', async () => {
  const {inventory, inventoryBytes, map, sourceClosure} = await sources0();
  const name = 'PNP.Concrete.ResidualReduction.SourceReductionRuntime.recover_certificate_runtime';
  const addAuthority = row => row.name === name
    ? {...row, axioms: ['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const mutation = {...inventory, declarations: inventory.declarations.map(addAuthority),
    milestoneCandidates: inventory.milestoneCandidates.map(addAuthority)};
  const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), sourceClosure);
  assert.equal(result.milestones.find(row => row.id === MILESTONE.id).earned, false);
  assert.equal(result.gate.passed, false);
  const missing = {...inventory,
    milestoneCandidates: inventory.milestoneCandidates.filter(row => row.name !== name)};
  assert.throws(() => DeriveFormalPublication0(missing, map, canonical0(missing), sourceClosure),
    /reviewed milestone theorem candidate inventory mismatch/u);
  for (const field of ['scope', 'nonClaim']) {
    const widened = {...map, milestones: map.milestones.map(row => row.id === MILESTONE.id
      ? {...row, [field]: 'The complete polynomial solver discovers every terminal model and decides every input.'} : row)};
    assert.throws(() => DeriveFormalPublication0(inventory, widened, inventoryBytes, sourceClosure),
      /map drifted from the reviewed specification/u);
  }
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256: {
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]: '0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, inventoryBytes, sourceClosure),
    /map drifted from the reviewed specification/u);
});

test('M284 release: scripts, root contracts, verifier and exact workflow are synchronized', async () => {
  const [pkg, surface, verifier, workflow, statusSource, root] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'), text0('.github/workflows/lean-bridge.yml'),
    text0('pcc-formal-reconstruction-status0.mjs'), text0('lean/PNP.lean'),
  ]);
  assert.equal(JSON.parse(pkg).scripts['audit:m284'], META.command);
  assert.ok(surface.includes("'audit:m284': '" + META.command + "'"));
  for (const file of META.testFiles) assert.ok(verifier.includes("'" + file + "'"), file);
  assert.equal(root.split('\n').filter(line => line === 'import ' + META.rootContractModule).length, 1);
  const steps = workflow.split(/^      - name:/mu).filter(step =>
    step.includes('node scripts/check-lean-axioms.mjs ' + META.audit));
  assert.equal(steps.length, 1);
  const block = steps[0].split('        run: |\n')[1];
  assert.ok(block);
  assert.equal(block.trimEnd().split('\n').map(line => line.slice(10)).join('\n') + '\n',
    META.workflowCommands);
  const {status} = await sources0();
  for (const command of ['npm run audit:m284', 'node scripts/check-lean-axioms.mjs ' + META.audit])
    assert.ok(status.verificationCommands.includes(command), command);
  for (const field of Object.keys(META.statusFields))
    assert.equal(statusSource.split(field + ':').length - 1, 2, field);
});

test('M284 release: endpoint runtime and retained terminal-model boundary are fail closed', async () => {
  const {status} = await sources0();
  for (const [field, value] of Object.entries(META.statusFields)) {
    assert.deepEqual(status[field], value, field);
    const mutation = {...status, [field]: typeof value === 'boolean' ? !value
      : typeof value === 'number' ? value + 1 : value + ':unreviewed'};
    const result = await CheckFormalReconstructionStatus0({
      writeOutput: false, statusOverride: mutation, siteOverride: mutation});
    assert.equal(result.tag, 'reject', field);
    assert.equal(result.coord, 'FormalReconstructionStatus.Field', field);
    assert.deepEqual(result.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
  }
});

test('M284 release: endpoint bounds do not earn complete-algorithm checkpoint credit', async () => {
  const {status, progress, inventory} = await sources0();
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
  assert.deepEqual(progress.rootTheorem,
    {name: 'PNP.Main.p_eq_np', present: false, built: false, axiomAuditPassed: false});
  const inflated = structuredClone(progress);
  inflated.proofCompletion.pointsEarned += 1;
  inflated.proofCompletion.percent += 1;
  assert.throws(() => validateProofProgress0(inflated, status, inventory),
    error => error.code === 'ProofCompletion.StoredEarned');
});

test('M284 release: current summaries separate phase runtime from the unresolved solver', async () => {
  const {progress} = await sources0();
  for (const file of [META.doc, META.plan]) {
    const doc = prose0(await text0(file));
    assert.ok(doc.includes(META.coordinate), file);
    assert.ok(doc.includes(prose0(MILESTONE.scope)), file);
    assert.ok(doc.includes(prose0(MILESTONE.nonClaim)), file);
    assert.ok(doc.includes(prose0(META.publicationDecision)), file);
  }
  if (progress.asOfCoordinate !== META.coordinate) return;
  const p = progress.proofCompletion, a = progress.formalArtefactCoverage;
  const metrics = [
    'Formal artefact coverage: ' + a.earnedRows + ' of ' + a.totalRows + ' current scoped publication rows earned.',
    'Risk-weighted proof completion estimate: ' + p.percent + '%.',
    'Uncertainty range: ' + p.uncertaintyLowPercent + '% to ' + p.uncertaintyHighPercent + '%.',
    'Global gates closed: ' + progress.globalGates.filter(gate => gate.status === 'closed').length + ' of 5.',
  ];
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md', META.doc, META.plan]) {
    const text = await text0(file);
    for (const metric of metrics) assert.ok(prose0(text).includes(metric), file + ': ' + metric);
    if (['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
      'docs/proof_pipeline.md', 'docs/audit_questions.md'].includes(file)) {
      const region = text.split('<!-- M284-CURRENT-SUMMARY:BEGIN -->')[1]?.split('<!-- M284-CURRENT-SUMMARY:END -->')[0];
      assert.ok(region, file);
      for (const metric of metrics) assert.ok(prose0(region).includes(metric), file + ': current region');
      assert.ok(prose0(region).includes('remaining core still requires a solver'), file);
      assert.ok(prose0(region).includes('global route coverage'), file);
      assert.doesNotMatch(region, /\d+[ -]pages?|PDF[^\n]*page count/iu);
    }
    if (file === 'README.md') {
      const row = text.split('\n').find(line => line.startsWith('| **How is progress measured?** |'));
      assert.ok(row);
      for (const metric of metrics) assert.ok(prose0(row).includes(metric), 'FAQ: ' + metric);
      const boundary = text.split('\n').find(line => line.startsWith('| **What is the current verification status?** |'));
      assert.ok(boundary?.includes('M284'));
      assert.ok(boundary.includes('remaining core still requires a solver'));
    }
    if (file === 'docs/proof_progress.md') {
      const intro = prose0(text.split('## Risk-weighted proof completion estimate')[0]);
      for (const metric of metrics) assert.ok(intro.includes(metric), file + ': current introduction');
      assert.ok(intro.includes(META.coordinate));
    }
  }
  const cover = prose0((await text0('canonical_proof_report.tex')).split('\\end{titlepage}')[0]);
  assert.doesNotMatch(cover, /Latest earned evidence:/u);
  assert.ok(cover.includes('Formal artefact coverage: ' + a.earnedRows + ' of ' + a.totalRows));
  assert.ok(cover.includes('Risk-weighted proof completion estimate: ' + p.percent + ' percent.'));
});
