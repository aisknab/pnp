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
    "PNP.DirectWire.ClosedWholeMinimum.ambient_output_absent",
    "de1f2f9477952316157534c5abccc9eb177defc5ca4c63f3d3813b47b56d6f63",
    "PNP.NANDClosedWholeMinimumPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.available_all",
    "abda5f4e8f992398218a6715a299cd2040fa7484a95c40e6427e8aaedcf6d4c7",
    "PNP.NANDClosedWholeMinimumPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.forward_available",
    "d2bc1aa0bc4e5b2485adb2b925a9ea19d3ad2165fcf5cb85f68da57bb8adb7b2",
    "PNP.NANDClosedWholeMinimum",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.forward_equivalent",
    "1b55ee408cd4b476c52987bc53616ce1a0b26e6e9fa904db928fe37c086fe516",
    "PNP.NANDClosedWholeMinimum",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.forward_gateCount",
    "0a6b23e44cbdda91623811bde32b30c4afed5f39a27cfd30ae18de3677825803",
    "PNP.NANDClosedWholeMinimum",
    []
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.forward_output_none",
    "717987c2cf6cee2ee80ce3e80336f92d6327a475483976348f1acbc9bd245ae0",
    "PNP.NANDClosedWholeMinimum",
    []
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.forward_output_some",
    "8f107d84399f072c2dea4fc67e348da169a3cb6bb716b8965eba34cdfd6ca22f",
    "PNP.NANDClosedWholeMinimum",
    []
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.fullSlack_eq",
    "b87bc9c3743641fe8d6481244fb1fcfe4a3bd090a75fd1563505eb98c2ace03d",
    "PNP.NANDClosedWholeMinimum",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.full_minimum",
    "1130eabcdce4e914eb1b975ba1a71cbc5aaba01c275c589522d419190f180577",
    "PNP.NANDClosedWholeMinimum",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.gate_selected",
    "4941ffa61289594b072955d12bdf1d4b745dc4044652d9802b32f811b45321ce",
    "PNP.NANDClosedWholeMinimumPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.global_minimum_le",
    "620f470f41a44eed9fcc3b80b1d0ed4bff3eb078430433dbc5f1b30c1aa0051f",
    "PNP.NANDClosedWholeMinimumPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.improvement_none_iff",
    "d31e874330121a7b2919784e382cc5c0956e819d4a9415e68773d2fb2de9695e",
    "PNP.NANDClosedWholeMinimum",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.interface_iff_output",
    "958fd1e723c83dd5071f3a5dffcffc38bdf66fab22357ad6da44d0b249d64179",
    "PNP.NANDClosedWholeMinimumPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.outputIndex_exists",
    "bc950d30ff11863f52698c243a1668d7b015a945377de5571996238d2671533c",
    "PNP.NANDClosedWholeMinimumPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.outputIndex_none_not_interface",
    "d6e35fa2b4b3d2dfd9a1de80fb8f2d4b2bd6166f7edd192867f7d89920b979f6",
    "PNP.NANDClosedWholeMinimumPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.outputIndex_sound",
    "949c3138997ab5f60be81748a37eb85c64823d87d61c4cf8abe303c8180d49d8",
    "PNP.NANDClosedWholeMinimumPrefix",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.result_gateCount",
    "10ad0ca84393a31831a39e1a0db9c8f0068e672d9d5d8075328d2dbdc9a25014",
    "PNP.NANDClosedWholeMinimumPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.result_optimal",
    "98b401fb9516b8b8e1a9525bb49d69be4cc0318e11cf9f8a5f1aa7f47e02696b",
    "PNP.NANDClosedWholeMinimum",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.result_zero_fullSlack",
    "848cab843f093d0b0ecb0c5d8f966843bee0079620bae28bb8dda4d3afd4d6e5",
    "PNP.NANDClosedWholeMinimum",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.source_retained",
    "00955517186813221b3a6ce2d1dceacfbfd4d6edcaefbe348be0d8c0ebf086d6",
    "PNP.NANDClosedWholeMinimumPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.support_gateCount",
    "cbdc7da1e90b9748c70d67cd45d0c4e2cd54b7d79b68b9fe0d7379c6b7068d0d",
    "PNP.NANDClosedWholeMinimumPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedWholeMinimum.support_minimum_le",
    "200e284d486b2a3494379785431d126117cc77f4956c42ef5d24d9341109c925",
    "PNP.NANDClosedWholeMinimum",
    [
      "Quot.sound",
      "propext"
    ]
  ]
];
const MILESTONE = {
  "classification": "formalized-foundation-only",
  "id": "computed-whole-support-minimum-bridge",
  "nonClaim": "The whole-span reference branch remains exhaustive, including minimum search, source matching and saturation influence. Zero slack after exhaustive reference minimization is not the manuscript's unconditional ZeroSlack theorem or a polynomial PCCMin algorithm. This does not discover a proper positive support, compile arbitrary minima into proper-local VerifyDW histories, reconstruct the complete noncomputational profile grammar, derive global route coverage or unconditional SaturatePositive and BCELReady, or establish complete polynomial runtime, output-size or certificate bounds. The eligible root theorem remains absent and P = NP is not proved.",
  "requiredTheorems": [
    "PNP.DirectWire.ClosedWholeMinimum.ambient_output_absent",
    "PNP.DirectWire.ClosedWholeMinimum.available_all",
    "PNP.DirectWire.ClosedWholeMinimum.forward_available",
    "PNP.DirectWire.ClosedWholeMinimum.forward_equivalent",
    "PNP.DirectWire.ClosedWholeMinimum.forward_gateCount",
    "PNP.DirectWire.ClosedWholeMinimum.forward_output_none",
    "PNP.DirectWire.ClosedWholeMinimum.forward_output_some",
    "PNP.DirectWire.ClosedWholeMinimum.fullSlack_eq",
    "PNP.DirectWire.ClosedWholeMinimum.full_minimum",
    "PNP.DirectWire.ClosedWholeMinimum.gate_selected",
    "PNP.DirectWire.ClosedWholeMinimum.global_minimum_le",
    "PNP.DirectWire.ClosedWholeMinimum.improvement_none_iff",
    "PNP.DirectWire.ClosedWholeMinimum.interface_iff_output",
    "PNP.DirectWire.ClosedWholeMinimum.outputIndex_exists",
    "PNP.DirectWire.ClosedWholeMinimum.outputIndex_none_not_interface",
    "PNP.DirectWire.ClosedWholeMinimum.outputIndex_sound",
    "PNP.DirectWire.ClosedWholeMinimum.result_gateCount",
    "PNP.DirectWire.ClosedWholeMinimum.result_optimal",
    "PNP.DirectWire.ClosedWholeMinimum.result_zero_fullSlack",
    "PNP.DirectWire.ClosedWholeMinimum.source_retained",
    "PNP.DirectWire.ClosedWholeMinimum.support_gateCount",
    "PNP.DirectWire.ClosedWholeMinimum.support_minimum_le"
  ],
  "scope": "For arbitrary finite wire carriers and keep masks, the physical whole-support seed is derived from all original gates. Its computed saturated interface contains exactly the original gate-valued ordinary outputs, while every computational field is available. Explicit size-preserving comparisons identify its full-profile reference minimum with the independent whole-carrier output-and-field minimum. The actual computed full-profile replacement attains that minimum, has zero remaining whole-carrier full slack, and returns no strict improvement exactly when the original whole-carrier full slack is zero. The seed, interface, observer, minimum and replacement are derived rather than supplied correctness data.",
  "title": "Computed whole-support minimum bridge"
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

test('M279 compiled interface: exact types, modules and axiom closures earn only the reviewed row', async () => {
  const {inventory, map, inventoryBytes, sourceClosure} = await sources0();
  assert.ok(canonical0(inventory).equals(inventoryBytes));
  const names = REVIEWED.map(row => row[0]);
  assert.equal(names.length, 22);
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

test('M279 compiled interface: weakening or supplying a conclusion cannot retain credit', async () => {
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
  // the exact minimum equality, attained optimum and whole-span no-gain boundary.
  for (const name of [
    'PNP.DirectWire.ClosedWholeMinimum.full_minimum',
    'PNP.DirectWire.ClosedWholeMinimum.result_optimal',
    'PNP.DirectWire.ClosedWholeMinimum.improvement_none_iff',
  ]) for (const kernelType of alternatives.get(name)) {
    const mutation = {...inventory, milestoneCandidates: inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), sourceClosure);
    assert.equal(result.milestones.find(row => row.id === MILESTONE.id).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
});

test('M279 compiled interface: missing evidence, added authority and widened scope reject', async () => {
  const {inventory, inventoryBytes, map, sourceClosure} = await sources0();
  const name = 'PNP.DirectWire.ClosedWholeMinimum.result_optimal';
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
      ? {...row, [field]: 'Computed reference savings automatically yield proper-positive supports, global route completeness, unconditional ZeroSlack and polynomial minimization.'} : row)};
    assert.throws(() => DeriveFormalPublication0(inventory, widened, inventoryBytes, sourceClosure),
      /map drifted from the reviewed specification/u);
  }
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256: {
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]: '0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, inventoryBytes, sourceClosure),
    /map drifted from the reviewed specification/u);
});

const META = {
  "coordinate": "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-20-279",
  "doc": "docs/lean_closed_whole_minimum.md",
  "plan": "docs/plans/2026-09-20-computed-whole-support-minimum-bridge.md",
  "audit": "lean-audit/PNPClosedWholeMinimumAxiomAudit.lean",
  "testFiles": [
    "audits/lean-closed-whole-minimum0.test.mjs",
    "audits/lean-closed-whole-minimum-publication0.test.mjs"
  ],
  "command": "node --test audits/lean-closed-whole-minimum0.test.mjs audits/lean-closed-whole-minimum-publication0.test.mjs",
  "workflowCommands": "set -euo pipefail\nnode scripts/check-lean-axioms.mjs lean-audit/PNPClosedWholeMinimumAxiomAudit.lean\nlake env lean -DwarningAsError=true --run lean-regression/PNPClosedWholeMinimum.lean\n",
  "publicationDecision": "Publication decision: defer. This identifies two finite reference minima and the exact whole-span reference branch, not a new polynomial construction, proper-positive support discovery, complete manuscript profiles or global route closure. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.",
  "regressionCommands": [
    "lake env lean -DwarningAsError=true --run lean-regression/PNPClosedWholeMinimum.lean"
  ],
  "statusFields": {
    "leanClosedWholeMinimumFormalized": true,
    "leanClosedWholeMinimumAxiomAuditPassed": true,
    "leanClosedWholeMinimumAuditedDeclarationCount": 22,
    "leanClosedWholeMinimumDerivedWholeSeedTheorem": "PNP.DirectWire.ClosedWholeMinimum.support_gateCount",
    "leanClosedWholeMinimumExactOrdinaryInterfaceTheorem": "PNP.DirectWire.ClosedWholeMinimum.interface_iff_output",
    "leanClosedWholeMinimumComputedFieldAvailabilityTheorem": "PNP.DirectWire.ClosedWholeMinimum.available_all",
    "leanClosedWholeMinimumSizePreservingComparisonTheorem": "PNP.DirectWire.ClosedWholeMinimum.forward_gateCount",
    "leanClosedWholeMinimumExactMinimumTheorem": "PNP.DirectWire.ClosedWholeMinimum.full_minimum",
    "leanClosedWholeMinimumAttainedMinimumTheorem": "PNP.DirectWire.ClosedWholeMinimum.result_optimal",
    "leanClosedWholeMinimumExactFullSlackTheorem": "PNP.DirectWire.ClosedWholeMinimum.fullSlack_eq",
    "leanClosedWholeMinimumPostReferenceSlackTheorem": "PNP.DirectWire.ClosedWholeMinimum.result_zero_fullSlack",
    "leanClosedWholeMinimumCheckedNoImprovementTheorem": "PNP.DirectWire.ClosedWholeMinimum.improvement_none_iff",
    "leanClosedWholeMinimumArbitraryFiniteDimensionsCovered": true,
    "leanClosedWholeMinimumSeedInterfaceAndObserverDerived": true,
    "leanClosedWholeMinimumIndependentFullReferenceMinimaEqual": true,
    "leanClosedWholeMinimumComputedResultAttainsFullReferenceMinimum": true,
    "leanClosedWholeMinimumCallerSuppliedEqualityMinimumOrCorrectnessRequired": false,
    "leanClosedWholeMinimumWholeSpanIsProperLocalVerifyDW": false,
    "leanClosedWholeMinimumProperPositiveSupportDiscoveryProved": false,
    "leanClosedWholeMinimumCompleteManuscriptProfileGrammarProved": false,
    "leanClosedWholeMinimumGlobalRouteCoverageProved": false,
    "leanClosedWholeMinimumUnconditionalSaturatePositiveProved": false,
    "leanClosedWholeMinimumUnconditionalBCELReadyProved": false,
    "leanClosedWholeMinimumUnconditionalZeroSlackProved": false,
    "leanClosedWholeMinimumExactPolynomialPCCMinProved": false,
    "leanClosedWholeMinimumPolynomialRuntimeOutputAndCertificateBoundsProved": false,
    "leanClosedWholeMinimumReferenceSearchRemainsExhaustive": true,
    "leanClosedWholeMinimumRuntimeExecutionIsProofAuthority": false,
    "leanClosedWholeMinimumScope": "arbitrary-finite-derived-whole-gate-seed-computed-ordinary-interface-full-field-availability-size-preserving-two-way-reference-minimum-equality-attained-whole-full-minimum-no-proper-local-manuscript-zeroslack-global-route-or-polynomial-claim"
  }
};
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();
async function release0() {
  const [statusText, progressText] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('status/PROOF_PROGRESS.json'),
  ]);
  return {status: JSON.parse(statusText), progress: JSON.parse(progressText)};
}

test('M279 release preflight: package, exact workflow and status commands share one interface', async () => {
  const [pkg, surface, verifier, workflow, statusSource, statusText] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'), text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'), text0('pcc-formal-reconstruction-status0.mjs'),
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  ]);
  assert.equal(JSON.parse(pkg).scripts['audit:m279'], META.command);
  assert.ok(surface.includes("'audit:m279': '" + META.command + "'"));
  for (const file of META.testFiles) assert.ok(verifier.includes("'" + file + "'"), file);
  assert.ok(workflow.includes('run: npm run audit:m279'));
  const steps = workflow.split(/^      - name:/mu).filter(step =>
    step.includes('node scripts/check-lean-axioms.mjs ' + META.audit));
  assert.equal(steps.length, 1);
  const block = steps[0].split('        run: |\n')[1];
  assert.ok(block);
  assert.equal(block.trimEnd().split('\n').map(line => line.slice(10)).join('\n') + '\n', META.workflowCommands);
  const status = JSON.parse(statusText);
  for (const command of [
    'npm run audit:m279', 'node scripts/check-lean-axioms.mjs ' + META.audit,
    ...META.regressionCommands,
  ]) assert.ok(status.verificationCommands.includes(command), command);
  for (const field of Object.keys(META.statusFields))
    assert.equal(statusSource.split(field + ':').length - 1, 2, field);
});

test('M279 release: status pins the exact bounded claims and rejects every changed field', async () => {
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

test('M279 release: computed whole-support minimum bridge earns no unconditional checkpoint', async () => {
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

test('M279 release: every current summary and FAQ uses the canonical independent metrics', async () => {
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
      assert.ok(boundary?.includes('M279'));
      assert.ok(boundary.includes('global route coverage'));
    }
    if (['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
      'docs/proof_pipeline.md', 'docs/audit_questions.md'].includes(file)) {
      const region = text.split('<!-- M279-CURRENT-SUMMARY:BEGIN -->')[1]?.split('<!-- M279-CURRENT-SUMMARY:END -->')[0];
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
