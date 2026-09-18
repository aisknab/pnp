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
    "PNP.DirectWire.WireProfileRestoration.quotientAgreement_iff",
    "ac36df8e2914ca2ce3b3ac0d5194e7a44198896040c925ef6043ac2f22fb3aa8",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.expanded_fullEquivalent",
    "152cc0a4a34040eefc769049f57dcc7aaf507acf0c24c01eec7bfa5ab6196db3",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.paidWitness_fullEquivalent",
    "91fcd87a05266afd4d59445e508f39356e1e965d285ef0b60cc4f56c4a4dd9ed",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.paidWitness_gateCount",
    "e65c828f6ba184573026592c22c615ae9f0fe922aff384f9f2f9fbc71ff11e2c",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.fullMinimum_le_quotientMinimum_add_charge",
    "e2f252b82be65ebb18a0e0c5ace67f3caabe1dc7a5f05ea2c0764a2a140d3dc2",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.projectionDefect_le_charge",
    "d13d80014d1eb15d43b0a481ec8410b545b7d5a4da81db03642497e4a9adc34a",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.paidWitness_exact_overhead",
    "d6e074081f87063d2ad6b713ea09e5b94f40b36fc757d0e6f0380a845a181bc8",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.paidWitness_smaller_iff",
    "2d72664e0872f27c3be711951c70a4bde84886e8d534ba832e6cb064fada4110",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.paidWitness_optimal_iff",
    "604ebe08bd50792b3dbe74affbc0492bf2a02f32ed646c9516b750d6d4ab6f70",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.normalizedWitness_fullEquivalent",
    "b37fe38d1f18d15b720080ce5e292b25c8e54a38828f1c680c79c8e2d61ca99c",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.normalizedWitness_exact_accounting",
    "ccec14b81c029475f4a7caad3f9b3ba495fb09ca36775702d4136fe61f96802e",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.reclaimed_le_overhead",
    "c3969ffe2a61b71d46de269c9fe5f133acd8e70ad4ce790bacc2c3ea0679bf30",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.normalizedWitness_exact_overhead",
    "9bd7117014ca4004f05332c0799bb8e826688013cfc98ad10753be970beb3792",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.normalizedWitness_smaller_iff",
    "e881bf24f9e1fbe5127979e5c6f5e5c2ec61332e3dbdcbf51a33073fd74e4139",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.normalizedWitness_optimal_iff",
    "cbdfbb757e43dc5d2f937f0df5b89af7a810ec01e5959945386694abba9892ae",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.checkedGain_isSome_iff",
    "04233de3e6c6d5992d8c268e06c05f122e8ec5be9f2b628eead4590c7e3f3c5d",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.CheckedGain.checked",
    "f4d34bc65c13885b7f892e5ecaad086bb0d53ea2a7208656998c0f1754fc8b90",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.unary_fullMinimum",
    "ac5222a3652828c7cffb92f14906304bb4e1d65b250e533093b217fea53bb4e4",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfileRestoration.unary_smaller_iff_fullSlack_positive",
    "7533c99f91b3438644083adba00c92b4e89522c9e45b65e14b8f65f11bac5df3",
    "PNP.NANDWireProfileRestoration",
    [
      "Quot.sound",
      "propext"
    ]
  ]
];
const MILESTONE = {
  "classification": "formalized-foundation-only",
  "id": "wire-profile-restoration-cost",
  "title": "Constructive wire-profile restoration cost and exact gain boundary",
  "requiredTheorems": [
    "PNP.DirectWire.WireProfileRestoration.quotientAgreement_iff",
    "PNP.DirectWire.WireProfileRestoration.expanded_fullEquivalent",
    "PNP.DirectWire.WireProfileRestoration.paidWitness_fullEquivalent",
    "PNP.DirectWire.WireProfileRestoration.paidWitness_gateCount",
    "PNP.DirectWire.WireProfileRestoration.fullMinimum_le_quotientMinimum_add_charge",
    "PNP.DirectWire.WireProfileRestoration.projectionDefect_le_charge",
    "PNP.DirectWire.WireProfileRestoration.paidWitness_exact_overhead",
    "PNP.DirectWire.WireProfileRestoration.paidWitness_smaller_iff",
    "PNP.DirectWire.WireProfileRestoration.paidWitness_optimal_iff",
    "PNP.DirectWire.WireProfileRestoration.normalizedWitness_fullEquivalent",
    "PNP.DirectWire.WireProfileRestoration.normalizedWitness_exact_accounting",
    "PNP.DirectWire.WireProfileRestoration.reclaimed_le_overhead",
    "PNP.DirectWire.WireProfileRestoration.normalizedWitness_exact_overhead",
    "PNP.DirectWire.WireProfileRestoration.normalizedWitness_smaller_iff",
    "PNP.DirectWire.WireProfileRestoration.normalizedWitness_optimal_iff",
    "PNP.DirectWire.WireProfileRestoration.checkedGain_isSome_iff",
    "PNP.DirectWire.WireProfileRestoration.CheckedGain.checked",
    "PNP.DirectWire.WireProfileRestoration.unary_fullMinimum",
    "PNP.DirectWire.WireProfileRestoration.unary_smaller_iff_fullSlack_positive"
  ],
  "scope": "For arbitrary finite input, ordinary-output and computational-field widths, the existing concrete quotient agreement is equivalent to wire-profile quotient comparison. The actual shared hidden-wire materializer restores the computed quotient-minimum witness into a full-equivalent carrier, preserving every ordinary output and actual field at every input valuation. If F is the full minimum, Q the quotient minimum, C the actual materializer charge, D = F - Q and S the actual full-field normalization saving, the theorems prove F <= Q + C, D <= C, paid cost = F + (C - D), S <= C - D and normalized cost = F + (C - D - S). Strict improvement against the original carrier is equivalent to the remaining overhead being smaller than its full slack; the executable acceptance test checks the actual final size and yields a sound strict equivalent gain. The existing complete one-input constructor has gate count exactly F for arbitrary output and field widths, and improves the original exactly when full slack is positive. No full replacement, minimum, charge or correctness certificate is supplied to the constructed route.",
  "nonClaim": "This is a cost and compatibility interface for computational wire profiles, not complete manuscript profiles or a terminal-derived family. The materializer charge only upper-bounds projection defect; equality and forced-cost transparency are not established. Physical normalization is not a semantic minimizer. A kernel-checked positive-slack example is refused by restoration plus normalization, while the existing unary route recovers it; this limits that component, not every route or the manuscript's complete route family. Returning no gain does not establish ZeroSlack. Unary completeness is restricted to one input and is reused, not newly proved for arbitrary inputs. Reference minimization is exhaustive, not a polynomial PCCMin algorithm. Complete Package E, global route coverage and rank decrease, unconditional SaturatePositive, BCELReady and ZeroSlack, exact polynomial PCCMin, encoded runtime, output and certificate bounds, deterministic CNFSAT in P and the eligible root remain open. No fixed weighted checkpoint or global proof gate closes, and P = NP is not proved."
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

test('M275 compiled interface: exact types, modules and axiom closures earn only the reviewed row', async () => {
  const {inventory, map, inventoryBytes, sourceClosure} = await sources0();
  assert.ok(canonical0(inventory).equals(inventoryBytes));
  const names = REVIEWED.map(row => row[0]);
  assert.equal(names.length, 19);
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

test('M275 compiled interface: weakening or supplying a conclusion cannot retain credit', async () => {
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
  // full restoration, exact normalized overhead and the unary minimum interface.
  for (const name of [
    'PNP.DirectWire.WireProfileRestoration.paidWitness_fullEquivalent',
    'PNP.DirectWire.WireProfileRestoration.normalizedWitness_exact_overhead',
    'PNP.DirectWire.WireProfileRestoration.unary_fullMinimum',
  ]) for (const kernelType of alternatives.get(name)) {
    const mutation = {...inventory, milestoneCandidates: inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), sourceClosure);
    assert.equal(result.milestones.find(row => row.id === MILESTONE.id).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
});

test('M275 compiled interface: missing evidence, added authority and widened scope reject', async () => {
  const {inventory, inventoryBytes, map, sourceClosure} = await sources0();
  const name = 'PNP.DirectWire.WireProfileRestoration.normalizedWitness_exact_overhead';
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
      ? {...row, [field]: 'Restoration always finds a strict gain, computes a polynomial minimum and establishes unconditional global ZeroSlack.'} : row)};
    assert.throws(() => DeriveFormalPublication0(inventory, widened, inventoryBytes, sourceClosure),
      /map drifted from the reviewed specification/u);
  }
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256: {
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]: '0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, inventoryBytes, sourceClosure),
    /map drifted from the reviewed specification/u);
});

const META = {
  "coordinate": "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-19-275",
  "statusFields": {
    "leanWireProfileRestorationFormalized": true,
    "leanWireProfileRestorationAxiomAuditPassed": true,
    "leanWireProfileRestorationAuditedDeclarationCount": 19,
    "leanWireProfileRestorationQuotientAgreementTheorem": "PNP.DirectWire.WireProfileRestoration.quotientAgreement_iff",
    "leanWireProfileRestorationFullRestorationTheorem": "PNP.DirectWire.WireProfileRestoration.paidWitness_fullEquivalent",
    "leanWireProfileRestorationChargeBoundTheorem": "PNP.DirectWire.WireProfileRestoration.projectionDefect_le_charge",
    "leanWireProfileRestorationPaidOverheadTheorem": "PNP.DirectWire.WireProfileRestoration.paidWitness_exact_overhead",
    "leanWireProfileRestorationReclaimedBoundTheorem": "PNP.DirectWire.WireProfileRestoration.reclaimed_le_overhead",
    "leanWireProfileRestorationNormalizedOverheadTheorem": "PNP.DirectWire.WireProfileRestoration.normalizedWitness_exact_overhead",
    "leanWireProfileRestorationStrictGainTheorem": "PNP.DirectWire.WireProfileRestoration.normalizedWitness_smaller_iff",
    "leanWireProfileRestorationCheckedGainTheorem": "PNP.DirectWire.WireProfileRestoration.CheckedGain.checked",
    "leanWireProfileRestorationUnaryMinimumTheorem": "PNP.DirectWire.WireProfileRestoration.unary_fullMinimum",
    "leanWireProfileRestorationUnaryGainTheorem": "PNP.DirectWire.WireProfileRestoration.unary_smaller_iff_fullSlack_positive",
    "leanWireProfileRestorationArbitraryFiniteDimensionsCovered": true,
    "leanWireProfileRestorationOrdinaryOutputsAndActualFieldsPreserved": true,
    "leanWireProfileRestorationExistingSharedMaterializerReused": true,
    "leanWireProfileRestorationActualPhysicalChargeAndSavingsComputed": true,
    "leanWireProfileRestorationExactRemainingOverheadDerived": true,
    "leanWireProfileRestorationStrictOriginalSizeComparisonChecked": true,
    "leanWireProfileRestorationExistingUnaryMinimumCompatibilityProved": true,
    "leanWireProfileRestorationUnaryCompatibilityHasArbitraryOutputAndFieldWidths": true,
    "leanWireProfileRestorationPositiveSlackRefusalAndUnaryRecoveryKernelChecked": true,
    "leanWireProfileRestorationCallerSuppliedWitnessMinimumOrCorrectnessRequired": false,
    "leanWireProfileRestorationChargeEqualsProjectionDefectProved": false,
    "leanWireProfileRestorationNormalizerIsSemanticallyComplete": false,
    "leanWireProfileRestorationNoGainImpliesZeroSlack": false,
    "leanWireProfileRestorationUnaryCompletenessExtendedToArbitraryInputs": false,
    "leanWireProfileRestorationCompleteManuscriptProfileGrammarProved": false,
    "leanWireProfileRestorationTerminalFamiliesDerived": false,
    "leanWireProfileRestorationCompletePackageEOrGlobalRoutesProved": false,
    "leanWireProfileRestorationUnconditionalSaturatePositiveProved": false,
    "leanWireProfileRestorationUnconditionalBCELReadyProved": false,
    "leanWireProfileRestorationUnconditionalZeroSlackProved": false,
    "leanWireProfileRestorationExactPolynomialPCCMinProved": false,
    "leanWireProfileRestorationPolynomialRuntimeOutputAndCertificateBoundsProved": false,
    "leanWireProfileRestorationReferenceMinimizationIsExhaustive": true,
    "leanWireProfileRestorationRuntimeExecutionIsProofAuthority": false,
    "leanWireProfileRestorationScope": "arbitrary-finite-actual-wire-full-restoration-shared-materializer-charge-defect-upper-bound-paid-and-normalized-exact-overhead-checked-strict-gain-existing-one-input-minimum-compatibility-no-general-completeness-or-polynomial-claim"
  },
  "command": "node --test audits/lean-wire-profile-restoration0.test.mjs audits/lean-wire-profile-restoration-publication0.test.mjs",
  "testFiles": [
    "audits/lean-wire-profile-restoration0.test.mjs",
    "audits/lean-wire-profile-restoration-publication0.test.mjs"
  ],
  "audit": "lean-audit/PNPWireProfileRestorationAxiomAudit.lean",
  "regressionCommands": [
    "lake env lean -DwarningAsError=true --run lean-regression/PNPWireProfileRestoration.lean",
    "lake env lean -DwarningAsError=true lean-regression/PNPWireProfileRestorationObstruction.lean"
  ],
  "workflowCommands": "set -euo pipefail\nnode scripts/check-lean-axioms.mjs lean-audit/PNPWireProfileRestorationAxiomAudit.lean\nlake env lean -DwarningAsError=true --run lean-regression/PNPWireProfileRestoration.lean\nlake env lean -DwarningAsError=true lean-regression/PNPWireProfileRestorationObstruction.lean\n",
  "publicationDecision": "Publication decision: defer. This establishes a general restoration-cost interface and its checked limitations, not terminal-derived families, complete Package E or global route coverage. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.",
  "rationale": "M275 connects the existing actual shared hidden-wire materializer to wire-profile full and quotient minima. It proves exact paid and normalized overhead and the strict original-size gain boundary without a supplied replacement, minimum, charge or correctness certificate. A kernel-checked positive-slack refusal records the limit of restoration alone; the already complete one-input constructor recovers that example, and its general output/field-width minimum is identified with the current full minimum. This reuses existing construction and unary completeness rather than awarding duplicate progress. Reference minimization remains exhaustive. Complete profile grammar, derived terminal families, forced-cost transparency, global route coverage and polynomial minimization remain open. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.",
  "doc": "docs/lean_wire_profile_restoration.md",
  "plan": "docs/plans/2026-09-19-wire-profile-restoration-cost.md"
};
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();
async function release0() {
  const [statusText, progressText] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('status/PROOF_PROGRESS.json'),
  ]);
  return {status: JSON.parse(statusText), progress: JSON.parse(progressText)};
}

test('M275 release preflight: package, exact workflow and status commands share one interface', async () => {
  const [pkg, surface, verifier, workflow, statusSource, statusText] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'), text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'), text0('pcc-formal-reconstruction-status0.mjs'),
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  ]);
  assert.equal(JSON.parse(pkg).scripts['audit:m275'], META.command);
  assert.ok(surface.includes("'audit:m275': '" + META.command + "'"));
  for (const file of META.testFiles) assert.ok(verifier.includes("'" + file + "'"), file);
  assert.ok(workflow.includes('run: npm run audit:m275'));
  const steps = workflow.split(/^      - name:/mu).filter(step =>
    step.includes('node scripts/check-lean-axioms.mjs ' + META.audit));
  assert.equal(steps.length, 1);
  const block = steps[0].split('        run: |\n')[1];
  assert.ok(block);
  assert.equal(block.trimEnd().split('\n').map(line => line.slice(10)).join('\n') + '\n', META.workflowCommands);
  const status = JSON.parse(statusText);
  for (const command of [
    'npm run audit:m275', 'node scripts/check-lean-axioms.mjs ' + META.audit,
    ...META.regressionCommands,
  ]) assert.ok(status.verificationCommands.includes(command), command);
  for (const field of Object.keys(META.statusFields))
    assert.equal(statusSource.split(field + ':').length - 1, 2, field);
});

test('M275 release: status pins the exact bounded claims and rejects every changed field', async () => {
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

test('M275 release: restoration cost compatibility earns no unconditional checkpoint', async () => {
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

test('M275 release: every current summary and FAQ uses the canonical independent metrics', async () => {
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
      assert.ok(boundary?.includes('M275'));
      assert.ok(boundary.includes('global route coverage'));
    }
    if (['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
      'docs/proof_pipeline.md', 'docs/audit_questions.md'].includes(file)) {
      const region = text.split('<!-- M275-CURRENT-SUMMARY:BEGIN -->')[1]?.split('<!-- M275-CURRENT-SUMMARY:END -->')[0];
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
