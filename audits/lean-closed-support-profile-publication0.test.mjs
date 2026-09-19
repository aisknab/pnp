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
    "PNP.DirectWire.ClosedSupportObservation.available_eq_tableAvailable",
    "36284860f3182440dcc3da9997bd6ed38ead391b387a68fadc80ed25afac84d0",
    "PNP.NANDClosedSupportObservation",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportObservation.available_iff_retained_source",
    "fb3cb40786c80fcf013c7f3b416afde3aa2387726e22d9e9493e31e029509a9e",
    "PNP.NANDClosedSupportObservation",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportObservation.available_of_retained_source",
    "f313f1f1d7ee09299706e95e0f60c23bbb7ef276e2eb5258128d2ed374e08d66",
    "PNP.NANDClosedSupportObservation",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportObservation.boundary_isInput",
    "e5d2bdf2e64b60135b2d4e6252234b5243512f5cd8e53856081b30ee9569e790",
    "PNP.NANDClosedSupportObservation",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportObservation.gate_value",
    "950413f4c8ad24ce9d900ad8e199be263bc32bc12bf90cbdd9d59baa82503ad0",
    "PNP.NANDClosedSupportObservation",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportObservation.lift_retained_source",
    "c4e8768c53b537b640523e5c1d0611fb537c87246605a8c092c02e964abe9f4b",
    "PNP.NANDClosedSupportObservation",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportObservation.mem_matchingSources",
    "2b64c44c843b773cc956648fcd42c136cf5ee3bf16145ca09ca5d996fbbdba15",
    "PNP.NANDClosedSupportObservation",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportObservation.retract_support_source",
    "13d83a42f5ffa140fff436423e6c8f6970d29f3edfb0a19934e6817f96475210",
    "PNP.NANDClosedSupportObservation",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportObservation.tableAvailable_iff",
    "70a629b8bf4422a67cc1d98a7439d27894a786f3aa7d27f6f5c12d7de06a3e1f",
    "PNP.NANDClosedSupportObservation",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportProfile.profile_available",
    "0c747b559a85a56a1bec444232dce9fa606376204c01ea1e7fc95942017c6ce2",
    "PNP.NANDClosedSupportProfile",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportProfile.projected_available",
    "9c9c8563bcb49b2ec9d6b9ab3adeacd1c7cd478a192a667b65f33ed5ee74cfb9",
    "PNP.NANDClosedSupportProfile",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportProfile.projected_fieldValue",
    "d4667a897c89db1f6be34087132d22ee064e589dddfce16ee9c2e3a9958051d6",
    "PNP.NANDClosedSupportProfile",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportProfile.projected_tableAvailable",
    "86a59577ff0afb9bd2fa697503a95050a44b2b898886d539749522c129c92e89",
    "PNP.NANDClosedSupportProfile",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportSquare.corner_available",
    "be838c5b6f99217989f84aa11a754ed1d1525ee873c4849d805bf4859f886d8e",
    "PNP.NANDClosedSupportSquare",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportSquare.corner_fieldValue",
    "4f09121aaf481d01c80e32facf4824f2b9da76e056e472f264157ecd313934a0",
    "PNP.NANDClosedSupportSquare",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportSquare.corner_profileMember",
    "ef29c2d6dbf0afbd1fcb21f82f2fa23afd42478e9240a817813932c0aaf1cad4",
    "PNP.NANDClosedSupportSquare",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportSquare.corners_fieldValue_equal",
    "c4b49f95b5d857ed5a1b166c77ce9b7cb072cfaab7ce97b0651f002ec90855b8",
    "PNP.NANDClosedSupportSquare",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportUnion.available_append",
    "cf59906f789c5a7c18e811d8dd05fd878ea337c3f934b17f4237df8ee8063488",
    "PNP.NANDClosedSupportUnion",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportUnion.available_flatten",
    "826ace2bec3532d1c43ed0f33596c8c873a0c7b86c93607936066eb2ba39a15b",
    "PNP.NANDClosedSupportUnion",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportUnion.available_mono",
    "43c2830b54c41efa14a24e72c51d53c9d3e0683c48aa8b16e7daba77164fdba7",
    "PNP.NANDClosedSupportUnion",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportUnion.mem_records_append",
    "85c496b68303cc018de0098c6cf542f56d757ad95079bc9730e33f06853cb5bc",
    "PNP.NANDClosedSupportUnion",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportUnion.records_mono",
    "365f866fe74f2f178e8beadce47d4efbdd5d34d4f1207118081c8a47ddcc1b58",
    "PNP.NANDClosedSupportUnion",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportUnion.retained_append",
    "88acde589597fc8632407c9035e7d569998125775d3e4860e9bff33687720c18",
    "PNP.NANDClosedSupportUnion",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportUnion.tableAvailable_append",
    "d97244bbc85ab3df8ac32c368da9c1fc1eb61d943845c974a74a02ed320f96ef",
    "PNP.NANDClosedSupportUnion",
    [
      "Quot.sound",
      "propext"
    ]
  ]
];
const MILESTONE = {
  "classification": "formalized-foundation-only",
  "id": "computed-closed-support-profile-squares",
  "title": "Computed closed-support observations and profile-compatible squares",
  "scope": "For arbitrary finite input, ordinary-output and computational-field widths, the actual computed dependency-closed support observes a field exactly when it retains an original constant, input or gate source whose value agrees with that field uniformly over every input valuation. The matching table and support are computed from the circuit and ordinary seed data. For arbitrary seed pairs, observations of the computed union are the Boolean union of the separate observations. This extends to arbitrary finite families, with the empty support's observation as the base, and to seed-inclusion monotonicity. Seeding the requested profile records derives availability and uniform field-value preservation without injecting their literal original gate bindings. The actual meet, left, right and join of the constructed support square all preserve those requested computational fields and agree pairwise on their values at every ambient input valuation. Existing source extraction, structural square laws and arbitrary-context profile locality are reused, not newly claimed.",
  "nonClaim": "This is computational-field compatibility, not ordinary-output equivalence, the complete manuscript profile grammar, a terminal-derived governed family, or a legitimate full projection square. Field preservation does not imply a proper, smaller, minimum or positive support. A kernel-checked duplicate-circuit example has positive full slack but no proper seed in the computed model; the existing sharing pass removes that duplicate, so the example is not a normalized terminal counterexample and does not refute a manuscript theorem with additional terminal or admissibility hypotheses. Source matching and influence remain finite exhaustive computations, not polynomial algorithms. Complete Package E, forced-cost transparency, global route coverage and rank decrease, unconditional SaturatePositive, BCELReady and ZeroSlack, exact polynomial PCCMin, encoded runtime, output and certificate bounds, deterministic CNFSAT in P and the eligible root remain open. No fixed weighted checkpoint or global proof gate closes, and P = NP is not proved.",
  "requiredTheorems": [
    "PNP.DirectWire.ClosedSupportObservation.available_eq_tableAvailable",
    "PNP.DirectWire.ClosedSupportObservation.available_iff_retained_source",
    "PNP.DirectWire.ClosedSupportObservation.available_of_retained_source",
    "PNP.DirectWire.ClosedSupportObservation.boundary_isInput",
    "PNP.DirectWire.ClosedSupportObservation.gate_value",
    "PNP.DirectWire.ClosedSupportObservation.lift_retained_source",
    "PNP.DirectWire.ClosedSupportObservation.mem_matchingSources",
    "PNP.DirectWire.ClosedSupportObservation.retract_support_source",
    "PNP.DirectWire.ClosedSupportObservation.tableAvailable_iff",
    "PNP.DirectWire.ClosedSupportProfile.profile_available",
    "PNP.DirectWire.ClosedSupportProfile.projected_available",
    "PNP.DirectWire.ClosedSupportProfile.projected_fieldValue",
    "PNP.DirectWire.ClosedSupportProfile.projected_tableAvailable",
    "PNP.DirectWire.ClosedSupportSquare.corner_available",
    "PNP.DirectWire.ClosedSupportSquare.corner_fieldValue",
    "PNP.DirectWire.ClosedSupportSquare.corner_profileMember",
    "PNP.DirectWire.ClosedSupportSquare.corners_fieldValue_equal",
    "PNP.DirectWire.ClosedSupportUnion.available_append",
    "PNP.DirectWire.ClosedSupportUnion.available_flatten",
    "PNP.DirectWire.ClosedSupportUnion.available_mono",
    "PNP.DirectWire.ClosedSupportUnion.mem_records_append",
    "PNP.DirectWire.ClosedSupportUnion.records_mono",
    "PNP.DirectWire.ClosedSupportUnion.retained_append",
    "PNP.DirectWire.ClosedSupportUnion.tableAvailable_append"
  ]
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

test('M277 compiled interface: exact types, modules and axiom closures earn only the reviewed row', async () => {
  const {inventory, map, inventoryBytes, sourceClosure} = await sources0();
  assert.ok(canonical0(inventory).equals(inventoryBytes));
  const names = REVIEWED.map(row => row[0]);
  assert.equal(names.length, 24);
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

test('M277 compiled interface: weakening or supplying a conclusion cannot retain credit', async () => {
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
  // the computed observer, derived requested fields and actual square corners.
  for (const name of [
    'PNP.DirectWire.ClosedSupportObservation.available_iff_retained_source',
    'PNP.DirectWire.ClosedSupportProfile.projected_fieldValue',
    'PNP.DirectWire.ClosedSupportSquare.corners_fieldValue_equal',
  ]) for (const kernelType of alternatives.get(name)) {
    const mutation = {...inventory, milestoneCandidates: inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), sourceClosure);
    assert.equal(result.milestones.find(row => row.id === MILESTONE.id).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
});

test('M277 compiled interface: missing evidence, added authority and widened scope reject', async () => {
  const {inventory, inventoryBytes, map, sourceClosure} = await sources0();
  const name = 'PNP.DirectWire.ClosedSupportProfile.projected_fieldValue';
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
      ? {...row, [field]: 'Profile-compatible supports automatically preserve ordinary outputs and give proper positive supports, polynomial minimization and unconditional ZeroSlack.'} : row)};
    assert.throws(() => DeriveFormalPublication0(inventory, widened, inventoryBytes, sourceClosure),
      /map drifted from the reviewed specification/u);
  }
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256: {
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]: '0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, inventoryBytes, sourceClosure),
    /map drifted from the reviewed specification/u);
});

const META = {
  "coordinate": "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-19-277",
  "id": "computed-closed-support-profile-squares",
  "title": "Computed closed-support observations and profile-compatible squares",
  "classification": "formalized-foundation-only",
  "scope": "For arbitrary finite input, ordinary-output and computational-field widths, the actual computed dependency-closed support observes a field exactly when it retains an original constant, input or gate source whose value agrees with that field uniformly over every input valuation. The matching table and support are computed from the circuit and ordinary seed data. For arbitrary seed pairs, observations of the computed union are the Boolean union of the separate observations. This extends to arbitrary finite families, with the empty support's observation as the base, and to seed-inclusion monotonicity. Seeding the requested profile records derives availability and uniform field-value preservation without injecting their literal original gate bindings. The actual meet, left, right and join of the constructed support square all preserve those requested computational fields and agree pairwise on their values at every ambient input valuation. Existing source extraction, structural square laws and arbitrary-context profile locality are reused, not newly claimed.",
  "nonClaim": "This is computational-field compatibility, not ordinary-output equivalence, the complete manuscript profile grammar, a terminal-derived governed family, or a legitimate full projection square. Field preservation does not imply a proper, smaller, minimum or positive support. A kernel-checked duplicate-circuit example has positive full slack but no proper seed in the computed model; the existing sharing pass removes that duplicate, so the example is not a normalized terminal counterexample and does not refute a manuscript theorem with additional terminal or admissibility hypotheses. Source matching and influence remain finite exhaustive computations, not polynomial algorithms. Complete Package E, forced-cost transparency, global route coverage and rank decrease, unconditional SaturatePositive, BCELReady and ZeroSlack, exact polynomial PCCMin, encoded runtime, output and certificate bounds, deterministic CNFSAT in P and the eligible root remain open. No fixed weighted checkpoint or global proof gate closes, and P = NP is not proved.",
  "doc": "docs/lean_closed_support_profile.md",
  "plan": "docs/plans/2026-09-19-computed-closed-support-profile-square.md",
  "publicationDecision": "Publication decision: defer. This establishes computational-field compatibility for derived closed supports and their actual squares, not ordinary-output reconstruction, complete manuscript profiles, terminal-derived families, proper-positive discovery or global route coverage. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.",
  "rationale": "M277 derives the computational observations of actual closed supports and proves uniform preservation of requested fields at every corner of a constructed support square. The source table, arbitrary-family union law and profile-seeded construction close that bounded compatibility interface without supplied correctness data. Existing extraction, structural square laws and profile locality are reused, not awarded again. The positive-slack duplicate obstruction is explicitly candidate-level: the existing physical normalizer removes it, so it is not evidence against a normalized-terminal manuscript theorem. Ordinary-output reconstruction, the complete profile grammar, proper-positive support discovery, terminal-derived families, global routing and polynomial minimization remain open. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.",
  "statusFields": {
    "leanClosedSupportProfileFormalized": true,
    "leanClosedSupportProfileAxiomAuditPassed": true,
    "leanClosedSupportProfileAuditedDeclarationCount": 24,
    "leanClosedSupportProfileRetainedSourceTheorem": "PNP.DirectWire.ClosedSupportObservation.available_iff_retained_source",
    "leanClosedSupportProfileComputedTableTheorem": "PNP.DirectWire.ClosedSupportObservation.available_eq_tableAvailable",
    "leanClosedSupportProfileSeedUnionTheorem": "PNP.DirectWire.ClosedSupportUnion.available_append",
    "leanClosedSupportProfileFiniteFamilyTheorem": "PNP.DirectWire.ClosedSupportUnion.available_flatten",
    "leanClosedSupportProfileRequestedFieldsTheorem": "PNP.DirectWire.ClosedSupportProfile.projected_fieldValue",
    "leanClosedSupportProfileActualCornerTheorem": "PNP.DirectWire.ClosedSupportSquare.corner_fieldValue",
    "leanClosedSupportProfileCornerAgreementTheorem": "PNP.DirectWire.ClosedSupportSquare.corners_fieldValue_equal",
    "leanClosedSupportProfileArbitraryFiniteDimensionsCovered": true,
    "leanClosedSupportProfileComputedSupportAndMatchingTable": true,
    "leanClosedSupportProfileUniformFieldValuesAtActualCornersProved": true,
    "leanClosedSupportProfileCallerSuppliedClosureOrCorrectnessRequired": false,
    "leanClosedSupportProfileOrdinaryOutputEquivalenceProved": false,
    "leanClosedSupportProfileCompleteManuscriptProjectionSquareProved": false,
    "leanClosedSupportProfileProperPositiveSupportProved": false,
    "leanClosedSupportProfileDuplicateIsNormalizedTerminalCounterexample": false,
    "leanClosedSupportProfileCompletePackageEOrGlobalRoutesProved": false,
    "leanClosedSupportProfileUnconditionalSaturatePositiveProved": false,
    "leanClosedSupportProfileUnconditionalBCELReadyProved": false,
    "leanClosedSupportProfileUnconditionalZeroSlackProved": false,
    "leanClosedSupportProfileExactPolynomialPCCMinProved": false,
    "leanClosedSupportProfilePolynomialRuntimeOutputAndCertificateBoundsProved": false,
    "leanClosedSupportProfileSourceMatchingAndInfluenceAreExhaustive": true,
    "leanClosedSupportProfileRuntimeExecutionIsProofAuthority": false,
    "leanClosedSupportProfileScope": "arbitrary-finite-computed-closed-support-observations-source-alternatives-union-and-profile-seeded-actual-square-corner-compatibility-no-ordinary-output-proper-positive-full-profile-or-polynomial-claim"
  },
  "audit": "lean-audit/PNPClosedSupportProfileSquareAxiomAudit.lean",
  "command": "node --test audits/lean-closed-support-profile0.test.mjs audits/lean-closed-support-profile-publication0.test.mjs",
  "testFiles": [
    "audits/lean-closed-support-profile0.test.mjs",
    "audits/lean-closed-support-profile-publication0.test.mjs"
  ],
  "regressionCommands": [
    "lake env lean -DwarningAsError=true --run lean-regression/PNPClosedSupportProfileSquare.lean"
  ],
  "workflowCommands": "set -euo pipefail\nnode scripts/check-lean-axioms.mjs lean-audit/PNPClosedSupportProfileSquareAxiomAudit.lean\nlake env lean -DwarningAsError=true --run lean-regression/PNPClosedSupportProfileSquare.lean\n",
  "milestone": {
    "classification": "formalized-foundation-only",
    "id": "computed-closed-support-profile-squares",
    "title": "Computed closed-support observations and profile-compatible squares",
    "scope": "For arbitrary finite input, ordinary-output and computational-field widths, the actual computed dependency-closed support observes a field exactly when it retains an original constant, input or gate source whose value agrees with that field uniformly over every input valuation. The matching table and support are computed from the circuit and ordinary seed data. For arbitrary seed pairs, observations of the computed union are the Boolean union of the separate observations. This extends to arbitrary finite families, with the empty support's observation as the base, and to seed-inclusion monotonicity. Seeding the requested profile records derives availability and uniform field-value preservation without injecting their literal original gate bindings. The actual meet, left, right and join of the constructed support square all preserve those requested computational fields and agree pairwise on their values at every ambient input valuation. Existing source extraction, structural square laws and arbitrary-context profile locality are reused, not newly claimed.",
    "nonClaim": "This is computational-field compatibility, not ordinary-output equivalence, the complete manuscript profile grammar, a terminal-derived governed family, or a legitimate full projection square. Field preservation does not imply a proper, smaller, minimum or positive support. A kernel-checked duplicate-circuit example has positive full slack but no proper seed in the computed model; the existing sharing pass removes that duplicate, so the example is not a normalized terminal counterexample and does not refute a manuscript theorem with additional terminal or admissibility hypotheses. Source matching and influence remain finite exhaustive computations, not polynomial algorithms. Complete Package E, forced-cost transparency, global route coverage and rank decrease, unconditional SaturatePositive, BCELReady and ZeroSlack, exact polynomial PCCMin, encoded runtime, output and certificate bounds, deterministic CNFSAT in P and the eligible root remain open. No fixed weighted checkpoint or global proof gate closes, and P = NP is not proved.",
    "requiredTheorems": [
      "PNP.DirectWire.ClosedSupportObservation.available_eq_tableAvailable",
      "PNP.DirectWire.ClosedSupportObservation.available_iff_retained_source",
      "PNP.DirectWire.ClosedSupportObservation.available_of_retained_source",
      "PNP.DirectWire.ClosedSupportObservation.boundary_isInput",
      "PNP.DirectWire.ClosedSupportObservation.gate_value",
      "PNP.DirectWire.ClosedSupportObservation.lift_retained_source",
      "PNP.DirectWire.ClosedSupportObservation.mem_matchingSources",
      "PNP.DirectWire.ClosedSupportObservation.retract_support_source",
      "PNP.DirectWire.ClosedSupportObservation.tableAvailable_iff",
      "PNP.DirectWire.ClosedSupportProfile.profile_available",
      "PNP.DirectWire.ClosedSupportProfile.projected_available",
      "PNP.DirectWire.ClosedSupportProfile.projected_fieldValue",
      "PNP.DirectWire.ClosedSupportProfile.projected_tableAvailable",
      "PNP.DirectWire.ClosedSupportSquare.corner_available",
      "PNP.DirectWire.ClosedSupportSquare.corner_fieldValue",
      "PNP.DirectWire.ClosedSupportSquare.corner_profileMember",
      "PNP.DirectWire.ClosedSupportSquare.corners_fieldValue_equal",
      "PNP.DirectWire.ClosedSupportUnion.available_append",
      "PNP.DirectWire.ClosedSupportUnion.available_flatten",
      "PNP.DirectWire.ClosedSupportUnion.available_mono",
      "PNP.DirectWire.ClosedSupportUnion.mem_records_append",
      "PNP.DirectWire.ClosedSupportUnion.records_mono",
      "PNP.DirectWire.ClosedSupportUnion.retained_append",
      "PNP.DirectWire.ClosedSupportUnion.tableAvailable_append"
    ]
  }
};
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();
async function release0() {
  const [statusText, progressText] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('status/PROOF_PROGRESS.json'),
  ]);
  return {status: JSON.parse(statusText), progress: JSON.parse(progressText)};
}

test('M277 release preflight: package, exact workflow and status commands share one interface', async () => {
  const [pkg, surface, verifier, workflow, statusSource, statusText] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'), text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'), text0('pcc-formal-reconstruction-status0.mjs'),
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  ]);
  assert.equal(JSON.parse(pkg).scripts['audit:m277'], META.command);
  assert.ok(surface.includes("'audit:m277': '" + META.command + "'"));
  for (const file of META.testFiles) assert.ok(verifier.includes("'" + file + "'"), file);
  assert.ok(workflow.includes('run: npm run audit:m277'));
  const steps = workflow.split(/^      - name:/mu).filter(step =>
    step.includes('node scripts/check-lean-axioms.mjs ' + META.audit));
  assert.equal(steps.length, 1);
  const block = steps[0].split('        run: |\n')[1];
  assert.ok(block);
  assert.equal(block.trimEnd().split('\n').map(line => line.slice(10)).join('\n') + '\n', META.workflowCommands);
  const status = JSON.parse(statusText);
  for (const command of [
    'npm run audit:m277', 'node scripts/check-lean-axioms.mjs ' + META.audit,
    ...META.regressionCommands,
  ]) assert.ok(status.verificationCommands.includes(command), command);
  for (const field of Object.keys(META.statusFields))
    assert.equal(statusSource.split(field + ':').length - 1, 2, field);
});

test('M277 release: status pins the exact bounded claims and rejects every changed field', async () => {
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

test('M277 release: computed closed-support compatibility earns no unconditional checkpoint', async () => {
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

test('M277 release: every current summary and FAQ uses the canonical independent metrics', async () => {
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
      assert.ok(boundary?.includes('M277'));
      assert.ok(boundary.includes('global route coverage'));
    }
    if (['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
      'docs/proof_pipeline.md', 'docs/audit_questions.md'].includes(file)) {
      const region = text.split('<!-- M277-CURRENT-SUMMARY:BEGIN -->')[1]?.split('<!-- M277-CURRENT-SUMMARY:END -->')[0];
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
