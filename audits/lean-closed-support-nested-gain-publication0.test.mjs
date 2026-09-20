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
    "PNP.DirectWire.ClosedSupportNestedGain.ambient_output_absent",
    "1664f58363b58e2c4c8929e40f2943a2bc2b85ca27f6a03b0a2f49a3ffb14eeb",
    "PNP.NANDClosedSupportNestedCandidate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.append_positive",
    "897a005fbccaec759f9eba406f4ff023c11150fb6715f5d4fad198719d6f0503",
    "PNP.NANDClosedSupportNestedGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.available_from_large",
    "8c623a327f3cebc67b3513429cb47fb1c5a2cca2b26aaf5d88412dbe5e011e9b",
    "PNP.NANDClosedSupportNestedProfile",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.available_from_prefix",
    "b580a0417f4910e4ad3fc66a455a5ac588175b88f99907fadd9fd719982046dd",
    "PNP.NANDClosedSupportNestedOrigin",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.available_mono",
    "71aee9407786af19d679a0bcb683a2751fb12acdabe895c77e172c0f4b12454c",
    "PNP.NANDClosedSupportNestedSelection",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.available_to_large",
    "d49f4dd99d7988a662426b51825e658fb6e605d12f453365458937cc61ef0c32",
    "PNP.NANDClosedSupportNestedOrigin",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.boundarySource_value",
    "311f7c6d778c661574dfff22b51ef34ba4104baad08b83c5a895c6f6d7958ac9",
    "PNP.NANDClosedSupportNestedProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.difference_boundary_interface",
    "732dd2145705b32aa601738869239d79034dba4452f2e3cc76791e7b5896367c",
    "PNP.NANDClosedSupportNestedSelection",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.difference_gate_value",
    "00c86a0020703f9bf2b568e88aeb0c4155e33d11035f285d3aadc7a054e81821",
    "PNP.NANDClosedSupportNestedProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.difference_selected",
    "b412470a70a0afe5ec6830b64fbe4d5953b243e09f9ac7ef5d791dcba94340ac",
    "PNP.NANDClosedSupportNestedSelection",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.difference_selected_iff",
    "ca6e55b2bcc4c309cc7c97f69e1bff37ca7c30e209d4d8073b1e6aa6deba3a30",
    "PNP.NANDClosedSupportNestedSelection",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.extended_available",
    "4b6df1a65ce33609c3c5c0bb5b8d765ca682bd4f82635529dea24b69c261adb4",
    "PNP.NANDClosedSupportNestedProfile",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.extended_gateCount",
    "4ebda64f982971ba3807738fd34f40afc60da6ecfd0fbf294f5afb35664e0306",
    "PNP.NANDClosedSupportNestedCandidate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.extended_source_origin",
    "4c6ac839e7bffe961565584cdcb447c54fee221eab14dda60e106ad31d60b1e6",
    "PNP.NANDClosedSupportNestedOrigin",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.full_minimum_cost_balance",
    "60b0038366bc77325b182db70b379a1d4ccd6d939ce44304cd43ff08b568249c",
    "PNP.NANDClosedSupportNestedCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.full_minimum_extension_bound",
    "9e986a725b3196c616e8b44df6f7873d93cc88e4ee50661166454309ca1b8f07",
    "PNP.NANDClosedSupportNestedCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.full_minimum_le_support",
    "cfdff420135f7c2ceb28b016f8701b86a76056fe8e123f587b459ae90e0416d8",
    "PNP.NANDClosedSupportNestedCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.full_slack_le",
    "f4c721eab26422c24a1cf98041108a09b10df02628198e041ff363e924142ce2",
    "PNP.NANDClosedSupportNestedCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.included_of_seed_subset",
    "9bd26f7c83382fe22808178b4e55b6393b281a83fd6d9aeaf45ad6768a94ba5f",
    "PNP.NANDClosedSupportNestedGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.larger_interface_in_smaller",
    "dc775e41f2508444b469371f96a41ce729a8986e3b4070a07ba094d9313fba7e",
    "PNP.NANDClosedSupportNestedSelection",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.outputSource_value",
    "76ea15c3a5db333c53e611ef4921519338bfa78b0293c44eca9e73d5d74475a9",
    "PNP.NANDClosedSupportNestedCandidate",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.positive_iff_quotient_slack",
    "df0f381c225b4b093125e22d13b37f004fbc58c301adc0ef3673fa80db350e45",
    "PNP.NANDClosedSupportNestedCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.positive_mono",
    "77ad2d4afeb2095127ef63ec8909f0bf9320209e22f43197e31b8f657810216b",
    "PNP.NANDClosedSupportNestedCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.prefix_source_value",
    "0e49fcd7689996edf7458c32f9fbae1891e0a787e489afdf5ee29327d4847430",
    "PNP.NANDClosedSupportNestedProgram",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.quotient_minimum_cost_balance",
    "848c75e167d99f2a56e9f4916014c4d7a9a26648cf3dcb38e0b5ff8e34ca9efd",
    "PNP.NANDClosedSupportNestedCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.quotient_minimum_extension_bound",
    "c6b5541566f7748262cab20f1dfd954f5b3fd796d5909c3a75ab13e239a9def6",
    "PNP.NANDClosedSupportNestedCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.quotient_minimum_le_full",
    "97e24b411e2d21a573d584a2fc5fe23c84e2ea5ac863821ef950a5daa600035e",
    "PNP.NANDClosedSupportNestedCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.quotient_slack_le",
    "82e78dab58263c396357954e430425c86d63ac529fc0e93184a388ef7d09f1be",
    "PNP.NANDClosedSupportNestedCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.retained_mono",
    "5e47a8a5a86b175f94d9c9cb7713aeff1cf3df317087cf702de5d4ee20f4c5e9",
    "PNP.NANDClosedSupportNestedSelection",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.seed_full_cost_balance",
    "f701dc6f40d1a1942880d874b233be2fc5799faf9b6ee3f5d2447dd7d83f9fef",
    "PNP.NANDClosedSupportNestedGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.seed_full_slack_le",
    "2db48e318859984afa830b2d29d3df0bfe5df506f9618dee4a84fdef6a17007c",
    "PNP.NANDClosedSupportNestedGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.seed_positive",
    "f66fc5a639623f276d3ba47340ff3e8d61ed9138da139d234da24dda6c8613fb",
    "PNP.NANDClosedSupportNestedGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.seed_quotient_cost_balance",
    "5d074646b191df56413549534f015796b2dea82c8c9652751bdc14865bc17558",
    "PNP.NANDClosedSupportNestedGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.slack_decomposition",
    "97622a1b2b0c8459de7a60f5fd6f78ee45dcee5d81cf2a456897ae5d5b974ff6",
    "PNP.NANDClosedSupportNestedCost",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.support_count_decomposition",
    "feccbeff2848a7ab6a6a91e131908821466381c92dcec72ecd3895b0e025e165",
    "PNP.NANDClosedSupportNestedSelection",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportNestedGain.support_size_le",
    "3ab31589337c8aab441b8c7d94fd9b418594efca81d09110a507798ad60162fb",
    "PNP.NANDClosedSupportNestedSelection",
    [
      "Quot.sound",
      "propext"
    ]
  ]
];
const MILESTONE = {
  "classification": "formalized-foundation-only",
  "id": "computed-closed-support-nested-positivity",
  "nonClaim": "This compares already completed dependency-closed supports in the computational-wire-profile model. It does not prove preservation of an arbitrary raw witness's initial positivity during completion, transparency of every intermediate event, monotonicity of projection defect alone, complete manuscript profile semantics, discovery of a proper positive support, global routing or unconditional SaturatePositive, BCELReady or ZeroSlack. Reference minimization, matching and influence computations remain exhaustive; complete polynomial PCCMin runtime, output-size and certificate bounds are not proved. The eligible root theorem remains absent and P = NP is not proved.",
  "requiredTheorems": [
    "PNP.DirectWire.ClosedSupportNestedGain.ambient_output_absent",
    "PNP.DirectWire.ClosedSupportNestedGain.append_positive",
    "PNP.DirectWire.ClosedSupportNestedGain.available_from_large",
    "PNP.DirectWire.ClosedSupportNestedGain.available_from_prefix",
    "PNP.DirectWire.ClosedSupportNestedGain.available_mono",
    "PNP.DirectWire.ClosedSupportNestedGain.available_to_large",
    "PNP.DirectWire.ClosedSupportNestedGain.boundarySource_value",
    "PNP.DirectWire.ClosedSupportNestedGain.difference_boundary_interface",
    "PNP.DirectWire.ClosedSupportNestedGain.difference_gate_value",
    "PNP.DirectWire.ClosedSupportNestedGain.difference_selected",
    "PNP.DirectWire.ClosedSupportNestedGain.difference_selected_iff",
    "PNP.DirectWire.ClosedSupportNestedGain.extended_available",
    "PNP.DirectWire.ClosedSupportNestedGain.extended_gateCount",
    "PNP.DirectWire.ClosedSupportNestedGain.extended_source_origin",
    "PNP.DirectWire.ClosedSupportNestedGain.full_minimum_cost_balance",
    "PNP.DirectWire.ClosedSupportNestedGain.full_minimum_extension_bound",
    "PNP.DirectWire.ClosedSupportNestedGain.full_minimum_le_support",
    "PNP.DirectWire.ClosedSupportNestedGain.full_slack_le",
    "PNP.DirectWire.ClosedSupportNestedGain.included_of_seed_subset",
    "PNP.DirectWire.ClosedSupportNestedGain.larger_interface_in_smaller",
    "PNP.DirectWire.ClosedSupportNestedGain.outputSource_value",
    "PNP.DirectWire.ClosedSupportNestedGain.positive_iff_quotient_slack",
    "PNP.DirectWire.ClosedSupportNestedGain.positive_mono",
    "PNP.DirectWire.ClosedSupportNestedGain.prefix_source_value",
    "PNP.DirectWire.ClosedSupportNestedGain.quotient_minimum_cost_balance",
    "PNP.DirectWire.ClosedSupportNestedGain.quotient_minimum_extension_bound",
    "PNP.DirectWire.ClosedSupportNestedGain.quotient_minimum_le_full",
    "PNP.DirectWire.ClosedSupportNestedGain.quotient_slack_le",
    "PNP.DirectWire.ClosedSupportNestedGain.retained_mono",
    "PNP.DirectWire.ClosedSupportNestedGain.seed_full_cost_balance",
    "PNP.DirectWire.ClosedSupportNestedGain.seed_full_slack_le",
    "PNP.DirectWire.ClosedSupportNestedGain.seed_positive",
    "PNP.DirectWire.ClosedSupportNestedGain.seed_quotient_cost_balance",
    "PNP.DirectWire.ClosedSupportNestedGain.slack_decomposition",
    "PNP.DirectWire.ClosedSupportNestedGain.support_count_decomposition",
    "PNP.DirectWire.ClosedSupportNestedGain.support_size_le"
  ],
  "scope": "For arbitrary finite wire carriers, keep masks and two raw seed lists whose computed completed supports are physically nested, derive the exact gate difference and crossing bindings. Extend the actual full or quotient reference minimum inside the common ambient input domain, preserving the larger padded ordinary interface and exact required computational-field availability, including false values. The derived comparisons prove that either minimum grows by at most the added physical gates, that full slack and support size minus quotient minimum are monotone, and that positive full slack or projection defect remains positive in the completed larger support. Raw-seed inclusion derives the physical inclusion. No cost inequality, field-equality certificate or optimizer is supplied to the final theorem.",
  "title": "Computed nested-support cost and positivity transport"
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

test('M280 compiled interface: exact types, modules and axiom closures earn only the reviewed row', async () => {
  const {inventory, map, inventoryBytes, sourceClosure} = await sources0();
  assert.ok(canonical0(inventory).equals(inventoryBytes));
  const names = REVIEWED.map(row => row[0]);
  assert.equal(names.length, 36);
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

test('M280 compiled interface: weakening or supplying a conclusion cannot retain credit', async () => {
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
  // the full and quotient cost bounds and the raw-seed positivity boundary.
  for (const name of [
    'PNP.DirectWire.ClosedSupportNestedGain.full_minimum_cost_balance',
    'PNP.DirectWire.ClosedSupportNestedGain.quotient_minimum_cost_balance',
    'PNP.DirectWire.ClosedSupportNestedGain.seed_positive',
  ]) for (const kernelType of alternatives.get(name)) {
    const mutation = {...inventory, milestoneCandidates: inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), sourceClosure);
    assert.equal(result.milestones.find(row => row.id === MILESTONE.id).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
});

test('M280 compiled interface: missing evidence, added authority and widened scope reject', async () => {
  const {inventory, inventoryBytes, map, sourceClosure} = await sources0();
  const name = 'PNP.DirectWire.ClosedSupportNestedGain.quotient_minimum_cost_balance';
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
      ? {...row, [field]: 'Completed-support positivity automatically proves initial raw-witness completion, global route completeness, unconditional ZeroSlack and polynomial minimization.'} : row)};
    assert.throws(() => DeriveFormalPublication0(inventory, widened, inventoryBytes, sourceClosure),
      /map drifted from the reviewed specification/u);
  }
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256: {
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]: '0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, inventoryBytes, sourceClosure),
    /map drifted from the reviewed specification/u);
});

const META = {
  "coordinate": "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-20-280",
  "doc": "docs/lean_closed_support_nested_gain.md",
  "plan": "docs/plans/2026-09-20-computed-nested-support-positivity.md",
  "audit": "lean-audit/PNPClosedSupportNestedGainAxiomAudit.lean",
  "testFiles": [
    "audits/lean-closed-support-nested-gain0.test.mjs",
    "audits/lean-closed-support-nested-gain-publication0.test.mjs"
  ],
  "command": "node --test audits/lean-closed-support-nested-gain0.test.mjs audits/lean-closed-support-nested-gain-publication0.test.mjs",
  "workflowCommands": "set -euo pipefail\nnode scripts/check-lean-axioms.mjs lean-audit/PNPClosedSupportNestedGainAxiomAudit.lean\nlake env lean -DwarningAsError=true --run lean-regression/PNPClosedSupportNestedGain.lean\n",
  "publicationDecision": "Publication decision: defer. The result proves general preservation between computed completed supports, not the unresolved initial-completion boundary or a global saturation theorem. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.",
  "regressionCommands": [
    "lake env lean -DwarningAsError=true --run lean-regression/PNPClosedSupportNestedGain.lean"
  ],
  "statusFields": {
    "leanClosedSupportNestedGainFormalized": true,
    "leanClosedSupportNestedGainAxiomAuditPassed": true,
    "leanClosedSupportNestedGainAuditedDeclarationCount": 36,
    "leanClosedSupportNestedGainPhysicalDifferenceTheorem": "PNP.DirectWire.ClosedSupportNestedGain.support_count_decomposition",
    "leanClosedSupportNestedGainExactOrdinaryInterfaceTheorem": "PNP.DirectWire.ClosedSupportNestedGain.outputSource_value",
    "leanClosedSupportNestedGainExactFieldObservationTheorem": "PNP.DirectWire.ClosedSupportNestedGain.extended_available",
    "leanClosedSupportNestedGainFullMinimumCostBoundTheorem": "PNP.DirectWire.ClosedSupportNestedGain.full_minimum_cost_balance",
    "leanClosedSupportNestedGainQuotientMinimumCostBoundTheorem": "PNP.DirectWire.ClosedSupportNestedGain.quotient_minimum_cost_balance",
    "leanClosedSupportNestedGainFullSlackMonotonicityTheorem": "PNP.DirectWire.ClosedSupportNestedGain.full_slack_le",
    "leanClosedSupportNestedGainQuotientSlackMonotonicityTheorem": "PNP.DirectWire.ClosedSupportNestedGain.quotient_slack_le",
    "leanClosedSupportNestedGainPhysicalInclusionPositivityTheorem": "PNP.DirectWire.ClosedSupportNestedGain.positive_mono",
    "leanClosedSupportNestedGainRawSeedInclusionTheorem": "PNP.DirectWire.ClosedSupportNestedGain.included_of_seed_subset",
    "leanClosedSupportNestedGainRawSeedPositivityTheorem": "PNP.DirectWire.ClosedSupportNestedGain.seed_positive",
    "leanClosedSupportNestedGainArbitraryFiniteDimensionsCovered": true,
    "leanClosedSupportNestedGainSupportsDifferenceAndBindingsDerived": true,
    "leanClosedSupportNestedGainAmbientInputsRetained": true,
    "leanClosedSupportNestedGainExactFalseAndTrueFieldObservationsPreserved": true,
    "leanClosedSupportNestedGainFullAndQuotientComparisonsDerived": true,
    "leanClosedSupportNestedGainCallerSuppliedCostOrFieldEqualityRequired": false,
    "leanClosedSupportNestedGainInitialRawWitnessPositivityPreservationProved": false,
    "leanClosedSupportNestedGainProperPositiveSupportDiscoveryProved": false,
    "leanClosedSupportNestedGainCompleteManuscriptProfileGrammarProved": false,
    "leanClosedSupportNestedGainGlobalRouteCoverageProved": false,
    "leanClosedSupportNestedGainUnconditionalSaturatePositiveProved": false,
    "leanClosedSupportNestedGainUnconditionalBCELReadyProved": false,
    "leanClosedSupportNestedGainUnconditionalZeroSlackProved": false,
    "leanClosedSupportNestedGainExactPolynomialPCCMinProved": false,
    "leanClosedSupportNestedGainPolynomialRuntimeOutputAndCertificateBoundsProved": false,
    "leanClosedSupportNestedGainReferenceSearchRemainsExhaustive": true,
    "leanClosedSupportNestedGainRuntimeExecutionIsProofAuthority": false,
    "leanClosedSupportNestedGainScope": "arbitrary-finite-computed-completed-nested-support-derived-physical-difference-common-ambient-exact-ordinary-and-field-comparisons-full-and-quotient-cost-bounds-slack-and-combined-positivity-transport-no-initial-completion-manuscript-global-route-or-polynomial-claim",
    "leanClosedSupportNestedGainEveryIntermediateEventTransparencyProved": false,
    "leanClosedSupportNestedGainProjectionDefectAloneMonotonicityProved": false
  }
};
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();
async function release0() {
  const [statusText, progressText] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('status/PROOF_PROGRESS.json'),
  ]);
  return {status: JSON.parse(statusText), progress: JSON.parse(progressText)};
}

test('M280 release preflight: package, exact workflow and status commands share one interface', async () => {
  const [pkg, surface, verifier, workflow, statusSource, statusText] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'), text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'), text0('pcc-formal-reconstruction-status0.mjs'),
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  ]);
  assert.equal(JSON.parse(pkg).scripts['audit:m280'], META.command);
  assert.ok(surface.includes("'audit:m280': '" + META.command + "'"));
  for (const file of META.testFiles) assert.ok(verifier.includes("'" + file + "'"), file);
  assert.ok(workflow.includes('run: npm run audit:m280'));
  const steps = workflow.split(/^      - name:/mu).filter(step =>
    step.includes('node scripts/check-lean-axioms.mjs ' + META.audit));
  assert.equal(steps.length, 1);
  const block = steps[0].split('        run: |\n')[1];
  assert.ok(block);
  assert.equal(block.trimEnd().split('\n').map(line => line.slice(10)).join('\n') + '\n', META.workflowCommands);
  const status = JSON.parse(statusText);
  for (const command of [
    'npm run audit:m280', 'node scripts/check-lean-axioms.mjs ' + META.audit,
    ...META.regressionCommands,
  ]) assert.ok(status.verificationCommands.includes(command), command);
  for (const field of Object.keys(META.statusFields))
    assert.equal(statusSource.split(field + ':').length - 1, 2, field);
});

test('M280 release: status pins the exact bounded claims and rejects every changed field', async () => {
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

test('M280 release: computed nested-support positivity earns no unconditional checkpoint', async () => {
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

test('M280 release: every current summary and FAQ uses the canonical independent metrics', async () => {
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
      assert.ok(boundary?.includes('M280'));
      assert.ok(boundary.includes('global route coverage'));
    }
    if (['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
      'docs/proof_pipeline.md', 'docs/audit_questions.md'].includes(file)) {
      const region = text.split('<!-- M280-CURRENT-SUMMARY:BEGIN -->')[1]?.split('<!-- M280-CURRENT-SUMMARY:END -->')[0];
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
