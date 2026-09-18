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
    "PNP.DirectWire.WireProfile.mask_implementation",
    "a5e99322915e0ca88895287bf073d302b2b29df82ebdcdf7a84982461d861a05",
    "PNP.NANDWireProfileExposure",
    []
  ],
  [
    "PNP.DirectWire.WireProfile.mask_fieldValue",
    "02bd6191dfb811c25056a049e8e86fa16ada2242ad981e9d302c3be1da8df54e",
    "PNP.NANDWireProfileExposure",
    []
  ],
  [
    "PNP.DirectWire.WireProfile.full_iff",
    "5d698934e56bdcf88b7dcf60eafac3eab9e7db32ea6bf3f9d38f5fa1ff31ff8f",
    "PNP.NANDWireProfileExposure",
    []
  ],
  [
    "PNP.DirectWire.WireProfile.quotient_iff",
    "fccf2f775e403e158d93d6139963ae4158be4993b4d8f377e840eb0733e2d928",
    "PNP.NANDWireProfileExposure",
    []
  ],
  [
    "PNP.DirectWire.WireProfile.full_to_quotient",
    "48950dc3e4b866af61a3e6444bd32cbceae0a46c0957f77cb4fa5e9d54f0f989",
    "PNP.NANDWireProfileExposure",
    []
  ],
  [
    "PNP.DirectWire.WireProfile.full_lift_iff",
    "aaa96b36a3742f3fbf460ac282c6dcea4aa6b136e03c129162f243d303ba25d5",
    "PNP.NANDWireProfileExposure",
    []
  ],
  [
    "PNP.DirectWire.WireProfile.fullWitness_gateCount",
    "099dc96ab5aaa8b8f55d148aae45bf022e4a6d4bfa2d72183f93cd91edf7e188",
    "PNP.NANDWireProfileExposure",
    []
  ],
  [
    "PNP.DirectWire.WireProfile.fullWitness_matches",
    "b7afccdcdb9354ae51800ae53cd96073283c7994b327a4b6a28618dc7c8b2969",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.fullMinimum_le_physical",
    "0d3ec56776d0c9c8f43c66d71bf0209cf5080d34347aca3d0eedeaae9bd975f2",
    "PNP.NANDWireProfileExposure",
    []
  ],
  [
    "PNP.DirectWire.WireProfile.quotientMinimum_le_full",
    "bc1adee3880f8b44318713263f3b979a747c83c909a77a5b9c58357d010b54d0",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.quotientWitness_gateCount",
    "652ff627431bbb569f5e42ca2d542dd1424e11a522427ae3040d546825e8e7ed",
    "PNP.NANDWireProfileExposure",
    []
  ],
  [
    "PNP.DirectWire.WireProfile.quotientWitness_matches",
    "eebcc528071e48f3c185e9e70535081af327c58a3294bc6ad14583cfbf39ddad",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.quotient_candidate_lower_bound",
    "834f4fc9ffa0ba6d873d5ddd4bbad11e4f3a7f93a5ae9bd0cea1670a65f827c7",
    "PNP.NANDWireProfileExposure",
    []
  ],
  [
    "PNP.DirectWire.WireProfile.full_candidate_lower_bound",
    "2b3886e4849ac17ef8565b28f1bd0907293a8a46dd7a922f14689cd3a4d63348",
    "PNP.NANDWireProfileExposure",
    []
  ],
  [
    "PNP.DirectWire.WireProfile.fullSlack_add_projectionDefect",
    "19fe9cf0cbb7a6364face3057ca7d7007fb703836df32eb59ad9efe7b6a7e132",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.exposure_balance",
    "f687b4f65e9d51beb3024edb123c1ff2204fed3b8adbd26df53cc12ffca3a439",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.exposure_preserves_positive_alternative",
    "c54845f73cc4c477d4335448949eafb39c53c853ce1da97b9d522d634a50ce32",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.quotient_minimum_cannot_lift_of_positive_defect",
    "edb1bb6409b16c4bc54f0b3ef32d76a35ccf551487d39a41642d7973fee1f43c",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.exposure_loss_has_unliftable_quotient_witness",
    "7f3d9d4c895acc696bc99ac5648a6c49e5ab20c9f19553031d12c27fe53b57ed",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.allGateFields_value",
    "54b34f81e456e694484f290a71c634f4a45b016993e8208744b7a096b59b27b9",
    "PNP.NANDWireProfileExposure",
    []
  ],
  [
    "PNP.DirectWire.WireProfile.allGateFields_positive_alternative",
    "e9281676603a9b4eb5d0739ca3bf71e44a0fe8623f6f7d8ba4015ae0c41be575",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.quotientMinimum_forget_all",
    "edd5a27a002e25340fe7ca068bd95007b60d9e4c5a703d0034b0e1e9a26ded26",
    "PNP.NANDWireProfileExposure",
    []
  ],
  [
    "PNP.DirectWire.WireProfile.source_slack_balance",
    "ff2ba7a5fb4b772b4ee011f7ef07f7170de32acbdf025fb7e342d7934c8fad12",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.source_positive_alternative",
    "285b87162a99076953ebe58aeeb633e9feba45114f232ad4b00d6202411714c6",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.mask_absorb_equivalent",
    "2cf73c7192313cbdbd76735b7b77042b777f74f8b5e649976c8069093a876e46",
    "PNP.NANDWireProfileExposure",
    []
  ],
  [
    "PNP.DirectWire.WireProfile.quotientMinimum_mask_active",
    "b79c9065239510e20587a22cb40b765d2201744deb19f5607789d1fa44858a23",
    "PNP.NANDWireProfileExposure",
    []
  ],
  [
    "PNP.DirectWire.WireProfile.fullMinimum_mask_mono",
    "43029536c1d99c3cfec5ca745449d974a430bf361fefd2b93e2ffceb236e1576",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.exposure_states_balance",
    "e654e8bd8a28e49091b5bb146f72a4f9268c497b82839c77a542aa3a3b4bbae6",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.exposure_moves_exact_slack_to_defect",
    "7b4fbd1ffde330cac1106dfce09549e1c44646f640e9d9c3f1cbf132a20c61e3",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.normalize_fullEquivalent",
    "aae04d9117416a78c56fb98de5f4181f7fe92fd593051bc841c2e02f7161b78b",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.fullMinimum_normalize",
    "7ab5397d66beaca752e9f08856b3b8746e2bcffcc9637d923abde103af56fe5e",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.quotientMinimum_normalize",
    "019da02696fa365128110df9065f50101439921957a98b46c6397b9f34d67045",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.splice_fullEquivalent",
    "2c6287494db7ca5d8bdfb46f0aa27f842ac5c7fd2927f8c687ca9ced370d77d1",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.fullMinimum_splice",
    "f1ca47b85073fa3b09587f992d21cb51635fdf7831d9536bbea7f4b9be28b564",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.WireProfile.quotientMinimum_splice",
    "7fc79932a7744ce1ff140a2c4df84342b54cd79fae1b4a3380a78b73da3b2634",
    "PNP.NANDWireProfileExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ]
];
const MILESTONE = {
  "classification": "formalized-foundation-only",
  "id": "wire-profile-exposure-balance",
  "nonClaim": "This is a proposed reconstruction of computational profile comparison, not the complete manuscript ten-role grammar or a derived governed terminal family. Ordinary outgoing Boolean interface wires cannot be forgotten. The all-gate field tuple is source-derived but is not asserted to be a canonical terminal profile. Conservation of full slack plus projection defect proves neither forced-cost transparency nor a Package E route, positive-slack activation, global rank decrease or route coverage. A quotient witness cannot be used as a full replacement without restoring every omitted field. Checked splicing still requires an equivalent open replacement and successful compilation; global discovery is not proved. Reference minima and attained witnesses use exhaustive finite minimization, not a polynomial algorithm. Unconditional SaturatePositive, BCELReady and ZeroSlack, exact polynomial PCCMin, encoded-input runtime, output and certificate bounds, deterministic CNFSAT in P and the eligible root remain open. No fixed weighted checkpoint or global proof gate closes, and P = NP is not proved.",
  "requiredTheorems": [
    "PNP.DirectWire.WireProfile.mask_implementation",
    "PNP.DirectWire.WireProfile.mask_fieldValue",
    "PNP.DirectWire.WireProfile.full_iff",
    "PNP.DirectWire.WireProfile.quotient_iff",
    "PNP.DirectWire.WireProfile.full_to_quotient",
    "PNP.DirectWire.WireProfile.full_lift_iff",
    "PNP.DirectWire.WireProfile.fullWitness_gateCount",
    "PNP.DirectWire.WireProfile.fullWitness_matches",
    "PNP.DirectWire.WireProfile.fullMinimum_le_physical",
    "PNP.DirectWire.WireProfile.quotientMinimum_le_full",
    "PNP.DirectWire.WireProfile.quotientWitness_gateCount",
    "PNP.DirectWire.WireProfile.quotientWitness_matches",
    "PNP.DirectWire.WireProfile.quotient_candidate_lower_bound",
    "PNP.DirectWire.WireProfile.full_candidate_lower_bound",
    "PNP.DirectWire.WireProfile.fullSlack_add_projectionDefect",
    "PNP.DirectWire.WireProfile.exposure_balance",
    "PNP.DirectWire.WireProfile.exposure_preserves_positive_alternative",
    "PNP.DirectWire.WireProfile.quotient_minimum_cannot_lift_of_positive_defect",
    "PNP.DirectWire.WireProfile.exposure_loss_has_unliftable_quotient_witness",
    "PNP.DirectWire.WireProfile.allGateFields_value",
    "PNP.DirectWire.WireProfile.allGateFields_positive_alternative",
    "PNP.DirectWire.WireProfile.quotientMinimum_forget_all",
    "PNP.DirectWire.WireProfile.source_slack_balance",
    "PNP.DirectWire.WireProfile.source_positive_alternative",
    "PNP.DirectWire.WireProfile.mask_absorb_equivalent",
    "PNP.DirectWire.WireProfile.quotientMinimum_mask_active",
    "PNP.DirectWire.WireProfile.fullMinimum_mask_mono",
    "PNP.DirectWire.WireProfile.exposure_states_balance",
    "PNP.DirectWire.WireProfile.exposure_moves_exact_slack_to_defect",
    "PNP.DirectWire.WireProfile.normalize_fullEquivalent",
    "PNP.DirectWire.WireProfile.fullMinimum_normalize",
    "PNP.DirectWire.WireProfile.quotientMinimum_normalize",
    "PNP.DirectWire.WireProfile.splice_fullEquivalent",
    "PNP.DirectWire.WireProfile.fullMinimum_splice",
    "PNP.DirectWire.WireProfile.quotientMinimum_splice"
  ],
  "scope": "For arbitrary finite input, ordinary-output and computational-field widths, full comparison preserves the ordinary Boolean outputs and every actual wire-backed field at every input valuation. Quotient comparison masks only selected profile constraints and still preserves every ordinary output. Exact characterization, full-lift, attained-witness and universal lower-bound theorems establish quotient minimum <= full minimum <= physical gate count. Full slack plus projection defect equals physical size minus quotient minimum. Exposure masks that both retain a fixed comparison mask preserve that quotient minimum and the combined measure; nested masks transfer exactly the lost full slack into projection defect. Loss of positive full slack to zero yields an attained quotient witness with a strict deficit that cannot be used as a full witness. Forgetting all profile constraints recovers the ordinary semantic minimum. The actual all-gate source tuple, checked normalization and checked splicing connect this model to computational wire carriers without a supplied observer, semantic minimum or correctness certificate for the comparison model.",
  "title": "Wire-backed computational profiles and exposure balance"
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

test('M274 compiled interface: exact types, modules and axiom closures earn only the reviewed row', async () => {
  const {inventory, map, inventoryBytes, sourceClosure} = await sources0();
  assert.ok(canonical0(inventory).equals(inventoryBytes));
  const names = REVIEWED.map(row => row[0]);
  assert.equal(names.length, 35);
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

test('M274 compiled interface: weakening or supplying a conclusion cannot retain credit', async () => {
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
  // full restoration, exact exposure transfer and checked splicing.
  for (const name of [
    'PNP.DirectWire.WireProfile.full_lift_iff',
    'PNP.DirectWire.WireProfile.exposure_moves_exact_slack_to_defect',
    'PNP.DirectWire.WireProfile.splice_fullEquivalent',
  ]) for (const kernelType of alternatives.get(name)) {
    const mutation = {...inventory, milestoneCandidates: inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), sourceClosure);
    assert.equal(result.milestones.find(row => row.id === MILESTONE.id).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
});

test('M274 compiled interface: missing evidence, added authority and widened scope reject', async () => {
  const {inventory, inventoryBytes, map, sourceClosure} = await sources0();
  const name = 'PNP.DirectWire.WireProfile.exposure_moves_exact_slack_to_defect';
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
      ? {...row, [field]: 'Ordinary outputs may be forgotten and every quotient witness establishes unconditional global ZeroSlack.'} : row)};
    assert.throws(() => DeriveFormalPublication0(inventory, widened, inventoryBytes, sourceClosure),
      /map drifted from the reviewed specification/u);
  }
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256: {
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]: '0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, inventoryBytes, sourceClosure),
    /map drifted from the reviewed specification/u);
});

const META = {
  "coordinate": "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-19-274",
  "statusFields": {
    "leanWireProfileExposureFormalized": true,
    "leanWireProfileExposureAxiomAuditPassed": true,
    "leanWireProfileExposureAuditedDeclarationCount": 35,
    "leanWireProfileExposureFullComparisonTheorem": "PNP.DirectWire.WireProfile.full_iff",
    "leanWireProfileExposureQuotientComparisonTheorem": "PNP.DirectWire.WireProfile.quotient_iff",
    "leanWireProfileExposureFullLiftTheorem": "PNP.DirectWire.WireProfile.full_lift_iff",
    "leanWireProfileExposureAttainedQuotientWitnessTheorem": "PNP.DirectWire.WireProfile.quotientWitness_matches",
    "leanWireProfileExposureExposureBalanceTheorem": "PNP.DirectWire.WireProfile.exposure_states_balance",
    "leanWireProfileExposureExactTransferTheorem": "PNP.DirectWire.WireProfile.exposure_moves_exact_slack_to_defect",
    "leanWireProfileExposureNonLiftabilityTheorem": "PNP.DirectWire.WireProfile.exposure_loss_has_unliftable_quotient_witness",
    "leanWireProfileExposureOrdinarySlackTheorem": "PNP.DirectWire.WireProfile.source_slack_balance",
    "leanWireProfileExposureNormalizationTheorem": "PNP.DirectWire.WireProfile.normalize_fullEquivalent",
    "leanWireProfileExposureCheckedSpliceTheorem": "PNP.DirectWire.WireProfile.splice_fullEquivalent",
    "leanWireProfileExposureArbitraryFiniteDimensionsCovered": true,
    "leanWireProfileExposureOrdinaryOutputsPreservedInBothModes": true,
    "leanWireProfileExposureActualWireValuesAtAllValuations": true,
    "leanWireProfileExposureMinimaAndAttainedWitnessesDerived": true,
    "leanWireProfileExposureExposureTransfersSlackToDefect": true,
    "leanWireProfileExposureCallerSuppliedObserverOrMinimumRequired": false,
    "leanWireProfileExposureQuotientWitnessAloneIsFullReplacement": false,
    "leanWireProfileExposureAllGateFieldsAreCanonicalTerminalFamily": false,
    "leanWireProfileExposureCompleteManuscriptProfileGrammarProved": false,
    "leanWireProfileExposureForcedCostTransparencyProved": false,
    "leanWireProfileExposureCompletePackageEOrGlobalRoutesProved": false,
    "leanWireProfileExposureTerminalFamiliesDerived": false,
    "leanWireProfileExposureUnconditionalSaturatePositiveProved": false,
    "leanWireProfileExposureUnconditionalBCELReadyProved": false,
    "leanWireProfileExposureUnconditionalZeroSlackProved": false,
    "leanWireProfileExposureExactPolynomialPCCMinProved": false,
    "leanWireProfileExposurePolynomialRuntimeOutputAndCertificateBoundsProved": false,
    "leanWireProfileExposureReferenceMinimizationIsExhaustive": true,
    "leanWireProfileExposureScope": "arbitrary-finite-actual-wire-profile-values-all-input-valuations-mandatory-ordinary-outputs-full-quotient-lift-attained-minima-exact-exposure-slack-defect-transfer-checked-normalization-splice-no-full-manuscript-global-route-or-polynomial-claim"
  },
  "command": "node --test audits/lean-wire-profile-exposure0.test.mjs audits/lean-wire-profile-exposure-publication0.test.mjs",
  "testFiles": [
    "audits/lean-wire-profile-exposure0.test.mjs",
    "audits/lean-wire-profile-exposure-publication0.test.mjs"
  ],
  "audit": "lean-audit/PNPWireProfileExposureAxiomAudit.lean",
  "parts": [
    "WireProfileExposure"
  ],
  "workflowCommands": "set -euo pipefail\nnode scripts/check-lean-axioms.mjs lean-audit/PNPWireProfileExposureAxiomAudit.lean\nlake env lean -DwarningAsError=true lean-regression/PNPWireProfileExposure.lean\n",
  "publicationDecision": "Publication decision: defer. This establishes a general computational profile-comparison and exposure-balance component, not full manuscript profiles, terminal-derived families or global route coverage. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.",
  "rationale": "M274 derives full and quotient computational profile semantics from actual wire sources at every valuation, with mandatory ordinary outputs in both modes. Constructed exhaustive minima and attained witnesses prove the exact full-lift boundary, universal cost bounds and conservation of full slack plus projection defect. Nested exposure masks transfer exactly the lost full slack to defect; an attained deficient quotient witness cannot silently become full replacement evidence. Source-derived all-gate fields and checked normalization and splicing connect the model to actual carriers. This closes a general computational comparison/accounting edge, not the full manuscript grammar, canonical terminal-family construction, forced-cost transparency, Package E, global routing or polynomial minimization. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.",
  "doc": "docs/lean_wire_profile_exposure.md",
  "plan": "docs/plans/2026-09-19-wire-profile-exposure.md"
};
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();
async function release0() {
  const [statusText, progressText] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('status/PROOF_PROGRESS.json'),
  ]);
  return {status: JSON.parse(statusText), progress: JSON.parse(progressText)};
}

test('M274 release preflight: package, exact workflow and status commands share one interface', async () => {
  const [pkg, surface, verifier, workflow, statusSource, statusText] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'), text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'), text0('pcc-formal-reconstruction-status0.mjs'),
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  ]);
  assert.equal(JSON.parse(pkg).scripts['audit:m274'], META.command);
  assert.ok(surface.includes("'audit:m274': '" + META.command + "'"));
  for (const file of META.testFiles) assert.ok(verifier.includes("'" + file + "'"), file);
  assert.ok(workflow.includes('run: npm run audit:m274'));
  const steps = workflow.split(/^      - name:/mu).filter(step =>
    step.includes('node scripts/check-lean-axioms.mjs ' + META.audit));
  assert.equal(steps.length, 1);
  const block = steps[0].split('        run: |\n')[1];
  assert.ok(block);
  assert.equal(block.trimEnd().split('\n').map(line => line.slice(10)).join('\n') + '\n', META.workflowCommands);
  const status = JSON.parse(statusText);
  for (const command of [
    'npm run audit:m274', 'node scripts/check-lean-axioms.mjs ' + META.audit,
    ...META.parts.map(part => 'lake env lean -DwarningAsError=true lean-regression/PNP' + part + '.lean'),
  ]) assert.ok(status.verificationCommands.includes(command), command);
  for (const field of Object.keys(META.statusFields))
    assert.equal(statusSource.split(field + ':').length - 1, 2, field);
});

test('M274 release: status pins the exact bounded claims and rejects every changed field', async () => {
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

test('M274 release: computational profile exposure earns no unconditional checkpoint', async () => {
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

test('M274 release: every current summary and FAQ uses the canonical independent metrics', async () => {
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
      assert.ok(boundary?.includes('M274'));
      assert.ok(boundary.includes('global route coverage'));
    }
    if (['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
      'docs/proof_pipeline.md', 'docs/audit_questions.md'].includes(file)) {
      const region = text.split('<!-- M274-CURRENT-SUMMARY:BEGIN -->')[1]?.split('<!-- M274-CURRENT-SUMMARY:END -->')[0];
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
