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
    "PNP.DirectWire.ZeroCostExposure.Reference.toSource_eval",
    "18a33b06fc291b34cb074d9688282210f4c21a2708a0c4ab924f8dd985335bab",
    "PNP.NANDZeroCostExposure",
    []
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.extend_gateCount",
    "668882a9bee592090a6cec5f6f2c005121d7682ffb9daa2c5996f8c4d68dee42",
    "PNP.NANDZeroCostExposure",
    []
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.project_gateCount",
    "315753fe80872380b5de8fdca1acf5d866c46416b5e009aeeda8fcc0522f68ae",
    "PNP.NANDZeroCostExposure",
    []
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.extend_original",
    "f735eb48df9890020c841808534c329a72147c759c301d871f21553788157c1f",
    "PNP.NANDZeroCostExposure",
    []
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.extend_field",
    "e9c748c782da7b3b5800c4720fe32cc1fc2d064c15a57ad05109aa844805e6ec",
    "PNP.NANDZeroCostExposure",
    []
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.project_semantics",
    "5cb6faa5210bc24c6aeaabeb999b2a3927da180a0fbf7be9c07cd10b7119bf38",
    "PNP.NANDZeroCostExposure",
    []
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.extend_equivalent",
    "aa61a3a9de83ed22b63685b40b6252144097ae47ce12e57379c69b4e0ae4b74d",
    "PNP.NANDZeroCostExposure",
    []
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.project_equivalent",
    "1cb9297b40140397fc91a2ce4e347ec69b6a9fbe3eee1850d3c1e2a4ed029949",
    "PNP.NANDZeroCostExposure",
    []
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.project_extend_equivalent",
    "95ed0c663bfa2ce81f7763f170bab6e3ff26cf9ac9f0e5ce87ff7e8c084f1f41",
    "PNP.NANDZeroCostExposure",
    []
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.referenceMinimum_extend",
    "e70b4f616f47d81708dfa5b8531191b6942b71ba7c98a2512597416aa98fce55",
    "PNP.NANDZeroCostExposure",
    []
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.residualSlack_extend",
    "11201b09ca4b92710181dde08fb4fbded4bfb4287ad300290472eb7a090a2cdd",
    "PNP.NANDZeroCostExposure",
    []
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.compileLayout_success_iff",
    "0a80a0b6ab49c9d96899615f2bfea720c3c609b514fa2c2909fa7ab0aa892f25",
    "PNP.NANDZeroCostExposure",
    []
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.compileLayout_sound",
    "f62382d60b18888943122868a9e6fbe45f4ec8574fa71dfc4d159b8aba448f11",
    "PNP.NANDZeroCostExposure",
    []
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.recognize_success_iff",
    "7ab1cec4a649def55ddef0b39b50192de5909625fdc73ad330ed49c521f0fbb1",
    "PNP.NANDZeroCostExposure",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.recognize_isSome_iff",
    "e86ee10c9054890003e5c6b8e9ef7c53b0d1c4ade0eb1238011988ea4506b60d",
    "PNP.NANDZeroCostExposure",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.recognize_none_iff",
    "c1dd878bb5e68de979dd4a96d5f25d1aefc035ed17e2fcf7408b976de6d936ef",
    "PNP.NANDZeroCostExposure",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.recognize_gate_none_iff",
    "e877cd0cdd33656f9b03cfedab16e3416385a5fba0ff74e177ba6687471da183",
    "PNP.NANDZeroCostExposure",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.checkLayout_iff",
    "bb17be20fa7299b6c7eaf7ac27f95bae162d39fe6099a07d46e1eba7d69be8d4",
    "PNP.NANDZeroCostExposure",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.ZeroCostExposure.compileLayout_available_iff",
    "32b03086b0cb2a74ad96b70307963768468c8e43f39e4ac11fb0ea655e6febae",
    "PNP.NANDZeroCostExposure",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.WireCarrier.exposed_referenceMinimum_of_checkLayout",
    "df88d190913b101113192fbe892aef9f7109efaf2717c40433ca0833867d1dfa",
    "PNP.NANDWireCarrierZeroCostExposure",
    []
  ],
  [
    "PNP.DirectWire.WireCarrier.exposed_residualSlack_of_checkLayout",
    "2b0c5ec9087e8f70a023a82fbb930615453c26be4b9addefb45b3b1fb20cba95",
    "PNP.NANDWireCarrierZeroCostExposure",
    []
  ],
  [
    "PNP.DirectWire.WireCarrier.checked_exposure_preserves_problem",
    "2ed10a640a706bb5f1965313859d77148125723d97ea25fb117286ffce7f691c",
    "PNP.NANDWireCarrierZeroCostExposure",
    []
  ]
];
const MILESTONE = {
  "classification": "formalized-foundation-only",
  "id": "source-derived-zero-cost-exposure",
  "nonClaim": "This covers the literal input/constant/old-output alias class, not every semantically free exposure or arbitrary hidden internal wire. Refusal proves neither semantic impossibility nor a Package E gain or route. Adding no physical gates need not preserve the semantic minimum, and unique physical ownership or an extra recorded charge does not force an equal minimum increase. The concrete counterexamples are regression and obstruction evidence, not new global progress. The existing fresh-independent-input materializer theorem is reused, not re-awarded. Full manuscript profiles, positive-cost transparency for arbitrary materializers, terminal-family derivation, global route coverage, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin and complete encoded-input polynomial runtime, output and certificate bounds remain open. No fixed weighted checkpoint or global proof gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.",
  "requiredTheorems": [
    "PNP.DirectWire.ZeroCostExposure.Reference.toSource_eval",
    "PNP.DirectWire.ZeroCostExposure.extend_gateCount",
    "PNP.DirectWire.ZeroCostExposure.project_gateCount",
    "PNP.DirectWire.ZeroCostExposure.extend_original",
    "PNP.DirectWire.ZeroCostExposure.extend_field",
    "PNP.DirectWire.ZeroCostExposure.project_semantics",
    "PNP.DirectWire.ZeroCostExposure.extend_equivalent",
    "PNP.DirectWire.ZeroCostExposure.project_equivalent",
    "PNP.DirectWire.ZeroCostExposure.project_extend_equivalent",
    "PNP.DirectWire.ZeroCostExposure.referenceMinimum_extend",
    "PNP.DirectWire.ZeroCostExposure.residualSlack_extend",
    "PNP.DirectWire.ZeroCostExposure.compileLayout_success_iff",
    "PNP.DirectWire.ZeroCostExposure.compileLayout_sound",
    "PNP.DirectWire.ZeroCostExposure.recognize_success_iff",
    "PNP.DirectWire.ZeroCostExposure.recognize_isSome_iff",
    "PNP.DirectWire.ZeroCostExposure.recognize_none_iff",
    "PNP.DirectWire.ZeroCostExposure.recognize_gate_none_iff",
    "PNP.DirectWire.ZeroCostExposure.checkLayout_iff",
    "PNP.DirectWire.ZeroCostExposure.compileLayout_available_iff",
    "PNP.DirectWire.WireCarrier.exposed_referenceMinimum_of_checkLayout",
    "PNP.DirectWire.WireCarrier.exposed_residualSlack_of_checkLayout",
    "PNP.DirectWire.WireCarrier.checked_exposure_preserves_problem"
  ],
  "scope": "For arbitrary finite input, ordinary-output and extra-field widths, a literal output extension adds only input, constant or existing-output aliases and a literal projection recovers the original outputs without allocating gates. Both constructions transfer arbitrary equivalent realizations, proving exact equality of the semantic reference minimum and residual slack. A source-derived recognizer scans the actual output wires; a gate field is accepted exactly when an ordinary output names that same wire. The tuple compiler derives every alias and accepts exactly when all requested fields have such literal references. The actual WireCarrier exposure therefore preserves physical gate count, semantic minimum and slack whenever this executable source check accepts. Constructors and recognition do not enumerate truth tables or minimum implementations and do not receive an observer, semantic minimum, route or correctness certificate from the caller.",
  "title": "Source-derived zero-cost alias exposure"
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

test('M273 compiled interface: exact types, modules and axiom closures earn only the reviewed row', async () => {
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

test('M273 compiled interface: weakening or supplying a conclusion cannot retain credit', async () => {
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
  // minimum preservation, exact refusal and actual carrier exposure.
  for (const name of [
    'PNP.DirectWire.ZeroCostExposure.referenceMinimum_extend',
    'PNP.DirectWire.ZeroCostExposure.recognize_gate_none_iff',
    'PNP.DirectWire.WireCarrier.checked_exposure_preserves_problem',
  ]) for (const kernelType of alternatives.get(name)) {
    const mutation = {...inventory, milestoneCandidates: inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), sourceClosure);
    assert.equal(result.milestones.find(row => row.id === MILESTONE.id).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
});

test('M273 compiled interface: missing evidence, added authority and widened scope reject', async () => {
  const {inventory, inventoryBytes, map, sourceClosure} = await sources0();
  const name = 'PNP.DirectWire.ZeroCostExposure.recognize_gate_none_iff';
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
      ? {...row, [field]: 'Every hidden exposure is a zero-cost retract and establishes unconditional global ZeroSlack.'} : row)};
    assert.throws(() => DeriveFormalPublication0(inventory, widened, inventoryBytes, sourceClosure),
      /map drifted from the reviewed specification/u);
  }
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256: {
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]: '0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, inventoryBytes, sourceClosure),
    /map drifted from the reviewed specification/u);
});

const META = {
  "coordinate": "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-18-273",
  "statusFields": {
    "leanSourceDerivedZeroCostExposureFormalized": true,
    "leanSourceDerivedZeroCostExposureAxiomAuditPassed": true,
    "leanSourceDerivedZeroCostExposureAuditedDeclarationCount": 22,
    "leanSourceDerivedZeroCostExposureMinimumTheorem": "PNP.DirectWire.ZeroCostExposure.referenceMinimum_extend",
    "leanSourceDerivedZeroCostExposureSlackTheorem": "PNP.DirectWire.ZeroCostExposure.residualSlack_extend",
    "leanSourceDerivedZeroCostExposureRecognitionTheorem": "PNP.DirectWire.ZeroCostExposure.recognize_success_iff",
    "leanSourceDerivedZeroCostExposureGateRefusalTheorem": "PNP.DirectWire.ZeroCostExposure.recognize_gate_none_iff",
    "leanSourceDerivedZeroCostExposureTupleAcceptanceTheorem": "PNP.DirectWire.ZeroCostExposure.compileLayout_available_iff",
    "leanSourceDerivedZeroCostExposureCarrierMinimumTheorem": "PNP.DirectWire.WireCarrier.exposed_referenceMinimum_of_checkLayout",
    "leanSourceDerivedZeroCostExposureCarrierSlackTheorem": "PNP.DirectWire.WireCarrier.exposed_residualSlack_of_checkLayout",
    "leanSourceDerivedZeroCostExposureCarrierPreservationTheorem": "PNP.DirectWire.WireCarrier.checked_exposure_preserves_problem",
    "leanSourceDerivedZeroCostExposureArbitraryFiniteDimensionsCovered": true,
    "leanSourceDerivedZeroCostExposureLiteralInputConstantAndOldOutputAliasesCovered": true,
    "leanSourceDerivedZeroCostExposureBothRealizationTransfersProved": true,
    "leanSourceDerivedZeroCostExposureActualSourceRecognitionComputed": true,
    "leanSourceDerivedZeroCostExposureEveryRequestedFieldChecked": true,
    "leanSourceDerivedZeroCostExposureActualCarrierMinimumAndSlackPreserved": true,
    "leanSourceDerivedZeroCostExposureCallerSuppliedObserverMinimumOrCorrectnessRequired": false,
    "leanSourceDerivedZeroCostExposureConstructorOrRecognizerEnumeratesSemanticMinima": false,
    "leanSourceDerivedZeroCostExposureAllSemanticallyFreeExposuresRecognized": false,
    "leanSourceDerivedZeroCostExposureRefusalImpliesPackageERoute": false,
    "leanSourceDerivedZeroCostExposureNoPhysicalGateIncreaseAloneImpliesZeroCost": false,
    "leanSourceDerivedZeroCostExposureUniquePhysicalChargeAloneForcesMinimumIncrease": false,
    "leanSourceDerivedZeroCostExposureArbitraryPositiveCostTransparencyProved": false,
    "leanSourceDerivedZeroCostExposureFullManuscriptProfileSemanticsProved": false,
    "leanSourceDerivedZeroCostExposureTerminalFamiliesDerived": false,
    "leanSourceDerivedZeroCostExposureGlobalRouteCoverageProved": false,
    "leanSourceDerivedZeroCostExposureUnconditionalSaturatePositiveProved": false,
    "leanSourceDerivedZeroCostExposureUnconditionalBCELReadyProved": false,
    "leanSourceDerivedZeroCostExposureUnconditionalZeroSlackProved": false,
    "leanSourceDerivedZeroCostExposureExactGeneralPCCMinProved": false,
    "leanSourceDerivedZeroCostExposurePolynomialRuntimeOutputAndCertificateBoundsProved": false,
    "leanSourceDerivedZeroCostExposureScope": "arbitrary-finite-literal-input-constant-old-output-alias-extension-projection-exact-minimum-slack-source-derived-tuple-recognition-actual-carrier-no-semantic-completeness-positive-cost-global-route-or-polynomial-claim"
  },
  "command": "node --test audits/lean-zero-cost-exposure0.test.mjs audits/lean-zero-cost-exposure-publication0.test.mjs",
  "testFiles": [
    "audits/lean-zero-cost-exposure0.test.mjs",
    "audits/lean-zero-cost-exposure-publication0.test.mjs"
  ],
  "audit": "lean-audit/PNPZeroCostExposureAxiomAudit.lean",
  "parts": [
    "ZeroCostExposure"
  ],
  "workflowCommands": "set -euo pipefail\nnode scripts/check-lean-axioms.mjs lean-audit/PNPZeroCostExposureAxiomAudit.lean\nlake env lean -DwarningAsError=true lean-regression/PNPZeroCostExposure.lean\n",
  "publicationDecision": "Publication decision: defer. This establishes a source-derived literal-alias branch with exact minimum and slack preservation, not all semantic exposure, full manuscript profiles or global route coverage. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.",
  "rationale": "M273 constructs and checks the literal input/constant/old-output alias branch of zero-cost exposure for arbitrary finite circuits. Two-way transfer of arbitrary realizations proves exact semantic-minimum and slack preservation, and the source-derived tuple recognizer connects that guarantee to actual computational carrier fields. Refusal is exact only for the syntactic alias class and does not provide a positive route. Kernel-checked counterexamples prevent equating zero new gates with zero semantic cost or unique physical charging with a forced minimum increase. Existing independent-materializer work is reused. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged. Full profiles, arbitrary materializers, global routes, unconditional residual theorems and polynomial bounds remain open.",
  "doc": "docs/lean_zero_cost_exposure.md",
  "plan": "docs/plans/2026-09-18-source-derived-zero-cost-exposure.md"
};
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();
async function release0() {
  const [statusText, progressText] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('status/PROOF_PROGRESS.json'),
  ]);
  return {status: JSON.parse(statusText), progress: JSON.parse(progressText)};
}

test('M273 release preflight: package, exact workflow and status commands share one interface', async () => {
  const [pkg, surface, verifier, workflow, statusSource, statusText] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'), text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'), text0('pcc-formal-reconstruction-status0.mjs'),
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  ]);
  assert.equal(JSON.parse(pkg).scripts['audit:m273'], META.command);
  assert.ok(surface.includes("'audit:m273': '" + META.command + "'"));
  for (const file of META.testFiles) assert.ok(verifier.includes("'" + file + "'"), file);
  assert.ok(workflow.includes('run: npm run audit:m273'));
  const steps = workflow.split(/^      - name:/mu).filter(step =>
    step.includes('node scripts/check-lean-axioms.mjs ' + META.audit));
  assert.equal(steps.length, 1);
  const block = steps[0].split('        run: |\n')[1];
  assert.ok(block);
  assert.equal(block.trimEnd().split('\n').map(line => line.slice(10)).join('\n') + '\n', META.workflowCommands);
  const status = JSON.parse(statusText);
  for (const command of [
    'npm run audit:m273', 'node scripts/check-lean-axioms.mjs ' + META.audit,
    ...META.parts.map(part => 'lake env lean -DwarningAsError=true lean-regression/PNP' + part + '.lean'),
  ]) assert.ok(status.verificationCommands.includes(command), command);
  for (const field of Object.keys(META.statusFields))
    assert.equal(statusSource.split(field + ':').length - 1, 2, field);
});

test('M273 release: status pins the exact bounded claims and rejects every changed field', async () => {
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

test('M273 release: literal-alias exposure earns no unconditional checkpoint', async () => {
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

test('M273 release: every current summary and FAQ uses the canonical independent metrics', async () => {
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
      assert.ok(boundary?.includes('M273'));
      assert.ok(boundary.includes('global route coverage'));
    }
    if (['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
      'docs/proof_pipeline.md', 'docs/audit_questions.md'].includes(file)) {
      const region = text.split('<!-- M273-CURRENT-SUMMARY:BEGIN -->')[1]?.split('<!-- M273-CURRENT-SUMMARY:END -->')[0];
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
