import assert from 'node:assert/strict';
import { mkdtemp, readFile, rm, symlink } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  CollectLeanSourceFiles0,
  ComputeLeanSourceClosureSha2560,
  DeriveFormalPublication0,
  ValidateLeanTheoremInventory0,
  stableStringify0,
  REQUIRED_MILESTONE_THEOREMS0,
} from '../formal-publication0.mjs';
import { ParseLeanInventoryProbe0 } from '../scripts/export-lean-theorem-inventory.mjs';

const ROOT = fileURLToPath(new URL('../', import.meta.url));

function compareNames0(left, right) {
  return left.name < right.name ? -1 : left.name > right.name ? 1 : 0;
}

function addRootCandidate0(inventory, { kind, kernelType, kernelValue, axioms = [] }) {
  assert.equal(inventory.compatibilityRootCandidate, null);
  const name = inventory.compatibilityRootName;
  const row = { name, module: 'PNP.Main', kind, axioms: [...axioms].sort() };
  inventory.declarations.push(row);
  inventory.declarations.sort(compareNames0);
  inventory.declarationCount += 1;
  inventory.declarationKindCounts[kind] += 1;
  if (kind === 'theorem') {
    inventory.theoremCount += 1;
    if (row.axioms.length === 0) inventory.assumptionFreeTheoremCount += 1;
  }
  inventory.compatibilityRootCandidate = { ...row, kernelType, kernelValue };
  return row;
}

function replaceConcreteTarget0(inventory, { kind, kernelType, kernelValue, axioms = [] }) {
  const current = inventory.concreteTargetCandidate;
  assert.notEqual(current, null);
  const index = inventory.declarations.findIndex(({ name }) => name === inventory.concreteTargetName);
  assert.notEqual(index, -1);
  const oldRow = inventory.declarations[index];
  inventory.declarationKindCounts[oldRow.kind] -= 1;
  if (oldRow.kind === 'theorem') {
    inventory.theoremCount -= 1;
    if (oldRow.axioms.length === 0) inventory.assumptionFreeTheoremCount -= 1;
  }
  const row = {
    name: inventory.concreteTargetName,
    module: current.module,
    kind,
    axioms: [...axioms].sort(),
  };
  inventory.declarations[index] = row;
  inventory.declarations.sort(compareNames0);
  inventory.declarationKindCounts[kind] += 1;
  if (kind === 'theorem') {
    inventory.theoremCount += 1;
    if (row.axioms.length === 0) inventory.assumptionFreeTheoremCount += 1;
  }
  inventory.concreteTargetCandidate = { ...row, kernelType, kernelValue };
  return row;
}

async function fixture0() {
  const [inventoryBytes, publicBytes, mapText] = await Promise.all([
    readFile(new URL('../status/LEAN_THEOREM_INVENTORY.json', import.meta.url)),
    readFile(new URL('../public/pnp-theorem-inventory.json', import.meta.url)),
    readFile(new URL('../publication/FORMAL_PUBLICATION_MAP.json', import.meta.url), 'utf8'),
  ]);
  return {
    inventoryBytes,
    publicBytes,
    inventory: JSON.parse(inventoryBytes.toString('utf8')),
    map: JSON.parse(mapText),
  };
}

test('compiled Lean inventory is canonical, complete, deterministic, and byte-mirrored', async () => {
  const { inventoryBytes, publicBytes, inventory } = await fixture0();
  assert.equal(inventoryBytes.equals(publicBytes), true);
  assert.equal(`${stableStringify0(inventory)}\n`, inventoryBytes.toString('utf8'));
  ValidateLeanTheoremInventory0(inventory);
  assert.equal(inventory.environmentProbeComplete, true);
  assert.equal(inventory.declarationCount, 27193);
  assert.equal(inventory.excludedPrivateDeclarationCount, 14995);
  assert.equal(inventory.theoremCount, 14163);
  assert.equal(inventory.assumptionFreeTheoremCount, 7264);
  assert.equal(inventory.axiomCount, 4);
  assert.equal(inventory.sourceClosureModuleCount, 244);
  assert.deepEqual(inventory.declarationKindCounts, {
    axiom: 4,
    constructor: 846,
    definition: 11408,
    inductive: 386,
    opaque: 0,
    quotient: 0,
    recursor: 386,
    theorem: 14163,
  });
  assert.deepEqual(inventory.projectAxioms, [
    'PNP.CheckPCCPackexp',
    'PNP.GeneratePCCPack',
    'PNP.LockedNANDThreshold',
    'PNP.ResidualBandExactMinimization',
  ]);
  assert.equal(inventory.compatibilityRootCandidate, null);
  assert.deepEqual(inventory.concreteTargetCandidate, {
    axioms: [],
    kernelType: 'Lean.Expr.sort (Lean.Level.zero)',
    kernelValue: 'Lean.Expr.const `PNP.Concrete.PEqualsNP []',
    kind: 'definition',
    module: 'PNP.Concrete.Target',
    name: 'PNP.Main.ConcretePEqualsNP',
  });
  assert.equal(inventory.milestoneCandidates.length, 2530);
  assert.deepEqual(inventory.milestoneCandidates.map((entry) => entry.name), REQUIRED_MILESTONE_THEOREMS0);
  assert.equal(inventory.milestoneCandidates.every((entry) => entry.kind === 'theorem'
    && entry.kernelValue === null && typeof entry.kernelType === 'string'), true);
});

test('source closure scans every Lean source and rejects a symlinked source root', async () => {
  const files = await CollectLeanSourceFiles0(ROOT);
  assert.equal(files.length, 247);
  assert.equal(files.every((file) => file.startsWith('lean/') && file.endsWith('.lean')), true);
  assert.deepEqual(files, [...files].sort());
  assert.equal(files.includes('lean/PNP.lean'), true);
  assert.equal(
    files.includes('lean/PNP/ResidualTerminalFourCornerSideTightCompletion.lean'),
    true,
  );
  assert.equal(
    files.includes('lean/PNP/ResidualTerminalFourCornerTightBasisMaximum.lean'),
    true,
  );
  assert.equal(
    files.includes('lean/PNP/ResidualTerminalBN2SquareLegitimacy.lean'),
    true,
  );
  assert.equal(
    files.includes('lean/PNP/ResidualTerminalBCELAnchorNucleus.lean'),
    true,
  );
  assert.equal(
    files.includes('lean/PNP/ResidualTerminalSaturationPositivityFirewall.lean'),
    true,
  );
  assert.equal(
    files.includes('lean/PNP/ResidualTerminalCandidateSaturation.lean'),
    true,
  );
  assert.equal(
    files.includes('lean/PNP/ResidualTerminalSaturationCostBalance.lean'),
    true,
  );
  assert.equal(
    files.includes('lean/PNP/ResidualTerminalInterfaceExposureRouting.lean'),
    true,
  );
  assert.equal(
    files.includes(
      'lean/PNP/ResidualTerminalOriginKernelObligationRouting.lean'),
    true,
  );
  assert.equal(
    files.includes('lean/PNP/ResidualTerminalFiniteSaturatePositive.lean'),
    true,
  );
  assert.equal(
    files.includes('lean/PNP/ResidualTerminalRankWF.lean'),
    true,
  );
  assert.equal(
    files.includes('lean/PNP/ResidualTerminalBN3RequestEnvelope.lean'),
    true,
  );
  assert.equal(
    files.includes('lean/PNP/ResidualTerminalBN4ActivationCancellation.lean'),
    true,
  );
  assert.equal(
    files.includes('lean/PNP/ResidualTerminalBN5FullShadowLocalization.lean'),
    true,
  );
  assert.equal(
    files.includes(
      'lean/PNP/ResidualTerminalConsumerAntichainNormalForm.lean'),
    true,
  );
  assert.equal(
    files.includes('lean/PNP/LockedNANDGlobalUnsatisfiableFinalZero.lean'),
    true,
  );
  assert.equal(
    files.includes('lean/PNP/LockedNANDGlobalSemanticThreshold.lean'),
    true,
  );
  assert.equal(
    files.includes('lean/PNP/Concrete/LockedNANDThresholdPublication.lean'),
    true,
  );
  assert.equal(files.includes('lean/PNP/ResidualRoutes.lean'), true);
  assert.equal(files.includes('lean/PNP/ResidualGainChain.lean'), true);
  assert.equal(files.includes('lean/PNP/ResidualGainStopping.lean'), true);
  assert.equal(files.includes('lean/PNP/ResidualTerminalFullBridge.lean'), true);
  assert.equal(files.includes('lean/PNP/ResidualTerminalModeFirewall.lean'), true);
  assert.equal(files.includes('lean/PNP/ResidualTerminalExecutableSaturation.lean'), true);
  assert.equal(files.includes('lean/PNP/ResidualTerminalPhysicalSupportCompletion.lean'), true);
  assert.equal(files.includes('lean/PNP/ResidualTerminalProperSupport.lean'), true);
  assert.equal(files.includes('lean/PNP/ResidualTerminalSupportSquareClosure.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/ResidualTerminalGovernedSupportCompletion.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/ResidualTerminalFrontierPushout.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/ResidualTerminalProjectionSquare.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/ResidualTerminalSideTightMinimum.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/ResidualTerminalFourCornerCarrier.lean'), true);
  assert.equal(files.includes('lean/PNP/LockedNANDResidualGainBound.lean'), true);
  assert.equal(files.includes('lean/PNP/LockedNANDCarrierTrace.lean'), true);
  assert.equal(files.includes('lean/PNP/LockedNANDGlobalCandidates.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/BitString.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CNFToNAND.lean'), true);
  assert.equal(
    files.includes('lean/PNP/Concrete/CNFToNANDPolynomialReduction.lean'),
    true,
  );
  assert.equal(files.includes('lean/PNP/Concrete/Machine.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/PipelineStageBridges.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/PipelineTerminalBridge.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralTerminatorStep.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.lean'),
  true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStep.lean'),
  true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderSecondConstraintSeventhPaddingOrUnaryOpportunityStep.lean'),
  true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralSuccessorTokenStep.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinBuilderSecondClausePrefix.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderSecondClausePaddingRun.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderThirdClauseSeparatorStep.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderThirdClauseFirstLiteralPrefix.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderThirdClauseSecondLiteralPrefix.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderThirdClausePrefix.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderThirdClausePaddingRun.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderFourthClauseSeparatorStep.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderFourthClauseFirstLiteralPrefix.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderFourthClauseSecondLiteralPrefix.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderFourthClausePrefix.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderFirstConstraintPaddingRun.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderSecondConstraintSeparatorStep.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralSignStep.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderSecondClauseFirstLiteralPrefix.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderSecondClauseSecondLiteralPrefix.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinFormulaSchedule.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinFormulaCursor.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinBuilderInputLength.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinBuilderInputPrefix.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinBuilderTokenAppender.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinBuilderSecondClauseSeparatorStep.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinBuilderFirstTokenPrefix.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinBuilderUnaryPolynomial.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinBuilderCompleteHeader.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinBuilderBodyStartPrefix.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinBuilderFirstLiteralPrefix.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinBuilderFirstClausePrefix.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderDynamicTokenCursorStep.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/CookLevinBuilderFirstClausePaddingRun.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/PipelinePairedCompiler.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/PipelineCompiler.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/TerminalOutputPacker.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/TapeHandoff.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/TapeBlankEquivalence.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/PipelineTapeGeometry.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/PipelineInputFramer.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/PipelineOutputHandoff.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/PipelineStateNamespace.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/PipelineSequentialStateNamespace.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/PipelineSequentialCompiler.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/PipelineMachineSimulation.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/Complexity.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/PipelineRefinement.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/Target.lean'), true);
  assert.equal(files.includes(
    'lean/PNP/Concrete/LockedNANDThresholdPublication.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CNFWorkUniversalCorrectness.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinLocalCNF.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinTableauCNF.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinTableauCNFSemantics.lean'), true);
  assert.equal(files.includes('lean/PNP/Concrete/CookLevinRawTapeBridge.lean'), true);

  const temporary = await mkdtemp(path.join(os.tmpdir(), 'pnp-lean-source-symlink-'));
  try {
    await symlink(path.join(ROOT, 'lean'), path.join(temporary, 'lean'), 'dir');
    await assert.rejects(CollectLeanSourceFiles0(temporary), /real directory/u);
  } finally {
    await rm(temporary, { recursive: true, force: true });
  }
});

test('inventory source uses the compiled environment and collectAxioms rather than source parsing', async () => {
  const source = await readFile(new URL('../lean-audit/PNPTheoremInventory.lean', import.meta.url), 'utf8');
  assert.match(source, /env\.constants\.fold/u);
  assert.match(source, /collectAxioms name/u);
  assert.match(source, /env\.getModuleIdxFor\? name/u);
  assert.doesNotMatch(source, /readFile|readDir|IO\.FS|Regex/u);
  assert.doesNotMatch(source, /foldStage2/u);
});

test('positive Lean probe parser rejects empty, malformed, noisy, failed, or noncanonical output', async () => {
  const { inventoryBytes } = await fixture0();
  const valid = ParseLeanInventoryProbe0({
    stdout: inventoryBytes.toString('utf8'), stderr: '', exitCode: 0, timedOut: false,
  });
  assert.equal(valid.inventory.declarationCount, 27193);
  for (const input of [
    { stdout: '', stderr: '', exitCode: 0, timedOut: false },
    { stdout: '{}\n', stderr: '', exitCode: 0, timedOut: false },
    { stdout: inventoryBytes.toString('utf8'), stderr: 'warning', exitCode: 0, timedOut: false },
    { stdout: inventoryBytes.toString('utf8'), stderr: ' ', exitCode: 0, timedOut: false },
    { stdout: inventoryBytes.toString('utf8'), stderr: '', exitCode: 1, timedOut: false },
    { stdout: inventoryBytes.toString('utf8'), stderr: '', exitCode: 0, timedOut: true },
    { stdout: `${JSON.stringify(JSON.parse(inventoryBytes), null, 2)}\n`, stderr: '', exitCode: 0, timedOut: false },
    { stdout: ` ${inventoryBytes.toString('utf8')}`, stderr: '', exitCode: 0, timedOut: false },
    { stdout: `${inventoryBytes.toString('utf8')}{}\n`, stderr: '', exitCode: 0, timedOut: false },
  ]) assert.throws(() => ParseLeanInventoryProbe0(input));
});

test('inventory validation rejects forged axioms, vacuous rows, stale coordinates, and unsorted declarations', async () => {
  const { inventory } = await fixture0();
  const mutations = [];
  const forged = structuredClone(inventory);
  forged.projectAxioms = [];
  mutations.push(forged);
  const vacuous = structuredClone(inventory);
  vacuous.declarations = [];
  vacuous.declarationCount = 0;
  vacuous.theoremCount = 0;
  vacuous.assumptionFreeTheoremCount = 0;
  vacuous.axiomCount = 0;
  mutations.push(vacuous);
  const stale = structuredClone(inventory);
  stale.coordinate = 'PNP-LEAN-THEOREM-INVENTORY-STALE';
  mutations.push(stale);
  const unsorted = structuredClone(inventory);
  [unsorted.declarations[0], unsorted.declarations[1]] = [unsorted.declarations[1], unsorted.declarations[0]];
  mutations.push(unsorted);
  for (const mutation of mutations) assert.throws(() => ValidateLeanTheoremInventory0(mutation));
});

test('publication derivation binds the validated inventory to its exact canonical bytes', async () => {
  const { inventoryBytes, inventory, map } = await fixture0();
  assert.throws(() => DeriveFormalPublication0(inventory, map, Buffer.from('{}\n'), '0'.repeat(64)));
  assert.doesNotThrow(() => DeriveFormalPublication0(inventory, map, inventoryBytes, '0'.repeat(64)));
});

test('target-present publication derivation remains false with null fingerprints despite an eligible model', async () => {
  const { inventoryBytes, inventory, map } = await fixture0();
  const sourceClosure = await ComputeLeanSourceClosureSha2560(ROOT, inventory);
  assert.match(sourceClosure, /^[0-9a-f]{64}$/u);
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes, sourceClosure);
  assert.equal(publication.gate.passed, false);
  assert.equal(publication.gate.abstractPEqualsNPIsPublicationIneligible, true);
  assert.equal(publication.gate.unsetFingerprintIsIntentionalFailClosedMigrationGate, true);
  assert.equal(publication.gate.subchecks.standardComplexityModelEligible, true);
  assert.equal(publication.gate.subchecks.concreteTargetPresent, true);
  assert.equal(publication.gate.subchecks.concreteTargetIsDefinition, true);
  assert.match(publication.gate.actualConcreteTargetKernelTypeSha256, /^[0-9a-f]{64}$/u);
  assert.match(publication.gate.actualConcreteTargetKernelValueSha256, /^[0-9a-f]{64}$/u);
  for (const field of [
    'expectedConcreteTargetKernelTypeSha256',
    'expectedConcreteTargetKernelValueSha256',
    'expectedRootKernelTypeSha256',
    'expectedAxiomClosureSha256',
    'expectedSourceClosureSha256',
  ]) assert.equal(publication.gate[field], null, field);
  for (const field of [
    'concreteTargetKernelTypeFingerprintConfigured',
    'concreteTargetKernelTypeFingerprintMatches',
    'concreteTargetKernelValueFingerprintConfigured',
    'concreteTargetKernelValueFingerprintMatches',
  ]) assert.equal(publication.gate.subchecks[field], false, field);
  assert.equal(publication.gate.subchecks.compatibilityRootPresent, false);
  assert.equal(publication.gate.subchecks.axiomClosureUsesOnlyLeanStandardAllowlist, false);
  assert.equal(publication.gate.subchecks.sourceClosureFingerprintConfigured, false);
  assert.equal(publication.emissionFields.publicTheoremEmissionAllowed, false);
  assert.equal(publication.emissionFields.publicTheoremStatement, null);
});

test('abstract PEqualsNP candidate cannot satisfy the concrete publication type check', async () => {
  const { inventory, map } = await fixture0();
  const mutated = structuredClone(inventory);
  addRootCandidate0(mutated, {
    kind: 'theorem',
    kernelType: 'Lean.Expr.const `PNP.PEqualsNP []',
    kernelValue: null,
  });
  const bytes = Buffer.from(`${stableStringify0(mutated)}\n`);
  const publication = DeriveFormalPublication0(mutated, map, bytes, '0'.repeat(64));
  assert.equal(publication.gate.subchecks.compatibilityRootPresent, true);
  assert.equal(publication.gate.subchecks.compatibilityRootIsTheorem, true);
  assert.equal(publication.gate.subchecks.compatibilityRootHasExactConcreteType, false);
  assert.equal(publication.gate.passed, false);
});

test('wrong concrete target/root kinds or root types cannot satisfy the gate', async () => {
  const { inventory, map } = await fixture0();
  const exactRootType = 'Lean.Expr.const `PNP.Main.ConcretePEqualsNP []';
  const cases = [
    {
      label: 'target theorem',
      target: { kind: 'theorem', kernelType: 'Lean.Expr.sort (Lean.Level.zero)', kernelValue: 'Lean.Expr.lit 0' },
      root: { kind: 'theorem', kernelType: exactRootType, kernelValue: null },
      failed: 'concreteTargetIsDefinition',
    },
    {
      label: 'root definition',
      target: { kind: 'definition', kernelType: 'Lean.Expr.sort (Lean.Level.zero)', kernelValue: 'Lean.Expr.lit 0' },
      root: { kind: 'definition', kernelType: exactRootType, kernelValue: 'Lean.Expr.lit 0' },
      failed: 'compatibilityRootIsTheorem',
    },
    {
      label: 'abstract root type',
      target: { kind: 'definition', kernelType: 'Lean.Expr.sort (Lean.Level.zero)', kernelValue: 'Lean.Expr.lit 0' },
      root: { kind: 'theorem', kernelType: 'Lean.Expr.const `PNP.PEqualsNP []', kernelValue: null },
      failed: 'compatibilityRootHasExactConcreteType',
    },
  ];
  for (const fixture of cases) {
    const mutated = structuredClone(inventory);
    replaceConcreteTarget0(mutated, fixture.target);
    addRootCandidate0(mutated, fixture.root);
    const bytes = Buffer.from(`${stableStringify0(mutated)}\n`);
    const publication = DeriveFormalPublication0(mutated, map, bytes, '0'.repeat(64));
    assert.equal(publication.gate.subchecks[fixture.failed], false, fixture.label);
    assert.equal(publication.gate.passed, false, fixture.label);
  }
});

test('same-name theorem type weakening and source-closure drift revoke milestone earning', async () => {
  const { inventoryBytes, inventory, map } = await fixture0();
  const current = DeriveFormalPublication0(
    inventory,
    map,
    inventoryBytes,
    map.milestoneSourceClosureSha256,
  );
  assert.equal(current.milestones.filter((entry) => entry.earned).length, 103);
  const tableauSemantics = current.milestones.find(
    (entry) => entry.id === 'concrete-cook-levin-tableau-cnf-semantics',
  );
  assert.equal(tableauSemantics.allAssumptionFree, false);
  assert.equal(tableauSemantics.axiomClosureUsesOnlyLeanStandardAllowlist, true);
  assert.equal(tableauSemantics.earned, true);

  const weakened = structuredClone(inventory);
  const candidate = weakened.milestoneCandidates.find(
    (entry) => entry.name === 'PNP.DirectWire.andCircuit_spec',
  );
  candidate.kernelType = 'Lean.Expr.const `True []';
  const weakenedBytes = Buffer.from(`${stableStringify0(weakened)}\n`);
  const weakenedPublication = DeriveFormalPublication0(
    weakened,
    map,
    weakenedBytes,
    map.milestoneSourceClosureSha256,
  );
  const semantics = weakenedPublication.milestones.find((entry) => entry.id === 'direct-wire-semantics');
  assert.equal(semantics.allPresent, true);
  assert.equal(semantics.allAssumptionFree, true);
  assert.equal(semantics.allKernelTypesMatch, false);
  assert.equal(semantics.earned, false);
  assert.equal(semantics.status, 'not-formalized');

  const sourceDrift = DeriveFormalPublication0(inventory, map, inventoryBytes, 'f'.repeat(64));
  assert.equal(sourceDrift.milestones.every((entry) => entry.earned === false), true);
  assert.equal(sourceDrift.milestones.every(
    (entry) => entry.sourceClosureFingerprintMatches === false,
  ), true);
});

test('a project axiom in a milestone closure revokes standard-axiom earning', async () => {
  const { inventory, map } = await fixture0();
  const contaminated = structuredClone(inventory);
  const name = 'PNP.Concrete.CookLevin.VerifierTableauProblem.formula_satisfiable_iff_finiteAccepting';
  const axioms = ['PNP.SAT', 'Quot.sound', 'propext'];
  contaminated.declarations.find((entry) => entry.name === name).axioms = axioms;
  contaminated.milestoneCandidates.find((entry) => entry.name === name).axioms = axioms;
  const bytes = Buffer.from(`${stableStringify0(contaminated)}\n`);
  const publication = DeriveFormalPublication0(
    contaminated,
    map,
    bytes,
    map.milestoneSourceClosureSha256,
  );
  const milestone = publication.milestones.find(
    (entry) => entry.id === 'concrete-cook-levin-tableau-cnf-semantics',
  );
  assert.equal(milestone.allPresent, true);
  assert.equal(milestone.axiomClosureUsesOnlyLeanStandardAllowlist, false);
  assert.equal(milestone.earned, false);
  assert.equal(milestone.status, 'not-formalized');
});

test('project, unknown, and sorry axioms cannot pass the fixed standard-axiom closure', async () => {
  const { inventory, map } = await fixture0();
  for (const axiom of ['PNP.SAT', 'Unknown.UnreviewedAxiom', 'sorryAx']) {
    const mutated = structuredClone(inventory);
    replaceConcreteTarget0(mutated, {
      kind: 'definition',
      kernelType: 'Lean.Expr.sort (Lean.Level.zero)',
      kernelValue: 'Lean.Expr.lit 0',
      axioms: [axiom],
    });
    addRootCandidate0(mutated, {
      kind: 'theorem',
      kernelType: 'Lean.Expr.const `PNP.Main.ConcretePEqualsNP []',
      kernelValue: null,
      axioms: [],
    });
    const bytes = Buffer.from(`${stableStringify0(mutated)}\n`);
    const publication = DeriveFormalPublication0(mutated, map, bytes, '0'.repeat(64));
    assert.deepEqual(publication.gate.axiomClosure, [axiom]);
    assert.equal(publication.gate.subchecks.axiomClosureUsesOnlyLeanStandardAllowlist, false, axiom);
    assert.equal(publication.gate.passed, false, axiom);
  }
});

test('publication map cannot set fingerprints or expand the axiom allowlist', async () => {
  const { inventoryBytes, inventory, map } = await fixture0();
  const fingerprinted = structuredClone(map);
  fingerprinted.gate.expectedRootKernelTypeSha256 = 'a'.repeat(64);
  assert.throws(() => DeriveFormalPublication0(inventory, fingerprinted, inventoryBytes, 'b'.repeat(64)));
  const expanded = structuredClone(map);
  expanded.gate.allowedLeanStandardAxioms.push('PNP.SAT');
  assert.throws(() => DeriveFormalPublication0(inventory, expanded, inventoryBytes, 'b'.repeat(64)));
  const vacuousMilestone = structuredClone(map);
  vacuousMilestone.milestones[0].requiredTheorems = [];
  assert.throws(() => DeriveFormalPublication0(inventory, vacuousMilestone, inventoryBytes, 'b'.repeat(64)));
  const promotedMilestone = structuredClone(map);
  promotedMilestone.milestones.at(-1).classification = 'formalized';
  assert.throws(() => DeriveFormalPublication0(inventory, promotedMilestone, inventoryBytes, 'b'.repeat(64)));
});
