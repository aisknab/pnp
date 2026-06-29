import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckFiniteToUnboundedFamilyAudit0 } from '../pcc-finite-to-unbounded-family-audit0.mjs';

async function json0(pathname) {
  return JSON.parse(await readFile(new URL(`../${pathname}`, import.meta.url), 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('finite-to-unbounded audit accepts current manifest and gap linkage', async () => {
  const out = await CheckFiniteToUnboundedFamilyAudit0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-FINITE-TO-UNBOUNDED-FAMILY-AUDIT-2026-06-27-01');
  assert.equal(out.finiteToUnboundedFamilyAuditReady, true);
  assert.equal(out.uniformityRepresented, true);
  assert.equal(out.uniformAllInputSizesCoverageProved, false);
  assert.equal(out.polynomialUniformGeneratorProved, false);
  assert.equal(out.unrestrictedFinalSoundnessDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByAudit, false);
  assert.equal(out.linkedGap, 'GAP-004-FiniteToUnboundedUniformity');
  assert.equal(out.gapStatus, 'represented-not-discharged');
  assert.equal(out.gapSeverity, 'activation-blocking');
  assert.equal(out.gapBlocker, 'Release.UnrestrictedFinalSoundness');
  assert.deepEqual(out.requiredUniformityCriteria, [
    'Uniform.InputFamily',
    'Uniform.Generator',
    'Uniform.PolynomialBound',
    'Uniform.SemanticPreservation',
    'Uniform.NoFiniteExtrapolation',
  ]);
  assert.ok(out.evidenceFileCount > 0);
  assert.equal(out.evidenceDigestSha256.length, 64);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('finite-to-unbounded audit rejects public theorem activation', async () => {
  const manifest = clone0(await json0('proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json'));
  manifest.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckFiniteToUnboundedFamilyAudit0({
    manifestOverride: manifest,
    gapLedgerOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FiniteToUnboundedAudit.PublicEmission');
});

test('finite-to-unbounded audit rejects uniform coverage overclaim', async () => {
  const manifest = clone0(await json0('proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json'));
  manifest.uniformAllInputSizesCoverageProved = true;

  const out = await CheckFiniteToUnboundedFamilyAudit0({
    manifestOverride: manifest,
    gapLedgerOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FiniteToUnboundedAudit.UniformCoverageOverclaim');
});

test('finite-to-unbounded audit rejects polynomial generator overclaim', async () => {
  const manifest = clone0(await json0('proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json'));
  manifest.polynomialUniformGeneratorProved = true;

  const out = await CheckFiniteToUnboundedFamilyAudit0({
    manifestOverride: manifest,
    gapLedgerOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FiniteToUnboundedAudit.PolynomialGeneratorOverclaim');
});

test('finite-to-unbounded audit rejects unrestricted final soundness discharge', async () => {
  const manifest = clone0(await json0('proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json'));
  manifest.unrestrictedFinalSoundnessDischarged = true;

  const out = await CheckFiniteToUnboundedFamilyAudit0({
    manifestOverride: manifest,
    gapLedgerOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FiniteToUnboundedAudit.UnrestrictedSoundnessOverclaim');
});

test('finite-to-unbounded audit rejects changed criteria order', async () => {
  const manifest = clone0(await json0('proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json'));
  const temp = manifest.requiredUniformityCriteria[0];
  manifest.requiredUniformityCriteria[0] = manifest.requiredUniformityCriteria[1];
  manifest.requiredUniformityCriteria[1] = temp;

  const out = await CheckFiniteToUnboundedFamilyAudit0({
    manifestOverride: manifest,
    gapLedgerOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FiniteToUnboundedAudit.CriteriaIds');
});

test('finite-to-unbounded audit rejects GAP-004 as unresolved future placeholder', async () => {
  const gapLedger = clone0(await json0('proof-obligations/GAP_LEDGER.json'));
  const gap = gapLedger.gaps.find((entry) => entry.id === 'GAP-004-FiniteToUnboundedUniformity');
  gap.status = 'known-unresolved';
  gap.ownerSurface = 'future-finite-to-unbounded-audit';

  const out = await CheckFiniteToUnboundedFamilyAudit0({
    manifestOverride: await json0('proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json'),
    gapLedgerOverride: gapLedger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FiniteToUnboundedAudit.Gap004Status');
});

test('finite-to-unbounded audit rejects GAP-004 if blocker is cleared', async () => {
  const gapLedger = clone0(await json0('proof-obligations/GAP_LEDGER.json'));
  const gap = gapLedger.gaps.find((entry) => entry.id === 'GAP-004-FiniteToUnboundedUniformity');
  gap.blocker = null;

  const out = await CheckFiniteToUnboundedFamilyAudit0({
    manifestOverride: await json0('proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json'),
    gapLedgerOverride: gapLedger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FiniteToUnboundedAudit.Gap004Blocker');
});

test('finite-to-unbounded audit rejects missing evidence surface', async () => {
  const manifest = clone0(await json0('proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json'));
  manifest.evidenceSurfaces.push('missing/finite-to-unbounded-evidence.json');

  const out = await CheckFiniteToUnboundedFamilyAudit0({
    manifestOverride: manifest,
    gapLedgerOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FiniteToUnboundedAudit.PathMissing');
});
