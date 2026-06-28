import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  AuditCheckerCycles0,
} from '../scripts/audit-checker-cycles.mjs';

async function loadManifest0() {
  const text = await readFile(new URL('../checker-cycles/CHECKER_AUTHORITY_GRAPH.json', import.meta.url), 'utf8');
  return JSON.parse(text);
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('checker cycle audit accepts current authority graph', async () => {
  const out = await AuditCheckerCycles0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-CHECKER-AUTHORITY-GRAPH-2026-06-27-01');
  assert.equal(out.dependencyGraphCoordinate, 'PNP-CHECKER-DEPENDENCY-GRAPH-2026-06-27-01');
  assert.equal(out.authorityGraphReady, true);
  assert.equal(out.noCircularAuthorityProved, true);
  assert.equal(out.fullStaticImportCycleFreedomProved, false);
  assert.equal(out.staticDependencyCyclesAreAuthorityOnlyWhenDeclared, true);
  assert.equal(out.checkedCycleCount, 0);
  assert.ok(out.authorityEdgeCount >= 1);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('checker cycle audit rejects public theorem activation', async () => {
  const manifest = clone0(await loadManifest0());
  manifest.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await AuditCheckerCycles0({
    manifestOverride: manifest,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CheckerCycles.PublicEmission');
  assert.deepEqual(out.path, ['claimBoundary', 'publicTheoremEmissionAllowed']);
});

test('checker cycle audit rejects static import cycle freedom overclaim', async () => {
  const manifest = clone0(await loadManifest0());
  manifest.fullStaticImportCycleFreedomProved = true;

  const out = await AuditCheckerCycles0({
    manifestOverride: manifest,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CheckerCycles.StaticCycleFreedomFlag');
  assert.deepEqual(out.path, ['fullStaticImportCycleFreedomProved']);
});

test('checker cycle audit rejects unknown authority edge node', async () => {
  const manifest = clone0(await loadManifest0());
  manifest.authorityEdges[0].from = 'UnknownChecker0';

  const out = await AuditCheckerCycles0({
    manifestOverride: manifest,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CheckerCycles.EdgeUnknownFrom');
  assert.deepEqual(out.path, ['authorityEdges', 0, 'from']);
});

test('checker cycle audit rejects declared authority cycle', async () => {
  const manifest = clone0(await loadManifest0());
  manifest.authorityEdges.push({
    from: 'RunPNPVerifyAll0',
    to: 'CheckPublicEntryReleaseSurface0',
    kind: 'authority-premise',
    description: 'mutation edge that feeds the integrated verifier conclusion back into the public surface premise',
  });

  const out = await AuditCheckerCycles0({
    manifestOverride: manifest,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CheckerCycles.AuthorityCycleDetected');
  assert.deepEqual(out.path, ['authorityEdges']);
  assert.ok(out.witness.cycle.includes('CheckPublicEntryReleaseSurface0'));
  assert.ok(out.witness.cycle.includes('RunPNPVerifyAll0'));
});
