import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  GenerateCheckerDependencyGraph0,
} from '../scripts/generate-checker-dependency-graph.mjs';

test('checker dependency graph generator accepts current repository', async () => {
  const out = await GenerateCheckerDependencyGraph0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-CHECKER-DEPENDENCY-GRAPH-2026-06-27-01');
  assert.equal(out.graphCycleAuditRequired, true);
  assert.equal(out.noCircularAuthorityProved, false);
  assert.ok(out.checkerCount >= 5);
  assert.ok(out.moduleImportEdgeCount >= 1);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
  assert.equal(out.graphSha256.length, 64);
  assert.equal(out.dotSha256.length, 64);
  assert.equal(out.svgSha256.length, 64);
});

test('checker dependency graph generator writes graph artifacts when requested', async () => {
  const outputDir = 'artifacts/checker-dependency-graph-test';
  const out = await GenerateCheckerDependencyGraph0({ outputDir, writeOutput: true });

  assert.equal(out.tag, 'accept');
  assert.equal(out.graphPath, `${outputDir}/checker-dependency-graph.json`);
  assert.equal(out.dotPath, `${outputDir}/checker-dependency-graph.dot`);
  assert.equal(out.svgPath, `${outputDir}/checker-dependency-graph.svg`);
});
