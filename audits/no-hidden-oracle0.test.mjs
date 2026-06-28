import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  AuditNoHiddenOracle0,
} from '../scripts/audit-no-hidden-oracle.mjs';

async function loadManifest0() {
  const text = await readFile(new URL('../oracle-audit/NO_HIDDEN_ORACLE_AUDIT.json', import.meta.url), 'utf8');
  return JSON.parse(text);
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('no-hidden-oracle audit accepts current repository seed surface', async () => {
  const out = await AuditNoHiddenOracle0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-NO-HIDDEN-ORACLE-AUDIT-2026-06-27-01');
  assert.equal(out.noHiddenOracleAuditReady, true);
  assert.equal(out.fullNoHiddenOracleProved, false);
  assert.equal(out.publicTheoremEmissionAllowedByAudit, false);
  assert.ok(out.scannedFileCount > 0);
  assert.ok(out.executableFileCount > 0);
  assert.equal(out.forbiddenExecutableHitCount, 0);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('no-hidden-oracle audit rejects public theorem activation', async () => {
  const manifest = clone0(await loadManifest0());
  manifest.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await AuditNoHiddenOracle0({
    manifestOverride: manifest,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoHiddenOracle.PublicEmission');
  assert.deepEqual(out.path, ['claimBoundary', 'publicTheoremEmissionAllowed']);
});

test('no-hidden-oracle audit rejects full proof overclaim', async () => {
  const manifest = clone0(await loadManifest0());
  manifest.fullNoHiddenOracleProved = true;

  const out = await AuditNoHiddenOracle0({
    manifestOverride: manifest,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoHiddenOracle.FullProofFlag');
  assert.deepEqual(out.path, ['fullNoHiddenOracleProved']);
});

test('no-hidden-oracle audit rejects injected executable SAT solver call', async () => {
  const out = await AuditNoHiddenOracle0({
    extraVirtualFiles: [
      {
        path: 'src/bad-oracle.mjs',
        text: 'export function bad0(formula) { return solveSAT(formula); }\n',
      },
    ],
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoHiddenOracle.ForbiddenExecutableHit');
  assert.equal(out.witness.forbiddenHits[0].patternId, 'SATSolverAPI');
});

test('no-hidden-oracle audit rejects injected NP oracle and unbounded search', async () => {
  const out = await AuditNoHiddenOracle0({
    extraVirtualFiles: [
      {
        path: 'src/bad-np-oracle.mjs',
        text: 'export const result = NPOracle(instance);\nwhile (true) { searchUntilFound(); }\n',
      },
    ],
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoHiddenOracle.ForbiddenExecutableHit');
  const ids = out.witness.forbiddenHits.map((hit) => hit.patternId);
  assert.ok(ids.includes('NPOracle'));
});

test('no-hidden-oracle audit allows documentation-only formal references', async () => {
  const out = await AuditNoHiddenOracle0({
    extraVirtualFiles: [
      {
        path: 'docs/formal-oracle-reference.md',
        text: 'This formal reference mentions NP oracle and SAT solver as forbidden examples.\n',
      },
    ],
    writeOutput: false,
  });

  assert.equal(out.tag, 'accept');
  assert.ok(out.documentationReferenceCount >= 1);
});
