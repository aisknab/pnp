import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  CheckReleaseAudit0,
  makeReleaseAuditConfig0,
} from '../pcc-release-audit0.mjs';

function childFailureMessage0(child) {
  return [
    child.error?.message ?? '',
    child.stderr ?? '',
    child.stdout ?? '',
  ].filter((entry) => entry.length > 0).join('\n');
}

test('CheckReleaseAudit0 NF exposes materialized public status gate proof summary', async (t) => {
  const outputDir = await makeTempDir0(t);

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runMaterializedPublicStatusGate: true,
    materializedPublicStatusGateOutputDir: outputDir,
    materializedPublicStatusGateRunCliChecks: false,
  }));

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.materializedPublicStatusGate, true);

  assert.equal(out.NF.materializedPublicStatusGateSummary.kind, 'ReleaseMaterializedPublicStatusGateSummary0');
  assert.equal(out.NF.materializedPublicStatusGateSummary.enabled, true);
  assert.equal(out.NF.materializedPublicStatusGateSummary.skipped, false);
  assert.equal(out.NF.materializedPublicStatusGateSummary.deterministic, true);
  assert.equal(out.NF.materializedPublicStatusGateSummary.materializedPath, true);
  assert.equal(out.NF.materializedPublicStatusGateSummary.syntheticRunAll, false);
  assert.equal(out.NF.materializedPublicStatusGateSummary.acceptedPublicConclusionOnly, true);
  assert.equal(out.NF.materializedPublicStatusGateSummary.fileCount, 4);
  assert.equal(out.NF.materializedPublicStatusGateSummary.directRecordCount, 4);
  assert.equal(out.NF.materializedPublicStatusGateSummary.cliRecordCount, 0);
  assert.match(out.NF.materializedPublicStatusGateSummary.gateDigest.hex, /^[0-9a-f]{64}$/);

  assert.deepEqual(out.NF.materializedPublicStatusGateDigest, out.NF.materializedPublicStatusGateSummary.gateDigest);
  assert.equal(out.NF.materializedPublicStatusGateFileCount, 4);
  assert.equal(out.NF.materializedPublicStatusGateDirectRecordCount, 4);
  assert.equal(out.NF.materializedPublicStatusGateCliRecordCount, 0);
  assert.equal(out.NF.materializedPublicStatusGateAcceptedPublicConclusionOnly, true);
});

test('CheckReleaseAudit0 NF exposes skipped materialized gate summary', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runMaterializedPublicStatusGate: false,
  }));

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.materializedPublicStatusGate, false);
  assert.equal(out.NF.materializedPublicStatusGateSummary.enabled, false);
  assert.equal(out.NF.materializedPublicStatusGateSummary.skipped, true);
  assert.equal(out.NF.materializedPublicStatusGateSummary.gateDigest, null);
  assert.equal(out.NF.materializedPublicStatusGateFileCount, 0);
  assert.equal(out.NF.materializedPublicStatusGateAcceptedPublicConclusionOnly, null);
});

test('release audit CLI summary exposes materialized public status gate proof summary', async (t) => {
  const outputDir = await makeTempDir0(t);
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [
    cliPath,
    '--materialized-gate',
    '--materialized-gate-out',
    outputDir,
    '--no-materialized-gate-cli',
  ], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.materializedPublicStatusGate, true);
  assert.equal(out.materializedPublicStatusGateSummary.skipped, false);
  assert.equal(out.materializedPublicStatusGateSummary.fileCount, 4);
  assert.equal(out.materializedPublicStatusGateSummary.directRecordCount, 4);
  assert.equal(out.materializedPublicStatusGateSummary.cliRecordCount, 0);
  assert.equal(out.materializedPublicStatusGateSummary.acceptedPublicConclusionOnly, true);
  assert.match(out.materializedPublicStatusGateDigest.hex, /^[0-9a-f]{64}$/);
});

test('release audit CLI full mode exposes materialized public status gate proof summary in NF', async (t) => {
  const outputDir = await makeTempDir0(t);
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [
    cliPath,
    '--full',
    '--materialized-gate',
    '--materialized-gate-out',
    outputDir,
    '--no-materialized-gate-cli',
  ], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.materializedPublicStatusGate, true);
  assert.equal(out.NF.materializedPublicStatusGateSummary.fileCount, 4);
  assert.equal(out.NF.materializedPublicStatusGateSummary.directRecordCount, 4);
  assert.equal(out.NF.materializedPublicStatusGateSummary.cliRecordCount, 0);
  assert.equal(out.NF.materializedPublicStatusGateAcceptedPublicConclusionOnly, true);
});

test('README documents release audit materialized gate summary fields', async () => {
  const readme = await fs.readFile(new URL('../README.md', import.meta.url), 'utf8');

  assert.equal(readme.includes('Release audit materialized gate summary'), true);
  assert.equal(readme.includes('materializedPublicStatusGateDigest'), true);
  assert.equal(readme.includes('materializedPublicStatusGateFileCount'), true);
  assert.equal(readme.includes('materializedPublicStatusGateDirectRecordCount'), true);
  assert.equal(readme.includes('materializedPublicStatusGateCliRecordCount'), true);
  assert.equal(readme.includes('materializedPublicStatusGateAcceptedPublicConclusionOnly'), true);
  assert.equal(readme.includes('syntheticRunAll = false'), true);
  assert.equal(readme.includes('acceptedPublicConclusionOnly = true'), true);
});

async function makeTempDir0(t) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-release-audit-full-mode-gate-summary-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  return dir;
}