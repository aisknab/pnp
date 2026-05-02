import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  CheckReleaseAudit0,
  RELEASE_AUDIT_CLI_SUMMARY_KEYS0,
  RELEASE_AUDIT_NF_KEYS0,
  RELEASE_AUDIT_PUBLIC_SURFACE_FREEZE_SUMMARY_KEYS0,
  makeReleaseAuditConfig0,
  summarizeReleaseAudit0,
} from '../pcc-release-audit0.mjs';

function childFailureMessage0(child) {
  return [
    child.error?.message ?? '',
    child.stderr ?? '',
    child.stdout ?? '',
  ].filter((entry) => entry.length > 0).join('\n');
}

test('CheckReleaseAudit0 NF exposes public surface freeze proof summary', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: true,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
  }));

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.publicSurfaceFreeze, true);

  assert.equal(out.NF.publicSurfaceFreezeSummary.kind, 'ReleasePublicSurfaceFreezeSummary0');
  assert.equal(out.NF.publicSurfaceFreezeSummary.enabled, true);
  assert.equal(out.NF.publicSurfaceFreezeSummary.skipped, false);
  assert.equal(out.NF.publicSurfaceFreezeSummary.surfaceFrozen, true);
  assert.equal(out.NF.publicSurfaceFreezeSummary.publicEntryExportCount > 0, true);
  assert.equal(out.NF.publicSurfaceFreezeSummary.packageExportCount > 0, true);
  assert.equal(out.NF.publicSurfaceFreezeSummary.packageBinCount > 0, true);
  assert.equal(out.NF.publicSurfaceFreezeSummary.packageScriptCount > 0, true);
  assert.match(out.NF.publicSurfaceFreezeSummary.publicSurfaceDigest.hex, /^[0-9a-f]{64}$/);

  assert.deepEqual(out.NF.publicSurfaceFreezeDigest, out.NF.publicSurfaceFreezeSummary.publicSurfaceDigest);
  assert.equal(out.NF.publicSurfaceFreezePublicEntryExportCount, out.NF.publicSurfaceFreezeSummary.publicEntryExportCount);
  assert.equal(out.NF.publicSurfaceFreezePackageExportCount, out.NF.publicSurfaceFreezeSummary.packageExportCount);
  assert.equal(out.NF.publicSurfaceFreezePackageBinCount, out.NF.publicSurfaceFreezeSummary.packageBinCount);
  assert.equal(out.NF.publicSurfaceFreezePackageScriptCount, out.NF.publicSurfaceFreezeSummary.packageScriptCount);
  assert.equal(out.NF.publicSurfaceFreezeSurfaceFrozen, true);

  assert.deepEqual(Object.keys(out.NF), RELEASE_AUDIT_NF_KEYS0);
  assert.deepEqual(Object.keys(out.NF.publicSurfaceFreezeSummary), RELEASE_AUDIT_PUBLIC_SURFACE_FREEZE_SUMMARY_KEYS0);
});

test('CheckReleaseAudit0 NF exposes skipped public surface freeze summary', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
  }));

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.publicSurfaceFreeze, false);
  assert.equal(out.NF.publicSurfaceFreezeSummary.enabled, false);
  assert.equal(out.NF.publicSurfaceFreezeSummary.skipped, true);
  assert.equal(out.NF.publicSurfaceFreezeSummary.publicSurfaceDigest, null);
  assert.equal(out.NF.publicSurfaceFreezePublicEntryExportCount, 0);
  assert.equal(out.NF.publicSurfaceFreezePackageExportCount, 0);
  assert.equal(out.NF.publicSurfaceFreezePackageBinCount, 0);
  assert.equal(out.NF.publicSurfaceFreezePackageScriptCount, 0);
  assert.equal(out.NF.publicSurfaceFreezeSurfaceFrozen, null);
});

test('summarizeReleaseAudit0 exposes public surface freeze proof summary', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: true,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
  }));

  const summary = summarizeReleaseAudit0(out);

  assert.equal(summary.tag, 'accept');
  assert.equal(summary.publicSurfaceFreeze, true);
  assert.equal(summary.publicSurfaceFreezeSummary.skipped, false);
  assert.equal(summary.publicSurfaceFreezeSummary.surfaceFrozen, true);
  assert.equal(summary.publicSurfaceFreezeSurfaceFrozen, true);
  assert.match(summary.publicSurfaceFreezeDigest.hex, /^[0-9a-f]{64}$/);

  assert.deepEqual(Object.keys(summary), RELEASE_AUDIT_CLI_SUMMARY_KEYS0);
  assert.deepEqual(Object.keys(summary.publicSurfaceFreezeSummary), RELEASE_AUDIT_PUBLIC_SURFACE_FREEZE_SUMMARY_KEYS0);
});

test('release audit CLI summary exposes public surface freeze proof summary', () => {
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--no-materialized-gate', '--no-final-certificate-gate'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.publicSurfaceFreeze, true);
  assert.equal(out.publicSurfaceFreezeSummary.skipped, false);
  assert.equal(out.publicSurfaceFreezeSurfaceFrozen, true);
  assert.match(out.publicSurfaceFreezeDigest.hex, /^[0-9a-f]{64}$/);
  assert.deepEqual(Object.keys(out), RELEASE_AUDIT_CLI_SUMMARY_KEYS0);
  assert.deepEqual(Object.keys(out.publicSurfaceFreezeSummary), RELEASE_AUDIT_PUBLIC_SURFACE_FREEZE_SUMMARY_KEYS0);
});

test('release audit CLI full mode exposes public surface freeze proof summary in NF', () => {
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--no-materialized-gate', '--no-final-certificate-gate', '--full'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.publicSurfaceFreeze, true);
  assert.equal(out.NF.publicSurfaceFreezeSummary.skipped, false);
  assert.equal(out.NF.publicSurfaceFreezeSurfaceFrozen, true);
  assert.match(out.NF.publicSurfaceFreezeDigest.hex, /^[0-9a-f]{64}$/);
  assert.deepEqual(Object.keys(out.NF), RELEASE_AUDIT_NF_KEYS0);
  assert.deepEqual(Object.keys(out.NF.publicSurfaceFreezeSummary), RELEASE_AUDIT_PUBLIC_SURFACE_FREEZE_SUMMARY_KEYS0);
});

test('README documents release audit public surface freeze summary fields', async () => {
  const readme = await fs.readFile(new URL('../README.md', import.meta.url), 'utf8');

  assert.equal(readme.includes('Release audit public surface freeze summary'), true);
  assert.equal(readme.includes('publicSurfaceFreezeDigest'), true);
  assert.equal(readme.includes('publicSurfaceFreezePublicEntryExportCount'), true);
  assert.equal(readme.includes('publicSurfaceFreezePackageExportCount'), true);
  assert.equal(readme.includes('publicSurfaceFreezePackageBinCount'), true);
  assert.equal(readme.includes('publicSurfaceFreezePackageScriptCount'), true);
  assert.equal(readme.includes('publicSurfaceFreezeSurfaceFrozen'), true);
  assert.equal(readme.includes('surfaceFrozen = true'), true);
});