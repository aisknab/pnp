import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  CheckReleaseAudit0,
  RELEASE_AUDIT_CLI_SUMMARY_KEYS0,
  RELEASE_AUDIT_MATERIALIZED_GATE_SUMMARY_KEYS0,
  RELEASE_AUDIT_NF_KEYS0,
  makeReleaseAuditConfig0,
  summarizeReleaseAudit0,
  validateReleaseAuditCliSummarySurface0,
  validateReleaseAuditSurface0,
} from '../pcc-release-audit0.mjs';

function childFailureMessage0(child) {
  return [
    child.error?.message ?? '',
    child.stderr ?? '',
    child.stdout ?? '',
  ].filter((entry) => entry.length > 0).join('\n');
}

test('CheckReleaseAudit0 freezes ReleaseAudit0NF key surface', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runMaterializedPublicStatusGate: false,
  }));

  assert.equal(out.tag, 'accept');
  assert.deepEqual(Object.keys(out.NF), RELEASE_AUDIT_NF_KEYS0);
  assert.deepEqual(Object.keys(out.NF.materializedPublicStatusGateSummary), RELEASE_AUDIT_MATERIALIZED_GATE_SUMMARY_KEYS0);

  const surfaceLedger = out.Ledger.find((entry) => entry.phase === 'surfaceFreeze');

  assert.equal(surfaceLedger.status, 'pass');
});

test('summarizeReleaseAudit0 freezes release audit CLI summary key surface', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runMaterializedPublicStatusGate: false,
  }));

  const summary = summarizeReleaseAudit0(out);

  assert.equal(summary.tag, 'accept');
  assert.deepEqual(Object.keys(summary), RELEASE_AUDIT_CLI_SUMMARY_KEYS0);
  assert.deepEqual(Object.keys(summary.materializedPublicStatusGateSummary), RELEASE_AUDIT_MATERIALIZED_GATE_SUMMARY_KEYS0);
});

test('validateReleaseAuditSurface0 rejects missing NF keys', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runMaterializedPublicStatusGate: false,
  }));

  const bad = {
    ...out.NF,
  };

  delete bad.publicConclusion;

  const result = validateReleaseAuditSurface0(bad);

  assert.equal(result.ok, false);
  assert.deepEqual(result.path, ['NF']);
  assert.equal(result.witness.reason, 'release audit surface keys changed');
  assert.deepEqual(result.witness.detail.missingKeys, ['publicConclusion']);
});

test('validateReleaseAuditSurface0 rejects extra NF keys', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runMaterializedPublicStatusGate: false,
  }));

  const bad = {
    ...out.NF,
    unexpectedReleaseField: true,
  };

  const result = validateReleaseAuditSurface0(bad);

  assert.equal(result.ok, false);
  assert.deepEqual(result.path, ['NF']);
  assert.equal(result.witness.reason, 'release audit surface keys changed');
  assert.deepEqual(result.witness.detail.extraKeys, ['unexpectedReleaseField']);
});

test('validateReleaseAuditCliSummarySurface0 rejects extra summary keys', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runMaterializedPublicStatusGate: false,
  }));

  const summary = {
    ...summarizeReleaseAudit0(out),
    extraSummaryKey: true,
  };

  const result = validateReleaseAuditCliSummarySurface0(summary);

  assert.equal(result.ok, false);
  assert.deepEqual(result.path, ['summary']);
  assert.equal(result.witness.reason, 'release audit surface keys changed');
  assert.deepEqual(result.witness.detail.extraKeys, ['extraSummaryKey']);
});

test('release audit CLI summary emits frozen summary key surface', () => {
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--no-materialized-gate'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.deepEqual(Object.keys(out), RELEASE_AUDIT_CLI_SUMMARY_KEYS0);
  assert.deepEqual(Object.keys(out.materializedPublicStatusGateSummary), RELEASE_AUDIT_MATERIALIZED_GATE_SUMMARY_KEYS0);
});

test('release audit CLI full mode emits frozen NF key surface', () => {
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--no-materialized-gate', '--full'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.deepEqual(Object.keys(out.NF), RELEASE_AUDIT_NF_KEYS0);
  assert.deepEqual(Object.keys(out.NF.materializedPublicStatusGateSummary), RELEASE_AUDIT_MATERIALIZED_GATE_SUMMARY_KEYS0);
});

test('README documents release audit surface freeze', async () => {
  const readme = await fs.readFile(new URL('../README.md', import.meta.url), 'utf8');

  assert.equal(readme.includes('Release audit surface freeze'), true);
  assert.equal(readme.includes('materializedPublicStatusGateDigest'), true);
  assert.equal(readme.includes('materializedPublicStatusGateAcceptedPublicConclusionOnly'), true);
  assert.equal(readme.includes('surfaceFreeze'), true);
});