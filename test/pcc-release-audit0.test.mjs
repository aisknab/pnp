import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  CheckReleaseAudit0,
  RELEASE_AUDIT_REQUIRED_MODULES0,
  RELEASE_AUDIT_REQUIRED_TESTS0,
} from '../pcc-release-audit0.mjs';

test('CheckReleaseAudit0 accepts the current release surface', async () => {
  const out = await CheckReleaseAudit0();

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.NF.kind, 'ReleaseAudit0NF');
  assert.equal(out.NF.moduleCount, RELEASE_AUDIT_REQUIRED_MODULES0.length);
  assert.equal(out.NF.testCount, RELEASE_AUDIT_REQUIRED_TESTS0.length);
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('release audit CLI emits an accepted summary', () => {
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, child.stderr);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.moduleCount, RELEASE_AUDIT_REQUIRED_MODULES0.length);
  assert.equal(out.testCount, RELEASE_AUDIT_REQUIRED_TESTS0.length);
  assert.equal(out.publicConclusion.consequent, 'P = NP');
  assert.match(out.digest.hex, /^[0-9a-f]{64}$/);
});

test('release audit CLI full mode emits the complete accept record', () => {
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--full'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, child.stderr);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.NF.kind, 'ReleaseAudit0NF');
  assert.equal(Array.isArray(out.Ledger), true);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});