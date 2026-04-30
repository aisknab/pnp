import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckReleaseAudit0,
  makeReleaseAuditConfig0,
} from '../pcc-release-audit0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

test('CheckReleaseAudit0 executes the materialized public status roundtrip gate', async (t) => {
  const outputDir = await makeTempDir0(t);

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runMaterializedPublicStatusGate: true,
    materializedPublicStatusGateOutputDir: outputDir,
    materializedPublicStatusGateRunCliChecks: true,
  }));

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.NF.materializedPublicStatusGate, true);

  const gateLedger = out.Ledger.find((entry) => entry.phase === 'materializedPublicStatusGate');

  assert.equal(gateLedger.status, 'pass');
  assert.match(gateLedger.digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckReleaseAudit0 rejects when the materialized public status roundtrip gate rejects', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runMaterializedPublicStatusGate: true,
    materializedPublicStatusGateRunner: async () => ({
      tag: 'reject',
      kind: 'reject',
      checker: 'BadMaterializedPublicStatusGate0',
      Coord: 'BadMaterializedPublicStatusGate0.firstFailure',
      Path: [
        'Fixture',
      ],
      Witness: {
        reason: 'synthetic materialized gate failure',
      },
      Digest: digestCanonical0({
        kind: 'BadMaterializedPublicStatusGate0RejectNF',
      }),
      Ledger: [],
    }),
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.materializedPublicStatusGate');
  assert.deepEqual(out.Path, ['materializedPublicStatusGate']);
  assert.equal(out.Witness.reason, 'materialized public status roundtrip gate rejected');
  assert.equal(out.Witness.detail.inner.coord, 'BadMaterializedPublicStatusGate0.firstFailure');
});

test('CheckReleaseAudit0 can explicitly skip the materialized public status roundtrip gate', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runMaterializedPublicStatusGate: false,
  }));

  assert.equal(out.tag, 'accept');

  const gateLedger = out.Ledger.find((entry) => entry.phase === 'materializedPublicStatusGate');

  assert.equal(gateLedger.status, 'pass');
});

test('CheckReleaseAudit0 validates materialized public status gate config shape', async () => {
  const out = await CheckReleaseAudit0({
    ...makeReleaseAuditConfig0(),
    runMaterializedPublicStatusGate: 'yes',
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.input');
  assert.deepEqual(out.Path, ['runMaterializedPublicStatusGate']);
  assert.equal(out.Witness.reason, 'ReleaseAuditConfig0 runMaterializedPublicStatusGate must be boolean');
});

test('README documents release audit materialized gate flags', async () => {
  const readme = await fs.readFile(new URL('../README.md', import.meta.url), 'utf8');

  assert.equal(readme.includes('Release audit materialized gate flags'), true);
  assert.equal(readme.includes('npm run release:audit -- --materialized-gate'), true);
  assert.equal(readme.includes('npm run release:audit -- --no-materialized-gate'), true);
  assert.equal(readme.includes('--materialized-gate-out'), true);
  assert.equal(readme.includes('--no-materialized-gate-cli'), true);
  assert.equal(readme.includes('separate from synthetic `RunAll0`'), true);
});

async function makeTempDir0(t) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-release-audit-materialized-gate-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  return dir;
}