import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckMaterializedPCCPackShell0,
  MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
  MATERIALIZED_PACK_REQUIRED_CHECKS0,
  canonicalBytesForMaterializedObject0,
  makeMaterializedPCCPackShell0,
  sha256Utf8DigestRecord0,
} from '../pcc-materialized-pack0.mjs';

test('CheckMaterializedPCCPackShell0 accepts a concrete materialized package shell', async () => {
  const out = await CheckMaterializedPCCPackShell0(makeMaterializedPCCPackShell0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShell0');
  assert.equal(out.NF.kind, 'MaterializedPCCPackShell0NF');
  assert.equal(out.NF.envelopeOnly, true);
  assert.deepEqual(out.NF.requiredChecks, MATERIALIZED_PACK_REQUIRED_CHECKS0);
  assert.deepEqual(out.NF.publicClaimBoundary, MATERIALIZED_PACK_PUBLIC_BOUNDARY0);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedPCCPackShell0 rejects CoreDigest mismatch', async () => {
  const shell = makeMaterializedPCCPackShell0();

  shell.CoreDigest = {
    ...shell.CoreDigest,
    hex: '0000000000000000000000000000000000000000000000000000000000000000',
  };

  const out = await CheckMaterializedPCCPackShell0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShell0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPackShell0.canonicalBytes');
  assert.deepEqual(out.Path, ['CoreDigest']);
  assert.equal(out.Witness.reason, 'CoreDigest must be SHA256 over CoreBytes');
});

test('CheckMaterializedPCCPackShell0 rejects PackDigest mismatch', async () => {
  const shell = makeMaterializedPCCPackShell0();

  shell.PackDigest = {
    ...shell.PackDigest,
    hex: '1111111111111111111111111111111111111111111111111111111111111111',
  };

  const out = await CheckMaterializedPCCPackShell0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShell0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPackShell0.canonicalBytes');
  assert.deepEqual(out.Path, ['PackDigest']);
  assert.equal(out.Witness.reason, 'PackDigest must be SHA256 over PackBytes');
});

test('CheckMaterializedPCCPackShell0 rejects non-canonical CoreBytes', async () => {
  const shell = makeMaterializedPCCPackShell0();

  shell.CoreBytes = JSON.stringify({
    z: 1,
    a: 2,
  });

  shell.CoreDigest = sha256Utf8DigestRecord0(shell.CoreBytes);

  const out = await CheckMaterializedPCCPackShell0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShell0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPackShell0.canonicalBytes');
  assert.deepEqual(out.Path, ['CoreBytes']);
  assert.equal(out.Witness.reason, 'CoreBytes must be canonical JSON bytes');
});

test('CheckMaterializedPCCPackShell0 rejects embedded AcceptRun in CoreBytes', async () => {
  const shell = makeMaterializedPCCPackShell0();

  const badCore = {
    kind: 'PCCCorePackage0',
    version: 0,
    AcceptRun: {
      kind: 'AcceptRun0',
    },
  };

  shell.CoreBytes = canonicalBytesForMaterializedObject0(badCore);
  shell.CoreDigest = sha256Utf8DigestRecord0(shell.CoreBytes);

  const out = await CheckMaterializedPCCPackShell0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShell0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPackShell0.canonicalBytes');
  assert.deepEqual(out.Path, ['CoreBytes']);
  assert.equal(out.Witness.reason, 'materialized core bytes must not embed AcceptRun');
});

test('CheckMaterializedPCCPackShell0 rejects synthetic text in shell values', async () => {
  const shell = makeMaterializedPCCPackShell0();

  shell.Manifest = {
    ...shell.Manifest,
    label: 'sched.synthetic',
  };

  const out = await CheckMaterializedPCCPackShell0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShell0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPackShell0.materialized');
  assert.equal(out.Witness.reason, 'CheckMaterialized0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterialized0.scan');
});

test('CheckMaterializedPCCPackShell0 rejects digest-only equality policy', async () => {
  const shell = makeMaterializedPCCPackShell0();

  shell.CanonicalBytePolicy = {
    ...shell.CanonicalBytePolicy,
    digestEqualityIsNotObjectEquality: false,
  };

  const out = await CheckMaterializedPCCPackShell0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShell0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPackShell0.canonicalBytePolicy');
  assert.deepEqual(out.Path, ['CanonicalBytePolicy', 'digestEqualityIsNotObjectEquality']);
  assert.equal(out.Witness.reason, 'CanonicalBytePolicy must certify digestEqualityIsNotObjectEquality');
});

test('CheckMaterializedPCCPackShell0 rejects a missing future check phase', async () => {
  const shell = makeMaterializedPCCPackShell0();

  shell.CheckPlan = {
    ...shell.CheckPlan,
    phases: shell.CheckPlan.phases.filter((phase) => phase !== 'ReplayAcceptRun0'),
  };

  const out = await CheckMaterializedPCCPackShell0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShell0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPackShell0.checkPlan');
  assert.deepEqual(out.Path, ['CheckPlan', 'phases', 'ReplayAcceptRun0']);
  assert.equal(out.Witness.reason, 'CheckPlan is missing a required future check phase');
});

test('CheckMaterializedPCCPackShell0 rejects non-conditional public claim boundary', async () => {
  const shell = makeMaterializedPCCPackShell0();

  shell.PublicClaimBoundary = {
    ...shell.PublicClaimBoundary,
    conditional: false,
  };

  const out = await CheckMaterializedPCCPackShell0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShell0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPackShell0.publicClaimBoundary');
  assert.deepEqual(out.Path, ['PublicClaimBoundary', 'conditional']);
  assert.equal(out.Witness.reason, 'PublicClaimBoundary must be conditional');
});