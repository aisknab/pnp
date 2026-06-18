import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckReleaseAudit0,
  makeReleaseAuditConfig0,
} from '../pcc-release-audit0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

function makeGateAcceptRecord0(overrides = {}) {
  const nf = {
    kind: 'MaterializedPublicStatusRoundtrip0NF',
    checker: 'CheckMaterializedPublicStatusRoundtrip0',
    version: 0,
    outputDir: 'synthetic-negative-fixture',
    canonicalEnvelopeBytes: false,
    deterministic: true,
    fileCount: 4,
    byteComparisons: [
      {
        filename: 'MaterializedPCCPack0.json',
      },
      {
        filename: 'MaterializedAcceptRun.pending0.json',
      },
      {
        filename: 'MaterializedAcceptRun.reject0.json',
      },
      {
        filename: 'MaterializedAcceptRun.accepted0.json',
      },
    ],
    directRecords: [
      {
        checker: 'CheckMaterializedAggregateFile0',
      },
      {
        checker: 'CheckMaterializedPublicStatusFile0',
        status: 'pending',
      },
      {
        checker: 'CheckMaterializedPublicStatusFile0',
        status: 'rejected',
      },
      {
        checker: 'CheckMaterializedPublicStatusFile0',
        status: 'accepted',
      },
    ],
    cliRecords: [
      {
        checker: 'CLI.check-materialized-aggregate0',
      },
      {
        checker: 'CLI.check-materialized-public-status0.pending',
        status: 'pending',
      },
      {
        checker: 'CLI.check-materialized-public-status0.rejected',
        status: 'rejected',
      },
      {
        checker: 'CLI.check-materialized-public-status0.accepted',
        status: 'accepted',
      },
    ],
    acceptedPublicConclusionOnly: true,
    syntheticRunAll: false,
    materializedPath: true,
    ...overrides,
  };

  return {
    tag: 'accept',
    kind: 'accept',
    checker: 'CheckMaterializedPublicStatusRoundtrip0',
    version: 0,
    NF: nf,
    Digest: digestCanonical0(nf),
    Ledger: [],
    nf,
    digest: digestCanonical0(nf),
    ledger: [],
  };
}

async function runReleaseAuditWithGateRecord0(record, overrides = {}) {
  return CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runMaterializedPublicStatusGate: true,
    materializedPublicStatusGateRunCliChecks: true,
    materializedPublicStatusGateRunner: async () => record,
    ...overrides,
  }));
}

test('CheckReleaseAudit0 rejects materialized gate accept record with wrong NF kind', async () => {
  const out = await runReleaseAuditWithGateRecord0(makeGateAcceptRecord0({
    kind: 'WrongMaterializedGateNF',
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.materializedPublicStatusGate');
  assert.deepEqual(out.Path, ['materializedPublicStatusGate', 'NF', 'kind']);
  assert.equal(out.Witness.reason, 'materialized public status roundtrip gate emitted the wrong NF kind');
});

test('CheckReleaseAudit0 rejects materialized gate accept record without deterministic bytes', async () => {
  const out = await runReleaseAuditWithGateRecord0(makeGateAcceptRecord0({
    deterministic: false,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.materializedPublicStatusGate');
  assert.deepEqual(out.Path, ['materializedPublicStatusGate', 'NF', 'deterministic']);
  assert.equal(out.Witness.reason, 'materialized public status roundtrip gate must prove deterministic fixture bytes');
});

test('CheckReleaseAudit0 rejects materialized gate accept record that is not materializedPath=true', async () => {
  const out = await runReleaseAuditWithGateRecord0(makeGateAcceptRecord0({
    materializedPath: false,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.materializedPublicStatusGate');
  assert.deepEqual(out.Path, ['materializedPublicStatusGate', 'NF', 'materializedPath']);
  assert.equal(out.Witness.reason, 'materialized public status roundtrip gate must certify materializedPath=true');
});

test('CheckReleaseAudit0 rejects materialized gate accept record that falls back to synthetic RunAll0', async () => {
  const out = await runReleaseAuditWithGateRecord0(makeGateAcceptRecord0({
    syntheticRunAll: true,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.materializedPublicStatusGate');
  assert.deepEqual(out.Path, ['materializedPublicStatusGate', 'NF', 'syntheticRunAll']);
  assert.equal(out.Witness.reason, 'materialized public status roundtrip gate must remain separate from synthetic RunAll0');
});

test('CheckReleaseAudit0 rejects materialized gate accept record that does not prove accepted-only public conclusion', async () => {
  const out = await runReleaseAuditWithGateRecord0(makeGateAcceptRecord0({
    acceptedPublicConclusionOnly: false,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.materializedPublicStatusGate');
  assert.deepEqual(out.Path, ['materializedPublicStatusGate', 'NF', 'acceptedPublicConclusionOnly']);
  assert.equal(out.Witness.reason, 'materialized public status roundtrip gate must prove only accepted replay emits the public conclusion');
});

test('CheckReleaseAudit0 rejects materialized gate accept record with too few checked files', async () => {
  const out = await runReleaseAuditWithGateRecord0(makeGateAcceptRecord0({
    fileCount: 3,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.materializedPublicStatusGate');
  assert.deepEqual(out.Path, ['materializedPublicStatusGate', 'NF', 'fileCount']);
  assert.equal(out.Witness.reason, 'materialized public status roundtrip gate must check the package plus all public status fixtures');
});

test('CheckReleaseAudit0 rejects materialized gate accept record with missing direct records', async () => {
  const out = await runReleaseAuditWithGateRecord0(makeGateAcceptRecord0({
    directRecords: [
      {
        checker: 'CheckMaterializedAggregateFile0',
      },
    ],
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.materializedPublicStatusGate');
  assert.deepEqual(out.Path, ['materializedPublicStatusGate', 'NF', 'directRecords']);
  assert.equal(out.Witness.reason, 'materialized public status roundtrip gate must include direct checker records');
});

test('CheckReleaseAudit0 rejects materialized gate accept record with missing CLI records when CLI checks are enabled', async () => {
  const out = await runReleaseAuditWithGateRecord0(makeGateAcceptRecord0({
    cliRecords: [],
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.materializedPublicStatusGate');
  assert.deepEqual(out.Path, ['materializedPublicStatusGate', 'NF', 'cliRecords']);
  assert.equal(out.Witness.reason, 'materialized public status roundtrip gate must include CLI checker records when CLI checks are enabled');
});

test('CheckReleaseAudit0 permits skipped CLI records when materialized gate CLI checks are disabled', async () => {
  const out = await runReleaseAuditWithGateRecord0(
    makeGateAcceptRecord0({
      cliRecords: [],
    }),
    {
      materializedPublicStatusGateRunCliChecks: false,
    },
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckReleaseAudit0');

  const gateLedger = out.Ledger.find((entry) => entry.phase === 'materializedPublicStatusGate');

  assert.equal(gateLedger.status, 'pass');
});