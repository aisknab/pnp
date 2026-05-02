import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckMaterializedCheckPCCPack0,
  MATERIALIZED_CHECKPCCPACK_PHASES0,
  makeMaterializedCheckPCCPackShell0,
} from '../pcc-materialized-checkpack0.mjs';

import {
  MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
} from '../pcc-materialized-pack0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

test('CheckMaterializedCheckPCCPack0 accepts skeleton fixtures as pending in deferred mode', async () => {
  const out = await CheckMaterializedCheckPCCPack0(makeMaterializedCheckPCCPackShell0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedCheckPCCPack0');
  assert.equal(out.NF.kind, 'MaterializedCheckPCCPack0NF');
  assert.deepEqual(out.NF.phaseOrder, MATERIALIZED_CHECKPCCPACK_PHASES0);
  assert.equal(out.NF.status, 'pending');
  assert.equal(out.NF.accepted, false);
  assert.equal(out.NF.strict, false);
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.checkerBoundary, 'CheckPCCPackexp');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedCheckPCCPack0 rejects skeleton fixtures in strict mode', async () => {
  const out = await CheckMaterializedCheckPCCPack0(makeMaterializedCheckPCCPackShell0(), {
    mode: 'strict',
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedCheckPCCPack0');
  assert.equal(out.Coord, 'CheckMaterializedCheckPCCPack0.CheckPCCPackexp');
  assert.deepEqual(out.Path, ['PackObject']);
  assert.equal(
    out.Witness.reason,
    'strict materialized CheckPCCPackexp bridge requires accepted package check',
  );
});

test('CheckMaterializedCheckPCCPack0 accepts when an injected CheckPCCPackexp runner accepts', async () => {
  const packageNF = {
    kind: 'PackSufficiency0NF',
    publicConclusion: {
      ...MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
    },
  };

  const packageRecord = {
    tag: 'accept',
    checker: 'InjectedCheckPCCPackexp0',
    NF: packageNF,
    Digest: digestCanonical0(packageNF),
    Ledger: [],
  };

  const out = await CheckMaterializedCheckPCCPack0(makeMaterializedCheckPCCPackShell0(), {
    packageCheckRunner: async () => packageRecord,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.status, 'accepted');
  assert.equal(out.NF.accepted, true);
  assert.equal(out.NF.strict, false);
  assert.equal(out.NF.pendingReason, null);
  assert.deepEqual(out.NF.publicClaimBoundary, MATERIALIZED_PACK_PUBLIC_BOUNDARY0);
});

test('CheckMaterializedCheckPCCPack0 rejects an accepted package record with wrong public boundary', async () => {
  const packageNF = {
    kind: 'PackSufficiency0NF',
    publicConclusion: {
      antecedent: MATERIALIZED_PACK_PUBLIC_BOUNDARY0.antecedent,
      consequent: 'P != NP',
      conditional: true,
    },
  };

  const packageRecord = {
    tag: 'accept',
    checker: 'InjectedCheckPCCPackexp0',
    NF: packageNF,
    Digest: digestCanonical0(packageNF),
    Ledger: [],
  };

  const out = await CheckMaterializedCheckPCCPack0(makeMaterializedCheckPCCPackShell0(), {
    packageCheckRunner: async () => packageRecord,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedCheckPCCPack0');
  assert.equal(out.Coord, 'CheckMaterializedCheckPCCPack0.acceptedPackage');
  assert.deepEqual(out.Path, ['CheckPCCPackexp', 'NF', 'publicConclusion']);
});

test('CheckMaterializedCheckPCCPack0 rejects invalid bridge mode', async () => {
  const out = await CheckMaterializedCheckPCCPack0(makeMaterializedCheckPCCPackShell0(), {
    mode: 'bad-mode',
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckMaterializedCheckPCCPack0.config');
  assert.deepEqual(out.Path, ['mode']);
});