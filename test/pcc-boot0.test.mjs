import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  BOOT_BATCH0_REQUIRED_ROWS,
  CheckBoot0,
  CheckBootAudit0,
  CheckBootBatch0,
  makeBootRow0,
  makeBootstrapB0Rows0,
} from '../pcc-boot0.mjs';

import {
  makeAuditCase,
  makeRejectCase,
} from '../pcc-verifier-frag0.mjs';

function makeSyntheticBoot0(overrides = {}) {
  const rows = makeBootstrapB0Rows0();

  return {
    kind: 'Boot0',
    version: 0,

    ByteLang0: {
      kind: 'ByteLang0',
      version: 0,
      tags: {
        Boot0: 0x0001,
        BootBatch0: 0x0002,
        Row0: 0x0003,
        Digest0: 0x0004,
      },
      sorts: {
        Unit: 'Unit',
        Name: 'Name',
        Record: 'Record',
        Row: 'Row',
      },
      constructors: {
        accept: 'accept',
        reject: 'reject',
        row: 'row',
      },
      records: {
        Boot0: 9,
        BootBatch0: 3,
        Row0: 12,
      },
    },

    Codec0: {
      kind: 'Codec0',
      version: 0,
      canonical: true,
    },

    Digest0: {
      kind: 'Digest0',
      version: 0,
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
    },

    IfaceDict0: {
      kind: 'IfaceDict0',
      version: 0,
      forbiddenSymbols: [
        'µ',
        'µ*',
        'µ#',
        'Can',
        'argmin',
        'maxG',
        'minimumEquivalent',
        'optimalCircuit',
        'exactMinSearch',
        'canonicalMinimizer',
        'maximizeGain',
      ],
      publicConstructors: [
        'Gain',
        'Minimum',
        'ZeroSlack',
        'NoBudget',
        'NoHereditary',
        'SelectorSilent',
        'Faithful',
        'Token',
      ],
    },

    Sched0: {
      kind: 'Sched0',
      version: 0,
      core: {
        B0: 64,
        K0: 512,
        R0: 64,
        H0: 128,
        O0: 64,
        Rel0: 16,
      },
    },

    KernelSeed0: {
      kind: 'KernelSeed0',
      version: 0,
      rules: [
        'Eq',
        'Subst',
        'Record',
        'DAGInd',
        'LedgerInd',
        'OblTopoInd',
        'TraceInd',
        'FiniteExhaust',
        'DPInd',
        'Hall',
        'RankInd',
        'MinCounterexample',
        'IntArith',
        'Transport',
        'TruthVec',
        'FiniteRel',
      ],
    },

    B0: {
      kind: 'BootBatch0',
      version: 0,
      batchId: 'B0',
      rows,
    },

    BootAudit0: {
      kind: 'VerifierFrag0',
      version: 0,
      suiteId: 'boot0.synthetic.audit',
      cases: [
        makeAuditCase({
          id: 'boot.audit.positive',
          target: 'BootAudit0',
          run: () => {
            assert.equal(2 + 2, 4);
          },
        }),
        makeRejectCase({
          id: 'boot.audit.negative',
          target: 'BootAudit0',
          run: () => ({
            tag: 'reject',
            coord: 'synthetic.negative',
          }),
        }),
      ],
    },

    PiBoot: {
      kind: 'PiBoot0',
      version: 0,
      refs: [],
      note: 'synthetic bootstrap proof marker',
    },

    ...overrides,
  };
}

test('CheckBootBatch0 accepts a correctly shaped B0 batch', async () => {
  const boot = makeSyntheticBoot0();
  const out = await CheckBootBatch0(boot.B0);
  const rows = makeBootstrapB0Rows0();

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckBootBatch0');
  assert.equal(out.NF.batchId, 'B0');
  assert.equal(out.NF.rowCount, BOOT_BATCH0_REQUIRED_ROWS.length);
  assert.equal(out.Digest.alg, 'SHA256');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckBootAudit0 accepts a runnable VerifierFrag0 audit suite', async () => {
  const boot = makeSyntheticBoot0();
  const out = await CheckBootAudit0(boot.BootAudit0);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckBootAudit0');
  assert.equal(out.NF.auditKind, 'suite');
  assert.equal(out.NF.caseCount, 2);
});

test('CheckBoot0 accepts the synthetic bootstrap seed', async () => {
  const boot = makeSyntheticBoot0();
  const out = await CheckBoot0(boot);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckBoot0');
  assert.equal(out.NF.kind, 'Boot0NF');
  assert.equal(out.NF.rowCount, BOOT_BATCH0_REQUIRED_ROWS.length);
  assert.equal(out.NF.kernelRuleCount, 16);
  assert.deepEqual(out.NF.scheduleCore, {
    B0: 64,
    K0: 512,
    R0: 64,
    H0: 128,
    O0: 64,
    Rel0: 16,
  });
});

test('CheckBoot0 rejects a bad schedule constant at the first schedule coordinate', async () => {
  const boot = makeSyntheticBoot0({
    Sched0: {
      kind: 'Sched0',
      version: 0,
      core: {
        B0: 63,
        K0: 512,
        R0: 64,
        H0: 128,
        O0: 64,
        Rel0: 16,
      },
    },
  });

  const out = await CheckBoot0(boot);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckBoot0.Sched0');
  assert.deepEqual(out.Path, ['Sched0', 'core', 'B0']);
  assert.equal(out.Witness.reason, 'Sched0 core constant mismatch');
});

test('CheckBootBatch0 rejects duplicate RowKey records with conflicting routes', async () => {
  const first = makeBootRow0({
    PackageID: 'BHash',
    SchemaID: 'HashProtocolRow',
    KindKey: 'hash-protocol',
    ArityKey: 1,
    SelectedRoute: 'Accept',
  });

  const second = {
    ...first,
    SelectedRoute: 'Reject',
    ActiveRouteSet: ['Reject'],
    CandidateRoutes: ['Accept', 'Reject'],
  };

  const out = await CheckBootBatch0({
    kind: 'BootBatch0',
    version: 0,
    batchId: 'B0',
    rows: [
      first,
      second,
    ],
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckBootBatch0.duplicateRows');
  assert.equal(out.Witness.reason, 'duplicate row conflict');
});

test('CheckBootAudit0 rejects a failing audit suite', async () => {
  const out = await CheckBootAudit0({
    kind: 'VerifierFrag0',
    version: 0,
    suiteId: 'boot0.synthetic.bad-audit',
    cases: [
      makeAuditCase({
        id: 'boot.audit.fail',
        target: 'BootAudit0',
        run: () => {
          assert.equal(1, 2);
        },
      }),
    ],
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckBootAudit0.audit');
  assert.equal(out.Witness.reason, 'VerifierFrag0 audit rejected');
});