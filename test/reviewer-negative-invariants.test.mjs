import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  REVIEWER_NEGATIVE_INVARIANTS0,
} from '../reviewer-negative-invariants.mjs';

import {
  CheckGPack0,
  makeSyntheticGPack0,
} from '../pcc-gpack0.mjs';

import {
  CheckPackSufficiency0,
  makeSyntheticPCCPack0,
} from '../pcc-pack-sufficiency0.mjs';

import {
  COORD,
  MODE,
  SORT,
  TAG,
  bytes,
  checkModeUse0,
  checkRowKey0,
  computeRowKey0,
  concatBytes,
  encodeNat0,
  installDeclarationSchema,
  list,
  makeMinimalBootstrapContext,
  name,
  nat,
  parseTop0,
  record,
} from '../pcc-core.mjs';

assert.deepEqual(REVIEWER_NEGATIVE_INVARIANTS0, [
  'invalid-locked-nand',
  'residual-slack-mismatch',
  'hidden-minimization-attempt',
  'mode-firewall-violation',
  'malformed-pccpack',
  'invalid-zero-slack',
  'hash-mismatch',
  'certificate-parser-mismatch',
]);

function assertCheckerReject(out, {
  checker,
  coord,
  path,
  reason,
}) {
  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, checker);
  assert.equal(out.Coord, coord);
  assert.deepEqual(out.Path, path);
  assert.equal(out.Witness?.reason, reason);
}

function assertCoreError(out, {
  coord,
  path = [],
}) {
  assert.equal(out.kind, 'err');
  assert.equal(out.coord, coord);
  assert.deepEqual(out.path, path);
}

function makeRowWithIncorrectDisplayedHash0() {
  const ctx = makeMinimalBootstrapContext();
  const packageId = 'Iface';
  const schemaId = 'SortDecl';

  installDeclarationSchema(ctx, packageId, schemaId, 'Sort');

  const rawObj = record(0x00030001, [
    name('DemoSort'),
    nat(0n),
  ]);

  const rowKey = computeRowKey0(ctx, {
    PackageID: packageId,
    SchemaID: schemaId,
    RawObj: rawObj,
  });

  const row = record(TAG.Row, [
    name(packageId),
    name(schemaId),
    rawObj,
    rawObj,
    rowKey,
    name('TransportId'),
    list(TAG.List, [name('AcceptDecl'), name('RejectMalformed')]),
    list(TAG.List, [name('AcceptDecl')]),
    name('AcceptDecl'),
    name('ProofRef.SortDeclWellTyped'),
    name('BoundsRef.BootFinite'),
    bytes(new Uint8Array(32)),
  ], SORT.Row);

  return { ctx, row };
}

test('reviewer negative: invalid locked NAND rejects final-lock leakage', async () => {
  const gpack = makeSyntheticGPack0();
  gpack.SepCert = {
    ...gpack.SepCert,
    finalLockOnlyFinal: false,
  };

  const out = await CheckGPack0(gpack);

  assertCheckerReject(out, {
    checker: 'CheckGPack0',
    coord: 'CheckGPack0.sep',
    path: ['SepCert', 'finalLockOnlyFinal'],
    reason: 'SepCert must certify finalLockOnlyFinal',
  });
});

test('reviewer negative: residual-slack mismatch rejects a bound above four', async () => {
  const gpack = makeSyntheticGPack0();
  gpack.ThresholdCert = {
    ...gpack.ThresholdCert,
    residualSlackMax: 5,
  };

  const out = await CheckGPack0(gpack);

  assertCheckerReject(out, {
    checker: 'CheckGPack0',
    coord: 'CheckGPack0.threshold',
    path: ['ThresholdCert', 'residualSlackMax'],
    reason: 'ThresholdCert residual slack must be an integer at most four',
  });
});

test('reviewer negative: expanded hidden-minimization attempt rejects at the executable call', async () => {
  const gpack = makeSyntheticGPack0();
  gpack.NoMinCert = {
    ...gpack.NoMinCert,
    expandedArtifacts: [
      {
        kind: 'GeneratedLockedNANDTemplate0',
        body: ['minimumEquivalent'],
      },
    ],
  };

  const out = await CheckGPack0(gpack);

  assertCheckerReject(out, {
    checker: 'CheckGPack0',
    coord: 'CheckGPack0.noHiddenMin',
    path: ['GPack0', 'NoMinCert', 'expandedArtifacts', 0, 'body', 0],
    reason: 'forbidden minimization symbol appears in executable position',
  });
});

test('reviewer negative: mode firewall rejects quotient equality used as a full replacement', () => {
  const out = checkModeUse0(MODE.QUOT, 'ReplacementEquality');

  assertCoreError(out, {
    coord: COORD.MODE_PROMOTION,
  });
  assert.deepEqual(out.witness, {
    eqMode: MODE.QUOT,
    consumerKind: 'ReplacementEquality',
  });
});

test('reviewer negative: malformed PCCPack rejects a missing required GPack artefact', async () => {
  const pack = makeSyntheticPCCPack0();
  delete pack.GPack;

  const out = await CheckPackSufficiency0(pack);

  assertCheckerReject(out, {
    checker: 'CheckPackSufficiency0',
    coord: 'CheckPackSufficiency0.input',
    path: ['GPack'],
    reason: 'PCCPack0 is missing a required artefact',
  });
  assert.equal(out.Witness.detail?.field, 'GPack');
});

test('reviewer negative: invalid ZeroSlack condition rejects zeroSlackSound=false', async () => {
  const pack = makeSyntheticPCCPack0();
  pack.PackSufficiencyTheorem = {
    ...pack.PackSufficiencyTheorem,
    residualBandMinimization: {
      ...pack.PackSufficiencyTheorem.residualBandMinimization,
      zeroSlackSound: false,
    },
  };

  const out = await CheckPackSufficiency0(pack);

  assertCheckerReject(out, {
    checker: 'CheckPackSufficiency0',
    coord: 'CheckPackSufficiency0.PackSufficiencyTheorem',
    path: ['PackSufficiencyTheorem', 'residualBandMinimization', 'zeroSlackSound'],
    reason: 'residualBandMinimization must certify zeroSlackSound',
  });
});

test('reviewer negative: row-key hash mismatch rejects the displayed digest', () => {
  const { ctx, row } = makeRowWithIncorrectDisplayedHash0();
  const out = checkRowKey0(ctx, row);

  assertCoreError(out, {
    coord: COORD.ROWKEY_HASH_MISMATCH,
  });
  assert.match(out.witness.expectedHash, /^[0-9a-f]{64}$/u);
  assert.equal(out.witness.displayedHash, '0'.repeat(64));
  assert.notEqual(out.witness.expectedHash, out.witness.displayedHash);
});

test('reviewer negative: certificate/parser mismatch rejects a RowKey with arity 16 instead of 17', () => {
  const ctx = makeMinimalBootstrapContext();
  const malformedCertificateBytes = concatBytes(
    encodeNat0(BigInt(TAG.RowKey)),
    encodeNat0(16n),
  );

  const out = parseTop0(ctx, malformedCertificateBytes, SORT.RowKey);

  assertCoreError(out, {
    coord: COORD.PARSE_BAD_ARITY,
  });
  assert.equal(out.witness.tag, TAG.RowKey);
  assert.equal(out.witness.expected, 17);
  assert.equal(out.witness.actual, 16);
});
