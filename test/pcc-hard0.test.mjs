import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckHard0,
  HARD_CHECKER_FIELDS0,
  HARD_FORBIDDEN_SYMBOLS0,
  HARD_ROWKEY_FIELDS0,
  makeSyntheticHardCheck0,
} from '../pcc-hard0.mjs';

test('CheckHard0 accepts the synthetic hardened checker suite', async () => {
  const out = await CheckHard0(makeSyntheticHardCheck0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckHard0');
  assert.equal(out.NF.kind, 'HardCheck0NF');
  assert.equal(out.NF.checkerCount, HARD_CHECKER_FIELDS0.length);
  assert.deepEqual(out.NF.rowKeyFields, HARD_ROWKEY_FIELDS0);
  assert.deepEqual(out.NF.forbiddenSymbols, HARD_FORBIDDEN_SYMBOLS0);
  assert.equal(out.Digest.alg, 'SHA256');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckHard0 rejects a missing checker descriptor', async () => {
  const hard = makeSyntheticHardCheck0();

  delete hard.NoMinCheck;

  const out = await CheckHard0(hard);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckHard0');
  assert.equal(out.Coord, 'CheckHard0.input');
  assert.deepEqual(out.Path, ['NoMinCheck']);
  assert.equal(out.Witness.reason, 'HardCheck0 is missing a required checker descriptor');
});

test('CheckHard0 rejects a descriptor with unknown output enabled', async () => {
  const hard = makeSyntheticHardCheck0();

  hard.DiagCheck = {
    ...hard.DiagCheck,
    noUnknown: false,
  };

  const out = await CheckHard0(hard);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckHard0');
  assert.equal(out.Coord, 'CheckHard0.checkers');
  assert.deepEqual(out.Path, ['DiagCheck', 'noUnknown']);
  assert.equal(out.Witness.reason, 'checker descriptor flag noUnknown must be true');
});

test('CheckHard0 rejects route priorities that downgrade Gain', async () => {
  const hard = makeSyntheticHardCheck0();

  hard.RouteCheck = {
    ...hard.RouteCheck,
    priority: [
      'Neutral',
      'Gain',
      'Minimum',
      'ZeroSlack',
      'NoBudget',
      'NoHereditary',
      'SelectorSilent',
      'Faithful',
      'Token',
      'Reject',
    ],
  };

  const out = await CheckHard0(hard);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckHard0');
  assert.equal(out.Coord, 'CheckHard0.RouteCheck');
  assert.deepEqual(out.Path, ['RouteCheck', 'priority', 0]);
  assert.equal(out.Witness.reason, 'RouteCheck must give Gain highest priority');
});

test('CheckHard0 rejects hash protocols that rely on hash equality alone', async () => {
  const hard = makeSyntheticHardCheck0();

  hard.HashCheck = {
    ...hard.HashCheck,
    fullKeyCompareAfterHash: false,
    canonicalByteCompareAfterHash: false,
  };

  const out = await CheckHard0(hard);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckHard0');
  assert.equal(out.Coord, 'CheckHard0.HashCheck');
  assert.deepEqual(out.Path, ['HashCheck', 'fullKeyCompareAfterHash']);
  assert.equal(out.Witness.reason, 'HashCheck must compare full keys or canonical bytes after hash lookup');
});

test('CheckHard0 rejects a no-hidden-min checker missing a forbidden alias', async () => {
  const hard = makeSyntheticHardCheck0();

  hard.NoMinCheck = {
    ...hard.NoMinCheck,
    forbiddenSymbols: hard.NoMinCheck.forbiddenSymbols.filter((symbol) => symbol !== 'minimumEquivalent'),
  };

  const out = await CheckHard0(hard);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckHard0');
  assert.equal(out.Coord, 'CheckHard0.NoMinCheck');
  assert.deepEqual(out.Path, ['NoMinCheck', 'forbiddenSymbols', 'minimumEquivalent']);
  assert.equal(out.Witness.reason, 'NoMinCheck is missing a forbidden minimization symbol or alias');
});

test('CheckHard0 rejects executable hidden minimization use after descriptor validation', async () => {
  const hard = makeSyntheticHardCheck0();

  hard.DiagCheck = {
    ...hard.DiagCheck,
    body: [
      'minimumEquivalent',
    ],
  };

  const out = await CheckHard0(hard);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckHard0');
  assert.equal(out.Coord, 'CheckHard0.noHiddenMin');
  assert.deepEqual(out.Path, ['HardCheck0', 'DiagCheck', 'body', 0]);
  assert.equal(out.Witness.reason, 'forbidden minimization symbol appears in executable position');
});

test('CheckHard0 rejects a proof-reference checker that permits opaque proof blobs', async () => {
  const hard = makeSyntheticHardCheck0();

  hard.ProofRefCheck = {
    ...hard.ProofRefCheck,
    rejectsOpaque: false,
  };

  const out = await CheckHard0(hard);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckHard0');
  assert.equal(out.Coord, 'CheckHard0.ProofRefCheck');
  assert.deepEqual(out.Path, ['ProofRefCheck', 'rejectsOpaque']);
  assert.equal(out.Witness.reason, 'ProofRefCheck must reject opaque proof blobs');
});

test('CheckHard0 rejects an import checker missing a forbidden import edge', async () => {
  const hard = makeSyntheticHardCheck0();

  hard.ImportCheck = {
    ...hard.ImportCheck,
    forbiddenEdges: hard.ImportCheck.forbiddenEdges.filter((edge) => !(edge[0] === 'O' && edge[1] === 'G')),
  };

  const out = await CheckHard0(hard);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckHard0');
  assert.equal(out.Coord, 'CheckHard0.ImportCheck');
  assert.deepEqual(out.Path, ['ImportCheck', 'forbiddenEdges']);
  assert.equal(out.Witness.reason, 'ImportCheck is missing a forbidden import edge');
});

test('CheckHard0 rejects non-polynomial bounds descriptors', async () => {
  const hard = makeSyntheticHardCheck0();

  hard.BoundsCheck = {
    ...hard.BoundsCheck,
    polynomialBounds: false,
  };

  const out = await CheckHard0(hard);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckHard0');
  assert.equal(out.Coord, 'CheckHard0.BoundsCheck');
  assert.deepEqual(out.Path, ['BoundsCheck', 'polynomialBounds']);
  assert.equal(out.Witness.reason, 'BoundsCheck must enforce polynomial bounds');
});

test('CheckHard0 rejects opaque proof material anywhere in HardCheck0', async () => {
  const hard = makeSyntheticHardCheck0();

  hard.PiHard = {
    ...hard.PiHard,
    opaqueProof: {
      bytes: 'not allowed',
    },
  };

  const out = await CheckHard0(hard);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckHard0');
  assert.equal(out.Coord, 'CheckHard0.opaqueProof');
  assert.deepEqual(out.Path, ['HardCheck0', 'PiHard', 'opaqueProof']);
});