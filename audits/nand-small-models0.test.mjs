import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckNANDSmallModels0,
} from '../pcc-nand-small-models0.mjs';

import {
  enumerateNANDWords0,
  RunNANDSmallModelAudit0,
} from '../semantics/nand-small-models.mjs';

import {
  flattenedTruthTable0,
  makeBoundarySource0,
  makeNANDWord0,
  validateNANDWord0,
} from '../semantics/nand-direct-wire-reference.mjs';

async function loadConfig0() {
  const text = await readFile(new URL('../semantics/nand-small-models-config.json', import.meta.url), 'utf8');
  return JSON.parse(text);
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('NAND small-model checker accepts current config', async () => {
  const out = await CheckNANDSmallModels0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-NAND-SMALL-MODELS-2026-06-27-01');
  assert.equal(out.semanticsCoordinate, 'PNP-NAND-DIRECT-WIRE-SEMANTICS-2026-06-27-01');
  assert.equal(out.smallModelsReady, true);
  assert.equal(out.fullSmallModelCoverageProved, false);
  assert.deepEqual(out.boundarySizes, [0, 1, 2]);
  assert.equal(out.maxGates, 2);
  assert.equal(out.outputArity, 1);
  assert.ok(out.wordCount > 0);
  assert.ok(out.truthClassCount > 0);
  assert.ok(out.equivalenceReplacementChecks > 0);
  assert.ok(out.nonEquivalenceRejectChecks > 0);
  assert.equal(out.futureGateRejectChecked, true);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('NAND small-model audit is exhaustive inside configured seed bounds', () => {
  const out = RunNANDSmallModelAudit0({ boundarySizes: [0, 1, 2], maxGates: 2 });

  assert.equal(out.tag, 'accept');
  assert.equal(out.boundarySizes.length, 3);
  assert.equal(out.families.length, 3);
  assert.ok(out.wordCount >= out.truthClassCount);
  assert.ok(out.families.every((family) => family.wordCount > 0));
});

test('NAND small-model enumerator generates validated words with deterministic truth tables', () => {
  const words = enumerateNANDWords0({ boundary: ['x0', 'x1'], maxGates: 1 });

  assert.ok(words.length > 0);
  for (const word of words) {
    assert.equal(validateNANDWord0(word).tag, 'accept');
    const first = flattenedTruthTable0(word);
    const second = flattenedTruthTable0(word);
    assert.equal(first.tag, 'accept');
    assert.deepEqual(first.bits, second.bits);
  }
});

test('NAND small-model checker rejects public theorem activation', async () => {
  const config = clone0(await loadConfig0());
  config.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckNANDSmallModels0({
    configOverride: config,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NANDSmallModels.PublicEmission');
  assert.deepEqual(out.path, ['claimBoundary', 'publicTheoremEmissionAllowed']);
});

test('NAND small-model checker rejects full coverage overclaim', async () => {
  const config = clone0(await loadConfig0());
  config.fullSmallModelCoverageProved = true;

  const out = await CheckNANDSmallModels0({
    configOverride: config,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NANDSmallModels.FullCoverageFlag');
  assert.deepEqual(out.path, ['fullSmallModelCoverageProved']);
});

test('NAND small-model checker rejects changed seed bounds', async () => {
  const config = clone0(await loadConfig0());
  config.maxGates = 3;

  const out = await CheckNANDSmallModels0({
    configOverride: config,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NANDSmallModels.MaxGates');
});

test('NAND small-model audit rejects malformed generated future gate when checked directly', () => {
  const malformed = makeNANDWord0({
    boundary: ['x0'],
    gates: [{ id: 'g0', op: 'NAND', left: { kind: 'gate', id: 'future' }, right: makeBoundarySource0('x0') }],
    outputs: [{ kind: 'gate', id: 'g0' }],
  });

  assert.equal(validateNANDWord0(malformed).tag, 'reject');
});
