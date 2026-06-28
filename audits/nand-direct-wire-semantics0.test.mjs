import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckNANDDirectWireSemantics0,
} from '../pcc-nand-direct-wire-semantics0.mjs';

import {
  compatibleReplacement0,
  equivalentNANDWords0,
  flattenedTruthTable0,
  makeBoundarySource0,
  makeConstSource0,
  makeGateSource0,
  makeNANDWord0,
  sizeOfNANDWord0,
  validateNANDWord0,
} from '../semantics/nand-direct-wire-reference.mjs';

async function loadSpec0() {
  const text = await readFile(new URL('../semantics/nand-direct-wire-spec.json', import.meta.url), 'utf8');
  return JSON.parse(text);
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('NAND direct-wire semantics checker accepts current seed spec', async () => {
  const out = await CheckNANDDirectWireSemantics0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-NAND-DIRECT-WIRE-SEMANTICS-2026-06-27-01');
  assert.equal(out.semanticsReady, true);
  assert.equal(out.fullSemanticsCoverageProved, false);
  assert.ok(out.coveredConceptCount >= 9);
  assert.ok(out.exampleCount >= 6);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('NAND truth tables match NAND, NOT, AND, and constants', () => {
  const nand = makeNANDWord0({
    boundary: ['x', 'y'],
    gates: [{ id: 'g', op: 'NAND', left: makeBoundarySource0('x'), right: makeBoundarySource0('y') }],
    outputs: [makeGateSource0('g')],
  });
  assert.deepEqual(flattenedTruthTable0(nand).bits, [1, 1, 1, 0]);

  const not = makeNANDWord0({
    boundary: ['x'],
    gates: [{ id: 'g', op: 'NAND', left: makeBoundarySource0('x'), right: makeBoundarySource0('x') }],
    outputs: [makeGateSource0('g')],
  });
  assert.deepEqual(flattenedTruthTable0(not).bits, [1, 0]);

  const and = makeNANDWord0({
    boundary: ['x', 'y'],
    gates: [
      { id: 'n', op: 'NAND', left: makeBoundarySource0('x'), right: makeBoundarySource0('y') },
      { id: 'a', op: 'NAND', left: makeGateSource0('n'), right: makeGateSource0('n') },
    ],
    outputs: [makeGateSource0('a')],
  });
  assert.deepEqual(flattenedTruthTable0(and).bits, [0, 0, 0, 1]);

  const constant = makeNANDWord0({ boundary: [], gates: [], outputs: [makeConstSource0(0), makeConstSource0(1)] });
  assert.deepEqual(flattenedTruthTable0(constant).bits, [0, 1]);
  assert.equal(sizeOfNANDWord0(constant).size, 0);
});

test('NAND replacement equivalence accepts commuted AND construction', () => {
  const left = makeNANDWord0({
    boundary: ['x', 'y'],
    gates: [
      { id: 'n', op: 'NAND', left: makeBoundarySource0('x'), right: makeBoundarySource0('y') },
      { id: 'a', op: 'NAND', left: makeGateSource0('n'), right: makeGateSource0('n') },
    ],
    outputs: [makeGateSource0('a')],
  });
  const right = makeNANDWord0({
    boundary: ['x', 'y'],
    gates: [
      { id: 'n', op: 'NAND', left: makeBoundarySource0('y'), right: makeBoundarySource0('x') },
      { id: 'a', op: 'NAND', left: makeGateSource0('n'), right: makeGateSource0('n') },
    ],
    outputs: [makeGateSource0('a')],
  });

  assert.equal(equivalentNANDWords0(left, right).equivalent, true);
  assert.equal(compatibleReplacement0(left, right).tag, 'accept');
});

test('NAND replacement equivalence rejects boundary and truth-table mismatch', () => {
  const nand = makeNANDWord0({
    boundary: ['x', 'y'],
    gates: [{ id: 'g', op: 'NAND', left: makeBoundarySource0('x'), right: makeBoundarySource0('y') }],
    outputs: [makeGateSource0('g')],
  });
  const projection = makeNANDWord0({
    boundary: ['x', 'y'],
    gates: [],
    outputs: [makeBoundarySource0('x')],
  });
  assert.equal(compatibleReplacement0(nand, projection).tag, 'reject');

  const swappedBoundary = makeNANDWord0({
    boundary: ['y', 'x'],
    gates: [{ id: 'g', op: 'NAND', left: makeBoundarySource0('y'), right: makeBoundarySource0('x') }],
    outputs: [makeGateSource0('g')],
  });
  assert.equal(equivalentNANDWords0(nand, swappedBoundary).tag, 'reject');
});

test('NAND word validation rejects future gates, duplicate boundaries, and bad constants', () => {
  const futureGate = makeNANDWord0({
    boundary: ['x'],
    gates: [{ id: 'g', op: 'NAND', left: makeGateSource0('later'), right: makeBoundarySource0('x') }],
    outputs: [makeGateSource0('g')],
  });
  assert.equal(validateNANDWord0(futureGate).tag, 'reject');

  const duplicateBoundary = makeNANDWord0({ boundary: ['x', 'x'], gates: [], outputs: [makeBoundarySource0('x')] });
  assert.equal(validateNANDWord0(duplicateBoundary).tag, 'reject');

  const badConst = makeNANDWord0({ boundary: [], gates: [], outputs: [makeConstSource0(2)] });
  assert.equal(validateNANDWord0(badConst).tag, 'reject');
});

test('NAND semantics checker rejects public theorem activation and full coverage overclaim', async () => {
  const spec = clone0(await loadSpec0());
  spec.claimBoundary.publicTheoremEmissionAllowed = true;

  const activated = await CheckNANDDirectWireSemantics0({
    specOverride: spec,
    writeOutput: false,
  });

  assert.equal(activated.tag, 'reject');
  assert.equal(activated.coord, 'NANDSemantics.PublicEmission');
  assert.deepEqual(activated.path, ['claimBoundary', 'publicTheoremEmissionAllowed']);

  const full = clone0(await loadSpec0());
  full.fullSemanticsCoverageProved = true;
  const overclaim = await CheckNANDDirectWireSemantics0({ specOverride: full, writeOutput: false });
  assert.equal(overclaim.tag, 'reject');
  assert.equal(overclaim.coord, 'NANDSemantics.FullCoverageFlag');
});
