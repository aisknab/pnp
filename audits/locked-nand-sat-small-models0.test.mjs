import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckLockedNANDSATSmallModels0,
} from '../pcc-locked-nand-sat-small-models0.mjs';

import {
  bruteForceCNFSAT0,
  constructLockedNANDSATSeedWord0,
  enumerateCNFUniverse0,
  exactMinimumForTruthBits0,
  expectedLockedOutputBits0,
  RunLockedNANDSATSmallModels0,
} from '../semantics/locked-nand-sat-small-models.mjs';

import {
  flattenedTruthTable0,
} from '../semantics/nand-direct-wire-reference.mjs';

async function loadConfig0() {
  const text = await readFile(new URL('../semantics/locked-nand-sat-small-models-config.json', import.meta.url), 'utf8');
  return JSON.parse(text);
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('locked NAND SAT small-model checker accepts current config', async () => {
  const out = await CheckLockedNANDSATSmallModels0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-LOCKED-NAND-SAT-SMALL-MODELS-2026-06-27-01');
  assert.equal(out.semanticsCoordinate, 'PNP-NAND-DIRECT-WIRE-SEMANTICS-2026-06-27-01');
  assert.equal(out.smallModelsCoordinate, 'PNP-NAND-SMALL-MODELS-2026-06-27-01');
  assert.equal(out.satSmallModelsReady, true);
  assert.equal(out.fullLockedNANDThresholdCoverageProved, false);
  assert.equal(out.exhaustiveWithinConfiguredFormulaUniverse, true);
  assert.ok(out.formulaCount > 0);
  assert.ok(out.satFormulaCount > 0);
  assert.ok(out.unsatFormulaCount > 0);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('locked NAND SAT small-model reference audit agrees with brute force SAT', () => {
  const out = RunLockedNANDSATSmallModels0({ maxVariables: 2, maxExactSearchGates: 3 });

  assert.equal(out.tag, 'accept');
  assert.equal(out.formulaCount, 9);
  assert.equal(out.satFormulaCount, 6);
  assert.equal(out.unsatFormulaCount, 3);
  assert.ok(out.results.every((row) => row.threshold === row.sat));
});

test('each configured formula has matching locked output truth table and threshold', () => {
  const formulas = enumerateCNFUniverse0({ maxVariables: 2 });
  assert.ok(formulas.length > 0);

  for (const formula of formulas) {
    const sat = bruteForceCNFSAT0(formula);
    assert.equal(sat.tag, 'accept');

    const construction = constructLockedNANDSATSeedWord0(formula);
    assert.equal(construction.tag, 'accept');

    const table = flattenedTruthTable0(construction.word);
    assert.equal(table.tag, 'accept');
    assert.deepEqual(table.bits, expectedLockedOutputBits0(formula));

    const exact = exactMinimumForTruthBits0({
      boundary: construction.word.boundary,
      bits: table.bits,
      maxGates: 3,
    });
    assert.equal(exact.tag, 'accept');
    assert.equal(exact.minimum > construction.baselineMinimum, sat.sat);
  }
});

test('contradiction pair produces zero output and unit formulas produce positive minimum', () => {
  const formulas = enumerateCNFUniverse0({ maxVariables: 1 });
  const contradiction = formulas.find((formula) => formula.id === 'contradiction-x0');
  const unit = formulas.find((formula) => formula.id === 'unit-x0');

  const contradictionConstruction = constructLockedNANDSATSeedWord0(contradiction);
  const contradictionBits = flattenedTruthTable0(contradictionConstruction.word).bits;
  assert.deepEqual(contradictionBits, [0, 0, 0, 0]);
  assert.equal(exactMinimumForTruthBits0({ boundary: contradictionConstruction.word.boundary, bits: contradictionBits, maxGates: 3 }).minimum, 0);

  const unitConstruction = constructLockedNANDSATSeedWord0(unit);
  const unitBits = flattenedTruthTable0(unitConstruction.word).bits;
  assert.ok(unitBits.some((bit) => bit === 1));
  assert.ok(exactMinimumForTruthBits0({ boundary: unitConstruction.word.boundary, bits: unitBits, maxGates: 3 }).minimum > 0);
});

test('locked NAND SAT small-model checker rejects public theorem activation', async () => {
  const config = clone0(await loadConfig0());
  config.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckLockedNANDSATSmallModels0({
    configOverride: config,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'LockedNANDSAT.PublicEmission');
  assert.deepEqual(out.path, ['claimBoundary', 'publicTheoremEmissionAllowed']);
});

test('locked NAND SAT small-model checker rejects full threshold coverage overclaim', async () => {
  const config = clone0(await loadConfig0());
  config.fullLockedNANDThresholdCoverageProved = true;

  const out = await CheckLockedNANDSATSmallModels0({
    configOverride: config,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'LockedNANDSAT.FullThresholdCoverageFlag');
  assert.deepEqual(out.path, ['fullLockedNANDThresholdCoverageProved']);
});

test('locked NAND SAT small-model checker rejects changed exact search bound', async () => {
  const config = clone0(await loadConfig0());
  config.thresholdModel.maxExactSearchGates = 2;

  const out = await CheckLockedNANDSATSmallModels0({
    configOverride: config,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'LockedNANDSAT.MaxExactSearchGates');
});
