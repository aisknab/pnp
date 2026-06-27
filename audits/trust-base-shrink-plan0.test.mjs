import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckTrustBaseShrinkPlan0,
} from '../pcc-trust-base-shrink-plan0.mjs';

async function loadPlan0() {
  const text = await readFile(new URL('../trust-base/SHRINK_PLAN.json', import.meta.url), 'utf8');
  return JSON.parse(text);
}

async function loadTrustBase0() {
  const text = await readFile(new URL('../trust-base/TRUST_BASE.json', import.meta.url), 'utf8');
  return JSON.parse(text);
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('trust-base shrink-plan checker accepts current plan', async () => {
  const out = await CheckTrustBaseShrinkPlan0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-TRUST-BASE-SHRINK-PLAN-2026-06-27-01');
  assert.equal(out.trustBaseCoordinate, 'PNP-TRUST-BASE-2026-06-27-01');
  assert.equal(out.shrinkPlanReady, true);
  assert.equal(out.shrinksTrustBaseNow, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
  assert.deepEqual(out.taskIds, ['TB-001', 'TB-002', 'TB-003', 'TB-004', 'TB-005', 'TB-006', 'TB-007']);
  assert.equal(out.planSha256.length, 64);
});

test('trust-base shrink-plan checker rejects public theorem activation', async () => {
  const plan = clone0(await loadPlan0());
  plan.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckTrustBaseShrinkPlan0({
    planOverride: plan,
    trustBaseOverride: await loadTrustBase0(),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ShrinkPlan.PublicEmission');
  assert.deepEqual(out.path, ['claimBoundary', 'publicTheoremEmissionAllowed']);
});

test('trust-base shrink-plan checker rejects premature completed tasks', async () => {
  const plan = clone0(await loadPlan0());
  plan.tasks[0].status = 'complete';

  const out = await CheckTrustBaseShrinkPlan0({
    planOverride: plan,
    trustBaseOverride: await loadTrustBase0(),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ShrinkPlan.TaskPrematureCompletion');
  assert.deepEqual(out.path, ['tasks', 0, 'status']);
});

test('trust-base shrink-plan checker rejects unknown assumption targets', async () => {
  const plan = clone0(await loadPlan0());
  plan.tasks[0].targetsAssumptions.push('Unknown.Assumption');

  const out = await CheckTrustBaseShrinkPlan0({
    planOverride: plan,
    trustBaseOverride: await loadTrustBase0(),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ShrinkPlan.TaskUnknownAssumption');
  assert.deepEqual(out.path, ['tasks', 0, 'targetsAssumptions']);
});

test('trust-base shrink-plan checker rejects unknown dependencies', async () => {
  const plan = clone0(await loadPlan0());
  plan.tasks[1].blockedBy.push('TB-999');

  const out = await CheckTrustBaseShrinkPlan0({
    planOverride: plan,
    trustBaseOverride: await loadTrustBase0(),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ShrinkPlan.TaskUnknownDependency');
  assert.deepEqual(out.path, ['tasks', 1, 'blockedBy']);
});

test('trust-base shrink-plan checker rejects trust-base coordinate mismatch', async () => {
  const trustBase = clone0(await loadTrustBase0());
  trustBase.coordinate = 'PNP-TRUST-BASE-MISMATCH';

  const out = await CheckTrustBaseShrinkPlan0({
    planOverride: await loadPlan0(),
    trustBaseOverride: trustBase,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ShrinkPlan.TrustBaseCoordinateMismatch');
  assert.deepEqual(out.path, ['trust-base', 'coordinate']);
});
