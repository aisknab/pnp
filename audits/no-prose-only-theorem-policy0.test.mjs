import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckNoProseOnlyTheoremPolicy0 } from '../pcc-no-prose-only-theorem-policy0.mjs';

async function json0(pathname) {
  return JSON.parse(await readFile(new URL(`../${pathname}`, import.meta.url), 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('no prose-only theorem policy accepts current policy and ledgers', async () => {
  const out = await CheckNoProseOnlyTheoremPolicy0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-NO-PROSE-ONLY-THEOREM-POLICY-2026-06-27-01');
  assert.equal(out.policyReady, true);
  assert.equal(out.releaseCriticalTheoremSpineCovered, true);
  assert.equal(out.allNumberedReportTheoremsCovered, false);
  assert.equal(out.fullReportTheoremInventoryExhaustive, false);
  assert.equal(out.proseOnlyTheoremActivationAllowed, false);
  assert.equal(out.publicTheoremEmissionAllowedByPolicy, false);
  assert.equal(out.theoremBindingCount, 20);
  assert.ok(out.proofObligationCount >= 15);
  assert.ok(out.gapCount >= 12);
  assert.equal(out.ruleCount, 5);
  assert.ok(out.evidenceFileCount >= 6);
  assert.equal(out.evidenceDigestSha256.length, 64);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('no prose-only theorem policy rejects public theorem activation in policy boundary', async () => {
  const policy = clone0(await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'));
  policy.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckNoProseOnlyTheoremPolicy0({
    policyOverride: policy,
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoProseOnlyTheoremPolicy.PublicEmission');
});

test('no prose-only theorem policy rejects exhaustive coverage overclaim', async () => {
  const policy = clone0(await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'));
  policy.allNumberedReportTheoremsCovered = true;

  const out = await CheckNoProseOnlyTheoremPolicy0({
    policyOverride: policy,
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoProseOnlyTheoremPolicy.AllNumberedOverclaim');
});

test('no prose-only theorem policy rejects prose-only theorem activation flag', async () => {
  const policy = clone0(await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'));
  policy.proseOnlyTheoremActivationAllowed = true;

  const out = await CheckNoProseOnlyTheoremPolicy0({
    policyOverride: policy,
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoProseOnlyTheoremPolicy.ProseActivationFlag');
});

test('no prose-only theorem policy rejects theorem binding that discharges public theorem', async () => {
  const bindings = clone0(await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'));
  bindings.theoremBindings[0].dischargesPublicTheorem = true;

  const out = await CheckNoProseOnlyTheoremPolicy0({
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    bindingsOverride: bindings,
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoProseOnlyTheoremPolicy.BindingDischargesPublicTheorem');
});

test('no prose-only theorem policy rejects binding groups without tests', async () => {
  const bindings = clone0(await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'));
  bindings.bindingGroups['final-release-boundary'].tests = [];

  const out = await CheckNoProseOnlyTheoremPolicy0({
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    bindingsOverride: bindings,
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoProseOnlyTheoremPolicy.BindingGroupIncomplete');
});

test('no prose-only theorem policy rejects missing finite-to-unbounded obligation', async () => {
  const obligations = clone0(await json0('proof-obligations/OBLIGATION_LEDGER.json'));
  obligations.obligations = obligations.obligations.filter((entry) => entry.id !== 'OBL-015-FiniteToUnboundedFamilyAudit');

  const out = await CheckNoProseOnlyTheoremPolicy0({
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    obligationsOverride: obligations,
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoProseOnlyTheoremPolicy.ObligationMissing');
});

test('no prose-only theorem policy rejects closed GAP-004', async () => {
  const gaps = clone0(await json0('proof-obligations/GAP_LEDGER.json'));
  const gap = gaps.gaps.find((entry) => entry.id === 'GAP-004-FiniteToUnboundedUniformity');
  gap.blocker = null;
  gap.status = 'closed';

  const out = await CheckNoProseOnlyTheoremPolicy0({
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: gaps,
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoProseOnlyTheoremPolicy.Gap004State');
});

test('no prose-only theorem policy rejects missing status coordinate', async () => {
  const status = clone0(await json0('PNP_STATUS.json'));
  delete status.noProseOnlyTheoremPolicyCoordinate;

  const out = await CheckNoProseOnlyTheoremPolicy0({
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: status,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NoProseOnlyTheoremPolicy.StatusCoordinate');
});
