import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

const LEAN = new URL('../lean-regression/PNPBN3JointRealizabilityGap.lean', import.meta.url);
const REVIEW = new URL('../review/bn3_joint_realizability_gap.md', import.meta.url);
const STATUS = new URL('../status/FORMAL_RECONSTRUCTION_STATUS.json', import.meta.url);

test('two-cut model has per-cut witnesses but no stable realizing family', () => {
  const cuts = [false, true];
  const bases = [false, true];
  const realizes = (cut, basis) => basis === cut;
  assert.equal(cuts.every((cut) => bases.some((basis) => realizes(cut, basis))), true);

  const choices = [
    () => false,
    (cut) => cut,
    (cut) => !cut,
    () => true,
  ];
  const stable = (choose) => choose(false) === choose(true);
  assert.equal(choices.some((choose) =>
    cuts.every((cut) => realizes(cut, choose(cut))) && stable(choose)), false);
});

test('Lean regression and review pin the missing BN3 inference without overclaim', async () => {
  const [lean, review] = await Promise.all([
    readFile(LEAN, 'utf8'),
    readFile(REVIEW, 'utf8'),
  ]);
  for (const name of [
    'twoCut_perCutRealizable',
    'twoCut_noStableRealizingFamily',
    'perCutRealizable_not_uniformly_sufficient',
  ]) assert.match(lean, new RegExp(`theorem ${name}\\b`, 'u'), name);
  assert.doesNotMatch(lean, /\b(?:axiom|opaque|sorry|admit|Classical\.choice|native_decide)\b/u);
  assert.match(review, /finite candidate-derived repair earned; global milestone not earned/u);
  assert.match(review, /fullHistoricalBN3TheoremDischarged` to `false`/u);
  assert.match(review, /countermodel to the inference from per-cut existence alone/u);
  assert.match(review, /ResidualTerminalBN3RequestEnvelope/u);
});

test('publication status keeps global ZeroSlack/PCCMin fail closed', async () => {
  const status = JSON.parse(await readFile(STATUS, 'utf8'));
  const milestone = status.formalPublicationMilestones.find(
    (entry) => entry.id === 'global-zeroslack-pccmin',
  );
  assert.equal(milestone?.earned, false);
  assert.deepEqual(milestone?.requiredTheorems, [
    'PNP.Main.pccmin_polynomial_exact',
    'PNP.Main.zero_slack_complete',
  ]);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.leanResidualTerminalBN3RequestEnvelopeFormalized, true);
  const finite = status.formalPublicationMilestones.find(
    (entry) => entry.id === 'residual-terminal-bn3-request-envelope',
  );
  assert.equal(finite?.earned, true);
  assert.match(finite?.nonClaim, /exponential/u);
  assert.equal(status.nonClaims.some((claim) =>
    claim.includes('BN3 joint-realizability gap')), true);
});
