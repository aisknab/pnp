import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CURRENT_VERIFICATION_TESTS0,
  MakeCurrentVerificationPlan0,
  RunPNPVerifyAll0,
} from '../scripts/pnp-verify-all.mjs';

test('current verifier plan contains status, surface, archive integrity, and current tests only', () => {
  const plan = MakeCurrentVerificationPlan0();
  assert.deepEqual(plan.map(({ id }) => id), [
    'formal-reconstruction-status',
    'formal-public-surface',
    'legacy-v0-archive-integrity',
    'current-authority-unit-tests',
  ]);
  assert.equal(plan.some(({ id }) => /replay|release-audit|materialized/u.test(id)), false);
  assert.equal(CURRENT_VERIFICATION_TESTS0.some((file) => /pcc-runall|release-audit|materialized/u.test(file)), false);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-root-target0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-concrete-machine0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-concrete-tape-handoff0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes(
    'audits/lean-concrete-tape-blank-equivalence0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-concrete-pipeline-tape-geometry0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-concrete-pipeline-state-namespace0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-concrete-pipeline-stage-bridges0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-concrete-terminal-output-packer0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-concrete-pipeline-terminal-bridge0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-concrete-pipeline-paired-compiler0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-concrete-pipeline-compiler0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-concrete-pipeline-machine-simulation0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-concrete-complexity0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-concrete-pipeline-refinement0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-concrete-cnf0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes(
    'audits/lean-concrete-cook-levin-layout0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes(
    'audits/lean-concrete-cook-levin-tableau0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes(
    'audits/lean-concrete-cook-levin-verifier-tableau0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes(
    'audits/lean-concrete-cook-levin-local-cnf0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes(
    'audits/lean-concrete-cook-levin-tableau-cnf0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes(
    'audits/lean-concrete-cook-levin-tableau-cnf-semantics0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-theorem-inventory0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/formal-publication0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-nand-semantics0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-nand-enumerator0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-nand-reference-minimum0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-locked-nand-baseline0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-locked-nand-threshold-boundary0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes(
    'audits/lean-concrete-locked-nand-source-parser0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes(
    'audits/lean-concrete-cnf-to-nand-polynomial-reduction0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-residual-routes0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-residual-gain-chain0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-residual-gain-stopping0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-residual-terminal-full-bridge0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes('audits/lean-residual-terminal-mode-firewall0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes(
    'audits/lean-residual-terminal-projection-minimum0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes(
    'audits/lean-residual-terminal-projection-transfer0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes(
    'audits/lean-residual-terminal-saturation0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes(
    'audits/lean-residual-terminal-physical-support-completion0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes(
    'audits/lean-residual-terminal-support-extraction0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes(
    'audits/lean-residual-terminal-proper-support0.test.mjs'), true);
  assert.equal(CURRENT_VERIFICATION_TESTS0.includes(
    'audits/lean-residual-terminal-support-square-closure0.test.mjs'), true);
});

test('current verifier cannot be configured to execute the historical replay', () => {
  const defaultPlan = MakeCurrentVerificationPlan0();
  const ignoredLegacyOptionPlan = MakeCurrentVerificationPlan0({
    includeHistoricalAuditPipeline: true,
    includeLegacyReleaseAudit: true,
    historicalReplay: true,
  });
  assert.deepEqual(ignoredLegacyOptionPlan, defaultPlan);
});

test('current verifier accepts without executing a historical replay', async () => {
  const out = await RunPNPVerifyAll0({ writeOutput: false, includeUnitTests: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.currentStatusAuthority, true);
  assert.equal(out.mathematicalTheoremEstablished, false);
  assert.equal(out.leanConcreteCNFVerifierCorrectnessFormalized, true);
  assert.equal(out.leanConcreteCNFVerifierNoTimeoutFormalized, true);
  assert.equal(out.leanConcreteCNFSATMembershipFormalized, true);
  assert.equal(out.leanConcreteCNFSATMembershipTheorem,
    'PNP.Concrete.FinalUniversalDesign.cnfSATInNP');
  assert.equal(out.leanConcreteCNFSATInPFormalized, false);
  assert.equal(out.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(out.historicalReplayExecuted, false);
  assert.equal(out.legacyCheckerReplayAccepted, false);
  assert.equal(out.legacyCheckerReplayIsMathematicalProof, false);
  assert.equal(out.archiveIdentityVerified, true);
});
