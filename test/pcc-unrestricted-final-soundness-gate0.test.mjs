import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from '../pcc-global-proof-dag0.mjs';

import {
  CheckUnrestrictedFinalSoundnessGate0,
  EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_OBLIGATIONS0,
  makeUnrestrictedFinalSoundnessGateInput0,
} from '../pcc-unrestricted-final-soundness-gate0.mjs';

test('unrestricted final-soundness gate represents the review packet but keeps release blocked', async () => {
  const out = await CheckUnrestrictedFinalSoundnessGate0(
    makeUnrestrictedFinalSoundnessGateInput0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckUnrestrictedFinalSoundnessGate0');
  assert.equal(out.NF.unrestrictedFinalSoundnessGateRepresentedReady, true);
  assert.equal(out.NF.unrestrictedFinalSoundnessReviewPacketReady, true);
  assert.equal(out.NF.unrestrictedFinalSoundnessReady, false);
  assert.equal(out.NF.unrestrictedFinalSoundnessReleased, false);
  assert.equal(out.NF.unrestrictedFinalSoundnessBlocked, true);
  assert.equal(out.NF.externalReviewAcceptanceReady, false);
  assert.deepEqual(out.NF.remainingBlockerCoordinates, [
    UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
    EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  ]);
  assert.equal(
    out.NF.reviewObligationCount,
    UNRESTRICTED_FINAL_SOUNDNESS_REVIEW_OBLIGATIONS0.length,
  );
  assert.equal(out.NF.independentMathematicalReviewStillRequired, true);
  assert.equal(out.NF.independentCheckerSoundnessReviewStillRequired, true);
  assert.equal(out.NF.externalReviewAcceptanceRequired, true);
  assert.equal(out.NF.publicTheoremEmissionReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0);
  assert.equal(out.NF.sealedReleaseNotOverwritten, true);
  assert.equal(out.NF.sourceAndArtifactAccessPublicWithoutRequest, true);
  assert.equal(out.NF.reviewPacketDigest.alg, 'SHA256');
  assert.equal(out.NF.gateBindingDigest.alg, 'SHA256');
  assert.equal(out.NF.releasePublicTheoremEmissionBlockerDigest.alg, 'SHA256');
});

test('unrestricted final-soundness gate rejects caller-supplied truth assertions', async () => {
  const input = {
    ...makeUnrestrictedFinalSoundnessGateInput0(),
    unrestrictedFinalSoundnessReady: true,
  };
  const out = await CheckUnrestrictedFinalSoundnessGate0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckUnrestrictedFinalSoundnessGate0.input');
  assert.deepEqual(out.Path, ['unrestrictedFinalSoundnessReady']);
  assert.equal(
    out.Witness.reason,
    'unrestricted final-soundness gate rejects caller-supplied readiness or truth assertions',
  );
});
