import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckHistoricalReportSupersession0 } from '../pcc-historical-report-supersession0.mjs';

test('historical report supersession audit accepts sanitized root report surface', async () => {
  const out = await CheckHistoricalReportSupersession0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-HISTORICAL-REPORT-SUPERSESSION-2026-06-27-01');
  assert.equal(out.sanitizedReportCoordinate, 'PNP-HISTORICAL-REPORT-SANITIZED-2026-06-27-01');
  assert.equal(out.historicalReportSupersessionReady, true);
  assert.equal(out.historicalReportSanitizedReady, true);
  assert.equal(out.historicalReportPath, 'canonical_proof_report.tex');
  assert.equal(out.historicalReportPdfPath, 'canonical_proof_report.pdf');
  assert.equal(out.historicalDirectTheoremEmissionRepresented, false);
  assert.equal(out.historicalDirectTheoremEmissionSanitized, true);
  assert.equal(out.currentRootReportSanitized, true);
  assert.equal(out.currentPdfSanitized, true);
  assert.equal(out.currentBoundarySupersedesHistoricalEmission, true);
  assert.equal(out.historicalReportMayBeMutatedBySuccessorPRs, true);
  assert.equal(out.publicTheoremEmissionAllowedBySupersession, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});
