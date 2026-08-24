#!/usr/bin/env node

import { readFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckProofProgress0';
const VERSION = 0;
const BASELINE_COORDINATE =
  'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-23-184';
const BASELINE_COVERAGE = Object.freeze({ earnedRows: 160, totalRows: 162 });
const BASELINE_SCORE = 30;
const CURRENT_SCORE = 35;
const FILES = Object.freeze({
  ledger: 'status/PROOF_PROGRESS.json',
  status: 'status/FORMAL_RECONSTRUCTION_STATUS.json',
  inventory: 'status/LEAN_THEOREM_INVENTORY.json',
});

const EXPECTED_TRACKS = Object.freeze([
  {
    id: 'formal-foundations',
    title: 'Formal foundations and proof infrastructure',
    pointsAvailable: 15,
    pointsEarned: 13,
    checkpoints: [
      ['foundations-concrete-kernel-interfaces', 4, 'earned'],
      ['foundations-recursive-pipeline', 4, 'earned'],
      ['foundations-inventory-gate', 3, 'earned'],
      ['foundations-cnfsat-in-np', 2, 'earned'],
      ['foundations-final-compatibility', 2, 'open'],
    ],
  },
  {
    id: 'concrete-reductions',
    title: 'Concrete reductions and locked-NAND route',
    pointsAvailable: 20,
    pointsEarned: 15,
    checkpoints: [
      ['reductions-cook-levin-semantics', 3, 'earned'],
      ['reductions-cnf-to-nand', 3, 'earned'],
      ['reductions-locked-nand', 4, 'earned'],
      ['reductions-builder-prefixes', 2, 'earned'],
      ['reductions-report-locked-nand-linkage', 2, 'earned'],
      ['reductions-complete-cook-levin-builder', 3, 'open'],
      ['reductions-concrete-np-hardness', 2, 'open'],
      ['reductions-final-target-compatibility', 1, 'earned'],
    ],
  },
  {
    id: 'unconditional-residual-core',
    title: 'Unconditional residual core and ZeroSlack',
    pointsAvailable: 35,
    pointsEarned: 2,
    checkpoints: [
      ['residual-finite-stopping-foundations', 2, 'earned'],
      ['residual-derive-terminal-objects', 5, 'open'],
      ['residual-pkgc-bn3-bn6-integration', 4, 'open'],
      ['residual-hn-bud-hb-semantics', 4, 'open'],
      ['residual-global-route-coverage', 4, 'open'],
      ['residual-unconditional-saturate-positive', 4, 'open'],
      ['residual-unconditional-bcel-ready', 4, 'open'],
      ['residual-unconditional-zero-slack', 8, 'open'],
    ],
  },
  {
    id: 'exact-pccmin',
    title: 'Exact PCCMin algorithm, complexity and bounds',
    pointsAvailable: 20,
    pointsEarned: 1,
    checkpoints: [
      ['pccmin-strict-gain-scaffold', 1, 'earned'],
      ['pccmin-executable-loop', 3, 'open'],
      ['pccmin-iteration-sound-descent', 4, 'open'],
      ['pccmin-termination-exactness', 4, 'open'],
      ['pccmin-polynomial-objects', 4, 'open'],
      ['pccmin-total-polynomial-bounds', 4, 'open'],
    ],
  },
  {
    id: 'root-and-axioms',
    title: 'Root theorem and project-axiom elimination',
    pointsAvailable: 10,
    pointsEarned: 4,
    checkpoints: [
      ['axiom-remove-generate-pccpack', 1, 'earned'],
      ['axiom-remove-check-pccpackexp', 1, 'earned'],
      ['axiom-remove-locked-nand-threshold', 1, 'earned'],
      ['axiom-remove-residual-band-minimum', 1, 'earned'],
      ['root-deterministic-cnfsat-in-p', 2, 'open'],
      ['root-complexity-transport', 1, 'open'],
      ['root-eligible-theorem', 2, 'open'],
      ['root-publication-gate', 1, 'open'],
    ],
  },
]);

const EXPECTED_GATES = Object.freeze([
  ['concrete-sat', 'Concrete SAT', 'Formal.ConcreteSAT'],
  ['residual-band-minimizer', 'Residual-band minimiser', 'Formal.ResidualBandMinimizer'],
  ['unconditional-zero-slack', 'Unconditional ZeroSlack', 'Formal.ZeroSlack'],
  ['polynomial-runtime-bounds', 'Polynomial runtime and certificate bounds', 'Formal.PolynomialRuntimeAndCertificateBounds'],
  ['root-theorem-axiom-audit', 'Root theorem and axiom audit', 'Formal.RootTheoremAndAxiomAudit'],
]);

const EXPECTED_PROJECT_AXIOMS = Object.freeze([]);

const REQUIRED_CHANGE_RECORD_FIELDS = Object.freeze([
  'checkpointId',
  'oldStatus',
  'newStatus',
  'compiledEvidence',
  'sourceCoordinateOrCommit',
  'loadBearingRationale',
  'remainingTrackLimitations',
  'oldAndNewTotal',
  'uncertaintyRangeDecision',
]);

const BASELINE_EARNED_CHECKPOINT_IDS = new Set([
  'foundations-concrete-kernel-interfaces',
  'foundations-recursive-pipeline',
  'foundations-inventory-gate',
  'foundations-cnfsat-in-np',
  'reductions-cook-levin-semantics',
  'reductions-cnf-to-nand',
  'reductions-locked-nand',
  'reductions-builder-prefixes',
  'reductions-report-locked-nand-linkage',
  'residual-finite-stopping-foundations',
  'pccmin-strict-gain-scaffold',
]);

class ProofProgressError extends Error {
  constructor(code, message, details = {}) {
    super(message);
    this.name = 'ProofProgressError';
    this.code = code;
    this.details = details;
  }
}

export function validateProofProgress0(ledger, status, inventory) {
  requirePlain(ledger, 'Ledger.Shape', 'progress ledger must be an object');
  requirePlain(status, 'Status.Shape', 'formal reconstruction status must be an object');
  requirePlain(inventory, 'Inventory.Shape', 'compiled theorem inventory must be an object');
  requireValue(ledger.kind, 'PNPProofProgress0', 'Ledger.Kind');
  requireValue(ledger.version, VERSION, 'Ledger.Version');
  requireValue(ledger.modelId, 'fixed-risk-weighted-checkpoints-v0', 'Ledger.Model');
  requireValue(ledger.asOfCoordinate, status.coordinate, 'Ledger.Coordinate');
  requireDate(ledger.lastReviewedDate, 'Ledger.LastReviewedDate');

  requirePlain(ledger.proofCompletion, 'ProofCompletion.Shape', 'proofCompletion must be an object');
  requireValue(ledger.proofCompletion.label, 'risk-weighted proof completion estimate', 'ProofCompletion.Label');
  requireValue(ledger.proofCompletion.pointsAvailable, 100, 'ProofCompletion.Available');
  requireValue(ledger.proofCompletion.isProbabilityOfCorrectness, false, 'ProofCompletion.ProbabilityBoundary');
  requireValue(ledger.proofCompletion.isTimeEstimate, false, 'ProofCompletion.TimeBoundary');
  requireValue(ledger.proofCompletion.mayDecrease, true, 'ProofCompletion.MayDecrease');

  requireArray(ledger.tracks, 'Tracks.Shape', 'tracks must be an array');
  requireValue(ledger.tracks.length, EXPECTED_TRACKS.length, 'Tracks.Count');
  let pointsAvailable = 0;
  let pointsEarned = 0;
  let checkpointCount = 0;
  for (let index = 0; index < EXPECTED_TRACKS.length; index += 1) {
    const expectedTrack = EXPECTED_TRACKS[index];
    const track = ledger.tracks[index];
    requirePlain(track, 'Track.Shape', 'track must be an object', { index });
    requireValue(track.id, expectedTrack.id, 'Track.Id', { index });
    requireValue(track.title, expectedTrack.title, 'Track.Title', { id: expectedTrack.id });
    requireValue(track.pointsAvailable, expectedTrack.pointsAvailable, 'Track.PointsAvailable', { id: expectedTrack.id });
    requireArray(track.checkpoints, 'Checkpoint.Shape', 'track checkpoints must be an array', { id: expectedTrack.id });
    requireValue(track.checkpoints.length, expectedTrack.checkpoints.length, 'Checkpoint.Count', { id: expectedTrack.id });
    let trackAvailable = 0;
    let trackEarned = 0;
    for (let checkpointIndex = 0; checkpointIndex < expectedTrack.checkpoints.length; checkpointIndex += 1) {
      const [expectedId, expectedPoints, expectedStatus] = expectedTrack.checkpoints[checkpointIndex];
      const checkpoint = track.checkpoints[checkpointIndex];
      requirePlain(checkpoint, 'Checkpoint.Shape', 'checkpoint must be an object', { id: expectedId });
      requireValue(checkpoint.id, expectedId, 'Checkpoint.Id', { track: expectedTrack.id, checkpointIndex });
      requireString(checkpoint.title, 'Checkpoint.Title', { id: expectedId });
      requireValue(checkpoint.points, expectedPoints, 'Checkpoint.Points', { id: expectedId });
      requireValue(checkpoint.status, expectedStatus, 'Checkpoint.Status', { id: expectedId });
      requireArray(checkpoint.evidence, 'Checkpoint.EvidenceShape', 'checkpoint evidence must be an array', { id: expectedId });
      if (checkpoint.evidence.length === 0) fail('Checkpoint.EvidenceMissing', 'checkpoint must retain exact evidence', { id: expectedId });
      for (const evidence of checkpoint.evidence) validateEvidence(evidence, status, inventory, expectedId);
      if (checkpoint.status === 'earned') {
        if (BASELINE_EARNED_CHECKPOINT_IDS.has(expectedId)) {
          requireValue(checkpoint.awardedAtCoordinate, BASELINE_COORDINATE,
            'Checkpoint.AwardCoordinate', { id: expectedId });
        } else {
          requireString(checkpoint.awardedAtCoordinate,
            'Checkpoint.AwardCoordinate', { id: expectedId });
        }
        trackEarned += checkpoint.points;
      } else {
        requireValue(checkpoint.awardedAtCoordinate, null, 'Checkpoint.OpenAwardCoordinate', { id: expectedId });
      }
      requireString(checkpoint.justification, 'Checkpoint.Justification', { id: expectedId });
      requireString(checkpoint.remainingLimitation, 'Checkpoint.RemainingLimitation', { id: expectedId });
      requireDate(checkpoint.lastReviewedDate, 'Checkpoint.LastReviewedDate', { id: expectedId });
      trackAvailable += checkpoint.points;
      checkpointCount += 1;
    }
    requireValue(trackAvailable, track.pointsAvailable, 'Track.CheckpointTotal', { id: expectedTrack.id });
    requireValue(trackEarned, expectedTrack.pointsEarned, 'Track.ExpectedEarned', { id: expectedTrack.id });
    requireValue(track.pointsEarned, trackEarned, 'Track.StoredEarned', { id: expectedTrack.id });
    pointsAvailable += trackAvailable;
    pointsEarned += trackEarned;
  }
  requireValue(pointsAvailable, 100, 'ProofCompletion.TrackMaximumTotal');
  requireValue(pointsEarned, CURRENT_SCORE, 'ProofCompletion.CurrentEarned');
  requireValue(ledger.proofCompletion.pointsEarned, pointsEarned, 'ProofCompletion.StoredEarned');
  requireValue(ledger.proofCompletion.percent, pointsEarned, 'ProofCompletion.StoredPercent');
  if (!(ledger.proofCompletion.uncertaintyLowPercent <= ledger.proofCompletion.percent
    && ledger.proofCompletion.percent <= ledger.proofCompletion.uncertaintyHighPercent)) {
    fail('ProofCompletion.UncertaintyRange', 'uncertainty range must contain the displayed estimate');
  }
  requireValue(ledger.proofCompletion.uncertaintyLowPercent, 20, 'ProofCompletion.BaselineUncertaintyLow');
  requireValue(ledger.proofCompletion.uncertaintyHighPercent, 40, 'ProofCompletion.BaselineUncertaintyHigh');

  const milestones = status.formalPublicationMilestones;
  requireArray(milestones, 'Coverage.StatusMilestones', 'status milestone ledger must be an array');
  const earnedRows = milestones.filter((row) => row?.earned === true).length;
  const totalRows = milestones.length;
  requirePlain(ledger.formalArtefactCoverage, 'Coverage.Shape', 'formalArtefactCoverage must be an object');
  requireValue(ledger.formalArtefactCoverage.label, 'formal artefact coverage', 'Coverage.Label');
  requireValue(ledger.formalArtefactCoverage.earnedRows, earnedRows, 'Coverage.EarnedRows');
  requireValue(ledger.formalArtefactCoverage.totalRows, totalRows, 'Coverage.TotalRows');
  requireValue(ledger.formalArtefactCoverage.percentRoundedOneDecimal, roundOne(100 * earnedRows / totalRows), 'Coverage.Percent');
  requireValue(ledger.formalArtefactCoverage.isProofCompletionMetric, false, 'Coverage.ProofCompletionBoundary');
  requireValue(ledger.formalArtefactCoverage.denominatorCanGrow, true, 'Coverage.DenominatorBoundary');

  requireArray(ledger.globalGates, 'Gates.Shape', 'globalGates must be an array');
  requireValue(ledger.globalGates.length, EXPECTED_GATES.length, 'Gates.Count');
  requireArray(status.remainingBlockers, 'Gates.StatusBlockers', 'status remainingBlockers must be an array');
  requireArray(status.remainingFormalObligations, 'Gates.StatusObligations', 'status remainingFormalObligations must be an array');
  const expectedBlockers = EXPECTED_GATES.map(([, , blocker]) => blocker);
  requireJson(status.remainingBlockers, expectedBlockers, 'Gates.StatusBlockerSet');
  requireJson(status.remainingFormalObligations, expectedBlockers, 'Gates.StatusObligationSet');
  for (let index = 0; index < EXPECTED_GATES.length; index += 1) {
    const [id, title, blocker] = EXPECTED_GATES[index];
    const gate = ledger.globalGates[index];
    requirePlain(gate, 'Gate.Shape', 'global gate must be an object', { id });
    requireValue(gate.id, id, 'Gate.Id', { index });
    requireValue(gate.title, title, 'Gate.Title', { id });
    requireValue(gate.statusBlocker, blocker, 'Gate.Blocker', { id });
    requireValue(gate.status, status.remainingBlockers.includes(blocker) ? 'open' : 'closed', 'Gate.Status', { id });
  }

  requireJson(ledger.projectSpecificAxiomsRemaining, EXPECTED_PROJECT_AXIOMS, 'Axioms.Ledger');
  requireJson(status.projectSpecificAxiomInventory, EXPECTED_PROJECT_AXIOMS, 'Axioms.Status');
  requireJson(inventory.projectAxioms, EXPECTED_PROJECT_AXIOMS, 'Axioms.Inventory');
  requireValue(status.projectSpecificAxiomsRemaining, false, 'Axioms.StatusFlag');

  requirePlain(ledger.rootTheorem, 'Root.Shape', 'rootTheorem must be an object');
  requireValue(ledger.rootTheorem.name, status.rootLeanTheorem, 'Root.Name');
  requireValue(ledger.rootTheorem.name, inventory.compatibilityRootName, 'Root.InventoryName');
  requireValue(ledger.rootTheorem.present, status.rootLeanTheoremPresent, 'Root.Present');
  requireValue(ledger.rootTheorem.built, status.rootLeanTheoremBuilt, 'Root.Built');
  requireValue(ledger.rootTheorem.axiomAuditPassed, status.rootLeanTheoremAxiomAuditPassed, 'Root.AxiomAudit');
  requireValue(inventory.declarations.some((row) => row?.name === ledger.rootTheorem.name), ledger.rootTheorem.present, 'Root.InventoryPresence');

  requirePlain(ledger.publicationGate, 'PublicationGate.Shape', 'publicationGate must be an object');
  requireValue(ledger.publicationGate.passed, status.concretePublicationGate?.passed, 'PublicationGate.Status');
  requireValue(ledger.publicationGate.passed, false, 'PublicationGate.Baseline');

  requirePlain(ledger.scoreChangePolicy, 'Policy.Shape', 'scoreChangePolicy must be an object');
  requireValue(ledger.scoreChangePolicy.fixedCheckpointWeights, true, 'Policy.FixedWeights');
  requireValue(ledger.scoreChangePolicy.localMilestonesDoNotAutomaticallyChangeScore, true, 'Policy.LocalMilestones');
  requireValue(ledger.scoreChangePolicy.externalReviewIsNotMathematicalPremise, true, 'Policy.ExternalReview');
  requireJson(ledger.scoreChangePolicy.requiredChangeRecordFields, REQUIRED_CHANGE_RECORD_FIELDS, 'Policy.ChangeFields');

  requireArray(ledger.history, 'History.Shape', 'history must be an array');
  if (ledger.history.length === 0) fail('History.Empty', 'progress history must include the M184 baseline');
  const baseline = ledger.history.find((entry) =>
    entry?.kind === 'baseline' && entry?.asOfCoordinate === BASELINE_COORDINATE);
  requirePlain(baseline, 'History.BaselineShape', 'baseline history entry must be an object');
  requireValue(baseline.kind, 'baseline', 'History.BaselineKind');
  requireValue(baseline.asOfCoordinate, BASELINE_COORDINATE, 'History.BaselineCoordinate');
  requireJson(baseline.formalArtefactCoverage, BASELINE_COVERAGE, 'History.BaselineCoverage');
  requireValue(baseline.riskWeightedProofCompletionPercent, BASELINE_SCORE, 'History.BaselineScore');
  requireValue(baseline.uncertaintyLowPercent, 20, 'History.BaselineUncertaintyLow');
  requireValue(baseline.uncertaintyHighPercent, 40, 'History.BaselineUncertaintyHigh');
  requireValue(baseline.globalGatesClosed, 0, 'History.BaselineGatesClosed');
  requireValue(baseline.globalGatesAvailable, EXPECTED_GATES.length, 'History.BaselineGatesAvailable');
  requireString(baseline.rationale, 'History.BaselineRationale');

  const currentReviewIndex = ledger.history.findLastIndex((entry) =>
    entry?.asOfCoordinate === ledger.asOfCoordinate);
  const currentReview = ledger.history[currentReviewIndex];
  requirePlain(currentReview, 'History.CurrentShape',
    'progress history must include the current coordinate');
  requireValue(currentReviewIndex, ledger.history.length - 1,
    'History.CurrentMustBeLatest');
  requireJson(currentReview.formalArtefactCoverage, { earnedRows, totalRows },
    'History.CurrentCoverage');
  requireValue(currentReview.riskWeightedProofCompletionPercent, pointsEarned,
    'History.CurrentScore');
  requireValue(currentReview.uncertaintyLowPercent,
    ledger.proofCompletion.uncertaintyLowPercent, 'History.CurrentUncertaintyLow');
  requireValue(currentReview.uncertaintyHighPercent,
    ledger.proofCompletion.uncertaintyHighPercent, 'History.CurrentUncertaintyHigh');
  requireValue(currentReview.globalGatesClosed,
    ledger.globalGates.filter((gate) => gate.status === 'closed').length,
    'History.CurrentGatesClosed');
  requireValue(currentReview.globalGatesAvailable, EXPECTED_GATES.length,
    'History.CurrentGatesAvailable');
  requireString(currentReview.rationale, 'History.CurrentRationale');
  requireValue(ledger.history.indexOf(baseline), 0,
    'History.BaselineMustBeFirst');
  for (let reviewIndex = 1; reviewIndex < ledger.history.length;
    reviewIndex += 1) {
    const review = ledger.history[reviewIndex];
    const previousReview = ledger.history[reviewIndex - 1];
    requirePlain(review, 'History.ReviewShape',
      'every post-baseline history entry must be a milestone review',
      { reviewIndex });
    requirePlain(previousReview, 'History.PreviousShape',
      'every milestone review must follow a scored history entry',
      { reviewIndex });
    const previousScore = previousReview.riskWeightedProofCompletionPercent;
    const reviewScore = review.riskWeightedProofCompletionPercent;
    requireValue(Number.isInteger(previousScore), true,
      'History.PreviousScoreShape', { reviewIndex });
    requireValue(Number.isInteger(reviewScore), true,
      'History.ReviewScoreShape', { reviewIndex });
    requireValue(review.kind, 'milestone-review', 'History.ReviewKind',
      { reviewIndex });
    requireValue(review.scoreChanged, reviewScore !== previousScore,
      'History.ReviewScoreChanged', { reviewIndex });
    requireArray(review.changedCheckpointIds,
      'History.ReviewCheckpointChanges',
      'milestone review must list changed checkpoint IDs', { reviewIndex });
    if (review.scoreChanged === false) {
      requireValue(review.changedCheckpointIds.length, 0,
        'History.ReviewUnexpectedCheckpointChange', { reviewIndex });
      requireJson(review.changeRecords ?? [], [],
        'History.ReviewUnexpectedChangeRecords', { reviewIndex });
    } else {
      validateChangeRecords0(review, ledger, status, inventory,
        previousScore, reviewScore, reviewIndex === currentReviewIndex);
    }
  }

  requireArray(ledger.nonClaims, 'NonClaims.Shape', 'nonClaims must be an array');
  const nonClaims = ledger.nonClaims.join(' ');
  for (const required of ['not the probability', 'not a delivery or time-remaining estimate', 'Formal artefact coverage is not proof completion', 'External review']) {
    if (!nonClaims.includes(required)) fail('NonClaims.RequiredBoundary', 'required progress boundary is missing', { required });
  }

  return {
    tag: 'accept',
    kind: 'accept',
    checker: CHECKER,
    version: VERSION,
    coordinate: ledger.asOfCoordinate,
    modelId: ledger.modelId,
    trackCount: ledger.tracks.length,
    checkpointCount,
    pointsEarned,
    pointsAvailable,
    uncertaintyLowPercent: ledger.proofCompletion.uncertaintyLowPercent,
    uncertaintyHighPercent: ledger.proofCompletion.uncertaintyHighPercent,
    formalArtefactCoverage: { earnedRows, totalRows },
    globalGatesClosed: ledger.globalGates.filter((gate) => gate.status === 'closed').length,
    globalGatesAvailable: ledger.globalGates.length,
    projectSpecificAxiomCount: ledger.projectSpecificAxiomsRemaining.length,
    rootTheoremPresent: ledger.rootTheorem.present,
    publicationGatePassed: ledger.publicationGate.passed,
    isProbabilityOfCorrectness: false,
    isTimeEstimate: false,
  };
}

export async function CheckProofProgress0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  try {
    const [ledger, status, inventory] = await Promise.all([
      readJson(root, FILES.ledger, options.ledgerOverride),
      readJson(root, FILES.status, options.statusOverride),
      readJson(root, FILES.inventory, options.inventoryOverride),
    ]);
    return validateProofProgress0(ledger, status, inventory);
  } catch (error) {
    return {
      tag: 'reject',
      kind: 'reject',
      checker: CHECKER,
      version: VERSION,
      code: error?.code ?? 'ProofProgress.UnhandledException',
      reason: error?.message ?? String(error),
      details: error?.details ?? {},
      pointsEarned: null,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
    };
  }
}

function validateChangeRecords0(review, ledger, status, inventory,
  previousScore, currentScore, requireCurrentEvidence) {
  requireArray(review.changeRecords, 'History.ChangeRecordsShape',
    'score-changing review must include one record per changed checkpoint');
  requireValue(review.changeRecords.length, review.changedCheckpointIds.length,
    'History.ChangeRecordCount');
  const seenCheckpointIds = new Set();
  let runningTotal = previousScore;
  for (let index = 0; index < review.changeRecords.length; index += 1) {
    const record = review.changeRecords[index];
    const checkpointId = review.changedCheckpointIds[index];
    requirePlain(record, 'History.ChangeRecordShape',
      'score change record must be an object', { index, checkpointId });
    requireJson(Object.keys(record).sort(),
      [...REQUIRED_CHANGE_RECORD_FIELDS].sort(),
      'History.ChangeRecordFields', { index, checkpointId });
    requireValue(record.checkpointId, checkpointId,
      'History.ChangeRecordCheckpoint', { index });
    if (seenCheckpointIds.has(checkpointId)) {
      fail('History.ChangeRecordDuplicateCheckpoint',
        'score-changing review must not repeat a checkpoint', { checkpointId });
    }
    seenCheckpointIds.add(checkpointId);
    const checkpoint = ledger.tracks.flatMap((track) => track.checkpoints)
      .find((candidate) => candidate.id === checkpointId);
    requirePlain(checkpoint, 'History.ChangeRecordKnownCheckpoint',
      'score change record names an unknown checkpoint', { checkpointId });
    if (!['open', 'earned'].includes(record.oldStatus)
        || !['open', 'earned'].includes(record.newStatus)
        || record.oldStatus === record.newStatus) {
      fail('History.ChangeRecordTransition',
        'score change must transition one checkpoint between open and earned',
        { checkpointId, oldStatus: record.oldStatus, newStatus: record.newStatus });
    }
    if (requireCurrentEvidence) {
      requireValue(record.newStatus, checkpoint.status,
        'History.ChangeRecordNewStatus', { checkpointId });
    }
    requireArray(record.compiledEvidence, 'History.ChangeRecordEvidenceShape',
      'score change record must include compiled evidence', { checkpointId });
    if (record.compiledEvidence.length === 0) {
      fail('History.ChangeRecordEvidenceMissing',
        'score change record must include compiled evidence', { checkpointId });
    }
    for (const evidence of record.compiledEvidence) {
      if (requireCurrentEvidence) {
        validateEvidence(evidence, status, inventory, checkpointId);
      } else {
        requirePlain(evidence, 'History.ChangeRecordEvidenceEntryShape',
          'historical compiled evidence must remain an object',
          { checkpointId });
      }
    }
    if (record.sourceCoordinateOrCommit !== review.asOfCoordinate
        && !/^[0-9a-f]{40}$/u.test(record.sourceCoordinateOrCommit)) {
      fail('History.ChangeRecordCoordinate',
        'score change evidence must name its review coordinate or a full commit',
        { checkpointId });
    }
    requireString(record.loadBearingRationale,
      'History.ChangeRecordRationale', { checkpointId });
    requireString(record.remainingTrackLimitations,
      'History.ChangeRecordLimitations', { checkpointId });
    requirePlain(record.oldAndNewTotal,
      'History.ChangeRecordTotalShape',
      'score change record total must be an object', { checkpointId });
    const delta = record.newStatus === 'earned'
      ? checkpoint.points
      : -checkpoint.points;
    requireJson(record.oldAndNewTotal,
      { old: runningTotal, new: runningTotal + delta },
      'History.ChangeRecordTotal', { checkpointId });
    runningTotal += delta;
    requirePlain(record.uncertaintyRangeDecision,
      'History.ChangeRecordUncertaintyShape',
      'uncertainty decision must be an object', { checkpointId });
    requireValue(record.uncertaintyRangeDecision.lowPercent,
      review.uncertaintyLowPercent,
      'History.ChangeRecordUncertaintyLow', { checkpointId });
    requireValue(record.uncertaintyRangeDecision.highPercent,
      review.uncertaintyHighPercent,
      'History.ChangeRecordUncertaintyHigh', { checkpointId });
    requireValue(typeof record.uncertaintyRangeDecision.changed, 'boolean',
      'History.ChangeRecordUncertaintyChangedShape', { checkpointId });
    requireString(record.uncertaintyRangeDecision.rationale,
      'History.ChangeRecordUncertaintyRationale', { checkpointId });
  }
  requireValue(runningTotal, currentScore,
    'History.ChangeRecordFinalTotal');
}

function validateEvidence(evidence, status, inventory, checkpointId) {
  requirePlain(evidence, 'Evidence.Shape', 'checkpoint evidence must be an object', { checkpointId });
  if (evidence.kind === 'status-field') {
    requireString(evidence.field, 'Evidence.StatusField', { checkpointId });
    const actual = resolveField(status, evidence.field);
    requireJson(actual, evidence.expected, 'Evidence.StatusMismatch', { checkpointId, field: evidence.field });
    return;
  }
  if (evidence.kind === 'milestone-earned') {
    requireString(evidence.id, 'Evidence.MilestoneId', { checkpointId });
    const milestone = status.formalPublicationMilestones?.find?.((row) => row?.id === evidence.id);
    if (!milestone || milestone.earned !== true) fail('Evidence.MilestoneNotEarned', 'required formal publication milestone is not earned', { checkpointId, milestoneId: evidence.id });
    return;
  }
  if (evidence.kind === 'status-blocker-open') {
    requireString(evidence.id, 'Evidence.BlockerId', { checkpointId });
    if (!status.remainingBlockers?.includes?.(evidence.id)) fail('Evidence.BlockerNotOpen', 'required open blocker is absent', { checkpointId, blocker: evidence.id });
    return;
  }
  if (evidence.kind === 'inventory-declaration') {
    requireString(evidence.name, 'Evidence.DeclarationName', { checkpointId });
    requireValue(typeof evidence.expectedPresent, 'boolean', 'Evidence.DeclarationExpectedPresent', { checkpointId });
    const present = inventory.declarations?.some?.((row) => row?.name === evidence.name) ?? false;
    requireValue(present, evidence.expectedPresent, 'Evidence.DeclarationPresence', { checkpointId, name: evidence.name });
    return;
  }
  if (evidence.kind === 'inventory-project-axiom') {
    requireString(evidence.name, 'Evidence.AxiomName', { checkpointId });
    requireValue(typeof evidence.expectedPresent, 'boolean', 'Evidence.AxiomExpectedPresent', { checkpointId });
    const present = inventory.projectAxioms?.includes?.(evidence.name) ?? false;
    requireValue(present, evidence.expectedPresent, 'Evidence.AxiomPresence', { checkpointId, name: evidence.name });
    return;
  }
  fail('Evidence.UnknownKind', 'unsupported checkpoint evidence kind', { checkpointId, kind: evidence.kind });
}

function resolveField(root, dottedPath) {
  let value = root;
  for (const part of dottedPath.split('.')) {
    if (!plain(value) || !Object.hasOwn(value, part)) fail('Evidence.StatusFieldMissing', 'status evidence field is missing', { dottedPath, part });
    value = value[part];
  }
  return value;
}

async function readJson(root, relativePath, override) {
  if (override !== undefined) return override;
  const absolute = path.resolve(root, relativePath);
  const back = path.relative(root, absolute);
  if (back.startsWith('..') || path.isAbsolute(back)) fail('Read.UnsafePath', 'source path escapes repository root', { relativePath });
  return JSON.parse(await readFile(absolute, 'utf8'));
}

function fail(code, message, details = {}) {
  throw new ProofProgressError(code, message, details);
}

function plain(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function requirePlain(value, code, message, details = {}) {
  if (!plain(value)) fail(code, message, details);
}

function requireArray(value, code, message, details = {}) {
  if (!Array.isArray(value)) fail(code, message, details);
}

function requireString(value, code, details = {}) {
  if (typeof value !== 'string' || value.trim().length === 0) fail(code, 'required text is missing', details);
}

function requireDate(value, code, details = {}) {
  if (typeof value !== 'string' || !/^\d{4}-\d{2}-\d{2}$/u.test(value)) fail(code, 'expected an ISO calendar date', details);
}

function requireValue(actual, expected, code, details = {}) {
  if (!Object.is(actual, expected)) fail(code, 'value does not match the fixed progress contract', { ...details, expected, actual });
}

function requireJson(actual, expected, code, details = {}) {
  if (JSON.stringify(actual) !== JSON.stringify(expected)) fail(code, 'structured value does not match the progress contract', { ...details, expected, actual });
}

function roundOne(value) {
  return Math.round((value + Number.EPSILON) * 10) / 10;
}

function parseArgs(argv) {
  const options = { root: process.cwd(), json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--root') options.root = argv[++index];
    else if (arg === '--json') options.json = true;
    else if (arg === '--no-write') continue;
    else if (arg === '--help' || arg === '-h') {
      process.stdout.write('Usage: node pcc-proof-progress0.mjs [--root <path>] [--json] [--no-write]\n');
      process.exit(0);
    } else throw new Error(`unknown argument: ${arg}`);
  }
  return options;
}

async function main() {
  let options;
  try {
    options = parseArgs(process.argv.slice(2));
  } catch (error) {
    process.stderr.write(`${JSON.stringify({ tag: 'reject', checker: CHECKER, reason: error.message })}\n`);
    process.exit(2);
  }
  const result = await CheckProofProgress0(options);
  const output = options.json ? JSON.stringify(result) : JSON.stringify(result, null, 2);
  (result.tag === 'accept' ? process.stdout : process.stderr).write(`${output}\n`);
  process.exit(result.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main();
