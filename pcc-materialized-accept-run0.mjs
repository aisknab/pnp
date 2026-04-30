import fs from 'node:fs/promises';
import { fileURLToPath } from 'node:url';

import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedAggregateFile0,
  MATERIALIZED_AGGREGATE_PHASES0,
} from './pcc-materialized-aggregate0.mjs';

import {
  MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
} from './pcc-materialized-pack0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_ACCEPT_RUN_VERDICTS0 = Object.freeze([
  'pending',
  'reject',
  'accept',
]);

export const MATERIALIZED_ACCEPT_RUN_PHASES0 = Object.freeze([
  ...MATERIALIZED_AGGREGATE_PHASES0,
  'CheckPCCPackexpPrecondition0',
  'ExternalReplayTranscript0',
  'EmitMaterializedAcceptRunVerdict0',
]);

export const MATERIALIZED_ACCEPT_RUN_REQUIRED_FIELDS0 = Object.freeze([
  'RunID',
  'GeneratedPackage',
  'AggregateCheck',
  'ReplayTranscript',
  'AuditLogs',
  'RejectLog',
  'Verdict',
  'PublicClaimBoundary',
]);

export function makeMaterializedReplayFirstFailure0(overrides = {}) {
  return {
    kind: 'MaterializedReplayFirstFailure0',
    version: CHECKER_VERSION,
    index: 0,
    coord: 'ExternalReplayTranscript0.firstFailure',
    path: [
      'ReplayTranscript',
    ],
    rejectionClass: 'ReplayMismatch',
    replayable: true,
    ...overrides,
  };
}

export function makeMaterializedReplayTranscript0({
  verdict = 'pending',
  firstFailure = null,
  entries = null,
  overrides = {},
} = {}) {
  if (!MATERIALIZED_ACCEPT_RUN_VERDICTS0.includes(verdict)) {
    throw new TypeError(`unknown materialized replay verdict: ${String(verdict)}`);
  }

  const replayAccepted = verdict === 'accept';
  const effectiveFirstFailure = verdict === 'reject'
    ? firstFailure ?? makeMaterializedReplayFirstFailure0()
    : null;

  const material = {
    kind: 'MaterializedReplayTranscript0',
    version: CHECKER_VERSION,
    verdict,
    replayAccepted,
    phaseOrder: MATERIALIZED_ACCEPT_RUN_PHASES0,
    entries: entries ?? MATERIALIZED_ACCEPT_RUN_PHASES0.map((phase, index) => ({
      index,
      phase,
      replayed: verdict !== 'pending',
    })),
    firstFailure: effectiveFirstFailure,
    replayable: true,
    generatorUntrusted: true,
    materializedOutputOnly: true,
    canonicalByteEquality: true,
    noDigestOnlyEquality: true,
    publicConclusionEmitted: false,
    publicConclusion: null,
    ...overrides,
  };

  return {
    ...material,
    transcriptDigest: digestCanonical0(material),
  };
}

export function makeMaterializedAcceptRunVerdict0({
  verdict = 'pending',
  publicConclusionEmitted = false,
  publicConclusion = null,
  overrides = {},
} = {}) {
  return {
    kind: 'MaterializedAcceptRunVerdict0',
    version: CHECKER_VERSION,
    verdict,
    conditional: true,
    noClaimBeforeAccept: true,
    publicConclusionEmitted,
    publicConclusion,
    ...overrides,
  };
}

export function makeMaterializedAcceptRun0({
  packFilePath,
  aggregateDigest,
  verdict = 'pending',
  replayTranscript = null,
  overrides = {},
} = {}) {
  const transcript = replayTranscript ?? makeMaterializedReplayTranscript0({
    verdict,
  });

  const accepted = verdict === 'accept';
  const rejected = verdict === 'reject';

  return {
    kind: 'MaterializedAcceptRun0',
    version: CHECKER_VERSION,

    RunID: 'materialized-accept-run.synthetic-envelope.0',

    GeneratedPackage: {
      kind: 'MaterializedGeneratedPackageRef0',
      version: CHECKER_VERSION,
      path: packFilePath,
      generator: 'GeneratePCCPack',
      generatorUntrusted: true,
      materializedOutputOnly: true,
      canonicalByteEquality: true,
      noDigestOnlyEquality: true,
      coreExcludesAcceptRun: true,
    },

    AggregateCheck: {
      kind: 'MaterializedAggregateCheckRef0',
      version: CHECKER_VERSION,
      checker: 'CheckMaterializedAggregateFile0',
      status: 'accepted',
      accepted: true,
      packagePath: packFilePath,
      digest: aggregateDigest,
      publicConclusionEmitted: false,
    },

    ReplayTranscript: transcript,

    AuditLogs: {
      kind: 'MaterializedAcceptRunAuditLogs0',
      version: CHECKER_VERSION,
      canonicalByteComparisons: [
        {
          left: 'GeneratedPackage.path',
          right: 'AggregateCheck.packagePath',
          method: 'materialized-file-path',
          equal: true,
        },
      ],
      digestComparisonsOnly: false,
      replayable: true,
    },

    RejectLog: rejected
      ? [
          transcript.firstFailure,
        ]
      : [],

    Verdict: makeMaterializedAcceptRunVerdict0({
      verdict,
      publicConclusionEmitted: accepted,
      publicConclusion: accepted
        ? {
            ...MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
          }
        : null,
    }),

    PublicClaimBoundary: {
      ...MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
    },

    ...overrides,
  };
}

export async function CheckMaterializedAcceptRun0(run, config = {}) {
  const checker = 'CheckMaterializedAcceptRun0';
  const ledger = [];

  const shape = validateAcceptRunShape0(run);

  ledger.push({
    phase: 'shape',
    status: shape.ok ? 'pass' : 'fail',
    digest: digestCanonical0(shape.nf ?? shape.witness ?? null),
  });

  if (!shape.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: shape.path,
      witness: shape.witness,
      ledger,
    });
  }

  const packageRef = validateGeneratedPackageRef0(run.GeneratedPackage);

  ledger.push({
    phase: 'generatedPackageRef',
    status: packageRef.ok ? 'pass' : 'fail',
    digest: digestCanonical0(packageRef.nf ?? packageRef.witness ?? null),
  });

  if (!packageRef.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.GeneratedPackage`,
      path: packageRef.path,
      witness: packageRef.witness,
      ledger,
    });
  }

  const noEmbedded = validateNoEmbeddedGeneratedPackageBytes0(run);

  ledger.push({
    phase: 'noEmbeddedPackageBytes',
    status: noEmbedded.ok ? 'pass' : 'fail',
    digest: digestCanonical0(noEmbedded.nf ?? noEmbedded.witness ?? null),
  });

  if (!noEmbedded.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.noEmbeddedPackageBytes`,
      path: noEmbedded.path,
      witness: noEmbedded.witness,
      ledger,
    });
  }

  const aggregateRecord = await CheckMaterializedAggregateFile0(
    run.GeneratedPackage.path,
    config.aggregateConfig ?? {},
  );
  const aggregate = recordToValidation0(aggregateRecord, ['GeneratedPackage', 'path']);

  ledger.push({
    phase: 'CheckMaterializedAggregateFile0',
    status: aggregate.ok ? 'pass' : 'fail',
    digest: aggregateRecord.Digest ?? aggregateRecord.digest ?? digestCanonical0(aggregateRecord),
  });

  if (!aggregate.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.aggregate`,
      path: aggregate.path,
      witness: aggregate.witness,
      ledger,
    });
  }

  const aggregateRef = validateAggregateCheckRef0(run.AggregateCheck, run.GeneratedPackage, aggregateRecord);

  ledger.push({
    phase: 'aggregateCheckRef',
    status: aggregateRef.ok ? 'pass' : 'fail',
    digest: digestCanonical0(aggregateRef.nf ?? aggregateRef.witness ?? null),
  });

  if (!aggregateRef.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.AggregateCheck`,
      path: aggregateRef.path,
      witness: aggregateRef.witness,
      ledger,
    });
  }

  const transcript = validateReplayTranscript0(run.ReplayTranscript);

  ledger.push({
    phase: 'replayTranscript',
    status: transcript.ok ? 'pass' : 'fail',
    digest: digestCanonical0(transcript.nf ?? transcript.witness ?? null),
  });

  if (!transcript.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.ReplayTranscript`,
      path: transcript.path,
      witness: transcript.witness,
      ledger,
    });
  }

  const audit = validateAuditLogs0(run.AuditLogs);

  ledger.push({
    phase: 'auditLogs',
    status: audit.ok ? 'pass' : 'fail',
    digest: digestCanonical0(audit.nf ?? audit.witness ?? null),
  });

  if (!audit.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.AuditLogs`,
      path: audit.path,
      witness: audit.witness,
      ledger,
    });
  }

  const rejectLog = validateRejectLog0(run);

  ledger.push({
    phase: 'rejectLog',
    status: rejectLog.ok ? 'pass' : 'fail',
    digest: digestCanonical0(rejectLog.nf ?? rejectLog.witness ?? null),
  });

  if (!rejectLog.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.RejectLog`,
      path: rejectLog.path,
      witness: rejectLog.witness,
      ledger,
    });
  }

  const publicBoundary = validatePublicClaimBoundary0(run.PublicClaimBoundary);

  ledger.push({
    phase: 'publicClaimBoundary',
    status: publicBoundary.ok ? 'pass' : 'fail',
    digest: digestCanonical0(publicBoundary.nf ?? publicBoundary.witness ?? null),
  });

  if (!publicBoundary.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.PublicClaimBoundary`,
      path: publicBoundary.path,
      witness: publicBoundary.witness,
      ledger,
    });
  }

  const verdict = validateAcceptRunVerdict0(run);

  ledger.push({
    phase: 'verdict',
    status: verdict.ok ? 'pass' : 'fail',
    digest: digestCanonical0(verdict.nf ?? verdict.witness ?? null),
  });

  if (!verdict.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.Verdict`,
      path: verdict.path,
      witness: verdict.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedAcceptRun0NF',
    checker,
    version: CHECKER_VERSION,
    runId: run.RunID,
    generatedPackagePath: run.GeneratedPackage.path,
    aggregateDigest: aggregateRecord.Digest ?? aggregateRecord.digest,
    transcriptDigest: run.ReplayTranscript.transcriptDigest,
    verdict: run.Verdict.verdict,
    replayAccepted: run.ReplayTranscript.replayAccepted,
    rejectLogCount: run.RejectLog.length,
    publicConclusionEmitted: run.Verdict.publicConclusionEmitted,
    publicConclusion: run.Verdict.publicConclusion,
    publicClaimBoundary: run.PublicClaimBoundary,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckMaterializedAcceptRunFile0(filePath, config = {}) {
  const checker = 'CheckMaterializedAcceptRunFile0';
  const ledger = [];

  const loaded = await loadAcceptRunFile0(filePath, config.loaderConfig ?? {});
  const loadResult = loaded.ok
    ? validationAccept0(loaded.nf)
    : validationReject0(loaded.path, loaded.witness.reason, loaded.witness.detail);

  ledger.push({
    phase: 'load',
    status: loadResult.ok ? 'pass' : 'fail',
    digest: digestCanonical0(loadResult.nf ?? loadResult.witness ?? null),
  });

  if (!loadResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.load`,
      path: loadResult.path,
      witness: loadResult.witness,
      ledger,
    });
  }

  const checked = await CheckMaterializedAcceptRun0(loaded.value, config);
  const checkResult = recordToValidation0(checked, ['AcceptRun']);

  ledger.push({
    phase: 'CheckMaterializedAcceptRun0',
    status: checkResult.ok ? 'pass' : 'fail',
    digest: checked.Digest ?? checked.digest ?? digestCanonical0(checked),
  });

  if (!checkResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.acceptRun`,
      path: checkResult.path,
      witness: checkResult.witness,
      ledger,
    });
  }

  const checkedNF = checked.NF ?? checked.nf;

  const nf = {
    kind: 'MaterializedAcceptRunFile0NF',
    checker,
    version: CHECKER_VERSION,
    filePath: loaded.nf.filePath,
    byteLength: loaded.nf.byteLength,
    fileDigest: loaded.nf.fileDigest,
    acceptRunDigest: checked.Digest ?? checked.digest,
    verdict: checkedNF.verdict,
    replayAccepted: checkedNF.replayAccepted,
    rejectLogCount: checkedNF.rejectLogCount,
    publicConclusionEmitted: checkedNF.publicConclusionEmitted,
    publicConclusion: checkedNF.publicConclusion,
    transcriptDigest: checkedNF.transcriptDigest,
    generatedPackagePath: checkedNF.generatedPackagePath,
    aggregateDigest: checkedNF.aggregateDigest,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateAcceptRunShape0(run) {
  if (!isPlainObject(run)) {
    return validationReject0([], 'MaterializedAcceptRun0 must be an object', {
      actual: typeof run,
    });
  }

  if (run.kind !== undefined && run.kind !== 'MaterializedAcceptRun0') {
    return validationReject0(['kind'], 'MaterializedAcceptRun0 kind must be MaterializedAcceptRun0 when present', {
      actual: run.kind,
    });
  }

  if (run.version !== undefined && run.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedAcceptRun0 version must be ${CHECKER_VERSION} when present`, {
      actual: run.version,
    });
  }

  for (const field of MATERIALIZED_ACCEPT_RUN_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(run, field)) {
      return validationReject0([field], 'MaterializedAcceptRun0 is missing a required field', {
        field,
      });
    }
  }

  if (typeof run.RunID !== 'string' || run.RunID.length === 0) {
    return validationReject0(['RunID'], 'MaterializedAcceptRun0 RunID must be a non-empty string', {
      actual: run.RunID,
    });
  }

  return validationAccept0({
    kind: 'MaterializedAcceptRunShape0NF',
  });
}

function validateGeneratedPackageRef0(ref) {
  if (!isPlainObject(ref)) {
    return validationReject0(['GeneratedPackage'], 'GeneratedPackage must be an object', {
      actual: typeof ref,
    });
  }

  if (ref.kind !== 'MaterializedGeneratedPackageRef0') {
    return validationReject0(['GeneratedPackage', 'kind'], 'GeneratedPackage kind mismatch', {
      actual: ref.kind,
    });
  }

  if (typeof ref.path !== 'string' || ref.path.length === 0) {
    return validationReject0(['GeneratedPackage', 'path'], 'GeneratedPackage path must be a non-empty string', {
      actual: ref.path,
    });
  }

  for (const field of [
    'generatorUntrusted',
    'materializedOutputOnly',
    'canonicalByteEquality',
    'noDigestOnlyEquality',
    'coreExcludesAcceptRun',
  ]) {
    if (ref[field] !== true) {
      return validationReject0(['GeneratedPackage', field], `GeneratedPackage must certify ${field}`, {
        actual: ref[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedGeneratedPackageRef0NF',
  });
}

function validateNoEmbeddedGeneratedPackageBytes0(run) {
  const forbiddenRootFields = [
    'Pgen',
    'CoreBytes',
    'PackBytes',
  ];

  for (const field of forbiddenRootFields) {
    if (Object.prototype.hasOwnProperty.call(run, field)) {
      return validationReject0([field], 'MaterializedAcceptRun0 must not embed generated package bytes or Pgen', {
        field,
      });
    }
  }

  for (const field of forbiddenRootFields) {
    if (Object.prototype.hasOwnProperty.call(run.GeneratedPackage, field)) {
      return validationReject0(['GeneratedPackage', field], 'GeneratedPackage ref must not embed generated package bytes or Pgen', {
        field,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedNoEmbeddedGeneratedPackageBytes0NF',
  });
}

function validateAggregateCheckRef0(ref, generatedPackage, aggregateRecord) {
  if (!isPlainObject(ref)) {
    return validationReject0(['AggregateCheck'], 'AggregateCheck must be an object', {
      actual: typeof ref,
    });
  }

  if (ref.kind !== 'MaterializedAggregateCheckRef0') {
    return validationReject0(['AggregateCheck', 'kind'], 'AggregateCheck kind mismatch', {
      actual: ref.kind,
    });
  }

  if (ref.checker !== 'CheckMaterializedAggregateFile0') {
    return validationReject0(['AggregateCheck', 'checker'], 'AggregateCheck checker mismatch', {
      actual: ref.checker,
    });
  }

  if (ref.status !== 'accepted' || ref.accepted !== true) {
    return validationReject0(['AggregateCheck', 'status'], 'AggregateCheck must record accepted aggregate package precondition', {
      status: ref.status,
      accepted: ref.accepted,
    });
  }

  if (ref.packagePath !== generatedPackage.path) {
    return validationReject0(['AggregateCheck', 'packagePath'], 'AggregateCheck packagePath must match GeneratedPackage.path', {
      expected: generatedPackage.path,
      actual: ref.packagePath,
    });
  }

  if (!sameDigestRecord0(ref.digest, aggregateRecord.Digest ?? aggregateRecord.digest)) {
    return validationReject0(['AggregateCheck', 'digest'], 'AggregateCheck digest must match CheckMaterializedAggregateFile0 digest', {
      expected: aggregateRecord.Digest ?? aggregateRecord.digest,
      actual: ref.digest,
    });
  }

  if (ref.publicConclusionEmitted === true) {
    return validationReject0(['AggregateCheck', 'publicConclusionEmitted'], 'AggregateCheck must not emit public conclusion directly', {
      actual: ref.publicConclusionEmitted,
    });
  }

  return validationAccept0({
    kind: 'MaterializedAggregateCheckRef0NF',
  });
}

function validateReplayTranscript0(transcript) {
  if (!isPlainObject(transcript)) {
    return validationReject0(['ReplayTranscript'], 'ReplayTranscript must be an object', {
      actual: typeof transcript,
    });
  }

  if (transcript.kind !== 'MaterializedReplayTranscript0') {
    return validationReject0(['ReplayTranscript', 'kind'], 'ReplayTranscript kind mismatch', {
      actual: transcript.kind,
    });
  }

  if (!MATERIALIZED_ACCEPT_RUN_VERDICTS0.includes(transcript.verdict)) {
    return validationReject0(['ReplayTranscript', 'verdict'], 'ReplayTranscript verdict is not allowed', {
      actual: transcript.verdict,
    });
  }

  if (transcript.replayAccepted !== (transcript.verdict === 'accept')) {
    return validationReject0(['ReplayTranscript', 'replayAccepted'], 'ReplayTranscript replayAccepted must match verdict', {
      verdict: transcript.verdict,
      replayAccepted: transcript.replayAccepted,
    });
  }

  if (!Array.isArray(transcript.phaseOrder)) {
    return validationReject0(['ReplayTranscript', 'phaseOrder'], 'ReplayTranscript phaseOrder must be an array', {
      actual: typeof transcript.phaseOrder,
    });
  }

  for (let index = 0; index < MATERIALIZED_ACCEPT_RUN_PHASES0.length; index += 1) {
    if (transcript.phaseOrder[index] !== MATERIALIZED_ACCEPT_RUN_PHASES0[index]) {
      return validationReject0(['ReplayTranscript', 'phaseOrder', index], 'ReplayTranscript phaseOrder mismatch', {
        expected: MATERIALIZED_ACCEPT_RUN_PHASES0[index],
        actual: transcript.phaseOrder[index],
      });
    }
  }

  if (!Array.isArray(transcript.entries)) {
    return validationReject0(['ReplayTranscript', 'entries'], 'ReplayTranscript entries must be an array', {
      actual: typeof transcript.entries,
    });
  }

  for (const field of [
    'replayable',
    'generatorUntrusted',
    'materializedOutputOnly',
    'canonicalByteEquality',
    'noDigestOnlyEquality',
  ]) {
    if (transcript[field] !== true) {
      return validationReject0(['ReplayTranscript', field], `ReplayTranscript must certify ${field}`, {
        actual: transcript[field],
      });
    }
  }

  if (transcript.publicConclusionEmitted === true || transcript.publicConclusion !== null) {
    return validationReject0(['ReplayTranscript', 'publicConclusion'], 'ReplayTranscript must not emit public conclusion directly', {
      publicConclusionEmitted: transcript.publicConclusionEmitted,
      publicConclusion: transcript.publicConclusion,
    });
  }

  if (transcript.verdict === 'reject') {
    if (!isReplayableFirstFailure0(transcript.firstFailure)) {
      return validationReject0(['ReplayTranscript', 'firstFailure'], 'reject transcript must contain a replayable first failure', {
        actual: transcript.firstFailure,
      });
    }
  } else if (transcript.firstFailure !== null) {
    return validationReject0(['ReplayTranscript', 'firstFailure'], 'non-reject transcript must not contain firstFailure', {
      actual: transcript.firstFailure,
    });
  }

  const expectedDigest = expectedTranscriptDigest0(transcript);

  if (!sameDigestRecord0(transcript.transcriptDigest, expectedDigest)) {
    return validationReject0(['ReplayTranscript', 'transcriptDigest'], 'ReplayTranscript transcriptDigest mismatch', {
      expected: expectedDigest,
      actual: transcript.transcriptDigest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedReplayTranscript0NF',
    verdict: transcript.verdict,
  });
}

function validateAuditLogs0(logs) {
  if (!isPlainObject(logs)) {
    return validationReject0(['AuditLogs'], 'AuditLogs must be an object', {
      actual: typeof logs,
    });
  }

  if (logs.digestComparisonsOnly === true) {
    return validationReject0(['AuditLogs', 'digestComparisonsOnly'], 'AuditLogs must not use digest equality as package equality', {
      actual: logs.digestComparisonsOnly,
    });
  }

  if (logs.replayable !== true) {
    return validationReject0(['AuditLogs', 'replayable'], 'AuditLogs must be replayable', {
      actual: logs.replayable,
    });
  }

  if (!Array.isArray(logs.canonicalByteComparisons)) {
    return validationReject0(['AuditLogs', 'canonicalByteComparisons'], 'AuditLogs must include canonical byte comparisons', {
      actual: typeof logs.canonicalByteComparisons,
    });
  }

  const hasPathComparison = logs.canonicalByteComparisons.some((entry) => (
    entry.left === 'GeneratedPackage.path' &&
    entry.right === 'AggregateCheck.packagePath' &&
    entry.equal === true
  ));

  if (!hasPathComparison) {
    return validationReject0(['AuditLogs', 'canonicalByteComparisons'], 'AuditLogs must compare generated package path with aggregate package path', null);
  }

  return validationAccept0({
    kind: 'MaterializedAcceptRunAuditLogs0NF',
  });
}

function validateRejectLog0(run) {
  if (!Array.isArray(run.RejectLog)) {
    return validationReject0(['RejectLog'], 'RejectLog must be an array', {
      actual: typeof run.RejectLog,
    });
  }

  if (run.ReplayTranscript.verdict === 'reject') {
    if (run.RejectLog.length !== 1) {
      return validationReject0(['RejectLog'], 'reject verdict must contain exactly one first rejection entry', {
        actual: run.RejectLog.length,
      });
    }

    const first = run.RejectLog[0];

    if (!isReplayableFirstFailure0(first)) {
      return validationReject0(['RejectLog', 0], 'RejectLog first entry must be replayable', {
        actual: first,
      });
    }

    if (
      first.coord !== run.ReplayTranscript.firstFailure.coord ||
      JSON.stringify(first.path) !== JSON.stringify(run.ReplayTranscript.firstFailure.path)
    ) {
      return validationReject0(['RejectLog', 0], 'RejectLog first entry must match ReplayTranscript.firstFailure', {
        rejectLog: first,
        firstFailure: run.ReplayTranscript.firstFailure,
      });
    }

    return validationAccept0({
      kind: 'MaterializedRejectLog0NF',
      rejectLogCount: 1,
    });
  }

  if (run.RejectLog.length !== 0) {
    return validationReject0(['RejectLog'], 'non-reject verdict must have an empty RejectLog', {
      actual: run.RejectLog.length,
    });
  }

  return validationAccept0({
    kind: 'MaterializedRejectLog0NF',
    rejectLogCount: 0,
  });
}

function validateAcceptRunVerdict0(run) {
  const verdict = run.Verdict;

  if (!isPlainObject(verdict)) {
    return validationReject0(['Verdict'], 'Verdict must be an object', {
      actual: typeof verdict,
    });
  }

  if (verdict.kind !== 'MaterializedAcceptRunVerdict0') {
    return validationReject0(['Verdict', 'kind'], 'Verdict kind mismatch', {
      actual: verdict.kind,
    });
  }

  if (verdict.verdict !== run.ReplayTranscript.verdict) {
    return validationReject0(['Verdict', 'verdict'], 'Verdict must match ReplayTranscript verdict', {
      expected: run.ReplayTranscript.verdict,
      actual: verdict.verdict,
    });
  }

  if (verdict.conditional !== true) {
    return validationReject0(['Verdict', 'conditional'], 'Verdict must be conditional', {
      actual: verdict.conditional,
    });
  }

  if (verdict.noClaimBeforeAccept !== true) {
    return validationReject0(['Verdict', 'noClaimBeforeAccept'], 'Verdict must certify noClaimBeforeAccept', {
      actual: verdict.noClaimBeforeAccept,
    });
  }

  if (verdict.verdict === 'accept') {
    if (verdict.publicConclusionEmitted !== true) {
      return validationReject0(['Verdict', 'publicConclusionEmitted'], 'accept verdict must emit public conclusion', {
        actual: verdict.publicConclusionEmitted,
      });
    }

    if (!samePublicConclusion0(verdict.publicConclusion, MATERIALIZED_PACK_PUBLIC_BOUNDARY0)) {
      return validationReject0(['Verdict', 'publicConclusion'], 'accept verdict public conclusion mismatch', {
        expected: MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
        actual: verdict.publicConclusion,
      });
    }

    return validationAccept0({
      kind: 'MaterializedAcceptRunVerdict0NF',
      verdict: 'accept',
    });
  }

  if (verdict.publicConclusionEmitted !== false || verdict.publicConclusion !== null) {
    return validationReject0(['Verdict', 'publicConclusion'], 'non-accept verdict must not emit public conclusion', {
      publicConclusionEmitted: verdict.publicConclusionEmitted,
      publicConclusion: verdict.publicConclusion,
    });
  }

  return validationAccept0({
    kind: 'MaterializedAcceptRunVerdict0NF',
    verdict: verdict.verdict,
  });
}

function validatePublicClaimBoundary0(boundary) {
  if (!isPlainObject(boundary)) {
    return validationReject0(['PublicClaimBoundary'], 'PublicClaimBoundary must be an object', {
      actual: typeof boundary,
    });
  }

  if (!samePublicConclusion0(boundary, MATERIALIZED_PACK_PUBLIC_BOUNDARY0)) {
    return validationReject0(['PublicClaimBoundary'], 'PublicClaimBoundary mismatch', {
      expected: MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
      actual: boundary,
    });
  }

  return validationAccept0({
    kind: 'MaterializedAcceptRunPublicClaimBoundary0NF',
  });
}

function isReplayableFirstFailure0(value) {
  return (
    isPlainObject(value) &&
    Number.isInteger(value.index) &&
    value.index >= 0 &&
    typeof value.coord === 'string' &&
    value.coord.length > 0 &&
    Array.isArray(value.path) &&
    typeof value.rejectionClass === 'string' &&
    value.rejectionClass.length > 0 &&
    value.replayable === true
  );
}

function expectedTranscriptDigest0(transcript) {
  const material = {};

  for (const key of Object.keys(transcript).sort()) {
    if (key !== 'transcriptDigest') {
      material[key] = transcript[key];
    }
  }

  return digestCanonical0(material);
}

async function loadAcceptRunFile0(filePath, config) {
  const maxBytes = Number.isInteger(config.maxBytes) && config.maxBytes > 0
    ? config.maxBytes
    : 16 * 1024 * 1024;

  const normalized = normalizeFilePath0(filePath);

  if (!normalized.ok) {
    return normalized;
  }

  let stat;

  try {
    stat = await fs.stat(normalized.filePath);
  } catch (error) {
    return validationRejectLike0(['filePath'], 'materialized accept run file must exist', {
      filePath: normalized.filePath,
      error: error.message,
    });
  }

  if (!stat.isFile()) {
    return validationRejectLike0(['filePath'], 'materialized accept run path must be a file', {
      filePath: normalized.filePath,
    });
  }

  if (stat.size > maxBytes) {
    return validationRejectLike0(['filePath'], 'materialized accept run file exceeds maxBytes', {
      filePath: normalized.filePath,
      maxBytes,
      actualBytes: stat.size,
    });
  }

  let text;

  try {
    text = await fs.readFile(normalized.filePath, 'utf8');
  } catch (error) {
    return validationRejectLike0(['filePath'], 'materialized accept run file must be readable UTF-8 text', {
      filePath: normalized.filePath,
      error: error.message,
    });
  }

  let value;

  try {
    value = JSON.parse(text);
  } catch (error) {
    return validationRejectLike0(['file'], 'materialized accept run file must parse as JSON', {
      error: error.message,
    });
  }

  return {
    ok: true,
    value,
    nf: {
      kind: 'LoadedMaterializedAcceptRunFile0NF',
      filePath: normalized.filePath,
      byteLength: Buffer.byteLength(text, 'utf8'),
      fileDigest: digestCanonical0(text),
      acceptRunDigest: digestCanonical0(value),
    },
  };
}

function normalizeFilePath0(filePath) {
  if (filePath instanceof URL) {
    return {
      ok: true,
      filePath: fileURLToPath(filePath),
    };
  }

  if (typeof filePath !== 'string' || filePath.length === 0) {
    return validationRejectLike0(['filePath'], 'filePath must be a non-empty string or file URL', {
      actual: filePath,
    });
  }

  return {
    ok: true,
    filePath,
  };
}

function validationRejectLike0(path, reason, detail) {
  return {
    ok: false,
    path,
    witness: {
      reason,
      detail,
    },
  };
}

function sameDigestRecord0(a, b) {
  return (
    isPlainObject(a) &&
    isPlainObject(b) &&
    a.alg === b.alg &&
    a.bytes === b.bytes &&
    a.hex === b.hex
  );
}

function samePublicConclusion0(a, b) {
  return (
    isPlainObject(a) &&
    isPlainObject(b) &&
    a.antecedent === b.antecedent &&
    a.consequent === b.consequent &&
    a.conditional === b.conditional
  );
}

function recordToValidation0(record, path) {
  if (isRejectRecord0(record)) {
    return validationReject0(path, `${record.checker} rejected`, {
      inner: compactReject0(record),
    });
  }

  return validationAccept0(record.NF ?? record.nf ?? record);
}

function makeAcceptRecord({
  checker,
  nf,
  ledger,
}) {
  const digest = digestCanonical0(nf);

  return {
    tag: 'accept',
    kind: 'accept',
    checker,
    version: CHECKER_VERSION,
    NF: nf,
    Digest: digest,
    Ledger: ledger,
    nf,
    digest,
    ledger,
  };
}

function makeRejectRecord({
  checker,
  coord,
  path,
  witness,
  ledger,
}) {
  const rejectNF = {
    kind: `${checker}RejectNF`,
    checker,
    version: CHECKER_VERSION,
    coord,
    path,
    witness,
    ledger,
  };

  const digest = digestCanonical0(rejectNF);

  return {
    tag: 'reject',
    kind: 'reject',
    checker,
    version: CHECKER_VERSION,
    Coord: coord,
    Path: path,
    Witness: witness,
    Digest: digest,
    Ledger: ledger,
    coord,
    path,
    witness,
    digest,
    ledger,
  };
}

function validationAccept0(nf) {
  return {
    ok: true,
    nf,
  };
}

function validationReject0(path, reason, detail) {
  return {
    ok: false,
    path,
    witness: {
      reason,
      detail,
    },
  };
}

function isRejectRecord0(value) {
  return classifyRecord0(value) === 'reject';
}

function classifyRecord0(value) {
  if (!isPlainObject(value)) {
    return 'unknown';
  }

  const raw =
    value.tag ??
    value.kind ??
    value.verdict ??
    value.status ??
    value.result ??
    value.outcome;

  if (typeof raw !== 'string') {
    return 'unknown';
  }

  const normalized = raw.trim().toLowerCase();

  if (
    normalized === 'accept' ||
    normalized === 'accepted' ||
    normalized === 'ok' ||
    normalized === 'pass' ||
    normalized === 'passed'
  ) {
    return 'accept';
  }

  if (
    normalized === 'reject' ||
    normalized === 'rejected' ||
    normalized === 'err' ||
    normalized === 'error' ||
    normalized === 'fail' ||
    normalized === 'failed'
  ) {
    return 'reject';
  }

  return 'unknown';
}

function compactReject0(value) {
  if (!isPlainObject(value)) {
    return value;
  }

  return {
    checker: value.checker ?? null,
    coord: value.Coord ?? value.coord ?? null,
    path: value.Path ?? value.path ?? null,
    witness: value.Witness ?? value.witness ?? null,
    digest: value.Digest ?? value.digest ?? null,
  };
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}