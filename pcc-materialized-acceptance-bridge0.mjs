import fs from 'node:fs/promises';
import { fileURLToPath } from 'node:url';

import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
} from './pcc-materialized-pack0.mjs';

import {
  CheckMaterializedAggregate0,
  makeMaterializedAggregateShell0,
} from './pcc-materialized-aggregate0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_ACCEPTANCE_BRIDGE_PHASES0 = Object.freeze([
  'CheckMaterializedAggregate0',
  'CheckPCCPackexpPrecondition0',
  'CheckExternalAcceptRunReplay0',
  'EmitMaterializedBridgeVerdict0',
]);

export const MATERIALIZED_ACCEPTANCE_REPLAY_VERDICTS0 = Object.freeze([
  'pending',
  'reject',
  'accept',
]);

export const MATERIALIZED_PCCPACK_CHECK_STATUSES0 = Object.freeze([
  'pending-real-check',
  'rejected',
  'accepted',
]);

export const MATERIALIZED_ACCEPTANCE_BRIDGE_REQUIRED_FIELDS0 = Object.freeze([
  'Shell',
  'CheckPCCPackexp',
  'ExternalAcceptRunReplay',
  'BridgeVerdict',
  'VerdictPolicy',
  'PublicClaimBoundary',
]);

export const MATERIALIZED_ACCEPTANCE_VERDICT_POLICY0 = Object.freeze({
  kind: 'MaterializedAcceptanceVerdictPolicy0',
  version: CHECKER_VERSION,
  generatorUntrusted: true,
  materializedOutputOnly: true,
  canonicalByteEquality: true,
  noDigestOnlyEquality: true,
  publicConclusionOnlyAfterReplayAccept: true,
  rejectEmitsNoPublicConclusion: true,
  firstFailureReplayable: true,
});

export function makeMaterializedCheckPCCPackexpBridge0({
  status = 'pending-real-check',
  aggregateDigest = null,
  overrides = {},
} = {}) {
  if (!MATERIALIZED_PCCPACK_CHECK_STATUSES0.includes(status)) {
    throw new TypeError(`unknown CheckPCCPackexp bridge status: ${String(status)}`);
  }

  return {
    kind: 'CheckPCCPackexpBridge0',
    version: CHECKER_VERSION,
    checker: 'CheckPCCPackexp',
    status,
    accepted: status === 'accepted',
    aggregatePreconditionAccepted: status === 'accepted',
    aggregateDigest,
    generatorUntrusted: true,
    materializedOutputOnly: true,
    canonicalByteEquality: true,
    noDigestOnlyEquality: true,
    publicConclusionEmitted: false,
    ...overrides,
  };
}

export function makeExternalAcceptRunReplay0({
  verdict = 'pending',
  replayDigest = null,
  overrides = {},
} = {}) {
  if (!MATERIALIZED_ACCEPTANCE_REPLAY_VERDICTS0.includes(verdict)) {
    throw new TypeError(`unknown external replay verdict: ${String(verdict)}`);
  }

  return {
    kind: 'ExternalAcceptRunReplay0',
    version: CHECKER_VERSION,
    verdict,
    replayAccepted: verdict === 'accept',
    replayDigest,
    generatorUntrusted: true,
    materializedOutputOnly: true,
    canonicalByteEquality: true,
    noDigestOnlyEquality: true,
    publicConclusionEmitted: false,
    publicConclusion: null,
    RejectLog: verdict === 'reject'
      ? [
          {
            index: 0,
            coord: 'ExternalAcceptRunReplay0.syntheticReject',
            path: [
              'ExternalAcceptRunReplay',
            ],
            rejectionClass: 'ReplayMismatch',
            replayable: true,
          },
        ]
      : [],
    ...overrides,
  };
}

export function makeMaterializedBridgeVerdict0({
  verdict = 'pending',
  publicConclusionEmitted = false,
  publicConclusion = null,
  overrides = {},
} = {}) {
  return {
    kind: 'MaterializedBridgeVerdict0',
    version: CHECKER_VERSION,
    verdict,
    publicConclusionEmitted,
    publicConclusion,
    conditional: true,
    noClaimBeforeAccept: true,
    ...overrides,
  };
}

export function makeMaterializedAcceptanceBridge0({
  shell = makeMaterializedAggregateShell0(),
  checkStatus = 'pending-real-check',
  replayVerdict = 'pending',
  overrides = {},
} = {}) {
  return {
    kind: 'MaterializedAcceptanceBridge0',
    version: CHECKER_VERSION,
    Shell: shell,
    CheckPCCPackexp: makeMaterializedCheckPCCPackexpBridge0({
      status: checkStatus,
    }),
    ExternalAcceptRunReplay: makeExternalAcceptRunReplay0({
      verdict: replayVerdict,
    }),
    BridgeVerdict: makeMaterializedBridgeVerdict0({
      verdict: replayVerdict === 'reject' || checkStatus === 'rejected'
        ? 'reject'
        : 'pending',
      publicConclusionEmitted: false,
      publicConclusion: null,
    }),
    VerdictPolicy: {
      ...MATERIALIZED_ACCEPTANCE_VERDICT_POLICY0,
    },
    PublicClaimBoundary: {
      ...MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
    },
    ...overrides,
  };
}

export function makeAcceptedMaterializedAcceptanceBridge0({
  shell = makeMaterializedAggregateShell0(),
  aggregateDigest = null,
  replayDigest = null,
  overrides = {},
} = {}) {
  return makeMaterializedAcceptanceBridge0({
    shell,
    checkStatus: 'accepted',
    replayVerdict: 'accept',
    overrides: {
      CheckPCCPackexp: makeMaterializedCheckPCCPackexpBridge0({
        status: 'accepted',
        aggregateDigest,
      }),
      ExternalAcceptRunReplay: makeExternalAcceptRunReplay0({
        verdict: 'accept',
        replayDigest,
      }),
      BridgeVerdict: makeMaterializedBridgeVerdict0({
        verdict: 'accept',
        publicConclusionEmitted: true,
        publicConclusion: {
          ...MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
        },
      }),
      ...overrides,
    },
  });
}

export async function CheckMaterializedAcceptanceBridge0(bridge, config = {}) {
  const checker = 'CheckMaterializedAcceptanceBridge0';
  const ledger = [];
  const phaseDigests = [];

  const shape = validateBridgeShape0(bridge);

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

  const aggregateRecord = await CheckMaterializedAggregate0(
    bridge.Shell,
    config.aggregateConfig ?? {},
  );
  const aggregate = recordToValidation0(aggregateRecord, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedAggregate0',
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

  phaseDigests.push({
    phase: 'CheckMaterializedAggregate0',
    digest: aggregateRecord.Digest ?? aggregateRecord.digest,
  });

  const checkPcc = validateCheckPCCPackexpBridge0(bridge.CheckPCCPackexp, aggregateRecord);

  ledger.push({
    phase: 'CheckPCCPackexpPrecondition0',
    status: checkPcc.ok ? 'pass' : 'fail',
    digest: digestCanonical0(checkPcc.nf ?? checkPcc.witness ?? null),
  });

  if (!checkPcc.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.CheckPCCPackexp`,
      path: checkPcc.path,
      witness: checkPcc.witness,
      ledger,
    });
  }

  phaseDigests.push({
    phase: 'CheckPCCPackexpPrecondition0',
    digest: digestCanonical0(checkPcc.nf),
  });

  const replay = validateExternalAcceptRunReplay0(bridge.ExternalAcceptRunReplay, bridge.CheckPCCPackexp);

  ledger.push({
    phase: 'CheckExternalAcceptRunReplay0',
    status: replay.ok ? 'pass' : 'fail',
    digest: digestCanonical0(replay.nf ?? replay.witness ?? null),
  });

  if (!replay.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.ExternalAcceptRunReplay`,
      path: replay.path,
      witness: replay.witness,
      ledger,
    });
  }

  phaseDigests.push({
    phase: 'CheckExternalAcceptRunReplay0',
    digest: digestCanonical0(replay.nf),
  });

  const verdictPolicy = validateVerdictPolicy0(bridge.VerdictPolicy);

  ledger.push({
    phase: 'VerdictPolicy0',
    status: verdictPolicy.ok ? 'pass' : 'fail',
    digest: digestCanonical0(verdictPolicy.nf ?? verdictPolicy.witness ?? null),
  });

  if (!verdictPolicy.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.VerdictPolicy`,
      path: verdictPolicy.path,
      witness: verdictPolicy.witness,
      ledger,
    });
  }

  const publicBoundary = validatePublicClaimBoundary0(bridge.PublicClaimBoundary);

  ledger.push({
    phase: 'PublicClaimBoundary0',
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

  const bridgeVerdict = validateBridgeVerdict0(bridge);

  ledger.push({
    phase: 'EmitMaterializedBridgeVerdict0',
    status: bridgeVerdict.ok ? 'pass' : 'fail',
    digest: digestCanonical0(bridgeVerdict.nf ?? bridgeVerdict.witness ?? null),
  });

  if (!bridgeVerdict.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.BridgeVerdict`,
      path: bridgeVerdict.path,
      witness: bridgeVerdict.witness,
      ledger,
    });
  }

  phaseDigests.push({
    phase: 'EmitMaterializedBridgeVerdict0',
    digest: digestCanonical0(bridgeVerdict.nf),
  });

  const nf = {
    kind: 'MaterializedAcceptanceBridge0NF',
    checker,
    version: CHECKER_VERSION,
    phaseOrder: MATERIALIZED_ACCEPTANCE_BRIDGE_PHASES0,
    phaseDigests,
    aggregateDigest: aggregateRecord.Digest ?? aggregateRecord.digest,
    checkPCCPackexpStatus: bridge.CheckPCCPackexp.status,
    replayVerdict: bridge.ExternalAcceptRunReplay.verdict,
    publicConclusionEmitted: bridge.BridgeVerdict.publicConclusionEmitted,
    publicConclusion: bridge.BridgeVerdict.publicConclusion,
    claimBoundary: 'conditional-on-accepted-materialized-package-and-accepted-external-replay',
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckMaterializedAcceptanceBridgeFile0(filePath, config = {}) {
  const checker = 'CheckMaterializedAcceptanceBridgeFile0';
  const ledger = [];

  const loaded = await loadBridgeFile0(filePath, config.loaderConfig ?? {});
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

  const checked = await CheckMaterializedAcceptanceBridge0(loaded.value, config);
  const checkResult = recordToValidation0(checked, ['Bridge']);

  ledger.push({
    phase: 'CheckMaterializedAcceptanceBridge0',
    status: checkResult.ok ? 'pass' : 'fail',
    digest: checked.Digest ?? checked.digest ?? digestCanonical0(checked),
  });

  if (!checkResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.bridge`,
      path: checkResult.path,
      witness: checkResult.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedAcceptanceBridgeFile0NF',
    checker,
    version: CHECKER_VERSION,
    filePath: loaded.nf.filePath,
    byteLength: loaded.nf.byteLength,
    fileDigest: loaded.nf.fileDigest,
    bridgeDigest: checked.Digest ?? checked.digest,
    publicConclusionEmitted: checked.NF.publicConclusionEmitted,
    replayVerdict: checked.NF.replayVerdict,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateBridgeShape0(bridge) {
  if (!isPlainObject(bridge)) {
    return validationReject0([], 'MaterializedAcceptanceBridge0 must be an object', {
      actual: typeof bridge,
    });
  }

  if (bridge.kind !== undefined && bridge.kind !== 'MaterializedAcceptanceBridge0') {
    return validationReject0(['kind'], 'MaterializedAcceptanceBridge0 kind must be MaterializedAcceptanceBridge0 when present', {
      actual: bridge.kind,
    });
  }

  if (bridge.version !== undefined && bridge.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedAcceptanceBridge0 version must be ${CHECKER_VERSION} when present`, {
      actual: bridge.version,
    });
  }

  for (const field of MATERIALIZED_ACCEPTANCE_BRIDGE_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(bridge, field)) {
      return validationReject0([field], 'MaterializedAcceptanceBridge0 is missing a required field', {
        field,
      });
    }
  }

  if (!isPlainObject(bridge.Shell)) {
    return validationReject0(['Shell'], 'MaterializedAcceptanceBridge0 Shell must be an object', {
      actual: typeof bridge.Shell,
    });
  }

  return validationAccept0({
    kind: 'MaterializedAcceptanceBridgeShape0NF',
  });
}

function validateCheckPCCPackexpBridge0(record, aggregateRecord) {
  if (!isPlainObject(record)) {
    return validationReject0(['CheckPCCPackexp'], 'CheckPCCPackexp bridge record must be an object', {
      actual: typeof record,
    });
  }

  if (record.kind !== 'CheckPCCPackexpBridge0') {
    return validationReject0(['CheckPCCPackexp', 'kind'], 'CheckPCCPackexp bridge kind mismatch', {
      actual: record.kind,
    });
  }

  if (record.checker !== 'CheckPCCPackexp') {
    return validationReject0(['CheckPCCPackexp', 'checker'], 'CheckPCCPackexp bridge checker mismatch', {
      actual: record.checker,
    });
  }

  if (!MATERIALIZED_PCCPACK_CHECK_STATUSES0.includes(record.status)) {
    return validationReject0(['CheckPCCPackexp', 'status'], 'CheckPCCPackexp bridge status is not allowed', {
      actual: record.status,
    });
  }

  for (const field of [
    'generatorUntrusted',
    'materializedOutputOnly',
    'canonicalByteEquality',
    'noDigestOnlyEquality',
  ]) {
    if (record[field] !== true) {
      return validationReject0(['CheckPCCPackexp', field], `CheckPCCPackexp bridge must certify ${field}`, {
        actual: record[field],
      });
    }
  }

  if (record.publicConclusionEmitted === true) {
    return validationReject0(['CheckPCCPackexp', 'publicConclusionEmitted'], 'CheckPCCPackexp bridge must not emit the public conclusion directly', {
      actual: record.publicConclusionEmitted,
    });
  }

  if (record.status === 'accepted') {
    if (record.accepted !== true) {
      return validationReject0(['CheckPCCPackexp', 'accepted'], 'accepted CheckPCCPackexp bridge must set accepted=true', {
        actual: record.accepted,
      });
    }

    if (record.aggregatePreconditionAccepted !== true) {
      return validationReject0(['CheckPCCPackexp', 'aggregatePreconditionAccepted'], 'accepted CheckPCCPackexp bridge must certify aggregatePreconditionAccepted', {
        actual: record.aggregatePreconditionAccepted,
      });
    }

    if (record.aggregateDigest !== null && !sameDigestRecord0(record.aggregateDigest, aggregateRecord.Digest ?? aggregateRecord.digest)) {
      return validationReject0(['CheckPCCPackexp', 'aggregateDigest'], 'CheckPCCPackexp bridge aggregateDigest mismatch', {
        expected: aggregateRecord.Digest ?? aggregateRecord.digest,
        actual: record.aggregateDigest,
      });
    }
  }

  if (record.status !== 'accepted' && record.accepted === true) {
    return validationReject0(['CheckPCCPackexp', 'accepted'], 'non-accepted CheckPCCPackexp bridge must not set accepted=true', {
      status: record.status,
      accepted: record.accepted,
    });
  }

  return validationAccept0({
    kind: 'CheckPCCPackexpBridge0NF',
    status: record.status,
  });
}

function validateExternalAcceptRunReplay0(replay, checkPcc) {
  if (!isPlainObject(replay)) {
    return validationReject0(['ExternalAcceptRunReplay'], 'ExternalAcceptRunReplay must be an object', {
      actual: typeof replay,
    });
  }

  if (replay.kind !== 'ExternalAcceptRunReplay0') {
    return validationReject0(['ExternalAcceptRunReplay', 'kind'], 'ExternalAcceptRunReplay kind mismatch', {
      actual: replay.kind,
    });
  }

  if (!MATERIALIZED_ACCEPTANCE_REPLAY_VERDICTS0.includes(replay.verdict)) {
    return validationReject0(['ExternalAcceptRunReplay', 'verdict'], 'ExternalAcceptRunReplay verdict is not allowed', {
      actual: replay.verdict,
    });
  }

  for (const field of [
    'generatorUntrusted',
    'materializedOutputOnly',
    'canonicalByteEquality',
    'noDigestOnlyEquality',
  ]) {
    if (replay[field] !== true) {
      return validationReject0(['ExternalAcceptRunReplay', field], `ExternalAcceptRunReplay must certify ${field}`, {
        actual: replay[field],
      });
    }
  }

  if (replay.publicConclusionEmitted === true || replay.publicConclusion !== null) {
    return validationReject0(['ExternalAcceptRunReplay', 'publicConclusion'], 'ExternalAcceptRunReplay must not emit the public conclusion directly', {
      publicConclusionEmitted: replay.publicConclusionEmitted,
      publicConclusion: replay.publicConclusion,
    });
  }

  if (!Array.isArray(replay.RejectLog)) {
    return validationReject0(['ExternalAcceptRunReplay', 'RejectLog'], 'ExternalAcceptRunReplay RejectLog must be an array', {
      actual: typeof replay.RejectLog,
    });
  }

  if (replay.verdict === 'accept') {
    if (checkPcc.status !== 'accepted') {
      return validationReject0(['ExternalAcceptRunReplay', 'verdict'], 'external accept replay requires accepted CheckPCCPackexp precondition', {
        checkPCCPackexpStatus: checkPcc.status,
      });
    }

    if (replay.replayAccepted !== true) {
      return validationReject0(['ExternalAcceptRunReplay', 'replayAccepted'], 'accept replay must set replayAccepted=true', {
        actual: replay.replayAccepted,
      });
    }

    if (replay.RejectLog.length !== 0) {
      return validationReject0(['ExternalAcceptRunReplay', 'RejectLog'], 'accept replay must have an empty RejectLog', {
        actual: replay.RejectLog.length,
      });
    }
  }

  if (replay.verdict === 'pending') {
    if (replay.replayAccepted !== false) {
      return validationReject0(['ExternalAcceptRunReplay', 'replayAccepted'], 'pending replay must set replayAccepted=false', {
        actual: replay.replayAccepted,
      });
    }

    if (replay.RejectLog.length !== 0) {
      return validationReject0(['ExternalAcceptRunReplay', 'RejectLog'], 'pending replay must have an empty RejectLog', {
        actual: replay.RejectLog.length,
      });
    }
  }

  if (replay.verdict === 'reject') {
    if (replay.replayAccepted !== false) {
      return validationReject0(['ExternalAcceptRunReplay', 'replayAccepted'], 'reject replay must set replayAccepted=false', {
        actual: replay.replayAccepted,
      });
    }

    if (replay.RejectLog.length !== 1) {
      return validationReject0(['ExternalAcceptRunReplay', 'RejectLog'], 'reject replay must contain exactly one first rejection entry', {
        actual: replay.RejectLog.length,
      });
    }

    if (replay.RejectLog[0].replayable !== true) {
      return validationReject0(['ExternalAcceptRunReplay', 'RejectLog', 0, 'replayable'], 'reject replay first failure must be replayable', {
        actual: replay.RejectLog[0].replayable,
      });
    }
  }

  return validationAccept0({
    kind: 'ExternalAcceptRunReplay0NF',
    verdict: replay.verdict,
  });
}

function validateVerdictPolicy0(policy) {
  if (!isPlainObject(policy)) {
    return validationReject0(['VerdictPolicy'], 'VerdictPolicy must be an object', {
      actual: typeof policy,
    });
  }

  for (const field of [
    'generatorUntrusted',
    'materializedOutputOnly',
    'canonicalByteEquality',
    'noDigestOnlyEquality',
    'publicConclusionOnlyAfterReplayAccept',
    'rejectEmitsNoPublicConclusion',
    'firstFailureReplayable',
  ]) {
    if (policy[field] !== true) {
      return validationReject0(['VerdictPolicy', field], `VerdictPolicy must certify ${field}`, {
        actual: policy[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedAcceptanceVerdictPolicy0NF',
  });
}

function validatePublicClaimBoundary0(boundary) {
  if (!isPlainObject(boundary)) {
    return validationReject0(['PublicClaimBoundary'], 'PublicClaimBoundary must be an object', {
      actual: typeof boundary,
    });
  }

  if (boundary.antecedent !== MATERIALIZED_PACK_PUBLIC_BOUNDARY0.antecedent) {
    return validationReject0(['PublicClaimBoundary', 'antecedent'], 'PublicClaimBoundary antecedent mismatch', {
      expected: MATERIALIZED_PACK_PUBLIC_BOUNDARY0.antecedent,
      actual: boundary.antecedent,
    });
  }

  if (boundary.consequent !== MATERIALIZED_PACK_PUBLIC_BOUNDARY0.consequent) {
    return validationReject0(['PublicClaimBoundary', 'consequent'], 'PublicClaimBoundary consequent mismatch', {
      expected: MATERIALIZED_PACK_PUBLIC_BOUNDARY0.consequent,
      actual: boundary.consequent,
    });
  }

  if (boundary.conditional !== true) {
    return validationReject0(['PublicClaimBoundary', 'conditional'], 'PublicClaimBoundary must be conditional', {
      actual: boundary.conditional,
    });
  }

  return validationAccept0({
    kind: 'MaterializedAcceptancePublicClaimBoundary0NF',
  });
}

function validateBridgeVerdict0(bridge) {
  const verdict = bridge.BridgeVerdict;

  if (!isPlainObject(verdict)) {
    return validationReject0(['BridgeVerdict'], 'BridgeVerdict must be an object', {
      actual: typeof verdict,
    });
  }

  if (verdict.kind !== 'MaterializedBridgeVerdict0') {
    return validationReject0(['BridgeVerdict', 'kind'], 'BridgeVerdict kind mismatch', {
      actual: verdict.kind,
    });
  }

  if (verdict.noClaimBeforeAccept !== true) {
    return validationReject0(['BridgeVerdict', 'noClaimBeforeAccept'], 'BridgeVerdict must certify noClaimBeforeAccept', {
      actual: verdict.noClaimBeforeAccept,
    });
  }

  if (verdict.conditional !== true) {
    return validationReject0(['BridgeVerdict', 'conditional'], 'BridgeVerdict must be conditional', {
      actual: verdict.conditional,
    });
  }

  const ready =
    bridge.CheckPCCPackexp.status === 'accepted' &&
    bridge.ExternalAcceptRunReplay.verdict === 'accept' &&
    bridge.ExternalAcceptRunReplay.replayAccepted === true;

  const expectedVerdict = ready
    ? 'accept'
    : (
        bridge.CheckPCCPackexp.status === 'rejected' ||
        bridge.ExternalAcceptRunReplay.verdict === 'reject'
          ? 'reject'
          : 'pending'
      );

  if (verdict.verdict !== expectedVerdict) {
    return validationReject0(['BridgeVerdict', 'verdict'], 'BridgeVerdict verdict does not match acceptance and replay state', {
      expected: expectedVerdict,
      actual: verdict.verdict,
    });
  }

  if (ready) {
    if (verdict.publicConclusionEmitted !== true) {
      return validationReject0(['BridgeVerdict', 'publicConclusionEmitted'], 'BridgeVerdict must emit public conclusion only after accepted replay', {
        actual: verdict.publicConclusionEmitted,
      });
    }

    if (!samePublicConclusion0(verdict.publicConclusion, MATERIALIZED_PACK_PUBLIC_BOUNDARY0)) {
      return validationReject0(['BridgeVerdict', 'publicConclusion'], 'BridgeVerdict public conclusion mismatch', {
        expected: MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
        actual: verdict.publicConclusion,
      });
    }

    return validationAccept0({
      kind: 'MaterializedBridgeAcceptVerdict0NF',
      verdict: 'accept',
      publicConclusionEmitted: true,
    });
  }

  if (verdict.publicConclusionEmitted !== false || verdict.publicConclusion !== null) {
    return validationReject0(['BridgeVerdict', 'publicConclusion'], 'BridgeVerdict must not emit public conclusion before accepted replay', {
      publicConclusionEmitted: verdict.publicConclusionEmitted,
      publicConclusion: verdict.publicConclusion,
      checkPCCPackexpStatus: bridge.CheckPCCPackexp.status,
      replayVerdict: bridge.ExternalAcceptRunReplay.verdict,
    });
  }

  return validationAccept0({
    kind: 'MaterializedBridgeNonAcceptVerdict0NF',
    verdict: expectedVerdict,
    publicConclusionEmitted: false,
  });
}

async function loadBridgeFile0(filePath, config) {
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
    return validationRejectLike0(['filePath'], 'materialized acceptance bridge file must exist', {
      filePath: normalized.filePath,
      error: error.message,
    });
  }

  if (!stat.isFile()) {
    return validationRejectLike0(['filePath'], 'materialized acceptance bridge path must be a file', {
      filePath: normalized.filePath,
    });
  }

  if (stat.size > maxBytes) {
    return validationRejectLike0(['filePath'], 'materialized acceptance bridge file exceeds maxBytes', {
      filePath: normalized.filePath,
      maxBytes,
      actualBytes: stat.size,
    });
  }

  let text;

  try {
    text = await fs.readFile(normalized.filePath, 'utf8');
  } catch (error) {
    return validationRejectLike0(['filePath'], 'materialized acceptance bridge file must be readable UTF-8 text', {
      filePath: normalized.filePath,
      error: error.message,
    });
  }

  let value;

  try {
    value = JSON.parse(text);
  } catch (error) {
    return validationRejectLike0(['file'], 'materialized acceptance bridge file must parse as JSON', {
      error: error.message,
    });
  }

  return {
    ok: true,
    value,
    nf: {
      kind: 'LoadedMaterializedAcceptanceBridgeFile0NF',
      filePath: normalized.filePath,
      byteLength: Buffer.byteLength(text, 'utf8'),
      fileDigest: digestCanonical0(text),
      bridgeDigest: digestCanonical0(value),
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