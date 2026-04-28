import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckPackSufficiency0,
  PACK_SUFFICIENCY_PHASES0,
  makeSyntheticPCCPack0,
} from './pcc-pack-sufficiency0.mjs';

const CHECKER_VERSION = 0;

export const ACCEPT_RUN_PHASES0 = Object.freeze([
  ...PACK_SUFFICIENCY_PHASES0,
  'Φ14.EmitFinalVerdict0',
]);

export const ACCEPT_RUN_REQUIRED_FIELDS0 = Object.freeze([
  'RunID',
  'GenCall',
  'Pgen',
  'Env',
  'PhaseOrder',
  'Transcript',
  'AuditLogs',
  'RejectLog',
  'Verdict',
]);

export const ACCEPT_RUN_REJECTION_CLASSES0 = Object.freeze([
  'ParseFailure',
  'InterfaceFailure',
  'ScheduleFailure',
  'MissingRow',
  'BadTransport',
  'DuplicateConflict',
  'RoutePriorityFailure',
  'ProofReferenceFailure',
  'KernelFailure',
  'ReflectionFailure',
  'HiddenMinimization',
  'ImportCycle',
  'ForbiddenImport',
  'BoundsFailure',
  'ModeFirewallFailure',
  'ObligationFailure',
  'ChargeFailure',
  'HashProtocolFailure',
  'LockedNANDFailure',
  'FinalFrameworkMismatch',
  'SATDecisionFailure',
  'ReplayMismatch',
]);

export const ACCEPT_RUN_FORBIDDEN_EXEC_SYMBOLS0 = Object.freeze([
  'µ',
  'µ*',
  'µ#',
  'Can',
  'argmin',
  'maxG',
  'minimumEquivalent',
  'optimalCircuit',
  'exactMinSearch',
  'canonicalMinimizer',
  'maximizeGain',
]);

const EXECUTABLE_KEYS0 = new Set([
  'exec',
  'execs',
  'execCall',
  'execCalls',
  'call',
  'calls',
  'callee',
  'operator',
  'operation',
  'program',
  'body',
  'macroBody',
  'templateBody',
  'generatedBody',
]);

export function makeSyntheticAcceptRun0({
  pack = makeSyntheticPCCPack0(),
  verdict = 'accept',
  rejectLog = [],
  overrides = {},
} = {}) {
  const outputCoreBytes = stableStringify0(pack.Core);
  const outputPackBytes = stableStringify0(pack);

  const accepted = verdict === 'accept';

  const run = {
    kind: 'AcceptRun0',
    version: CHECKER_VERSION,

    RunID: 'accept-run.synthetic.0',

    GenCall: {
      kind: 'GenCall0',
      version: CHECKER_VERSION,
      generator: 'GeneratePCCPack',
      args: [],
      deterministic: true,
      untrusted: true,
      materializedOutputOnly: true,
      canonicalByteEquality: true,
      outputCoreBytes,
      outputPackBytes,
      outputCoreDigest: digestCanonical0(outputCoreBytes),
      outputPackDigest: digestCanonical0(outputPackBytes),
    },

    Pgen: pack,

    Env: {
      kind: 'AcceptEnv0',
      version: CHECKER_VERSION,
      deterministic: true,
      platform: 'node-esm',
      noNetwork: true,
      noClockDependency: true,
      noRandomness: true,
      canonicalJson: true,
    },

    PhaseOrder: ACCEPT_RUN_PHASES0,

    Transcript: {
      kind: 'AcceptTranscript0',
      version: CHECKER_VERSION,
      phaseOrder: ACCEPT_RUN_PHASES0,
      entries: ACCEPT_RUN_PHASES0.map((phase, index) => ({
        index,
        phase,
        replayed: true,
      })),
    },

    AuditLogs: {
      kind: 'AcceptAuditLogs0',
      version: CHECKER_VERSION,
      canonicalByteComparisons: [
        {
          left: 'GenCall.outputCoreBytes',
          right: 'Pgen.Core',
          method: 'canonical-bytes',
          equal: true,
        },
        {
          left: 'GenCall.outputPackBytes',
          right: 'Pgen',
          method: 'canonical-bytes',
          equal: true,
        },
      ],
      digestComparisonsOnly: false,
      replayable: true,
    },

    RejectLog: rejectLog,

    Verdict: {
      kind: 'FinalVerdict0',
      version: CHECKER_VERSION,
      verdict,
      conditional: accepted,
      noClaimBeforeAccept: true,
      publicConclusionEmitted: accepted,
      rejectionOnly: !accepted,
      publicConclusion: accepted
        ? {
            antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
            consequent: 'P = NP',
          }
        : null,
    },

    PiRun: {
      kind: 'PiAcceptRun0',
      version: CHECKER_VERSION,
      note: 'synthetic final acceptance run proof marker',
    },

    ...overrides,
  };

  return run;
}

export function makeSyntheticRejectAcceptRun0(overrides = {}) {
  const pack = makeSyntheticPCCPack0();

  pack.GPack = {
    ...pack.GPack,
    ThresholdCert: {
      ...pack.GPack.ThresholdCert,
      residualSlackMax: 5,
    },
  };

  return makeSyntheticAcceptRun0({
    pack,
    verdict: 'reject',
    rejectLog: [
      {
        index: 0,
        coord: 'CheckPackSufficiency0.GPack',
        path: ['GPack'],
        rejectionClass: 'LockedNANDFailure',
        replayable: true,
      },
    ],
    overrides,
  });
}

export async function ReplayAcceptRun0(run) {
  const checker = 'ReplayAcceptRun0';
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

  const generator = validateGeneratorMaterialization0(run);

  ledger.push({
    phase: 'generatorMaterialization',
    status: generator.ok ? 'pass' : 'fail',
    digest: digestCanonical0(generator.nf ?? generator.witness ?? null),
  });

  if (!generator.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.generatorBytes`,
      path: generator.path,
      witness: generator.witness,
      ledger,
    });
  }

  const packRecord = await CheckPackSufficiency0(run.Pgen);
  const packValidation = recordToValidation0(packRecord, ['Pgen']);

  ledger.push({
    phase: 'CheckPackSufficiency0',
    status: packValidation.ok ? 'pass' : 'fail',
    digest: packRecord.Digest ?? packRecord.digest ?? digestCanonical0(packRecord),
  });

  if (!packValidation.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.CheckPackSufficiency0`,
      path: packValidation.path,
      witness: packValidation.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'AcceptRunReplay0NF',
    checker,
    version: CHECKER_VERSION,
    runId: run.RunID,
    generator: run.GenCall.generator,
    coreByteDigest: digestCanonical0(stableStringify0(run.Pgen.Core)),
    packByteDigest: digestCanonical0(stableStringify0(run.Pgen)),
    packSufficiencyDigest: packRecord.Digest ?? packRecord.digest,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckAcceptRun0(run) {
  const checker = 'CheckAcceptRun0';
  const ledger = [];

  const phases = [
    ['shape', `${checker}.input`, () => validateAcceptRunShape0(run)],
    ['env', `${checker}.env`, () => validateAcceptEnv0(run.Env)],
    ['phaseOrder', `${checker}.phaseOrder`, () => validatePhaseOrder0(run.PhaseOrder)],
    ['transcript', `${checker}.transcript`, () => validateTranscript0(run)],
    ['auditLogs', `${checker}.auditLogs`, () => validateAuditLogs0(run)],
  ];

  for (const [phase, coord, runPhase] of phases) {
    const result = runPhase();

    ledger.push({
      phase,
      status: result.ok ? 'pass' : 'fail',
      digest: digestCanonical0(result.nf ?? result.witness ?? null),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  const replayRecord = await ReplayAcceptRun0(run);

  ledger.push({
    phase: 'ReplayAcceptRun0',
    status: isRejectRecord0(replayRecord) ? 'fail' : 'pass',
    digest: replayRecord.Digest ?? replayRecord.digest ?? digestCanonical0(replayRecord),
  });

  const verdict = validateVerdictAgainstReplay0(run, replayRecord);

  ledger.push({
    phase: 'verdict',
    status: verdict.ok ? 'pass' : 'fail',
    digest: digestCanonical0(verdict.nf ?? verdict.witness ?? null),
  });

  if (!verdict.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.verdict`,
      path: verdict.path,
      witness: verdict.witness,
      ledger,
    });
  }

  const noHiddenMin = validateNoHiddenExecutableMin0(run, ['AcceptRun0']);

  ledger.push({
    phase: 'noHiddenMin',
    status: noHiddenMin.ok ? 'pass' : 'fail',
    digest: digestCanonical0(noHiddenMin.nf ?? noHiddenMin.witness ?? null),
  });

  if (!noHiddenMin.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.noHiddenMin`,
      path: noHiddenMin.path,
      witness: noHiddenMin.witness,
      ledger,
    });
  }

  const noOpaque = validateNoOpaqueProof0(run, ['AcceptRun0']);

  ledger.push({
    phase: 'opaque',
    status: noOpaque.ok ? 'pass' : 'fail',
    digest: digestCanonical0(noOpaque.nf ?? noOpaque.witness ?? null),
  });

  if (!noOpaque.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.opaqueProof`,
      path: noOpaque.path,
      witness: noOpaque.witness,
      ledger,
    });
  }

  const replayAccepted = !isRejectRecord0(replayRecord);

  const nf = {
    kind: 'AcceptRun0NF',
    checker,
    version: CHECKER_VERSION,
    runId: run.RunID,
    replayAccepted,
    verdict: run.Verdict.verdict,
    phaseOrder: ACCEPT_RUN_PHASES0,
    publicConclusion: run.Verdict.publicConclusion,
    rejectLogCount: run.RejectLog.length,
    replayDigest: replayRecord.Digest ?? replayRecord.digest,
    piRunDigest: digestCanonical0(getPiRun0(run)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function EmitFinalVerdict0(run) {
  const checker = 'EmitFinalVerdict0';
  const ledger = [];

  const acceptRunRecord = await CheckAcceptRun0(run);

  ledger.push({
    phase: 'CheckAcceptRun0',
    status: isRejectRecord0(acceptRunRecord) ? 'fail' : 'pass',
    digest: acceptRunRecord.Digest ?? acceptRunRecord.digest ?? digestCanonical0(acceptRunRecord),
  });

  if (isRejectRecord0(acceptRunRecord)) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.AcceptRun`,
      path: ['AcceptRun'],
      witness: {
        reason: 'CheckAcceptRun0 rejected',
        inner: compactReject0(acceptRunRecord),
      },
      ledger,
    });
  }

  const verdict = run.Verdict.verdict;

  const nf = {
    kind: 'FinalVerdictEmission0NF',
    checker,
    version: CHECKER_VERSION,
    verdict,
    runId: run.RunID,
    publicConclusionEmitted: verdict === 'accept',
    publicConclusion: verdict === 'accept'
      ? {
          antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
          consequent: 'P = NP',
          conditional: true,
        }
      : null,
    rejectionOnly: verdict === 'reject',
    noClaimBeforeAccept: true,
    acceptRunDigest: acceptRunRecord.Digest ?? acceptRunRecord.digest,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateAcceptRunShape0(run) {
  if (!isPlainObject(run)) {
    return validationReject0([], 'AcceptRun0 must be an object', {
      actual: typeof run,
    });
  }

  if (run.kind !== undefined && run.kind !== 'AcceptRun0') {
    return validationReject0(['kind'], 'AcceptRun0 kind must be AcceptRun0 when present', {
      actual: run.kind,
    });
  }

  if (run.version !== undefined && run.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `AcceptRun0 version must be ${CHECKER_VERSION} when present`, {
      actual: run.version,
    });
  }

  for (const field of ACCEPT_RUN_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(run, field)) {
      return validationReject0([field], 'AcceptRun0 is missing a required field', {
        field,
      });
    }
  }

  if (!isNonEmptyString(run.RunID)) {
    return validationReject0(['RunID'], 'AcceptRun0 RunID must be a non-empty string', {
      actual: run.RunID,
    });
  }

  if (!isPlainObject(run.Pgen)) {
    return validationReject0(['Pgen'], 'AcceptRun0 Pgen must be an object', {
      actual: typeof run.Pgen,
    });
  }

  if (!Array.isArray(run.RejectLog)) {
    return validationReject0(['RejectLog'], 'AcceptRun0 RejectLog must be an array', {
      actual: typeof run.RejectLog,
    });
  }

  if (getPiRun0(run) === undefined) {
    return validationReject0(['PiRun'], 'AcceptRun0 is missing PiRun or Πrun', null);
  }

  return validationAccept0({
    kind: 'AcceptRunShape0NF',
  });
}

function validateGeneratorMaterialization0(run) {
  const gen = run.GenCall;

  if (!isPlainObject(gen)) {
    return validationReject0(['GenCall'], 'GenCall must be an object', {
      actual: typeof gen,
    });
  }

  if (gen.generator !== 'GeneratePCCPack') {
    return validationReject0(['GenCall', 'generator'], 'GenCall generator must be GeneratePCCPack', {
      actual: gen.generator,
    });
  }

  for (const field of [
    'deterministic',
    'untrusted',
    'materializedOutputOnly',
    'canonicalByteEquality',
  ]) {
    if (gen[field] !== true) {
      return validationReject0(['GenCall', field], `GenCall must certify ${field}`, {
        actual: gen[field],
      });
    }
  }

  const coreBytes = stableStringify0(run.Pgen.Core);
  const packBytes = stableStringify0(run.Pgen);

  if (gen.outputCoreBytes !== coreBytes) {
    return validationReject0(['GenCall', 'outputCoreBytes'], 'generated core package must match Pgen.Core by canonical byte equality', {
      expectedDigest: digestCanonical0(coreBytes),
      actualDigest: digestCanonical0(gen.outputCoreBytes),
    });
  }

  if (gen.outputPackBytes !== packBytes) {
    return validationReject0(['GenCall', 'outputPackBytes'], 'generated package must match Pgen by canonical byte equality', {
      expectedDigest: digestCanonical0(packBytes),
      actualDigest: digestCanonical0(gen.outputPackBytes),
    });
  }

  return validationAccept0({
    kind: 'GeneratorMaterialization0NF',
    coreByteDigest: digestCanonical0(coreBytes),
    packByteDigest: digestCanonical0(packBytes),
  });
}

function validateAcceptEnv0(env) {
  if (!isPlainObject(env)) {
    return validationReject0(['Env'], 'AcceptRun0 Env must be an object', {
      actual: typeof env,
    });
  }

  for (const field of [
    'deterministic',
    'noNetwork',
    'noClockDependency',
    'noRandomness',
    'canonicalJson',
  ]) {
    if (env[field] !== true) {
      return validationReject0(['Env', field], `AcceptRun0 Env must certify ${field}`, {
        actual: env[field],
      });
    }
  }

  return validationAccept0({
    kind: 'AcceptEnv0NF',
  });
}

function validatePhaseOrder0(phaseOrder) {
  if (!Array.isArray(phaseOrder)) {
    return validationReject0(['PhaseOrder'], 'AcceptRun0 PhaseOrder must be an array', {
      actual: typeof phaseOrder,
    });
  }

  for (let index = 0; index < ACCEPT_RUN_PHASES0.length; index += 1) {
    if (phaseOrder[index] !== ACCEPT_RUN_PHASES0[index]) {
      return validationReject0(['PhaseOrder', index], 'AcceptRun0 PhaseOrder mismatch', {
        expected: ACCEPT_RUN_PHASES0[index],
        actual: phaseOrder[index],
      });
    }
  }

  if (phaseOrder.length !== ACCEPT_RUN_PHASES0.length) {
    return validationReject0(['PhaseOrder'], 'AcceptRun0 PhaseOrder has the wrong length', {
      expected: ACCEPT_RUN_PHASES0.length,
      actual: phaseOrder.length,
    });
  }

  return validationAccept0({
    kind: 'AcceptPhaseOrder0NF',
    phaseCount: phaseOrder.length,
  });
}

function validateTranscript0(run) {
  const transcript = run.Transcript;

  if (!isPlainObject(transcript)) {
    return validationReject0(['Transcript'], 'AcceptRun0 Transcript must be an object', {
      actual: typeof transcript,
    });
  }

  if (!Array.isArray(transcript.phaseOrder)) {
    return validationReject0(['Transcript', 'phaseOrder'], 'AcceptRun0 transcript phaseOrder must be an array', {
      actual: typeof transcript.phaseOrder,
    });
  }

  for (let index = 0; index < ACCEPT_RUN_PHASES0.length; index += 1) {
    if (transcript.phaseOrder[index] !== ACCEPT_RUN_PHASES0[index]) {
      return validationReject0(['Transcript', 'phaseOrder', index], 'AcceptRun0 transcript phase order mismatch', {
        expected: ACCEPT_RUN_PHASES0[index],
        actual: transcript.phaseOrder[index],
      });
    }
  }

  if (!Array.isArray(transcript.entries)) {
    return validationReject0(['Transcript', 'entries'], 'AcceptRun0 transcript entries must be an array', {
      actual: typeof transcript.entries,
    });
  }

  const phases = new Set(transcript.entries.map((entry) => entry.phase));

  for (const phase of ACCEPT_RUN_PHASES0) {
    if (!phases.has(phase)) {
      return validationReject0(['Transcript', 'entries'], 'AcceptRun0 transcript is missing a phase entry', {
        phase,
      });
    }
  }

  return validationAccept0({
    kind: 'AcceptTranscript0NF',
    entryCount: transcript.entries.length,
  });
}

function validateAuditLogs0(run) {
  const logs = run.AuditLogs;

  if (!isPlainObject(logs)) {
    return validationReject0(['AuditLogs'], 'AcceptRun0 AuditLogs must be an object', {
      actual: typeof logs,
    });
  }

  if (logs.digestComparisonsOnly === true) {
    return validationReject0(['AuditLogs', 'digestComparisonsOnly'], 'AcceptRun0 must not use digest equality as package equality', {
      actual: logs.digestComparisonsOnly,
    });
  }

  if (logs.replayable !== true) {
    return validationReject0(['AuditLogs', 'replayable'], 'AcceptRun0 AuditLogs must be replayable', {
      actual: logs.replayable,
    });
  }

  if (!Array.isArray(logs.canonicalByteComparisons)) {
    return validationReject0(['AuditLogs', 'canonicalByteComparisons'], 'AcceptRun0 AuditLogs must include canonical byte comparisons', {
      actual: typeof logs.canonicalByteComparisons,
    });
  }

  const hasCoreComparison = logs.canonicalByteComparisons.some((entry) => (
    entry.left === 'GenCall.outputCoreBytes' &&
    entry.right === 'Pgen.Core' &&
    entry.method === 'canonical-bytes' &&
    entry.equal === true
  ));

  const hasPackComparison = logs.canonicalByteComparisons.some((entry) => (
    entry.left === 'GenCall.outputPackBytes' &&
    entry.right === 'Pgen' &&
    entry.method === 'canonical-bytes' &&
    entry.equal === true
  ));

  if (!hasCoreComparison) {
    return validationReject0(['AuditLogs', 'canonicalByteComparisons'], 'AcceptRun0 AuditLogs must compare generated core bytes with Pgen.Core', null);
  }

  if (!hasPackComparison) {
    return validationReject0(['AuditLogs', 'canonicalByteComparisons'], 'AcceptRun0 AuditLogs must compare generated pack bytes with Pgen', null);
  }

  return validationAccept0({
    kind: 'AcceptAuditLogs0NF',
  });
}

function validateVerdictAgainstReplay0(run, replayRecord) {
  if (!isPlainObject(run.Verdict)) {
    return validationReject0(['Verdict'], 'AcceptRun0 Verdict must be an object', {
      actual: typeof run.Verdict,
    });
  }

  if (run.Verdict.verdict !== 'accept' && run.Verdict.verdict !== 'reject') {
    return validationReject0(['Verdict', 'verdict'], 'AcceptRun0 verdict must be accept or reject', {
      actual: run.Verdict.verdict,
    });
  }

  if (isRejectRecord0(replayRecord)) {
    if (run.Verdict.verdict !== 'reject') {
      return validationReject0(['Verdict', 'verdict'], 'AcceptRun0 verdict must be reject when replay rejects', {
        actual: run.Verdict.verdict,
        replay: compactReject0(replayRecord),
      });
    }

    if (run.Verdict.publicConclusionEmitted !== false) {
      return validationReject0(['Verdict', 'publicConclusionEmitted'], 'AcceptRun0 reject verdict must not emit a public P = NP conclusion', {
        actual: run.Verdict.publicConclusionEmitted,
      });
    }

    if (run.Verdict.rejectionOnly !== true) {
      return validationReject0(['Verdict', 'rejectionOnly'], 'AcceptRun0 reject verdict must be rejection-only', {
        actual: run.Verdict.rejectionOnly,
      });
    }

    if (run.RejectLog.length !== 1) {
      return validationReject0(['RejectLog'], 'AcceptRun0 reject verdict must contain exactly one first rejection entry', {
        actual: run.RejectLog.length,
      });
    }

    const first = run.RejectLog[0];
    const replayCoord = replayRecord.Witness?.detail?.inner?.coord ?? replayRecord.coord ?? replayRecord.Coord;

    if (first.coord !== replayCoord) {
      return validationReject0(['RejectLog', 0, 'coord'], 'AcceptRun0 reject log must record the replay first failure coordinate', {
        expected: replayCoord,
        actual: first.coord,
      });
    }

    if (first.replayable !== true) {
      return validationReject0(['RejectLog', 0, 'replayable'], 'AcceptRun0 reject log entry must be replayable', {
        actual: first.replayable,
      });
    }

    if (!ACCEPT_RUN_REJECTION_CLASSES0.includes(first.rejectionClass)) {
      return validationReject0(['RejectLog', 0, 'rejectionClass'], 'AcceptRun0 reject log entry has an unknown rejection class', {
        actual: first.rejectionClass,
      });
    }

    return validationAccept0({
      kind: 'AcceptRejectVerdict0NF',
      verdict: 'reject',
      replayCoord,
    });
  }

  if (run.Verdict.verdict !== 'accept') {
    return validationReject0(['Verdict', 'verdict'], 'AcceptRun0 verdict must be accept when replay accepts', {
      actual: run.Verdict.verdict,
    });
  }

  if (run.RejectLog.length !== 0) {
    return validationReject0(['RejectLog'], 'AcceptRun0 accept verdict must have an empty RejectLog', {
      actual: run.RejectLog.length,
    });
  }

  if (run.Verdict.conditional !== true) {
    return validationReject0(['Verdict', 'conditional'], 'AcceptRun0 accept verdict must be conditional', {
      actual: run.Verdict.conditional,
    });
  }

  if (run.Verdict.noClaimBeforeAccept !== true) {
    return validationReject0(['Verdict', 'noClaimBeforeAccept'], 'AcceptRun0 accept verdict must certify no claim before acceptance', {
      actual: run.Verdict.noClaimBeforeAccept,
    });
  }

  if (run.Verdict.publicConclusionEmitted !== true) {
    return validationReject0(['Verdict', 'publicConclusionEmitted'], 'AcceptRun0 accept verdict must emit a public conclusion', {
      actual: run.Verdict.publicConclusionEmitted,
    });
  }

  if (!isPlainObject(run.Verdict.publicConclusion)) {
    return validationReject0(['Verdict', 'publicConclusion'], 'AcceptRun0 accept verdict must include a public conclusion object', {
      actual: typeof run.Verdict.publicConclusion,
    });
  }

  if (run.Verdict.publicConclusion.antecedent !== 'CheckPCCPackexp(GeneratePCCPack())=accept') {
    return validationReject0(['Verdict', 'publicConclusion', 'antecedent'], 'AcceptRun0 public conclusion antecedent mismatch', {
      actual: run.Verdict.publicConclusion.antecedent,
    });
  }

  if (run.Verdict.publicConclusion.consequent !== 'P = NP') {
    return validationReject0(['Verdict', 'publicConclusion', 'consequent'], 'AcceptRun0 public conclusion consequent mismatch', {
      actual: run.Verdict.publicConclusion.consequent,
    });
  }

  return validationAccept0({
    kind: 'AcceptVerdict0NF',
    verdict: 'accept',
  });
}

function validateNoHiddenExecutableMin0(value, path) {
  const hit = findForbiddenExecutableUse0(value, path, false);

  if (hit !== null) {
    return validationReject0(hit.path, 'forbidden minimization symbol appears in executable position', hit);
  }

  return validationAccept0({
    kind: 'AcceptRunNoHiddenExecutableMin0NF',
  });
}

function validateNoOpaqueProof0(value, path) {
  const hit = findOpaqueProof0(value, path);

  if (hit !== null) {
    return validationReject0(hit.path, 'opaque proof material is not allowed in AcceptRun0', hit);
  }

  return validationAccept0({
    kind: 'AcceptRunNoOpaqueProof0NF',
  });
}

function findForbiddenExecutableUse0(value, path = [], inExecutablePosition = false) {
  if (typeof value === 'string') {
    if (inExecutablePosition && ACCEPT_RUN_FORBIDDEN_EXEC_SYMBOLS0.includes(value)) {
      return {
        symbol: value,
        path,
      };
    }

    return null;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = findForbiddenExecutableUse0(value[index], [...path, index], inExecutablePosition);

      if (hit !== null) {
        return hit;
      }
    }

    return null;
  }

  if (!isPlainObject(value)) {
    return null;
  }

  for (const key of Object.keys(value)) {
    const nextExecutablePosition =
      inExecutablePosition ||
      EXECUTABLE_KEYS0.has(key) ||
      /exec|call|program|body|operator|operation/i.test(key);

    const hit = findForbiddenExecutableUse0(value[key], [...path, key], nextExecutablePosition);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

function findOpaqueProof0(value, path = []) {
  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = findOpaqueProof0(value[index], [...path, index]);

      if (hit !== null) {
        return hit;
      }
    }

    return null;
  }

  if (!isPlainObject(value)) {
    return null;
  }

  for (const key of Object.keys(value)) {
    if (isOpaqueProofMaterialKey0(key)) {
      return {
        key,
        path: [...path, key],
        value: value[key],
      };
    }

    const hit = findOpaqueProof0(value[key], [...path, key]);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

function isOpaqueProofMaterialKey0(key) {
  const normalized = String(key).replace(/[_\-\s]/g, '').toLowerCase();

  return (
    normalized === 'opaqueproof' ||
    normalized === 'opaqueproofblob' ||
    normalized === 'proofblob' ||
    normalized === 'trustedblob' ||
    normalized === 'trustedproofblob' ||
    normalized === 'assumeproof'
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

function getPiRun0(run) {
  return run.PiRun ?? run['Πrun'] ?? run.piRun;
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

function isNonEmptyString(value) {
  return typeof value === 'string' && value.length > 0;
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}