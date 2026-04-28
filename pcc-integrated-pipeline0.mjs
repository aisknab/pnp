import {
  CheckVerifierFrag0,
  digestCanonical0,
  makeAuditCase,
  makeRejectCase,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckBoot0,
} from './pcc-boot0.mjs';

import {
  CheckKBundle0,
} from './pcc-kimpl0.mjs';

import {
  CheckHard0,
} from './pcc-hard0.mjs';

import {
  CheckRows0,
} from './pcc-rows0.mjs';

import {
  CheckGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckLocalPackages0,
} from './pcc-local-packages0.mjs';

import {
  CheckGlobalFirewalls0,
} from './pcc-global-firewalls0.mjs';

import {
  CheckGPack0,
  CheckRowFamG0,
} from './pcc-gpack0.mjs';

import {
  CheckFinalIntegration0,
} from './pcc-final-framework0.mjs';

import {
  CheckFinal0,
  CheckRowFamFinal0,
} from './pcc-final0.mjs';

import {
  CheckPackSufficiency0,
  makeSyntheticPCCPack0,
} from './pcc-pack-sufficiency0.mjs';

import {
  CheckAcceptRun0,
  EmitFinalVerdict0,
  ReplayAcceptRun0,
  makeSyntheticAcceptRun0,
} from './pcc-accept-run0.mjs';

const CHECKER_VERSION = 0;

export const INTEGRATED_PIPELINE_PHASES0 = Object.freeze([
  'CheckVerifierFrag0',
  'CheckBoot0',
  'CheckKBundle0',
  'CheckHard0',
  'CheckRows0',
  'CheckGlobalProofDAG0',
  'CheckLocalPackages0',
  'CheckGlobalFirewalls0',
  'CheckGPack0',
  'CheckRowFamG0',
  'CheckFinalIntegration0',
  'CheckFinal0',
  'CheckRowFamFinal0',
  'CheckPackSufficiency0',
  'BindAcceptRunPgen0',
  'ReplayAcceptRun0',
  'CheckAcceptRun0',
  'EmitFinalVerdict0',
]);

export function makeSyntheticVerifierFragSuite0() {
  return {
    kind: 'VerifierFrag0',
    version: CHECKER_VERSION,
    suiteId: 'integrated.pipeline.verifier-frag0',
    cases: [
      makeAuditCase({
        id: 'integrated.verifier.positive',
        target: 'IntegratedPipeline0',
        run: () => undefined,
      }),
      makeRejectCase({
        id: 'integrated.verifier.negative',
        target: 'IntegratedPipeline0',
        run: () => ({
          tag: 'reject',
          coord: 'synthetic.integrated.negative',
        }),
      }),
    ],
  };
}

export function makeSyntheticIntegratedPipeline0(overrides = {}) {
  const pack = makeSyntheticPCCPack0();
  const acceptRun = makeSyntheticAcceptRun0({
    pack,
  });

  const pipeline = {
    kind: 'IntegratedPipeline0',
    version: CHECKER_VERSION,
    VerifierFrag0: makeSyntheticVerifierFragSuite0(),
    PCCPack: pack,
    AcceptRun: acceptRun,
    PhaseOrder: INTEGRATED_PIPELINE_PHASES0,
    PiIntegrated: {
      kind: 'PiIntegratedPipeline0',
      version: CHECKER_VERSION,
      note: 'synthetic deterministic full-stack integration transcript marker',
    },
  };

  return {
    ...pipeline,
    ...overrides,
  };
}

export async function RunIntegratedPCC0(pipeline = makeSyntheticIntegratedPipeline0()) {
  return CheckIntegratedPipeline0(pipeline);
}

export async function CheckIntegratedPipeline0(pipeline = makeSyntheticIntegratedPipeline0()) {
  const checker = 'CheckIntegratedPipeline0';
  const ledger = [];

  const shape = validatePipelineShape0(pipeline);

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

  const pack = pipeline.PCCPack;
  const acceptRun = pipeline.AcceptRun;

  const phases = [
    ['CheckVerifierFrag0', ['VerifierFrag0'], () => CheckVerifierFrag0(pipeline.VerifierFrag0)],
    ['CheckBoot0', ['PCCPack', 'Boot0'], () => CheckBoot0(pack.Boot0)],
    ['CheckKBundle0', ['PCCPack', 'KBundle'], () => CheckKBundle0(pack.KBundle)],
    ['CheckHard0', ['PCCPack', 'HardCheck'], () => CheckHard0(pack.HardCheck)],
    ['CheckRows0', ['PCCPack', 'RowPack'], () => CheckRows0(pack.RowPack)],
    ['CheckGlobalProofDAG0', ['PCCPack', 'GlobalProofDAG'], () => CheckGlobalProofDAG0(pack.GlobalProofDAG)],
    ['CheckLocalPackages0', ['PCCPack', 'LocalPackages'], () => CheckLocalPackages0(pack.LocalPackages)],
    ['CheckGlobalFirewalls0', ['PCCPack', 'GlobalFirewalls'], () => CheckGlobalFirewalls0(pack.GlobalFirewalls)],
    ['CheckGPack0', ['PCCPack', 'GPack'], () => CheckGPack0(pack.GPack)],
    ['CheckRowFamG0', ['PCCPack', 'RowFamG'], () => CheckRowFamG0(pack.RowFamG)],
    ['CheckFinalIntegration0', ['PCCPack', 'FinalIntegration'], () => CheckFinalIntegration0(pack.FinalIntegration)],
    ['CheckFinal0', ['PCCPack', 'FinalTheorem'], () => CheckFinal0(pack.FinalTheorem)],
    ['CheckRowFamFinal0', ['PCCPack', 'RowFamFinal'], () => CheckRowFamFinal0(pack.RowFamFinal)],
    ['CheckPackSufficiency0', ['PCCPack'], () => CheckPackSufficiency0(pack)],
    ['BindAcceptRunPgen0', ['AcceptRun', 'Pgen'], () => validateAcceptRunPackBinding0(pipeline)],
    ['ReplayAcceptRun0', ['AcceptRun'], () => ReplayAcceptRun0(acceptRun)],
    ['CheckAcceptRun0', ['AcceptRun'], () => CheckAcceptRun0(acceptRun)],
    ['EmitFinalVerdict0', ['AcceptRun'], () => EmitFinalVerdict0(acceptRun)],
  ];

  const phaseDigests = [];
  let finalVerdictRecord = null;

  for (const [phase, path, runPhase] of phases) {
    const record = await runPhase();

    if (phase === 'BindAcceptRunPgen0') {
      ledger.push({
        phase,
        status: record.ok ? 'pass' : 'fail',
        digest: digestCanonical0(record.nf ?? record.witness ?? null),
      });

      if (!record.ok) {
        return makeRejectRecord({
          checker,
          coord: `${checker}.${phase}`,
          path: record.path,
          witness: record.witness,
          ledger,
        });
      }

      phaseDigests.push({
        phase,
        digest: digestCanonical0(record.nf),
      });

      continue;
    }

    const validation = recordToValidation0(record, path);

    ledger.push({
      phase,
      status: validation.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!validation.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.${phase}`,
        path: validation.path,
        witness: validation.witness,
        ledger,
      });
    }

    phaseDigests.push({
      phase,
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (phase === 'EmitFinalVerdict0') {
      finalVerdictRecord = record;
    }
  }

  const nf = {
    kind: 'IntegratedPipeline0NF',
    checker,
    version: CHECKER_VERSION,
    phaseOrder: INTEGRATED_PIPELINE_PHASES0,
    phaseCount: INTEGRATED_PIPELINE_PHASES0.length,
    phaseDigests,
    finalVerdict: finalVerdictRecord.NF?.verdict ?? finalVerdictRecord.nf?.verdict ?? null,
    publicConclusion: finalVerdictRecord.NF?.publicConclusion ?? finalVerdictRecord.nf?.publicConclusion ?? null,
    publicConclusionEmitted: finalVerdictRecord.NF?.publicConclusionEmitted ?? finalVerdictRecord.nf?.publicConclusionEmitted ?? false,
    packDigest: digestCanonical0(pack),
    acceptRunDigest: digestCanonical0(acceptRun),
    piIntegratedDigest: digestCanonical0(getPiIntegrated0(pipeline)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validatePipelineShape0(pipeline) {
  if (!isPlainObject(pipeline)) {
    return validationReject0([], 'IntegratedPipeline0 must be an object', {
      actual: typeof pipeline,
    });
  }

  if (pipeline.kind !== undefined && pipeline.kind !== 'IntegratedPipeline0') {
    return validationReject0(['kind'], 'IntegratedPipeline0 kind must be IntegratedPipeline0 when present', {
      actual: pipeline.kind,
    });
  }

  if (pipeline.version !== undefined && pipeline.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `IntegratedPipeline0 version must be ${CHECKER_VERSION} when present`, {
      actual: pipeline.version,
    });
  }

  for (const field of [
    'VerifierFrag0',
    'PCCPack',
    'AcceptRun',
    'PhaseOrder',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(pipeline, field)) {
      return validationReject0([field], 'IntegratedPipeline0 is missing a required field', {
        field,
      });
    }
  }

  if (!Array.isArray(pipeline.PhaseOrder)) {
    return validationReject0(['PhaseOrder'], 'IntegratedPipeline0 PhaseOrder must be an array', {
      actual: typeof pipeline.PhaseOrder,
    });
  }

  for (let index = 0; index < INTEGRATED_PIPELINE_PHASES0.length; index += 1) {
    if (pipeline.PhaseOrder[index] !== INTEGRATED_PIPELINE_PHASES0[index]) {
      return validationReject0(['PhaseOrder', index], 'IntegratedPipeline0 PhaseOrder mismatch', {
        expected: INTEGRATED_PIPELINE_PHASES0[index],
        actual: pipeline.PhaseOrder[index],
      });
    }
  }

  if (pipeline.PhaseOrder.length !== INTEGRATED_PIPELINE_PHASES0.length) {
    return validationReject0(['PhaseOrder'], 'IntegratedPipeline0 PhaseOrder has the wrong length', {
      expected: INTEGRATED_PIPELINE_PHASES0.length,
      actual: pipeline.PhaseOrder.length,
    });
  }

  if (getPiIntegrated0(pipeline) === undefined) {
    return validationReject0(['PiIntegrated'], 'IntegratedPipeline0 is missing PiIntegrated or Πintegrated', null);
  }

  return validationAccept0({
    kind: 'IntegratedPipelineShape0NF',
  });
}

function validateAcceptRunPackBinding0(pipeline) {
  const packBytes = stableStringify0(pipeline.PCCPack);
  const acceptRunPackBytes = stableStringify0(pipeline.AcceptRun.Pgen);

  if (packBytes !== acceptRunPackBytes) {
    return validationReject0(['AcceptRun', 'Pgen'], 'AcceptRun Pgen must match the integrated PCCPack by canonical byte equality', {
      expectedDigest: digestCanonical0(packBytes),
      actualDigest: digestCanonical0(acceptRunPackBytes),
    });
  }

  return validationAccept0({
    kind: 'AcceptRunPackBinding0NF',
    packByteDigest: digestCanonical0(packBytes),
  });
}

function recordToValidation0(record, path) {
  if (isRejectRecord0(record)) {
    return validationReject0(path, `${record.checker} rejected`, {
      inner: compactReject0(record),
    });
  }

  return validationAccept0(record.NF ?? record.nf ?? record);
}

function getPiIntegrated0(pipeline) {
  return pipeline.PiIntegrated ?? pipeline['Πintegrated'] ?? pipeline.piIntegrated;
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