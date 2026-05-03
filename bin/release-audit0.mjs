#!/usr/bin/env node

import {
  CheckReleaseAudit0,
  summarizeReleaseAudit0,
} from '../pcc-release-audit0.mjs';

const args = process.argv.slice(2);

const full = hasFlag0('--full');
const fastLocal = hasFlag0('--fast-local');

const materializedGate = hasFlag0('--materialized-gate');
const noMaterializedGate = hasFlag0('--no-materialized-gate');
const materializedGateCli = hasFlag0('--materialized-gate-cli');
const noMaterializedGateCli = hasFlag0('--no-materialized-gate-cli');
const materializedGateCanonical = hasFlag0('--materialized-gate-canonical');
const materializedGateOut = readFlagValue0('--materialized-gate-out');

const finalCertificateGate = hasFlag0('--final-certificate-gate');
const noFinalCertificateGate = hasFlag0('--no-final-certificate-gate');
const finalCertificateGateCanonical = hasFlag0('--final-certificate-gate-canonical');
const finalCertificateGateOut = readFlagValue0('--final-certificate-gate-out');

const concreteFinalCertificateGate = hasFlag0('--concrete-final-certificate-gate');
const noConcreteFinalCertificateGate = hasFlag0('--no-concrete-final-certificate-gate');
const concreteFinalCertificateGateCanonical = hasFlag0('--concrete-final-certificate-gate-canonical');
const concreteFinalCertificateGateOut = readFlagValue0('--concrete-final-certificate-gate-out');

const argCheck = validateArgs0();

if (!argCheck.ok) {
  console.log(JSON.stringify({
    tag: 'reject',
    checker: 'release-audit0',
    coord: 'release-audit0.args',
    path: argCheck.path,
    witness: argCheck.witness,
  }, null, 2));

  process.exitCode = 1;
} else {
  const runMaterializedPublicStatusGate = fastLocal
    ? false
    : (noMaterializedGate ? false : true);

  const runFinalCertificatePublicStatusGate = fastLocal
    ? false
    : (noFinalCertificateGate ? false : true);

  const runConcreteFinalCertificatePublicStatusGate = fastLocal
    ? false
    : (
        noConcreteFinalCertificateGate
          ? false
          : (concreteFinalCertificateGate ? true : !noFinalCertificateGate)
      );

  const out = await CheckReleaseAudit0({
    runCliSmoke: false,

    runMaterializedPublicStatusGate,
    materializedPublicStatusGateRunCliChecks: noMaterializedGateCli ? false : true,
    materializedPublicStatusGateCanonicalEnvelopeBytes: materializedGateCanonical,
    ...(materializedGateOut === null ? {} : {
      materializedPublicStatusGateOutputDir: materializedGateOut,
    }),

    runFinalCertificatePublicStatusGate,
    finalCertificatePublicStatusGateCanonicalEnvelopeBytes: finalCertificateGateCanonical,
    ...(finalCertificateGateOut === null ? {} : {
      finalCertificatePublicStatusGateOutputDir: finalCertificateGateOut,
    }),

    runConcreteFinalCertificatePublicStatusGate,
    concreteFinalCertificatePublicStatusGateCanonicalEnvelopeBytes: concreteFinalCertificateGateCanonical,
    ...(concreteFinalCertificateGateOut === null ? {} : {
      concreteFinalCertificatePublicStatusGateOutputDir: concreteFinalCertificateGateOut,
    }),
  });

  console.log(JSON.stringify(full ? out : summarizeReleaseAudit0(out), null, 2));

  if (out.tag !== 'accept') {
    process.exitCode = 1;
  }
}

function validateArgs0() {
  if (fastLocal && materializedGate) {
    return rejectArg0(['argv'], 'release audit CLI cannot use both --fast-local and --materialized-gate');
  }

  if (fastLocal && materializedGateOut !== null) {
    return rejectArg0(['argv', '--materialized-gate-out'], 'release audit CLI cannot use --materialized-gate-out with --fast-local');
  }

  if (fastLocal && materializedGateCanonical) {
    return rejectArg0(['argv'], 'release audit CLI cannot use --materialized-gate-canonical with --fast-local');
  }

  if (materializedGate && noMaterializedGate) {
    return rejectArg0(['argv'], 'release audit CLI cannot use both --materialized-gate and --no-materialized-gate');
  }

  if (materializedGateCli && noMaterializedGateCli) {
    return rejectArg0(['argv'], 'release audit CLI cannot use both --materialized-gate-cli and --no-materialized-gate-cli');
  }

  if (fastLocal && finalCertificateGate) {
    return rejectArg0(['argv'], 'release audit CLI cannot use both --fast-local and --final-certificate-gate');
  }

  if (fastLocal && finalCertificateGateOut !== null) {
    return rejectArg0(['argv', '--final-certificate-gate-out'], 'release audit CLI cannot use --final-certificate-gate-out with --fast-local');
  }

  if (fastLocal && finalCertificateGateCanonical) {
    return rejectArg0(['argv'], 'release audit CLI cannot use --final-certificate-gate-canonical with --fast-local');
  }

  if (finalCertificateGate && noFinalCertificateGate) {
    return rejectArg0(['argv'], 'release audit CLI cannot use both --final-certificate-gate and --no-final-certificate-gate');
  }

  if (fastLocal && concreteFinalCertificateGate) {
    return rejectArg0(['argv'], 'release audit CLI cannot use both --fast-local and --concrete-final-certificate-gate');
  }

  if (fastLocal && concreteFinalCertificateGateOut !== null) {
    return rejectArg0(['argv', '--concrete-final-certificate-gate-out'], 'release audit CLI cannot use --concrete-final-certificate-gate-out with --fast-local');
  }

  if (fastLocal && concreteFinalCertificateGateCanonical) {
    return rejectArg0(['argv'], 'release audit CLI cannot use --concrete-final-certificate-gate-canonical with --fast-local');
  }

  if (concreteFinalCertificateGate && noConcreteFinalCertificateGate) {
    return rejectArg0(['argv'], 'release audit CLI cannot use both --concrete-final-certificate-gate and --no-concrete-final-certificate-gate');
  }

  const materializedOutIndex = args.indexOf('--materialized-gate-out');

  if (materializedOutIndex >= 0) {
    const value = args[materializedOutIndex + 1];

    if (value === undefined || value.startsWith('--')) {
      return rejectArg0(['argv', '--materialized-gate-out'], '--materialized-gate-out requires a directory argument');
    }
  }

  const finalCertificateOutIndex = args.indexOf('--final-certificate-gate-out');

  if (finalCertificateOutIndex >= 0) {
    const value = args[finalCertificateOutIndex + 1];

    if (value === undefined || value.startsWith('--')) {
      return rejectArg0(['argv', '--final-certificate-gate-out'], '--final-certificate-gate-out requires a directory argument');
    }
  }

  const concreteFinalCertificateOutIndex = args.indexOf('--concrete-final-certificate-gate-out');

  if (concreteFinalCertificateOutIndex >= 0) {
    const value = args[concreteFinalCertificateOutIndex + 1];

    if (value === undefined || value.startsWith('--')) {
      return rejectArg0(['argv', '--concrete-final-certificate-gate-out'], '--concrete-final-certificate-gate-out requires a directory argument');
    }
  }

  return {
    ok: true,
  };
}

function rejectArg0(path, reason) {
  return {
    ok: false,
    path,
    witness: {
      reason,
    },
  };
}

function hasFlag0(flag) {
  return args.includes(flag);
}

function readFlagValue0(flag) {
  const index = args.indexOf(flag);

  if (index < 0) {
    return null;
  }

  const value = args[index + 1];

  if (value === undefined || value.startsWith('--')) {
    return null;
  }

  return value;
}
