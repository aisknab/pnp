#!/usr/bin/env node

import {
  CheckReleaseAudit0,
} from '../pcc-release-audit0.mjs';

const args = process.argv.slice(2);

const full = hasFlag0('--full');
const materializedGate = hasFlag0('--materialized-gate');
const noMaterializedGate = hasFlag0('--no-materialized-gate');
const materializedGateCli = hasFlag0('--materialized-gate-cli');
const noMaterializedGateCli = hasFlag0('--no-materialized-gate-cli');
const materializedGateCanonical = hasFlag0('--materialized-gate-canonical');

const materializedGateOut = readFlagValue0('--materialized-gate-out');

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
  const out = await CheckReleaseAudit0({
    runCliSmoke: false,
    runMaterializedPublicStatusGate: noMaterializedGate ? false : true,
    materializedPublicStatusGateRunCliChecks: noMaterializedGateCli ? false : true,
    materializedPublicStatusGateCanonicalEnvelopeBytes: materializedGateCanonical,
    ...(materializedGateOut === null ? {} : {
      materializedPublicStatusGateOutputDir: materializedGateOut,
    }),
  });

  console.log(JSON.stringify(full ? out : summarizeReleaseAudit0(out), null, 2));

  if (out.tag !== 'accept') {
    process.exitCode = 1;
  }
}

function validateArgs0() {
  if (materializedGate && noMaterializedGate) {
    return {
      ok: false,
      path: ['argv'],
      witness: {
        reason: 'release audit CLI cannot use both --materialized-gate and --no-materialized-gate',
      },
    };
  }

  if (materializedGateCli && noMaterializedGateCli) {
    return {
      ok: false,
      path: ['argv'],
      witness: {
        reason: 'release audit CLI cannot use both --materialized-gate-cli and --no-materialized-gate-cli',
      },
    };
  }

  const outIndex = args.indexOf('--materialized-gate-out');

  if (outIndex >= 0) {
    const value = args[outIndex + 1];

    if (value === undefined || value.startsWith('--')) {
      return {
        ok: false,
        path: ['argv', '--materialized-gate-out'],
        witness: {
          reason: '--materialized-gate-out requires a directory argument',
        },
      };
    }
  }

  return {
    ok: true,
  };
}

function summarizeReleaseAudit0(out) {
  if (out.tag === 'accept') {
    return {
      tag: out.tag,
      checker: out.checker,
      moduleCount: out.NF.moduleCount,
      testCount: out.NF.testCount,
      checkerCoverageCount: out.NF.checkerCoverageCount,

      materializedPublicStatusGate: out.NF.materializedPublicStatusGate,
      materializedPublicStatusGateSummary: out.NF.materializedPublicStatusGateSummary,
      materializedPublicStatusGateDigest: out.NF.materializedPublicStatusGateDigest,
      materializedPublicStatusGateFileCount: out.NF.materializedPublicStatusGateFileCount,
      materializedPublicStatusGateDirectRecordCount: out.NF.materializedPublicStatusGateDirectRecordCount,
      materializedPublicStatusGateCliRecordCount: out.NF.materializedPublicStatusGateCliRecordCount,
      materializedPublicStatusGateAcceptedPublicConclusionOnly: out.NF.materializedPublicStatusGateAcceptedPublicConclusionOnly,

      publicConclusion: out.NF.publicConclusion,
      digest: out.Digest,
    };
  }

  return {
    tag: out.tag,
    checker: out.checker,
    coord: out.Coord,
    path: out.Path,
    witness: out.Witness,
    digest: out.Digest,
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