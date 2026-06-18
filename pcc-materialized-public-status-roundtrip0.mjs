import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedAggregateFile0,
} from './pcc-materialized-aggregate0.mjs';

import {
  CheckMaterializedPublicStatusFile0,
} from './pcc-materialized-public-status0.mjs';

import {
  MATERIALIZED_FIXTURE_FILENAMES0,
} from './pcc-materialized-fixture-writer0.mjs';

import {
  MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0,
} from './pcc-materialized-accept-run-fixtures0.mjs';

import {
  WriteMaterializedFinalRunFixtureSet0,
} from './pcc-materialized-final-run-fixtures0.mjs';

const CHECKER_VERSION = 0;
const REPO_ROOT = path.dirname(fileURLToPath(import.meta.url));

export const MATERIALIZED_PUBLIC_STATUS_ROUNDTRIP_CHECKS0 = Object.freeze([
  'WriteMaterializedFinalRunFixtureSet0.first',
  'WriteMaterializedFinalRunFixtureSet0.second',
  'CompareMaterializedPublicStatusFixtureBytes0',
  'CheckMaterializedAggregateFile0',
  'CheckMaterializedPublicStatusFile0.pending',
  'CheckMaterializedPublicStatusFile0.rejected',
  'CheckMaterializedPublicStatusFile0.accepted',
  'CLI.check-materialized-aggregate0',
  'CLI.check-materialized-public-status0.pending',
  'CLI.check-materialized-public-status0.rejected',
  'CLI.check-materialized-public-status0.accepted',
]);

export const MATERIALIZED_PUBLIC_STATUS_ROUNDTRIP_FILES0 = Object.freeze([
  Object.freeze({
    kind: 'MaterializedPCCPack0',
    status: null,
    verdict: null,
    filename: MATERIALIZED_FIXTURE_FILENAMES0.pack,
  }),
  Object.freeze({
    kind: 'MaterializedPublicStatus.pending',
    status: 'pending',
    verdict: 'pending',
    filename: MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.pending,
  }),
  Object.freeze({
    kind: 'MaterializedPublicStatus.rejected',
    status: 'rejected',
    verdict: 'reject',
    filename: MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.reject,
  }),
  Object.freeze({
    kind: 'MaterializedPublicStatus.accepted',
    status: 'accepted',
    verdict: 'accept',
    filename: MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.accepted,
  }),
]);

export function makeMaterializedPublicStatusRoundtripConfig0(overrides = {}) {
  return {
    kind: 'MaterializedPublicStatusRoundtripConfig0',
    version: CHECKER_VERSION,
    outputDir: path.join(process.cwd(), 'materialized-public-status-roundtrip0'),
    canonicalEnvelopeBytes: false,
    overwrite: true,
    verifyFinalRunWriter: true,
    runCliChecks: true,
    mutateSecondWrite: null,
    ...overrides,
  };
}

export async function CheckMaterializedPublicStatusRoundtrip0(config = makeMaterializedPublicStatusRoundtripConfig0()) {
  const checker = 'CheckMaterializedPublicStatusRoundtrip0';
  const ledger = [];
  const cfg = makeMaterializedPublicStatusRoundtripConfig0(config);

  const shape = validateRoundtripConfig0(cfg);

  ledger.push({
    phase: 'config',
    status: shape.ok ? 'pass' : 'fail',
    digest: digestCanonical0(shape.nf ?? shape.witness ?? null),
  });

  if (!shape.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.config`,
      path: shape.path,
      witness: shape.witness,
      ledger,
    });
  }

  const firstWrite = await WriteMaterializedFinalRunFixtureSet0({
    outputDir: cfg.outputDir,
    canonicalEnvelopeBytes: cfg.canonicalEnvelopeBytes,
    overwrite: cfg.overwrite,
    verifyAcceptRunWriter: cfg.verifyFinalRunWriter,
    verifyDirect: cfg.verifyFinalRunWriter,
    verifyCli: cfg.verifyFinalRunWriter,
  });
  const firstWriteResult = recordToValidation0(firstWrite, ['outputDir']);

  ledger.push({
    phase: 'WriteMaterializedFinalRunFixtureSet0.first',
    status: firstWriteResult.ok ? 'pass' : 'fail',
    digest: firstWrite.Digest ?? firstWrite.digest ?? digestCanonical0(firstWrite),
  });

  if (!firstWriteResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.writeFirst`,
      path: firstWriteResult.path,
      witness: firstWriteResult.witness,
      ledger,
    });
  }

  const firstSnapshot = await readPublicStatusSnapshot0(cfg.outputDir);

  ledger.push({
    phase: 'ReadFirstSnapshot0',
    status: firstSnapshot.ok ? 'pass' : 'fail',
    digest: digestCanonical0(firstSnapshot.nf ?? firstSnapshot.witness ?? null),
  });

  if (!firstSnapshot.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.readFirstSnapshot`,
      path: firstSnapshot.path,
      witness: firstSnapshot.witness,
      ledger,
    });
  }

  const secondWrite = await WriteMaterializedFinalRunFixtureSet0({
    outputDir: cfg.outputDir,
    canonicalEnvelopeBytes: cfg.canonicalEnvelopeBytes,
    overwrite: true,
    verifyAcceptRunWriter: cfg.verifyFinalRunWriter,
    verifyDirect: cfg.verifyFinalRunWriter,
    verifyCli: cfg.verifyFinalRunWriter,
  });
  const secondWriteResult = recordToValidation0(secondWrite, ['outputDir']);

  ledger.push({
    phase: 'WriteMaterializedFinalRunFixtureSet0.second',
    status: secondWriteResult.ok ? 'pass' : 'fail',
    digest: secondWrite.Digest ?? secondWrite.digest ?? digestCanonical0(secondWrite),
  });

  if (!secondWriteResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.writeSecond`,
      path: secondWriteResult.path,
      witness: secondWriteResult.witness,
      ledger,
    });
  }

  if (typeof cfg.mutateSecondWrite === 'function') {
    await cfg.mutateSecondWrite({
      outputDir: cfg.outputDir,
      files: MATERIALIZED_PUBLIC_STATUS_ROUNDTRIP_FILES0,
    });
  }

  const secondSnapshot = await readPublicStatusSnapshot0(cfg.outputDir);

  ledger.push({
    phase: 'ReadSecondSnapshot0',
    status: secondSnapshot.ok ? 'pass' : 'fail',
    digest: digestCanonical0(secondSnapshot.nf ?? secondSnapshot.witness ?? null),
  });

  if (!secondSnapshot.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.readSecondSnapshot`,
      path: secondSnapshot.path,
      witness: secondSnapshot.witness,
      ledger,
    });
  }

  const compare = comparePublicStatusSnapshots0(firstSnapshot.snapshot, secondSnapshot.snapshot);

  ledger.push({
    phase: 'CompareMaterializedPublicStatusFixtureBytes0',
    status: compare.ok ? 'pass' : 'fail',
    digest: digestCanonical0(compare.nf ?? compare.witness ?? null),
  });

  if (!compare.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.compareBytes`,
      path: compare.path,
      witness: compare.witness,
      ledger,
    });
  }

  const direct = await verifyDirectPublicStatusRoundtrip0(cfg);

  ledger.push({
    phase: 'VerifyDirectMaterializedPublicStatusRoundtrip0',
    status: direct.ok ? 'pass' : 'fail',
    digest: digestCanonical0(direct.nf ?? direct.witness ?? null),
  });

  if (!direct.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.direct`,
      path: direct.path,
      witness: direct.witness,
      ledger,
    });
  }

  let cli = validationAccept0({
    kind: 'MaterializedPublicStatusCliRoundtripSkipped0NF',
    cliChecked: false,
    records: [],
  });

  if (cfg.runCliChecks === true) {
    cli = await verifyCliPublicStatusRoundtrip0(cfg);
  }

  ledger.push({
    phase: 'VerifyCliMaterializedPublicStatusRoundtrip0',
    status: cli.ok ? 'pass' : 'fail',
    digest: digestCanonical0(cli.nf ?? cli.witness ?? null),
  });

  if (!cli.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.cli`,
      path: cli.path,
      witness: cli.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedPublicStatusRoundtrip0NF',
    checker,
    version: CHECKER_VERSION,
    outputDir: cfg.outputDir,
    canonicalEnvelopeBytes: cfg.canonicalEnvelopeBytes,
    deterministic: true,
    fileCount: compare.nf.fileCount,
    byteComparisons: compare.nf.comparisons,
    directRecords: direct.nf.records,
    cliRecords: cli.nf.records,
    acceptedPublicConclusionOnly: true,
    syntheticRunAll: false,
    materializedPath: true,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

async function readPublicStatusSnapshot0(outputDir) {
  const entries = [];

  for (const file of MATERIALIZED_PUBLIC_STATUS_ROUNDTRIP_FILES0) {
    const filePath = path.join(outputDir, file.filename);

    let text;

    try {
      text = await fs.readFile(filePath, 'utf8');
    } catch (error) {
      return validationReject0(['files', file.filename], 'materialized public status fixture file must be readable', {
        filePath,
        error: error.message,
      });
    }

    entries.push({
      ...file,
      filePath,
      text,
      byteLength: Buffer.byteLength(text, 'utf8'),
      digest: digestCanonical0(text),
    });
  }

  return {
    ok: true,
    snapshot: entries,
    nf: {
      kind: 'MaterializedPublicStatusSnapshot0NF',
      fileCount: entries.length,
      files: entries.map((entry) => ({
        kind: entry.kind,
        status: entry.status,
        verdict: entry.verdict,
        filename: entry.filename,
        filePath: entry.filePath,
        byteLength: entry.byteLength,
        digest: entry.digest,
      })),
    },
  };
}

function comparePublicStatusSnapshots0(first, second) {
  const comparisons = [];

  for (const firstEntry of first) {
    const secondEntry = second.find((entry) => entry.filename === firstEntry.filename);

    if (secondEntry === undefined) {
      return validationReject0(['files', firstEntry.filename], 'second materialized public status snapshot is missing a file', {
        filename: firstEntry.filename,
      });
    }

    if (firstEntry.text !== secondEntry.text) {
      return validationReject0(['files', firstEntry.filename], 'materialized public status fixture bytes are not deterministic across repeated writes', {
        filename: firstEntry.filename,
        first: {
          byteLength: firstEntry.byteLength,
          digest: firstEntry.digest,
        },
        second: {
          byteLength: secondEntry.byteLength,
          digest: secondEntry.digest,
        },
      });
    }

    comparisons.push({
      kind: firstEntry.kind,
      status: firstEntry.status,
      verdict: firstEntry.verdict,
      filename: firstEntry.filename,
      filePath: firstEntry.filePath,
      byteLength: firstEntry.byteLength,
      digest: firstEntry.digest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedPublicStatusByteComparisons0NF',
    fileCount: comparisons.length,
    comparisons,
  });
}

async function verifyDirectPublicStatusRoundtrip0(config) {
  const packFile = path.join(config.outputDir, MATERIALIZED_FIXTURE_FILENAMES0.pack);

  const aggregate = await CheckMaterializedAggregateFile0(packFile, {
    loaderConfig: {
      requireCanonicalEnvelopeBytes: config.canonicalEnvelopeBytes,
    },
  });

  if (isRejectRecord0(aggregate)) {
    return validationReject0(['files', MATERIALIZED_FIXTURE_FILENAMES0.pack], 'materialized public status roundtrip aggregate file rejected', {
      inner: compactReject0(aggregate),
    });
  }

  const records = [
    {
      checker: 'CheckMaterializedAggregateFile0',
      filename: MATERIALIZED_FIXTURE_FILENAMES0.pack,
      digest: aggregate.Digest ?? aggregate.digest,
    },
  ];

  for (const file of MATERIALIZED_PUBLIC_STATUS_ROUNDTRIP_FILES0) {
    if (file.status === null) {
      continue;
    }

    const filePath = path.join(config.outputDir, file.filename);
    const record = await CheckMaterializedPublicStatusFile0(filePath);

    if (isRejectRecord0(record)) {
      return validationReject0(['files', file.filename], 'materialized public status roundtrip status file rejected', {
        file,
        inner: compactReject0(record),
      });
    }

    const status = validatePublicStatusNF0(record.NF ?? record.nf, file, ['files', file.filename]);

    if (!status.ok) {
      return status;
    }

    records.push({
      checker: 'CheckMaterializedPublicStatusFile0',
      filename: file.filename,
      status: file.status,
      verdict: file.verdict,
      digest: record.Digest ?? record.digest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedPublicStatusDirectRoundtrip0NF',
    records,
  });
}

async function verifyCliPublicStatusRoundtrip0(config) {
  const packFile = path.join(config.outputDir, MATERIALIZED_FIXTURE_FILENAMES0.pack);
  const aggregateArgs = [
    path.join(REPO_ROOT, 'bin', 'check-materialized-aggregate0.mjs'),
    packFile,
  ];

  if (config.canonicalEnvelopeBytes === true) {
    aggregateArgs.push('--canonical-envelope-bytes');
  }

  const checks = [
    {
      label: 'CLI.check-materialized-aggregate0',
      filename: MATERIALIZED_FIXTURE_FILENAMES0.pack,
      args: aggregateArgs,
      expectedChecker: 'CheckMaterializedAggregateFile0',
      status: null,
      verdict: null,
    },
    ...MATERIALIZED_PUBLIC_STATUS_ROUNDTRIP_FILES0
      .filter((file) => file.status !== null)
      .map((file) => ({
        label: `CLI.check-materialized-public-status0.${file.status}`,
        filename: file.filename,
        args: [
          path.join(REPO_ROOT, 'bin', 'check-materialized-public-status0.mjs'),
          path.join(config.outputDir, file.filename),
        ],
        expectedChecker: 'CheckMaterializedPublicStatus0',
        status: file.status,
        verdict: file.verdict,
      })),
  ];

  const records = [];

  for (const check of checks) {
    const child = spawnSync(process.execPath, check.args, {
      encoding: 'utf8',
      windowsHide: true,
    });

    if (child.status !== 0) {
      return validationReject0(['cli', check.label], 'materialized public status roundtrip CLI command failed', {
        label: check.label,
        args: check.args,
        status: child.status,
        stdout: child.stdout,
        stderr: child.stderr,
        error: child.error?.message ?? null,
      });
    }

    let parsed;

    try {
      parsed = JSON.parse(child.stdout);
    } catch (error) {
      return validationReject0(['cli', check.label], 'materialized public status roundtrip CLI did not emit JSON', {
        label: check.label,
        stdout: child.stdout,
        error: error.message,
      });
    }

    if (parsed.tag !== 'accept') {
      return validationReject0(['cli', check.label], 'materialized public status roundtrip CLI emitted non-accept', {
        label: check.label,
        parsed,
      });
    }

    if (parsed.checker !== check.expectedChecker) {
      return validationReject0(['cli', check.label, 'checker'], 'materialized public status roundtrip CLI emitted unexpected checker', {
        expected: check.expectedChecker,
        actual: parsed.checker,
      });
    }

    if (check.status !== null) {
      const status = validatePublicStatusNF0(parsed, {
        filename: check.filename,
        status: check.status,
        verdict: check.verdict,
      }, ['cli', check.label]);

      if (!status.ok) {
        return status;
      }
    }

    records.push({
      checker: check.label,
      filename: check.filename,
      status: check.status,
      verdict: check.verdict,
      digest: parsed.digest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedPublicStatusCliRoundtrip0NF',
    cliChecked: true,
    records,
  });
}

function validatePublicStatusNF0(nf, file, path) {
  if (!isPlainObject(nf)) {
    return validationReject0(path, 'materialized public status summary must be an object', {
      file,
      actual: typeof nf,
    });
  }

  if (nf.status !== file.status) {
    return validationReject0([...path, 'status'], 'materialized public status returned wrong status', {
      expected: file.status,
      actual: nf.status,
    });
  }

  if (nf.verdict !== file.verdict) {
    return validationReject0([...path, 'verdict'], 'materialized public status returned wrong verdict', {
      expected: file.verdict,
      actual: nf.verdict,
    });
  }

  if (nf.materializedPath !== true || nf.syntheticRunAll !== false) {
    return validationReject0(path, 'materialized public status must be separate from synthetic RunAll0', {
      file,
      materializedPath: nf.materializedPath,
      syntheticRunAll: nf.syntheticRunAll,
    });
  }

  if (file.status === 'pending') {
    if (
      nf.replayAccepted !== false ||
      nf.publicConclusionEmitted !== false ||
      nf.publicConclusion !== null
    ) {
      return validationReject0(path, 'pending public status must emit no public conclusion', {
        file,
        nf,
      });
    }
  }

  if (file.status === 'rejected') {
    if (
      nf.replayAccepted !== false ||
      nf.publicConclusionEmitted !== false ||
      nf.publicConclusion !== null ||
      nf.rejectLogCount !== 1
    ) {
      return validationReject0(path, 'rejected public status must emit one replayable failure and no public conclusion', {
        file,
        nf,
      });
    }
  }

  if (file.status === 'accepted') {
    if (
      nf.replayAccepted !== true ||
      nf.publicConclusionEmitted !== true ||
      !isPlainObject(nf.publicConclusion) ||
      nf.publicConclusion.consequent !== 'P = NP'
    ) {
      return validationReject0(path, 'accepted public status must emit public conclusion only after accepted replay', {
        file,
        nf,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedPublicStatusCheck0NF',
    status: file.status,
    verdict: file.verdict,
  });
}

function validateRoundtripConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedPublicStatusRoundtripConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedPublicStatusRoundtripConfig0') {
    return validationReject0(['kind'], 'MaterializedPublicStatusRoundtripConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedPublicStatusRoundtripConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  if (typeof config.outputDir !== 'string' || config.outputDir.length === 0) {
    return validationReject0(['outputDir'], 'MaterializedPublicStatusRoundtripConfig0 outputDir must be a non-empty string', {
      actual: config.outputDir,
    });
  }

  for (const field of [
    'canonicalEnvelopeBytes',
    'overwrite',
    'verifyFinalRunWriter',
    'runCliChecks',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedPublicStatusRoundtripConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (
    config.mutateSecondWrite !== null &&
    typeof config.mutateSecondWrite !== 'function'
  ) {
    return validationReject0(['mutateSecondWrite'], 'mutateSecondWrite must be null or a function', {
      actual: typeof config.mutateSecondWrite,
    });
  }

  return validationAccept0({
    kind: 'MaterializedPublicStatusRoundtripConfig0NF',
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