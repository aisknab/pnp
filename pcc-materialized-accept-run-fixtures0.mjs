import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedAggregateFile0,
} from './pcc-materialized-aggregate0.mjs';

import {
  MATERIALIZED_FIXTURE_FILENAMES0,
  WriteMaterializedFixtureSet0,
} from './pcc-materialized-fixture-writer0.mjs';

import {
  CheckMaterializedAcceptRunFile0,
  makeMaterializedAcceptRun0,
  makeMaterializedReplayFirstFailure0,
  makeMaterializedReplayTranscript0,
} from './pcc-materialized-accept-run0.mjs';

const CHECKER_VERSION = 0;
const REPO_ROOT = path.dirname(fileURLToPath(import.meta.url));

export const MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0 = Object.freeze({
  pending: 'MaterializedAcceptRun.pending0.json',
  reject: 'MaterializedAcceptRun.reject0.json',
  accepted: 'MaterializedAcceptRun.accepted0.json',
});

export function makeMaterializedAcceptRunFixtureWriterConfig0(overrides = {}) {
  return {
    kind: 'MaterializedAcceptRunFixtureWriterConfig0',
    version: CHECKER_VERSION,
    outputDir: path.join(process.cwd(), 'materialized-accept-run-fixtures0'),
    canonicalEnvelopeBytes: false,
    overwrite: true,
    verifyDirect: true,
    verifyCli: true,
    includePackageFixture: true,
    includePending: true,
    includeReject: true,
    includeAccepted: true,
    ...overrides,
  };
}

export async function WriteMaterializedAcceptRunFixtureSet0(config = makeMaterializedAcceptRunFixtureWriterConfig0()) {
  const checker = 'WriteMaterializedAcceptRunFixtureSet0';
  const ledger = [];
  const cfg = makeMaterializedAcceptRunFixtureWriterConfig0(config);

  const shape = validateAcceptRunFixtureWriterConfig0(cfg);

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

  const ensureDir = await ensureOutputDir0(cfg.outputDir);

  ledger.push({
    phase: 'ensureOutputDir',
    status: ensureDir.ok ? 'pass' : 'fail',
    digest: digestCanonical0(ensureDir.nf ?? ensureDir.witness ?? null),
  });

  if (!ensureDir.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.outputDir`,
      path: ensureDir.path,
      witness: ensureDir.witness,
      ledger,
    });
  }

  if (cfg.includePackageFixture === true) {
    const packageWrite = await WriteMaterializedFixtureSet0({
      outputDir: cfg.outputDir,
      canonicalEnvelopeBytes: cfg.canonicalEnvelopeBytes,
      overwrite: cfg.overwrite,
      verify: true,
      includePack: true,
      includePendingBridge: false,
      includeAcceptedBridge: false,
    });

    const packageWriteResult = recordToValidation0(packageWrite, ['PackageFixture']);

    ledger.push({
      phase: 'WriteMaterializedFixtureSet0.package',
      status: packageWriteResult.ok ? 'pass' : 'fail',
      digest: packageWrite.Digest ?? packageWrite.digest ?? digestCanonical0(packageWrite),
    });

    if (!packageWriteResult.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.packageFixture`,
        path: packageWriteResult.path,
        witness: packageWriteResult.witness,
        ledger,
      });
    }
  }

  const packFilePath = path.join(cfg.outputDir, MATERIALIZED_FIXTURE_FILENAMES0.pack);
  const aggregateRecord = await CheckMaterializedAggregateFile0(packFilePath, {
    loaderConfig: {
      requireCanonicalEnvelopeBytes: cfg.canonicalEnvelopeBytes,
    },
  });
  const aggregate = recordToValidation0(aggregateRecord, ['GeneratedPackage']);

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

  const writes = await writeAcceptRunFixtures0(cfg, {
    packFilePath,
    aggregateDigest: aggregateRecord.Digest ?? aggregateRecord.digest,
  });

  ledger.push({
    phase: 'writeAcceptRunFixtures',
    status: writes.ok ? 'pass' : 'fail',
    digest: digestCanonical0(writes.nf ?? writes.witness ?? null),
  });

  if (!writes.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.writeAcceptRuns`,
      path: writes.path,
      witness: writes.witness,
      ledger,
    });
  }

  let directVerification = validationAccept0({
    kind: 'MaterializedAcceptRunFixtureDirectVerificationSkipped0NF',
    verified: false,
    records: [],
  });

  if (cfg.verifyDirect === true) {
    directVerification = await verifyAcceptRunFixturesDirect0(writes.files);
  }

  ledger.push({
    phase: 'verifyDirect',
    status: directVerification.ok ? 'pass' : 'fail',
    digest: digestCanonical0(directVerification.nf ?? directVerification.witness ?? null),
  });

  if (!directVerification.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.verifyDirect`,
      path: directVerification.path,
      witness: directVerification.witness,
      ledger,
    });
  }

  let cliVerification = validationAccept0({
    kind: 'MaterializedAcceptRunFixtureCliVerificationSkipped0NF',
    verified: false,
    records: [],
  });

  if (cfg.verifyCli === true) {
    cliVerification = await verifyAcceptRunFixturesCli0(writes.files);
  }

  ledger.push({
    phase: 'verifyCli',
    status: cliVerification.ok ? 'pass' : 'fail',
    digest: digestCanonical0(cliVerification.nf ?? cliVerification.witness ?? null),
  });

  if (!cliVerification.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.verifyCli`,
      path: cliVerification.path,
      witness: cliVerification.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedAcceptRunFixtureWriter0NF',
    checker,
    version: CHECKER_VERSION,
    outputDir: cfg.outputDir,
    packageFilePath: packFilePath,
    aggregateDigest: aggregateRecord.Digest ?? aggregateRecord.digest,
    canonicalEnvelopeBytes: cfg.canonicalEnvelopeBytes,
    fileCount: writes.files.length,
    files: writes.files,
    directVerification: directVerification.nf,
    cliVerification: cliVerification.nf,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export function summarizeMaterializedAcceptRunFixtureWriter0(record) {
  if (record?.tag === 'accept') {
    return {
      tag: record.tag,
      checker: record.checker,
      outputDir: record.NF.outputDir,
      packageFilePath: record.NF.packageFilePath,
      fileCount: record.NF.fileCount,
      files: record.NF.files.map((entry) => ({
        kind: entry.kind,
        verdict: entry.verdict,
        filePath: entry.filePath,
        byteLength: entry.byteLength,
        digest: entry.digest,
      })),
      directVerified: record.NF.directVerification.verified,
      cliVerified: record.NF.cliVerification.verified,
      digest: record.Digest,
    };
  }

  return {
    tag: record?.tag,
    checker: record?.checker,
    coord: record?.Coord ?? record?.coord,
    path: record?.Path ?? record?.path,
    witness: record?.Witness ?? record?.witness,
    digest: record?.Digest ?? record?.digest,
  };
}

function makeAcceptRunFixtureObjects0({
  packFilePath,
  aggregateDigest,
}) {
  const rejectFirstFailure = makeMaterializedReplayFirstFailure0({
    coord: 'MaterializedAcceptRunFixture0.syntheticFirstFailure',
    path: [
      'ReplayTranscript',
      'entries',
    ],
    rejectionClass: 'ReplayMismatch',
  });

  const rejectTranscript = makeMaterializedReplayTranscript0({
    verdict: 'reject',
    firstFailure: rejectFirstFailure,
  });

  return [
    {
      kind: 'MaterializedAcceptRun0.pending',
      verdict: 'pending',
      filename: MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.pending,
      value: makeMaterializedAcceptRun0({
        packFilePath,
        aggregateDigest,
        verdict: 'pending',
      }),
    },
    {
      kind: 'MaterializedAcceptRun0.reject',
      verdict: 'reject',
      filename: MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.reject,
      value: makeMaterializedAcceptRun0({
        packFilePath,
        aggregateDigest,
        verdict: 'reject',
        replayTranscript: rejectTranscript,
      }),
    },
    {
      kind: 'MaterializedAcceptRun0.accepted',
      verdict: 'accept',
      filename: MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.accepted,
      value: makeMaterializedAcceptRun0({
        packFilePath,
        aggregateDigest,
        verdict: 'accept',
      }),
    },
  ];
}

async function writeAcceptRunFixtures0(config, aggregateInfo) {
  const allFixtures = makeAcceptRunFixtureObjects0(aggregateInfo);

  const requested = allFixtures.filter((fixture) => {
    if (fixture.verdict === 'pending') {
      return config.includePending;
    }

    if (fixture.verdict === 'reject') {
      return config.includeReject;
    }

    if (fixture.verdict === 'accept') {
      return config.includeAccepted;
    }

    return false;
  });

  if (requested.length === 0) {
    return validationReject0(['includePending'], 'accept-run fixture writer must write at least one accept-run fixture', {
      includePending: config.includePending,
      includeReject: config.includeReject,
      includeAccepted: config.includeAccepted,
    });
  }

  const files = [];

  for (const fixture of requested) {
    const filePath = path.join(config.outputDir, fixture.filename);
    const bytes = config.canonicalEnvelopeBytes
      ? stableStringify0(fixture.value)
      : JSON.stringify(fixture.value, null, 2);

    const write = await writeFile0(filePath, bytes, config.overwrite);

    if (!write.ok) {
      return write;
    }

    files.push({
      kind: fixture.kind,
      verdict: fixture.verdict,
      filename: fixture.filename,
      filePath,
      byteLength: Buffer.byteLength(bytes, 'utf8'),
      digest: digestCanonical0(bytes),
    });
  }

  return {
    ok: true,
    files,
    nf: {
      kind: 'MaterializedAcceptRunFixtureWrites0NF',
      fileCount: files.length,
      files,
    },
  };
}

async function verifyAcceptRunFixturesDirect0(files) {
  const records = [];

  for (const file of files) {
    const record = await CheckMaterializedAcceptRunFile0(file.filePath);

    if (isRejectRecord0(record)) {
      return validationReject0(['files', file.filename], 'materialized accept-run fixture failed direct verification', {
        file,
        inner: compactReject0(record),
      });
    }

    const nf = record.NF ?? record.nf;

    if (nf.verdict !== file.verdict) {
      return validationReject0(['files', file.filename], 'materialized accept-run fixture direct verification returned wrong verdict', {
        file,
        actual: nf.verdict,
      });
    }

    records.push({
      filename: file.filename,
      verdict: file.verdict,
      checker: record.checker,
      digest: record.Digest ?? record.digest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedAcceptRunFixtureDirectVerification0NF',
    verified: true,
    records,
  });
}

async function verifyAcceptRunFixturesCli0(files) {
  const cliPath = path.join(REPO_ROOT, 'bin', 'check-materialized-accept-run0.mjs');
  const records = [];

  for (const file of files) {
    const child = spawnSync(process.execPath, [cliPath, file.filePath], {
      encoding: 'utf8',
      windowsHide: true,
    });

    if (child.status !== 0) {
      return validationReject0(['files', file.filename], 'materialized accept-run fixture failed CLI verification', {
        file,
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
      return validationReject0(['files', file.filename], 'materialized accept-run fixture CLI did not emit JSON', {
        file,
        stdout: child.stdout,
        error: error.message,
      });
    }

    if (parsed.tag !== 'accept') {
      return validationReject0(['files', file.filename], 'materialized accept-run fixture CLI emitted non-accept', {
        file,
        parsed,
      });
    }

    if (parsed.verdict !== file.verdict) {
      return validationReject0(['files', file.filename], 'materialized accept-run fixture CLI returned wrong verdict', {
        file,
        parsed,
      });
    }

    records.push({
      filename: file.filename,
      verdict: file.verdict,
      checker: parsed.checker,
      digest: parsed.digest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedAcceptRunFixtureCliVerification0NF',
    verified: true,
    records,
  });
}

async function writeFile0(filePath, bytes, overwrite) {
  try {
    await fs.writeFile(filePath, bytes, {
      encoding: 'utf8',
      flag: overwrite ? 'w' : 'wx',
    });

    return validationAccept0({
      kind: 'MaterializedAcceptRunFixtureWrite0NF',
      filePath,
      byteLength: Buffer.byteLength(bytes, 'utf8'),
    });
  } catch (error) {
    return validationReject0(['filePath'], 'failed to write materialized accept-run fixture file', {
      filePath,
      overwrite,
      error: error.message,
    });
  }
}

async function ensureOutputDir0(outputDir) {
  try {
    await fs.mkdir(outputDir, {
      recursive: true,
    });

    return validationAccept0({
      kind: 'MaterializedAcceptRunFixtureOutputDir0NF',
      outputDir,
    });
  } catch (error) {
    return validationReject0(['outputDir'], 'failed to create materialized accept-run fixture output directory', {
      outputDir,
      error: error.message,
    });
  }
}

function validateAcceptRunFixtureWriterConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedAcceptRunFixtureWriterConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedAcceptRunFixtureWriterConfig0') {
    return validationReject0(['kind'], 'MaterializedAcceptRunFixtureWriterConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedAcceptRunFixtureWriterConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  if (typeof config.outputDir !== 'string' || config.outputDir.length === 0) {
    return validationReject0(['outputDir'], 'MaterializedAcceptRunFixtureWriterConfig0 outputDir must be a non-empty string', {
      actual: config.outputDir,
    });
  }

  for (const field of [
    'canonicalEnvelopeBytes',
    'overwrite',
    'verifyDirect',
    'verifyCli',
    'includePackageFixture',
    'includePending',
    'includeReject',
    'includeAccepted',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedAcceptRunFixtureWriterConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedAcceptRunFixtureWriterConfig0NF',
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