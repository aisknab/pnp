import { spawnSync } from 'node:child_process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedFinalVerdictFile0,
} from './pcc-materialized-final-verdict0.mjs';

import {
  MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0,
  WriteMaterializedAcceptRunFixtureSet0,
} from './pcc-materialized-accept-run-fixtures0.mjs';

const CHECKER_VERSION = 0;
const REPO_ROOT = path.dirname(fileURLToPath(import.meta.url));

export const MATERIALIZED_FINAL_RUN_FIXTURE_FILENAMES0 = Object.freeze({
  pending: MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.pending,
  reject: MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.reject,
  accepted: MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.accepted,
});

export function makeMaterializedFinalRunFixtureWriterConfig0(overrides = {}) {
  return {
    kind: 'MaterializedFinalRunFixtureWriterConfig0',
    version: CHECKER_VERSION,
    outputDir: path.join(process.cwd(), 'materialized-final-run-fixtures0'),
    canonicalEnvelopeBytes: false,
    overwrite: true,
    verifyAcceptRunWriter: true,
    verifyDirect: true,
    verifyCli: true,
    includePackageFixture: true,
    includePending: true,
    includeReject: true,
    includeAccepted: true,
    ...overrides,
  };
}

export async function WriteMaterializedFinalRunFixtureSet0(config = makeMaterializedFinalRunFixtureWriterConfig0()) {
  const checker = 'WriteMaterializedFinalRunFixtureSet0';
  const ledger = [];
  const cfg = makeMaterializedFinalRunFixtureWriterConfig0(config);

  const shape = validateFinalRunFixtureWriterConfig0(cfg);

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

  const acceptRunWriter = await WriteMaterializedAcceptRunFixtureSet0({
    outputDir: cfg.outputDir,
    canonicalEnvelopeBytes: cfg.canonicalEnvelopeBytes,
    overwrite: cfg.overwrite,
    verifyDirect: cfg.verifyAcceptRunWriter,
    verifyCli: cfg.verifyAcceptRunWriter,
    includePackageFixture: cfg.includePackageFixture,
    includePending: cfg.includePending,
    includeReject: cfg.includeReject,
    includeAccepted: cfg.includeAccepted,
  });

  const acceptRunWriterResult = recordToValidation0(acceptRunWriter, ['AcceptRunFixtures']);

  ledger.push({
    phase: 'WriteMaterializedAcceptRunFixtureSet0',
    status: acceptRunWriterResult.ok ? 'pass' : 'fail',
    digest: acceptRunWriter.Digest ?? acceptRunWriter.digest ?? digestCanonical0(acceptRunWriter),
  });

  if (!acceptRunWriterResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.acceptRunFixtures`,
      path: acceptRunWriterResult.path,
      witness: acceptRunWriterResult.witness,
      ledger,
    });
  }

  const files = acceptRunWriter.NF.files;

  let directVerification = validationAccept0({
    kind: 'MaterializedFinalRunDirectVerificationSkipped0NF',
    verified: false,
    records: [],
  });

  if (cfg.verifyDirect === true) {
    directVerification = await verifyFinalRunFixturesDirect0(files);
  }

  ledger.push({
    phase: 'verifyDirectFinalVerdicts',
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
    kind: 'MaterializedFinalRunCliVerificationSkipped0NF',
    verified: false,
    records: [],
  });

  if (cfg.verifyCli === true) {
    cliVerification = await verifyFinalRunFixturesCli0(files);
  }

  ledger.push({
    phase: 'verifyCliFinalVerdicts',
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
    kind: 'MaterializedFinalRunFixtureWriter0NF',
    checker,
    version: CHECKER_VERSION,
    outputDir: cfg.outputDir,
    packageFilePath: acceptRunWriter.NF.packageFilePath,
    aggregateDigest: acceptRunWriter.NF.aggregateDigest,
    canonicalEnvelopeBytes: cfg.canonicalEnvelopeBytes,
    acceptRunWriterDigest: acceptRunWriter.Digest ?? acceptRunWriter.digest,
    fileCount: files.length,
    files,
    directVerification: directVerification.nf,
    cliVerification: cliVerification.nf,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export function summarizeMaterializedFinalRunFixtureWriter0(record) {
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

async function verifyFinalRunFixturesDirect0(files) {
  const records = [];

  for (const file of files) {
    const record = await CheckMaterializedFinalVerdictFile0(file.filePath);

    if (isRejectRecord0(record)) {
      return validationReject0(['files', file.filename], 'materialized final-run fixture failed direct final-verdict verification', {
        file,
        inner: compactReject0(record),
      });
    }

    const verdict = validateFinalVerdictRecord0(record, file, ['files', file.filename]);

    if (!verdict.ok) {
      return verdict;
    }

    records.push({
      filename: file.filename,
      verdict: file.verdict,
      checker: record.checker,
      digest: record.Digest ?? record.digest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedFinalRunDirectVerification0NF',
    verified: true,
    records,
  });
}

async function verifyFinalRunFixturesCli0(files) {
  const cliPath = path.join(REPO_ROOT, 'bin', 'check-materialized-final-verdict0.mjs');
  const records = [];

  for (const file of files) {
    const child = spawnSync(process.execPath, [cliPath, file.filePath], {
      encoding: 'utf8',
      windowsHide: true,
    });

    if (child.status !== 0) {
      return validationReject0(['files', file.filename], 'materialized final-run fixture failed final-verdict CLI verification', {
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
      return validationReject0(['files', file.filename], 'materialized final-run fixture final-verdict CLI did not emit JSON', {
        file,
        stdout: child.stdout,
        error: error.message,
      });
    }

    if (parsed.tag !== 'accept') {
      return validationReject0(['files', file.filename], 'materialized final-run fixture final-verdict CLI emitted non-accept', {
        file,
        parsed,
      });
    }

    const verdict = validateFinalVerdictSummary0(parsed, file, ['files', file.filename]);

    if (!verdict.ok) {
      return verdict;
    }

    records.push({
      filename: file.filename,
      verdict: file.verdict,
      checker: parsed.checker,
      digest: parsed.digest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedFinalRunCliVerification0NF',
    verified: true,
    records,
  });
}

function validateFinalVerdictRecord0(record, file, path) {
  const nf = record.NF ?? record.nf;

  if (!isPlainObject(nf)) {
    return validationReject0(path, 'final verdict record must include a normal form object', {
      file,
      actual: typeof nf,
    });
  }

  return validateFinalVerdictNF0(nf, file, path);
}

function validateFinalVerdictSummary0(summary, file, path) {
  return validateFinalVerdictNF0(summary, file, path);
}

function validateFinalVerdictNF0(nf, file, path) {
  if (nf.verdict !== file.verdict) {
    return validationReject0([...path, 'verdict'], 'materialized final-run fixture returned wrong verdict', {
      file,
      expected: file.verdict,
      actual: nf.verdict,
    });
  }

  if (file.verdict === 'pending') {
    if (nf.replayAccepted !== false || nf.publicConclusionEmitted !== false || nf.publicConclusion !== null) {
      return validationReject0(path, 'pending final-run fixture must emit no public conclusion', {
        file,
        nf,
      });
    }
  }

  if (file.verdict === 'reject') {
    if (
      nf.replayAccepted !== false ||
      nf.publicConclusionEmitted !== false ||
      nf.publicConclusion !== null ||
      nf.rejectLogCount !== 1
    ) {
      return validationReject0(path, 'reject final-run fixture must emit one replayable failure and no public conclusion', {
        file,
        nf,
      });
    }
  }

  if (file.verdict === 'accept') {
    if (
      nf.replayAccepted !== true ||
      nf.publicConclusionEmitted !== true ||
      !isPlainObject(nf.publicConclusion) ||
      nf.publicConclusion.consequent !== 'P = NP'
    ) {
      return validationReject0(path, 'accepted final-run fixture must emit the public conclusion after accepted replay', {
        file,
        nf,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedFinalRunVerdictCheck0NF',
    verdict: file.verdict,
  });
}

function validateFinalRunFixtureWriterConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedFinalRunFixtureWriterConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedFinalRunFixtureWriterConfig0') {
    return validationReject0(['kind'], 'MaterializedFinalRunFixtureWriterConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedFinalRunFixtureWriterConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  if (typeof config.outputDir !== 'string' || config.outputDir.length === 0) {
    return validationReject0(['outputDir'], 'MaterializedFinalRunFixtureWriterConfig0 outputDir must be a non-empty string', {
      actual: config.outputDir,
    });
  }

  for (const field of [
    'canonicalEnvelopeBytes',
    'overwrite',
    'verifyAcceptRunWriter',
    'verifyDirect',
    'verifyCli',
    'includePackageFixture',
    'includePending',
    'includeReject',
    'includeAccepted',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedFinalRunFixtureWriterConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedFinalRunFixtureWriterConfig0NF',
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