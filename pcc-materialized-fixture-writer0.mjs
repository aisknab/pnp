import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedAggregateFile0,
  makeMaterializedAggregateShell0,
} from './pcc-materialized-aggregate0.mjs';

import {
  CheckMaterializedAcceptanceBridgeFile0,
  makeAcceptedMaterializedAcceptanceBridge0,
  makeMaterializedAcceptanceBridge0,
} from './pcc-materialized-acceptance-bridge0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_FIXTURE_FILENAMES0 = Object.freeze({
  pack: 'MaterializedPCCPack0.json',
  pendingBridge: 'MaterializedAcceptanceBridge.pending0.json',
  acceptedBridge: 'MaterializedAcceptanceBridge.accepted0.json',
});

export function makeMaterializedFixtureWriterConfig0(overrides = {}) {
  return {
    kind: 'MaterializedFixtureWriterConfig0',
    version: CHECKER_VERSION,
    outputDir: path.join(process.cwd(), 'materialized-fixtures0'),
    canonicalEnvelopeBytes: false,
    overwrite: true,
    verify: true,
    includePack: true,
    includePendingBridge: true,
    includeAcceptedBridge: true,
    ...overrides,
  };
}

export async function WriteMaterializedFixtureSet0(config = makeMaterializedFixtureWriterConfig0()) {
  const checker = 'WriteMaterializedFixtureSet0';
  const ledger = [];
  const cfg = makeMaterializedFixtureWriterConfig0(config);

  const shape = validateWriterConfig0(cfg);

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

  const material = makeFixtureObjects0();

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

  const writes = await writeRequestedFixtures0(cfg, material);

  ledger.push({
    phase: 'writeFixtures',
    status: writes.ok ? 'pass' : 'fail',
    digest: digestCanonical0(writes.nf ?? writes.witness ?? null),
  });

  if (!writes.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.writeFixtures`,
      path: writes.path,
      witness: writes.witness,
      ledger,
    });
  }

  let verificationNF = {
    kind: 'MaterializedFixtureVerificationSkipped0NF',
    verified: false,
    records: [],
  };

  if (cfg.verify === true) {
    const verify = await verifyWrittenFixtures0(cfg, writes.files);

    ledger.push({
      phase: 'verifyFixtures',
      status: verify.ok ? 'pass' : 'fail',
      digest: digestCanonical0(verify.nf ?? verify.witness ?? null),
    });

    if (!verify.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.verifyFixtures`,
        path: verify.path,
        witness: verify.witness,
        ledger,
      });
    }

    verificationNF = verify.nf;
  }

  const nf = {
    kind: 'MaterializedFixtureWriter0NF',
    checker,
    version: CHECKER_VERSION,
    outputDir: cfg.outputDir,
    canonicalEnvelopeBytes: cfg.canonicalEnvelopeBytes,
    overwrite: cfg.overwrite,
    verify: cfg.verify,
    fileCount: writes.files.length,
    files: writes.files,
    verification: verificationNF,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export function summarizeMaterializedFixtureWriter0(record) {
  if (record?.tag === 'accept') {
    return {
      tag: record.tag,
      checker: record.checker,
      outputDir: record.NF.outputDir,
      fileCount: record.NF.fileCount,
      files: record.NF.files.map((entry) => ({
        kind: entry.kind,
        filePath: entry.filePath,
        byteLength: entry.byteLength,
        digest: entry.digest,
      })),
      verified: record.NF.verification.verified,
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

function makeFixtureObjects0() {
  const pack = makeMaterializedAggregateShell0();

  return {
    pack,
    pendingBridge: makeMaterializedAcceptanceBridge0({
      shell: pack,
    }),
    acceptedBridge: makeAcceptedMaterializedAcceptanceBridge0({
      shell: pack,
    }),
  };
}

async function writeRequestedFixtures0(config, material) {
  const files = [];

  const requests = [
    {
      enabled: config.includePack,
      kind: 'MaterializedPCCPack0',
      filename: MATERIALIZED_FIXTURE_FILENAMES0.pack,
      value: material.pack,
    },
    {
      enabled: config.includePendingBridge,
      kind: 'MaterializedAcceptanceBridge0.pending',
      filename: MATERIALIZED_FIXTURE_FILENAMES0.pendingBridge,
      value: material.pendingBridge,
    },
    {
      enabled: config.includeAcceptedBridge,
      kind: 'MaterializedAcceptanceBridge0.accepted',
      filename: MATERIALIZED_FIXTURE_FILENAMES0.acceptedBridge,
      value: material.acceptedBridge,
    },
  ];

  for (const request of requests) {
    if (request.enabled !== true) {
      continue;
    }

    const filePath = path.join(config.outputDir, request.filename);
    const bytes = config.canonicalEnvelopeBytes
      ? stableStringify0(request.value)
      : JSON.stringify(request.value, null, 2);

    const result = await writeFile0(filePath, bytes, config.overwrite);

    if (!result.ok) {
      return result;
    }

    files.push({
      kind: request.kind,
      filename: request.filename,
      filePath,
      byteLength: Buffer.byteLength(bytes, 'utf8'),
      digest: digestCanonical0(bytes),
    });
  }

  if (files.length === 0) {
    return validationReject0(['includePack'], 'fixture writer must write at least one fixture file', {
      includePack: config.includePack,
      includePendingBridge: config.includePendingBridge,
      includeAcceptedBridge: config.includeAcceptedBridge,
    });
  }

  return {
    ok: true,
    files,
    nf: {
      kind: 'MaterializedFixtureWrites0NF',
      fileCount: files.length,
      files,
    },
  };
}

async function verifyWrittenFixtures0(config, files) {
  const records = [];

  for (const entry of files) {
    let record;

    if (entry.kind === 'MaterializedPCCPack0') {
      record = await CheckMaterializedAggregateFile0(entry.filePath, {
        loaderConfig: {
          requireCanonicalEnvelopeBytes: config.canonicalEnvelopeBytes,
        },
      });
    } else if (
      entry.kind === 'MaterializedAcceptanceBridge0.pending' ||
      entry.kind === 'MaterializedAcceptanceBridge0.accepted'
    ) {
      record = await CheckMaterializedAcceptanceBridgeFile0(entry.filePath);
    } else {
      return validationReject0(['files', entry.filename], 'unknown fixture kind during verification', {
        entry,
      });
    }

    if (isRejectRecord0(record)) {
      return validationReject0(['files', entry.filename], 'written materialized fixture failed verification', {
        entry,
        inner: compactReject0(record),
      });
    }

    records.push({
      kind: entry.kind,
      filename: entry.filename,
      verifier: record.checker,
      digest: record.Digest ?? record.digest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedFixtureVerification0NF',
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
      kind: 'MaterializedFixtureWrite0NF',
      filePath,
      byteLength: Buffer.byteLength(bytes, 'utf8'),
    });
  } catch (error) {
    return validationReject0(['filePath'], 'failed to write materialized fixture file', {
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
      kind: 'MaterializedFixtureOutputDir0NF',
      outputDir,
    });
  } catch (error) {
    return validationReject0(['outputDir'], 'failed to create materialized fixture output directory', {
      outputDir,
      error: error.message,
    });
  }
}

function validateWriterConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedFixtureWriterConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedFixtureWriterConfig0') {
    return validationReject0(['kind'], 'MaterializedFixtureWriterConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedFixtureWriterConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  if (typeof config.outputDir !== 'string' || config.outputDir.length === 0) {
    return validationReject0(['outputDir'], 'MaterializedFixtureWriterConfig0 outputDir must be a non-empty string', {
      actual: config.outputDir,
    });
  }

  for (const field of [
    'canonicalEnvelopeBytes',
    'overwrite',
    'verify',
    'includePack',
    'includePendingBridge',
    'includeAcceptedBridge',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedFixtureWriterConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedFixtureWriterConfig0NF',
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