import { createHash } from 'node:crypto';
import fs from 'node:fs/promises';
import { fileURLToPath } from 'node:url';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedPCCPackShell0,
} from './pcc-materialized-pack0.mjs';

const CHECKER_VERSION = 0;

export function makeMaterializedLoaderConfig0(overrides = {}) {
  return {
    kind: 'MaterializedLoaderConfig0',
    version: CHECKER_VERSION,
    requireCanonicalEnvelopeBytes: false,
    maxBytes: 16 * 1024 * 1024,
    ...overrides,
  };
}

export async function LoadMaterializedPCCPackShellFile0(filePath, config = makeMaterializedLoaderConfig0()) {
  const checker = 'LoadMaterializedPCCPackShellFile0';
  const ledger = [];
  const cfg = makeMaterializedLoaderConfig0(config);

  const configCheck = validateLoaderConfig0(cfg);

  ledger.push({
    phase: 'config',
    status: configCheck.ok ? 'pass' : 'fail',
    digest: digestCanonical0(configCheck.nf ?? configCheck.witness ?? null),
  });

  if (!configCheck.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.config`,
      path: configCheck.path,
      witness: configCheck.witness,
      ledger,
    });
  }

  const pathCheck = normalizeFilePath0(filePath);

  ledger.push({
    phase: 'path',
    status: pathCheck.ok ? 'pass' : 'fail',
    digest: digestCanonical0(pathCheck.nf ?? pathCheck.witness ?? null),
  });

  if (!pathCheck.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.path`,
      path: pathCheck.path,
      witness: pathCheck.witness,
      ledger,
    });
  }

  const read = await readFileUtf80(pathCheck.filePath, cfg);

  ledger.push({
    phase: 'read',
    status: read.ok ? 'pass' : 'fail',
    digest: digestCanonical0(read.nf ?? read.witness ?? null),
  });

  if (!read.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.read`,
      path: read.path,
      witness: read.witness,
      ledger,
    });
  }

  const parsed = parseJson0(read.text);

  ledger.push({
    phase: 'parse',
    status: parsed.ok ? 'pass' : 'fail',
    digest: digestCanonical0(parsed.nf ?? parsed.witness ?? null),
  });

  if (!parsed.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.parse`,
      path: parsed.path,
      witness: parsed.witness,
      ledger,
    });
  }

  if (cfg.requireCanonicalEnvelopeBytes === true) {
    const canonicalText = stableStringify0(parsed.value);

    if (canonicalText !== read.text) {
      const witness = {
        reason: 'materialized envelope file bytes must be canonical JSON',
        detail: {
          expectedDigest: sha256Utf8DigestRecord0(canonicalText),
          actualDigest: sha256Utf8DigestRecord0(read.text),
        },
      };

      ledger.push({
        phase: 'canonicalEnvelopeBytes',
        status: 'fail',
        digest: digestCanonical0(witness),
      });

      return makeRejectRecord({
        checker,
        coord: `${checker}.canonicalEnvelopeBytes`,
        path: ['file'],
        witness,
        ledger,
      });
    }
  }

  const nf = {
    kind: 'LoadedMaterializedPCCPackShellFile0NF',
    checker,
    version: CHECKER_VERSION,
    filePath: pathCheck.filePath,
    byteLength: read.byteLength,
    fileDigest: sha256Utf8DigestRecord0(read.text),
    shellDigest: digestCanonical0(parsed.value),
    requireCanonicalEnvelopeBytes: cfg.requireCanonicalEnvelopeBytes,
  };

  return {
    ...makeAcceptRecord({
      checker,
      nf,
      ledger,
    }),
    Shell: parsed.value,
    shell: parsed.value,
  };
}

export async function CheckMaterializedPCCPackShellFile0(filePath, config = makeMaterializedLoaderConfig0()) {
  const checker = 'CheckMaterializedPCCPackShellFile0';
  const ledger = [];

  const loaded = await LoadMaterializedPCCPackShellFile0(filePath, config);
  const loadResult = recordToValidation0(loaded, ['file']);

  ledger.push({
    phase: 'load',
    status: loadResult.ok ? 'pass' : 'fail',
    digest: loaded.Digest ?? loaded.digest ?? digestCanonical0(loaded),
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

  const checked = await CheckMaterializedPCCPackShell0(loaded.Shell);
  const checkResult = recordToValidation0(checked, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedPCCPackShell0',
    status: checkResult.ok ? 'pass' : 'fail',
    digest: checked.Digest ?? checked.digest ?? digestCanonical0(checked),
  });

  if (!checkResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.shell`,
      path: checkResult.path,
      witness: checkResult.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'CheckedMaterializedPCCPackShellFile0NF',
    checker,
    version: CHECKER_VERSION,
    filePath: loaded.NF.filePath,
    byteLength: loaded.NF.byteLength,
    fileDigest: loaded.NF.fileDigest,
    shellDigest: loaded.NF.shellDigest,
    shellCheckDigest: checked.Digest ?? checked.digest,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export function summarizeMaterializedShellFileRecord0(record) {
  if (record?.tag === 'accept') {
    return {
      tag: record.tag,
      checker: record.checker,
      filePath: record.NF?.filePath ?? record.nf?.filePath,
      byteLength: record.NF?.byteLength ?? record.nf?.byteLength,
      fileDigest: record.NF?.fileDigest ?? record.nf?.fileDigest,
      shellDigest: record.NF?.shellDigest ?? record.nf?.shellDigest,
      shellCheckDigest: record.NF?.shellCheckDigest ?? record.nf?.shellCheckDigest,
      digest: record.Digest ?? record.digest,
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

function validateLoaderConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedLoaderConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedLoaderConfig0') {
    return validationReject0(['kind'], 'MaterializedLoaderConfig0 kind must be MaterializedLoaderConfig0 when present', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedLoaderConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  if (typeof config.requireCanonicalEnvelopeBytes !== 'boolean') {
    return validationReject0(['requireCanonicalEnvelopeBytes'], 'requireCanonicalEnvelopeBytes must be boolean', {
      actual: config.requireCanonicalEnvelopeBytes,
    });
  }

  if (!Number.isInteger(config.maxBytes) || config.maxBytes <= 0) {
    return validationReject0(['maxBytes'], 'maxBytes must be a positive integer', {
      actual: config.maxBytes,
    });
  }

  return validationAccept0({
    kind: 'MaterializedLoaderConfig0NF',
  });
}

function normalizeFilePath0(filePath) {
  if (filePath instanceof URL) {
    return {
      ok: true,
      filePath: fileURLToPath(filePath),
      nf: {
        kind: 'MaterializedFilePath0NF',
      },
    };
  }

  if (typeof filePath !== 'string' || filePath.length === 0) {
    return validationReject0(['filePath'], 'filePath must be a non-empty string or file URL', {
      actual: filePath,
    });
  }

  return {
    ok: true,
    filePath,
    nf: {
      kind: 'MaterializedFilePath0NF',
    },
  };
}

async function readFileUtf80(filePath, config) {
  let stat;

  try {
    stat = await fs.stat(filePath);
  } catch (error) {
    return validationReject0(['filePath'], 'materialized shell file must exist', {
      filePath,
      error: error.message,
    });
  }

  if (!stat.isFile()) {
    return validationReject0(['filePath'], 'materialized shell path must be a file', {
      filePath,
    });
  }

  if (stat.size > config.maxBytes) {
    return validationReject0(['filePath'], 'materialized shell file exceeds maxBytes', {
      filePath,
      maxBytes: config.maxBytes,
      actualBytes: stat.size,
    });
  }

  try {
    const text = await fs.readFile(filePath, 'utf8');

    return {
      ok: true,
      text,
      byteLength: Buffer.byteLength(text, 'utf8'),
      nf: {
        kind: 'MaterializedFileRead0NF',
        byteLength: Buffer.byteLength(text, 'utf8'),
      },
    };
  } catch (error) {
    return validationReject0(['filePath'], 'materialized shell file must be readable UTF-8 text', {
      filePath,
      error: error.message,
    });
  }
}

function parseJson0(text) {
  try {
    const value = JSON.parse(text);

    return {
      ok: true,
      value,
      nf: {
        kind: 'MaterializedJsonParse0NF',
      },
    };
  } catch (error) {
    return validationReject0(['file'], 'materialized shell file must parse as JSON', {
      error: error.message,
    });
  }
}

function sha256Utf8DigestRecord0(value) {
  return {
    alg: 'SHA256',
    bytes: 'utf8',
    hex: createHash('sha256').update(String(value), 'utf8').digest('hex'),
  };
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