import { createHash } from 'node:crypto';
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
  CheckMaterializedAcceptanceBridgeFile0,
} from './pcc-materialized-acceptance-bridge0.mjs';

import {
  MATERIALIZED_FIXTURE_FILENAMES0,
} from './pcc-materialized-fixture-writer0.mjs';

const CHECKER_VERSION = 0;
const REPO_ROOT = path.dirname(fileURLToPath(import.meta.url));

export const MATERIALIZED_DIGEST_RESOLVER_DIGEST_KINDS0 = Object.freeze([
  'fileBytesSha256',
  'canonicalBytesSha256',
  'canonicalObjectDigest',
]);

export function makeMaterializedDigestResolverConfig0(overrides = {}) {
  return {
    kind: 'MaterializedDigestResolverConfig0',
    version: CHECKER_VERSION,
    fixtureDir: path.join(process.cwd(), 'materialized-fixtures0'),
    filenames: Object.values(MATERIALIZED_FIXTURE_FILENAMES0),
    verify: true,
    includeBytes: true,
    ...overrides,
  };
}

export async function IndexMaterializedFixtureDigests0(config = makeMaterializedDigestResolverConfig0()) {
  const checker = 'IndexMaterializedFixtureDigests0';
  const ledger = [];
  const cfg = makeMaterializedDigestResolverConfig0(config);

  const shape = validateResolverConfig0(cfg);

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

  const entries = [];

  for (const filename of cfg.filenames) {
    const filePath = path.join(cfg.fixtureDir, filename);
    const read = await readFixtureFile0(filePath, filename);

    ledger.push({
      phase: `read.${filename}`,
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

    if (cfg.verify === true) {
      const verified = await verifyFixtureFile0(filePath, filename);

      ledger.push({
        phase: `verify.${filename}`,
        status: verified.ok ? 'pass' : 'fail',
        digest: digestCanonical0(verified.nf ?? verified.witness ?? null),
      });

      if (!verified.ok) {
        return makeRejectRecord({
          checker,
          coord: `${checker}.verify`,
          path: verified.path,
          witness: verified.witness,
          ledger,
        });
      }
    }

    entries.push(makeIndexEntry0({
      filename,
      filePath,
      fileBytes: read.text,
      parsed: read.value,
    }));
  }

  const lookup = buildDigestLookup0(entries);
  const ambiguity = findAmbiguousDigest0(lookup);

  ledger.push({
    phase: 'lookup',
    status: ambiguity === null ? 'pass' : 'fail',
    digest: digestCanonical0(ambiguity ?? lookup),
  });

  if (ambiguity !== null) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.lookup`,
      path: ['DigestIndex', ambiguity.digest],
      witness: {
        reason: 'materialized digest index contains an ambiguous cross-file digest',
        detail: ambiguity,
      },
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedDigestIndex0NF',
    checker,
    version: CHECKER_VERSION,
    fixtureDir: cfg.fixtureDir,
    fileCount: entries.length,
    digestKinds: MATERIALIZED_DIGEST_RESOLVER_DIGEST_KINDS0,
    reverseLookupOnly: true,
    notCryptographicInversion: true,
    entries: entries.map((entry) => summarizeIndexEntry0(entry)),
  };

  return {
    ...makeAcceptRecord({
      checker,
      nf,
      ledger,
    }),
    IndexEntries: entries,
    Lookup: lookup,
    indexEntries: entries,
    lookup,
  };
}

export async function ResolveMaterializedDigest0(digestInput, config = makeMaterializedDigestResolverConfig0()) {
  const checker = 'ResolveMaterializedDigest0';
  const ledger = [];
  const cfg = makeMaterializedDigestResolverConfig0(config);

  const digest = normalizeDigestInput0(digestInput);

  ledger.push({
    phase: 'digest',
    status: digest.ok ? 'pass' : 'fail',
    digest: digestCanonical0(digest.nf ?? digest.witness ?? null),
  });

  if (!digest.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.digest`,
      path: digest.path,
      witness: digest.witness,
      ledger,
    });
  }

  const indexRecord = await IndexMaterializedFixtureDigests0(cfg);
  const indexResult = recordToValidation0(indexRecord, ['DigestIndex']);

  ledger.push({
    phase: 'IndexMaterializedFixtureDigests0',
    status: indexResult.ok ? 'pass' : 'fail',
    digest: indexRecord.Digest ?? indexRecord.digest ?? digestCanonical0(indexRecord),
  });

  if (!indexResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.index`,
      path: indexResult.path,
      witness: indexResult.witness,
      ledger,
    });
  }

  const matches = resolveMatches0(indexRecord.IndexEntries, digest.hex);

  ledger.push({
    phase: 'resolve',
    status: matches.ok ? 'pass' : 'fail',
    digest: digestCanonical0(matches.nf ?? matches.witness ?? null),
  });

  if (!matches.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.resolve`,
      path: matches.path,
      witness: matches.witness,
      ledger,
    });
  }

  const resolved = matches.entry;
  const read = await readFixtureFile0(resolved.filePath, resolved.filename);

  ledger.push({
    phase: 'readResolved',
    status: read.ok ? 'pass' : 'fail',
    digest: digestCanonical0(read.nf ?? read.witness ?? null),
  });

  if (!read.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.readResolved`,
      path: read.path,
      witness: read.witness,
      ledger,
    });
  }

  const canonicalBytes = stableStringify0(read.value);
  const nf = {
    kind: 'MaterializedDigestResolution0NF',
    checker,
    version: CHECKER_VERSION,
    digest: digest.hex,
    matchedDigestKinds: matches.matchedDigestKinds,
    fixtureDir: cfg.fixtureDir,
    filename: resolved.filename,
    filePath: resolved.filePath,
    byteLength: Buffer.byteLength(read.text, 'utf8'),
    canonicalByteLength: Buffer.byteLength(canonicalBytes, 'utf8'),
    fileBytesSha256: sha256Utf8DigestRecord0(read.text),
    canonicalBytesSha256: sha256Utf8DigestRecord0(canonicalBytes),
    canonicalObjectDigest: digestCanonical0(read.value),
    reverseLookupOnly: true,
    notCryptographicInversion: true,
    resolvedFromKnownIndex: true,
  };

  return {
    ...makeAcceptRecord({
      checker,
      nf,
      ledger,
    }),
    FileBytes: cfg.includeBytes ? read.text : null,
    CanonicalBytes: cfg.includeBytes ? canonicalBytes : null,
    ParsedObject: cfg.includeBytes ? read.value : null,
    fileBytes: cfg.includeBytes ? read.text : null,
    canonicalBytes: cfg.includeBytes ? canonicalBytes : null,
    parsedObject: cfg.includeBytes ? read.value : null,
  };
}

function validateResolverConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedDigestResolverConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedDigestResolverConfig0') {
    return validationReject0(['kind'], 'MaterializedDigestResolverConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedDigestResolverConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  if (typeof config.fixtureDir !== 'string' || config.fixtureDir.length === 0) {
    return validationReject0(['fixtureDir'], 'MaterializedDigestResolverConfig0 fixtureDir must be a non-empty string', {
      actual: config.fixtureDir,
    });
  }

  if (!Array.isArray(config.filenames) || config.filenames.length === 0) {
    return validationReject0(['filenames'], 'MaterializedDigestResolverConfig0 filenames must be a non-empty array', {
      actual: config.filenames,
    });
  }

  for (let index = 0; index < config.filenames.length; index += 1) {
    if (typeof config.filenames[index] !== 'string' || config.filenames[index].length === 0) {
      return validationReject0(['filenames', index], 'materialized fixture filename must be a non-empty string', {
        actual: config.filenames[index],
      });
    }
  }

  for (const field of [
    'verify',
    'includeBytes',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedDigestResolverConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedDigestResolverConfig0NF',
  });
}

function normalizeDigestInput0(input) {
  const hex = typeof input === 'string'
    ? input
    : (
        isPlainObject(input)
          ? input.hex ?? input.digest ?? input.sha256
          : null
      );

  if (typeof hex !== 'string' || !/^[0-9a-f]{64}$/.test(hex)) {
    return validationReject0(['digest'], 'digest must be a lowercase SHA256 hex string or digest record', {
      actual: input,
    });
  }

  return {
    ok: true,
    hex,
    nf: {
      kind: 'MaterializedDigestInput0NF',
      hex,
    },
  };
}

async function readFixtureFile0(filePath, filename) {
  let text;

  try {
    text = await fs.readFile(filePath, 'utf8');
  } catch (error) {
    return validationReject0(['files', filename], 'materialized fixture file must be readable', {
      filePath,
      error: error.message,
    });
  }

  let value;

  try {
    value = JSON.parse(text);
  } catch (error) {
    return validationReject0(['files', filename], 'materialized fixture file must parse as JSON', {
      filePath,
      error: error.message,
    });
  }

  return {
    ok: true,
    text,
    value,
    nf: {
      kind: 'MaterializedFixtureFileRead0NF',
      filename,
      filePath,
      byteLength: Buffer.byteLength(text, 'utf8'),
      fileBytesSha256: sha256Utf8DigestRecord0(text),
      canonicalObjectDigest: digestCanonical0(value),
    },
  };
}

async function verifyFixtureFile0(filePath, filename) {
  let record;

  if (filename === MATERIALIZED_FIXTURE_FILENAMES0.pack) {
    record = await CheckMaterializedAggregateFile0(filePath);
  } else if (
    filename === MATERIALIZED_FIXTURE_FILENAMES0.pendingBridge ||
    filename === MATERIALIZED_FIXTURE_FILENAMES0.acceptedBridge
  ) {
    record = await CheckMaterializedAcceptanceBridgeFile0(filePath);
  } else {
    return validationReject0(['files', filename], 'unknown materialized fixture filename cannot be verified', {
      filename,
    });
  }

  if (isRejectRecord0(record)) {
    return validationReject0(['files', filename], 'materialized fixture file failed checker verification', {
      filename,
      inner: compactReject0(record),
    });
  }

  return validationAccept0({
    kind: 'MaterializedFixtureFileVerification0NF',
    filename,
    checker: record.checker,
    digest: record.Digest ?? record.digest,
  });
}

function makeIndexEntry0({
  filename,
  filePath,
  fileBytes,
  parsed,
}) {
  const canonicalBytes = stableStringify0(parsed);

  return {
    filename,
    filePath,
    kind: parsed.kind ?? null,
    byteLength: Buffer.byteLength(fileBytes, 'utf8'),
    canonicalByteLength: Buffer.byteLength(canonicalBytes, 'utf8'),
    fileBytesSha256: sha256Utf8DigestRecord0(fileBytes),
    canonicalBytesSha256: sha256Utf8DigestRecord0(canonicalBytes),
    canonicalObjectDigest: digestCanonical0(parsed),
    digests: [
      {
        digestKind: 'fileBytesSha256',
        digest: sha256Utf8DigestRecord0(fileBytes),
      },
      {
        digestKind: 'canonicalBytesSha256',
        digest: sha256Utf8DigestRecord0(canonicalBytes),
      },
      {
        digestKind: 'canonicalObjectDigest',
        digest: digestCanonical0(parsed),
      },
    ],
  };
}

function summarizeIndexEntry0(entry) {
  return {
    filename: entry.filename,
    filePath: entry.filePath,
    kind: entry.kind,
    byteLength: entry.byteLength,
    canonicalByteLength: entry.canonicalByteLength,
    fileBytesSha256: entry.fileBytesSha256,
    canonicalBytesSha256: entry.canonicalBytesSha256,
    canonicalObjectDigest: entry.canonicalObjectDigest,
  };
}

function buildDigestLookup0(entries) {
  const lookup = {};

  for (const entry of entries) {
    for (const digestEntry of entry.digests) {
      const hex = digestEntry.digest.hex;

      lookup[hex] ??= [];
      lookup[hex].push({
        filename: entry.filename,
        filePath: entry.filePath,
        digestKind: digestEntry.digestKind,
      });
    }
  }

  return lookup;
}

function findAmbiguousDigest0(lookup) {
  for (const [digest, entries] of Object.entries(lookup)) {
    const files = new Set(entries.map((entry) => entry.filePath));

    if (files.size > 1) {
      return {
        digest,
        entries,
      };
    }
  }

  return null;
}

function resolveMatches0(indexEntries, hex) {
  const matches = [];

  for (const entry of indexEntries) {
    const matchedDigestKinds = entry.digests
      .filter((digestEntry) => digestEntry.digest.hex === hex)
      .map((digestEntry) => digestEntry.digestKind);

    if (matchedDigestKinds.length > 0) {
      matches.push({
        entry,
        matchedDigestKinds,
      });
    }
  }

  if (matches.length === 0) {
    return validationReject0(['digest'], 'digest was not found in the materialized fixture digest index', {
      digest: hex,
      reverseLookupOnly: true,
      notCryptographicInversion: true,
    });
  }

  const files = new Set(matches.map((match) => match.entry.filePath));

  if (files.size > 1) {
    return validationReject0(['digest'], 'digest resolves to multiple fixture files and is ambiguous', {
      digest: hex,
      matches: matches.map((match) => ({
        filename: match.entry.filename,
        filePath: match.entry.filePath,
        matchedDigestKinds: match.matchedDigestKinds,
      })),
    });
  }

  const match = matches[0];

  return {
    ok: true,
    entry: match.entry,
    matchedDigestKinds: match.matchedDigestKinds,
    nf: {
      kind: 'MaterializedDigestResolutionMatch0NF',
      filename: match.entry.filename,
      filePath: match.entry.filePath,
      matchedDigestKinds: match.matchedDigestKinds,
    },
  };
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