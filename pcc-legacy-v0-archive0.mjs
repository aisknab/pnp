#!/usr/bin/env node

import { execFile as execFileCallback } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';

const execFile = promisify(execFileCallback);

const CHECKER = 'CheckLegacyV0Archive0';
const VERSION = 0;
const ARCHIVE_PATH = 'archive/legacy-v0/ARCHIVE.json';
const COORDINATE = 'PNP-LEGACY-V0-ARCHIVE-2026-07-10-01';
const BUNDLE_PATH = 'proof-artifacts/final-pnp-proof-report-hardened-7072f8d';

const SOURCE_TAG0 = {
  name: 'final-pnp-proof-report-hardened-7072f8d',
  object: '9b69c4f8d8d6d62eb359af759288e5794d1c81c2',
  commit: '7072f8d0bda6d44d240f9bb3fad624fd357e1278',
  tree: '2b673c397c8438a0631952c2d0325456e96c5341',
  annotated: true,
  signed: false,
};

const ARTIFACT_TAG0 = {
  name: 'final-pnp-proof-report-artifacts-hardened-7072f8d-sealed',
  object: 'e7ea459c907ed9e334af8c0bd5f3bb117348992d',
  commit: '9d1de19f827e5cb6880741352eb2349cbbb45994',
  tree: 'fa34921ab6279b2258436b325326d32bfb40fd36',
  annotated: true,
  signed: false,
};

const DOCUMENT_TAG0 = {
  name: 'final-pnp-proof-report-docs-hardened-7072f8d-sealed',
  object: '9eeb4b85af1c04c43e6f086debcd3ac37d5d27d1',
  commit: '3ba356c79b545d2c734283bf10d85d0710de2b60',
  tree: '4f0c3b5d93da1783be1c24560dac3bf4023370f8',
  annotated: true,
  signed: false,
};

const SOURCE_FILES0 = [
  {
    path: 'package.json',
    sha256: 'e3da897862cb99de2deedb29cb5d7362b8db15760de6bef235a1a6485a6201d3',
  },
  {
    path: 'package-lock.json',
    sha256: 'd33eae7a5ae1b2589db9ab7658b8bc21c4134b63db63206cfbf6a7ca55ef9599',
  },
];

const ARTIFACT_FILES0 = [
  {
    path: `${BUNDLE_PATH}/SHA256SUMS`,
    sha256: 'd1da103bbf2867b656e8026b734f81b33bc61deb79dbf3a2d48a16f83e8a2356',
  },
  {
    path: `${BUNDLE_PATH}/SHA256SUMS.sha256`,
    sha256: '61228d99a2ce57dde4e9fa605626277ad3cb591ff424f73c8c240e28e8a876fa',
  },
  {
    path: `${BUNDLE_PATH}/final-pnp-proof-report.summary.json`,
    sha256: '70f7baf244f759e309ae848584286e5ca6e9a3704df630dacc17529e5fdb3491',
  },
  {
    path: `${BUNDLE_PATH}/final-pnp-proof-report.full.json`,
    sha256: '90989c03e5da774822b400896b880bc293b5b300f0f4b08e5de352773451263e',
  },
  {
    path: `${BUNDLE_PATH}/release-seal.json`,
    sha256: '03a95ff0baeb5b251577780ecbce51e9b305fb611daddee4db9b05f2621d6bc7',
  },
  {
    path: `${BUNDLE_PATH}/validation-summary.json`,
    sha256: 'cebcc69ec0ed846f2cea42558d1e458f649e4cd473e1cab8d42c54516722518d',
  },
];

const DOCUMENT_FILES0 = [
  {
    path: 'canonical_proof_report.pdf',
    sha256: 'a46c501e305e0889a95fc66c99229fd016698ca4474edcac43c389709e885ca4',
  },
  {
    path: 'canonical_proof_report.tex',
    sha256: '85a7ef5230ba74ad7d52a0789da4e43a70c15f32b3bd6d9f9ee140c0a2e31474',
  },
];

const CLAIM_BOUNDARY0 = {
  historicalReplay: true,
  currentStatusAuthority: false,
  mathematicalTheoremEstablished: false,
  checkerReplayIsMathematicalProof: false,
  publicTheoremEmissionAllowed: false,
  finalTheoremReady: false,
};

const EXPECTED_ARCHIVE0 = {
  kind: 'PNPLegacyV0Archive0',
  version: VERSION,
  coordinate: COORDINATE,
  status: 'historical-checker-archive',
  archiveId: 'legacy-v0-7072f8d',
  source: {
    packageVersion: '0.1.0',
    tag: SOURCE_TAG0,
    files: SOURCE_FILES0,
  },
  artifacts: {
    tag: ARTIFACT_TAG0,
    bundlePath: BUNDLE_PATH,
    files: ARTIFACT_FILES0,
  },
  documents: {
    tag: DOCUMENT_TAG0,
    files: DOCUMENT_FILES0,
  },
  historicalValidation: {
    command: 'npm run validate',
    tests: 1121,
    pass: 1121,
    fail: 0,
    cancelled: 0,
    skipped: 0,
    todo: 0,
    recordedIn: `${BUNDLE_PATH}/release-seal.json`,
    recordedNotReexecutedByArchiveCheck: true,
  },
  replay: {
    command: 'npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d',
    fullCommand: 'npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d --full',
    outputMustBeOutsideCheckout: true,
    refuseExistingOutput: true,
  },
  claimBoundary: CLAIM_BOUNDARY0,
  provenanceLimitations: [
    'The three annotated Git tags are unsigned; these pins establish Git object identity, not signed provenance.',
    'The archive does not add missing pins for Node.js/npm patch levels, operating system, CPU, or filesystem semantics.',
    'Historical checker acceptance is not a mathematical proof and carries no current theorem authority.',
  ],
};

export const LEGACY_V0_ARCHIVE_PINS0 = deepFreeze0({
  coordinate: COORDINATE,
  archiveId: EXPECTED_ARCHIVE0.archiveId,
  source: {
    packageVersion: EXPECTED_ARCHIVE0.source.packageVersion,
    tag: SOURCE_TAG0,
    files: SOURCE_FILES0,
  },
  artifacts: {
    tag: ARTIFACT_TAG0,
    bundlePath: BUNDLE_PATH,
    files: ARTIFACT_FILES0,
  },
  documents: {
    tag: DOCUMENT_TAG0,
    files: DOCUMENT_FILES0,
  },
});

export async function CheckLegacyV0Archive0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());

  const forbiddenOverrides = [
    'manifestOverride',
    'tagIdentityOverrides',
    'fileBytesOverrides',
  ].filter((field) => Object.hasOwn(options, field));
  if (forbiddenOverrides.length !== 0) {
    return reject0(
      'LegacyV0Archive.TestOverrideForbidden',
      forbiddenOverrides,
      'production archive verification does not accept injected manifests, tag identities, or file bytes',
    );
  }

  try {
    const archiveRead = await readArchive0(root);
    if (archiveRead.tag === 'reject') return archiveRead;

    const manifestCheck = compareExact0(archiveRead.archive, EXPECTED_ARCHIVE0, []);
    if (manifestCheck.tag === 'reject') return manifestCheck;

    const tagChecks = [];
    for (const expectedTag of [SOURCE_TAG0, ARTIFACT_TAG0, DOCUMENT_TAG0]) {
      const actualTag = await readTagIdentity0(root, expectedTag.name);
      const tagCheck = compareTagIdentity0(actualTag, expectedTag);
      if (tagCheck.tag === 'reject') return tagCheck;
      tagChecks.push(tagCheck);
    }

    const verifiedFiles = new Map();
    for (const [commit, files] of [
      [SOURCE_TAG0.commit, SOURCE_FILES0],
      [ARTIFACT_TAG0.commit, ARTIFACT_FILES0],
      [DOCUMENT_TAG0.commit, DOCUMENT_FILES0],
    ]) {
      for (const file of files) {
        const bytes = await readGitFile0(root, commit, file.path);
        const actualSha256 = sha256Hex0(bytes);
        if (actualSha256 !== file.sha256) {
          return reject0('LegacyV0Archive.FileDigest', [commit, file.path], 'archived file digest mismatch', {
            expectedSha256: file.sha256,
            actualSha256,
          });
        }
        verifiedFiles.set(`${commit}:${file.path}`, bytes);
      }
    }

    const packageCheck = validatePackageVersion0(
      verifiedFiles.get(`${SOURCE_TAG0.commit}:package.json`),
      EXPECTED_ARCHIVE0.source.packageVersion,
    );
    if (packageCheck.tag === 'reject') return packageCheck;

    const ledgerCheck = validateArtifactLedger0(verifiedFiles);
    if (ledgerCheck.tag === 'reject') return ledgerCheck;

    const validationCheck = validateHistoricalValidation0(verifiedFiles);
    if (validationCheck.tag === 'reject') return validationCheck;

    return {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORDINATE,
      archiveId: EXPECTED_ARCHIVE0.archiveId,
      claimStatus: 'historical-checker-archive-integrity-verified',
      archiveManifestAccepted: true,
      tagObjectIdentityVerified: true,
      archivedFileDigestsVerified: true,
      artifactChecksumLedgerVerified: true,
      verifiedTagCount: tagChecks.length,
      verifiedFileCount: verifiedFiles.size,
      tagsAnnotated: true,
      tagsSigned: false,
      signedProvenanceEstablished: false,
      historicalValidationRecorded: true,
      historicalValidationReexecuted: false,
      ...CLAIM_BOUNDARY0,
    };
  } catch (error) {
    return reject0(
      'LegacyV0Archive.UnhandledException',
      [],
      'legacy-v0 archive checker failed closed',
      normalizeError0(error),
    );
  }
}

async function readArchive0(root) {
  try {
    const text = await readFile(path.join(root, ARCHIVE_PATH), 'utf8');
    return { tag: 'accept', archive: JSON.parse(text) };
  } catch (error) {
    return reject0('LegacyV0Archive.ReadOrParse', [ARCHIVE_PATH], 'could not read or parse archive manifest', normalizeError0(error));
  }
}

async function readTagIdentity0(root, tagName) {
  const ref = `refs/tags/${tagName}`;
  const [type, object, commit, tree, payload] = await Promise.all([
    gitText0(root, ['cat-file', '-t', ref]),
    gitText0(root, ['rev-parse', '--verify', ref]),
    gitText0(root, ['rev-parse', '--verify', `${ref}^{commit}`]),
    gitText0(root, ['rev-parse', '--verify', `${ref}^{commit}^{tree}`]),
    gitBytes0(root, ['cat-file', '-p', ref]),
  ]);

  const payloadText = payload.toString('utf8');
  return {
    name: tagName,
    object,
    commit,
    tree,
    annotated: type === 'tag',
    signed: /-----BEGIN (?:PGP|SSH|X509) SIGNATURE-----/u.test(payloadText),
  };
}

function compareTagIdentity0(actual, expected) {
  if (!isPlainObject0(actual)) {
    return reject0('LegacyV0Archive.TagShape', [expected.name], 'resolved tag identity must be an object');
  }
  for (const field of ['name', 'object', 'commit', 'tree', 'annotated', 'signed']) {
    if (actual[field] !== expected[field]) {
      return reject0('LegacyV0Archive.TagIdentity', [expected.name, field], 'annotated tag identity mismatch', {
        expected: expected[field],
        actual: actual[field] ?? null,
      });
    }
  }
  return { tag: 'accept', name: expected.name };
}

async function readGitFile0(root, commit, filePath) {
  const key = `${commit}:${filePath}`;
  return gitBytes0(root, ['show', key]);
}

function validatePackageVersion0(bytes, expectedVersion) {
  try {
    const packageJson = JSON.parse(bytes.toString('utf8'));
    if (packageJson.version !== expectedVersion) {
      return reject0('LegacyV0Archive.PackageVersion', ['source', 'packageVersion'], 'archived package version mismatch', {
        expected: expectedVersion,
        actual: packageJson.version ?? null,
      });
    }
    return { tag: 'accept' };
  } catch (error) {
    return reject0('LegacyV0Archive.PackageJson', ['source', 'files', 'package.json'], 'archived package.json could not be parsed', normalizeError0(error));
  }
}

function validateArtifactLedger0(verifiedFiles) {
  const ledgerPath = `${BUNDLE_PATH}/SHA256SUMS`;
  const detachedPath = `${BUNDLE_PATH}/SHA256SUMS.sha256`;
  const ledgerBytes = verifiedFiles.get(`${ARTIFACT_TAG0.commit}:${ledgerPath}`);
  const detachedBytes = verifiedFiles.get(`${ARTIFACT_TAG0.commit}:${detachedPath}`);
  const entries = parseSha256Sums0(ledgerBytes.toString('utf8'));
  if (entries.tag === 'reject') return entries;

  for (const file of ARTIFACT_FILES0.slice(2)) {
    const actual = entries.map.get(file.path);
    if (actual !== file.sha256) {
      return reject0('LegacyV0Archive.ChecksumLedgerEntry', [ledgerPath, file.path], 'sealed checksum ledger entry mismatch', {
        expectedSha256: file.sha256,
        actualSha256: actual ?? null,
      });
    }
  }

  const expectedDetached = `${ARTIFACT_FILES0[0].sha256}  ${ledgerPath}\n`;
  if (detachedBytes.toString('utf8') !== expectedDetached) {
    return reject0('LegacyV0Archive.DetachedLedger', [detachedPath], 'detached SHA256SUMS hash record mismatch');
  }
  return { tag: 'accept' };
}

function parseSha256Sums0(text) {
  const map = new Map();
  const lines = text.split(/\r?\n/u).filter((line) => line.length !== 0);
  if (lines.length === 0) {
    return reject0('LegacyV0Archive.EmptyChecksumLedger', [`${BUNDLE_PATH}/SHA256SUMS`], 'sealed checksum ledger must not be empty');
  }
  for (let index = 0; index < lines.length; index += 1) {
    const match = lines[index].match(/^([0-9a-f]{64})  ([^\\]+)$/u);
    if (!match) {
      return reject0('LegacyV0Archive.BadChecksumLine', [`${BUNDLE_PATH}/SHA256SUMS`, index + 1], 'malformed checksum ledger line');
    }
    const [, digest, filePath] = match;
    if (path.isAbsolute(filePath) || filePath.split('/').includes('..') || map.has(filePath)) {
      return reject0('LegacyV0Archive.BadChecksumPath', [`${BUNDLE_PATH}/SHA256SUMS`, index + 1], 'unsafe or duplicate checksum path', { filePath });
    }
    map.set(filePath, digest);
  }
  return { tag: 'accept', map };
}

function validateHistoricalValidation0(verifiedFiles) {
  const sealPath = `${BUNDLE_PATH}/release-seal.json`;
  const summaryPath = `${BUNDLE_PATH}/validation-summary.json`;
  try {
    const seal = JSON.parse(verifiedFiles.get(`${ARTIFACT_TAG0.commit}:${sealPath}`).toString('utf8'));
    const summary = JSON.parse(verifiedFiles.get(`${ARTIFACT_TAG0.commit}:${summaryPath}`).toString('utf8'));
    const expected = EXPECTED_ARCHIVE0.historicalValidation;
    for (const field of ['tests', 'pass', 'fail', 'cancelled', 'skipped', 'todo']) {
      if (seal.validation?.[field] !== expected[field] || summary[field] !== expected[field]) {
        return reject0('LegacyV0Archive.HistoricalValidation', ['historicalValidation', field], 'sealed historical validation count mismatch', {
          expected: expected[field],
          seal: seal.validation?.[field] ?? null,
          summary: summary[field] ?? null,
        });
      }
    }
    if (
      seal.sourceCommit !== SOURCE_TAG0.commit ||
      seal.sourceTag !== SOURCE_TAG0.name ||
      seal.sealedArtifactTag !== ARTIFACT_TAG0.name ||
      seal.bundlePath !== BUNDLE_PATH
    ) {
      return reject0('LegacyV0Archive.ReleaseSealIdentity', [sealPath], 'release seal does not bind the pinned source, artifact tag, and bundle');
    }
    return { tag: 'accept' };
  } catch (error) {
    return reject0('LegacyV0Archive.ReleaseSealParse', [sealPath], 'sealed validation metadata could not be parsed', normalizeError0(error));
  }
}

function compareExact0(actual, expected, pathArray) {
  if (Array.isArray(expected)) {
    if (!Array.isArray(actual) || actual.length !== expected.length) {
      return reject0('LegacyV0Archive.ManifestShape', pathArray, 'archive manifest array shape mismatch', {
        expectedLength: expected.length,
        actualLength: Array.isArray(actual) ? actual.length : null,
      });
    }
    for (let index = 0; index < expected.length; index += 1) {
      const result = compareExact0(actual[index], expected[index], [...pathArray, index]);
      if (result.tag === 'reject') return result;
    }
    return { tag: 'accept' };
  }

  if (isPlainObject0(expected)) {
    if (!isPlainObject0(actual)) {
      return reject0('LegacyV0Archive.ManifestShape', pathArray, 'archive manifest object shape mismatch');
    }
    const expectedKeys = Object.keys(expected).sort();
    const actualKeys = Object.keys(actual).sort();
    if (!sameArray0(actualKeys, expectedKeys)) {
      return reject0('LegacyV0Archive.ManifestKeys', pathArray, 'archive manifest keys mismatch', {
        expected: expectedKeys,
        actual: actualKeys,
      });
    }
    for (const key of expectedKeys) {
      const result = compareExact0(actual[key], expected[key], [...pathArray, key]);
      if (result.tag === 'reject') return result;
    }
    return { tag: 'accept' };
  }

  if (!Object.is(actual, expected)) {
    return reject0('LegacyV0Archive.ManifestField', pathArray, 'archive manifest field differs from the pinned value', {
      expected,
      actual: actual ?? null,
    });
  }
  return { tag: 'accept' };
}

async function gitBytes0(root, args) {
  const { stdout } = await execFile('git', args, {
    cwd: root,
    encoding: 'buffer',
    maxBuffer: 16 * 1024 * 1024,
    windowsHide: true,
  });
  return Buffer.isBuffer(stdout) ? stdout : Buffer.from(stdout);
}

async function gitText0(root, args) {
  return (await gitBytes0(root, args)).toString('utf8').trim();
}

function sha256Hex0(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function reject0(coord, pathArray, reason, witness = {}) {
  return {
    tag: 'reject',
    kind: 'reject',
    checker: CHECKER,
    version: VERSION,
    coord,
    path: pathArray,
    witness: { reason, ...witness },
    ...CLAIM_BOUNDARY0,
  };
}

function normalizeError0(error) {
  if (error instanceof Error) {
    return {
      errorName: error.name,
      errorMessage: error.message,
      errorCode: typeof error.code === 'string' ? error.code : null,
    };
  }
  return { errorName: 'UnknownError', errorMessage: String(error), errorCode: null };
}

function isPlainObject0(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function sameArray0(left, right) {
  return left.length === right.length && left.every((value, index) => value === right[index]);
}

function deepFreeze0(value) {
  if (value !== null && typeof value === 'object' && !Object.isFrozen(value)) {
    Object.freeze(value);
    for (const child of Object.values(value)) deepFreeze0(child);
  }
  return value;
}

async function main0() {
  const args = process.argv.slice(2);
  if (args.some((arg) => arg !== '--json' && arg !== '--no-write')) {
    process.stderr.write('usage: node pcc-legacy-v0-archive0.mjs [--json] [--no-write]\n');
    process.exitCode = 2;
    return;
  }
  const verdict = await CheckLegacyV0Archive0();
  process.stdout.write(`${JSON.stringify(verdict, null, 2)}\n`);
  if (verdict.tag !== 'accept') process.exitCode = 1;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  await main0();
}
