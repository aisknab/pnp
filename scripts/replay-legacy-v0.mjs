#!/usr/bin/env node

import { createHash } from 'node:crypto';
import {
  closeSync,
  existsSync,
  lstatSync,
  mkdirSync,
  mkdtempSync,
  openSync,
  readFileSync,
  realpathSync,
  rmSync,
  statSync,
  writeFileSync,
} from 'node:fs';
import { spawnSync } from 'node:child_process';
import os from 'node:os';
import path from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';

const DEFAULT_MANIFEST_PATH = 'archive/legacy-v0/ARCHIVE.json';
const ARCHIVE_COORDINATE = 'PNP-LEGACY-V0-ARCHIVE-2026-07-10-01';
const BUNDLE_PATH = 'proof-artifacts/final-pnp-proof-report-hardened-7072f8d';

export const LEGACY_V0_REPLAY_PINS0 = Object.freeze({
  source: Object.freeze({
    name: 'final-pnp-proof-report-hardened-7072f8d',
    object: '9b69c4f8d8d6d62eb359af759288e5794d1c81c2',
    commit: '7072f8d0bda6d44d240f9bb3fad624fd357e1278',
    tree: '2b673c397c8438a0631952c2d0325456e96c5341',
  }),
  artifacts: Object.freeze({
    name: 'final-pnp-proof-report-artifacts-hardened-7072f8d-sealed',
    object: 'e7ea459c907ed9e334af8c0bd5f3bb117348992d',
    commit: '9d1de19f827e5cb6880741352eb2349cbbb45994',
    tree: 'fa34921ab6279b2258436b325326d32bfb40fd36',
  }),
  documents: Object.freeze({
    name: 'final-pnp-proof-report-docs-hardened-7072f8d-sealed',
    object: '9eeb4b85af1c04c43e6f086debcd3ac37d5d27d1',
    commit: '3ba356c79b545d2c734283bf10d85d0710de2b60',
    tree: '4f0c3b5d93da1783be1c24560dac3bf4023370f8',
  }),
});

export const LEGACY_V0_ARCHIVE_FILE_PINS0 = Object.freeze({
  source: Object.freeze([
    Object.freeze({ path: 'package.json', sha256: 'e3da897862cb99de2deedb29cb5d7362b8db15760de6bef235a1a6485a6201d3' }),
    Object.freeze({ path: 'package-lock.json', sha256: 'd33eae7a5ae1b2589db9ab7658b8bc21c4134b63db63206cfbf6a7ca55ef9599' }),
  ]),
  artifacts: Object.freeze([
    Object.freeze({ path: `${BUNDLE_PATH}/SHA256SUMS`, sha256: 'd1da103bbf2867b656e8026b734f81b33bc61deb79dbf3a2d48a16f83e8a2356' }),
    Object.freeze({ path: `${BUNDLE_PATH}/SHA256SUMS.sha256`, sha256: '61228d99a2ce57dde4e9fa605626277ad3cb591ff424f73c8c240e28e8a876fa' }),
    Object.freeze({ path: `${BUNDLE_PATH}/final-pnp-proof-report.summary.json`, sha256: '70f7baf244f759e309ae848584286e5ca6e9a3704df630dacc17529e5fdb3491' }),
    Object.freeze({ path: `${BUNDLE_PATH}/final-pnp-proof-report.full.json`, sha256: '90989c03e5da774822b400896b880bc293b5b300f0f4b08e5de352773451263e' }),
    Object.freeze({ path: `${BUNDLE_PATH}/release-seal.json`, sha256: '03a95ff0baeb5b251577780ecbce51e9b305fb611daddee4db9b05f2621d6bc7' }),
    Object.freeze({ path: `${BUNDLE_PATH}/validation-summary.json`, sha256: 'cebcc69ec0ed846f2cea42558d1e458f649e4cd473e1cab8d42c54516722518d' }),
  ]),
  documents: Object.freeze([
    Object.freeze({ path: 'canonical_proof_report.pdf', sha256: 'a46c501e305e0889a95fc66c99229fd016698ca4474edcac43c389709e885ca4' }),
    Object.freeze({ path: 'canonical_proof_report.tex', sha256: '85a7ef5230ba74ad7d52a0789da4e43a70c15f32b3bd6d9f9ee140c0a2e31474' }),
  ]),
});

export const LEGACY_V0_SMOKE_TESTS0 = Object.freeze([
  'test/pcc-gpack0.test.mjs',
  'test/pcc-global-proof-dag0.test.mjs',
  'test/pcc-final-framework0.test.mjs',
  'test/pcc-final0.test.mjs',
  'test/pcc-final-integration-materialized0.test.mjs',
  'test/pcc-final-integration-concrete-materialized0.test.mjs',
  'test/pcc-pack-concrete-materialized0.test.mjs',
  'test/pcc-check-pcc-pack-exp0.test.mjs',
  'test/pcc-integrated-pipeline0.test.mjs',
  'test/pcc-runall0.test.mjs',
]);

export const LEGACY_V0_CLAIM_CRITICAL_PATHS0 = Object.freeze([
  'tag',
  'checker',
  'finalPNPProofReportAccepted',
  'status',
  'theorem.statement',
  'theorem.antecedent',
  'theorem.consequent',
  'theorem.conditional',
  'claimBoundary',
  'finalPNPReleaseGateAccepted',
  'finalPNPCertificateAccepted',
  'releaseAuditAccepted',
  'finalAcceptanceReplayClosed',
  'verdict',
  'generator',
  'checkerName',
  'generatorIsGeneratePCCPack',
  'checkPCCPackexpAccepted',
  'checkAcceptRunAccepted',
  'replayAccepted',
  'finalVerdictAccepted',
  'publicConclusionAntecedent',
  'publicConclusionConsequent',
  'publicConclusionConditional',
  'publicConclusionStatement',
]);

const CLAIM_BOUNDARY0 = Object.freeze({
  historicalReplay: true,
  currentStatusAuthority: false,
  mathematicalTheoremEstablished: false,
  checkerReplayIsMathematicalProof: false,
  publicTheoremEmissionAllowed: false,
  finalTheoremReady: false,
});

export class LegacyV0ReplayError0 extends Error {
  constructor(code, message, detail = undefined) {
    super(message);
    this.name = 'LegacyV0ReplayError0';
    this.code = code;
    this.detail = detail;
  }
}

export function parseLegacyV0ReplayArgs0(argv) {
  const out = {
    root: process.cwd(),
    output: null,
    full: false,
    dryRun: false,
    help: false,
  };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--output') out.output = requireValue0(argv, ++index, '--output');
    else if (arg === '--root') out.root = requireValue0(argv, ++index, '--root');
    else if (arg === '--full') out.full = true;
    else if (arg === '--dry-run') out.dryRun = true;
    else if (arg === '--help' || arg === '-h') out.help = true;
    else throw new LegacyV0ReplayError0('Replay.BadArgument', `unknown argument: ${arg}`);
  }
  if (!out.help && out.output === null) {
    throw new LegacyV0ReplayError0('Replay.OutputRequired', '--output <path> is required');
  }
  return out;
}

export function validateLegacyV0OutputPath0(root, output) {
  if (typeof output !== 'string' || output.trim() === '') {
    throw new LegacyV0ReplayError0('Replay.OutputRequired', '--output must be a non-empty path');
  }
  const checkout = resolveGitTopLevel0(root);
  const requested = path.resolve(output);
  if (lexists0(requested)) {
    throw new LegacyV0ReplayError0(
      'Replay.OutputExists',
      `refusing to overwrite existing output: ${requested}`,
      { output: requested },
    );
  }
  const candidate = canonicalProspectivePath0(requested);
  if (inside0(checkout, candidate)) {
    throw new LegacyV0ReplayError0(
      'Replay.OutputInsideCheckout',
      'replay output must be outside the active checkout',
      { checkout, output: candidate },
    );
  }
  return { checkout, output: candidate };
}

export function loadLegacyV0ArchiveManifest0(root, override = undefined) {
  let manifest;
  if (override !== undefined) manifest = override;
  else {
    const manifestPath = path.join(root, DEFAULT_MANIFEST_PATH);
    try {
      manifest = JSON.parse(readFileSync(manifestPath, 'utf8'));
    } catch (error) {
      throw new LegacyV0ReplayError0(
        'Replay.ManifestReadFailed',
        `could not read ${DEFAULT_MANIFEST_PATH}`,
        normalizeError0(error),
      );
    }
  }
  validateArchiveManifest0(manifest);
  return manifest;
}

export function verifyLegacyV0TagPins0(root) {
  const verified = {};
  for (const [role, pin] of Object.entries(LEGACY_V0_REPLAY_PINS0)) {
    const ref = `refs/tags/${pin.name}`;
    const objectType = git0(root, ['cat-file', '-t', ref]);
    const object = git0(root, ['rev-parse', ref]);
    const commit = git0(root, ['rev-parse', `${ref}^{commit}`]);
    const tree = git0(root, ['rev-parse', `${ref}^{tree}`]);
    const tagBody = git0(root, ['cat-file', '-p', ref], { trim: false });
    const signed = /-----BEGIN (?:PGP|SSH) SIGNATURE-----/.test(tagBody);
    const header = parseAnnotatedTagHeader0(tagBody);
    assertEqual0(objectType, 'tag', 'Replay.TagNotAnnotated', `${pin.name} must be an annotated tag`);
    assertEqual0(object, pin.object, 'Replay.TagObjectMismatch', `${pin.name} tag object mismatch`);
    assertEqual0(commit, pin.commit, 'Replay.TagCommitMismatch', `${pin.name} peeled commit mismatch`);
    assertEqual0(tree, pin.tree, 'Replay.TagTreeMismatch', `${pin.name} tree mismatch`);
    assertEqual0(header.object, pin.commit, 'Replay.TagHeaderObjectMismatch', `${pin.name} tag header object mismatch`);
    assertEqual0(header.type, 'commit', 'Replay.TagHeaderTypeMismatch', `${pin.name} must tag a commit`);
    assertEqual0(header.tag, pin.name, 'Replay.TagHeaderNameMismatch', `${pin.name} tag header name mismatch`);
    if (signed) {
      throw new LegacyV0ReplayError0(
        'Replay.UnexpectedTagSignature',
        `${pin.name} is pinned as an unsigned annotated tag`,
      );
    }
    verified[role] = {
      tag: pin.name,
      object,
      commit,
      tree,
      annotated: true,
      signed: false,
    };
  }
  return verified;
}

export function buildLegacyV0ReplayPlan0({ full = false } = {}) {
  const validation = full
    ? { mode: 'full', command: ['npm', 'run', 'validate'] }
    : { mode: 'hardened-smoke', command: ['node', '--test', ...LEGACY_V0_SMOKE_TESTS0] };
  return {
    kind: 'PNPLegacyV0ReplayPlan0',
    version: 0,
    archiveId: 'legacy-v0-7072f8d',
    ...CLAIM_BOUNDARY0,
    mode: validation.mode,
    pins: clonePins0(),
    steps: [
      { id: 'verify-manifest', action: `verify ${DEFAULT_MANIFEST_PATH} against compiled pins` },
      { id: 'verify-tags', action: 'verify annotated tag objects, peeled commits, and trees' },
      { id: 'checkout', command: ['git', 'worktree', 'add', '--detach', '$WORKTREE', '$PINNED_COMMIT'], count: 3 },
      { id: 'verify-files', action: 'verify manifest file digests and sealed SHA256SUMS ledgers' },
      { id: 'install', cwd: '$SOURCE_WORKTREE', command: ['npm', 'ci', '--ignore-scripts'] },
      { id: 'validate', cwd: '$SOURCE_WORKTREE', ...validation },
      {
        id: 'regenerate-compact',
        cwd: '$SOURCE_WORKTREE',
        command: ['node', './bin/write-final-pnp-proof-report0.mjs', '$OUTPUT/compact'],
      },
      { id: 'compare', action: 'compare regenerated and sealed claim-critical fields' },
      { id: 'transcript', action: 'write replay-transcript.json with non-authoritative claim boundary' },
    ],
  };
}

export function compareClaimCriticalFields0(expected, actual) {
  const compared = {};
  for (const fieldPath of LEGACY_V0_CLAIM_CRITICAL_PATHS0) {
    const expectedValue = getPath0(expected, fieldPath);
    const actualValue = getPath0(actual, fieldPath);
    if (stableStringify0(expectedValue) !== stableStringify0(actualValue)) {
      throw new LegacyV0ReplayError0(
        'Replay.ClaimCriticalMismatch',
        `regenerated claim-critical field mismatch: ${fieldPath}`,
        { path: fieldPath, expected: expectedValue, actual: actualValue },
      );
    }
    compared[fieldPath] = actualValue;
  }
  return compared;
}

export function verifyChecksumLedger0(root, ledgerRelativePath, options = {}) {
  const ledgerFile = confinedRegularFile0(root, ledgerRelativePath, 'Replay.UnsafeLedgerPath');
  const ledgerPath = ledgerFile.path;
  let text;
  try {
    text = readFileSync(ledgerPath, 'utf8');
  } catch (error) {
    throw new LegacyV0ReplayError0(
      'Replay.ChecksumLedgerReadFailed',
      `could not read checksum ledger: ${ledgerRelativePath}`,
      normalizeError0(error),
    );
  }
  const entries = [];
  const seen = new Set();
  for (const [index, rawLine] of text.split(/\r?\n/).entries()) {
    if (rawLine === '') continue;
    const match = /^([0-9a-f]{64}) ([ *])(.+)$/.exec(rawLine);
    if (match === null) {
      throw new LegacyV0ReplayError0(
        'Replay.ChecksumLedgerSyntax',
        `invalid checksum ledger line ${index + 1}`,
        { ledger: ledgerRelativePath, line: index + 1 },
      );
    }
    const [, expected, , relativePath] = match;
    if (seen.has(relativePath)) {
      throw new LegacyV0ReplayError0(
        'Replay.ChecksumLedgerDuplicate',
        `duplicate checksum path: ${relativePath}`,
      );
    }
    seen.add(relativePath);
    if (options.allowedPrefix !== undefined && !insideRelative0(options.allowedPrefix, relativePath)) {
      throw new LegacyV0ReplayError0(
        'Replay.ChecksumPathOutsideBundle',
        `checksum path leaves the sealed bundle: ${relativePath}`,
      );
    }
    if (options.allowedPaths !== undefined && !options.allowedPaths.includes(relativePath)) {
      throw new LegacyV0ReplayError0(
        'Replay.ChecksumPathUnexpected',
        `unexpected checksum path: ${relativePath}`,
      );
    }
    const confined = confinedRegularFile0(root, relativePath, 'Replay.ChecksumPathUnsafe');
    const filePath = confined.path;
    const info = confined.info;
    const actual = sha256File0(filePath);
    if (actual !== expected) {
      throw new LegacyV0ReplayError0(
        'Replay.ChecksumMismatch',
        `checksum mismatch: ${relativePath}`,
        { path: relativePath, expected, actual },
      );
    }
    entries.push({ path: relativePath, sha256: actual, size: info.size });
  }
  if (entries.length === 0) {
    throw new LegacyV0ReplayError0('Replay.ChecksumLedgerEmpty', `checksum ledger is empty: ${ledgerRelativePath}`);
  }
  if (options.expectedCount !== undefined && entries.length !== options.expectedCount) {
    throw new LegacyV0ReplayError0(
      'Replay.ChecksumEntryCount',
      `checksum ledger entry count mismatch: ${ledgerRelativePath}`,
      { expected: options.expectedCount, actual: entries.length },
    );
  }
  return {
    ledger: ledgerRelativePath,
    ledgerSha256: sha256Text0(text),
    entryCount: entries.length,
    entries,
  };
}

export function ReplayLegacyV00(options = {}) {
  const root = resolveGitTopLevel0(options.root ?? process.cwd());
  const outputCheck = validateLegacyV0OutputPath0(root, options.output);
  const manifest = loadLegacyV0ArchiveManifest0(root, options.manifest);
  const tags = verifyLegacyV0TagPins0(root);
  const plan = buildLegacyV0ReplayPlan0({ full: options.full === true });
  if (options.dryRun === true) {
    return {
      ...plan,
      dryRun: true,
      output: outputCheck.output,
      manifestCoordinate: manifest.coordinate,
      tagIdentityVerified: true,
      annotatedTagsSigned: false,
    };
  }

  const output = outputCheck.output;
  mkdirSync(output, { recursive: false });
  mkdirSync(path.join(output, 'logs'));
  const temporaryRoot = mkdtempSync(path.join(os.tmpdir(), 'pnp-legacy-v0-replay-'));
  const worktrees = {
    source: path.join(temporaryRoot, 'source'),
    artifacts: path.join(temporaryRoot, 'artifacts'),
    documents: path.join(temporaryRoot, 'documents'),
  };
  const disabledHooks = path.join(temporaryRoot, 'disabled-hooks');
  mkdirSync(disabledHooks);
  const added = [];
  try {
    for (const role of ['source', 'artifacts', 'documents']) {
      gitWorktreeAdd0(root, worktrees[role], LEGACY_V0_REPLAY_PINS0[role].commit, disabledHooks);
      added.push(worktrees[role]);
    }
    const initialWorktreeIntegrity = verifyWorktreeHeads0(worktrees);
    const manifestFiles = {
      source: verifyManifestFiles0(worktrees.source, manifest.source.files),
      artifacts: verifyArtifactManifestFiles0(worktrees.artifacts, manifest.artifacts),
      documents: verifyManifestFiles0(worktrees.documents, manifest.documents.files),
    };
    const checksums = verifySealedChecksums0(worktrees.artifacts);
    const seal = verifyReleaseSeal0(worktrees.artifacts);

    runLogged0(
      npmCommand0(),
      ['ci', '--ignore-scripts'],
      worktrees.source,
      path.join(output, 'logs', 'npm-ci.log'),
      'Replay.DependencyInstallFailed',
    );
    const postInstallSourceIntegrity = verifyPinnedWorktreeBytes0(
      worktrees.source,
      LEGACY_V0_REPLAY_PINS0.source.commit,
      LEGACY_V0_REPLAY_PINS0.source.tree,
    );
    const validationLog = path.join(output, 'logs', options.full === true ? 'validate.log' : 'hardened-smoke.log');
    if (options.full === true) {
      runLogged0(npmCommand0(), ['run', 'validate'], worktrees.source, validationLog, 'Replay.ValidationFailed');
    } else {
      runLogged0(
        process.execPath,
        ['--test', ...LEGACY_V0_SMOKE_TESTS0],
        worktrees.source,
        validationLog,
        'Replay.ValidationFailed',
      );
    }

    const postValidationSourceIntegrity = verifyPinnedWorktreeBytes0(
      worktrees.source,
      LEGACY_V0_REPLAY_PINS0.source.commit,
      LEGACY_V0_REPLAY_PINS0.source.tree,
    );

    const compactDirectory = path.join(output, 'compact');
    const regenerationLog = path.join(output, 'logs', 'regenerate-compact.stderr.log');
    const generatedText = runCaptured0(
      process.execPath,
      ['./bin/write-final-pnp-proof-report0.mjs', compactDirectory],
      worktrees.source,
      regenerationLog,
      'Replay.RegenerationFailed',
    );
    const postRegenerationSourceIntegrity = verifyPinnedWorktreeBytes0(
      worktrees.source,
      LEGACY_V0_REPLAY_PINS0.source.commit,
      LEGACY_V0_REPLAY_PINS0.source.tree,
    );
    let generatedSummary;
    try {
      generatedSummary = JSON.parse(generatedText);
    } catch (error) {
      throw new LegacyV0ReplayError0(
        'Replay.RegeneratedSummaryInvalid',
        'regenerated compact proof-report summary was not JSON',
        normalizeError0(error),
      );
    }
    const summaryPath = path.join(output, 'final-pnp-proof-report.summary.json');
    writeJson0(summaryPath, generatedSummary);
    const postExecutionArtifactIntegrity = verifyPinnedWorktreeBytes0(
      worktrees.artifacts,
      LEGACY_V0_REPLAY_PINS0.artifacts.commit,
      LEGACY_V0_REPLAY_PINS0.artifacts.tree,
    );
    const postExecutionDocumentIntegrity = verifyPinnedWorktreeBytes0(
      worktrees.documents,
      LEGACY_V0_REPLAY_PINS0.documents.commit,
      LEGACY_V0_REPLAY_PINS0.documents.tree,
    );
    const archivedSummaryPath = path.join(
      worktrees.artifacts,
      BUNDLE_PATH,
      'final-pnp-proof-report.summary.json',
    );
    const archivedSummary = JSON.parse(readFileSync(archivedSummaryPath, 'utf8'));
    const compared = compareClaimCriticalFields0(archivedSummary, generatedSummary);
    verifySealAcceptedFields0(seal, archivedSummary);

    const transcript = {
      kind: 'PNPLegacyV0ReplayTranscript0',
      version: 0,
      archiveId: 'legacy-v0-7072f8d',
      coordinate: ARCHIVE_COORDINATE,
      replayStatus: 'completed',
      historicalCheckerResult: generatedSummary.tag,
      ...CLAIM_BOUNDARY0,
      caution: 'This transcript replays a historical checker release. It is not current status authority or a mathematical proof.',
      mode: options.full === true ? 'full' : 'hardened-smoke',
      pins: clonePins0(),
      identityVerification: {
        exactAnnotatedTagObjects: true,
        exactPeeledCommits: true,
        exactTrees: true,
        annotatedTagsSigned: false,
        checkoutHooksDisabled: true,
        trackedRuntimeBytesVerified: true,
        worktrees: initialWorktreeIntegrity,
        sourceIntegrityPhases: {
          postInstall: postInstallSourceIntegrity,
          postValidation: postValidationSourceIntegrity,
          postRegeneration: postRegenerationSourceIntegrity,
        },
        postExecutionArtifactIntegrity,
        postExecutionDocumentIntegrity,
        tags,
      },
      fileVerification: {
        manifestFiles,
        sealedChecksumLedgerSha256: checksums.primary.ledgerSha256,
        sealedChecksumEntryCount: checksums.primary.entryCount,
        detachedChecksumLedgerSha256: checksums.detached.ledgerSha256,
        detachedChecksumEntryCount: checksums.detached.entryCount,
      },
      dependencyInstall: {
        command: 'npm ci --ignore-scripts',
        lifecycleScriptsAllowed: false,
        completed: true,
      },
      environment: replayEnvironment0(root),
      validation: {
        command: options.full === true
          ? 'npm run validate'
          : `node --test ${LEGACY_V0_SMOKE_TESTS0.join(' ')}`,
        smokeTestFileCount: options.full === true ? null : LEGACY_V0_SMOKE_TESTS0.length,
        completed: true,
      },
      regeneration: {
        mode: 'compact',
        outputDirectory: 'compact',
        summaryPath: 'final-pnp-proof-report.summary.json',
        completed: true,
      },
      claimCriticalComparison: {
        matched: true,
        fieldCount: LEGACY_V0_CLAIM_CRITICAL_PATHS0.length,
        fields: compared,
      },
    };
    writeJson0(path.join(output, 'replay-transcript.json'), transcript);
    return transcript;
  } finally {
    for (const worktree of added.reverse()) removeWorktree0(root, worktree);
    rmSync(temporaryRoot, { recursive: true, force: true });
  }
}

function validateArchiveManifest0(manifest) {
  if (!plain0(manifest)) throw new LegacyV0ReplayError0('Replay.ManifestShape', 'archive manifest must be an object');
  assertEqual0(manifest.kind, 'PNPLegacyV0Archive0', 'Replay.ManifestKind', 'archive manifest kind mismatch');
  assertEqual0(manifest.version, 0, 'Replay.ManifestVersion', 'archive manifest version mismatch');
  assertEqual0(manifest.coordinate, ARCHIVE_COORDINATE, 'Replay.ManifestCoordinate', 'archive coordinate mismatch');
  assertEqual0(manifest.status, 'historical-checker-archive', 'Replay.ManifestStatus', 'archive status mismatch');
  assertEqual0(manifest.archiveId, 'legacy-v0-7072f8d', 'Replay.ManifestId', 'archive id mismatch');
  for (const [role, pin] of Object.entries(LEGACY_V0_REPLAY_PINS0)) {
    const section = manifest[role];
    if (!plain0(section) || !plain0(section.tag)) {
      throw new LegacyV0ReplayError0('Replay.ManifestTagShape', `archive ${role}.tag must be an object`);
    }
    for (const field of ['name', 'object', 'commit', 'tree']) {
      assertEqual0(
        section.tag[field],
        pin[field],
        'Replay.ManifestTagPinMismatch',
        `archive ${role}.tag.${field} mismatch`,
      );
    }
    assertEqual0(section.tag.annotated, true, 'Replay.ManifestAnnotatedFlag', `${role} tag must be annotated`);
    assertEqual0(section.tag.signed, false, 'Replay.ManifestSignedFlag', `${role} tag is unsigned`);
    assertEqual0(
      stableStringify0(section.files),
      stableStringify0(LEGACY_V0_ARCHIVE_FILE_PINS0[role]),
      'Replay.ManifestFileList',
      `archive ${role}.files mismatch`,
    );
  }
  assertEqual0(manifest.source.packageVersion, '0.1.0', 'Replay.ManifestPackageVersion', 'source package version mismatch');
  assertEqual0(manifest.artifacts.bundlePath, BUNDLE_PATH, 'Replay.ManifestBundlePath', 'artifact bundle path mismatch');
  assertEqual0(manifest.historicalValidation?.tests, 1121, 'Replay.ManifestValidationTests', 'historical test count mismatch');
  assertEqual0(manifest.historicalValidation?.pass, 1121, 'Replay.ManifestValidationPass', 'historical pass count mismatch');
  for (const field of ['fail', 'cancelled', 'skipped', 'todo']) {
    assertEqual0(manifest.historicalValidation?.[field], 0, 'Replay.ManifestValidationFailureCount', `historicalValidation.${field} must be zero`);
  }
  if (!plain0(manifest.replay)) throw new LegacyV0ReplayError0('Replay.ManifestReplayShape', 'archive replay must be an object');
  assertEqual0(
    manifest.replay.command,
    'npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d',
    'Replay.ManifestCommand',
    'archive replay command mismatch',
  );
  assertEqual0(
    manifest.replay.fullCommand,
    'npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d --full',
    'Replay.ManifestFullCommand',
    'archive full replay command mismatch',
  );
  assertEqual0(manifest.replay.outputMustBeOutsideCheckout, true, 'Replay.ManifestOutputPolicy', 'archive replay output policy mismatch');
  assertEqual0(manifest.replay.refuseExistingOutput, true, 'Replay.ManifestOverwritePolicy', 'archive overwrite policy mismatch');
  if (!plain0(manifest.claimBoundary)) {
    throw new LegacyV0ReplayError0('Replay.ManifestBoundaryShape', 'archive claimBoundary must be an object');
  }
  for (const [field, expected] of Object.entries(CLAIM_BOUNDARY0)) {
    assertEqual0(
      manifest.claimBoundary[field],
      expected,
      'Replay.ManifestBoundaryMismatch',
      `archive claimBoundary.${field} mismatch`,
    );
  }
}

function verifyWorktreeHeads0(worktrees) {
  const verified = {};
  for (const [role, worktree] of Object.entries(worktrees)) {
    verified[role] = verifyPinnedWorktreeBytes0(
      worktree,
      LEGACY_V0_REPLAY_PINS0[role].commit,
      LEGACY_V0_REPLAY_PINS0[role].tree,
    );
  }
  return verified;
}

export function verifyPinnedWorktreeBytes0(worktree, expectedCommit, expectedTree) {
  const head = git0(worktree, ['rev-parse', 'HEAD']);
  const tree = git0(worktree, ['rev-parse', 'HEAD^{tree}']);
  assertEqual0(head, expectedCommit, 'Replay.WorktreeCommitMismatch', 'worktree commit mismatch');
  assertEqual0(tree, expectedTree, 'Replay.WorktreeTreeMismatch', 'worktree tree mismatch');

  const objectFormat = git0(worktree, ['rev-parse', '--show-object-format']);
  if (objectFormat !== 'sha1' && objectFormat !== 'sha256') {
    throw new LegacyV0ReplayError0('Replay.ObjectFormatUnsupported', `unsupported Git object format: ${objectFormat}`);
  }
  const listing = git0(worktree, ['ls-tree', '-r', '-z', '--full-tree', expectedCommit], { trim: false });
  const entries = listing.split('\0').filter((entry) => entry.length !== 0);
  for (const entry of entries) {
    const match = /^([0-7]{6}) (blob|commit) ([0-9a-f]+)\t([\s\S]+)$/u.exec(entry);
    if (match === null) {
      throw new LegacyV0ReplayError0('Replay.WorktreeTreeEntry', 'could not parse pinned tree entry');
    }
    const [, mode, type, expectedObject, relativePath] = match;
    if (type !== 'blob' || mode === '160000') {
      throw new LegacyV0ReplayError0(
        'Replay.WorktreeSubmoduleForbidden',
        `pinned replay worktree contains a submodule: ${relativePath}`,
      );
    }
    if (mode === '120000') {
      throw new LegacyV0ReplayError0(
        'Replay.WorktreeSymlinkForbidden',
        `pinned replay worktree contains a symbolic link: ${relativePath}`,
      );
    }
    const confined = confinedRegularFile0(worktree, relativePath, 'Replay.WorktreePathUnsafe');
    const bytes = readFileSync(confined.path);
    const actualObject = gitBlobObjectId0(objectFormat, bytes);
    if (actualObject !== expectedObject) {
      throw new LegacyV0ReplayError0(
        'Replay.WorktreeByteMismatch',
        `checked-out bytes differ from the pinned Git blob: ${relativePath}`,
        { path: relativePath, expectedObject, actualObject },
      );
    }
  }
  return {
    commit: head,
    tree,
    objectFormat,
    trackedBlobCount: entries.length,
    trackedBytesMatchPinnedTree: true,
    symlinksAllowed: false,
  };
}

function verifyManifestFiles0(root, files) {
  const verified = [];
  for (const file of files) {
    validateManifestFileRecord0(file);
    const confined = confinedRegularFile0(root, file.path, 'Replay.ManifestFilePathUnsafe');
    const actual = sha256File0(confined.path);
    if (actual !== file.sha256) {
      throw new LegacyV0ReplayError0(
        'Replay.ManifestFileDigestMismatch',
        `manifest file digest mismatch: ${file.path}`,
        { path: file.path, expected: file.sha256, actual },
      );
    }
    verified.push({ path: file.path, sha256: actual });
  }
  return verified;
}

function verifyArtifactManifestFiles0(artifactRoot, section) {
  const normalized = section.files.map((file) => {
    validateManifestFileRecord0(file);
    return file.path.startsWith(`${section.bundlePath}/`)
      ? file
      : { ...file, path: `${section.bundlePath}/${file.path}` };
  });
  return verifyManifestFiles0(artifactRoot, normalized);
}

function validateManifestFileRecord0(file) {
  if (!plain0(file) || typeof file.path !== 'string' || !/^[0-9a-f]{64}$/.test(file.sha256)) {
    throw new LegacyV0ReplayError0('Replay.ManifestFileRecord', 'manifest file records require path and sha256');
  }
}

function verifySealedChecksums0(artifactRoot) {
  const primaryPath = `${BUNDLE_PATH}/SHA256SUMS`;
  const detachedPath = `${BUNDLE_PATH}/SHA256SUMS.sha256`;
  const primary = verifyChecksumLedger0(artifactRoot, primaryPath, { allowedPrefix: BUNDLE_PATH });
  if (primary.entries.some((entry) => entry.path === primaryPath)) {
    throw new LegacyV0ReplayError0('Replay.ChecksumLedgerSelfEntry', 'SHA256SUMS must not contain a self-entry');
  }
  const detached = verifyChecksumLedger0(artifactRoot, detachedPath, {
    allowedPaths: [primaryPath],
    expectedCount: 1,
  });
  return { primary, detached };
}

function verifyReleaseSeal0(artifactRoot) {
  const sealPath = confinedRegularFile0(
    artifactRoot,
    `${BUNDLE_PATH}/release-seal.json`,
    'Replay.ReleaseSealPathUnsafe',
  ).path;
  let seal;
  try {
    seal = JSON.parse(readFileSync(sealPath, 'utf8'));
  } catch (error) {
    throw new LegacyV0ReplayError0('Replay.ReleaseSealReadFailed', 'could not read release seal', normalizeError0(error));
  }
  assertEqual0(seal.sourceCommit, LEGACY_V0_REPLAY_PINS0.source.commit, 'Replay.SealSourceCommit', 'release seal source commit mismatch');
  assertEqual0(seal.sourceTag, LEGACY_V0_REPLAY_PINS0.source.name, 'Replay.SealSourceTag', 'release seal source tag mismatch');
  assertEqual0(seal.sealedArtifactTag, LEGACY_V0_REPLAY_PINS0.artifacts.name, 'Replay.SealArtifactTag', 'release seal artifact tag mismatch');
  assertEqual0(seal.bundlePath, BUNDLE_PATH, 'Replay.SealBundlePath', 'release seal bundle path mismatch');
  assertEqual0(seal.validation?.tests, 1121, 'Replay.SealValidationTests', 'release seal test count mismatch');
  assertEqual0(seal.validation?.pass, 1121, 'Replay.SealValidationPass', 'release seal pass count mismatch');
  for (const field of ['fail', 'cancelled', 'skipped', 'todo']) {
    assertEqual0(seal.validation?.[field], 0, 'Replay.SealValidationFailureCount', `release seal validation.${field} must be zero`);
  }
  return seal;
}

function verifySealAcceptedFields0(seal, archivedSummary) {
  const expected = {
    summaryTag: archivedSummary.tag,
    summaryChecker: archivedSummary.checker,
    summaryStatus: archivedSummary.status,
    summaryFinalPNPProofReportAccepted: archivedSummary.finalPNPProofReportAccepted,
    summaryCheckPCCPackexpAccepted: archivedSummary.checkPCCPackexpAccepted,
  };
  for (const [field, value] of Object.entries(expected)) {
    assertEqual0(seal.acceptedFields?.[field], value, 'Replay.SealAcceptedFieldMismatch', `release seal ${field} mismatch`);
  }
  assertEqual0(seal.theorem?.statement, archivedSummary.theorem?.statement, 'Replay.SealTheoremMismatch', 'release seal theorem mismatch');
  assertEqual0(seal.theorem?.antecedent, archivedSummary.theorem?.antecedent, 'Replay.SealAntecedentMismatch', 'release seal antecedent mismatch');
  assertEqual0(seal.publicConclusionStatement, archivedSummary.publicConclusionStatement, 'Replay.SealConclusionMismatch', 'release seal public conclusion mismatch');
}

function gitWorktreeAdd0(root, worktree, commit, hooksPath) {
  const child = spawnSync('git', [
    '-c', `core.hooksPath=${hooksPath}`,
    '-c', `core.attributesFile=${os.devNull}`,
    'worktree', 'add', '--detach', worktree, commit,
  ], {
    cwd: root,
    encoding: 'utf8',
    maxBuffer: 16 * 1024 * 1024,
  });
  if (child.error || child.status !== 0) {
    throw new LegacyV0ReplayError0(
      'Replay.WorktreeAddFailed',
      `could not create detached worktree for ${commit}`,
      childFailure0(child),
    );
  }
}

function removeWorktree0(root, worktree) {
  const child = spawnSync('git', ['worktree', 'remove', '--force', worktree], {
    cwd: root,
    encoding: 'utf8',
    maxBuffer: 16 * 1024 * 1024,
  });
  if (child.status !== 0) rmSync(worktree, { recursive: true, force: true });
}

function runLogged0(command, args, cwd, logPath, errorCode) {
  const fd = openSync(logPath, 'w');
  let child;
  try {
    child = spawnSync(command, args, { cwd, stdio: ['ignore', fd, fd] });
  } finally {
    closeSync(fd);
  }
  if (child.error || child.status !== 0) {
    throw new LegacyV0ReplayError0(errorCode, `command failed; inspect ${logPath}`, childFailure0(child));
  }
}

function runCaptured0(command, args, cwd, stderrPath, errorCode) {
  const fd = openSync(stderrPath, 'w');
  let child;
  try {
    child = spawnSync(command, args, {
      cwd,
      encoding: 'utf8',
      maxBuffer: 64 * 1024 * 1024,
      stdio: ['ignore', 'pipe', fd],
    });
  } finally {
    closeSync(fd);
  }
  if (child.error || child.status !== 0) {
    throw new LegacyV0ReplayError0(errorCode, `command failed; inspect ${stderrPath}`, childFailure0(child));
  }
  return child.stdout;
}

function git0(root, args, options = {}) {
  const child = spawnSync('git', args, {
    cwd: root,
    encoding: 'utf8',
    maxBuffer: 16 * 1024 * 1024,
  });
  if (child.error || child.status !== 0) {
    throw new LegacyV0ReplayError0(
      'Replay.GitCommandFailed',
      `git ${args.join(' ')} failed`,
      childFailure0(child),
    );
  }
  return options.trim === false ? child.stdout : child.stdout.trim();
}

function resolveGitTopLevel0(root) {
  let candidate;
  try {
    candidate = realpathSync(path.resolve(root));
  } catch (error) {
    throw new LegacyV0ReplayError0(
      'Replay.RootInvalid',
      'replay root must resolve to a directory inside the repository worktree',
      normalizeError0(error),
    );
  }
  const child = spawnSync('git', ['rev-parse', '--show-toplevel'], {
    cwd: candidate,
    encoding: 'utf8',
    maxBuffer: 1024 * 1024,
  });
  if (child.error || child.status !== 0) {
    throw new LegacyV0ReplayError0(
      'Replay.GitTopLevelNotFound',
      'replay root must be inside a Git worktree',
      childFailure0(child),
    );
  }
  try {
    return realpathSync(child.stdout.trim());
  } catch (error) {
    throw new LegacyV0ReplayError0(
      'Replay.GitTopLevelInvalid',
      'Git reported an invalid worktree root',
      normalizeError0(error),
    );
  }
}

function canonicalProspectivePath0(candidate) {
  let cursor = candidate;
  const tail = [];
  while (!existsSync(cursor)) {
    const parent = path.dirname(cursor);
    if (parent === cursor) break;
    tail.unshift(path.basename(cursor));
    cursor = parent;
  }
  const canonicalBase = realpathSync(cursor);
  return path.resolve(canonicalBase, ...tail);
}

function lexists0(candidate) {
  try {
    lstatSync(candidate);
    return true;
  } catch (error) {
    if (error?.code === 'ENOENT' || error?.code === 'ENOTDIR') return false;
    throw error;
  }
}

function inside0(root, candidate) {
  const relative = path.relative(root, candidate);
  return relative === '' || (!relative.startsWith(`..${path.sep}`) && relative !== '..' && !path.isAbsolute(relative));
}

function insideRelative0(prefix, candidate) {
  const normalizedPrefix = path.posix.normalize(prefix.replaceAll('\\', '/'));
  const normalizedCandidate = path.posix.normalize(candidate.replaceAll('\\', '/'));
  return normalizedCandidate === normalizedPrefix || normalizedCandidate.startsWith(`${normalizedPrefix}/`);
}

function confinedRegularFile0(root, relativePath, errorCode) {
  if (typeof relativePath !== 'string' || relativePath === '' || path.isAbsolute(relativePath)) {
    throw new LegacyV0ReplayError0(errorCode, `unsafe file path: ${relativePath}`);
  }
  const canonicalRoot = realpathSync(path.resolve(root));
  const components = relativePath.replaceAll('\\', '/').split('/');
  if (components.some((component) => component === '' || component === '.' || component === '..')) {
    throw new LegacyV0ReplayError0(errorCode, `unsafe file path: ${relativePath}`);
  }
  let cursor = canonicalRoot;
  for (let index = 0; index < components.length; index += 1) {
    cursor = path.join(cursor, components[index]);
    let info;
    try {
      info = lstatSync(cursor);
    } catch (error) {
      throw new LegacyV0ReplayError0(errorCode, `file path is missing: ${relativePath}`, normalizeError0(error));
    }
    if (info.isSymbolicLink()) {
      throw new LegacyV0ReplayError0(errorCode, `symbolic links are forbidden in replay paths: ${relativePath}`);
    }
    if (index < components.length - 1 && !info.isDirectory()) {
      throw new LegacyV0ReplayError0(errorCode, `non-directory path component: ${relativePath}`);
    }
    if (index === components.length - 1 && !info.isFile()) {
      throw new LegacyV0ReplayError0(errorCode, `replay path is not a regular file: ${relativePath}`);
    }
  }
  const canonicalFile = realpathSync(cursor);
  if (!inside0(canonicalRoot, canonicalFile)) {
    throw new LegacyV0ReplayError0(errorCode, `file path leaves its root: ${relativePath}`);
  }
  return { path: canonicalFile, info: statSync(canonicalFile) };
}

function parseAnnotatedTagHeader0(text) {
  const headerText = text.split('\n\n', 1)[0];
  const out = {};
  for (const line of headerText.split('\n')) {
    const separator = line.indexOf(' ');
    if (separator > 0) out[line.slice(0, separator)] = line.slice(separator + 1);
  }
  return out;
}

function getPath0(value, dottedPath) {
  return dottedPath.split('.').reduce((current, key) => current?.[key], value);
}

function clonePins0() {
  return Object.fromEntries(
    Object.entries(LEGACY_V0_REPLAY_PINS0).map(([role, pin]) => [role, { ...pin }]),
  );
}

function assertEqual0(actual, expected, code, message) {
  if (!Object.is(actual, expected)) {
    throw new LegacyV0ReplayError0(code, message, { expected, actual });
  }
}

function requireValue0(argv, index, flag) {
  if (index >= argv.length || argv[index].startsWith('--')) {
    throw new LegacyV0ReplayError0('Replay.BadArgument', `${flag} requires a value`);
  }
  return argv[index];
}

function sha256File0(filePath) {
  return createHash('sha256').update(readFileSync(filePath)).digest('hex');
}

function sha256Text0(text) {
  return createHash('sha256').update(text, 'utf8').digest('hex');
}

function gitBlobObjectId0(format, bytes) {
  const header = Buffer.from(`blob ${bytes.length}\0`, 'utf8');
  return createHash(format).update(header).update(bytes).digest('hex');
}

function replayEnvironment0(root) {
  const npm = spawnSync(npmCommand0(), ['--version'], { cwd: root, encoding: 'utf8' });
  return {
    recordedAtReplay: true,
    releaseEnvironmentFullyPinned: false,
    node: process.version,
    npm: npm.status === 0 ? npm.stdout.trim() : null,
    git: git0(root, ['--version']),
    platform: process.platform,
    architecture: process.arch,
    osType: os.type(),
    osRelease: os.release(),
  };
}

function stableStringify0(value) {
  if (value === undefined) return 'undefined';
  if (value === null || typeof value !== 'object') return JSON.stringify(value);
  if (Array.isArray(value)) return `[${value.map(stableStringify0).join(',')}]`;
  return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`;
}

function writeJson0(filePath, value) {
  writeFileSync(filePath, `${JSON.stringify(value, null, 2)}\n`, { encoding: 'utf8', flag: 'wx' });
}

function npmCommand0() {
  return process.platform === 'win32' ? 'npm.cmd' : 'npm';
}

function childFailure0(child) {
  return {
    status: child?.status ?? null,
    signal: child?.signal ?? null,
    error: child?.error === undefined ? null : normalizeError0(child.error),
    stderr: typeof child?.stderr === 'string' ? child.stderr.trim().slice(0, 4096) : null,
  };
}

function normalizeError0(error) {
  return {
    name: typeof error?.name === 'string' ? error.name : 'Error',
    code: typeof error?.code === 'string' ? error.code : null,
    message: typeof error?.message === 'string' ? error.message : String(error),
  };
}

function plain0(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function printHelp0() {
  process.stdout.write(`Usage: node scripts/replay-legacy-v0.mjs --output <path> [--full] [--dry-run]\n\n`);
  process.stdout.write('Replays the pinned legacy-v0 checker release outside the active checkout.\n');
  process.stdout.write('The output path must not exist. The default validation is the ten-file hardened smoke set.\n');
  process.stdout.write('--full runs the pinned npm validation suite. --dry-run verifies identities and prints the plan.\n');
}

async function main0() {
  try {
    const options = parseLegacyV0ReplayArgs0(process.argv.slice(2));
    if (options.help) {
      printHelp0();
      return;
    }
    const result = ReplayLegacyV00(options);
    process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
  } catch (error) {
    const normalized = error instanceof LegacyV0ReplayError0
      ? { tag: 'reject', checker: 'ReplayLegacyV00', code: error.code, reason: error.message, detail: error.detail ?? null, ...CLAIM_BOUNDARY0 }
      : { tag: 'reject', checker: 'ReplayLegacyV00', code: 'Replay.UnhandledException', reason: String(error), detail: normalizeError0(error), ...CLAIM_BOUNDARY0 };
    process.stderr.write(`${JSON.stringify(normalized, null, 2)}\n`);
    process.exitCode = 1;
  }
}

if (process.argv[1] !== undefined && pathToFileURL(path.resolve(process.argv[1])).href === import.meta.url) {
  await main0();
}
