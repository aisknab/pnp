import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import {
  existsSync,
  mkdtempSync,
  mkdirSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { after, test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  LEGACY_V0_ARCHIVE_FILE_PINS0,
  LEGACY_V0_CLAIM_CRITICAL_PATHS0,
  LEGACY_V0_REPLAY_PINS0,
  LEGACY_V0_SMOKE_TESTS0,
  LegacyV0ReplayError0,
  ReplayLegacyV00,
  buildLegacyV0ReplayPlan0,
  compareClaimCriticalFields0,
  loadLegacyV0ArchiveManifest0,
  parseLegacyV0ReplayArgs0,
  validateLegacyV0OutputPath0,
  verifyChecksumLedger0,
  verifyLegacyV0TagPins0,
  verifyPinnedWorktreeBytes0,
} from '../scripts/replay-legacy-v0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const TEMP_ROOT = mkdtempSync(path.join(os.tmpdir(), 'pnp-replay-legacy-v0-test-'));

after(() => rmSync(TEMP_ROOT, { recursive: true, force: true }));

test('legacy-v0 replay pins exact annotated tag objects, commits, and trees', () => {
  assert.deepEqual(LEGACY_V0_REPLAY_PINS0, {
    source: {
      name: 'final-pnp-proof-report-hardened-7072f8d',
      object: '9b69c4f8d8d6d62eb359af759288e5794d1c81c2',
      commit: '7072f8d0bda6d44d240f9bb3fad624fd357e1278',
      tree: '2b673c397c8438a0631952c2d0325456e96c5341',
    },
    artifacts: {
      name: 'final-pnp-proof-report-artifacts-hardened-7072f8d-sealed',
      object: 'e7ea459c907ed9e334af8c0bd5f3bb117348992d',
      commit: '9d1de19f827e5cb6880741352eb2349cbbb45994',
      tree: 'fa34921ab6279b2258436b325326d32bfb40fd36',
    },
    documents: {
      name: 'final-pnp-proof-report-docs-hardened-7072f8d-sealed',
      object: '9eeb4b85af1c04c43e6f086debcd3ac37d5d27d1',
      commit: '3ba356c79b545d2c734283bf10d85d0710de2b60',
      tree: '4f0c3b5d93da1783be1c24560dac3bf4023370f8',
    },
  });
});

test('repository tag verification confirms all pins are annotated and unsigned', () => {
  const out = verifyLegacyV0TagPins0(ROOT);

  assert.deepEqual(Object.keys(out), ['source', 'artifacts', 'documents']);
  for (const [role, pin] of Object.entries(LEGACY_V0_REPLAY_PINS0)) {
    assert.equal(out[role].object, pin.object);
    assert.equal(out[role].commit, pin.commit);
    assert.equal(out[role].tree, pin.tree);
    assert.equal(out[role].annotated, true);
    assert.equal(out[role].signed, false);
  }
});

test('argument parser selects smoke by default and full only explicitly', () => {
  assert.deepEqual(
    parseLegacyV0ReplayArgs0(['--output', '/tmp/replay']),
    { root: process.cwd(), output: '/tmp/replay', full: false, dryRun: false, help: false },
  );
  assert.deepEqual(
    parseLegacyV0ReplayArgs0(['--root', ROOT, '--output', '/tmp/replay', '--full', '--dry-run']),
    { root: ROOT, output: '/tmp/replay', full: true, dryRun: true, help: false },
  );
  assert.throws(
    () => parseLegacyV0ReplayArgs0([]),
    (error) => error instanceof LegacyV0ReplayError0 && error.code === 'Replay.OutputRequired',
  );
  assert.throws(
    () => parseLegacyV0ReplayArgs0(['--output', '/tmp/replay', '--force']),
    (error) => error instanceof LegacyV0ReplayError0 && error.code === 'Replay.BadArgument',
  );
});

test('replay plan pins lifecycle-disabled install, ten smoke files, and compact regeneration', () => {
  const plan = buildLegacyV0ReplayPlan0();
  const install = plan.steps.find((step) => step.id === 'install');
  const validation = plan.steps.find((step) => step.id === 'validate');
  const regeneration = plan.steps.find((step) => step.id === 'regenerate-compact');

  assert.equal(plan.historicalReplay, true);
  assert.equal(plan.currentStatusAuthority, false);
  assert.equal(plan.mathematicalTheoremEstablished, false);
  assert.equal(plan.checkerReplayIsMathematicalProof, false);
  assert.equal(plan.publicTheoremEmissionAllowed, false);
  assert.equal(plan.finalTheoremReady, false);
  assert.deepEqual(install.command, ['npm', 'ci', '--ignore-scripts']);
  assert.equal(validation.mode, 'hardened-smoke');
  assert.deepEqual(validation.command, ['node', '--test', ...LEGACY_V0_SMOKE_TESTS0]);
  assert.equal(LEGACY_V0_SMOKE_TESTS0.length, 10);
  assert.ok(regeneration.command.includes('$OUTPUT/compact'));

  const full = buildLegacyV0ReplayPlan0({ full: true });
  assert.deepEqual(full.steps.find((step) => step.id === 'validate').command, ['npm', 'run', 'validate']);
});

test('output guard rejects existing output and every path inside the checkout', () => {
  const existing = path.join(TEMP_ROOT, 'existing');
  mkdirSync(existing);

  assert.throws(
    () => validateLegacyV0OutputPath0(ROOT, existing),
    (error) => error instanceof LegacyV0ReplayError0 && error.code === 'Replay.OutputExists',
  );
  assert.throws(
    () => validateLegacyV0OutputPath0(ROOT, path.join(ROOT, 'uncreated-replay-output')),
    (error) => error instanceof LegacyV0ReplayError0 && error.code === 'Replay.OutputInsideCheckout',
  );
});

test('output guard resolves the actual Git top-level when root is nested', () => {
  const nestedRoot = path.join(ROOT, 'scripts');
  const elsewhereInCheckout = path.join(ROOT, 'uncreated-replay-output-from-nested-root');

  assert.throws(
    () => validateLegacyV0OutputPath0(nestedRoot, elsewhereInCheckout),
    (error) => error instanceof LegacyV0ReplayError0 && error.code === 'Replay.OutputInsideCheckout',
  );
});

test('output guard resolves a symlinked parent before applying checkout confinement', () => {
  const symlink = path.join(TEMP_ROOT, 'checkout-link');
  symlinkSync(ROOT, symlink, 'dir');

  assert.throws(
    () => validateLegacyV0OutputPath0(ROOT, path.join(symlink, 'uncreated-replay-output')),
    (error) => error instanceof LegacyV0ReplayError0 && error.code === 'Replay.OutputInsideCheckout',
  );
});

test('output guard treats a dangling symlink as existing output', () => {
  const dangling = path.join(TEMP_ROOT, 'dangling-output');
  symlinkSync(path.join(TEMP_ROOT, 'missing-target'), dangling, 'dir');

  assert.throws(
    () => validateLegacyV0OutputPath0(ROOT, dangling),
    (error) => error instanceof LegacyV0ReplayError0 && error.code === 'Replay.OutputExists',
  );
});

test('manifest validation cross-checks pins and non-authoritative claim boundary', () => {
  const manifest = makeManifest0();
  assert.equal(loadLegacyV0ArchiveManifest0(ROOT, manifest), manifest);

  const tampered = structuredClone(manifest);
  tampered.source.tag.commit = '0'.repeat(40);
  assert.throws(
    () => loadLegacyV0ArchiveManifest0(ROOT, tampered),
    (error) => error instanceof LegacyV0ReplayError0 && error.code === 'Replay.ManifestTagPinMismatch',
  );

  const authorityEscalation = structuredClone(manifest);
  authorityEscalation.claimBoundary.mathematicalTheoremEstablished = true;
  assert.throws(
    () => loadLegacyV0ArchiveManifest0(ROOT, authorityEscalation),
    (error) => error instanceof LegacyV0ReplayError0 && error.code === 'Replay.ManifestBoundaryMismatch',
  );
});

test('dry-run is deterministic, creates no output, and performs no install', () => {
  const output = path.join(TEMP_ROOT, 'dry-run-output');
  const options = { root: ROOT, output, dryRun: true, manifest: makeManifest0() };

  const first = ReplayLegacyV00(options);
  const second = ReplayLegacyV00(options);

  assert.deepEqual(second, first);
  assert.equal(first.dryRun, true);
  assert.equal(first.tagIdentityVerified, true);
  assert.equal(first.currentStatusAuthority, false);
  assert.equal(first.mathematicalTheoremEstablished, false);
  assert.equal(first.checkerReplayIsMathematicalProof, false);
  assert.equal(first.steps.some((step) => step.id === 'install'), true);
  assert.throws(() => validateLegacyV0OutputPath0(ROOT, ROOT), /must be outside|overwrite existing/);
  assert.equal(pathExists0(output), false);
});

test('checksum verifier accepts a confined ledger and rejects a digest mutation', () => {
  const root = path.join(TEMP_ROOT, 'checksums');
  mkdirSync(path.join(root, 'bundle'), { recursive: true });
  const targetPath = path.join(root, 'bundle', 'payload.json');
  writeFileSync(targetPath, '{"accepted":true}\n');
  const digest = sha256Text0('{"accepted":true}\n');
  writeFileSync(path.join(root, 'SHA256SUMS'), `${digest}  bundle/payload.json\n`);

  const accepted = verifyChecksumLedger0(root, 'SHA256SUMS', { allowedPrefix: 'bundle' });
  assert.equal(accepted.entryCount, 1);
  assert.equal(accepted.entries[0].sha256, digest);

  writeFileSync(targetPath, '{"accepted":false}\n');
  assert.throws(
    () => verifyChecksumLedger0(root, 'SHA256SUMS', { allowedPrefix: 'bundle' }),
    (error) => error instanceof LegacyV0ReplayError0 && error.code === 'Replay.ChecksumMismatch',
  );
});

test('checksum verifier rejects traversal even when the traversed file exists', () => {
  const root = path.join(TEMP_ROOT, 'checksum-traversal');
  mkdirSync(path.join(root, 'bundle'), { recursive: true });
  const outside = path.join(root, 'outside.txt');
  writeFileSync(outside, 'outside\n');
  writeFileSync(
    path.join(root, 'SHA256SUMS'),
    `${sha256Text0('outside\n')}  bundle/../outside.txt\n`,
  );

  assert.throws(
    () => verifyChecksumLedger0(root, 'SHA256SUMS', { allowedPrefix: 'bundle' }),
    (error) => error instanceof LegacyV0ReplayError0 && error.code === 'Replay.ChecksumPathOutsideBundle',
  );
});

test('checksum verifier rejects a symlink even when its target has the expected digest', () => {
  const root = path.join(TEMP_ROOT, 'checksum-symlink');
  const outside = path.join(TEMP_ROOT, 'outside-symlink-target.txt');
  mkdirSync(path.join(root, 'bundle'), { recursive: true });
  writeFileSync(outside, 'outside\n');
  symlinkSync(outside, path.join(root, 'bundle', 'payload.txt'));
  writeFileSync(
    path.join(root, 'SHA256SUMS'),
    `${sha256Text0('outside\n')}  bundle/payload.txt\n`,
  );

  assert.throws(
    () => verifyChecksumLedger0(root, 'SHA256SUMS', { allowedPrefix: 'bundle' }),
    (error) => error instanceof LegacyV0ReplayError0 && error.code === 'Replay.ChecksumPathUnsafe',
  );
});

test('raw worktree verification rejects tracked bytes changed after checkout', () => {
  const repo = path.join(TEMP_ROOT, 'worktree-byte-integrity');
  mkdirSync(repo);
  gitFixture0(repo, ['init', '--quiet']);
  gitFixture0(repo, ['config', 'user.name', 'Replay Test']);
  gitFixture0(repo, ['config', 'user.email', 'replay-test@example.invalid']);
  writeFileSync(path.join(repo, 'payload.mjs'), 'export const pinned = true;\n');
  gitFixture0(repo, ['add', 'payload.mjs']);
  gitFixture0(repo, ['commit', '--quiet', '-m', 'fixture']);
  const commit = gitFixture0(repo, ['rev-parse', 'HEAD']);
  const tree = gitFixture0(repo, ['rev-parse', 'HEAD^{tree}']);

  const accepted = verifyPinnedWorktreeBytes0(repo, commit, tree);
  assert.equal(accepted.trackedBytesMatchPinnedTree, true);
  assert.equal(accepted.trackedBlobCount, 1);

  writeFileSync(path.join(repo, 'payload.mjs'), 'export const pinned = false;\n');
  assert.throws(
    () => verifyPinnedWorktreeBytes0(repo, commit, tree),
    (error) => error instanceof LegacyV0ReplayError0
      && error.code === 'Replay.WorktreeByteMismatch'
      && error.detail.path === 'payload.mjs',
  );
});

test('claim-critical comparison covers the full boundary and fails closed on mismatch', () => {
  const archived = makeSummary0();
  const regenerated = structuredClone(archived);
  const compared = compareClaimCriticalFields0(archived, regenerated);

  assert.equal(Object.keys(compared).length, LEGACY_V0_CLAIM_CRITICAL_PATHS0.length);
  regenerated.publicConclusionStatement = 'different';
  assert.throws(
    () => compareClaimCriticalFields0(archived, regenerated),
    (error) => error instanceof LegacyV0ReplayError0
      && error.code === 'Replay.ClaimCriticalMismatch'
      && error.detail.path === 'publicConclusionStatement',
  );
});

function makeManifest0() {
  const sections = Object.fromEntries(
    Object.entries(LEGACY_V0_REPLAY_PINS0).map(([role, pin]) => [role, {
      tag: { ...pin, annotated: true, signed: false },
      files: LEGACY_V0_ARCHIVE_FILE_PINS0[role].map((file) => ({ ...file })),
    }]),
  );
  sections.source.packageVersion = '0.1.0';
  return {
    kind: 'PNPLegacyV0Archive0',
    version: 0,
    coordinate: 'PNP-LEGACY-V0-ARCHIVE-2026-07-10-01',
    status: 'historical-checker-archive',
    archiveId: 'legacy-v0-7072f8d',
    ...sections,
    artifacts: {
      ...sections.artifacts,
      bundlePath: 'proof-artifacts/final-pnp-proof-report-hardened-7072f8d',
    },
    replay: {
      command: 'npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d',
      fullCommand: 'npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d --full',
      outputMustBeOutsideCheckout: true,
      refuseExistingOutput: true,
    },
    historicalValidation: {
      tests: 1121,
      pass: 1121,
      fail: 0,
      cancelled: 0,
      skipped: 0,
      todo: 0,
    },
    claimBoundary: {
      historicalReplay: true,
      currentStatusAuthority: false,
      mathematicalTheoremEstablished: false,
      checkerReplayIsMathematicalProof: false,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
    },
  };
}

function makeSummary0() {
  return {
    tag: 'accept',
    checker: 'CheckFinalPNPProofReport0',
    finalPNPProofReportAccepted: true,
    status: 'accepted',
    theorem: {
      statement: 'P = NP',
      antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
      consequent: 'P = NP',
      conditional: true,
    },
    claimBoundary: 'accepted-final-pnp-release-gate',
    finalPNPReleaseGateAccepted: true,
    finalPNPCertificateAccepted: true,
    releaseAuditAccepted: true,
    finalAcceptanceReplayClosed: true,
    verdict: 'accept',
    generator: 'GeneratePCCPack',
    checkerName: 'CheckPCCPackexp0',
    generatorIsGeneratePCCPack: true,
    checkPCCPackexpAccepted: true,
    checkAcceptRunAccepted: true,
    replayAccepted: true,
    finalVerdictAccepted: true,
    publicConclusionAntecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
    publicConclusionConsequent: 'P = NP',
    publicConclusionConditional: true,
    publicConclusionStatement: 'CheckPCCPackexp(GeneratePCCPack())=accept => P = NP',
  };
}

function sha256Text0(text) {
  return createHash('sha256').update(text, 'utf8').digest('hex');
}

function pathExists0(candidate) {
  return existsSync(candidate);
}

function gitFixture0(cwd, args) {
  const child = spawnSync('git', args, { cwd, encoding: 'utf8' });
  assert.equal(child.status, 0, child.stderr);
  return child.stdout.trim();
}
