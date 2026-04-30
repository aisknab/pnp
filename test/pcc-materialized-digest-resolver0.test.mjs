import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  IndexMaterializedFixtureDigests0,
  MATERIALIZED_DIGEST_RESOLVER_DIGEST_KINDS0,
  ResolveMaterializedDigest0,
} from '../pcc-materialized-digest-resolver0.mjs';

import {
  MATERIALIZED_FIXTURE_FILENAMES0,
  WriteMaterializedFixtureSet0,
} from '../pcc-materialized-fixture-writer0.mjs';

function npmCommand0() {
  return process.platform === 'win32'
    ? 'npm.cmd'
    : 'npm';
}

function childFailureMessage0(child) {
  return [
    child.error?.message ?? '',
    child.stderr ?? '',
    child.stdout ?? '',
  ].filter((entry) => entry.length > 0).join('\n');
}

function parseJsonFromStdout0(stdout) {
  const firstBrace = stdout.indexOf('{');

  assert.notEqual(firstBrace, -1, stdout);

  return JSON.parse(stdout.slice(firstBrace));
}

test('IndexMaterializedFixtureDigests0 indexes all materialized fixture digests', async (t) => {
  const fixtureDir = await writeFixtures0(t);
  const out = await IndexMaterializedFixtureDigests0({
    fixtureDir,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'IndexMaterializedFixtureDigests0');
  assert.equal(out.NF.kind, 'MaterializedDigestIndex0NF');
  assert.equal(out.NF.fileCount, 3);
  assert.deepEqual(out.NF.digestKinds, MATERIALIZED_DIGEST_RESOLVER_DIGEST_KINDS0);
  assert.equal(out.NF.reverseLookupOnly, true);
  assert.equal(out.NF.notCryptographicInversion, true);
  assert.equal(out.IndexEntries.length, 3);
});

test('ResolveMaterializedDigest0 resolves a file SHA256 digest to exact fixture bytes', async (t) => {
  const fixtureDir = await writeFixtures0(t);
  const index = await IndexMaterializedFixtureDigests0({
    fixtureDir,
  });

  const packEntry = index.IndexEntries.find((entry) => entry.filename === MATERIALIZED_FIXTURE_FILENAMES0.pack);
  const out = await ResolveMaterializedDigest0(packEntry.fileBytesSha256.hex, {
    fixtureDir,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'ResolveMaterializedDigest0');
  assert.equal(out.NF.filename, MATERIALIZED_FIXTURE_FILENAMES0.pack);
  assert.equal(out.NF.matchedDigestKinds.includes('fileBytesSha256'), true);
  assert.equal(out.NF.reverseLookupOnly, true);
  assert.equal(out.NF.notCryptographicInversion, true);
  assert.equal(typeof out.FileBytes, 'string');
  assert.equal(typeof out.CanonicalBytes, 'string');
  assert.equal(JSON.parse(out.CanonicalBytes).kind, 'MaterializedPCCPack0');
});

test('ResolveMaterializedDigest0 resolves canonical object digest records', async (t) => {
  const fixtureDir = await writeFixtures0(t);
  const index = await IndexMaterializedFixtureDigests0({
    fixtureDir,
  });

  const acceptedBridge = index.IndexEntries.find((entry) => entry.filename === MATERIALIZED_FIXTURE_FILENAMES0.acceptedBridge);
  const out = await ResolveMaterializedDigest0(acceptedBridge.canonicalObjectDigest, {
    fixtureDir,
    includeBytes: false,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.filename, MATERIALIZED_FIXTURE_FILENAMES0.acceptedBridge);
  assert.equal(out.NF.matchedDigestKinds.includes('canonicalObjectDigest'), true);
  assert.equal(out.FileBytes, null);
  assert.equal(out.CanonicalBytes, null);
});

test('ResolveMaterializedDigest0 rejects unknown digest without attempting cryptographic inversion', async (t) => {
  const fixtureDir = await writeFixtures0(t);
  const out = await ResolveMaterializedDigest0('0000000000000000000000000000000000000000000000000000000000000000', {
    fixtureDir,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'ResolveMaterializedDigest0');
  assert.equal(out.Coord, 'ResolveMaterializedDigest0.resolve');
  assert.deepEqual(out.Path, ['digest']);
  assert.equal(out.Witness.reason, 'digest was not found in the materialized fixture digest index');
  assert.equal(out.Witness.detail.notCryptographicInversion, true);
});

test('ResolveMaterializedDigest0 rejects malformed digest input', async (t) => {
  const fixtureDir = await writeFixtures0(t);
  const out = await ResolveMaterializedDigest0('not-a-sha256-digest', {
    fixtureDir,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'ResolveMaterializedDigest0');
  assert.equal(out.Coord, 'ResolveMaterializedDigest0.digest');
  assert.deepEqual(out.Path, ['digest']);
  assert.equal(out.Witness.reason, 'digest must be a lowercase SHA256 hex string or digest record');
});

test('IndexMaterializedFixtureDigests0 rejects tampered fixture files during verification', async (t) => {
  const fixtureDir = await writeFixtures0(t);
  const packFile = path.join(fixtureDir, MATERIALIZED_FIXTURE_FILENAMES0.pack);

  await fs.writeFile(packFile, '{ "kind": "not valid" }', 'utf8');

  const out = await IndexMaterializedFixtureDigests0({
    fixtureDir,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'IndexMaterializedFixtureDigests0');
  assert.equal(out.Coord, 'IndexMaterializedFixtureDigests0.verify');
  assert.deepEqual(out.Path, ['files', MATERIALIZED_FIXTURE_FILENAMES0.pack]);
  assert.equal(out.Witness.reason, 'materialized fixture file failed checker verification');
});

test('bin/resolve-materialized-digest0.mjs resolves a digest from fixture files', async (t) => {
  const fixtureDir = await writeFixtures0(t);
  const index = await IndexMaterializedFixtureDigests0({
    fixtureDir,
  });
  const packEntry = index.IndexEntries.find((entry) => entry.filename === MATERIALIZED_FIXTURE_FILENAMES0.pack);
  const cliPath = fileURLToPath(new URL('../bin/resolve-materialized-digest0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, packEntry.fileBytesSha256.hex, '--dir', fixtureDir], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'ResolveMaterializedDigest0');
  assert.equal(out.filename, MATERIALIZED_FIXTURE_FILENAMES0.pack);
  assert.equal(out.reverseLookupOnly, true);
  assert.equal(out.notCryptographicInversion, true);
});

test('npm run materialized:resolve-digest resolves a digest from fixture files', async (t) => {
  const fixtureDir = await writeFixtures0(t);
  const index = await IndexMaterializedFixtureDigests0({
    fixtureDir,
  });
  const pendingBridge = index.IndexEntries.find((entry) => entry.filename === MATERIALIZED_FIXTURE_FILENAMES0.pendingBridge);

  const child = spawnSync(npmCommand0(), ['run', 'materialized:resolve-digest', '--', pendingBridge.fileBytesSha256.hex, '--dir', fixtureDir], {
    encoding: 'utf8',
    shell: process.platform === 'win32',
    windowsHide: true,
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = parseJsonFromStdout0(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.filename, MATERIALIZED_FIXTURE_FILENAMES0.pendingBridge);
  assert.equal(out.reverseLookupOnly, true);
  assert.equal(out.notCryptographicInversion, true);
});

test('bin/resolve-materialized-digest0.mjs exits nonzero without digest input', () => {
  const cliPath = fileURLToPath(new URL('../bin/resolve-materialized-digest0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'resolve-materialized-digest0');
  assert.equal(out.coord, 'resolve-materialized-digest0.args');
});

async function writeFixtures0(t) {
  const fixtureDir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-digest-resolver-'));

  t.after(async () => {
    await fs.rm(fixtureDir, {
      recursive: true,
      force: true,
    });
  });

  const writer = await WriteMaterializedFixtureSet0({
    outputDir: fixtureDir,
  });

  assert.equal(writer.tag, 'accept');

  return fixtureDir;
}