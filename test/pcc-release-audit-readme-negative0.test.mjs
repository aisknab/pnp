import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckReadmeReleaseBoundary0,
} from '../pcc-readme-release-boundary0.mjs';

import {
  CheckReleaseAudit0,
  makeReleaseAuditConfig0,
} from '../pcc-release-audit0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

async function currentReadme0() {
  return fs.readFile(new URL('../README.md', import.meta.url), 'utf8');
}

function makeReadmeBoundaryAcceptRecord0(overrides = {}) {
  const nf = {
    kind: 'ReadmeReleaseBoundary0NF',
    checker: 'CheckReadmeReleaseBoundary0',
    version: 0,
    readmePath: '<synthetic>',
    byteLength: 1024,
    requiredSnippetCount: 20,
    forbiddenSnippetCount: 8,
    readmeTextDigest: digestCanonical0('synthetic-readme'),
    conditionalClaimBoundaryFrozen: true,
    staleLayoutWordingRejected: true,
    ...overrides,
  };

  const digest = digestCanonical0(nf);

  return {
    tag: 'accept',
    kind: 'accept',
    checker: 'CheckReadmeReleaseBoundary0',
    version: 0,
    NF: nf,
    Digest: digest,
    Ledger: [],
    nf,
    digest,
    ledger: [],
  };
}

async function runReleaseAuditWithReadmeRunner0(readmeReleaseBoundaryRunner, overrides = {}) {
  return CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    readmeReleaseBoundaryRunner,
    ...overrides,
  }));
}

test('CheckReleaseAudit0 rejects stale layout wording through README boundary runner', async () => {
  const readme = await currentReadme0();

  const out = await runReleaseAuditWithReadmeRunner0(() => CheckReadmeReleaseBoundary0({
    readmeText: `${readme}\nThe release audit checks stale duplicate ES modules under \`src\`.\n`,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.readme');
  assert.deepEqual(out.Path, ['README.md']);
  assert.equal(out.Witness.reason, 'README release boundary checker rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckReadmeReleaseBoundary0.forbiddenSnippet');
  assert.equal(out.Witness.detail.inner.witness.detail.snippet, 'stale duplicate ES modules under `src`');
});

test('CheckReleaseAudit0 rejects active legacy layout wording through README boundary runner', async () => {
  const readme = await currentReadme0();

  const out = await runReleaseAuditWithReadmeRunner0(() => CheckReadmeReleaseBoundary0({
    readmeText: `${readme}\nThe active implementation lives in the src folder.\n`,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.readme');
  assert.equal(out.Witness.reason, 'README release boundary checker rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckReadmeReleaseBoundary0.forbiddenSnippet');
  assert.equal(out.Witness.detail.inner.witness.detail.snippet, 'src folder');
});

test('CheckReleaseAudit0 rejects overclaiming theorem wording through README boundary runner', async () => {
  const readme = await currentReadme0();

  const out = await runReleaseAuditWithReadmeRunner0(() => CheckReadmeReleaseBoundary0({
    readmeText: `${readme}\nP = NP is established.\n`,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.readme');
  assert.equal(out.Witness.reason, 'README release boundary checker rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckReadmeReleaseBoundary0.forbiddenSnippet');
  assert.equal(out.Witness.detail.inner.witness.detail.snippet, 'P = NP is established');
});

test('CheckReleaseAudit0 rejects missing conditional claim through README boundary runner', async () => {
  const readme = await currentReadme0();
  const centralClaim = 'CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP';
  const mutatedReadme = readme.split(centralClaim).join('missing conditional claim');

  const out = await runReleaseAuditWithReadmeRunner0(() => CheckReadmeReleaseBoundary0({
    readmeText: mutatedReadme,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.readme');
  assert.equal(out.Witness.reason, 'README release boundary checker rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckReadmeReleaseBoundary0.requiredSnippet');
  assert.equal(out.Witness.detail.inner.witness.detail.snippet, centralClaim);
});

test('CheckReleaseAudit0 rejects README boundary runner accept record without NF', async () => {
  const out = await runReleaseAuditWithReadmeRunner0(() => ({
    tag: 'accept',
    kind: 'accept',
    checker: 'CheckReadmeReleaseBoundary0',
    version: 0,
    Digest: digestCanonical0({
      kind: 'MissingReadmeBoundaryNF',
    }),
    Ledger: [],
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.readme');
  assert.deepEqual(out.Path, ['README.md', 'NF']);
  assert.equal(out.Witness.reason, 'README release boundary checker must emit an NF object');
});

test('CheckReleaseAudit0 rejects README boundary runner accept record with wrong NF kind', async () => {
  const out = await runReleaseAuditWithReadmeRunner0(() => makeReadmeBoundaryAcceptRecord0({
    kind: 'WrongReadmeBoundaryNF',
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.readme');
  assert.deepEqual(out.Path, ['README.md', 'NF', 'kind']);
  assert.equal(out.Witness.reason, 'README release boundary checker emitted the wrong NF kind');
});

test('CheckReleaseAudit0 rejects README boundary runner accept record without conditional claim certification', async () => {
  const out = await runReleaseAuditWithReadmeRunner0(() => makeReadmeBoundaryAcceptRecord0({
    conditionalClaimBoundaryFrozen: false,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.readme');
  assert.deepEqual(out.Path, ['README.md', 'NF', 'conditionalClaimBoundaryFrozen']);
  assert.equal(out.Witness.reason, 'README release boundary checker must certify conditionalClaimBoundaryFrozen=true');
});

test('CheckReleaseAudit0 rejects README boundary runner accept record without stale-layout rejection certification', async () => {
  const out = await runReleaseAuditWithReadmeRunner0(() => makeReadmeBoundaryAcceptRecord0({
    staleLayoutWordingRejected: false,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.readme');
  assert.deepEqual(out.Path, ['README.md', 'NF', 'staleLayoutWordingRejected']);
  assert.equal(out.Witness.reason, 'README release boundary checker must certify staleLayoutWordingRejected=true');
});

test('CheckReleaseAudit0 rejects README boundary runner accept record with zero required snippet count', async () => {
  const out = await runReleaseAuditWithReadmeRunner0(() => makeReadmeBoundaryAcceptRecord0({
    requiredSnippetCount: 0,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.readme');
  assert.deepEqual(out.Path, ['README.md', 'NF', 'requiredSnippetCount']);
  assert.equal(out.Witness.reason, 'README release boundary checker must count required snippets');
});

test('CheckReleaseAudit0 rejects README boundary runner accept record with zero forbidden snippet count', async () => {
  const out = await runReleaseAuditWithReadmeRunner0(() => makeReadmeBoundaryAcceptRecord0({
    forbiddenSnippetCount: 0,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.readme');
  assert.deepEqual(out.Path, ['README.md', 'NF', 'forbiddenSnippetCount']);
  assert.equal(out.Witness.reason, 'README release boundary checker must count forbidden snippets');
});

test('CheckReleaseAudit0 validates README boundary runner config shape', async () => {
  const out = await CheckReleaseAudit0({
    ...makeReleaseAuditConfig0(),
    readmeReleaseBoundaryRunner: 'not a function',
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.input');
  assert.deepEqual(out.Path, ['readmeReleaseBoundaryRunner']);
  assert.equal(out.Witness.reason, 'ReleaseAuditConfig0 readmeReleaseBoundaryRunner must be null or a function');
});

test('README documents release audit README negative integration', async () => {
  const readme = await currentReadme0();

  assert.equal(readme.includes('Release audit README negative integration'), true);
  assert.equal(readme.includes('CheckReadmeReleaseBoundary0'), true);
  assert.equal(readme.includes('CheckReleaseAudit0.readme'), true);
  assert.equal(readme.includes('stale layout wording'), true);
  assert.equal(readme.includes('overclaiming theorem wording'), true);
});