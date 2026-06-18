import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckReadmeReleaseBoundary0,
  README_RELEASE_BOUNDARY_FORBIDDEN_SNIPPETS0,
  README_RELEASE_BOUNDARY_REQUIRED_SNIPPETS0,
} from '../pcc-readme-release-boundary0.mjs';

import {
  CheckReleaseAudit0,
  makeReleaseAuditConfig0,
} from '../pcc-release-audit0.mjs';

async function currentReadme0() {
  return fs.readFile(new URL('../README.md', import.meta.url), 'utf8');
}

test('CheckReadmeReleaseBoundary0 accepts the current README release-boundary wording', async () => {
  const out = await CheckReadmeReleaseBoundary0();

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckReadmeReleaseBoundary0');
  assert.equal(out.NF.kind, 'ReadmeReleaseBoundary0NF');
  assert.equal(out.NF.requiredSnippetCount, README_RELEASE_BOUNDARY_REQUIRED_SNIPPETS0.length);
  assert.equal(out.NF.forbiddenSnippetCount, README_RELEASE_BOUNDARY_FORBIDDEN_SNIPPETS0.length);
  assert.equal(out.NF.conditionalClaimBoundaryFrozen, true);
  assert.equal(out.NF.staleLayoutWordingRejected, true);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckReadmeReleaseBoundary0 rejects a missing central conditional claim', async () => {
  const readme = await currentReadme0();
  const centralClaim = 'CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP';

  const mutatedReadme = readme.split(centralClaim).join('missing conditional claim');

  assert.equal(mutatedReadme.includes(centralClaim), false);

  const out = await CheckReadmeReleaseBoundary0({
    readmeText: mutatedReadme,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReadmeReleaseBoundary0');
  assert.equal(out.Coord, 'CheckReadmeReleaseBoundary0.requiredSnippet');
  assert.equal(out.Witness.reason, 'README release boundary wording is missing a required snippet');
  assert.equal(out.Witness.detail.snippet, centralClaim);
});

test('CheckReadmeReleaseBoundary0 rejects stale layout wording about legacy src structure', async () => {
  const readme = await currentReadme0();
  const out = await CheckReadmeReleaseBoundary0({
    readmeText: `${readme}\nThe release audit checks stale duplicate ES modules under \`src\`.\n`,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReadmeReleaseBoundary0');
  assert.equal(out.Coord, 'CheckReadmeReleaseBoundary0.forbiddenSnippet');
  assert.equal(out.Witness.reason, 'README release boundary wording contains a forbidden stale or overclaiming snippet');
  assert.equal(out.Witness.detail.snippet, 'stale duplicate ES modules under `src`');
});

test('CheckReadmeReleaseBoundary0 rejects active src-folder wording', async () => {
  const readme = await currentReadme0();
  const out = await CheckReadmeReleaseBoundary0({
    readmeText: `${readme}\nThe active implementation lives in the src folder.\n`,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReadmeReleaseBoundary0');
  assert.equal(out.Coord, 'CheckReadmeReleaseBoundary0.forbiddenSnippet');
  assert.equal(out.Witness.detail.snippet, 'src folder');
});

test('CheckReadmeReleaseBoundary0 rejects unconditional P equals NP overclaims', async () => {
  const readme = await currentReadme0();
  const out = await CheckReadmeReleaseBoundary0({
    readmeText: `${readme}\nP = NP is established.\n`,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReadmeReleaseBoundary0');
  assert.equal(out.Coord, 'CheckReadmeReleaseBoundary0.forbiddenSnippet');
  assert.equal(out.Witness.detail.snippet, 'P = NP is established');
});

test('CheckReleaseAudit0 readme phase uses the README release-boundary checker', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
  }));

  assert.equal(out.tag, 'accept');

  const readmeLedger = out.Ledger.find((entry) => entry.phase === 'readme');

  assert.equal(readmeLedger.status, 'pass');
});

test('README documents the README wording freeze checker and excludes stale src prose', async () => {
  const readme = await currentReadme0();

  assert.equal(readme.includes('Release audit README wording freeze'), true);
  assert.equal(readme.includes('CheckReadmeReleaseBoundary0'), true);
  assert.equal(readme.includes('conditional theorem boundary'), true);
  assert.equal(readme.includes('stale-layout exclusions'), true);
  assert.equal(readme.includes('stale duplicate ES modules under `src`'), false);
  assert.equal(readme.includes('src folder'), false);
});