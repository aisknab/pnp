import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import { test } from 'node:test';
import { CheckReadmeReleaseBoundary0, README_RELEASE_BOUNDARY_FORBIDDEN_SNIPPETS0, README_RELEASE_BOUNDARY_REQUIRED_SNIPPETS0 } from '../pcc-readme-release-boundary0.mjs';
import { CheckReleaseAudit0, makeReleaseAuditConfig0 } from '../pcc-release-audit0.mjs';

async function currentReadme0() { return fs.readFile(new URL('../README.md', import.meta.url), 'utf8'); }

test('CheckReadmeReleaseBoundary0 accepts the formal reconstruction boundary', async () => {
  const out = await CheckReadmeReleaseBoundary0();
  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.kind, 'ReadmeReleaseBoundary0NF');
  assert.equal(out.NF.requiredSnippetCount, README_RELEASE_BOUNDARY_REQUIRED_SNIPPETS0.length);
  assert.equal(out.NF.forbiddenSnippetCount, README_RELEASE_BOUNDARY_FORBIDDEN_SNIPPETS0.length);
  assert.equal(out.NF.conditionalClaimBoundaryFrozen, true);
  assert.equal(out.NF.formalReconstructionBoundaryFrozen, true);
  assert.equal(out.NF.publicTheoremEmissionDisabled, true);
  assert.equal(out.NF.legacyActivationSuperseded, true);
  assert.equal(out.NF.staleLayoutWordingRejected, true);
  assert.equal(out.NF.overclaimingWordingRejected, true);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckReadmeReleaseBoundary0 rejects a missing non-activation statement', async () => {
  const readme = await currentReadme0();
  const required = 'public theorem emission is disabled';
  const out = await CheckReadmeReleaseBoundary0({ readmeText: readme.split(required).join('status omitted') });
  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckReadmeReleaseBoundary0.requiredSnippet');
  assert.equal(out.Witness.reason, 'README release boundary wording is missing a required snippet');
  assert.equal(out.Witness.detail.snippet, required);
});

test('CheckReadmeReleaseBoundary0 rejects a missing historical conditional record', async () => {
  const readme = await currentReadme0();
  const historical = 'CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP';
  const out = await CheckReadmeReleaseBoundary0({ readmeText: readme.split(historical).join('historical record omitted') });
  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckReadmeReleaseBoundary0.requiredSnippet');
  assert.equal(out.Witness.detail.snippet, historical);
});

test('CheckReadmeReleaseBoundary0 rejects stale layout wording', async () => {
  const readme = await currentReadme0();
  const out = await CheckReadmeReleaseBoundary0({ readmeText: `${readme}\nThe release audit checks stale duplicate ES modules under \`src\`.\n` });
  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckReadmeReleaseBoundary0.forbiddenSnippet');
  assert.equal(out.Witness.detail.snippet, 'stale duplicate ES modules under `src`');
});

test('CheckReadmeReleaseBoundary0 rejects theorem activation wording', async () => {
  const readme = await currentReadme0();
  const out = await CheckReadmeReleaseBoundary0({ readmeText: `${readme}\npublicTheoremEmissionAllowed = true\n` });
  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckReadmeReleaseBoundary0.forbiddenSnippet');
  assert.equal(out.Witness.detail.snippet, 'publicTheoremEmissionAllowed = true');
});

test('CheckReadmeReleaseBoundary0 rejects unconditional P equals NP overclaims', async () => {
  const readme = await currentReadme0();
  const out = await CheckReadmeReleaseBoundary0({ readmeText: `${readme}\nP = NP is established.\n` });
  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckReadmeReleaseBoundary0.forbiddenSnippet');
  assert.equal(out.Witness.detail.snippet, 'P = NP is established');
});

test('CheckReleaseAudit0 readme phase uses the reconstruction boundary checker', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({ runSyntaxCheck: false, runRunAll: false, runMutationCheck: false, runCliSmoke: false, runPublicSurfaceFreeze: false, runMaterializedPublicStatusGate: false }));
  assert.equal(out.tag, 'accept');
  assert.equal(out.Ledger.find((entry) => entry.phase === 'readme').status, 'pass');
});

test('README documents the reconstruction boundary and checker', async () => {
  const readme = await currentReadme0();
  assert.equal(readme.includes('formal reconstruction gate'), true);
  assert.equal(readme.includes('status/FORMAL_RECONSTRUCTION_STATUS.json'), true);
  assert.equal(readme.includes('public theorem emission is disabled'), true);
  assert.equal(readme.includes('P = NP is established'), false);
  assert.equal(readme.includes('publicTheoremEmissionAllowed = true'), false);
});
