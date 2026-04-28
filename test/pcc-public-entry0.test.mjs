import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  RUNALL_CHECKER_COVERAGE0,
  RUNALL_PUBLIC_CONCLUSION0,
  RunAll0,
} from '../index.mjs';

test('public index exports RunAll0 and the public conditional conclusion', async () => {
  const out = await RunAll0();

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'RunAll0');
  assert.equal(out.NF.status, 'complete');
  assert.deepEqual(out.NF.publicConclusion, RUNALL_PUBLIC_CONCLUSION0);
  assert.equal(out.NF.publicConclusion.antecedent, 'CheckPCCPackexp(GeneratePCCPack())=accept');
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
});

test('public checker coverage includes the final replay and verdict layers', () => {
  assert.equal(RUNALL_CHECKER_COVERAGE0.includes('ReplayAcceptRun0'), true);
  assert.equal(RUNALL_CHECKER_COVERAGE0.includes('CheckAcceptRun0'), true);
  assert.equal(RUNALL_CHECKER_COVERAGE0.includes('EmitFinalVerdict0'), true);
  assert.equal(RUNALL_CHECKER_COVERAGE0.includes('RunAll0'), true);
});

test('bin/runall0.mjs emits an accepted public status summary', () => {
  const cliPath = fileURLToPath(new URL('../bin/runall0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, child.stderr);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'RunAll0');
  assert.equal(out.status, 'complete');
  assert.equal(out.claimBoundary, 'conditional-on-accepted-generated-package');
  assert.equal(out.finalVerdict, 'accept');
  assert.equal(out.publicConclusionEmitted, true);
  assert.equal(out.publicConclusion.antecedent, 'CheckPCCPackexp(GeneratePCCPack())=accept');
  assert.equal(out.publicConclusion.consequent, 'P = NP');
  assert.match(out.digest.hex, /^[0-9a-f]{64}$/);
});

test('bin/runall0.mjs --full emits the full accept record', () => {
  const cliPath = fileURLToPath(new URL('../bin/runall0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--full'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, child.stderr);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'RunAll0');
  assert.equal(out.NF.kind, 'RunAll0StatusNF');
  assert.equal(Array.isArray(out.Ledger), true);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});