import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckMinimalKernel0,
  MINIMAL_KERNEL_REMAINING_BLOCKERS0,
  MINIMAL_KERNEL_REQUIRED_CHECKERS0,
  MINIMAL_KERNEL_REQUIRED_SPINE_IDS0,
  PNP_MINIMAL_KERNEL0,
  PNP_MINIMAL_KERNEL_COORDINATE0,
  makeMinimalKernelInput0,
} from '../pcc-minimal-kernel0.mjs';

async function loadKernelJson0() {
  const bytes = await readFile(new URL('../kernel/PNP_MINIMAL_KERNEL.json', import.meta.url), 'utf8');
  return JSON.parse(bytes);
}

function deepClone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('minimal kernel JSON accepts and keeps theorem emission disabled', async () => {
  const kernel = await loadKernelJson0();
  const out = await CheckMinimalKernel0(makeMinimalKernelInput0({ Kernel: kernel }));

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.coordinate, PNP_MINIMAL_KERNEL_COORDINATE0);
  assert.equal(out.NF.minimalKernelReady, true);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.remainingBlockers, [...MINIMAL_KERNEL_REMAINING_BLOCKERS0]);
  assert.equal(out.NF.checkerSurfaceCount, MINIMAL_KERNEL_REQUIRED_CHECKERS0.length);
  assert.equal(out.NF.proofSpineCount, MINIMAL_KERNEL_REQUIRED_SPINE_IDS0.length);
  assert.equal(out.NF.kernelDigest.hex.length, 64);
});

test('minimal kernel constructor exposes the small proof-spine entrypoint', async () => {
  const out = await CheckMinimalKernel0();

  assert.equal(out.tag, 'accept');
  assert.equal(PNP_MINIMAL_KERNEL0.coordinate, PNP_MINIMAL_KERNEL_COORDINATE0);
  assert.equal(PNP_MINIMAL_KERNEL0.entrypoints.kernelJson, 'kernel/PNP_MINIMAL_KERNEL.json');
  assert.equal(PNP_MINIMAL_KERNEL0.entrypoints.theoremBindingLedger, 'report-bindings/REPORT_THEOREM_BINDINGS.json');
  assert.deepEqual(PNP_MINIMAL_KERNEL0.claimBoundary.activeFinalNodeIds, []);
  assert.deepEqual(PNP_MINIMAL_KERNEL0.claimBoundary.remainingBlockers, MINIMAL_KERNEL_REMAINING_BLOCKERS0);
  assert.equal(PNP_MINIMAL_KERNEL0.proofSpine.length, MINIMAL_KERNEL_REQUIRED_SPINE_IDS0.length);
});

test('minimal kernel checker rejects caller-supplied readiness assertions', async () => {
  const input = {
    ...makeMinimalKernelInput0(),
    publicTheoremEmissionAllowed: true,
  };
  const out = await CheckMinimalKernel0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckMinimalKernel0.input');
  assert.deepEqual(out.Path, ['publicTheoremEmissionAllowed']);
  assert.equal(out.Witness.reason, 'minimal kernel checker rejects caller-supplied readiness or truth assertions');
});

test('minimal kernel checker rejects theorem-emission boundary mutation', async () => {
  const kernel = deepClone0(await loadKernelJson0());
  kernel.claimBoundary.publicTheoremEmissionAllowed = true;
  const out = await CheckMinimalKernel0(makeMinimalKernelInput0({ Kernel: kernel }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckMinimalKernel0.kernel');
  assert.deepEqual(out.Path, ['claimBoundary', 'publicTheoremEmissionAllowed']);
});

test('minimal kernel checker rejects missing primitive rule coverage', async () => {
  const kernel = deepClone0(await loadKernelJson0());
  kernel.proofKernel.primitiveRules = kernel.proofKernel.primitiveRules.slice(1);
  const out = await CheckMinimalKernel0(makeMinimalKernelInput0({ Kernel: kernel }));

  assert.equal(out.tag, 'reject');
  assert.deepEqual(out.Path, ['proofKernel', 'primitiveRules']);
});

test('minimal kernel checker rejects proof-spine checker ids outside the checker surface', async () => {
  const kernel = deepClone0(await loadKernelJson0());
  kernel.proofSpine[0].checkerIds = ['CheckVerifierFrag0', 'CheckMissingKernel0'];
  const out = await CheckMinimalKernel0(makeMinimalKernelInput0({ Kernel: kernel }));

  assert.equal(out.tag, 'reject');
  assert.deepEqual(out.Path, ['proofSpine', 0, 'checkerIds']);
});

test('minimal kernel checker is total on malformed inputs', async () => {
  const out = await CheckMinimalKernel0(null);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckMinimalKernel0.input');
  assert.deepEqual(out.Path, []);
});
