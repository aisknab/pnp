import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckRunAll0,
  RUNALL_CHECKER_COVERAGE0,
  RUNALL_PUBLIC_CONCLUSION0,
  RunAll0,
  makeSyntheticRunAllInput0,
} from '../pcc-runall0.mjs';

import {
  INTEGRATED_PIPELINE_PHASES0,
  makeSyntheticIntegratedPipeline0,
} from '../pcc-integrated-pipeline0.mjs';

test('RunAll0 accepts the synthetic full-stack public status artefact', async () => {
  const out = await RunAll0();

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'RunAll0');
  assert.equal(out.NF.kind, 'RunAll0StatusNF');
  assert.equal(out.NF.status, 'complete');
  assert.equal(out.NF.claimBoundary, 'conditional-on-accepted-generated-package');
  assert.deepEqual(out.NF.phaseOrder, INTEGRATED_PIPELINE_PHASES0);
  assert.deepEqual(out.NF.publicConclusion, RUNALL_PUBLIC_CONCLUSION0);
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.equal(out.NF.finalVerdict, 'accept');
  assert.equal(out.NF.checkerCount, RUNALL_CHECKER_COVERAGE0.length);
  assert.equal(out.Digest.alg, 'SHA256');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckRunAll0 accepts an explicit synthetic RunAll input', async () => {
  const out = await CheckRunAll0(makeSyntheticRunAllInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'RunAll0');
  assert.equal(out.NF.phaseCount, INTEGRATED_PIPELINE_PHASES0.length);
});

test('RunAll0 accepts a direct IntegratedPipeline0 object', async () => {
  const pipeline = makeSyntheticIntegratedPipeline0();
  const out = await RunAll0(pipeline);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'RunAll0');
  assert.equal(out.NF.finalVerdict, 'accept');
});

test('RunAll0 is deterministic on fresh synthetic inputs', async () => {
  const first = await RunAll0();
  const second = await RunAll0();

  assert.equal(first.tag, 'accept');
  assert.equal(second.tag, 'accept');
  assert.deepEqual(first.Digest, second.Digest);
});

test('RunAll0 rejects an integrated pipeline phase-order mismatch', async () => {
  const pipeline = makeSyntheticIntegratedPipeline0();

  pipeline.PhaseOrder = [
    ...pipeline.PhaseOrder,
  ];

  pipeline.PhaseOrder[0] = 'BadPhase';

  const out = await RunAll0(pipeline);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'RunAll0');
  assert.equal(out.Coord, 'RunAll0.integrated');
  assert.deepEqual(out.Path, ['Pipeline']);
  assert.equal(out.Witness.reason, 'CheckIntegratedPipeline0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckIntegratedPipeline0.input');
});

test('RunAll0 rejects if AcceptRun Pgen does not match integrated PCCPack', async () => {
  const pipeline = makeSyntheticIntegratedPipeline0();

  pipeline.AcceptRun = {
    ...pipeline.AcceptRun,
    Pgen: {
      ...pipeline.AcceptRun.Pgen,
      Core: {
        ...pipeline.AcceptRun.Pgen.Core,
        canonicalByteEquality: false,
      },
    },
  };

  const out = await RunAll0(pipeline);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'RunAll0');
  assert.equal(out.Coord, 'RunAll0.integrated');
  assert.deepEqual(out.Path, ['Pipeline']);
  assert.equal(out.Witness.reason, 'CheckIntegratedPipeline0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckIntegratedPipeline0.BindAcceptRunPgen0');
});

test('RunAll0 rejects if generator output bytes do not match the generated package', async () => {
  const pipeline = makeSyntheticIntegratedPipeline0();

  pipeline.AcceptRun = {
    ...pipeline.AcceptRun,
    GenCall: {
      ...pipeline.AcceptRun.GenCall,
      outputPackBytes: '{"not":"the pack"}',
    },
  };

  const out = await RunAll0(pipeline);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'RunAll0');
  assert.equal(out.Coord, 'RunAll0.integrated');
  assert.deepEqual(out.Path, ['Pipeline']);
  assert.equal(out.Witness.reason, 'CheckIntegratedPipeline0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckIntegratedPipeline0.ReplayAcceptRun0');
});

test('RunAll0 rejects if required checker coverage is missing', async () => {
  const input = makeSyntheticRunAllInput0({
    RequiredCheckers: RUNALL_CHECKER_COVERAGE0.filter((checker) => checker !== 'CheckGPack0'),
  });

  const out = await RunAll0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'RunAll0');
  assert.equal(out.Coord, 'RunAll0.input');
  assert.deepEqual(out.Path, ['RequiredCheckers']);
  assert.equal(out.Witness.reason, 'RunAllInput0 RequiredCheckers is missing required checker names');
});