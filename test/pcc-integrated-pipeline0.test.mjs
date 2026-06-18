import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckIntegratedPipeline0,
  INTEGRATED_PIPELINE_PHASES0,
  RunIntegratedPCC0,
  makeSyntheticIntegratedPipeline0,
} from '../pcc-integrated-pipeline0.mjs';

import {
  makeAuditCase,
} from '../pcc-verifier-frag0.mjs';

test('CheckIntegratedPipeline0 accepts the synthetic full-stack pipeline', async () => {
  const out = await CheckIntegratedPipeline0(makeSyntheticIntegratedPipeline0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckIntegratedPipeline0');
  assert.equal(out.NF.kind, 'IntegratedPipeline0NF');
  assert.deepEqual(out.NF.phaseOrder, INTEGRATED_PIPELINE_PHASES0);
  assert.equal(out.NF.phaseCount, INTEGRATED_PIPELINE_PHASES0.length);
  assert.equal(out.NF.finalVerdict, 'accept');
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
  assert.equal(out.Digest.alg, 'SHA256');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('RunIntegratedPCC0 is an alias for the integrated pipeline checker', async () => {
  const out = await RunIntegratedPCC0(makeSyntheticIntegratedPipeline0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckIntegratedPipeline0');
});

test('CheckIntegratedPipeline0 is deterministic on fresh synthetic pipelines', async () => {
  const first = await CheckIntegratedPipeline0(makeSyntheticIntegratedPipeline0());
  const second = await CheckIntegratedPipeline0(makeSyntheticIntegratedPipeline0());

  assert.equal(first.tag, 'accept');
  assert.equal(second.tag, 'accept');
  assert.deepEqual(first.Digest, second.Digest);
});

test('CheckIntegratedPipeline0 rejects at CheckVerifierFrag0 first when the verifier audit fails', async () => {
  const pipeline = makeSyntheticIntegratedPipeline0();

  pipeline.VerifierFrag0 = {
    kind: 'VerifierFrag0',
    version: 0,
    suiteId: 'integrated.pipeline.bad-verifier',
    cases: [
      makeAuditCase({
        id: 'integrated.bad-verifier',
        target: 'IntegratedPipeline0',
        run: () => ({
          pass: false,
          reason: 'synthetic verifier failure',
        }),
      }),
    ],
  };

  const out = await CheckIntegratedPipeline0(pipeline);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckIntegratedPipeline0');
  assert.equal(out.Coord, 'CheckIntegratedPipeline0.CheckVerifierFrag0');
  assert.deepEqual(out.Path, ['VerifierFrag0']);
  assert.equal(out.Witness.reason, 'CheckVerifierFrag0 rejected');
  assert.equal(out.Witness.detail.inner.checker, 'CheckVerifierFrag0');
});

test('CheckIntegratedPipeline0 rejects at CheckGPack0 before package sufficiency when locked NAND is bad', async () => {
  const pipeline = makeSyntheticIntegratedPipeline0();

  pipeline.PCCPack.GPack = {
    ...pipeline.PCCPack.GPack,
    ThresholdCert: {
      ...pipeline.PCCPack.GPack.ThresholdCert,
      residualSlackMax: 5,
    },
  };

  const out = await CheckIntegratedPipeline0(pipeline);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckIntegratedPipeline0');
  assert.equal(out.Coord, 'CheckIntegratedPipeline0.CheckGPack0');
  assert.deepEqual(out.Path, ['PCCPack', 'GPack']);
  assert.equal(out.Witness.reason, 'CheckGPack0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckGPack0.threshold');
});

test('CheckIntegratedPipeline0 rejects if AcceptRun Pgen is not the integrated PCCPack', async () => {
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

  const out = await CheckIntegratedPipeline0(pipeline);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckIntegratedPipeline0');
  assert.equal(out.Coord, 'CheckIntegratedPipeline0.BindAcceptRunPgen0');
  assert.deepEqual(out.Path, ['AcceptRun', 'Pgen']);
  assert.equal(out.Witness.reason, 'AcceptRun Pgen must match the integrated PCCPack by canonical byte equality');
});

test('CheckIntegratedPipeline0 rejects generator canonical byte mismatch during replay', async () => {
  const pipeline = makeSyntheticIntegratedPipeline0();

  pipeline.AcceptRun = {
    ...pipeline.AcceptRun,
    GenCall: {
      ...pipeline.AcceptRun.GenCall,
      outputPackBytes: '{"not":"the pack"}',
    },
  };

  const out = await CheckIntegratedPipeline0(pipeline);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckIntegratedPipeline0');
  assert.equal(out.Coord, 'CheckIntegratedPipeline0.ReplayAcceptRun0');
  assert.deepEqual(out.Path, ['AcceptRun']);
  assert.equal(out.Witness.reason, 'ReplayAcceptRun0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'ReplayAcceptRun0.generatorBytes');
});

test('CheckIntegratedPipeline0 rejects bad integrated phase order', async () => {
  const pipeline = makeSyntheticIntegratedPipeline0();

  pipeline.PhaseOrder = [
    ...pipeline.PhaseOrder,
  ];

  pipeline.PhaseOrder[0] = 'BadPhase';

  const out = await CheckIntegratedPipeline0(pipeline);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckIntegratedPipeline0');
  assert.equal(out.Coord, 'CheckIntegratedPipeline0.input');
  assert.deepEqual(out.Path, ['PhaseOrder', 0]);
  assert.equal(out.Witness.reason, 'IntegratedPipeline0 PhaseOrder mismatch');
});