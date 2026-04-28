import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  ACCEPT_RUN_PHASES0,
  CheckAcceptRun0,
  EmitFinalVerdict0,
  ReplayAcceptRun0,
  makeSyntheticAcceptRun0,
  makeSyntheticRejectAcceptRun0,
} from '../pcc-accept-run0.mjs';

test('ReplayAcceptRun0 accepts the synthetic generated package by canonical byte equality', async () => {
  const out = await ReplayAcceptRun0(makeSyntheticAcceptRun0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'ReplayAcceptRun0');
  assert.equal(out.NF.kind, 'AcceptRunReplay0NF');
  assert.equal(out.Digest.alg, 'SHA256');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckAcceptRun0 accepts the synthetic final acceptance run', async () => {
  const out = await CheckAcceptRun0(makeSyntheticAcceptRun0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckAcceptRun0');
  assert.equal(out.NF.kind, 'AcceptRun0NF');
  assert.equal(out.NF.verdict, 'accept');
  assert.equal(out.NF.replayAccepted, true);
  assert.deepEqual(out.NF.phaseOrder, ACCEPT_RUN_PHASES0);
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
});

test('EmitFinalVerdict0 emits the conditional public conclusion for an accepted run', async () => {
  const out = await EmitFinalVerdict0(makeSyntheticAcceptRun0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'EmitFinalVerdict0');
  assert.equal(out.NF.kind, 'FinalVerdictEmission0NF');
  assert.equal(out.NF.verdict, 'accept');
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.equal(out.NF.publicConclusion.antecedent, 'CheckPCCPackexp(GeneratePCCPack())=accept');
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
});

test('CheckAcceptRun0 accepts a replayable reject run without emitting P equals NP', async () => {
  const out = await CheckAcceptRun0(makeSyntheticRejectAcceptRun0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckAcceptRun0');
  assert.equal(out.NF.verdict, 'reject');
  assert.equal(out.NF.replayAccepted, false);
  assert.equal(out.NF.publicConclusion, null);
  assert.equal(out.NF.rejectLogCount, 1);
});

test('EmitFinalVerdict0 emits no public theorem for a reject run', async () => {
  const out = await EmitFinalVerdict0(makeSyntheticRejectAcceptRun0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'EmitFinalVerdict0');
  assert.equal(out.NF.verdict, 'reject');
  assert.equal(out.NF.publicConclusionEmitted, false);
  assert.equal(out.NF.publicConclusion, null);
  assert.equal(out.NF.rejectionOnly, true);
});

test('ReplayAcceptRun0 rejects generator core canonical byte mismatch', async () => {
  const run = makeSyntheticAcceptRun0();

  run.GenCall = {
    ...run.GenCall,
    outputCoreBytes: '{"not":"the core"}',
  };

  const out = await ReplayAcceptRun0(run);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'ReplayAcceptRun0');
  assert.equal(out.Coord, 'ReplayAcceptRun0.generatorBytes');
  assert.deepEqual(out.Path, ['GenCall', 'outputCoreBytes']);
  assert.equal(out.Witness.reason, 'generated core package must match Pgen.Core by canonical byte equality');
});

test('CheckAcceptRun0 rejects an accept verdict when replay rejects', async () => {
  const run = makeSyntheticRejectAcceptRun0();

  run.Verdict = {
    ...run.Verdict,
    verdict: 'accept',
    conditional: true,
    publicConclusionEmitted: true,
    rejectionOnly: false,
    publicConclusion: {
      antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
      consequent: 'P = NP',
    },
  };

  const out = await CheckAcceptRun0(run);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckAcceptRun0');
  assert.equal(out.Coord, 'CheckAcceptRun0.verdict');
  assert.deepEqual(out.Path, ['Verdict', 'verdict']);
  assert.equal(out.Witness.reason, 'AcceptRun0 verdict must be reject when replay rejects');
});

test('CheckAcceptRun0 rejects bad phase order', async () => {
  const run = makeSyntheticAcceptRun0();

  run.PhaseOrder = [
    ...run.PhaseOrder,
  ];

  run.PhaseOrder[0] = 'Φ99.BadPhase';

  const out = await CheckAcceptRun0(run);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckAcceptRun0');
  assert.equal(out.Coord, 'CheckAcceptRun0.phaseOrder');
  assert.deepEqual(out.Path, ['PhaseOrder', 0]);
  assert.equal(out.Witness.reason, 'AcceptRun0 PhaseOrder mismatch');
});

test('CheckAcceptRun0 rejects digest-only package equality', async () => {
  const run = makeSyntheticAcceptRun0();

  run.AuditLogs = {
    ...run.AuditLogs,
    digestComparisonsOnly: true,
  };

  const out = await CheckAcceptRun0(run);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckAcceptRun0');
  assert.equal(out.Coord, 'CheckAcceptRun0.auditLogs');
  assert.deepEqual(out.Path, ['AuditLogs', 'digestComparisonsOnly']);
  assert.equal(out.Witness.reason, 'AcceptRun0 must not use digest equality as package equality');
});

test('CheckAcceptRun0 rejects executable hidden minimization in run metadata', async () => {
  const run = makeSyntheticAcceptRun0();

  run.Transcript = {
    ...run.Transcript,
    body: [
      'minimumEquivalent',
    ],
  };

  const out = await CheckAcceptRun0(run);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckAcceptRun0');
  assert.equal(out.Coord, 'CheckAcceptRun0.noHiddenMin');
  assert.deepEqual(out.Path, ['AcceptRun0', 'Transcript', 'body', 0]);
  assert.equal(out.Witness.reason, 'forbidden minimization symbol appears in executable position');
});

test('CheckAcceptRun0 rejects opaque proof material', async () => {
  const run = makeSyntheticAcceptRun0();

  run.PiRun = {
    ...run.PiRun,
    proofBlob: {
      bytes: 'not allowed',
    },
  };

  const out = await CheckAcceptRun0(run);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckAcceptRun0');
  assert.equal(out.Coord, 'CheckAcceptRun0.opaqueProof');
  assert.deepEqual(out.Path, ['AcceptRun0', 'PiRun', 'proofBlob']);
  assert.equal(out.Witness.reason, 'opaque proof material is not allowed in AcceptRun0');
});