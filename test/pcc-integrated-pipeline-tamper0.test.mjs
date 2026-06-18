import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  RunAll0,
} from '../pcc-runall0.mjs';

import {
  makeSyntheticIntegratedPipeline0,
} from '../pcc-integrated-pipeline0.mjs';

import {
  makeAuditCase,
} from '../pcc-verifier-frag0.mjs';

const TAMPER_CASES0 = Object.freeze([
  Object.freeze({
    name: 'VerifierFrag0 tamper rejects at CheckVerifierFrag0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.CheckVerifierFrag0',
    mutate: (pipeline) => {
      pipeline.VerifierFrag0 = {
        kind: 'VerifierFrag0',
        version: 0,
        suiteId: 'tamper.verifier.frag0',
        cases: [
          makeAuditCase({
            id: 'tamper.verifier.fail',
            target: 'IntegratedPipeline0',
            run: () => ({
              pass: false,
              reason: 'synthetic verifier tamper',
            }),
          }),
        ],
      };
    },
  }),

  Object.freeze({
    name: 'Boot0 tamper rejects at CheckBoot0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.CheckBoot0',
    mutate: (pipeline) => {
      pipeline.PCCPack.Boot0.Sched0 = {
        ...pipeline.PCCPack.Boot0.Sched0,
        core: {
          ...pipeline.PCCPack.Boot0.Sched0.core,
          B0: 63,
        },
      };
    },
  }),

  Object.freeze({
    name: 'KBundle tamper rejects at CheckKBundle0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.CheckKBundle0',
    mutate: (pipeline) => {
      pipeline.PCCPack.KBundle.KImpl = {
        ...pipeline.PCCPack.KBundle.KImpl,
        RuleTable: pipeline.PCCPack.KBundle.KImpl.RuleTable.filter((rule) => rule.name !== 'Hall'),
      };
    },
  }),

  Object.freeze({
    name: 'HardCheck tamper rejects at CheckHard0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.CheckHard0',
    mutate: (pipeline) => {
      pipeline.PCCPack.HardCheck = {
        ...pipeline.PCCPack.HardCheck,
        DiagCheck: {
          ...pipeline.PCCPack.HardCheck.DiagCheck,
          noUnknown: false,
        },
      };
    },
  }),

  Object.freeze({
    name: 'RowPack tamper rejects at CheckRows0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.CheckRows0',
    mutate: (pipeline) => {
      pipeline.PCCPack.RowPack = {
        ...pipeline.PCCPack.RowPack,
        Rows: pipeline.PCCPack.RowPack.Rows.filter((row) => row.FamilyID !== 'PkgC'),
      };
    },
  }),

  Object.freeze({
    name: 'GlobalProofDAG tamper rejects at CheckGlobalProofDAG0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.CheckGlobalProofDAG0',
    mutate: (pipeline) => {
      pipeline.PCCPack.GlobalProofDAG = {
        ...pipeline.PCCPack.GlobalProofDAG,
        Nodes: pipeline.PCCPack.GlobalProofDAG.Nodes.filter((node) => node.id !== 'Row.PkgC'),
      };
    },
  }),

  Object.freeze({
    name: 'LocalPackages tamper rejects at CheckLocalPackages0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.CheckLocalPackages0',
    mutate: (pipeline) => {
      pipeline.PCCPack.LocalPackages = {
        ...pipeline.PCCPack.LocalPackages,
        Packages: pipeline.PCCPack.LocalPackages.Packages.filter((entry) => entry.family !== 'PkgC'),
      };
    },
  }),

  Object.freeze({
    name: 'GlobalFirewalls tamper rejects at CheckGlobalFirewalls0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.CheckGlobalFirewalls0',
    mutate: (pipeline) => {
      pipeline.PCCPack.GlobalFirewalls = {
        ...pipeline.PCCPack.GlobalFirewalls,
        ImportGraph: {
          ...pipeline.PCCPack.GlobalFirewalls.ImportGraph,
          edges: [
            ...pipeline.PCCPack.GlobalFirewalls.ImportGraph.edges,
            {
              from: 'O',
              to: 'G',
              kind: 'Import',
            },
          ],
        },
      };
    },
  }),

  Object.freeze({
    name: 'GPack tamper rejects at CheckGPack0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.CheckGPack0',
    mutate: (pipeline) => {
      pipeline.PCCPack.GPack = {
        ...pipeline.PCCPack.GPack,
        ThresholdCert: {
          ...pipeline.PCCPack.GPack.ThresholdCert,
          residualSlackMax: 5,
        },
      };
    },
  }),

  Object.freeze({
    name: 'RowFamG tamper rejects at CheckRowFamG0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.CheckRowFamG0',
    mutate: (pipeline) => {
      pipeline.PCCPack.RowFamG = {
        ...pipeline.PCCPack.RowFamG,
        rows: pipeline.PCCPack.RowFamG.rows.filter((row) => row.rowKind !== 'ThresholdCert'),
      };
    },
  }),

  Object.freeze({
    name: 'FinalIntegration tamper rejects at CheckFinalIntegration0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.CheckFinalIntegration0',
    mutate: (pipeline) => {
      pipeline.PCCPack.FinalIntegration = {
        ...pipeline.PCCPack.FinalIntegration,
        SATDecision: {
          ...pipeline.PCCPack.FinalIntegration.SATDecision,
          Baseline: {
            ...pipeline.PCCPack.FinalIntegration.SATDecision.Baseline,
            value: pipeline.PCCPack.FinalIntegration.SATDecision.Baseline.value + 1,
          },
        },
      };
    },
  }),

  Object.freeze({
    name: 'FinalTheorem tamper rejects at CheckFinal0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.CheckFinal0',
    mutate: (pipeline) => {
      pipeline.PCCPack.FinalTheorem = {
        ...pipeline.PCCPack.FinalTheorem,
        PCCMinBridge: {
          ...pipeline.PCCPack.FinalTheorem.PCCMinBridge,
          residualBandBound: 5,
        },
      };
    },
  }),

  Object.freeze({
    name: 'RowFamFinal tamper rejects at CheckRowFamFinal0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.CheckRowFamFinal0',
    mutate: (pipeline) => {
      pipeline.PCCPack.RowFamFinal = {
        ...pipeline.PCCPack.RowFamFinal,
        rows: pipeline.PCCPack.RowFamFinal.rows.filter((row) => row.rowKind !== 'GeneratedPackageSufficiency'),
      };
    },
  }),

  Object.freeze({
    name: 'PackSufficiency theorem tamper rejects at CheckPackSufficiency0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.CheckPackSufficiency0',
    mutate: (pipeline) => {
      pipeline.PCCPack.PackSufficiencyTheorem = {
        ...pipeline.PCCPack.PackSufficiencyTheorem,
        generatedPackageSufficiency: {
          ...pipeline.PCCPack.PackSufficiencyTheorem.generatedPackageSufficiency,
          canonicalByteEquality: false,
        },
      };
    },
  }),

  Object.freeze({
    name: 'AcceptRun Pgen tamper rejects at BindAcceptRunPgen0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.BindAcceptRunPgen0',
    mutate: (pipeline) => {
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
    },
  }),

  Object.freeze({
    name: 'AcceptRun generator-byte tamper rejects at ReplayAcceptRun0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.ReplayAcceptRun0',
    mutate: (pipeline) => {
      pipeline.AcceptRun = {
        ...pipeline.AcceptRun,
        GenCall: {
          ...pipeline.AcceptRun.GenCall,
          outputPackBytes: '{"not":"the pack"}',
        },
      };
    },
  }),

  Object.freeze({
    name: 'AcceptRun audit-log tamper rejects at CheckAcceptRun0',
    expectedInnerCoord: 'CheckIntegratedPipeline0.CheckAcceptRun0',
    mutate: (pipeline) => {
      pipeline.AcceptRun = {
        ...pipeline.AcceptRun,
        AuditLogs: {
          ...pipeline.AcceptRun.AuditLogs,
          digestComparisonsOnly: true,
        },
      };
    },
  }),
]);

for (const entry of TAMPER_CASES0) {
  test(`RunAll0 first-failure tamper fixture: ${entry.name}`, async () => {
    const pipeline = makeSyntheticIntegratedPipeline0();

    entry.mutate(pipeline);

    const out = await RunAll0(pipeline);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'RunAll0');
    assert.equal(out.Coord, 'RunAll0.integrated');
    assert.deepEqual(out.Path, ['Pipeline']);
    assert.equal(out.Witness.reason, 'CheckIntegratedPipeline0 rejected');
    assert.equal(out.Witness.detail.inner.coord, entry.expectedInnerCoord);
    assert.equal(Array.isArray(out.Ledger), true);
    assert.equal(out.Ledger.some((ledgerEntry) => ledgerEntry.status === 'fail'), true);
  });
}

test('RunAll0 emits no public conclusion for every tamper fixture', async () => {
  for (const entry of TAMPER_CASES0) {
    const pipeline = makeSyntheticIntegratedPipeline0();

    entry.mutate(pipeline);

    const out = await RunAll0(pipeline);

    assert.equal(out.tag, 'reject', entry.name);
    assert.equal(out.NF, undefined, entry.name);
    assert.equal(out.Witness.detail.inner.coord, entry.expectedInnerCoord, entry.name);
  }
});