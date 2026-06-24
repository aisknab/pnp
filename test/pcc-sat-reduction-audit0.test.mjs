import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckSATReductionAudit0,
  makeSATReductionAuditInput0,
} from '../pcc-sat-reduction-audit0.mjs';

import {
  makeSyntheticGPack0,
} from '../pcc-gpack0.mjs';

import {
  makeSyntheticFinalIntegration0,
} from '../pcc-final-framework0.mjs';

test('bounded SAT-reduction audit independently covers macro, baseline, trace, SAT, and UNSAT directions', async () => {
  const out = await CheckSATReductionAudit0(makeSATReductionAuditInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckSATReductionAudit0');
  assert.equal(out.NF.boundedSATReductionAuditReady, true);
  assert.equal(out.NF.distinguishedMacroRelationsReady, true);
  assert.equal(out.NF.activeBaselineInventoryAuditReady, true);
  assert.equal(out.NF.boundedTraceEquivalenceAuditReady, true);
  assert.equal(out.NF.boundedSATDirectionAuditReady, true);
  assert.equal(out.NF.boundedUNSATDirectionAuditReady, true);
  assert.equal(out.NF.boundedFinalLockSeparationAuditReady, true);
  assert.equal(out.NF.decisionExtractionInterfaceAuditReady, true);
  assert.equal(out.NF.constructionPolynomialLedgerReady, true);
  assert.equal(out.NF.circuitAuditCount, 3);
  assert.equal(out.NF.directionCoverage.satDirectionCovered, true);
  assert.equal(out.NF.directionCoverage.unsatDirectionCovered, true);
  assert.equal(out.NF.activeBaselineAudit.exactBaselineMinimum, 91);
  assert.equal(out.NF.activeBaselineAudit.fullWordSize, 95);
  assert.equal(out.NF.uniformReductionSoundnessReady, false);
  assert.equal(out.NF.uniformExactMinimizerSoundnessReady, false);
  assert.equal(out.NF.uniformPolynomialRuntimeReady, false);
  assert.equal(out.NF.globalFinalSATReductionDerivationReady, false);
  assert.equal(out.NF.satInPReady, false);
  assert.equal(out.NF.pEqualsNPReady, false);
  assert.deepEqual(out.NF.exactRemainingObligations, [
    'UniformLockedNANDEncodingSoundness',
    'UniformExactPCCMinSoundness',
    'UniformPolynomialPCCMinRuntime',
  ]);

  const sat = out.NF.circuitAudits.find(
    (entry) => entry.auditId === 'sat.single-nand',
  );
  assert.equal(sat.satisfiable, true);
  assert.equal(sat.finalPredicateEssentiallyDependsOnFreshZ, true);
  assert.equal(sat.exactMinimumConclusion.lowerBound, sat.baseline + 1);
  assert.equal(sat.exactMinimumConclusion.upperBound, sat.baseline + 4);

  const unsat = out.NF.circuitAudits.find(
    (entry) => entry.auditId === 'unsat.constant-zero',
  );
  assert.equal(unsat.satisfiable, false);
  assert.equal(unsat.finalPredicateIdenticallyZero, true);
  assert.equal(unsat.exactMinimumConclusion.exact, true);
  assert.equal(unsat.exactMinimumConclusion.exactValue, unsat.baseline);
});

test('bounded SAT-reduction audit rejects caller-supplied theorem readiness', async () => {
  const input = {
    ...makeSATReductionAuditInput0(),
    satInPReady: true,
  };
  const out = await CheckSATReductionAudit0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSATReductionAudit0.input');
  assert.deepEqual(out.Path, ['satInPReady']);
  assert.equal(
    out.Witness.reason,
    'SAT-reduction audit rejects caller-supplied readiness or theorem-truth assertions',
  );
});

test('bounded SAT-reduction audit rejects a distinguished equality relation mutation', async () => {
  const gpack = makeSyntheticGPack0();
  gpack.MacroTables.macros.Equality10.outputs.a8 = '00000000';
  const out = await CheckSATReductionAudit0(makeSATReductionAuditInput0({
    GPack: gpack,
    FinalIntegration: makeSyntheticFinalIntegration0({ gpack }),
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSATReductionAudit0.GPack');
});

test('bounded SAT-reduction audit rejects a final integration bound to another GPack', async () => {
  const gpack = makeSyntheticGPack0();
  const other = makeSyntheticGPack0({
    SchedHash: {
      alg: 'SHA256',
      hex: '0'.repeat(64),
    },
  });
  const out = await CheckSATReductionAudit0(makeSATReductionAuditInput0({
    GPack: gpack,
    FinalIntegration: makeSyntheticFinalIntegration0({ gpack: other }),
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSATReductionAudit0.FinalIntegration');
});

test('bounded SAT-reduction audit rejects witness suites without an UNSAT direction', async () => {
  const input = makeSATReductionAuditInput0();
  const out = await CheckSATReductionAudit0({
    ...input,
    WitnessCircuits: input.WitnessCircuits.filter(
      (entry) => entry.auditId === 'sat.single-nand',
    ),
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSATReductionAudit0.directionCoverage');
  assert.equal(
    out.Witness.reason,
    'bounded SAT-reduction audit requires at least one satisfiable and one unsatisfiable circuit',
  );
});

test('bounded SAT-reduction audit digests bind the independently enumerated surfaces', async () => {
  const out = await CheckSATReductionAudit0(makeSATReductionAuditInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.gpackDigest.alg, 'SHA256');
  assert.equal(out.NF.finalIntegrationDigest.alg, 'SHA256');
  assert.equal(out.NF.macroAudit.relations.length, 4);
  assert.equal(out.NF.decisionInterfaceAudit.negativeProbes.length, 3);
  for (const probe of out.NF.decisionInterfaceAudit.negativeProbes) {
    assert.equal(probe.recordDigest.alg, 'SHA256');
  }
});
