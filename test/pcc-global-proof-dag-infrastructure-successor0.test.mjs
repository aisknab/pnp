import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleSigmaSuccessor0,
} from '../pcc-kbundle-sigma-successor0.mjs';

import {
  makeKBundleReflectionSuccessor0,
} from '../pcc-kbundle-reflection-successor0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  makeGlobalInfrastructureSemanticSuite0,
} from '../pcc-global-infrastructure-semantic0.mjs';

import {
  CheckGlobalProofDAGInfrastructureFinalTheoremReadiness0,
  CheckGlobalProofDAGInfrastructureSuccessor0,
  makeGlobalProofDAGInfrastructureSuccessor0,
} from '../pcc-global-proof-dag-infrastructure-successor0.mjs';

import {
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  deriveSemanticFiniteRelJudgment0,
  makeSemanticFiniteRelClaim0,
  makeSemanticFiniteRelDomain0,
  makeSemanticFiniteRelNode0,
  makeSemanticFiniteRelProgram0,
  makeSemanticFiniteRelSpec0,
  makeSemanticFiniteRelTuple0,
} from '../pcc-kernel-finiterel-semantic0.mjs';

const infrastructureCoordinates = [
  'Bounds.Polynomial',
  'NoMin.Global',
  'Mode.Firewall',
  'Import.Acyclic',
];

const finalNodeIds = [
  'Final.PackageSoundness',
  'Final.GeneratedPackageSufficiency',
  'Final.AcceptedPackageImpliesSATinP',
  'Final.AcceptedPackageImpliesPEqualsNP',
];

function makeFiniteRelProof0() {
  const domain = makeSemanticFiniteRelDomain0({
    index: 0,
    id: 'D',
    elements: ['a', 'b'],
  });
  const literal = makeSemanticFiniteRelNode0({
    index: 0,
    id: 'R',
    op: 'literal',
    domainIds: ['D', 'D'],
    tuples: [makeSemanticFiniteRelTuple0({ index: 0, values: ['a', 'b'] })],
  });
  const closure = makeSemanticFiniteRelNode0({
    index: 1,
    id: 'R.rtc',
    op: 'reflexive-transitive-closure',
    domainIds: ['D', 'D'],
    inputIds: ['R'],
  });
  const program = makeSemanticFiniteRelProgram0({
    programId: 'global.infrastructure.successor.program',
    domains: [domain],
    nodes: [literal, closure],
    claims: [
      makeSemanticFiniteRelClaim0({
        index: 0,
        id: 'claim.R.in.rtc',
        claimKind: 'included',
        leftId: 'R',
        rightId: 'R.rtc',
      }),
      makeSemanticFiniteRelClaim0({
        index: 1,
        id: 'claim.rtc.closed',
        claimKind: 'reflexive-transitive-closed',
        leftId: 'R.rtc',
      }),
    ],
  });
  const spec = makeSemanticFiniteRelSpec0({
    evaluationId: 'global.infrastructure.successor.eval',
    program,
  });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.global.infrastructure.successor',
      RuleName: 'FiniteRel',
      Conclusion: deriveSemanticFiniteRelJudgment0({ spec }),
      Payload: { op: 'verify', spec },
    }),
  ]);
}

function makeInput0({
  Purpose = 'development',
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
} = {}) {
  const KBundle = makeKBundleReflectionSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  return makeGlobalProofDAGInfrastructureSuccessor0({
    KBundle,
    LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations:
      makeGlobalInfrastructureSemanticSuite0({ LegacyGlobalProofDAG }),
    Purpose,
  });
}

function withoutDigest0(node, changes) {
  const out = { ...node, ...changes };
  delete out.Digest;
  delete out.digest;
  return out;
}

test('global infrastructure successor activates four infrastructure nodes and keeps later families quarantined', async () => {
  const out = await CheckGlobalProofDAGInfrastructureSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGInfrastructureSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorGlobalAccepted, true);
  assert.equal(out.NF.predecessorGlobalDevelopmentOnly, true);
  assert.equal(out.NF.predecessorGlobalInfrastructureReady, false);
  assert.equal(out.NF.semanticKBundleDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKBundleFinalProbeAccepted, true);
  assert.equal(out.NF.kBundleFinalReady, true);
  assert.equal(out.NF.semanticK0ConformanceReady, true);
  assert.equal(out.NF.semanticSigmaReady, true);
  assert.equal(out.NF.semanticReflectionReady, true);
  assert.equal(out.NF.globalInfrastructureSemanticReady, true);
  assert.deepEqual(
    out.NF.globalInfrastructureCoordinates,
    infrastructureCoordinates,
  );

  assert.deepEqual(
    out.NF.semanticOverlay.semanticInfrastructureNodeIds,
    infrastructureCoordinates,
  );
  assert.deepEqual(out.NF.semanticOverlay.blockedInfrastructureNodeIds, []);
  assert.equal(out.NF.semanticOverlay.semanticInfrastructureBindings.length, 4);
  assert.equal(out.NF.semanticOverlay.globalInfrastructureSemanticReady, true);
  assert.equal(out.NF.semanticOverlay.globalRowDerivationsReady, false);
  assert.equal(out.NF.semanticOverlay.globalPackageDerivationsReady, false);
  assert.equal(out.NF.semanticOverlay.globalFinalDerivationsReady, false);
  assert.equal(out.NF.semanticOverlay.globalSemanticNodeDerivationsReady, false);
  assert.equal(out.NF.semanticOverlay.blockedRowNodeIds.length > 0, true);
  assert.equal(out.NF.semanticOverlay.blockedPackageNodeIds.length > 0, true);
  assert.deepEqual(out.NF.semanticOverlay.blockedFinalNodeIds, finalNodeIds);
  for (const coordinate of infrastructureCoordinates) {
    assert.equal(out.NF.semanticOverlay.semanticNodeIds.includes(coordinate), true);
    assert.equal(out.NF.semanticOverlay.structuralOnlyNodeIds.includes(coordinate), false);
  }

  assert.deepEqual(out.NF.computedGlobalGate.blockerCoordinates, [
    'GlobalDAG.RowDerivations',
    'GlobalDAG.PackageDerivations',
    'GlobalDAG.FinalDerivations',
  ]);
  assert.equal(out.NF.legacyFinalNodesQuarantined, true);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, finalNodeIds);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('global infrastructure successor rejects final purpose while row, package, and final derivations remain blocked', async () => {
  const out = await CheckGlobalProofDAGInfrastructureSuccessor0(
    makeInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGInfrastructureSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'semantic global infrastructure successor is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.filter((entry) => !entry.ready).length, 3);
});

test('explicit global infrastructure final gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGInfrastructureFinalTheoremReadiness0(
    makeInput0(),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGInfrastructureFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
});

test('global infrastructure successor rejects caller-supplied readiness assertions', async () => {
  const input = makeInput0();
  input.globalInfrastructureSemanticReady = true;

  const out = await CheckGlobalProofDAGInfrastructureSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGInfrastructureSuccessor0.input');
  assert.deepEqual(out.Path, ['globalInfrastructureSemanticReady']);
  assert.equal(
    out.Witness.reason,
    'semantic global infrastructure successor rejects caller-supplied readiness assertions',
  );
});

test('global infrastructure successor rejects a final-purpose child KBundle', async () => {
  const input = makeInput0();
  input.KBundle.Purpose = 'final-theorem';

  const out = await CheckGlobalProofDAGInfrastructureSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGInfrastructureSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
});

test('global infrastructure successor rejects a stale Sigma-only KBundle', async () => {
  const input = makeGlobalProofDAGInfrastructureSuccessor0({
    KBundle: makeKBundleSigmaSuccessor0(),
  });

  const out = await CheckGlobalProofDAGInfrastructureSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGInfrastructureSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'semantic reflection predecessor global gate rejected before infrastructure upgrade',
  );
});

test('global infrastructure successor rejects a malformed infrastructure premise at the semantic checker', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  dag.Nodes = dag.Nodes.map((node) => (
    node.id === 'Bounds.Polynomial'
      ? withoutDigest0(node, { premises: ['K.IntArith'] })
      : node
  ));
  const input = makeInput0({ LegacyGlobalProofDAG: dag });

  const out = await CheckGlobalProofDAGInfrastructureSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGInfrastructureSuccessor0.semanticInfrastructure',
  );
  assert.equal(
    out.Witness.reason,
    'semantic global infrastructure checker rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'global infrastructure node premise list must exactly match its semantic contract',
  );
});

test('global infrastructure successor rejects a stale infrastructure binding digest', async () => {
  const input = makeInput0();
  input.InfrastructureSemanticDerivations = {
    ...input.InfrastructureSemanticDerivations,
    derivations: input.InfrastructureSemanticDerivations.derivations.map((entry) => (
      entry.coordinate === 'Import.Acyclic'
        ? {
            ...entry,
            ledgerDigest: {
              alg: 'SHA256',
              hex: '0'.repeat(64),
            },
          }
        : entry
    )),
  };

  const out = await CheckGlobalProofDAGInfrastructureSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGInfrastructureSuccessor0.semanticInfrastructure',
  );
  assert.equal(
    out.Witness.reason,
    'semantic global infrastructure checker rejected',
  );
});

test('global infrastructure overlay binds every infrastructure node to its checked derivation digest', async () => {
  const out = await CheckGlobalProofDAGInfrastructureSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  const derivationByCoordinate = new Map(
    out.NF.globalInfrastructureDerivationDigests.map((entry) => [
      entry.coordinate,
      entry,
    ]),
  );
  for (const binding of out.NF.semanticOverlay.semanticInfrastructureBindings) {
    const derivation = derivationByCoordinate.get(binding.coordinate);
    assert.equal(binding.derivationDigest.hex, derivation.digest.hex);
    assert.equal(binding.nodeDigest.hex, derivation.nodeDigest.hex);
    assert.equal(binding.ledgerDigest.hex, derivation.ledgerDigest.hex);
    assert.equal(
      binding.checkerContractDigest.hex,
      derivation.checkerContractDigest.hex,
    );
    assert.equal(binding.conclusionDigest.hex, derivation.conclusionDigest.hex);
  }
  const infrastructureGate = out.NF.computedGlobalGate.nodes.find(
    (node) => node.id === 'Gate.GlobalDAG.InfrastructureDerivations',
  );
  assert.equal(infrastructureGate.ready, true);
  const finalGate = out.NF.computedGlobalGate.nodes.find(
    (node) => node.id === 'Gate.FinalTheorem.Readiness',
  );
  assert.equal(finalGate.ready, false);
});
