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
  makeSyntheticRowPack0,
} from '../pcc-rows0.mjs';

import {
  makeSyntheticRowFamG0,
} from '../pcc-gpack0.mjs';

import {
  makeGlobalRowSemanticSuite0,
} from '../pcc-global-row-semantic0.mjs';

import {
  makeSyntheticLocalPackages0,
} from '../pcc-local-packages0.mjs';

import {
  GLOBAL_PACKAGE_NODE_IDS0,
  makeGlobalPackageSemanticSuite0,
} from '../pcc-global-package-semantic0.mjs';

import {
  CheckGlobalProofDAGPackageFinalTheoremReadiness0,
  CheckGlobalProofDAGPackageSuccessor0,
  makeGlobalProofDAGPackageSuccessor0,
} from '../pcc-global-proof-dag-package-successor0.mjs';

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
    programId: 'global.package.successor.program',
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
    evaluationId: 'global.package.successor.eval',
    program,
  });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.global.package.successor',
      RuleName: 'FiniteRel',
      Conclusion: deriveSemanticFiniteRelJudgment0({ spec }),
      Payload: { op: 'verify', spec },
    }),
  ]);
}

function makeInput0({
  Purpose = 'development',
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  RowPack = makeSyntheticRowPack0(),
  RowFamG = makeSyntheticRowFamG0(),
  LocalPackages = makeSyntheticLocalPackages0(),
} = {}) {
  const KBundle = makeKBundleReflectionSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  return makeGlobalProofDAGPackageSuccessor0({
    KBundle,
    LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations:
      makeGlobalInfrastructureSemanticSuite0({ LegacyGlobalProofDAG }),
    RowPack,
    RowFamG,
    RowSemanticDerivations: makeGlobalRowSemanticSuite0({
      LegacyGlobalProofDAG,
      RowPack,
      RowFamG,
    }),
    LocalPackages,
    PackageSemanticDerivations: makeGlobalPackageSemanticSuite0({
      LegacyGlobalProofDAG,
      LocalPackages,
    }),
    Purpose,
  });
}

test('semantic package successor activates every package node and keeps final nodes quarantined', async () => {
  const out = await CheckGlobalProofDAGPackageSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGPackageSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorGlobalAccepted, true);
  assert.equal(out.NF.predecessorGlobalDevelopmentOnly, true);
  assert.equal(out.NF.predecessorGlobalRowReady, true);
  assert.equal(out.NF.predecessorGlobalPackageReady, false);
  assert.equal(out.NF.semanticKBundleFinalReady, true);
  assert.equal(out.NF.semanticK0ConformanceReady, true);
  assert.equal(out.NF.semanticSigmaReady, true);
  assert.equal(out.NF.semanticReflectionReady, true);
  assert.equal(out.NF.globalInfrastructureSemanticReady, true);
  assert.equal(out.NF.globalRowDerivationsReady, true);
  assert.equal(out.NF.globalPackageSemanticReady, true);
  assert.equal(out.NF.globalPackageDerivationsReady, true);
  assert.deepEqual(out.NF.globalPackageNodeIds, GLOBAL_PACKAGE_NODE_IDS0);
  assert.equal(
    out.NF.globalPackageRefinementCount,
    GLOBAL_PACKAGE_NODE_IDS0.length,
  );
  assert.equal(out.NF.boundedExecutablePackageRefinementsOnly, true);
  assert.equal(out.NF.unrestrictedPackageTheoremSoundnessNotClaimed, true);

  assert.deepEqual(
    out.NF.semanticOverlay.semanticPackageNodeIds,
    GLOBAL_PACKAGE_NODE_IDS0,
  );
  assert.deepEqual(out.NF.semanticOverlay.blockedPackageNodeIds, []);
  assert.equal(
    out.NF.semanticOverlay.semanticPackageBindings.length,
    GLOBAL_PACKAGE_NODE_IDS0.length,
  );
  assert.equal(out.NF.semanticOverlay.globalPackageDerivationsReady, true);
  assert.equal(out.NF.semanticOverlay.globalFinalDerivationsReady, false);
  assert.equal(out.NF.semanticOverlay.globalSemanticNodeDerivationsReady, false);
  assert.deepEqual(out.NF.semanticOverlay.blockedFinalNodeIds, finalNodeIds);
  for (const nodeId of GLOBAL_PACKAGE_NODE_IDS0) {
    assert.equal(out.NF.semanticOverlay.semanticNodeIds.includes(nodeId), true);
    assert.equal(out.NF.semanticOverlay.structuralOnlyNodeIds.includes(nodeId), false);
  }

  assert.deepEqual(out.NF.computedGlobalGate.blockerCoordinates, [
    'GlobalDAG.FinalDerivations',
  ]);
  assert.equal(out.NF.legacyFinalNodesQuarantined, true);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, finalNodeIds);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('semantic package successor rejects final purpose while final derivations remain blocked', async () => {
  const out = await CheckGlobalProofDAGPackageSuccessor0(
    makeInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGPackageSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'semantic package global successor is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.filter((entry) => !entry.ready).length, 1);
  assert.equal(out.Witness.unrestrictedPackageTheoremSoundnessNotClaimed, true);
});

test('explicit semantic package final gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGPackageFinalTheoremReadiness0(
    makeInput0(),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGPackageFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
});

test('semantic package successor rejects caller-supplied readiness assertions', async () => {
  const input = makeInput0();
  input.globalPackageDerivationsReady = true;

  const out = await CheckGlobalProofDAGPackageSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGPackageSuccessor0.input');
  assert.deepEqual(out.Path, ['globalPackageDerivationsReady']);
  assert.equal(
    out.Witness.reason,
    'semantic package global successor rejects caller-supplied readiness assertions',
  );
});

test('semantic package successor rejects a final-purpose child KBundle', async () => {
  const input = makeInput0();
  input.KBundle.Purpose = 'final-theorem';

  const out = await CheckGlobalProofDAGPackageSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGPackageSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
});

test('semantic package successor rejects a stale Sigma-only KBundle at the row predecessor', async () => {
  const input = makeGlobalProofDAGPackageSuccessor0({
    KBundle: makeKBundleSigmaSuccessor0(),
  });

  const out = await CheckGlobalProofDAGPackageSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGPackageSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'semantic row predecessor global gate rejected before package upgrade',
  );
});

test('semantic package successor rejects a stale package semantic binding digest', async () => {
  const input = makeInput0();
  input.PackageSemanticDerivations = {
    ...input.PackageSemanticDerivations,
    refinements: input.PackageSemanticDerivations.refinements.map((entry) => (
      entry.family === 'O'
        ? {
            ...entry,
            localPackageDigest: {
              alg: 'SHA256',
              hex: '0'.repeat(64),
            },
          }
        : entry
    )),
  };

  const out = await CheckGlobalProofDAGPackageSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGPackageSuccessor0.semanticPackages');
  assert.equal(
    out.Witness.reason,
    'bounded semantic package refinement checker rejected',
  );
});

test('semantic package successor rejects a missing local package family', async () => {
  const localPackages = makeSyntheticLocalPackages0();
  localPackages.Packages = localPackages.Packages.filter(
    (entry) => entry.family !== 'PACK',
  );
  const out = await CheckGlobalProofDAGPackageSuccessor0(makeInput0({
    LocalPackages: localPackages,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGPackageSuccessor0.semanticPackages');
  assert.equal(out.Witness.reason, 'bounded semantic package refinement checker rejected');
  assert.equal(out.Witness.inner.coord, 'CheckGlobalPackageSemantic0.localPackages');
});

test('semantic package overlay binds every package node to its computed refinement digest', async () => {
  const out = await CheckGlobalProofDAGPackageSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  const refinementByNodeId = new Map(
    out.NF.globalPackageRefinementDigests.map((entry) => [
      entry.nodeId,
      entry,
    ]),
  );
  for (const binding of out.NF.semanticOverlay.semanticPackageBindings) {
    const refinement = refinementByNodeId.get(binding.nodeId);
    assert.equal(binding.refinementDigest.hex, refinement.digest.hex);
    assert.equal(binding.globalNodeDigest.hex, refinement.globalNodeDigest.hex);
    assert.equal(binding.localPackageDigest.hex, refinement.localPackageDigest.hex);
    assert.equal(binding.rowDerivationDigest.hex, refinement.rowDerivationDigest.hex);
    assert.equal(binding.positiveRecordDigest.hex, refinement.positiveRecordDigest.hex);
    assert.equal(binding.negativeRecordDigest.hex, refinement.negativeRecordDigest.hex);
    assert.equal(
      binding.checkerContractDigest.hex,
      refinement.checkerContractDigest.hex,
    );
    assert.equal(binding.conclusionDigest.hex, refinement.conclusionDigest.hex);
  }
  const packageGate = out.NF.computedGlobalGate.nodes.find(
    (node) => node.id === 'Gate.GlobalDAG.PackageDerivations',
  );
  assert.equal(packageGate.ready, true);
  const finalGate = out.NF.computedGlobalGate.nodes.find(
    (node) => node.id === 'Gate.FinalTheorem.Readiness',
  );
  assert.equal(finalGate.ready, false);
});
