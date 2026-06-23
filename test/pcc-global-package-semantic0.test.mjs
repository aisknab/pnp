import assert from 'node:assert/strict';
import { test } from 'node:test';

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
  CheckGlobalPackageSemantic0,
  GLOBAL_PACKAGE_NODE_IDS0,
  GLOBAL_PACKAGE_SEMANTIC_REQUIREMENTS0,
  GLOBAL_SUPPORTING_LOCAL_PACKAGE_FAMILIES0,
  makeGlobalPackageSemanticInput0,
  makeGlobalPackageSemanticSuite0,
} from '../pcc-global-package-semantic0.mjs';

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
    programId: 'global.package.semantic.program',
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
    evaluationId: 'global.package.semantic.eval',
    program,
  });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.global.package.semantic',
      RuleName: 'FiniteRel',
      Conclusion: deriveSemanticFiniteRelJudgment0({ spec }),
      Payload: { op: 'verify', spec },
    }),
  ]);
}

function makeInput0({
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  RowPack = makeSyntheticRowPack0(),
  RowFamG = makeSyntheticRowFamG0(),
  LocalPackages = makeSyntheticLocalPackages0(),
} = {}) {
  const KBundle = makeKBundleReflectionSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  return makeGlobalPackageSemanticInput0({
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
    SemanticPackages: makeGlobalPackageSemanticSuite0({
      LegacyGlobalProofDAG,
      LocalPackages,
    }),
  });
}

function withoutDigest0(node, changes) {
  const out = { ...node, ...changes };
  delete out.Digest;
  delete out.digest;
  return out;
}

test('global package semantic checker accepts exact positive and negative refinements for every global package theorem', async () => {
  const out = await CheckGlobalPackageSemantic0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalPackageSemantic0');
  assert.equal(out.NF.globalPackageSemanticReady, true);
  assert.equal(out.NF.globalPackageDerivationsReady, true);
  assert.equal(out.NF.globalFinalDerivationsReady, false);
  assert.equal(out.NF.globalSemanticNodeDerivationsReady, false);
  assert.equal(
    out.NF.globalPackageRefinementCount,
    GLOBAL_PACKAGE_SEMANTIC_REQUIREMENTS0.length,
  );
  assert.equal(out.NF.positiveProbeCount, GLOBAL_PACKAGE_NODE_IDS0.length);
  assert.equal(out.NF.negativeProbeCount, GLOBAL_PACKAGE_NODE_IDS0.length);
  assert.deepEqual(out.NF.globalPackageNodeIds, GLOBAL_PACKAGE_NODE_IDS0);
  assert.deepEqual(
    out.NF.supportingLocalPackageFamilies,
    GLOBAL_SUPPORTING_LOCAL_PACKAGE_FAMILIES0,
  );
  assert.equal(
    out.NF.supportingLocalPackageCount,
    GLOBAL_SUPPORTING_LOCAL_PACKAGE_FAMILIES0.length,
  );
  assert.equal(out.NF.globalRowDerivationsReady, true);
  assert.equal(out.NF.globalInfrastructureSemanticReady, true);
  assert.equal(out.NF.semanticKBundleFinalReady, true);
  assert.equal(out.NF.boundedExecutablePackageRefinementsOnly, true);
  assert.equal(out.NF.unrestrictedPackageTheoremSoundnessNotClaimed, true);
  assert.equal(out.NF.finalTheoremSoundnessNotClaimedHere, true);

  for (const refinement of out.NF.packageRefinements) {
    assert.equal(refinement.ready, true);
    assert.equal(refinement.positiveNFKind, 'LocalPackageFamily0NF');
    assert.equal(
      refinement.negativeCoord,
      'CheckLocalPackageFamily0.identity',
    );
    assert.deepEqual(refinement.negativePath, ['theorem']);
    assert.equal(refinement.rowNodeId, `Row.${refinement.family}`);
    assert.equal(refinement.boundedExecutablePackageRefinement, true);
    assert.equal(refinement.unrestrictedPackageTheoremSoundnessNotClaimed, true);
  }
});

test('global package semantic checker rejects caller-supplied readiness assertions', async () => {
  const input = {
    ...makeInput0(),
    globalPackageDerivationsReady: true,
  };
  const out = await CheckGlobalPackageSemantic0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalPackageSemantic0.input');
  assert.deepEqual(out.Path, ['globalPackageDerivationsReady']);
  assert.equal(
    out.Witness.reason,
    'global package semantic checker rejects caller-supplied readiness or truth assertions',
  );
});

test('global package semantic checker rejects a stale package binding digest', async () => {
  const base = makeInput0();
  const input = {
    ...base,
    SemanticPackages: {
      ...base.SemanticPackages,
      refinements: base.SemanticPackages.refinements.map((entry) => (
        entry.family === 'BN4'
          ? {
              ...entry,
              checkerContractDigest: {
                alg: 'SHA256',
                hex: '0'.repeat(64),
              },
            }
          : entry
      )),
    },
  };
  const out = await CheckGlobalPackageSemantic0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalPackageSemantic0.semanticPackagesSuite');
  assert.equal(
    out.Witness.reason,
    'global package semantic suite must exactly match the computed global-node and local-package bindings',
  );
});

test('global package semantic checker rejects a missing required local package before refinement', async () => {
  const localPackages = makeSyntheticLocalPackages0();
  localPackages.Packages = localPackages.Packages.filter(
    (entry) => entry.family !== 'PkgC',
  );
  const out = await CheckGlobalPackageSemantic0(makeInput0({
    LocalPackages: localPackages,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalPackageSemantic0.localPackages');
  assert.equal(
    out.Witness.reason,
    'global package refinements require an accepted local package inventory',
  );
  assert.equal(out.Witness.inner.coord, 'CheckLocalPackages0.coverage');
});

test('global package semantic checker rejects a forbidden local import before refinement', async () => {
  const localPackages = makeSyntheticLocalPackages0();
  const index = localPackages.Packages.findIndex((entry) => entry.family === 'G');
  localPackages.Packages[index] = {
    ...localPackages.Packages[index],
    imports: ['O'],
  };
  const out = await CheckGlobalPackageSemantic0(makeInput0({
    LocalPackages: localPackages,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalPackageSemantic0.localPackages');
  assert.equal(out.Witness.inner.coord, 'CheckLocalPackages0.imports');
});

test('global package semantic checker rejects a weakened global package premise list', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  dag.Nodes = dag.Nodes.map((node) => (
    node.id === 'Package.E.VerifyDWSoundness'
      ? withoutDigest0(node, { premises: ['Bounds.Polynomial'] })
      : node
  ));
  const out = await CheckGlobalPackageSemantic0(makeInput0({
    LegacyGlobalProofDAG: dag,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalPackageSemantic0.package.E');
  assert.equal(
    out.Witness.reason,
    'global package theorem node premise list must exactly match its executable refinement contract',
  );
});

test('global package semantic checker rejects local theorem identity drift before positive refinement', async () => {
  const localPackages = makeSyntheticLocalPackages0();
  const index = localPackages.Packages.findIndex((entry) => entry.family === 'G');
  localPackages.Packages[index] = {
    ...localPackages.Packages[index],
    theorem: 'G.StaleThreshold',
  };
  const out = await CheckGlobalPackageSemantic0(makeInput0({
    LocalPackages: localPackages,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalPackageSemantic0.localPackages');
  assert.equal(out.Witness.inner.coord, 'CheckLocalPackages0.packages');
});

test('global package refinement digests bind node, local package, row, and probe records', async () => {
  const out = await CheckGlobalPackageSemantic0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(
    out.NF.packageRefinementDigests.length,
    GLOBAL_PACKAGE_NODE_IDS0.length,
  );
  for (const entry of out.NF.packageRefinementDigests) {
    assert.equal(entry.digest.alg, 'SHA256');
    assert.equal(entry.globalNodeDigest.alg, 'SHA256');
    assert.equal(entry.localPackageDigest.alg, 'SHA256');
    assert.equal(entry.rowDerivationDigest.alg, 'SHA256');
    assert.equal(entry.positiveRecordDigest.alg, 'SHA256');
    assert.equal(entry.negativeRecordDigest.alg, 'SHA256');
    assert.equal(entry.checkerContractDigest.alg, 'SHA256');
    assert.equal(entry.conclusionDigest.alg, 'SHA256');
  }
});
