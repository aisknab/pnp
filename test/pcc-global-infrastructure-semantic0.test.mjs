import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  makeKBundleReflectionSuccessor0,
} from '../pcc-kbundle-reflection-successor0.mjs';

import {
  CheckGlobalInfrastructureSemantic0,
  makeGlobalInfrastructureSemanticInput0,
  makeGlobalInfrastructureSemanticSuite0,
} from '../pcc-global-infrastructure-semantic0.mjs';

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
    programId: 'global.infrastructure.finiterel.program',
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
    evaluationId: 'global.infrastructure.finiterel.eval',
    program,
  });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.global.infrastructure',
      RuleName: 'FiniteRel',
      Conclusion: deriveSemanticFiniteRelJudgment0({ spec }),
      Payload: { op: 'verify', spec },
    }),
  ]);
}

function makeInput0({ LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0() } = {}) {
  const KBundle = makeKBundleReflectionSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  return makeGlobalInfrastructureSemanticInput0({
    KBundle,
    LegacyGlobalProofDAG,
    SemanticInfrastructure: makeGlobalInfrastructureSemanticSuite0({
      LegacyGlobalProofDAG,
    }),
  });
}

function withoutDigest0(node, changes) {
  const out = { ...node, ...changes };
  delete out.Digest;
  delete out.digest;
  return out;
}

test('semantic global infrastructure checker derives all four infrastructure coordinates', async () => {
  const out = await CheckGlobalInfrastructureSemantic0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalInfrastructureSemantic0');
  assert.equal(out.NF.globalInfrastructureSemanticReady, true);
  assert.equal(out.NF.globalInfrastructureDerivationsReady, true);
  assert.deepEqual(out.NF.infrastructureCoordinates, infrastructureCoordinates);
  assert.equal(out.NF.infrastructureCoordinateCount, 4);
  assert.equal(out.NF.semanticKBundleFinalReady, true);
  assert.equal(out.NF.semanticKImplFinalReady, true);
  assert.equal(out.NF.semanticK0ConformanceReady, true);
  assert.equal(out.NF.semanticSigmaReady, true);
  assert.equal(out.NF.semanticReflectionReady, true);
  assert.equal(out.NF.polynomialBoundsReady, true);
  assert.equal(out.NF.noHiddenMinimizationReady, true);
  assert.equal(out.NF.modeFirewallReady, true);
  assert.equal(out.NF.importAcyclicityReady, true);
  assert.equal(out.NF.globalRowDerivationsReady, false);
  assert.equal(out.NF.globalPackageDerivationsReady, false);
  assert.equal(out.NF.globalFinalDerivationsReady, false);
  assert.equal(out.NF.globalSemanticNodeDerivationsReady, false);

  const bounds = out.NF.infrastructureDerivations.find(
    (entry) => entry.coordinate === 'Bounds.Polynomial',
  );
  assert.equal(bounds.detail.globalExponent, 8);
  assert.equal(bounds.detail.maxNodeExponent, 8);

  const noMin = out.NF.infrastructureDerivations.find(
    (entry) => entry.coordinate === 'NoMin.Global',
  );
  assert.equal(noMin.detail.forbiddenHitCount, 0);

  const mode = out.NF.infrastructureDerivations.find(
    (entry) => entry.coordinate === 'Mode.Firewall',
  );
  assert.equal(mode.detail.quotientNodeCount, 0);

  const imports = out.NF.infrastructureDerivations.find(
    (entry) => entry.coordinate === 'Import.Acyclic',
  );
  assert.equal(imports.detail.packageImportAcyclic, true);
  assert.equal(imports.detail.nodeDependencyAcyclic, true);
});

test('semantic global infrastructure checker rejects caller-supplied readiness assertions', async () => {
  const input = {
    ...makeInput0(),
    globalInfrastructureSemanticReady: true,
  };
  const out = await CheckGlobalInfrastructureSemantic0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalInfrastructureSemantic0.input');
  assert.deepEqual(out.Path, ['globalInfrastructureSemanticReady']);
  assert.equal(
    out.Witness.reason,
    'global infrastructure semantic checker rejects caller-supplied readiness assertions',
  );
});

test('semantic global infrastructure checker rejects a stale executable contract binding', async () => {
  const base = makeInput0();
  const input = {
    ...base,
    SemanticInfrastructure: {
      ...base.SemanticInfrastructure,
      derivations: base.SemanticInfrastructure.derivations.map((entry) => (
        entry.coordinate === 'Mode.Firewall'
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
  const out = await CheckGlobalInfrastructureSemantic0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalInfrastructureSemantic0.semanticInfrastructureSuite',
  );
  assert.equal(
    out.Witness.reason,
    'global infrastructure binding must exactly match the computed node, ledger, and executable contract binding',
  );
});

test('semantic global infrastructure checker rejects a bounds envelope smaller than a node exponent', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  dag.BoundsLedger = {
    ...dag.BoundsLedger,
    exponent: 7,
  };
  const out = await CheckGlobalInfrastructureSemantic0(makeInput0({
    LegacyGlobalProofDAG: dag,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalInfrastructureSemantic0.infrastructure.Bounds.Polynomial',
  );
  assert.equal(
    out.Witness.reason,
    'Bounds.Polynomial node must bind the exact global polynomial exponent',
  );
});

test('semantic global infrastructure checker rejects an executable hidden-minimization symbol', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  dag.Nodes = dag.Nodes.map((node) => (
    node.id === 'Package.E.VerifyDWSoundness'
      ? withoutDigest0(node, {
          payload: {
            ...node.payload,
            execCall: 'argmin',
          },
        })
      : node
  ));
  const out = await CheckGlobalInfrastructureSemantic0(makeInput0({
    LegacyGlobalProofDAG: dag,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalInfrastructureSemantic0.legacyGlobalDAG');
  assert.equal(
    out.Witness.reason,
    'legacy global proof DAG rejected before infrastructure semantic upgrade',
  );
});

test('semantic global infrastructure checker rejects a quotient-only final theorem node', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  dag.Nodes = dag.Nodes.map((node) => (
    node.id === 'Final.PackageSoundness'
      ? withoutDigest0(node, { mode: 'Quot' })
      : node
  ));
  const out = await CheckGlobalInfrastructureSemantic0(makeInput0({
    LegacyGlobalProofDAG: dag,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalInfrastructureSemantic0.infrastructure.Mode.Firewall',
  );
  assert.equal(
    out.Witness.reason,
    'package and final theorem nodes cannot be justified only in quotient mode',
  );
});

test('semantic global infrastructure checker rejects a cycle in the explicit package import graph', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  dag.ImportGraph = {
    ...dag.ImportGraph,
    edges: [
      ['A', 'B'],
      ['B', 'A'],
    ],
  };
  const out = await CheckGlobalInfrastructureSemantic0(makeInput0({
    LegacyGlobalProofDAG: dag,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalInfrastructureSemantic0.infrastructure.Import.Acyclic',
  );
  assert.equal(
    out.Witness.reason,
    'global package import graph contains a cycle',
  );
});

test('semantic global infrastructure checker rejects a mutated infrastructure conclusion', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  dag.Nodes = dag.Nodes.map((node) => (
    node.id === 'Mode.Firewall'
      ? withoutDigest0(node, {
          conclusion: {
            ...node.conclusion,
            quotientNotReplacement: false,
          },
        })
      : node
  ));
  const out = await CheckGlobalInfrastructureSemantic0(makeInput0({
    LegacyGlobalProofDAG: dag,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalInfrastructureSemantic0.infrastructure.Mode.Firewall',
  );
  assert.equal(
    out.Witness.reason,
    'Mode.Firewall conclusion must enforce quotient-not-replacement',
  );
});

test('semantic global infrastructure derivation digests bind node and ledger records', async () => {
  const out = await CheckGlobalInfrastructureSemantic0(makeInput0());

  assert.equal(out.tag, 'accept');
  for (const entry of out.NF.infrastructureDerivationDigests) {
    assert.equal(entry.digest.alg, 'SHA256');
    assert.equal(entry.nodeDigest.alg, 'SHA256');
    assert.equal(entry.ledgerDigest.alg, 'SHA256');
    assert.equal(entry.checkerContractDigest.alg, 'SHA256');
    assert.equal(entry.conclusionDigest.alg, 'SHA256');
  }
  assert.equal(
    digestCanonical0(out.NF.infrastructureCoordinates).alg,
    'SHA256',
  );
});
