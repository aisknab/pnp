import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  ROW_REQUIRED_FAMILIES0,
} from '../pcc-rows0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  makeKBundleReflectionSuccessor0,
} from '../pcc-kbundle-reflection-successor0.mjs';

import {
  makeGlobalInfrastructureSemanticSuite0,
} from '../pcc-global-infrastructure-semantic0.mjs';

import {
  CheckGlobalRowsSemantic0,
  GLOBAL_GENERIC_ROW_NODE_IDS0,
  GLOBAL_LOCKED_NAND_ROW_NODE_IDS0,
  GLOBAL_ROW_SEMANTIC_NODE_IDS0,
  makeGlobalRowsSemanticInput0,
  makeGlobalRowsSemanticSuite0,
} from '../pcc-global-rows-semantic0.mjs';

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
    programId: 'global.rows.semantic.program',
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
    evaluationId: 'global.rows.semantic.eval',
    program,
  });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.global.rows.semantic',
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
  return makeGlobalRowsSemanticInput0({
    KBundle,
    LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations:
      makeGlobalInfrastructureSemanticSuite0({ LegacyGlobalProofDAG }),
    SemanticRows: makeGlobalRowsSemanticSuite0({ LegacyGlobalProofDAG }),
  });
}

function withoutDigest0(node, changes) {
  const out = { ...node, ...changes };
  delete out.Digest;
  delete out.digest;
  return out;
}

test('bounded global row checker binds every generic and locked-NAND row coordinate', async () => {
  const out = await CheckGlobalRowsSemantic0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalRowsSemantic0');
  assert.equal(out.NF.globalRowCoordinateDerivationsReady, true);
  assert.equal(out.NF.globalGenericRowFamilyCoordinateDerivationsReady, true);
  assert.equal(out.NF.globalLockedNANDRowCoordinateDerivationsReady, true);
  assert.equal(out.NF.globalRowCoordinateCount, GLOBAL_ROW_SEMANTIC_NODE_IDS0.length);
  assert.equal(out.NF.globalGenericRowFamilyCount, ROW_REQUIRED_FAMILIES0.length);
  assert.equal(out.NF.globalLockedNANDRowCount, 3);
  assert.deepEqual(out.NF.genericRowCoordinates, GLOBAL_GENERIC_ROW_NODE_IDS0);
  assert.deepEqual(
    out.NF.lockedNANDRowCoordinates,
    GLOBAL_LOCKED_NAND_ROW_NODE_IDS0,
  );
  assert.equal(out.NF.globalInfrastructureSemanticReady, true);
  assert.equal(out.NF.semanticKBundleFinalReady, true);
  assert.equal(out.NF.semanticK0ConformanceReady, true);
  assert.equal(out.NF.semanticSigmaReady, true);
  assert.equal(out.NF.semanticReflectionReady, true);
  assert.equal(out.NF.boundedGlobalRowCoordinateContractsOnly, true);
  assert.equal(out.NF.unrestrictedRowTheoremSoundnessNotClaimed, true);
  assert.equal(out.NF.globalRowTheoremDerivationsReady, false);
  assert.equal(out.NF.globalPackageDerivationsReady, false);
  assert.equal(out.NF.globalFinalDerivationsReady, false);
  assert.equal(out.NF.globalSemanticNodeDerivationsReady, false);

  const threshold = out.NF.rowDerivations.find(
    (entry) => entry.coordinate === 'G.ThresholdCert.proof',
  );
  assert.equal(threshold.detail.residualSlackMax, 4);
  assert.equal(threshold.detail.finalOutputGates, 4);
  assert.equal(threshold.detail.residualSlackEqualsOutputGateBudget, true);
});

test('bounded global row checker rejects caller-supplied readiness assertions', async () => {
  const input = {
    ...makeInput0(),
    globalRowCoordinateDerivationsReady: true,
  };
  const out = await CheckGlobalRowsSemantic0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalRowsSemantic0.input');
  assert.deepEqual(out.Path, ['globalRowCoordinateDerivationsReady']);
  assert.equal(
    out.Witness.reason,
    'global rows semantic checker rejects caller-supplied readiness assertions',
  );
});

test('bounded global row checker rejects a caller theorem assertion in a generic row payload', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  const coordinate = GLOBAL_GENERIC_ROW_NODE_IDS0[0];
  dag.Nodes = dag.Nodes.map((node) => (
    node.id === coordinate
      ? withoutDigest0(node, { payload: { theoremTrue: true } })
      : node
  ));
  const out = await CheckGlobalRowsSemantic0(makeInput0({
    LegacyGlobalProofDAG: dag,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, `CheckGlobalRowsSemantic0.row.${coordinate}`);
  assert.equal(
    out.Witness.reason,
    'generic row-family coordinate rejects caller-supplied theorem or readiness payload fields',
  );
});

test('bounded global row checker rejects a nonexact generic row premise list', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  const coordinate = GLOBAL_GENERIC_ROW_NODE_IDS0[0];
  dag.Nodes = dag.Nodes.map((node) => (
    node.id === coordinate
      ? withoutDigest0(node, { premises: ['K.Record'] })
      : node
  ));
  const out = await CheckGlobalRowsSemantic0(makeInput0({
    LegacyGlobalProofDAG: dag,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, `CheckGlobalRowsSemantic0.row.${coordinate}`);
  assert.equal(
    out.Witness.reason,
    'global row node premise list must exactly match its coordinate contract',
  );
});

test('bounded global row checker rejects quotient-only row coordinates', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  const coordinate = GLOBAL_GENERIC_ROW_NODE_IDS0[0];
  dag.Nodes = dag.Nodes.map((node) => (
    node.id === coordinate
      ? withoutDigest0(node, { mode: 'Quot' })
      : node
  ));
  const out = await CheckGlobalRowsSemantic0(makeInput0({
    LegacyGlobalProofDAG: dag,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, `CheckGlobalRowsSemantic0.row.${coordinate}`);
  assert.equal(out.Witness.reason, 'global row coordinate derivation requires Full mode');
});

test('bounded global row checker rejects a stale row binding digest', async () => {
  const base = makeInput0();
  const input = {
    ...base,
    SemanticRows: {
      ...base.SemanticRows,
      bindings: base.SemanticRows.bindings.map((entry) => (
        entry.coordinate === 'G.TraceCert.proof'
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
  const out = await CheckGlobalRowsSemantic0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalRowsSemantic0.semanticRowsSuite');
  assert.equal(
    out.Witness.reason,
    'global row binding must exactly match the computed node and executable coordinate contract',
  );
});

test('bounded global row checker propagates a mutated locked-NAND threshold contract through the predecessor', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  dag.Nodes = dag.Nodes.map((node) => (
    node.id === 'G.ThresholdCert.proof'
      ? withoutDigest0(node, {
          payload: {
            ...node.payload,
            residualSlackMax: 5,
          },
        })
      : node
  ));
  const out = await CheckGlobalRowsSemantic0(makeInput0({
    LegacyGlobalProofDAG: dag,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalRowsSemantic0.predecessorInfrastructure');
  assert.equal(
    out.Witness.reason,
    'global infrastructure predecessor rejected before row-coordinate upgrade',
  );
});

test('bounded global row derivation digests bind every coordinate surface', async () => {
  const out = await CheckGlobalRowsSemantic0(makeInput0());

  assert.equal(out.tag, 'accept');
  for (const entry of out.NF.rowDerivationDigests) {
    assert.equal(entry.digest.alg, 'SHA256');
    assert.equal(entry.nodeDigest.alg, 'SHA256');
    assert.equal(entry.premiseDigest.alg, 'SHA256');
    assert.equal(entry.conclusionDigest.alg, 'SHA256');
    assert.equal(entry.payloadDigest.alg, 'SHA256');
    assert.equal(entry.boundsDigest.alg, 'SHA256');
    assert.equal(entry.checkerContractDigest.alg, 'SHA256');
  }
});
