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
  CheckGlobalRowSemantic0,
  makeGlobalRowSemanticInput0,
  makeGlobalRowSemanticSuite0,
} from '../pcc-global-row-semantic0.mjs';

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

function makeInput0({
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  RowPack = makeSyntheticRowPack0(),
  RowFamG = makeSyntheticRowFamG0(),
} = {}) {
  const KBundle = makeKBundleReflectionSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  return makeGlobalRowSemanticInput0({
    KBundle,
    LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations:
      makeGlobalInfrastructureSemanticSuite0({ LegacyGlobalProofDAG }),
    RowPack,
    RowFamG,
    SemanticRows: makeGlobalRowSemanticSuite0({
      LegacyGlobalProofDAG,
      RowPack,
      RowFamG,
    }),
  });
}

function withoutDigest0(node, changes) {
  const out = { ...node, ...changes };
  delete out.Digest;
  delete out.digest;
  return out;
}

test('global row semantic checker derives all required row families and locked-NAND proof rows', async () => {
  const out = await CheckGlobalRowSemantic0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalRowSemantic0');
  assert.equal(out.NF.globalInfrastructureSemanticReady, true);
  assert.equal(out.NF.globalRowSemanticReady, true);
  assert.equal(out.NF.globalRowFamilyDerivationsReady, true);
  assert.equal(out.NF.globalLockedNANDProofRowsReady, true);
  assert.equal(out.NF.globalRowDerivationsReady, true);
  assert.equal(out.NF.familyDerivationCount, 39);
  assert.equal(out.NF.lockedNANDProofRowDerivationCount, 3);
  assert.equal(out.NF.totalGlobalRowDerivationCount, 42);
  assert.equal(out.NF.semanticGlobalRowNodeIds.length, 42);
  assert.equal(out.NF.semanticGlobalRowNodeIds.includes('Row.BIface'), true);
  assert.equal(out.NF.semanticGlobalRowNodeIds.includes('Row.PACK'), true);
  assert.equal(
    out.NF.semanticGlobalRowNodeIds.includes('G.ThresholdCert.proof'),
    true,
  );
  assert.equal(out.NF.mathematicalGovernedUniverseCompletenessNotClaimed, true);
  assert.equal(out.NF.primitiveProofRuleSoundnessNotClaimedHere, true);
  assert.equal(out.NF.globalPackageDerivationsReady, false);
  assert.equal(out.NF.globalFinalDerivationsReady, false);
  assert.equal(out.NF.globalSemanticNodeDerivationsReady, false);

  const threshold = out.NF.lockedNANDProofRowDerivations.find(
    (entry) => entry.rowKind === 'ThresholdCert',
  );
  assert.equal(threshold.theorem, 'LockedNANDThreshold');
  assert.equal(threshold.rule, 'LockedNANDThreshold0');
  assert.equal(threshold.ready, true);
});

test('global row semantic checker rejects caller-supplied readiness assertions', async () => {
  const input = {
    ...makeInput0(),
    globalRowDerivationsReady: true,
  };
  const out = await CheckGlobalRowSemantic0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalRowSemantic0.input');
  assert.deepEqual(out.Path, ['globalRowDerivationsReady']);
  assert.equal(
    out.Witness.reason,
    'global row semantic checker rejects caller-supplied readiness or truth assertions',
  );
});

test('global row semantic checker rejects a stale family binding digest', async () => {
  const base = makeInput0();
  const input = {
    ...base,
    SemanticRows: {
      ...base.SemanticRows,
      familyBindings: base.SemanticRows.familyBindings.map((entry) => (
        entry.family === 'E'
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
  const out = await CheckGlobalRowSemantic0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalRowSemantic0.semanticRowsSuite');
  assert.equal(
    out.Witness.reason,
    'global row semantic suite must exactly match the computed row, global-node, and locked-NAND bindings',
  );
});

test('global row semantic checker rejects a malformed global row-family premise list', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  dag.Nodes = dag.Nodes.map((node) => (
    node.id === 'Row.E'
      ? withoutDigest0(node, { premises: ['K.Record'] })
      : node
  ));
  const out = await CheckGlobalRowSemantic0(makeInput0({
    LegacyGlobalProofDAG: dag,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalRowSemantic0.rowFamily.E');
  assert.equal(
    out.Witness.reason,
    'global row-family node must retain the exact Record and Transport prerequisites',
  );
});

test('global row semantic checker rejects a row pack with a non-accept selected route', async () => {
  const rowPack = makeSyntheticRowPack0();
  rowPack.Rows = rowPack.Rows.map((row) => (
    row.FamilyID === 'BN4'
      ? {
          ...row,
          CandidateRoutes: ['Neutral'],
          ActiveRouteSet: ['Neutral'],
          SelectedRoute: 'Neutral',
        }
      : row
  ));
  const out = await CheckGlobalRowSemantic0(makeInput0({ RowPack: rowPack }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalRowSemantic0.rowFamily.BN4');
  assert.equal(
    out.Witness.reason,
    'executable row record must exactly match its required family contract',
  );
});

test('global row semantic checker rejects a mutated locked-NAND threshold derivation', async () => {
  const rowFamG = makeSyntheticRowFamG0();
  rowFamG.GPack.ThresholdCert = {
    ...rowFamG.GPack.ThresholdCert,
    derivation: {
      ...rowFamG.GPack.ThresholdCert.derivation,
      residualSlackMax: 5,
    },
  };
  const out = await CheckGlobalRowSemantic0(makeInput0({ RowFamG: rowFamG }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalRowSemantic0.gpack');
  assert.equal(
    out.Witness.reason,
    'locked-NAND GPack rejected before proof-row semantic upgrade',
  );
});

test('global row semantic checker rejects missing row-family coverage before semantic upgrade', async () => {
  const rowPack = makeSyntheticRowPack0();
  rowPack.Rows = rowPack.Rows.filter((row) => row.FamilyID !== 'Packet');
  const out = await CheckGlobalRowSemantic0(makeInput0({ RowPack: rowPack }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalRowSemantic0.rows');
  assert.equal(
    out.Witness.reason,
    'row package rejected before global row semantic upgrade',
  );
});

test('global row semantic derivation digests bind global nodes and executable row records', async () => {
  const out = await CheckGlobalRowSemantic0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.globalRowDerivationDigests.length, 42);
  for (const entry of out.NF.globalRowDerivationDigests) {
    assert.equal(entry.digest.alg, 'SHA256');
    assert.equal(entry.globalNodeDigest.alg, 'SHA256');
    assert.equal(entry.executableRecordDigest.alg, 'SHA256');
    assert.equal(entry.checkerContractDigest.alg, 'SHA256');
    assert.equal(entry.conclusionDigest.alg, 'SHA256');
  }
});
