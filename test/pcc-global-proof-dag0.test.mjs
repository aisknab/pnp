import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckGlobalProofDAG0,
  GLOBAL_DAG_REQUIRED_FINALS0,
  GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0,
  makeGlobalProofDAGNode0,
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  KERNEL_RULES0,
} from '../pcc-kimpl0.mjs';

import {
  ROW_REQUIRED_FAMILIES0,
} from '../pcc-rows0.mjs';

test('CheckGlobalProofDAG0 accepts the synthetic global proof DAG', async () => {
  const out = await CheckGlobalProofDAG0(makeSyntheticGlobalProofDAG0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAG0');
  assert.equal(out.NF.kind, 'GlobalProofDAG0NF');
  assert.equal(out.NF.kernelRuleCount, KERNEL_RULES0.length);
  assert.equal(out.NF.rowFamilyCount, ROW_REQUIRED_FAMILIES0.length);
  assert.equal(out.NF.packageTheoremCount, GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0.length);
  assert.deepEqual(out.NF.finalTheorems, GLOBAL_DAG_REQUIRED_FINALS0);
  assert.equal(out.Digest.alg, 'SHA256');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckGlobalProofDAG0 rejects a forward premise', async () => {
  const dag = makeSyntheticGlobalProofDAG0();

  dag.Nodes = [
    makeGlobalProofDAGNode0({
      id: 'bad.forward',
      kind: 'kernel',
      label: 'bad.forward',
      premises: ['later.node'],
    }),
    makeGlobalProofDAGNode0({
      id: 'later.node',
      kind: 'kernel',
      label: 'later.node',
    }),
    ...dag.Nodes,
  ];

  const out = await CheckGlobalProofDAG0(dag);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGlobalProofDAG0');
  assert.equal(out.Coord, 'CheckGlobalProofDAG0.nodes');
  assert.deepEqual(out.Path, ['Nodes', 0, 'premises', 0]);
  assert.equal(out.Witness.reason, 'premise must reference an earlier global proof node');
});

test('CheckGlobalProofDAG0 rejects missing row-family proof coverage', async () => {
  const dag = makeSyntheticGlobalProofDAG0();

  dag.Nodes = dag.Nodes.filter((node) => node.id !== 'Row.PkgC');

  const out = await CheckGlobalProofDAG0(dag);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGlobalProofDAG0');
  assert.equal(out.Coord, 'CheckGlobalProofDAG0.coverage');
  assert.deepEqual(out.Path, ['Nodes', 'coverage', 'row', 'PkgC']);
  assert.equal(out.Witness.reason, 'GlobalProofDAG0 is missing a row-family proof node');
});

test('CheckGlobalProofDAG0 rejects a forbidden import edge', async () => {
  const dag = makeSyntheticGlobalProofDAG0();

  dag.ImportGraph = {
    ...dag.ImportGraph,
    edges: [
      ['O', 'G'],
    ],
  };

  const out = await CheckGlobalProofDAG0(dag);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGlobalProofDAG0');
  assert.equal(out.Coord, 'CheckGlobalProofDAG0.imports');
  assert.deepEqual(out.Path, ['ImportGraph', 'edges', 0]);
  assert.equal(out.Witness.reason, 'ImportGraph contains a forbidden package edge');
});

test('CheckGlobalProofDAG0 rejects quotient nodes constructing full replacements', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  const index = dag.Nodes.findIndex((node) => node.id === 'Mode.Firewall');

  dag.Nodes[index] = makeGlobalProofDAGNode0({
    id: 'Mode.Firewall',
    kind: 'mode',
    label: 'ModeFirewall',
    premises: [
      'K.Transport',
    ],
    mode: 'Quot',
    payload: {
      constructiveFullReplacement: true,
    },
    conclusion: {
      tag: 'ModeFirewallAccepted0',
    },
  });

  const out = await CheckGlobalProofDAG0(dag);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGlobalProofDAG0');
  assert.equal(out.Coord, 'CheckGlobalProofDAG0.nodes');
  assert.deepEqual(out.Path, ['Nodes', index, 'payload']);
  assert.equal(out.Witness.reason, 'quotient proof node cannot construct a full-mode replacement');
});

test('CheckGlobalProofDAG0 rejects a constructive Gain route without VerifyDW acceptance', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  const index = dag.Nodes.findIndex((node) => node.id === 'Package.E.VerifyDWSoundness');

  dag.Nodes[index] = makeGlobalProofDAGNode0({
    id: 'Package.E.VerifyDWSoundness',
    kind: 'package',
    label: 'E.VerifyDWSoundness',
    premises: [
      'Bounds.Polynomial',
      'NoMin.Global',
      'Mode.Firewall',
      'Import.Acyclic',
    ],
    route: {
      kind: 'Gain',
      verifyDWAccepted: false,
    },
    conclusion: {
      tag: 'PackageTheoremAccepted0',
      theorem: 'E.VerifyDWSoundness',
    },
  });

  const out = await CheckGlobalProofDAG0(dag);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGlobalProofDAG0');
  assert.equal(out.Coord, 'CheckGlobalProofDAG0.nodes');
  assert.deepEqual(out.Path, ['Nodes', index, 'route', 'verifyDWAccepted']);
  assert.equal(out.Witness.reason, 'constructive Gain route must compile to VerifyDW acceptance');
});

test('CheckGlobalProofDAG0 rejects a descent route without rank decrease', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  const index = dag.Nodes.findIndex((node) => node.id === 'Package.HB.NegativeClosure');

  dag.Nodes[index] = makeGlobalProofDAGNode0({
    id: 'Package.HB.NegativeClosure',
    kind: 'package',
    label: 'HB.NegativeClosure',
    premises: [
      'Bounds.Polynomial',
      'NoMin.Global',
      'Mode.Firewall',
      'Import.Acyclic',
    ],
    route: {
      kind: 'Descent',
      rankDecreases: true,
      rankBefore: [3, 0],
      rankAfter: [3, 0],
    },
    conclusion: {
      tag: 'PackageTheoremAccepted0',
      theorem: 'HB.NegativeClosure',
    },
  });

  const out = await CheckGlobalProofDAG0(dag);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGlobalProofDAG0');
  assert.equal(out.Coord, 'CheckGlobalProofDAG0.nodes');
  assert.deepEqual(out.Path, ['Nodes', index, 'route', 'rankAfter']);
  assert.equal(out.Witness.reason, 'Descent route rankAfter must be lexicographically smaller than rankBefore');
});

test('CheckGlobalProofDAG0 rejects non-polynomial node bounds', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  const index = dag.Nodes.findIndex((node) => node.id === 'Bounds.Polynomial');

  dag.Nodes[index] = {
    ...dag.Nodes[index],
    bounds: {
      polynomial: false,
      exponent: 8,
    },
  };

  const out = await CheckGlobalProofDAG0(dag);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGlobalProofDAG0');
  assert.equal(out.Coord, 'CheckGlobalProofDAG0.nodes');
  assert.deepEqual(out.Path, ['Nodes', index, 'bounds', 'polynomial']);
  assert.equal(out.Witness.reason, 'global proof node bounds must be polynomial');
});

test('CheckGlobalProofDAG0 rejects executable hidden minimization', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  const index = dag.Nodes.findIndex((node) => node.id === 'NoMin.Global');

  dag.Nodes[index] = {
    ...dag.Nodes[index],
    payload: {
      body: [
        'minimumEquivalent',
      ],
    },
  };

  const out = await CheckGlobalProofDAG0(dag);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGlobalProofDAG0');
  assert.equal(out.Coord, 'CheckGlobalProofDAG0.noHiddenMin');
  assert.deepEqual(out.Path, ['GlobalProofDAG0', 'Nodes', index, 'payload', 'body', 0]);
  assert.equal(out.Witness.reason, 'forbidden minimization symbol appears in executable position');
});

test('CheckGlobalProofDAG0 rejects opaque proof material', async () => {
  const dag = makeSyntheticGlobalProofDAG0();

  dag.PiGlobalDAG = {
    ...dag.PiGlobalDAG,
    opaqueProof: {
      bytes: 'not allowed',
    },
  };

  const out = await CheckGlobalProofDAG0(dag);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGlobalProofDAG0');
  assert.equal(out.Coord, 'CheckGlobalProofDAG0.opaqueProof');
  assert.deepEqual(out.Path, ['GlobalProofDAG0', 'PiGlobalDAG', 'opaqueProof']);
  assert.equal(out.Witness.reason, 'opaque proof material is not allowed in GlobalProofDAG0');
});

test('CheckGlobalProofDAG0 binds G locked NAND theorem to explicit global proof nodes', async (t) => {
  await t.test('rejects missing G threshold proof dependency from package theorem', async () => {
    const dag = makeSyntheticGlobalProofDAG0();
    const node = dag.Nodes.find((entry) => entry.id === 'Package.G.LockedNANDThreshold');

    node.premises = node.premises.filter((premise) => premise !== 'G.ThresholdCert.proof');

    const out = await CheckGlobalProofDAG0(dag);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckGlobalProofDAG0');
    assert.equal(out.Coord, 'CheckGlobalProofDAG0.gLockedNANDProofs');
    assert.deepEqual(out.Path, ['Nodes', 'gLockedNANDProofs', 'Package.G.LockedNANDThreshold', 'premises']);
    assert.equal(out.Witness.reason, 'Package.G.LockedNANDThreshold must depend on G.ThresholdCert.proof and global safety roots');
  });

  await t.test('rejects wrong G threshold proof conclusion theorem', async () => {
    const dag = makeSyntheticGlobalProofDAG0();
    const node = dag.Nodes.find((entry) => entry.id === 'G.ThresholdCert.proof');

    node.conclusion = {
      ...node.conclusion,
      theorem: 'WrongTheorem',
    };

    const out = await CheckGlobalProofDAG0(dag);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckGlobalProofDAG0');
    assert.equal(out.Coord, 'CheckGlobalProofDAG0.gLockedNANDProofs');
    assert.deepEqual(out.Path, ['Nodes', 'gLockedNANDProofs', 'G.ThresholdCert.proof', 'conclusion', 'theorem']);
    assert.equal(out.Witness.reason, 'G locked NAND proof node conclusion mismatch');
  });

  await t.test('rejects wrong G threshold proof payload residual slack', async () => {
    const dag = makeSyntheticGlobalProofDAG0();
    const node = dag.Nodes.find((entry) => entry.id === 'G.ThresholdCert.proof');

    node.payload = {
      ...node.payload,
      residualSlackMax: 5,
    };

    const out = await CheckGlobalProofDAG0(dag);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckGlobalProofDAG0');
    assert.equal(out.Coord, 'CheckGlobalProofDAG0.gLockedNANDProofs');
    assert.deepEqual(out.Path, ['Nodes', 'gLockedNANDProofs', 'G.ThresholdCert.proof', 'payload', 'residualSlackMax']);
    assert.equal(out.Witness.reason, 'G threshold proof node payload mismatch');
  });
});
