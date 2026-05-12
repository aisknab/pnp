import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckGPack0,
  CheckRowFamG0,
  GPACK_ROWFAMG_REQUIRED_ROWS0,
  LOCKED_NAND_MACRO_SIGNATURES0,
  computeLockedNANDBaseline0,
  makeSyntheticGPack0,
  makeSyntheticRowFamG0,
} from '../pcc-gpack0.mjs';

test('CheckGPack0 accepts the synthetic locked NAND artefact pack', async () => {
  const out = await CheckGPack0(makeSyntheticGPack0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGPack0');
  assert.equal(out.NF.kind, 'GPack0NF');
  assert.equal(out.NF.gateCount, 2);
  assert.equal(out.NF.residualSlackMax, 4);
  assert.equal(out.NF.fullWordSize, out.NF.baseline + 4);
  assert.equal(out.Digest.alg, 'SHA256');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckRowFamG0 accepts the synthetic locked NAND row family', async () => {
  const out = await CheckRowFamG0(makeSyntheticRowFamG0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckRowFamG0');
  assert.equal(out.NF.kind, 'RowFamG0NF');
  assert.equal(out.NF.rowCount, GPACK_ROWFAMG_REQUIRED_ROWS0.length);
});

test('locked NAND baseline formula is stable', () => {
  const baseline = computeLockedNANDBaseline0({
    gateCount: 2,
    equalityOccurrences: 4,
    constZeroOccurrences: 1,
    constOneOccurrences: 1,
  });

  assert.equal(baseline, 18 * 2 + 10 * 4 + 3 * 1 + 2 * 1 + 2 * (3 * 2 - 1));
});

test('macro truth signatures include the locked NAND distinguished outputs', () => {
  assert.equal(LOCKED_NAND_MACRO_SIGNATURES0.Equality10.outputs.a8, '00001001');
  assert.equal(LOCKED_NAND_MACRO_SIGNATURES0.ConstOne2.outputs.b2, '0001');
  assert.equal(LOCKED_NAND_MACRO_SIGNATURES0.ConstZero3.outputs.d3, '0010');
  assert.equal(LOCKED_NAND_MACRO_SIGNATURES0.NANDTrace18.outputs.q16, '0000000000011110');
});

test('CheckGPack0 rejects duplicate slot allocation', async () => {
  const gpack = makeSyntheticGPack0();

  gpack.SlotAlloc = {
    ...gpack.SlotAlloc,
    families: {
      ...gpack.SlotAlloc.families,
      O: [
        gpack.SlotAlloc.families.X[0],
        ...gpack.SlotAlloc.families.O.slice(1),
      ],
    },
  };

  const out = await CheckGPack0(gpack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGPack0');
  assert.equal(out.Coord, 'CheckGPack0.slotAlloc');
  assert.deepEqual(out.Path, ['SlotAlloc', 'families', 'O', 0]);
  assert.equal(out.Witness.reason, 'SlotAlloc slots must be globally unique');
});

test('CheckGPack0 rejects a bad equality macro truth signature', async () => {
  const gpack = makeSyntheticGPack0();

  gpack.MacroTables = {
    ...gpack.MacroTables,
    macros: {
      ...gpack.MacroTables.macros,
      Equality10: {
        ...gpack.MacroTables.macros.Equality10,
        outputs: {
          ...gpack.MacroTables.macros.Equality10.outputs,
          a8: '00000000',
        },
      },
    },
  };

  const out = await CheckGPack0(gpack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGPack0');
  assert.equal(out.Coord, 'CheckGPack0.macroTables');
  assert.deepEqual(out.Path, ['MacroTables', 'macros', 'Equality10', 'outputs', 'a8']);
  assert.equal(out.Witness.reason, 'locked NAND macro truth signature mismatch');
});

test('CheckGPack0 rejects a bad baseline certificate', async () => {
  const gpack = makeSyntheticGPack0();

  gpack.BaselineCert = {
    ...gpack.BaselineCert,
    baseline: gpack.BaselineCert.baseline + 1,
  };

  const out = await CheckGPack0(gpack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGPack0');
  assert.equal(out.Coord, 'CheckGPack0.baseline');
  assert.deepEqual(out.Path, ['BaselineCert', 'baseline']);
  assert.equal(out.Witness.reason, 'BaselineCert baseline mismatch');
});

test('CheckGPack0 rejects final lock leakage before final output construction', async () => {
  const gpack = makeSyntheticGPack0();

  gpack.SepCert = {
    ...gpack.SepCert,
    finalLockOnlyFinal: false,
  };

  const out = await CheckGPack0(gpack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGPack0');
  assert.equal(out.Coord, 'CheckGPack0.sep');
  assert.deepEqual(out.Path, ['SepCert', 'finalLockOnlyFinal']);
  assert.equal(out.Witness.reason, 'SepCert must certify finalLockOnlyFinal');
});

test('CheckGPack0 rejects a failed coherence witness', async () => {
  const gpack = makeSyntheticGPack0();

  gpack.CohCert = {
    ...gpack.CohCert,
    allChecksOne: false,
  };

  const out = await CheckGPack0(gpack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGPack0');
  assert.equal(out.Coord, 'CheckGPack0.coh');
  assert.deepEqual(out.Path, ['CohCert', 'allChecksOne']);
  assert.equal(out.Witness.reason, 'CohCert must assign all distinguished checks the value one');
});

test('CheckGPack0 rejects residual slack above four', async () => {
  const gpack = makeSyntheticGPack0();

  gpack.ThresholdCert = {
    ...gpack.ThresholdCert,
    residualSlackMax: 5,
  };

  const out = await CheckGPack0(gpack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGPack0');
  assert.equal(out.Coord, 'CheckGPack0.threshold');
  assert.deepEqual(out.Path, ['ThresholdCert', 'residualSlackMax']);
  assert.equal(out.Witness.reason, 'ThresholdCert residual slack must be an integer at most four');
});

test('CheckGPack0 rejects executable hidden minimization in expanded artefacts', async () => {
  const gpack = makeSyntheticGPack0();

  gpack.NoMinCert = {
    ...gpack.NoMinCert,
    expandedArtifacts: [
      {
        kind: 'GeneratedLockedNANDTemplate0',
        body: [
          'minimumEquivalent',
        ],
      },
    ],
  };

  const out = await CheckGPack0(gpack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGPack0');
  assert.equal(out.Coord, 'CheckGPack0.noHiddenMin');
  assert.deepEqual(out.Path, ['GPack0', 'NoMinCert', 'expandedArtifacts', 0, 'body', 0]);
  assert.equal(out.Witness.reason, 'forbidden minimization symbol appears in executable position');
});

test('CheckGPack0 rejects opaque proof blobs', async () => {
  const gpack = makeSyntheticGPack0();

  gpack.PiG = {
    ...gpack.PiG,
    proofBlob: {
      bytes: 'not allowed',
    },
  };

  const out = await CheckGPack0(gpack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGPack0');
  assert.equal(out.Coord, 'CheckGPack0.opaqueProof');
  assert.deepEqual(out.Path, ['GPack0', 'PiG', 'proofBlob']);
  assert.equal(out.Witness.reason, 'opaque proof material is not allowed in GPack0');
});

test('CheckRowFamG0 rejects missing locked NAND row coverage', async () => {
  const rowFam = makeSyntheticRowFamG0();

  rowFam.rows = rowFam.rows.filter((row) => row.rowKind !== 'ThresholdCert');

  const out = await CheckRowFamG0(rowFam);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckRowFamG0');
  assert.equal(out.Coord, 'CheckRowFamG0.coverage');
  assert.deepEqual(out.Path, ['rows', 'coverage', 'ThresholdCert']);
  assert.equal(out.Witness.reason, 'RowFamG0 is missing a required locked NAND row');
});

test('CheckRowFamG0 wraps GPack rejection', async () => {
  const rowFam = makeSyntheticRowFamG0();

  rowFam.GPack.ThresholdCert = {
    ...rowFam.GPack.ThresholdCert,
    fullWordSize: rowFam.GPack.ThresholdCert.fullWordSize + 1,
  };

  const out = await CheckRowFamG0(rowFam);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckRowFamG0');
  assert.equal(out.Coord, 'CheckRowFamG0.GPack');
  assert.deepEqual(out.Path, ['GPack']);
  assert.equal(out.Witness.reason, 'CheckGPack0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckGPack0.threshold');
});

test('CheckGPack0 rejects theorem-bearing locked NAND certificate and derivation tampering', async (t) => {
  const cases = [
    {
      name: 'BaselineCert.lowerBound=false',
      coord: 'CheckGPack0.baseline',
      root: 'BaselineCert',
      mutate(gpack) {
        gpack.BaselineCert.lowerBound = false;
      },
    },
    {
      name: 'BaselineCert.distinctNonconstantNonprojection=false',
      coord: 'CheckGPack0.baseline',
      root: 'BaselineCert',
      mutate(gpack) {
        gpack.BaselineCert.distinctNonconstantNonprojection = false;
      },
    },
    {
      name: 'BaselineCert.derivation.totalFunctions mismatch',
      coord: 'CheckGPack0.baseline',
      root: 'BaselineCert',
      mutate(gpack) {
        gpack.BaselineCert.derivation.totalFunctions += 1;
      },
    },
    {
      name: 'TraceCert.traceCoherent=false',
      coord: 'CheckGPack0.trace',
      root: 'TraceCert',
      mutate(gpack) {
        gpack.TraceCert.traceCoherent = false;
      },
    },
    {
      name: 'TraceCert.derivation.topologicalInduction=false',
      coord: 'CheckGPack0.trace',
      root: 'TraceCert',
      mutate(gpack) {
        gpack.TraceCert.derivation.topologicalInduction = false;
      },
    },
    {
      name: 'ThresholdCert.lockedThreshold=false',
      coord: 'CheckGPack0.threshold',
      root: 'ThresholdCert',
      mutate(gpack) {
        gpack.ThresholdCert.lockedThreshold = false;
      },
    },
    {
      name: 'ThresholdCert.satIffMinAboveBaseline=false',
      coord: 'CheckGPack0.threshold',
      root: 'ThresholdCert',
      mutate(gpack) {
        gpack.ThresholdCert.satIffMinAboveBaseline = false;
      },
    },
    {
      name: 'ThresholdCert.unsatMinEqualsBaseline=false',
      coord: 'CheckGPack0.threshold',
      root: 'ThresholdCert',
      mutate(gpack) {
        gpack.ThresholdCert.unsatMinEqualsBaseline = false;
      },
    },
    {
      name: 'ThresholdCert.derivation.satUpperBoundExtraGates mismatch',
      coord: 'CheckGPack0.threshold',
      root: 'ThresholdCert',
      mutate(gpack) {
        gpack.ThresholdCert.derivation.satUpperBoundExtraGates = 5;
      },
    },
  ];

  for (const testCase of cases) {
    await t.test(testCase.name, async () => {
      const gpack = makeSyntheticGPack0();

      testCase.mutate(gpack);

      const out = await CheckGPack0(gpack);

      assert.equal(out.tag, 'reject');
      assert.equal(out.checker, 'CheckGPack0');
      assert.equal(out.Coord, testCase.coord);
      assert.equal(out.Path[0], testCase.root);
      assert.equal(typeof out.Witness.reason, 'string');
    });
  }
});


test('CheckGPack0 and CheckRowFamG0 bind locked NAND derivations to proof refs', async (t) => {
  await t.test('CheckGPack0 rejects missing BaselineCert derivation proofRef', async () => {
    const gpack = makeSyntheticGPack0();

    delete gpack.BaselineCert.derivation.proofRef;

    const out = await CheckGPack0(gpack);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckGPack0');
    assert.equal(out.Coord, 'CheckGPack0.baseline');
    assert.deepEqual(out.Path, ['BaselineCert', 'derivation', 'proofRef']);
    assert.equal(out.Witness.reason, 'G derivation proofRef must be an object');
  });

  await t.test('CheckGPack0 rejects wrong ThresholdCert derivation proofRef id', async () => {
    const gpack = makeSyntheticGPack0();

    gpack.ThresholdCert.derivation.proofRef = {
      ...gpack.ThresholdCert.derivation.proofRef,
      id: 'G.Wrong.proof',
    };

    const out = await CheckGPack0(gpack);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckGPack0');
    assert.equal(out.Coord, 'CheckGPack0.threshold');
    assert.deepEqual(out.Path, ['ThresholdCert', 'derivation', 'proofRef', 'id']);
    assert.equal(out.Witness.reason, 'G derivation proofRef mismatch');
  });

  await t.test('CheckRowFamG0 rejects row proofRef drift from GPack derivation proofRef', async () => {
    const rowFam = makeSyntheticRowFamG0();
    const thresholdRow = rowFam.rows.find((row) => row.rowKind === 'ThresholdCert');

    thresholdRow.proofRef = {
      ...thresholdRow.proofRef,
      id: 'G.Wrong.proof',
    };

    const out = await CheckRowFamG0(rowFam);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckRowFamG0');
    assert.ok(
      out.Coord === 'CheckRowFamG0.derivationProofRefs' ||
      out.Coord === 'CheckRowFamG0.rows',
    );
    assert.equal(typeof out.Witness.reason, 'string');
  });
});


test('CheckGPack0 resolves locked NAND derivation proof refs to typed non-opaque acyclic proof nodes', async (t) => {
  await t.test('rejects missing PiG proofNodes', async () => {
    const gpack = makeSyntheticGPack0();

    delete gpack.PiG.proofNodes;

    const out = await CheckGPack0(gpack);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckGPack0');
    assert.equal(out.Coord, 'CheckGPack0.derivationProofNodes');
    assert.deepEqual(out.Path, ['PiG', 'proofNodes']);
    assert.equal(out.Witness.reason, 'PiG must include proofNodes');
  });

  await t.test('rejects wrong ThresholdCert proof-node rule', async () => {
    const gpack = makeSyntheticGPack0();
    const node = gpack.PiG.proofNodes.find((entry) => entry.id === 'G.ThresholdCert.proof');

    node.rule = 'WrongRule0';

    const out = await CheckGPack0(gpack);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckGPack0');
    assert.equal(out.Coord, 'CheckGPack0.derivationProofNodes');
    assert.deepEqual(out.Path, ['PiG', 'proofNodes', 'G.ThresholdCert.proof', 'rule']);
    assert.equal(out.Witness.reason, 'G proof node field mismatch');
  });

  await t.test('rejects opaque proof material inside a G proof node', async () => {
    const gpack = makeSyntheticGPack0();
    const node = gpack.PiG.proofNodes.find((entry) => entry.id === 'G.BaselineCert.proof');

    node.proofBlob = {
      bytes: 'opaque',
    };

    const out = await CheckGPack0(gpack);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckGPack0');
    assert.equal(out.Coord, 'CheckGPack0.derivationProofNodes');
    assert.deepEqual(out.Path, ['PiG', 'proofNodes', 'G.BaselineCert.proof', 'proofBlob']);
    assert.equal(out.Witness.reason, 'G proof node must not contain opaque proof material');
  });

  await t.test('rejects cyclic G proof-node premises', async () => {
    const gpack = makeSyntheticGPack0();
    const baseline = gpack.PiG.proofNodes.find((entry) => entry.id === 'G.BaselineCert.proof');

    baseline.premises = [
      'G.ThresholdCert.proof',
    ];

    const out = await CheckGPack0(gpack);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckGPack0');
    assert.equal(out.Coord, 'CheckGPack0.derivationProofNodes');
    assert.equal(typeof out.Witness.reason, 'string');
  });
});


test('CheckGPack0 rejects explicit locked NAND theorem-obligation tampering', async (t) => {
  const cases = [
    {
      name: 'BaselineCert.directWireOutputLowerBound=false',
      coord: 'CheckGPack0.baseline',
      path0: 'BaselineCert',
      mutate(gpack) {
        gpack.BaselineCert.directWireOutputLowerBound = false;
      },
    },
    {
      name: 'BaselineCert.derivation.directWireOutputLowerBound=false',
      coord: 'CheckGPack0.baseline',
      path0: 'BaselineCert',
      mutate(gpack) {
        gpack.BaselineCert.derivation.directWireOutputLowerBound = false;
      },
    },
    {
      name: 'TraceCert.traceEquivalence=false',
      coord: 'CheckGPack0.trace',
      path0: 'TraceCert',
      mutate(gpack) {
        gpack.TraceCert.traceEquivalence = false;
      },
    },
    {
      name: 'ThresholdCert.zeroOutputConvention=false',
      coord: 'CheckGPack0.threshold',
      path0: 'ThresholdCert',
      mutate(gpack) {
        gpack.ThresholdCert.zeroOutputConvention = false;
      },
    },
    {
      name: 'ThresholdCert.finalLockSeparation=false',
      coord: 'CheckGPack0.threshold',
      path0: 'ThresholdCert',
      mutate(gpack) {
        gpack.ThresholdCert.finalLockSeparation = false;
      },
    },
    {
      name: 'ThresholdCert.derivation.zeroOutputConvention=false',
      coord: 'CheckGPack0.threshold',
      path0: 'ThresholdCert',
      mutate(gpack) {
        gpack.ThresholdCert.derivation.zeroOutputConvention = false;
      },
    },
    {
      name: 'ThresholdCert.derivation.finalLockSeparation=false',
      coord: 'CheckGPack0.threshold',
      path0: 'ThresholdCert',
      mutate(gpack) {
        gpack.ThresholdCert.derivation.finalLockSeparation = false;
      },
    },
    {
      name: 'PiG Baseline proof payload directWireOutputLowerBound=false',
      coord: 'CheckGPack0.derivationProofNodes',
      path0: 'PiG',
      mutate(gpack) {
        const node = gpack.PiG.proofNodes.find((entry) => entry.id === 'G.BaselineCert.proof');
        node.payload.directWireOutputLowerBound = false;
      },
    },
    {
      name: 'PiG Threshold proof payload zeroOutputConvention=false',
      coord: 'CheckGPack0.derivationProofNodes',
      path0: 'PiG',
      mutate(gpack) {
        const node = gpack.PiG.proofNodes.find((entry) => entry.id === 'G.ThresholdCert.proof');
        node.payload.zeroOutputConvention = false;
      },
    },
    {
      name: 'PiG Threshold proof payload finalLockSeparation=false',
      coord: 'CheckGPack0.derivationProofNodes',
      path0: 'PiG',
      mutate(gpack) {
        const node = gpack.PiG.proofNodes.find((entry) => entry.id === 'G.ThresholdCert.proof');
        node.payload.finalLockSeparation = false;
      },
    },
  ];

  for (const testCase of cases) {
    await t.test(testCase.name, async () => {
      const gpack = makeSyntheticGPack0();

      testCase.mutate(gpack);

      const out = await CheckGPack0(gpack);

      assert.equal(out.tag, 'reject');
      assert.equal(out.checker, 'CheckGPack0');
      assert.equal(out.Coord, testCase.coord);
      assert.equal(out.Path[0], testCase.path0);
      assert.equal(typeof out.Witness.reason, 'string');
    });
  }
});
