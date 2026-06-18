import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckFinal0,
  CheckRowFamFinal0,
  FINAL0_THEOREM_IDS0,
  ROWFAMFINAL_REQUIRED_ROWS0,
  makeSyntheticFinalTheorem0,
  makeSyntheticRowFamFinal0,
} from '../pcc-final0.mjs';

test('CheckFinal0 accepts the synthetic final theorem artefact', async () => {
  const out = await CheckFinal0(makeSyntheticFinalTheorem0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckFinal0');
  assert.equal(out.NF.kind, 'FinalTheorem0NF');
  assert.deepEqual(out.NF.theoremIds, FINAL0_THEOREM_IDS0);
  assert.equal(out.NF.residualSlackBound, 4);
  assert.equal(out.NF.exportedStatement.consequent, 'P = NP');
  assert.equal(out.Digest.alg, 'SHA256');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckRowFamFinal0 accepts the synthetic final row family', async () => {
  const out = await CheckRowFamFinal0(makeSyntheticRowFamFinal0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckRowFamFinal0');
  assert.equal(out.NF.kind, 'RowFamFinal0NF');
  assert.equal(out.NF.rowCount, ROWFAMFINAL_REQUIRED_ROWS0.length);
});

test('CheckFinal0 wraps final integration rejection', async () => {
  const finalTheorem = makeSyntheticFinalTheorem0();

  finalTheorem.FinalIntegration = {
    ...finalTheorem.FinalIntegration,
    GPack: {
      ...finalTheorem.FinalIntegration.GPack,
      ThresholdCert: {
        ...finalTheorem.FinalIntegration.GPack.ThresholdCert,
        residualSlackMax: 5,
      },
    },
  };

  const out = await CheckFinal0(finalTheorem);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinal0');
  assert.equal(out.Coord, 'CheckFinal0.FinalIntegration');
  assert.deepEqual(out.Path, ['FinalIntegration']);
  assert.equal(out.Witness.reason, 'CheckFinalIntegration0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckFinalIntegration0.GPack');
});

test('CheckFinal0 rejects residual band bounds above four', async () => {
  const finalTheorem = makeSyntheticFinalTheorem0();

  finalTheorem.PCCMinBridge = {
    ...finalTheorem.PCCMinBridge,
    residualBandBound: 5,
  };

  const out = await CheckFinal0(finalTheorem);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinal0');
  assert.equal(out.Coord, 'CheckFinal0.PCCMinBridge');
  assert.deepEqual(out.Path, ['PCCMinBridge', 'residualBandBound']);
  assert.equal(out.Witness.reason, 'PCCMinBridge residualBandBound must be an integer at most four');
});

test('CheckFinal0 rejects SAT in P theorem without package acceptance assumption', async () => {
  const finalTheorem = makeSyntheticFinalTheorem0();

  finalTheorem.AcceptedPackageImpliesSATinP = {
    ...finalTheorem.AcceptedPackageImpliesSATinP,
    assumptions: [
      'some-other-assumption',
    ],
  };

  const out = await CheckFinal0(finalTheorem);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinal0');
  assert.equal(out.Coord, 'CheckFinal0.SATinP');
  assert.deepEqual(out.Path, ['AcceptedPackageImpliesSATinP', 'assumptions']);
  assert.equal(out.Witness.reason, 'SAT in P implication must be conditional on package acceptance');
});

test('CheckFinal0 rejects generated sufficiency without canonical byte equality', async () => {
  const finalTheorem = makeSyntheticFinalTheorem0();

  finalTheorem.GeneratedPackageSufficiency = {
    ...finalTheorem.GeneratedPackageSufficiency,
    canonicalByteEquality: false,
  };

  const out = await CheckFinal0(finalTheorem);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinal0');
  assert.equal(out.Coord, 'CheckFinal0.GeneratedPackageSufficiency');
  assert.deepEqual(out.Path, ['GeneratedPackageSufficiency', 'canonicalByteEquality']);
  assert.equal(out.Witness.reason, 'GeneratedPackageSufficiency must certify canonicalByteEquality');
});

test('CheckFinal0 rejects public theorem that claims P equals NP before acceptance', async () => {
  const finalTheorem = makeSyntheticFinalTheorem0();

  finalTheorem.FinalPublicTheorem = {
    ...finalTheorem.FinalPublicTheorem,
    noClaimBeforeAccept: false,
  };

  const out = await CheckFinal0(finalTheorem);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinal0');
  assert.equal(out.Coord, 'CheckFinal0.FinalPublicTheorem');
  assert.deepEqual(out.Path, ['FinalPublicTheorem', 'noClaimBeforeAccept']);
  assert.equal(out.Witness.reason, 'FinalPublicTheorem must not claim P = NP before acceptance');
});

test('CheckFinal0 rejects non-polynomial final bound', async () => {
  const finalTheorem = makeSyntheticFinalTheorem0();

  finalTheorem.PolynomialBound = {
    ...finalTheorem.PolynomialBound,
    residualBandPolynomial: false,
  };

  const out = await CheckFinal0(finalTheorem);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinal0');
  assert.equal(out.Coord, 'CheckFinal0.PolynomialBound');
  assert.deepEqual(out.Path, ['PolynomialBound', 'residualBandPolynomial']);
  assert.equal(out.Witness.reason, 'PolynomialBound must certify residualBandPolynomial');
});

test('CheckFinal0 rejects final reflection cert missing a theorem', async () => {
  const finalTheorem = makeSyntheticFinalTheorem0();

  finalTheorem.ReflectionCert = {
    ...finalTheorem.ReflectionCert,
    reflectedTheorems: finalTheorem.ReflectionCert.reflectedTheorems.filter((entry) => entry !== 'GeneratedPackageSufficiency'),
  };

  const out = await CheckFinal0(finalTheorem);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinal0');
  assert.equal(out.Coord, 'CheckFinal0.ReflectionCert');
  assert.deepEqual(out.Path, ['ReflectionCert', 'reflectedTheorems']);
  assert.equal(out.Witness.reason, 'ReflectionCert is missing required final theorem reflections');
});

test('CheckFinal0 rejects executable hidden minimization in final theorem body', async () => {
  const finalTheorem = makeSyntheticFinalTheorem0();

  finalTheorem.FinalPublicTheorem = {
    ...finalTheorem.FinalPublicTheorem,
    body: [
      'minimumEquivalent',
    ],
  };

  const out = await CheckFinal0(finalTheorem);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinal0');
  assert.equal(out.Coord, 'CheckFinal0.noHiddenMin');
  assert.deepEqual(out.Path, ['FinalTheorem0', 'FinalPublicTheorem', 'body', 0]);
  assert.equal(out.Witness.reason, 'forbidden minimization symbol appears in executable position');
});

test('CheckFinal0 rejects opaque proof blobs', async () => {
  const finalTheorem = makeSyntheticFinalTheorem0();

  finalTheorem.PiFinal = {
    ...finalTheorem.PiFinal,
    proofBlob: {
      bytes: 'not allowed',
    },
  };

  const out = await CheckFinal0(finalTheorem);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinal0');
  assert.equal(out.Coord, 'CheckFinal0.opaqueProof');
  assert.deepEqual(out.Path, ['FinalTheorem0', 'PiFinal', 'proofBlob']);
  assert.equal(out.Witness.reason, 'opaque proof material is not allowed in Final0');
});

test('CheckRowFamFinal0 rejects missing final row coverage', async () => {
  const rowFam = makeSyntheticRowFamFinal0();

  rowFam.rows = rowFam.rows.filter((row) => row.rowKind !== 'GeneratedPackageSufficiency');

  const out = await CheckRowFamFinal0(rowFam);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckRowFamFinal0');
  assert.equal(out.Coord, 'CheckRowFamFinal0.coverage');
  assert.deepEqual(out.Path, ['rows', 'coverage', 'GeneratedPackageSufficiency']);
  assert.equal(out.Witness.reason, 'RowFamFinal0 is missing a required final row');
});

test('CheckRowFamFinal0 wraps final theorem rejection', async () => {
  const rowFam = makeSyntheticRowFamFinal0();

  rowFam.FinalTheorem.PCCMinBridge = {
    ...rowFam.FinalTheorem.PCCMinBridge,
    decisionComparator: 'bad-comparator',
  };

  const out = await CheckRowFamFinal0(rowFam);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckRowFamFinal0');
  assert.equal(out.Coord, 'CheckRowFamFinal0.FinalTheorem');
  assert.deepEqual(out.Path, ['FinalTheorem']);
  assert.equal(out.Witness.reason, 'CheckFinal0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckFinal0.PCCMinBridge');
});

test('CheckRowFamFinal0 rejects non-accept selected route', async () => {
  const rowFam = makeSyntheticRowFamFinal0();
  const index = rowFam.rows.findIndex((row) => row.rowKind === 'FinalPublicTheorem');

  rowFam.rows[index] = {
    ...rowFam.rows[index],
    selectedRoute: 'Reject',
    activeRouteSet: [
      'Reject',
    ],
  };

  const out = await CheckRowFamFinal0(rowFam);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckRowFamFinal0');
  assert.equal(out.Coord, 'CheckRowFamFinal0.rows');
  assert.deepEqual(out.Path, ['rows', index, 'selectedRoute']);
  assert.equal(out.Witness.reason, 'RowFamFinal0 rows must select Accept');
});

test('CheckFinal0 binds final theorem claims to final integration G proof chain', async (t) => {
  await t.test('rejects PCCMinBridge without G threshold proof source', async () => {
    const finalTheorem = makeSyntheticFinalTheorem0();

    finalTheorem.PCCMinBridge = {
      ...finalTheorem.PCCMinBridge,
      sourceTheorems: finalTheorem.PCCMinBridge.sourceTheorems.filter((entry) => entry !== 'G.ThresholdCert.proof'),
    };

    const out = await CheckFinal0(finalTheorem);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckFinal0');
    assert.equal(out.Coord, 'CheckFinal0.PCCMinBridge');
    assert.deepEqual(out.Path, ['PCCMinBridge', 'sourceTheorems']);
    assert.equal(out.Witness.reason, 'PCCMinBridge must cite required final source theorem');
  });

  await t.test('rejects SAT-in-P implication without global G proof assumption', async () => {
    const finalTheorem = makeSyntheticFinalTheorem0();

    finalTheorem.AcceptedPackageImpliesSATinP = {
      ...finalTheorem.AcceptedPackageImpliesSATinP,
      assumptions: finalTheorem.AcceptedPackageImpliesSATinP.assumptions.filter((entry) => entry !== 'G.ThresholdCert.proof'),
    };

    const out = await CheckFinal0(finalTheorem);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckFinal0');
    assert.equal(out.Coord, 'CheckFinal0.SATinP');
    assert.deepEqual(out.Path, ['AcceptedPackageImpliesSATinP', 'assumptions']);
    assert.equal(out.Witness.reason, 'SAT in P implication must cite accepted final integration and global G locked NAND proof chain');
  });

  await t.test('rejects SAT-in-P implication without usesGlobalGThreshold flag', async () => {
    const finalTheorem = makeSyntheticFinalTheorem0();

    finalTheorem.AcceptedPackageImpliesSATinP = {
      ...finalTheorem.AcceptedPackageImpliesSATinP,
      usesGlobalGThreshold: false,
    };

    const out = await CheckFinal0(finalTheorem);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckFinal0');
    assert.equal(out.Coord, 'CheckFinal0.SATinP');
    assert.deepEqual(out.Path, ['AcceptedPackageImpliesSATinP', 'usesGlobalGThreshold']);
    assert.equal(out.Witness.reason, 'SAT in P implication must certify usesGlobalGThreshold');
  });
});
