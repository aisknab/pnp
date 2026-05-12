import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckPackSufficiency0,
  PACK_SUFFICIENCY_PHASES0,
  PACK_SUFFICIENCY_THEOREM_IDS0,
  makeSyntheticPCCPack0,
} from '../pcc-pack-sufficiency0.mjs';

import {
  makeSyntheticGPack0,
} from '../pcc-gpack0.mjs';

import {
  makeSyntheticFinalIntegration0,
} from '../pcc-final-framework0.mjs';

import {
  makeSyntheticFinalTheorem0,
  makeSyntheticRowFamFinal0,
} from '../pcc-final0.mjs';

test('CheckPackSufficiency0 accepts the synthetic top-level package', async () => {
  const out = await CheckPackSufficiency0(makeSyntheticPCCPack0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckPackSufficiency0');
  assert.equal(out.NF.kind, 'PackSufficiency0NF');
  assert.deepEqual(out.NF.phaseOrder, PACK_SUFFICIENCY_PHASES0);
  assert.deepEqual(out.NF.theoremIds, PACK_SUFFICIENCY_THEOREM_IDS0);
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
  assert.equal(out.NF.residualBandExactMinimization, true);
  assert.equal(out.NF.zeroSlackSound, true);
  assert.equal(out.NF.zeroSlackContradictionFromPositiveSlack, true);
  assert.equal(out.NF.terminalMuBridgeComplete, true);
  assert.equal(out.NF.saturatePositiveComplete, true);
  assert.equal(out.NF.bcelReadyPositiveNucleusComplete, true);
  assert.equal(out.Digest.alg, 'SHA256');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckPackSufficiency0 rejects a package that embeds AcceptRun', async () => {
  const pack = makeSyntheticPCCPack0();

  pack.AcceptRun = {
    kind: 'AcceptRun0',
    Verdict: 'accept',
  };

  const out = await CheckPackSufficiency0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPackSufficiency0');
  assert.equal(out.Coord, 'CheckPackSufficiency0.core');
  assert.deepEqual(out.Path, ['AcceptRun']);
  assert.equal(out.Witness.reason, 'PCCPack0 core package must not contain AcceptRun');
});

test('CheckPackSufficiency0 rejects bad manifest phase order', async () => {
  const pack = makeSyntheticPCCPack0();

  pack.Manifest = {
    ...pack.Manifest,
    phaseOrder: [
      ...pack.Manifest.phaseOrder,
    ],
  };

  pack.Manifest.phaseOrder[0] = 'Φ99.BadPhase';

  const out = await CheckPackSufficiency0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPackSufficiency0');
  assert.equal(out.Coord, 'CheckPackSufficiency0.manifest');
  assert.deepEqual(out.Path, ['Manifest', 'phaseOrder', 0]);
  assert.equal(out.Witness.reason, 'PCCPack manifest phase order mismatch');
});

test('CheckPackSufficiency0 wraps a GPack rejection', async () => {
  const pack = makeSyntheticPCCPack0();

  pack.GPack = {
    ...pack.GPack,
    ThresholdCert: {
      ...pack.GPack.ThresholdCert,
      residualSlackMax: 5,
    },
  };

  const out = await CheckPackSufficiency0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPackSufficiency0');
  assert.equal(out.Coord, 'CheckPackSufficiency0.GPack');
  assert.deepEqual(out.Path, ['GPack']);
  assert.equal(out.Witness.reason, 'CheckGPack0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckGPack0.threshold');
});

test('CheckPackSufficiency0 rejects cross artefact GPack mismatch', async () => {
  const pack = makeSyntheticPCCPack0();

  const alternateGPack = {
    ...makeSyntheticGPack0(),
    acceptedAlternateGPackNonce: 1,
  };

  const alternateFinalIntegration = makeSyntheticFinalIntegration0({
    gpack: alternateGPack,
  });

  const alternateFinalTheorem = makeSyntheticFinalTheorem0({
    finalIntegration: alternateFinalIntegration,
  });

  const alternateRowFamFinal = makeSyntheticRowFamFinal0(alternateFinalTheorem);

  pack.FinalIntegration = alternateFinalIntegration;
  pack.FinalTheorem = alternateFinalTheorem;
  pack.RowFamFinal = alternateRowFamFinal;

  const out = await CheckPackSufficiency0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPackSufficiency0');
  assert.equal(out.Coord, 'CheckPackSufficiency0.cross');
  assert.deepEqual(out.Path, ['FinalIntegration', 'GPack']);
  assert.equal(out.Witness.reason, 'FinalIntegration GPack must match top-level GPack');
});

test('CheckPackSufficiency0 rejects generated-package sufficiency without canonical byte equality', async () => {
  const pack = makeSyntheticPCCPack0();

  pack.PackSufficiencyTheorem = {
    ...pack.PackSufficiencyTheorem,
    generatedPackageSufficiency: {
      ...pack.PackSufficiencyTheorem.generatedPackageSufficiency,
      canonicalByteEquality: false,
    },
  };

  const out = await CheckPackSufficiency0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPackSufficiency0');
  assert.equal(out.Coord, 'CheckPackSufficiency0.PackSufficiencyTheorem');
  assert.deepEqual(out.Path, ['PackSufficiencyTheorem', 'generatedPackageSufficiency', 'canonicalByteEquality']);
  assert.equal(out.Witness.reason, 'generatedPackageSufficiency must certify canonicalByteEquality');
});

test('CheckPackSufficiency0 rejects public theorem that claims P equals NP before acceptance', async () => {
  const pack = makeSyntheticPCCPack0();

  pack.PackSufficiencyTheorem = {
    ...pack.PackSufficiencyTheorem,
    publicConclusion: {
      ...pack.PackSufficiencyTheorem.publicConclusion,
      noClaimBeforeAccept: false,
    },
  };

  const out = await CheckPackSufficiency0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPackSufficiency0');
  assert.equal(out.Coord, 'CheckPackSufficiency0.PackSufficiencyTheorem');
  assert.deepEqual(out.Path, ['PackSufficiencyTheorem', 'publicConclusion', 'noClaimBeforeAccept']);
  assert.equal(out.Witness.reason, 'publicConclusion must certify noClaimBeforeAccept');
});

test('CheckPackSufficiency0 wraps a final theorem rejection', async () => {
  const pack = makeSyntheticPCCPack0();

  pack.FinalTheorem = {
    ...pack.FinalTheorem,
    FinalPublicTheorem: {
      ...pack.FinalTheorem.FinalPublicTheorem,
      exportedStatement: {
        ...pack.FinalTheorem.FinalPublicTheorem.exportedStatement,
        consequent: 'not P = NP',
      },
    },
  };

  const out = await CheckPackSufficiency0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPackSufficiency0');
  assert.equal(out.Coord, 'CheckPackSufficiency0.FinalTheorem');
  assert.deepEqual(out.Path, ['FinalTheorem']);
  assert.equal(out.Witness.reason, 'CheckFinal0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckFinal0.FinalPublicTheorem');
});

test('CheckPackSufficiency0 rejects executable hidden minimization in the pack theorem', async () => {
  const pack = makeSyntheticPCCPack0();

  pack.PackSufficiencyTheorem = {
    ...pack.PackSufficiencyTheorem,
    body: [
      'minimumEquivalent',
    ],
  };

  const out = await CheckPackSufficiency0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPackSufficiency0');
  assert.equal(out.Coord, 'CheckPackSufficiency0.noHiddenMin');
  assert.deepEqual(out.Path, ['PCCPack0', 'PackSufficiencyTheorem', 'body', 0]);
  assert.equal(out.Witness.reason, 'forbidden minimization symbol appears in executable position');
});

test('CheckPackSufficiency0 rejects opaque proof blobs', async () => {
  const pack = makeSyntheticPCCPack0();

  pack.PiPackSufficiency = {
    ...pack.PiPackSufficiency,
    proofBlob: {
      bytes: 'not allowed',
    },
  };

  const out = await CheckPackSufficiency0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPackSufficiency0');
  assert.equal(out.Coord, 'CheckPackSufficiency0.opaqueProof');
  assert.deepEqual(out.Path, ['PCCPack0', 'PiPackSufficiency', 'proofBlob']);
  assert.equal(out.Witness.reason, 'opaque proof material is not allowed in PCCPack0');
});

test('CheckPackSufficiency0 rejects missing ZeroSlack residual-band obligations', async (t) => {
  const cases = [
    'pccMinReturnsExactMinimum',
    'residualSlackBounded',
    'zeroSlackSound',
    'zeroSlackEarlierRoutesExcluded',
    'positiveResidualWitnessYieldsBCELReady',
    'bcelAnchorAlgebraBooleanOrRoutes',
    'selectorUniverseCompleteForPackets',
    'realizerBotOnlyHNBUDBlockedOrLowerRank',
    'hbBlockerGraphAcyclic',
    'zeroSlackContradictionFromPositiveSlack',
    'zeroSlackCertificatePolynomialSize',
  ];

  for (const field of cases) {
    await t.test(`${field}=false`, async () => {
      const pack = makeSyntheticPCCPack0();

      pack.PackSufficiencyTheorem = {
        ...pack.PackSufficiencyTheorem,
        residualBandMinimization: {
          ...pack.PackSufficiencyTheorem.residualBandMinimization,
          [field]: false,
        },
      };

      const out = await CheckPackSufficiency0(pack);

      assert.equal(out.tag, 'reject');
      assert.equal(out.checker, 'CheckPackSufficiency0');
      assert.equal(out.Coord, 'CheckPackSufficiency0.PackSufficiencyTheorem');
      assert.deepEqual(out.Path, ['PackSufficiencyTheorem', 'residualBandMinimization', field]);
      assert.equal(out.Witness.reason, `residualBandMinimization must certify ${field}`);
    });
  }
});

test('CheckPackSufficiency0 rejects malformed residual-band theorem boundary', async (t) => {
  await t.test('bad assumption', async () => {
    const pack = makeSyntheticPCCPack0();

    pack.PackSufficiencyTheorem = {
      ...pack.PackSufficiencyTheorem,
      residualBandMinimization: {
        ...pack.PackSufficiencyTheorem.residualBandMinimization,
        assumption: 'Lambda(C0)<=unbounded',
      },
    };

    const out = await CheckPackSufficiency0(pack);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckPackSufficiency0');
    assert.equal(out.Coord, 'CheckPackSufficiency0.PackSufficiencyTheorem');
    assert.deepEqual(out.Path, ['PackSufficiencyTheorem', 'residualBandMinimization', 'assumption']);
    assert.equal(out.Witness.reason, 'residualBandMinimization assumption mismatch');
  });

  await t.test('bad conclusion', async () => {
    const pack = makeSyntheticPCCPack0();

    pack.PackSufficiencyTheorem = {
      ...pack.PackSufficiencyTheorem,
      residualBandMinimization: {
        ...pack.PackSufficiencyTheorem.residualBandMinimization,
        conclusion: 'ZeroSlack may be approximate',
      },
    };

    const out = await CheckPackSufficiency0(pack);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckPackSufficiency0');
    assert.equal(out.Coord, 'CheckPackSufficiency0.PackSufficiencyTheorem');
    assert.deepEqual(out.Path, ['PackSufficiencyTheorem', 'residualBandMinimization', 'conclusion']);
    assert.equal(out.Witness.reason, 'residualBandMinimization conclusion mismatch');
  });
});


test('CheckPackSufficiency0 rejects missing Terminal MuBridge obligations', async (t) => {
  const cases = [
    'terminalCarrierPreservesSemantics',
    'terminalizationSizePreserving',
    'closedFullWordRealizesCircuit',
    'quotientEqualityNotConstructive',
    'wholeSpanCheaperImpliesStrictDescent',
  ];

  for (const field of cases) {
    await t.test(`${field}=false`, async () => {
      const pack = makeSyntheticPCCPack0();

      pack.PackSufficiencyTheorem = {
        ...pack.PackSufficiencyTheorem,
        residualBandMinimization: {
          ...pack.PackSufficiencyTheorem.residualBandMinimization,
          [field]: false,
        },
      };

      const out = await CheckPackSufficiency0(pack);

      assert.equal(out.tag, 'reject');
      assert.equal(out.checker, 'CheckPackSufficiency0');
      assert.equal(out.Coord, 'CheckPackSufficiency0.PackSufficiencyTheorem');
      assert.deepEqual(out.Path, ['PackSufficiencyTheorem', 'residualBandMinimization', field]);
      assert.equal(out.Witness.reason, `residualBandMinimization must certify ${field}`);
    });
  }
});

test('CheckPackSufficiency0 rejects missing SaturatePositive obligations', async (t) => {
  const cases = [
    'transparentSaturationCostBalanced',
    'interfaceExposureRoutesToE',
    'originKernelObligationClosureRouted',
    'projectionPositivityNotLostSilently',
    'firstNontransparentStepRecorded',
  ];

  for (const field of cases) {
    await t.test(`${field}=false`, async () => {
      const pack = makeSyntheticPCCPack0();

      pack.PackSufficiencyTheorem = {
        ...pack.PackSufficiencyTheorem,
        residualBandMinimization: {
          ...pack.PackSufficiencyTheorem.residualBandMinimization,
          [field]: false,
        },
      };

      const out = await CheckPackSufficiency0(pack);

      assert.equal(out.tag, 'reject');
      assert.equal(out.checker, 'CheckPackSufficiency0');
      assert.equal(out.Coord, 'CheckPackSufficiency0.PackSufficiencyTheorem');
      assert.deepEqual(out.Path, ['PackSufficiencyTheorem', 'residualBandMinimization', field]);
      assert.equal(out.Witness.reason, `residualBandMinimization must certify ${field}`);
    });
  }
});


test('CheckPackSufficiency0 rejects missing BCEL-ready positive nucleus obligations', async (t) => {
  const cases = [
    'positiveResidualWitnessExists',
    'finiteAnchorSetExtracted',
    'booleanAnchorAlgebraOrRoute',
    'minimalPositiveNucleus',
    'properCutConstantEquation',
    'anchorSizeAtLeastTwo',
  ];

  for (const field of cases) {
    await t.test(`${field}=false`, async () => {
      const pack = makeSyntheticPCCPack0();

      pack.PackSufficiencyTheorem = {
        ...pack.PackSufficiencyTheorem,
        residualBandMinimization: {
          ...pack.PackSufficiencyTheorem.residualBandMinimization,
          [field]: false,
        },
      };

      const out = await CheckPackSufficiency0(pack);

      assert.equal(out.tag, 'reject');
      assert.equal(out.checker, 'CheckPackSufficiency0');
      assert.equal(out.Coord, 'CheckPackSufficiency0.PackSufficiencyTheorem');
      assert.deepEqual(out.Path, ['PackSufficiencyTheorem', 'residualBandMinimization', field]);
      assert.equal(out.Witness.reason, `residualBandMinimization must certify ${field}`);
    });
  }
});
