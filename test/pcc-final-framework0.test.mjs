import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckFinalFrameworkMatch0,
  CheckFinalIntegration0,
  CheckSATBounds0,
  CheckSATDecision0,
  FINAL_INTEGRATION_PHASES0,
  makeSyntheticFinalFrameworkMatch0,
  makeSyntheticFinalIntegration0,
  makeSyntheticSATBounds0,
  makeSyntheticSATDecision0,
} from '../pcc-final-framework0.mjs';

test('CheckFinalFrameworkMatch0 accepts the synthetic O/G framework match', async () => {
  const out = await CheckFinalFrameworkMatch0(makeSyntheticFinalFrameworkMatch0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckFinalFrameworkMatch0');
  assert.equal(out.NF.kind, 'FinalFrameworkMatch0NF');
  assert.equal(out.NF.fullWordSize, out.NF.baseline + 4);
  assert.equal(out.Digest.alg, 'SHA256');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckSATDecision0 accepts the synthetic SAT decision artefact', async () => {
  const out = await CheckSATDecision0(makeSyntheticSATDecision0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckSATDecision0');
  assert.equal(out.NF.kind, 'SATDecision0NF');
  assert.equal(out.NF.fullWordSize, out.NF.baseline + 4);
});

test('CheckSATBounds0 accepts the synthetic SAT polynomial bounds artefact', async () => {
  const out = await CheckSATBounds0(makeSyntheticSATBounds0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckSATBounds0');
  assert.equal(out.NF.kind, 'SATBounds0NF');
  assert.equal(out.NF.residualSlackBound, 4);
});

test('CheckFinalIntegration0 accepts GPack, FinalMatch, SATDecision, and SATBounds together', async () => {
  const out = await CheckFinalIntegration0(makeSyntheticFinalIntegration0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckFinalIntegration0');
  assert.equal(out.NF.kind, 'FinalIntegration0NF');
  assert.deepEqual(out.NF.phases, FINAL_INTEGRATION_PHASES0);
});

test('CheckFinalFrameworkMatch0 rejects syntax mismatch between O and G', async () => {
  const match = makeSyntheticFinalFrameworkMatch0();

  match.SyntaxMap = {
    ...match.SyntaxMap,
    sameNANDSyntax: false,
  };

  const out = await CheckFinalFrameworkMatch0(match);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalFrameworkMatch0');
  assert.equal(out.Coord, 'CheckFinalFrameworkMatch0.syntax');
  assert.deepEqual(out.Path, ['SyntaxMap', 'sameNANDSyntax']);
  assert.equal(out.Witness.reason, 'SyntaxMap must certify identical NAND syntax');
});

test('CheckFinalFrameworkMatch0 rejects Package O importing Package G', async () => {
  const match = makeSyntheticFinalFrameworkMatch0();

  match.PO = {
    ...match.PO,
    imports: [
      ...match.PO.imports,
      'G',
    ],
  };

  const out = await CheckFinalFrameworkMatch0(match);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalFrameworkMatch0');
  assert.equal(out.Coord, 'CheckFinalFrameworkMatch0.imports');
  assert.deepEqual(out.Path, ['PO', 'imports', match.PO.imports.length - 1]);
  assert.equal(out.Witness.reason, 'Package O must not import Package G');
});

test('CheckFinalFrameworkMatch0 rejects Package G importing Package O through ImportMap', async () => {
  const match = makeSyntheticFinalFrameworkMatch0();

  match.ImportMap = {
    ...match.ImportMap,
    edges: [
      ...match.ImportMap.edges,
      {
        from: 'G',
        to: 'O',
      },
    ],
  };

  const out = await CheckFinalFrameworkMatch0(match);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalFrameworkMatch0');
  assert.equal(out.Coord, 'CheckFinalFrameworkMatch0.imports');
  assert.deepEqual(out.Path, ['ImportMap', 'edges', match.ImportMap.edges.length - 1]);
  assert.equal(out.Witness.reason, 'Final framework contains a forbidden O/G import edge');
});

test('CheckFinalFrameworkMatch0 rejects residual slack above four', async () => {
  const match = makeSyntheticFinalFrameworkMatch0();

  match.SlackMap = {
    ...match.SlackMap,
    lockedResidualSlackMax: 5,
  };

  const out = await CheckFinalFrameworkMatch0(match);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalFrameworkMatch0');
  assert.equal(out.Coord, 'CheckFinalFrameworkMatch0.slack');
  assert.deepEqual(out.Path, ['SlackMap', 'lockedResidualSlackMax']);
  assert.equal(out.Witness.reason, 'locked residual slack must be an integer at most four');
});

test('CheckFinalFrameworkMatch0 rejects executable hidden minimization', async () => {
  const match = makeSyntheticFinalFrameworkMatch0();

  match.NormBridge = {
    ...match.NormBridge,
    body: [
      'minimumEquivalent',
    ],
  };

  const out = await CheckFinalFrameworkMatch0(match);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalFrameworkMatch0');
  assert.equal(out.Coord, 'CheckFinalFrameworkMatch0.noHiddenMin');
  assert.deepEqual(out.Path, ['FinalFrameworkMatch0', 'NormBridge', 'body', 0]);
  assert.equal(out.Witness.reason, 'forbidden minimization symbol appears in executable position');
});

test('CheckSATDecision0 rejects bad baseline formula', async () => {
  const decision = makeSyntheticSATDecision0();

  decision.Baseline = {
    ...decision.Baseline,
    value: decision.Baseline.value + 1,
  };

  const out = await CheckSATDecision0(decision);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckSATDecision0');
  assert.equal(out.Coord, 'CheckSATDecision0.baseline');
  assert.deepEqual(out.Path, ['Baseline', 'value']);
  assert.equal(out.Witness.reason, 'SATDecision baseline formula mismatch');
});

test('CheckSATDecision0 rejects a case that violates minSize greater than baseline rule', async () => {
  const decision = makeSyntheticSATDecision0();

  decision.Cases[0] = {
    ...decision.Cases[0],
    minSize: decision.Cases[0].baseline,
    decision: 'SAT',
  };

  const out = await CheckSATDecision0(decision);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckSATDecision0');
  assert.equal(out.Coord, 'CheckSATDecision0.cases');
  assert.deepEqual(out.Path, ['Cases', 0, 'decision']);
  assert.equal(out.Witness.reason, 'SAT decision case does not match minSize>baseline rule');
});

test('CheckSATDecision0 rejects satisfiable case above residual slack four', async () => {
  const decision = makeSyntheticSATDecision0();

  decision.Cases[0] = {
    ...decision.Cases[0],
    minSize: decision.Cases[0].baseline + 5,
    decision: 'SAT',
  };

  const out = await CheckSATDecision0(decision);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckSATDecision0');
  assert.equal(out.Coord, 'CheckSATDecision0.cases');
  assert.deepEqual(out.Path, ['Cases', 0, 'minSize']);
  assert.equal(out.Witness.reason, 'satisfiable locked NAND case must have minimum between baseline plus one and baseline plus four');
});

test('CheckSATBounds0 rejects non-polynomial converter bounds', async () => {
  const bounds = makeSyntheticSATBounds0();

  bounds.Converter = {
    ...bounds.Converter,
    polynomial: false,
  };

  const out = await CheckSATBounds0(bounds);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckSATBounds0');
  assert.equal(out.Coord, 'CheckSATBounds0.converter');
  assert.deepEqual(out.Path, ['Converter', 'polynomial']);
  assert.equal(out.Witness.reason, 'Converter must certify polynomial');
});

test('CheckSATBounds0 rejects residual slack bound above four', async () => {
  const bounds = makeSyntheticSATBounds0();

  bounds.Minimizer = {
    ...bounds.Minimizer,
    residualSlackBound: 5,
  };

  const out = await CheckSATBounds0(bounds);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckSATBounds0');
  assert.equal(out.Coord, 'CheckSATBounds0.minimizer');
  assert.deepEqual(out.Path, ['Minimizer', 'residualSlackBound']);
  assert.equal(out.Witness.reason, 'Minimizer residualSlackBound must be an integer at most four');
});

test('CheckFinalIntegration0 wraps GPack rejection', async () => {
  const integration = makeSyntheticFinalIntegration0();

  integration.GPack = {
    ...integration.GPack,
    ThresholdCert: {
      ...integration.GPack.ThresholdCert,
      residualSlackMax: 5,
    },
  };

  const out = await CheckFinalIntegration0(integration);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalIntegration0');
  assert.equal(out.Coord, 'CheckFinalIntegration0.GPack');
  assert.deepEqual(out.Path, ['GPack']);
  assert.equal(out.Witness.reason, 'CheckGPack0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckGPack0.threshold');
});

test('CheckFinalIntegration0 rejects opaque proof material', async () => {
  const integration = makeSyntheticFinalIntegration0();

  integration.PiFinalIntegration = {
    ...integration.PiFinalIntegration,
    proofBlob: {
      bytes: 'not allowed',
    },
  };

  const out = await CheckFinalIntegration0(integration);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalIntegration0');
  assert.equal(out.Coord, 'CheckFinalIntegration0.opaqueProof');
  assert.deepEqual(out.Path, ['FinalIntegration0', 'PiFinalIntegration', 'proofBlob']);
  assert.equal(out.Witness.reason, 'opaque proof material is not allowed in final integration');
});

test('CheckFinalIntegration0 binds GPack to GlobalProofDAG locked NAND theorem', async (t) => {
  await t.test('rejects SATDecision drift from accepted GPack digest', async () => {
    const integration = makeSyntheticFinalIntegration0();

    integration.SATDecision.LockedWord.gpackDigest = {
      ...integration.SATDecision.LockedWord.gpackDigest,
      hex: '0'.repeat(64),
    };

    const out = await CheckFinalIntegration0(integration);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckFinalIntegration0');
    assert.equal(out.Coord, 'CheckFinalIntegration0.globalGLinkage');
    assert.deepEqual(out.Path, ['SATDecision', 'LockedWord', 'gpackDigest']);
    assert.equal(out.Witness.reason, 'FinalIntegration0 must bind SATDecision and FinalMatch to the accepted GPack digest');
  });

  await t.test('rejects GlobalProofDAG G threshold payload drift', async () => {
    const integration = makeSyntheticFinalIntegration0();
    const node = integration.GlobalProofDAG.Nodes.find((entry) => entry.id === 'G.ThresholdCert.proof');

    node.payload = {
      ...node.payload,
      residualSlackMax: 5,
    };

    const out = await CheckFinalIntegration0(integration);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckFinalIntegration0');
    assert.equal(out.Coord, 'CheckFinalIntegration0.GlobalProofDAG');
    assert.deepEqual(out.Path, ['GlobalProofDAG']);
    assert.equal(out.Witness.detail.inner.coord, 'CheckGlobalProofDAG0.gLockedNANDProofs');
  });

  await t.test('rejects missing final SAT-in-P dependency on Package.G.LockedNANDThreshold', async () => {
    const integration = makeSyntheticFinalIntegration0();
    const node = integration.GlobalProofDAG.Nodes.find((entry) => entry.id === 'Final.AcceptedPackageImpliesSATinP');

    node.premises = node.premises.filter((premise) => premise !== 'Package.G.LockedNANDThreshold');

    const out = await CheckFinalIntegration0(integration);

    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'CheckFinalIntegration0');
    assert.equal(out.Coord, 'CheckFinalIntegration0.GlobalProofDAG');
    assert.deepEqual(out.Path, ['GlobalProofDAG']);
    assert.equal(out.Witness.reason, 'CheckGlobalProofDAG0 rejected');
    assert.equal(out.Witness.detail.inner.coord, 'CheckGlobalProofDAG0.gLockedNANDProofs');
  });
});
