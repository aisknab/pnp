import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckComplexityBridge0,
  makeComplexityBridgeInput0,
} from '../pcc-complexity-bridge0.mjs';

test('complexity bridge derives only the guarded class equality', async () => {
  const out = await CheckComplexityBridge0(makeComplexityBridgeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckComplexityBridge0');
  assert.equal(out.NF.satInPAssumptionChecked, true);
  assert.equal(out.NF.satNPCompletenessDependencyChecked, true);
  assert.equal(out.NF.polynomialReductionClosureChecked, true);
  assert.equal(out.NF.pSubsetNPDependencyChecked, true);
  assert.equal(out.NF.npSubsetPDerived, true);
  assert.equal(out.NF.pSubsetNPDerived, true);
  assert.equal(out.NF.conditionalPEqualsNPDerived, true);
  assert.equal(out.NF.unconditionalPEqualsNPDerived, false);
  assert.equal(out.NF.noUnconditionalClaim, true);
  assert.equal(out.NF.publiclyActive, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.cookLevinFormalizationIncluded, false);
  assert.equal(out.NF.standardTheoremDependencyTrustRequired, true);
});

test('complexity bridge rejects removal of the SAT-in-P premise', async () => {
  const base = makeComplexityBridgeInput0();
  const out = await CheckComplexityBridge0({
    ...base,
    Claim: {
      ...base.Claim,
      assumptions: ['SAT is NP-complete'],
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckComplexityBridge0.Claim');
  assert.deepEqual(out.Path, ['Claim', 'assumptions']);
});

test('complexity bridge rejects an unconditional equality claim', async () => {
  const base = makeComplexityBridgeInput0();
  const out = await CheckComplexityBridge0({
    ...base,
    Claim: {
      ...base.Claim,
      noUnconditionalClaim: false,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckComplexityBridge0.Claim');
});

test('complexity bridge rejects drift in the standard reduction dependency', async () => {
  const base = makeComplexityBridgeInput0();
  const out = await CheckComplexityBridge0({
    ...base,
    Basis: {
      ...base.Basis,
      satNPCompleteness: {
        ...base.Basis.satNPCompleteness,
        reductionKind: 'oracle-reduction',
      },
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckComplexityBridge0.Basis');
  assert.deepEqual(out.Path, ['Basis']);
});

test('complexity bridge binds source, basis, claim, and derivation digests', async () => {
  const out = await CheckComplexityBridge0(makeComplexityBridgeInput0());

  assert.equal(out.tag, 'accept');
  for (const field of [
    'sourceDerivationDigest',
    'basisDigest',
    'claimDigest',
    'derivationDigest',
    'scopeDigest',
    'policyDigest',
  ]) {
    assert.equal(out.NF[field].alg, 'SHA256');
  }
});
