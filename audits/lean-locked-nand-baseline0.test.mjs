import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  computeLockedNANDBaseline0,
  makeSyntheticGPack0,
  makeSyntheticPreNAND0,
} from '../pcc-gpack0.mjs';
import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasPrivateLeanDeclaration0,
  hasUnauditedLeanDeclarationForm0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));

const LAYERS = Object.freeze([
  Object.freeze({
    source: 'lean/PNP/LockedNANDDirect.lean',
    audit: 'lean-audit/PNPLockedNANDDirectAxiomAudit.lean',
    imports: ['PNP.NANDEnumerator', 'PNP.LockedNANDPrefix'],
    required: [
      'def Program.hasNoConstant',
      'def exposeAllGates',
      'def equalityDirect : Candidate 3 10 10',
      'def constantOneDirect : Candidate 2 2 2',
      'def constantZeroDirect : Candidate 2 3 3',
      'def traceDirect : Candidate 4 18 18',
      'def prefixAndDirect : Candidate 2 2 2',
      'def finalConjunctionDirect : Candidate 3 4 1',
      'theorem finalConjunctionDirect_no_internal_constants',
    ],
  }),
  Object.freeze({
    source: 'lean/PNP/DirectWireBaseline.lean',
    audit: 'lean-audit/PNPDirectWireBaselineAxiomAudit.lean',
    imports: ['PNP.NANDMinimum'],
    required: [
      'def OutputNonconstant',
      'def OutputNotPositiveProjection',
      'def OutputPairwiseDistinct',
      'structure BaselineOutputConditions',
      'theorem outputGateIndex_injective',
      'theorem finCard_le_of_injective',
      'theorem outputCount_le_gateCount',
      'theorem BaselineOutputConditions.of_equivalent',
      'theorem referenceMinimum_eq_gateCount_of_squareBaseline',
    ],
  }),
  Object.freeze({
    source: 'lean/PNP/LockedNANDBaseline.lean',
    audit: 'lean-audit/PNPLockedNANDBaselineAxiomAudit.lean',
    imports: ['PNP.DirectWireBaseline'],
    required: [
      'structure SourceOccurrenceCounts',
      'def Source.occurrenceCounts',
      'def Gate.sourceCounts',
      'def Program.sourceCounts',
      'theorem Program.sourceCounts_total',
      'def distinguishedCheckCount',
      'theorem distinguishedCheckCount_eq_three_mul',
      'def prefixNodeCount',
      'def lockedBaselineCount',
      'theorem lockedBaselineCount_report_formula',
      'def lockedDisplayedGateCount',
      'theorem lockedBaseline_exact_of_constructed_distinct',
    ],
  }),
  Object.freeze({
    source: 'lean/PNP/LockedNANDLocalBaseline.lean',
    audit: 'lean-audit/PNPLockedNANDLocalBaselineAxiomAudit.lean',
    imports: ['PNP.DirectWireBaseline', 'PNP.LockedNANDDirect'],
    required: [
      'def FiniteBaselineSignatures',
      'def finiteBaselineSignatureCheck',
      'theorem finiteBaselineSignatureCheck_sound',
      'theorem baselineOutputConditions_of_finiteSignatures',
      'theorem equalityDirect_baselineOutputConditions',
      'theorem constantOneDirect_baselineOutputConditions',
      'theorem constantZeroDirect_baselineOutputConditions',
      'theorem traceDirect_baselineOutputConditions',
      'theorem prefixAndDirect_baselineOutputConditions',
      'theorem equalityDirect_referenceMinimum',
      'theorem constantOneDirect_referenceMinimum',
      'theorem constantZeroDirect_referenceMinimum',
      'theorem traceDirect_referenceMinimum',
      'theorem prefixAndDirect_referenceMinimum',
    ],
  }),
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map((head) => `PNP.DirectWire.${head.name}`);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

function validateLayer0(source, layer) {
  const failures = [];
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify(layer.imports)) failures.push('closed-import');
  if (!/namespace PNP\s+[\s\S]*namespace DirectWire/u.test(source)) failures.push('namespace');
  for (const required of layer.required) {
    if (!source.includes(required)) failures.push(`missing:${required}`);
  }
  if (/\b(?:Classical|funext|propext|native_decide|sorry|admit)\b/u.test(source)) failures.push('forbidden-shortcut');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasPrivateLeanDeclaration0(source)) failures.push('private-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('unaudited-declaration-form');
  return failures;
}

function baseline0({ gates, equality, zero, one, prefixChecks }) {
  return 18 * gates + 10 * equality + 3 * zero + 2 * one
    + 2 * (prefixChecks - 1);
}

test('typed macros, direct-wire lower bound, and source-derived accounting have closed constructive sources', async () => {
  for (const layer of LAYERS) {
    assert.deepEqual(validateLayer0(await text0(layer.source), layer), [], layer.source);
  }
});

test('each PR7 axiom transcript covers every explicit declaration exactly once', async () => {
  for (const layer of LAYERS) {
    const expected = declarations0(await text0(layer.source));
    const printed = printed0(await text0(layer.audit));
    assert.deepEqual(printed, expected, layer.audit);
    assert.equal(new Set(printed).size, printed.length, layer.audit);
  }
});

test('all six report-local gadgets are typed direct-wire candidates with honest output arities', async () => {
  const source = await text0('lean/PNP/LockedNANDDirect.lean');
  for (const declaration of [
    /def equalityDirect : Candidate 3 10 10/u,
    /def constantOneDirect : Candidate 2 2 2/u,
    /def constantZeroDirect : Candidate 2 3 3/u,
    /def traceDirect : Candidate 4 18 18/u,
    /def prefixAndDirect : Candidate 2 2 2/u,
    /def finalConjunctionDirect : Candidate 3 4 1/u,
  ]) assert.match(source, declaration);
  assert.match(source, /def exposeAllGates[\s\S]*Candidate inputs gates gates/u);
  assert.match(source, /theorem exposeAllGates_source/u);
  assert.equal((source.match(/theorem \w+Direct_no_internal_constants\b/gu) ?? []).length, 6);
  assert.doesNotMatch(source, /(?:def|theorem)\s+(?:lockedNANDBuilder|lockedNANDThreshold)/u);
});

test('the direct-wire lower bound is semantic and square exactness remains conditional', async () => {
  const source = await text0('lean/PNP/DirectWireBaseline.lean');
  assert.match(source, /structure BaselineOutputConditions[\s\S]*nonconstant[\s\S]*notPositiveProjection[\s\S]*pairwiseDistinct/u);
  assert.match(source, /theorem outputCount_le_gateCount[\s\S]*outputs ≤ gates/u);
  assert.match(source, /theorem referenceMinimum_eq_gateCount_of_squareBaseline[\s\S]*\(conditions : BaselineOutputConditions candidate\)/u);
  assert.doesNotMatch(source, /(?:axiom|constant|opaque)\s+(?:BaselineDistinct|MacroDistinct)/u);
  assert.doesNotMatch(source, /polynomial|LockedNANDThreshold|SAT/u);
});

test('finite signatures discharge the five square local macro baselines only', async () => {
  const source = await text0('lean/PNP/LockedNANDLocalBaseline.lean');
  for (const macro of [
    'equalityDirect',
    'constantOneDirect',
    'constantZeroDirect',
    'traceDirect',
    'prefixAndDirect',
  ]) {
    assert.match(source, new RegExp(`theorem ${macro}_finiteBaseline\\b`, 'u'));
    assert.match(source, new RegExp(`theorem ${macro}_baselineOutputConditions\\b`, 'u'));
    assert.match(source, new RegExp(`theorem ${macro}_referenceMinimum\\b`, 'u'));
  }
  assert.doesNotMatch(source, /theorem finalConjunctionDirect_referenceMinimum\b/u);
  assert.doesNotMatch(source, /(?:theorem|def)\s+(?:BaselineDistinct|lockedNANDBuilder|lockedNANDThreshold)\b/u);
});

test('locked baseline counts are derived from actual typed sources and preserve the multi-output convention', async () => {
  const source = await text0('lean/PNP/LockedNANDBaseline.lean');
  assert.match(source, /Program\.sourceCounts_total[\s\S]*= 2 \* gates/u);
  assert.match(source, /distinguishedCheckCount_eq_three_mul[\s\S]*= 3 \* gates/u);
  assert.match(source, /lockedBaselineCount_report_formula/u);
  assert.match(source, /18 \* gates[\s\S]*10 \* program\.sourceCounts\.equality[\s\S]*3 \* program\.sourceCounts\.zero[\s\S]*2 \* program\.sourceCounts\.one[\s\S]*2 \* \(3 \* gates - 1\)/u);
  assert.match(source, /lockedDisplayedGateCount[\s\S]*lockedBaselineCount program \+ 4/u);

  const docs = `${await text0('docs/lean_locked_nand_macros.md')}\n${await text0('docs/FORMAL_RECONSTRUCTION.md')}`;
  assert.match(docs, /multi-output/iu);
  assert.match(docs, /baseline coordinates? plus (?:one|the) final coordinate/iu);
  assert.doesNotMatch(docs, /global BaselineDistinct (?:is|has been) proved/iu);
});

test('legacy synthetic m=2 fixture is numerically inconsistent and quarantined', async () => {
  const preNAND = makeSyntheticPreNAND0();
  const gpack = makeSyntheticGPack0();
  const actualSources = preNAND.gates.flatMap((gate) => gate.sources);
  const metadata = preNAND.sourceOccurrences;
  const metadataTotal = metadata.equality + metadata.const0 + metadata.const1;

  assert.equal(preNAND.gates.length, 2);
  assert.deepEqual(actualSources, ['x0', 'x1', 'g0', 'x2']);
  assert.equal(actualSources.length, 4);
  assert.deepEqual(metadata, { equality: 4, const0: 1, const1: 1 });
  assert.equal(metadataTotal, 6);

  const honestBaseline = baseline0({ gates: 2, equality: 4, zero: 0, one: 0, prefixChecks: 6 });
  const metadataConsistentBaseline = baseline0({ gates: 2, equality: 4, zero: 1, one: 1, prefixChecks: 8 });
  const storedBaseline = computeLockedNANDBaseline0({
    gateCount: 2,
    equalityOccurrences: 4,
    constZeroOccurrences: 1,
    constOneOccurrences: 1,
  });

  assert.equal(honestBaseline, 86);
  assert.equal(metadataConsistentBaseline, 95);
  assert.equal(storedBaseline, 91);
  assert.deepEqual([honestBaseline + 4, metadataConsistentBaseline + 4, storedBaseline + 4], [90, 99, 95]);
  assert.equal(gpack.BaselineCert.baseline, 91);
  assert.equal(gpack.PrefixCert.prefixConjunctionGates, 10);
  assert.equal(gpack.ThresholdCert.fullWordSize, 95);

  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.legacySyntheticLockedNANDM2FixtureStatus, 'quarantined-internally-inconsistent');
  assert.equal(status.legacySyntheticLockedNANDM2HonestBaseline, 86);
  assert.equal(status.legacySyntheticLockedNANDM2MetadataConsistentBaseline, 95);
  assert.equal(status.legacySyntheticLockedNANDM2StoredBaseline, 91);
  assert.equal(status.legacySyntheticLockedNANDM2HonestDisplayedGateCount, 90);
  assert.equal(status.legacySyntheticLockedNANDM2MetadataConsistentDisplayedGateCount, 99);
  assert.equal(status.legacySyntheticLockedNANDM2StoredDisplayedGateCount, 95);
});

test('status credits only local and conditional PR7 results', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  for (const field of [
    'leanLockedNANDDirectCandidatesFormalized',
    'leanLockedNANDDirectAxiomAuditPassed',
    'leanLockedNANDInternalMacroConstantsAbsent',
    'leanDirectWireOutputLowerBoundFormalized',
    'leanDirectWireBaselineAxiomAuditPassed',
    'leanLockedNANDSourceDerivedCountsFormalized',
    'leanLockedNANDBaselineAccountingFormalized',
    'leanLockedNANDBaselineAxiomAuditPassed',
    'leanLockedNANDConditionalSquareBaselineExactnessFormalized',
    'leanLockedNANDLocalBaselineConditionsFormalized',
    'leanLockedNANDLocalSquareBaselineExactnessFormalized',
    'leanLockedNANDLocalBaselineAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.leanLockedNANDProofScope, 'typed-local-macros-source-derived-counts-and-five-local-square-baselines');
  for (const field of [
    'leanLockedNANDBuilderFormalized',
    'leanLockedNANDThresholdFormalized',
    'leanLockedNANDResidualSlackAtMostFourFormalized',
    'leanLockedNANDPolynomialBuilderFormalized',
  ]) assert.equal(status[field], false, field);
  assert.equal(status.remainingBlockers.length, 6);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.satInPConclusionAccepted, false);
  assert.equal(status.pEqualsNPConclusionAccepted, false);
});

test('audit rejects hidden assumptions, broad claims, missing local candidates, and transcript drift', async () => {
  const layer = LAYERS[0];
  const source = await text0(layer.source);
  assert.equal(validateLayer0(`import PNP.Complexity\n${source}`, layer).includes('closed-import'), true);
  assert.equal(validateLayer0(`${source}\naxiom hidden : True\n`, layer).includes('assumption-declaration'), true);
  assert.equal(validateLayer0(`${source}\nprivate theorem hidden : True := True.intro\n`, layer).includes('private-declaration'), true);
  assert.equal(validateLayer0(`${source}\nexample : True := True.intro\n`, layer).includes('unaudited-declaration-form'), true);
  assert.equal(validateLayer0(source.replace('def equalityDirect :', 'def removedEqualityDirect :'), layer).some((failure) => failure.includes('equalityDirect')), true);
  assert.equal(validateLayer0(`${source}\ntheorem hidden_propext (a b : Prop) (h : a ↔ b) : a = b := propext h\n`, layer).includes('forbidden-shortcut'), true);
  const printed = printed0(await text0(layer.audit));
  assert.notDeepEqual(declarations0(`${source}\ntheorem extra : True := True.intro\n`), printed);
  assert.notDeepEqual(printed.slice(0, -1), declarations0(source));
});
