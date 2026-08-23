import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const SOURCE_PATH = 'lean/PNP/LockedNANDCarrierTrace.lean';
const AUDIT_PATH = 'lean-audit/PNPLockedNANDCarrierTraceAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPLockedNANDCarrierTrace.lean';
const IMPORTS = Object.freeze([
  'PNP.LockedNANDBaseline',
  'PNP.LockedNANDLocalBaseline',
]);
const PRIVATE_HELPERS = Object.freeze([
  'acceptedEarlierChecks',
  'acceptedCurrentCheck',
]);
const REQUIRED = Object.freeze([
  'structure Circuit',
  'def Circuit.Satisfiable',
  'inductive CarrierSlot',
  'def carrierWidth',
  'def CarrierSlot.encode',
  'def decodeCarrierSlot',
  'theorem decode_encode',
  'theorem encode_decode',
  'theorem carrierSeparation',
  'theorem finalLock_fresh',
  'structure CarrierValuation',
  'def sourceCheck',
  'def traceCheck',
  'def distinguishedChecks',
  'theorem distinguishedChecks_length',
  'def coherentExtension',
  'theorem tracePredicate_coherentExtension',
  'theorem trace_sound_of_predicate_true',
  'theorem traceEquivalence',
  'theorem satisfiable_iff_trace_extension',
  'theorem exists_coherent_trace',
]);
const MILESTONE_THEOREMS = Object.freeze([
  'PNP.DirectWire.LockedNANDTrace.carrierSeparation',
  'PNP.DirectWire.LockedNANDTrace.finalLock_fresh',
  'PNP.DirectWire.LockedNANDTrace.distinguishedChecks_length',
  'PNP.DirectWire.LockedNANDTrace.tracePredicate_coherentExtension',
  'PNP.DirectWire.LockedNANDTrace.trace_sound_of_predicate_true',
  'PNP.DirectWire.LockedNANDTrace.traceEquivalence',
  'PNP.DirectWire.LockedNANDTrace.satisfiable_iff_trace_extension',
  'PNP.DirectWire.LockedNANDTrace.exists_coherent_trace',
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map((head) => `PNP.DirectWire.LockedNANDTrace.${head.name}`);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

function privateHelpers0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  return [...stripped.matchAll(/^\s*private\s+(?:def|theorem)\s+([^\s({:]+)/gmu)]
    .map((match) => match[1]);
}

function validateSource0(source) {
  const failures = [];
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify(IMPORTS)) failures.push('closed-import');
  if (!/namespace PNP\s+[\s\S]*namespace DirectWire\s+[\s\S]*namespace LockedNANDTrace/u.test(source)) {
    failures.push('namespace');
  }
  for (const required of REQUIRED) {
    if (!source.includes(required)) failures.push(`missing:${required}`);
  }
  if (/\b(?:Classical(?:\.choice)?|native_decide|exact_mod_cast|linarith|nlinarith|sorry|admit)\b/u.test(source)) {
    failures.push('forbidden-shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(source)) failures.push('host-evaluation');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('unaudited-declaration-form');
  if (JSON.stringify(privateHelpers0(source)) !== JSON.stringify(PRIVATE_HELPERS)) {
    failures.push('private-helper-drift');
  }
  return failures;
}

test('global carrier and trace source is closed, constructive, and narrowly imported', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers all 71 public declarations exactly once', async () => {
  const expected = declarations0(await text0(SOURCE_PATH));
  const printed = printed0(await text0(AUDIT_PATH));
  assert.equal(expected.length, 71);
  assert.deepEqual(printed, expected);
  assert.equal(new Set(printed).size, 71);
});

test('carrier layout is a derived exact partition with a fresh final lock', async () => {
  const source = await text0(SOURCE_PATH);
  assert.match(source, /def carrierWidth[\s\S]*inputs \+ 6 \* gates \+ 1/u);
  for (const family of [
    'primary',
    'trace',
    'occurrence',
    'sourceLock',
    'traceLock',
    'finalLock',
  ]) assert.match(source, new RegExp(`\\| ${family}\\b`, 'u'));
  assert.match(source, /structure CarrierSeparation[\s\S]*decodeEncode[\s\S]*encodeDecode[\s\S]*encodeInjective/u);
  assert.match(source, /theorem carrierSeparation[\s\S]*decodeEncode := decode_encode[\s\S]*encodeDecode := encode_decode/u);
  assert.match(source, /theorem finalLock_fresh[\s\S]*slot\.encode ≠ finalLockSlot/u);
  assert.doesNotMatch(source, /(?:separation|freshness)(?:Certificate|Digest|Claim|Flag)\s*:/u);
});

test('the trace predicate is generated from the typed program and has exactly three checks per gate', async () => {
  const source = await text0(SOURCE_PATH);
  assert.match(source, /def sourceCheck[\s\S]*match source with[\s\S]*\.input[\s\S]*\.constant false[\s\S]*\.constant true[\s\S]*\.gate/u);
  assert.match(source, /def gateChecks[\s\S]*sourceCheck gate\.left[\s\S]*sourceCheck gate\.right[\s\S]*traceCheck/u);
  assert.match(source, /def distinguishedChecks[\s\S]*Program inputs gates[\s\S]*\.empty[\s\S]*\.snoc initial gate/u);
  assert.match(source, /theorem distinguishedChecks_length[\s\S]*= 3 \* gates/u);
  assert.doesNotMatch(source, /(?:checks|occurrences|trace)\s*:\s*List Bool\s*→/u);
  assert.doesNotMatch(source, /(?:certificate|digest|proofRef|trustFlag|hostLookup|scheduleLookup)\s*:/u);
});

test('both directions of trace equivalence are proved for every finite typed circuit', async () => {
  const source = await text0(SOURCE_PATH);
  assert.match(source, /theorem tracePredicate_coherentExtension[\s\S]*tracePredicate program \(coherentExtension program input\) = true/u);
  assert.match(source, /theorem trace_sound_of_predicate_true[\s\S]*valuation\.trace index =[\s\S]*program\.eval valuation\.primary index/u);
  assert.match(source, /theorem traceEquivalence[\s\S]*∃ valuation : CarrierValuation inputs circuit\.gateCount[\s\S]*↔[\s\S]*circuit\.program\.eval input circuit\.outputGate = true/u);
  assert.match(source, /theorem satisfiable_iff_trace_extension[\s\S]*circuit\.Satisfiable ↔[\s\S]*∃ valuation/u);
  assert.match(source, /theorem exists_coherent_trace[\s\S]*∀?/u);
  assert.doesNotMatch(source, /\(traceCertificate\s*:/u);
  assert.doesNotMatch(source, /(?:def|theorem)\s+(?:lockedNANDBuilder|lockedNANDThreshold|p_eq_np)\b/u);
});

test('regression covers carrier families, zero/two-gate sizes, truth branches, and malformed traces', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'carrierWidth 2 2 = 15',
    'decodeCarrierSlot_primary',
    'decodeCarrierSlot_trace',
    'decodeCarrierSlot_occurrence',
    'decodeCarrierSlot_sourceLock',
    'decodeCarrierSlot_traceLock',
    'decodeCarrierSlot_finalLock',
    'finalLock_fresh',
    'distinguishedChecks (Program.empty',
    'distinguishedChecks negationProgram',
    'distinguishedChecks conjunctionProgram',
    'traceEquivalence negationCircuit inputFalse',
    'traceEquivalence negationCircuit inputTrue',
    'satisfiable_iff_trace_extension constantTrueCircuit',
    'malformedNegationTrace',
    'unlockedNegationTrace',
    'trace_sound_of_predicate_true',
  ]) assert.match(regression, new RegExp(token.replaceAll(/[.*+?^${}()|[\]\\]/gu, '\\$&'), 'u'));
  assert.doesNotMatch(regression, /\b(?:native_decide|sorry|admit)\b/u);
});

test('documentation maps the theorem to legacy Section 17 without overclaiming the threshold', async () => {
  const docs = `${await text0('docs/lean_locked_nand_carrier_trace.md')}\n${await text0('docs/FORMAL_RECONSTRUCTION.md')}`;
  assert.match(docs, /Section 17/iu);
  assert.match(docs, /Theorem 17\.2/iu);
  assert.match(docs, /Lemmas 17\.5[–-]17\.7/iu);
  assert.match(docs, /topological induction/iu);
  assert.match(docs, /arbitrary finite NAND circuits/iu);
  assert.match(docs,
    /not\s+(?:the\s+)?(?:complete\s+)?locked-NAND\s+(?:builder|threshold theorem)/iu);
  assert.match(docs, /BaselineDistinct/iu);
  assert.match(docs, /FinalLockSeparation/iu);
});

test('status and publication credit only carrier layout and trace equivalence', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  for (const field of [
    'leanLockedNANDCarrierLayoutFormalized',
    'leanLockedNANDTraceEquivalenceFormalized',
    'leanLockedNANDCarrierTraceAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.leanLockedNANDCarrierTraceAuditedDeclarationCount, 71);
  assert.equal(status.leanLockedNANDCarrierTraceScope,
    'arbitrary-finite-topological-nand-circuits-carrier-separation-and-trace-equivalence');
  for (const field of [
    'leanLockedNANDDerivedFinalOutputLawsFormalized',
    'leanLockedNANDResidualSlackAtMostFourFormalized',
    'leanLockedNANDGlobalSemanticThresholdFormalized',
  ]) assert.equal(status[field], true, field);
  for (const field of [
    'leanLockedNANDBuilderFormalized',
    'leanLockedNANDThresholdFormalized',
    'leanLockedNANDPolynomialBuilderFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.projectSpecificAxiomInventory.length, 3);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);

  const milestone = status.formalPublicationMilestones.find(
    ({ id }) => id === 'locked-nand-global-carrier-trace-equivalence',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone.requiredTheorems, MILESTONE_THEOREMS);
});

test('hostile mutations revoke source, transcript, and theorem-shape credit', async () => {
  const source = await text0(SOURCE_PATH);
  assert.equal(validateSource0(`import PNP.LockedNAND\n${source}`).includes('closed-import'), true);
  assert.equal(validateSource0(`${source}\naxiom hidden : True\n`).includes('assumption-declaration'), true);
  assert.equal(validateSource0(`${source}\nexample : True := True.intro\n`).includes('unaudited-declaration-form'), true);
  assert.equal(validateSource0(`${source}\ntheorem hidden : True := by native_decide\n`).includes('forbidden-shortcut'), true);
  assert.equal(validateSource0(`${source}\n#eval 1 + 1\n`).includes('host-evaluation'), true);
  assert.equal(validateSource0(source.replace('theorem traceEquivalence', 'theorem removedTraceEquivalence')).some(
    (failure) => failure.includes('traceEquivalence'),
  ), true);
  assert.equal(validateSource0(source.replace('private theorem acceptedEarlierChecks', 'private theorem renamedEarlierChecks')).includes(
    'private-helper-drift',
  ), true);
  const printed = printed0(await text0(AUDIT_PATH));
  assert.notDeepEqual(declarations0(`${source}\ntheorem extra : True := True.intro\n`), printed);
  assert.notDeepEqual(printed.slice(0, -1), declarations0(source));
});
