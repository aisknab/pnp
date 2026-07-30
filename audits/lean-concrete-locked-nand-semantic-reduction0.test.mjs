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
const ENCODING_PATH = 'lean/PNP/Concrete/LockedNANDEncoding.lean';
const REDUCTION_PATH = 'lean/PNP/Concrete/LockedNANDReduction.lean';
const AUDIT_PATH =
  'lean-audit/PNPConcreteLockedNANDSemanticReductionAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPConcreteLockedNANDSemanticReduction.lean';
const DOCS_PATH =
  'docs/lean_concrete_locked_nand_semantic_reduction.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const NAMESPACE = 'PNP.Concrete.LockedNAND';

const CORE_DEFINITIONS = Object.freeze([
  `${NAMESPACE}.RawCircuit.eval`,
  `${NAMESPACE}.RawCircuit.normalize`,
  `${NAMESPACE}.RawCircuit.elaborate`,
  `${NAMESPACE}.RawCandidate.elaborate`,
  `${NAMESPACE}.RawLockedInstance.elaborate`,
  `${NAMESPACE}.encodeCircuit`,
  `${NAMESPACE}.decodeCircuit`,
  `${NAMESPACE}.encodeLockedInstance`,
  `${NAMESPACE}.decodeLockedInstance`,
  `${NAMESPACE}.EncodedNANDSAT`,
  `${NAMESPACE}.EncodedLockedNANDThreshold`,
  `${NAMESPACE}.buildLockedNANDInstance`,
]);

const ENCODING_THEOREMS = Object.freeze([
  `${NAMESPACE}.evalRawGatesAux_append`,
  `${NAMESPACE}.evalRawGatesAux_length`,
  `${NAMESPACE}.RawCircuit.normalize_gate`,
  `${NAMESPACE}.RawCircuit.normalize_idempotent`,
  `${NAMESPACE}.RawCircuit.normalize_eval`,
  `${NAMESPACE}.RawCircuit.elaborate_normalize`,
  `${NAMESPACE}.RawCircuit.normalize_satisfiable`,
  `${NAMESPACE}.fallbackCircuit_not_satisfiable`,
  `${NAMESPACE}.RawSource.elaborate_ofSource`,
  `${NAMESPACE}.RawGate.elaborate_ofGate`,
  `${NAMESPACE}.elaborateGatesAux_append`,
  `${NAMESPACE}.elaborateGates_rawProgramGates`,
  `${NAMESPACE}.elaborateSources_rawOutputSources`,
  `${NAMESPACE}.RawCircuit.elaborate_ofCircuit`,
  `${NAMESPACE}.RawCandidate.elaborate_ofCandidate`,
  `${NAMESPACE}.RawLockedInstance.elaborate_ofCandidate`,
  `${NAMESPACE}.Token.ofBits_bits`,
  `${NAMESPACE}.decodeTokens_encodeTokens`,
  `${NAMESPACE}.decodeNatTokens_encodeNatTokens_append`,
  `${NAMESPACE}.decodeSourceTokens_encodeSourceTokens_append`,
  `${NAMESPACE}.decodeNGatesTokens_encodeGateListTokens_append`,
  `${NAMESPACE}.decodeNSourcesTokens_encodeSourceListTokens_append`,
  `${NAMESPACE}.decodeCircuitTokens_encodeCircuitTokens`,
  `${NAMESPACE}.decodeCircuit_encodeCircuit`,
  `${NAMESPACE}.decodeValidCircuit_encodeCircuit`,
  `${NAMESPACE}.decodeCandidateTokens_encodeCandidateTokens`,
  `${NAMESPACE}.decodeCandidate_encodeCandidate`,
  `${NAMESPACE}.decodeLockedInstanceTokens_encodeLockedInstanceTokens`,
  `${NAMESPACE}.decodeLockedInstance_encodeLockedInstance`,
  `${NAMESPACE}.encodeTokens_length`,
]);

const REDUCTION_THEOREMS = Object.freeze([
  `${NAMESPACE}.decodeElaboratedCircuit_encodeCircuit_ofCircuit`,
  `${NAMESPACE}.buildLockedNANDInstance_of_decoded`,
  `${NAMESPACE}.buildLockedNANDInstance_of_malformed`,
  `${NAMESPACE}.empty_not_encodedLockedNANDThreshold`,
  `${NAMESPACE}.encoded_fullCandidate_threshold_iff_satisfiable`,
  `${NAMESPACE}.buildLockedNANDInstance_correct`,
]);

const AUDITED_DECLARATIONS = Object.freeze([
  ...CORE_DEFINITIONS,
  ...ENCODING_THEOREMS,
  ...REDUCTION_THEOREMS,
]);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.RawCircuit.normalize_idempotent`,
  `${NAMESPACE}.RawCircuit.normalize_eval`,
  `${NAMESPACE}.RawCircuit.elaborate_ofCircuit`,
  `${NAMESPACE}.RawCandidate.elaborate_ofCandidate`,
  `${NAMESPACE}.RawLockedInstance.elaborate_ofCandidate`,
  `${NAMESPACE}.decodeTokens_encodeTokens`,
  `${NAMESPACE}.decodeCircuit_encodeCircuit`,
  `${NAMESPACE}.decodeLockedInstance_encodeLockedInstance`,
  `${NAMESPACE}.decodeElaboratedCircuit_encodeCircuit_ofCircuit`,
  `${NAMESPACE}.encoded_fullCandidate_threshold_iff_satisfiable`,
  `${NAMESPACE}.buildLockedNANDInstance_correct`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

function theoremHeads0(source) {
  return explicitLeanDeclarationHeads0(source)
    .filter(({ kind }) => kind === 'theorem')
    .map(({ name }) => name);
}

function validateSource0(encoding, reduction) {
  const failures = [];
  const combined = stripLeanCommentsAndStrings0(`${encoding}\n${reduction}`);
  if (/\b(?:Classical(?:\.choice)?|native_decide|exact_mod_cast|linarith|nlinarith|sorry|admit)\b/u.test(combined)) {
    failures.push('forbidden-shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(combined)) {
    failures.push('host-evaluation');
  }
  if (hasLeanAssumptionDeclaration0(encoding)
      || hasLeanAssumptionDeclaration0(reduction)) {
    failures.push('assumption-declaration');
  }
  if (hasUnauditedLeanDeclarationForm0(encoding)
      || hasUnauditedLeanDeclarationForm0(reduction)) {
    failures.push('unaudited-declaration-form');
  }
  if (/\b(?:hostLookup|scheduleLookup|proofCertificate|callerCertificate|trustFlag)\b/u.test(combined)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\b(?:PolynomialTimeFunction|PolynomialReduction|WorkMachine|compileWorkMachine|Machine)\b/u.test(combined)) {
    failures.push('machine-overclaim');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|lockedNANDPolynomialBuilder|encodedPolynomialReduction)\b/u.test(combined)) {
    failures.push('project-overclaim');
  }
  return failures;
}

test('encoding fixes the strict version-zero grammar and rejects spare codes', async () => {
  const source = await text0(ENCODING_PATH);
  assert.deepEqual(
    [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
      .map((match) => match[1]),
    ['PNP.Concrete.BitString', 'PNP.LockedNANDGlobalSemanticThreshold'],
  );
  for (const row of [
    ['version0', 'false, false, false, false'],
    ['unit', 'false, false, false, true'],
    ['natEnd', 'false, false, true, false'],
    ['input', 'false, false, true, true'],
    ['constantFalse', 'false, true, false, false'],
    ['constantTrue', 'false, true, false, true'],
    ['gate', 'false, true, true, false'],
    ['gateEnd', 'false, true, true, true'],
    ['programEnd', 'true, false, false, false'],
    ['outputsEnd', 'true, false, false, true'],
    ['threshold', 'true, false, true, false'],
    ['instanceEnd', 'true, false, true, true'],
  ]) {
    assert.match(
      source,
      new RegExp(`\\| \\.${row[0]} => \\[${row[1]}\\]`, 'u'),
      row[0],
    );
  }
  assert.match(source, /\| true, true, _, _ => none/u);
  assert.match(source, /decodeTokens[\s\S]*\| _ => none/u);
  assert.match(source, /decodeCircuitTokens[\s\S]*\.programEnd/u);
  assert.match(source, /\[\.outputsEnd, \.instanceEnd\]/u);
  assert.match(source, /decodeLockedInstanceTokens[\s\S]*\.threshold/u);
});

test('normalization has direct semantics and elaborates the complete candidate', async () => {
  const source = await text0(ENCODING_PATH);
  assert.match(source, /def RawCircuit\.normalize[\s\S]*\.input index[\s\S]*gates := circuit\.gates \+\+[\s\S]*\.gate \(first \+ 1\)/u);
  assert.match(source, /\.constant false[\s\S]*\.constant true[\s\S]*\.constant true/u);
  assert.match(source, /\.constant true[\s\S]*\.constant false[\s\S]*\.constant false/u);
  assert.match(source, /theorem RawCircuit\.normalize_eval[\s\S]*circuit\.normalize\.eval input = circuit\.eval input/u);
  assert.match(source, /def RawCandidate\.elaborate/u);
  assert.match(source, /def RawLockedInstance\.elaborate/u);
  assert.match(source, /def lockedInstanceOfCircuit[\s\S]*fullCandidate circuit[\s\S]*lockedBaselineCount circuit\.program/u);
  assert.deepEqual(validateSource0(source, await text0(REDUCTION_PATH)), []);
});

test('concrete languages measure decoded full bytes and remain machine-neutral', async () => {
  const source = await text0(REDUCTION_PATH);
  assert.deepEqual(
    [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
      .map((match) => match[1]),
    ['PNP.Concrete.Complexity', 'PNP.Concrete.LockedNANDEncoding'],
  );
  assert.match(source, /def EncodedNANDSAT\s*:\s*Language[\s\S]*decodeElaboratedCircuit/u);
  assert.match(source, /def EncodedLockedNANDThreshold\s*:\s*Language[\s\S]*raw\.elaborate[\s\S]*referenceMinimum[\s\S]*Implementation\.mk packed\.gateCount packed\.candidate/u);
  assert.match(source, /def buildLockedNANDInstance[\s\S]*\| none => \[\][\s\S]*encodeLockedInstance \(lockedInstanceOfCircuit packed\.circuit\)/u);
  assert.match(source, /theorem buildLockedNANDInstance_correct[\s\S]*EncodedNANDSAT bits ↔[\s\S]*EncodedLockedNANDThreshold/u);
  assert.doesNotMatch(source, /\b(?:runtimeBound|outputSizeBound|haltsWithin|machineOutput)\b/u);
});

test('all 36 theorem declarations and 12 executable interfaces are axiom-audited', async () => {
  const encoding = await text0(ENCODING_PATH);
  const reduction = await text0(REDUCTION_PATH);
  assert.deepEqual(
    theoremHeads0(encoding),
    ENCODING_THEOREMS.map((name) =>
      name === `${NAMESPACE}.Token.ofBits_bits`
        ? 'ofBits_bits'
        : name.slice(`${NAMESPACE}.`.length)),
  );
  assert.deepEqual(
    theoremHeads0(reduction),
    REDUCTION_THEOREMS.map((name) => name.slice(`${NAMESPACE}.`.length)),
  );
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(
    [...audit.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
      .map((match) => match[1]),
    ['PNP.Concrete.LockedNANDReduction'],
  );
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(printed0(audit)).size, 48);
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(
    inventory.declarations.map((entry) => [entry.name, entry]),
  );
  for (const name of AUDITED_DECLARATIONS) {
    const row = rows.get(name);
    assert.notEqual(row, undefined, name);
    assert.equal(
      row.axioms.every((axiom) =>
        ['Quot.sound', 'propext'].includes(axiom)),
      true,
      `${name}:${row.axioms.join(',')}`,
    );
  }
  const root = await text0('lean/PNP.lean');
  assert.match(root, /^import PNP\.Concrete\.LockedNANDEncoding$/mu);
  assert.match(root, /^import PNP\.Concrete\.LockedNANDReduction$/mu);
});

test('regression covers codecs, three normalization branches, exact bytes, and fail-closed behavior', async () => {
  const source = await text0(REGRESSION_PATH);
  for (const token of [
    'Token.ofBits true true false false = none',
    'decodeTokens [false] = none',
    'inputOutputCircuit.normalizationAddedGates = 2',
    'constantZeroOutputCircuit.normalizationAddedGates = 1',
    'RawCircuit.normalize_eval',
    'decodeCircuit_encodeCircuit',
    'decodeElaboratedCircuit_encodeCircuit_ofCircuit',
    'decodeCandidate_encodeCandidate',
    'decodeLockedInstance_encodeLockedInstance',
    'constantTrueCircuit_satisfiable',
    'constantFalseCircuit_not_satisfiable',
    'encoded_fullCandidate_threshold_iff_satisfiable',
    'buildLockedNANDInstance_of_decoded',
    'buildLockedNANDInstance [] = []',
    'empty_not_encodedLockedNANDThreshold',
    'buildLockedNANDInstance_correct',
  ]) assert.equal(source.includes(token), true, token);
  assert.doesNotMatch(
    source,
    /\b(?:Classical(?:\.choice)?|native_decide|sorry|admit)\b/u,
  );
});

test('status retains the semantic boundary and records its executable parser successor', async () => {
  const status = JSON.parse(
    await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  );
  for (const field of [
    'leanConcreteLockedNANDCanonicalEncodingFormalized',
    'leanConcreteLockedNANDNormalizationSemanticsFormalized',
    'leanConcreteLockedNANDCompleteCandidateCodecFormalized',
    'leanConcreteLockedNANDEncodedSemanticReductionFormalized',
    'leanConcreteLockedNANDEncodedSemanticReductionAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanConcreteLockedNANDEncodedSemanticReductionAuditedDeclarationCount,
    48,
  );
  assert.equal(
    status.leanConcreteLockedNANDEncodedSemanticReductionScope,
    'strict-version-zero-codec-direct-normalization-semantics-complete-candidate-bytes-and-fail-closed-semantic-reduction',
  );
  assert.equal(
    status.leanConcreteLockedNANDParserMachineFormalized,
    true,
  );
  assert.equal(
    status.leanConcreteLockedNANDEmitterMachineFormalized,
    true,
  );
  assert.equal(
    status.leanConcreteLockedNANDPolynomialReductionFormalized,
    true,
  );
  for (const field of [
    'leanLockedNANDPolynomialBuilderFormalized',
    'leanLockedNANDBuilderFormalized',
    'leanLockedNANDThresholdFormalized',
  ]) assert.equal(status[field], false, field);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.remainingBlockers.length, 6);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  const milestone = status.formalPublicationMilestones.find(
    ({ id }) =>
      id === 'concrete-locked-nand-encoded-semantic-boundary',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone.requiredTheorems, MILESTONE_THEOREMS);
});

test('technical documentation records generated evidence and the strategic next step', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const status = JSON.parse(
    await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  );
  const map = JSON.parse(
    await text0('publication/FORMAL_PUBLICATION_MAP.json'),
  );
  for (const token of [
    inventory.coordinate,
    status.coordinate,
    map.coordinate,
    `${inventory.declarationCount.toLocaleString('en-US')} declarations`,
    `${inventory.theoremCount.toLocaleString('en-US')} theorems`,
    `${inventory.assumptionFreeTheoremCount.toLocaleString('en-US')} assumption-free theorems`,
    '48 audited declarations',
    'Quot.sound',
    'propext',
    'parser/validator machine',
    'not a `PolynomialReduction`',
    'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('hostile mutations revoke grammar, byte, semantic, transcript, and overclaim credit', async () => {
  const encoding = await text0(ENCODING_PATH);
  const reduction = await text0(REDUCTION_PATH);
  assert.equal(validateSource0(
    `${encoding}\naxiom hidden : True\n`, reduction,
  ).includes('assumption-declaration'), true);
  assert.equal(validateSource0(
    `${encoding}\nexample : True := True.intro\n`, reduction,
  ).includes('unaudited-declaration-form'), true);
  assert.equal(validateSource0(
    `${encoding}\ntheorem hidden : True := by native_decide\n`, reduction,
  ).includes('forbidden-shortcut'), true);
  assert.equal(validateSource0(
    encoding, `${reduction}\ndef callerCertificate := true\n`,
  ).includes('caller-or-host-certificate'), true);
  assert.equal(validateSource0(
    encoding, `${reduction}\ndef fake : PolynomialReduction EncodedNANDSAT EncodedLockedNANDThreshold := by sorry\n`,
  ).includes('machine-overclaim'), true);
  assert.notDeepEqual(
    theoremHeads0(encoding.replace(
      'theorem RawCircuit.normalize_eval',
      'theorem removed_normalize_eval',
    )),
    ENCODING_THEOREMS.map((name) =>
      name === `${NAMESPACE}.Token.ofBits_bits`
        ? 'ofBits_bits'
        : name.slice(`${NAMESPACE}.`.length)),
  );
  assert.doesNotMatch(
    encoding.replace(
      '| true, true, _, _ => none',
      '| true, true, _, _ => some .version0',
    ),
    /\| true, true, _, _ => none/u,
  );
  assert.doesNotMatch(
    reduction.replace(
      'Implementation.mk packed.gateCount packed.candidate',
      'Implementation.mk 0 packed.candidate',
    ),
    /Implementation\.mk packed\.gateCount packed\.candidate/u,
  );
  assert.doesNotMatch(
    reduction.replace(
      '| none => []',
      '| none => [false]',
    ),
    /\| none => \[\]/u,
  );
  assert.notDeepEqual(
    printed0(await text0(AUDIT_PATH)).slice(0, -1),
    AUDITED_DECLARATIONS,
  );
});
