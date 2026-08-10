import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';
import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasPrivateLeanDeclaration0,
  hasUnauditedLeanDeclarationForm0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));

const LAYERS = Object.freeze([
  Object.freeze({
    source: 'lean/PNP/NANDTruthTable.lean',
    audit: 'lean-audit/PNPNANDTruthTableAxiomAudit.lean',
    imports: ['PNP.NANDEnumerator'],
    required: [
      'inductive BoolTuple',
      'def allBoolTuples',
      'theorem mem_allBoolTuples',
      'def equivalentBool',
      'theorem equivalentBool_eq_true_iff',
    ],
  }),
  Object.freeze({
    source: 'lean/PNP/NANDMinimum.lean',
    audit: 'lean-audit/PNPNANDMinimumAxiomAudit.lean',
    imports: ['PNP.NANDTruthTable'],
    required: [
      'structure Implementation',
      'def scanEquivalentSizes',
      'def referenceMinimum',
      'theorem referenceMinimumWitness_equivalent',
      'theorem referenceMinimum_le_of_equivalent',
      'theorem referenceMinimum_invariant',
      'def residualSlack',
      'theorem residualSlack_eq_zero_iff_minimum',
    ],
  }),
  Object.freeze({
    source: 'lean/PNP/NANDComposition.lean',
    audit: 'lean-audit/PNPNANDCompositionAxiomAudit.lean',
    imports: ['PNP.NANDTruthTable'],
    required: [
      'def Candidate.sequential',
      'theorem Candidate.sequential_size',
      'theorem Candidate.sequential_semantics',
      'structure FramedContext',
      'def FramedContext.plug',
      'theorem FramedContext.plug_size',
      'theorem compatibleReplacement_framed',
    ],
  }),
  Object.freeze({
    source: 'lean/PNP/NANDSlack.lean',
    audit: 'lean-audit/PNPNANDSlackAxiomAudit.lean',
    imports: ['PNP.NANDComposition', 'PNP.NANDMinimum'],
    required: [
      'theorem framedGlobalSlackLaw',
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
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)].map((match) => match[1]);
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

test('truth table, minimum, composition, and slack layers have closed constructive sources', async () => {
  for (const layer of LAYERS) {
    assert.deepEqual(validateLayer0(await text0(layer.source), layer), [], layer.source);
  }
});

test('each dedicated axiom transcript covers every explicit declaration exactly once', async () => {
  for (const layer of LAYERS) {
    const expected = declarations0(await text0(layer.source));
    const printed = printed0(await text0(layer.audit));
    assert.deepEqual(printed, expected, layer.audit);
    assert.equal(new Set(printed).size, printed.length, layer.audit);
  }
});

test('reference minimum is exhaustive and carries no polynomial-runtime claim', async () => {
  const source = await text0('lean/PNP/NANDMinimum.lean');
  assert.match(source, /scan exact gate counts in increasing order through `bound`/iu);
  assert.match(source, /referenceMinimum_le_of_equivalent/u);
  assert.match(source, /residualSlack_eq_zero_iff_minimum/u);
  assert.doesNotMatch(source, /polynomial(?:-time| runtime)|PolyTime/u);

  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanNANDReferenceMinimumExhaustive, true);
  assert.equal(status.leanNANDReferenceMinimumScope, 'finite-boolean-direct-wire-empty-profile');
  assert.equal(status.leanNANDReferenceMinimumPolynomialRuntimeProved, false);
  assert.equal(status.leanNANDReplacementScope, 'concrete-serial-framed-context');
  assert.equal(status.leanCompatibleReplacementFormalized, false);
  assert.equal(status.leanGlobalSlackLawFormalized, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.rootLeanTheoremPresent, false);
});

test('replacement and global slack are limited to concrete framed contexts', async () => {
  const composition = await text0('lean/PNP/NANDComposition.lean');
  const slack = await text0('lean/PNP/NANDSlack.lean');
  assert.match(composition, /structure FramedContext/u);
  assert.match(composition, /theorem compatibleReplacement_framed/u);
  assert.match(slack, /theorem framedGlobalSlackLaw/u);
  assert.match(composition, /does not model arbitrary gate subsets, support profiles/u);
  assert.match(slack, /introduces no arbitrary support sets, profile records/u);
  assert.doesNotMatch(`${composition}\n${slack}`, /(?:structure|def|theorem)\s+(?:SupportProfile|ArbitrarySupport)/u);
});

test('workflow enforces all four complete zero-axiom transcripts', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  for (const [audit, count] of [
    ['PNPNANDTruthTableAxiomAudit.lean', 29],
    ['PNPNANDMinimumAxiomAudit.lean', 27],
    ['PNPNANDCompositionAxiomAudit.lean', 50],
    ['PNPNANDSlackAxiomAudit.lean', 15],
  ]) {
    assert.match(workflow, new RegExp(
      `${audit.replace('.', '\\.')}[\\s\\S]{0,900}grep -Fc 'does not depend on any axioms'\\)" -eq ${count}`,
      'u',
    ));
  }
  assert.match(workflow, /run: node --test[^\n]*audits\/lean-nand-reference-minimum0\.test\.mjs/u);
});

test('audit rejects hidden assumptions, shortcuts, missing scope, and transcript drift', async () => {
  const layer = LAYERS[0];
  const source = await text0(layer.source);
  assert.equal(validateLayer0(`import PNP.Complexity\n${source}`, layer).includes('closed-import'), true);
  assert.equal(validateLayer0(`${source}\naxiom hidden : True\n`, layer).includes('assumption-declaration'), true);
  assert.equal(validateLayer0(`${source}\nprivate theorem hidden : True := True.intro\n`, layer).includes('private-declaration'), true);
  assert.equal(validateLayer0(`${source}\nexample : True := True.intro\n`, layer).includes('unaudited-declaration-form'), true);
  assert.equal(validateLayer0(source.replace('def equivalentBool', 'def removedEquivalentBool'), layer).some((failure) => failure.includes('equivalentBool')), true);
  assert.equal(validateLayer0(`${source}\ntheorem hidden_propext (a b : Prop) (h : a ↔ b) : a = b := propext h\n`, layer).includes('forbidden-shortcut'), true);
  const printed = printed0(await text0(layer.audit));
  assert.notDeepEqual(declarations0(`${source}\ntheorem extra : True := True.intro\n`), printed);
  assert.notDeepEqual(printed.slice(0, -1), declarations0(source));
});
