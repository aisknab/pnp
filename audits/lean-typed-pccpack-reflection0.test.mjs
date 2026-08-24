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
const PATHS = Object.freeze({
  bridge: 'lean/PNP/Bridge.lean',
  audit: 'lean-audit/PNPTypedPCCPackReflectionAxiomAudit.lean',
  regression: 'lean-regression/PNPTypedPCCPackReflection.lean',
});

const AUDITED_DECLARATIONS = Object.freeze([
  'PNP.generatedPCCPackId',
  'PNP.GeneratePCCPack',
  'PNP.CheckPCCPackexp',
  'PNP.check_generated_pcc_pack_exp_accepts',
  'PNP.generated_pcc_pack_loop_certificate_exact',
  'PNP.check_pcc_pack_exp_rejects_mismatched_id',
  'PNP.typed_pccpack_reflection_checked_complete',
  'PNP.AcceptedGeneratedPackage',
  'PNP.accepted_generated_package',
  'PNP.FinalReportAntecedent',
  'PNP.accepted_generated_package_implies_residual_band_in_p',
  'PNP.accepted_generated_package_implies_locked_nand_in_p',
  'PNP.accepted_generated_package_implies_sat_in_p',
  'PNP.accepted_generated_package_implies_p_eq_np',
  'PNP.final_report_bridge',
]);

const MILESTONE_THEOREMS = Object.freeze([
  'PNP.check_generated_pcc_pack_exp_accepts',
  'PNP.generated_pcc_pack_loop_certificate_exact',
  'PNP.check_pcc_pack_exp_rejects_mismatched_id',
  'PNP.typed_pccpack_reflection_checked_complete',
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function declarationBlock0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex((head) => head.name === name);
  if (index === -1) return '';
  const end = heads[index + 1]?.index ?? source.length;
  return source.slice(heads[index].index, end);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

function validateTypedReflection0(files) {
  const failures = [];
  const bridge = compact0(files.bridge);
  if (hasLeanAssumptionDeclaration0(files.bridge) ||
      hasUnauditedLeanDeclarationForm0(files.bridge)) {
    failures.push('bridge-assumption');
  }
  const pack = declarationBlock0(files.bridge, 'PCCPack');
  if (!/id\s*:\s*String/u.test(pack) ||
      !/loopCertificate\s*:\s*PCCMinLoopCertificate/u.test(pack)) {
    failures.push('typed-pack-fields');
  }
  const generator = compact0(declarationBlock0(files.bridge,
    'GeneratePCCPack'));
  if (!/def GeneratePCCPack \(loop : PCCMinLoopCertificate\) : PCCPack :=/u.test(generator) ||
      !/id := generatedPCCPackId/u.test(generator) ||
      !/loopCertificate := loop/u.test(generator)) {
    failures.push('transparent-generator');
  }
  const checker = compact0(declarationBlock0(files.bridge,
    'CheckPCCPackexp'));
  if (!/def CheckPCCPackexp \(pack : PCCPack\) : Verdict :=/u.test(checker) ||
      !/if pack\.id = generatedPCCPackId then Verdict\.accept else Verdict\.reject/u.test(checker)) {
    failures.push('structural-checker');
  }
  const trust = declarationBlock0(files.bridge, 'CheckerTrustModel');
  if (!/satHard\s*:\s*SATHard/u.test(trust) ||
      /pccPackProducesPCCMinLoop|checkerAccepts|accepted\s*:\s*Bool/u.test(trust)) {
    failures.push('checker-trust-boundary');
  }
  if (!/def AcceptedGeneratedPackage \(loop : PCCMinLoopCertificate\) : Prop :=/u.test(bridge) ||
      !/\u2203 loop : PCCMinLoopCertificate, AcceptedGeneratedPackage loop/u.test(bridge) ||
      !/\(GeneratePCCPack loop\)\.loopCertificate/u.test(bridge)) {
    failures.push('explicit-loop-boundary');
  }
  for (const theorem of [
    'check_generated_pcc_pack_exp_accepts',
    'generated_pcc_pack_loop_certificate_exact',
    'check_pcc_pack_exp_rejects_mismatched_id',
    'typed_pccpack_reflection_checked_complete',
  ]) {
    if (!new RegExp(`theorem ${theorem}\\b`, 'u').test(bridge)) {
      failures.push('checked-theorem-surface');
    }
  }
  if (/sorry|admit|noncomputable|unsafe/u.test(
    stripLeanCommentsAndStrings0(files.bridge))) {
    failures.push('bridge-shortcut');
  }
  return [...new Set(failures)];
}

test('typed PCCPack generation and checking expose the proof-bearing loop', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  assert.deepEqual(validateTypedReflection0(Object.fromEntries(entries)), []);
});

test('axiom transcript and generic regression pin the M188 boundary', async () => {
  const [audit, regression] = await Promise.all([
    text0(PATHS.audit), text0(PATHS.regression),
  ]);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  for (const token of [
    'check_generated_pcc_pack_exp_accepts loop',
    'generated_pcc_pack_loop_certificate_exact loop',
    'check_pcc_pack_exp_rejects_mismatched_id',
    'AcceptedGeneratedPackage loop',
    '⟨loop, accepted_generated_package loop⟩',
    '{ satHard := hard }',
    'typed_pccpack_reflection_checked_complete loop',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|axiom|opaque|noncomputable|unsafe)\b/u);
});

test('compiled inventory records definitions and no project axioms', async () => {
  const inventory = JSON.parse(await text0('status/LEAN_THEOREM_INVENTORY.json'));
  const rows = new Map(inventory.declarations
    .map((entry) => [entry.name, entry]));
  assert.equal(rows.get('PNP.GeneratePCCPack')?.kind, 'definition');
  assert.equal(rows.get('PNP.CheckPCCPackexp')?.kind, 'definition');
  for (const name of MILESTONE_THEOREMS) {
    assert.equal(rows.get(name)?.kind, 'theorem', name);
    assert.deepEqual(rows.get(name)?.axioms, ['Quot.sound', 'propext'], name);
  }
  assert.deepEqual(inventory.projectAxioms, []);
});

test('status, publication, durable workflow, and documentation publish only M188', async () => {
  const [status, publication, workflow, pkg, verifier, readme, formalDoc,
    bridgeDoc, focusedDoc] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
    text0('.github/workflows/lean-bridge.yml'),
    text0('package.json').then(JSON.parse),
    text0('scripts/pnp-verify-all.mjs'),
    text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('docs/lean_bridge.md'),
    text0('docs/lean_typed_pccpack_reflection.md'),
  ]);
  assert.equal(status.leanTypedPCCPackReflectionFormalized, true);
  assert.equal(status.leanTypedPCCPackReflectionAxiomAuditPassed, true);
  assert.equal(status.leanTypedPCCPackReflectionAuditedDeclarationCount,
    AUDITED_DECLARATIONS.length);
  assert.equal(status.leanTypedPCCPackReflectionEndpointProjectAssumptionFree,
    true);
  assert.equal(status.leanTypedPCCPackReflectionOpaqueDeclarationsRemoved,
    true);
  assert.deepEqual(status.projectSpecificAxiomInventory, []);
  const row = publication.milestones.find(
    ({ id }) => id === 'typed-pccpack-reflection');
  assert.deepEqual(row?.requiredTheorems,
    ['PNP.typed_pccpack_reflection_checked_complete']);
  for (const token of [
    'lean-audit/PNPTypedPCCPackReflectionAxiomAudit.lean',
    'lean-regression/PNPTypedPCCPackReflection.lean',
    'audits/lean-typed-pccpack-reflection0.test.mjs',
    'test "$expected_count" -eq 15',
  ]) assert.equal(workflow.includes(token), true, token);
  assert.equal(pkg.scripts.posttest.includes(
    'audits/lean-typed-pccpack-reflection0.test.mjs'), true);
  assert.equal(verifier.includes(
    "'audits/lean-typed-pccpack-reflection0.test.mjs'"), true);
  for (const document of [readme, formalDoc, bridgeDoc, focusedDoc]) {
    assert.equal(document.includes('PCCMinLoopCertificate'), true);
  }
  for (const document of [readme, formalDoc, focusedDoc]) {
    assert.match(document,
      /does not (?:construct|construct or validate)[\s\S]{0,120}(?:certificate|mathematical content)/u);
  }
});

test('hostile regressions reject opaque, vacuous, and caller-trusted variants', async () => {
  const entries = await Promise.all(Object.entries(PATHS)
    .map(async ([key, file]) => [key, await text0(file)]));
  const files = Object.fromEntries(entries);
  const mutations = [
    files.bridge.replace(
      'def GeneratePCCPack (loop : PCCMinLoopCertificate) : PCCPack :=',
      'axiom GeneratePCCPack : PCCMinLoopCertificate → PCCPack\n\ndef ignoredGeneratePCCPack (loop : PCCMinLoopCertificate) : PCCPack :='),
    files.bridge.replace(
      'def CheckPCCPackexp (pack : PCCPack) : Verdict :=',
      'axiom CheckPCCPackexp : PCCPack → Verdict\n\ndef ignoredCheckPCCPackexp (pack : PCCPack) : Verdict :='),
    files.bridge.replace(
      'loopCertificate : PCCMinLoopCertificate',
      'certificateName : String'),
    files.bridge.replace(
      'if pack.id = generatedPCCPackId then Verdict.accept else Verdict.reject',
      'Verdict.accept'),
    files.bridge.replace(
      'satHard : SATHard',
      'pccPackProducesPCCMinLoop : AcceptedGeneratedPackage loop → PCCMinLoopCertificate\n  satHard : SATHard'),
    files.bridge.replace(
      '∃ loop : PCCMinLoopCertificate, AcceptedGeneratedPackage loop',
      'True'),
  ];
  for (const mutation of mutations) {
    assert.notEqual(mutation, files.bridge);
    assert.notDeepEqual(validateTypedReflection0({ ...files, bridge: mutation }),
      []);
  }
});
