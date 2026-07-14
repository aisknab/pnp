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
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const SOURCE = 'lean/PNP/Concrete/CookLevinVerifierTableau.lean';
const AUDIT = 'lean-audit/PNPConcreteCookLevinVerifierTableauAxiomAudit.lean';
const PREFIX = 'PNP.Concrete.CookLevin.';

async function text0(relative) {
  return readFile(path.join(ROOT, relative), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^import\s+([^\s]+)\s*$/gmu)].map((match) => match[1]);
}

function printed0(source) {
  return [...source.matchAll(/^#print axioms\s+([^\s]+)\s*$/gmu)].map((match) => match[1]);
}

function validate0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  const acceptingWitness = stripped.match(
    /def AcceptingWitness[\s\S]*?(?=\n\ntheorem)/u,
  )?.[0] ?? '';
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.CookLevinTableau',
    'PNP.Concrete.PipelineRefinement',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace CookLevin$/mu.test(stripped)
    && /end PNP\.Concrete\s*$/u.test(stripped), 'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasPrivateLeanDeclaration0(source), 'private');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|funext|propext|referenceMinimum)\b/u.test(stripped),
    'shortcut');
  require0(/def inputModeOfVerifier[\s\S]*\| \.inputOnly => \.inputOnly[\s\S]*\| \.paired => \.paired/u.test(stripped),
    'input-mode');
  require0(/def refinement[\s\S]*DecisionProgram\.RawRefinement\.compile problem\.verifier\.program\.decision/u.test(stripped),
    'literal-compiler');
  require0(/theorem verifierEncodedInput_size_le[\s\S]*hCertificate[\s\S]*encodedInputPolynomial/u.test(stripped),
    'encoded-input-bound');
  require0(/def uniformFuel[\s\S]*problem\.rawTimeBound\.eval problem\.encodedInputLimit/u.test(stripped),
    'uniform-fuel');
  require0(/theorem actualFuel_le_uniformFuel[\s\S]*NatPolynomial\.eval_mono/u.test(stripped),
    'fuel-monotonicity');
  require0(/theorem uniformFuel_verdict_eq[\s\S]*boundedDecide_pad_of_halted[\s\S]*problem\.refinement\.verdict_eq/u.test(stripped),
    'exact-padded-verdict');
  require0(/BitString\.size certificate ≤ problem\.certificateLimit[\s\S]*problem\.Accepting certificate tableau/u.test(acceptingWitness),
    'bounded-witness');
  require0(/theorem language_iff_exists_acceptingTableau[\s\S]*language problem\.input ↔[\s\S]*∃ certificate tableau/u.test(stripped),
    'language-equivalence');
  require0(!/CNFFormula|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np/u.test(stripped),
    'boundary-overclaim');
  return failures;
}

test('bounded verifier tableaux are uniform, exact, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel audit covers all 41 explicit verifier-tableau declarations', async () => {
  const [source, audit, root, workflow, packageText, verifierScript] = await Promise.all([
    text0(SOURCE), text0(AUDIT), text0('lean/PNP.lean'),
    text0('.github/workflows/lean-bridge.yml'), text0('package.json'),
    text0('scripts/pnp-verify-all.mjs'),
  ]);
  const declarations = explicitLeanDeclarationHeads0(source);
  const printed = printed0(audit);
  assert.equal(imports0(audit).join(','), 'PNP');
  assert.equal(declarations.length, 41);
  assert.equal(printed.length, declarations.length);
  assert.equal(new Set(printed).size, printed.length);
  assert.ok(printed.every((name) => name.startsWith(PREFIX)));
  assert.ok(imports0(root).includes('PNP.Concrete.CookLevinVerifierTableau'));
  assert.ok(workflow.includes('PNPConcreteCookLevinVerifierTableauAxiomAudit.lean'));
  assert.ok(workflow.includes("grep -Fc 'does not depend on any axioms')\" -eq 41"));
  const packageJson = JSON.parse(packageText);
  assert.ok(packageJson.scripts.test.includes(
    'audits/lean-concrete-cook-levin-verifier-tableau0.test.mjs'));
  assert.ok(verifierScript.includes(
    "'audits/lean-concrete-cook-levin-verifier-tableau0.test.mjs'"));
});

test('mode, certificate-bound, uniform-fuel, and overclaim mutations fail closed', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    source.replace('| .paired => .paired', '| .paired => .inputOnly'),
    source.replace('BitString.size certificate ≤ problem.certificateLimit ∧', 'True ∧'),
    source.replace('problem.rawTimeBound.eval problem.encodedInputLimit',
      'problem.actualFuel []'),
    `${source}\ntheorem cnfSATNPComplete := True\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} changed source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} rejected`);
  }
});

test('verifier-tableau milestone keeps ConcreteSAT and publication fail-closed', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ConcreteSAT'));
});
