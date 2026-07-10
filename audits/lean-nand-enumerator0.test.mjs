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
const ENUMERATOR_PATH = 'lean/PNP/NANDEnumerator.lean';

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function explicitDeclarations0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map((head) => `PNP.DirectWire.${head.name}`);
}

function printedAxiomDeclarations0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)].map((match) => match[1]);
}

function validateEnumerator0(source) {
  const failures = [];
  const require0 = (condition, label) => {
    if (!condition) failures.push(label);
  };

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)].map((match) => match[1]);
  require0(JSON.stringify(imports) === JSON.stringify(['PNP.NANDSemantics']), 'foundation-import');
  require0(/namespace PNP\s+[\s\S]*namespace DirectWire/u.test(source), 'namespace');
  require0(/def allFin\b/u.test(source), 'fin-enumerator');
  require0(/theorem mem_allFin\b/u.test(source), 'fin-completeness');
  require0(/def allSources\b/u.test(source), 'source-enumerator');
  require0(/theorem mem_allSources\b/u.test(source), 'source-completeness');
  require0(/def allGates\b[\s\S]*flatMap[\s\S]*\.map/u.test(source), 'ordered-gate-enumerator');
  require0(/theorem mem_allGates\b/u.test(source), 'gate-completeness');
  require0(/def allPrograms\b/u.test(source), 'program-enumerator');
  require0(/theorem mem_allPrograms\b/u.test(source), 'program-completeness');
  require0(/inductive OutputWord \(inputs gates : Nat\) : Nat → Type/u.test(source), 'output-word');
  require0(/\| nil : OutputWord inputs gates 0/u.test(source), 'empty-output-word');
  require0(/def allOutputWords\b/u.test(source), 'output-enumerator');
  require0(/theorem mem_allOutputWords\b/u.test(source), 'output-completeness');
  require0(/theorem OutputWord\.eq_nil\b/u.test(source), 'unique-empty-output');
  require0(/def OutputWord\.ofFn\b/u.test(source), 'function-reification');
  require0(/theorem OutputWord\.get_ofFn\b/u.test(source), 'pointwise-reification');
  require0(/structure Candidate \(inputs gates outputs : Nat\)/u.test(source), 'candidate-type');
  require0(/def allCandidates\b/u.test(source), 'candidate-enumerator');
  require0(/theorem mem_allCandidates\b/u.test(source), 'candidate-completeness');
  require0(/theorem exactWidthEnumeration_complete\b/u.test(source), 'direct-interface-completeness');
  require0(/∀ output, candidate\.directWireWord\.source output = word\.source output/u.test(source), 'pointwise-direct-interface');
  require0(/abbrev BoundedCandidate\b/u.test(source), 'bounded-candidate');
  require0(/def allBoundedCandidates\b/u.test(source), 'bounded-enumerator');
  require0(/theorem mem_allBoundedCandidates_of_le\b/u.test(source), 'bounded-completeness');
  require0(/structure NANDEnumeratorCertificate : Prop/u.test(source), 'certificate-type');
  require0(/def nandEnumeratorCertificate : NANDEnumeratorCertificate/u.test(source), 'certificate-value');

  require0(!/\bList\.(?:finRange|mem_finRange|mem_map|mem_flatMap)\b/u.test(source), 'axiom-carrying-list-helper');
  require0(!/\b(?:funext|Classical|native_decide|sorry|admit)\b/u.test(source), 'forbidden-proof-shortcut');
  require0(!hasLeanAssumptionDeclaration0(source), 'hidden-declaration');
  require0(!hasPrivateLeanDeclaration0(source), 'private-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');

  return failures;
}

test('exact-width NAND enumerator is constructive, ordered, and complete', async () => {
  assert.deepEqual(validateEnumerator0(await text0(ENUMERATOR_PATH)), []);
});

test('enumerator reifies the PR4 function-backed interface pointwise', async () => {
  const source = await text0(ENUMERATOR_PATH);
  assert.match(source, /def Candidate\.ofDirectWireWord/u);
  assert.match(source, /Candidate\.ofDirectWireWord_pointwise/u);
  assert.match(source, /exactWidthEnumeration_complete/u);
  assert.doesNotMatch(source, /funext/u);
});

test('zero outputs are unique and NAND input pairs remain ordered', async () => {
  const source = await text0(ENUMERATOR_PATH);
  assert.match(source, /\| 0 => \[\.nil\]/u);
  assert.match(source, /theorem OutputWord\.eq_nil/u);
  assert.match(source, /allSources inputs priorGates\)\.flatMap fun left/u);
  assert.match(source, /allSources inputs priorGates\)\.map fun right/u);
  assert.match(source, /makes no commutativity quotient/u);
  assert.doesNotMatch(source, /^(?:def|theorem)\s+(?:canonicalGate|normalizeGate)\b/mu);
});

test('bounded enumeration exposes every exact candidate within its gate bound', async () => {
  const source = await text0(ENUMERATOR_PATH);
  assert.match(source, /Sigma fun gateCount : Fin \(gateBound \+ 1\)/u);
  assert.match(source, /def boundedCandidateOfLE/u);
  assert.match(source, /Nat\.lt_succ_of_le/u);
  assert.match(source, /mem_allBoundedCandidates_of_le/u);
});

test('enumerator axiom audit covers every explicit declaration exactly once', async () => {
  const source = await text0(ENUMERATOR_PATH);
  const audit = await text0('lean-audit/PNPNANDEnumeratorAxiomAudit.lean');
  const expected = explicitDeclarations0(source);
  const printed = printedAxiomDeclarations0(audit);
  assert.deepEqual(printed, expected);
  assert.equal(new Set(printed).size, printed.length);
  assert.doesNotMatch(audit, /LockedNANDThreshold|minimum|slack|p_eq_np/iu);
});

test('formal status earns enumeration only and retains every downstream boundary', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanNANDEnumeratorFormalized, true);
  assert.equal(status.leanNANDEnumeratorAxiomAuditPassed, true);
  assert.equal(status.leanNANDExactWidthEnumerationComplete, true);
  assert.equal(status.leanNANDEnumeratorUsesOrderedGatePairs, true);
  assert.equal(status.leanNANDEnumeratorIncludesUniqueEmptyOutputTuple, true);
  assert.equal(status.leanNANDEnumeratorDeduplicated, false);
  assert.equal(status.leanNANDSemanticEquivalenceDecidable, false);
  for (const field of [
    'leanNANDMinimumAndSlackFormalized',
    'leanCompatibleReplacementFormalized',
    'leanGlobalSlackLawFormalized',
    'leanLockedNANDBuilderFormalized',
    'leanLockedNANDThresholdFormalized',
  ]) assert.equal(status[field], false, field);
  assert.equal(status.remainingBlockers.includes('Formal.LockedNANDThreshold'), true);
  assert.equal(status.rootLeanTheoremPresent, false);
});

test('workflow fails closed on any enumerator axiom or incomplete transcript', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow, /node --test audits\/lean-root-target0\.test\.mjs audits\/lean-nand-semantics0\.test\.mjs audits\/lean-nand-enumerator0\.test\.mjs/u);
  assert.match(workflow, /lean-audit\/PNPNANDEnumeratorAxiomAudit\.lean/u);
  assert.match(workflow, /Exact-width NAND enumerator unexpectedly depends on axioms/u);
  assert.match(workflow, /grep -Fc 'does not depend on any axioms'\)" -eq 41/u);
});

test('enumerator audit rejects dependency, axiom, library-shortcut, and coverage regressions', async () => {
  const source = await text0(ENUMERATOR_PATH);

  assert.equal(validateEnumerator0(`import PNP.Complexity\n${source}`).includes('foundation-import'), true);
  assert.equal(validateEnumerator0(`${source}\nprivate axiom hidden : True\n`).includes('hidden-declaration'), true);
  assert.equal(validateEnumerator0(`${source}\naxiom «hidden-name» : True\n`).includes('hidden-declaration'), true);
  assert.equal(validateEnumerator0(`${source}\naxiom 隠し : True\n`).includes('hidden-declaration'), true);
  assert.equal(validateEnumerator0(`${source}\nprivate theorem hidden_private : True := True.intro\n`).includes('private-declaration'), true);
  assert.equal(validateEnumerator0(`${source}\nexample : True := True.intro\n`).includes('unaudited-declaration-form'), true);
  assert.equal(validateEnumerator0(source.replace('def allFin', 'def hidden := List.finRange\n\ndef allFin')).includes('axiom-carrying-list-helper'), true);
  assert.equal(validateEnumerator0(source.replace('theorem exactWidthEnumeration_complete', 'theorem exactWidthEnumeration_removed')).includes('direct-interface-completeness'), true);

  const audit = await text0('lean-audit/PNPNANDEnumeratorAxiomAudit.lean');
  const printed = printedAxiomDeclarations0(audit);
  const unlisted = `${source}\ntheorem hidden_propext (a b : Prop) : (a = b) → (a ↔ b) := fun h => h ▸ Iff.rfl\n`;
  assert.notDeepEqual(explicitDeclarations0(unlisted), printed);
  assert.notDeepEqual([...printed, printed.at(-1)], explicitDeclarations0(source));
  assert.notDeepEqual(printed.slice(0, -1), explicitDeclarations0(source));
});
