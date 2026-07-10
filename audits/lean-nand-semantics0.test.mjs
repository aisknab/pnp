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
const SEMANTICS_PATH = 'lean/PNP/NANDSemantics.lean';
const MACROS_PATH = 'lean/PNP/LockedNANDMacros.lean';

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function explicitDeclarations0(source) {
  const directWireStart = source.indexOf('namespace DirectWire');
  assert.notEqual(directWireStart, -1);
  const heads = explicitLeanDeclarationHeads0(source);
  return heads.map((match) => {
    const prefix = match.index < directWireStart ? 'PNP.' : 'PNP.DirectWire.';
    return `${prefix}${match.name}`;
  });
}

function printedAxiomDeclarations0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)].map((match) => match[1]);
}

function validateFoundation0(semantics, macros) {
  const failures = [];
  const require0 = (condition, label) => {
    if (!condition) failures.push(label);
  };

  require0(!/^\s*import\s+/mu.test(semantics), 'foundation-import');
  require0(/namespace PNP\s+[\s\S]*namespace DirectWire/u.test(semantics), 'namespace');
  require0(/^def boolNand \(a b : Bool\) : Bool :=$/mu.test(semantics), 'shared-bool-nand');
  require0(/inductive Source \(inputs gates : Nat\)/u.test(semantics), 'source-type');
  require0(/\| input : Fin inputs → Source inputs gates/u.test(semantics), 'finite-input-source');
  require0(/\| constant : Bool → Source inputs gates/u.test(semantics), 'constant-source');
  require0(/\| gate : Fin gates → Source inputs gates/u.test(semantics), 'finite-earlier-gate-source');
  require0(/inductive Program \(inputs : Nat\) : Nat → Type/u.test(semantics), 'indexed-program');
  require0(/Program inputs gates → Gate inputs gates → Program inputs \(gates \+ 1\)/u.test(semantics), 'topological-snoc');
  require0(/structure DirectWireWord \(inputs gates outputs : Nat\)/u.test(semantics), 'output-word');
  require0(/source : Fin outputs → Source inputs gates/u.test(semantics), 'finite-output-wiring');
  require0(/def Source\.eval/u.test(semantics), 'source-evaluation');
  require0(/def Program\.eval/u.test(semantics), 'program-evaluation');
  require0(/def DirectWireWord\.size/u.test(semantics), 'word-size');
  require0(/def DirectWireWord\.eval/u.test(semantics), 'word-evaluation');
  require0(/def semantics/u.test(semantics), 'open-semantics');
  require0(/def Equivalent/u.test(semantics), 'equivalence');
  require0(/theorem Equivalent\.refl/u.test(semantics), 'equivalence-reflexive');
  require0(/theorem Equivalent\.symm/u.test(semantics), 'equivalence-symmetric');
  require0(/theorem Equivalent\.trans/u.test(semantics), 'equivalence-transitive');
  require0(/theorem Program\.eval_snoc_castSucc/u.test(semantics), 'preserve-earlier-values');
  require0(/theorem Program\.eval_snoc_last/u.test(semantics), 'evaluate-new-gate');
  require0(/projectionWord_spec/u.test(semantics), 'projection-semantics');
  require0(/constantWord_spec/u.test(semantics), 'constant-semantics');
  require0(/def repeatedSourceWord/u.test(semantics), 'generic-repeated-output');
  require0(/repeatedSourceWord_spec/u.test(semantics), 'repeated-output-semantics');
  require0(/repeatedSourceWord_no_added_cost/u.test(semantics), 'repeated-output-cost');
  require0(/nandCircuit_spec/u.test(semantics), 'nand-example');
  require0(/notCircuit_spec/u.test(semantics), 'not-example');
  require0(/andCircuit_spec/u.test(semantics), 'and-example');
  require0(/structure DirectWireSemanticsCertificate : Prop/u.test(semantics), 'certificate-type');
  require0(/def directWireSemanticsCertificate : DirectWireSemanticsCertificate/u.test(semantics), 'certificate-value');
  require0(!hasLeanAssumptionDeclaration0(semantics), 'hidden-declaration');
  require0(!hasPrivateLeanDeclaration0(semantics), 'private-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(semantics), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide)\b/u.test(semantics), 'placeholder');

  require0(/^import PNP\.NANDSemantics$/mu.test(macros), 'macro-import');
  require0(!/^def boolNand\b/mu.test(macros), 'duplicate-bool-nand');

  return failures;
}

test('direct-wire NAND foundation is typed, topological, total, and placeholder-free', async () => {
  assert.deepEqual(validateFoundation0(await text0(SEMANTICS_PATH), await text0(MACROS_PATH)), []);
});

test('root and macro layers use the single foundational NAND definition', async () => {
  const root = await text0('lean/PNP.lean');
  const semantics = await text0(SEMANTICS_PATH);
  const macros = await text0(MACROS_PATH);

  assert.match(root, /^import PNP\.NANDSemantics$/mu);
  assert.equal([...semantics.matchAll(/^def boolNand\b/gmu)].length, 1);
  assert.equal([...macros.matchAll(/^def boolNand\b/gmu)].length, 0);
  assert.equal(macros.includes('boolNand'), true);
});

test('dedicated Lean audit covers every explicit semantics declaration exactly once', async () => {
  const semantics = await text0(SEMANTICS_PATH);
  const audit = await text0('lean-audit/PNPNANDSemanticsAxiomAudit.lean');
  const expected = explicitDeclarations0(semantics);
  const printed = printedAxiomDeclarations0(audit);
  assert.deepEqual(printed, expected);
  assert.equal(new Set(printed).size, printed.length);
  assert.doesNotMatch(audit, /LockedNANDThreshold|final_report_bridge|p_eq_np/u);
});

test('formal status preserves the semantics milestone and broad downstream boundaries', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanNANDDirectWireCoreFormalized, true);
  assert.equal(status.leanNANDDirectWireCoreAxiomAuditPassed, true);
  for (const field of [
    'leanNANDReferenceMinimumPolynomialRuntimeProved',
    'leanCompatibleReplacementFormalized',
    'leanGlobalSlackLawFormalized',
    'leanLockedNANDBuilderFormalized',
    'leanLockedNANDThresholdFormalized',
  ]) assert.equal(status[field], false, field);
  assert.equal(status.remainingBlockers.includes('Formal.LockedNANDThreshold'), true);
  assert.equal(status.projectSpecificAxiomInventory.includes('PNP.LockedNANDThreshold'), true);
  assert.equal(status.rootLeanTheoremPresent, false);
});

test('Lean workflow executes both static and kernel-level semantics audits', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow, /node --test audits\/lean-root-target0\.test\.mjs audits\/lean-nand-semantics0\.test\.mjs/u);
  assert.match(workflow, /lake build PNP/u);
  assert.match(workflow, /lake env lean -DwarningAsError=true lean-audit\/PNPNANDSemanticsAxiomAudit\.lean/u);
  assert.match(workflow, /grep -F 'depends on axioms:'/u);
  assert.match(workflow, /grep -Fc 'does not depend on any axioms'\)" -eq 57/u);
});

test('foundation audit fails closed on untyped references, new dependencies, and duplicate NAND semantics', async () => {
  const semantics = await text0(SEMANTICS_PATH);
  const macros = await text0(MACROS_PATH);

  const untyped = semantics.replace('| gate : Fin gates → Source inputs gates', '| gate : Nat → Source inputs gates');
  assert.equal(validateFoundation0(untyped, macros).includes('finite-earlier-gate-source'), true);

  const dependent = `import PNP.Complexity\n${semantics}`;
  assert.equal(validateFoundation0(dependent, macros).includes('foundation-import'), true);

  const privateAxiom = `${semantics}\nprivate axiom hidden : True\n`;
  assert.equal(validateFoundation0(privateAxiom, macros).includes('hidden-declaration'), true);

  const quotedAxiom = `${semantics}\naxiom «hidden-name» : True\n`;
  assert.equal(validateFoundation0(quotedAxiom, macros).includes('hidden-declaration'), true);

  const unicodeAxiom = `${semantics}\naxiom 隠し : True\n`;
  assert.equal(validateFoundation0(unicodeAxiom, macros).includes('hidden-declaration'), true);

  const privateTheorem = `${semantics}\nprivate theorem hidden_private : True := True.intro\n`;
  assert.equal(validateFoundation0(privateTheorem, macros).includes('private-declaration'), true);

  const unnamedExample = `${semantics}\nexample : True := True.intro\n`;
  assert.equal(validateFoundation0(unnamedExample, macros).includes('unaudited-declaration-form'), true);

  const unlistedTheorem = `${semantics}\ntheorem hidden_propext (a b : Prop) : (a = b) → (a ↔ b) := fun h => h ▸ Iff.rfl\n`;
  assert.notDeepEqual(explicitDeclarations0(unlistedTheorem), printedAxiomDeclarations0(await text0('lean-audit/PNPNANDSemanticsAxiomAudit.lean')));

  const duplicate = `${macros}\n\ndef boolNand (a b : Bool) : Bool := !(a && b)\n`;
  assert.equal(validateFoundation0(semantics, duplicate).includes('duplicate-bool-nand'), true);
});
