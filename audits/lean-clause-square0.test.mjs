import assert from 'node:assert/strict';
import {readFile, readdir} from 'node:fs/promises';
import {test} from 'node:test';
import {hasLeanAssumptionDeclaration0, stripLeanCommentsAndStrings0} from './lean-source-declarations0.mjs';

const root = new URL('../', import.meta.url);
const read = file => readFile(new URL(file, root), 'utf8');
const code = s => stripLeanCommentsAndStrings0(s).replace(/\s+/gu, ' ').trim();
const clauses = [
  ['Framed', 'if h : data.length = (n+1)*d*d then some ⟨n,d,data,h⟩ else none', '= (n+1)*d*d', '≤ (n+1)*d*d'],
  ['Framed', 'def accept (target : BitString) : Bool := match decode target with | none => false | some b => check b', 'decode target', 'decode []'],
  ['Framed', 'a < 2^b.n ∧ ∃ z : Nat, z≠0 ∧ z<2^b.d ∧ product b a z=0', 'product b a z', 'product b 0 z'],
  ['Framed', 'CNFSAT bits ↔ accept (emit bits)=true', '↔', '→'],
  ['Raw', 'def compile (source : BitString) : Raw := parsed (decodeEncodedCNF source)', 'decodeEncodedCNF source', 'none'],
  ['Raw', '| none => ⟨0,1,[[constant 0]]⟩', '[[constant 0]]', '[[]]'],
  ['Packed', '∃ z : Nat, z≠0 ∧ z<2^s.d ∧ action s x z=0', 'z≠0 ∧ ', ''],
  ['Packed', '∃ z : Nat, z≠0 ∧ z<2^s.d ∧ action s x z=0', 'z<2^s.d', 'z≤2^s.d'],
  ['Packed', 'xorSelected s.d (chosen s x) z.testBit', 'z.testBit', '(fun _ => true)'],
  ['Numbered', 'a<2^s.n ∧ MaskWitness s (numberedHead s.n a)', 'a<2^s.n', 'a≤2^s.n'],
  ['Numbered', 'CNFSAT bits ↔ ∃ a : Nat, NumberedKernel (compile bits) a', 'CNFSAT bits ↔', 'CNFSAT bits →'],
  ['Numbered', 'readWord (compile bits).n (numberedHead (compile bits).n a)=w', '=w', '≠w'],
];

test('the physical affine square keeps the original word, both widths and the nonzero kernel', async () => {
  for (const [mod, fragment, old, mutant] of clauses) {
    const s = code(await read('lean/PNP/ClauseSquare/' + mod + '.lean'));
    assert.ok(s.includes(fragment), mod + ': ' + fragment);
    const original = fragment.replace(old, mutant);
    assert.notEqual(original, fragment);
    assert.ok(!s.replaceAll(fragment, original).includes(fragment), mod);
  }
});

test('the ordinary proof root reaches the affine square without project assumptions', async () => {
  const sub = 'lean/PNP/ClauseSquare/';
  const modules = (await readdir(new URL(sub, root))).filter(f => f.endsWith('.lean'));
  assert.ok(modules.includes('Numbered.lean') && modules.includes('Packed.lean'));
  for (const file of modules) {
    const s = await read(sub + file);
    assert.ok(!hasLeanAssumptionDeclaration0(s), file);
    assert.doesNotMatch(stripLeanCommentsAndStrings0(s), /\b(sorry|admit|sorryAx|unsafe|native_decide|implemented_by)\b/u);
  }
  assert.match(await read('lean/PNP.lean'), /^import PNP\.ClauseSquare\.Framed$/mu);
  assert.match(await read('lean-audit/PNPClauseSquareAxiomAudit.lean'), /getModuleIdxFor\? n/u);
});
