import assert from 'node:assert/strict';
import {readFile, readdir} from 'node:fs/promises';
import {test} from 'node:test';
import {hasLeanAssumptionDeclaration0, stripLeanCommentsAndStrings0} from './lean-source-declarations0.mjs';

const base = new URL('../lean/PNP/SignedTernary/', import.meta.url);
const text = file => readFile(new URL(file, base), 'utf8');
const plain = value => stripLeanCommentsAndStrings0(value).replace(/\s+/gu, ' ').trim();

function contract(source) {
  const s = plain(source);
  return [
    'def SignedSolution (n : Nat) (A : Rows n n) : Prop := ∃ x : Vec n, Signed x ∧ Signed (applyRows A x)',
    'def MatrixSAT (bytes : BitString) : Prop := ∃ A : PNP.SignedTernary.Codec.Square, PNP.SignedTernary.Codec.unpack bytes = some A ∧ SignedSolution A.1 A.2',
    'theorem matrixSAT_encodeCNFMatrix_iff (raw : BitString) : MatrixSAT (encodeCNFMatrix raw) ↔ CNFSAT raw',
  ].every(line => s.includes(line));
}

async function modules(dir = base) {
  const files = [];
  for (const entry of await readdir(dir, {withFileTypes: true})) {
    assert.ok(!entry.isSymbolicLink(), entry.name);
    if (entry.isDirectory()) files.push(...await modules(new URL(entry.name + '/', dir)));
    else if (entry.isFile() && entry.name.endsWith('.lean')) files.push(new URL(entry.name, dir));
  }
  return files;
}

test('signed matrix target parses the actual word and uses one signed input for both sides', async () => {
  const s = await text('Encoding.lean');
  assert.ok(contract(s));
  for (const [before, after] of [
    ['∃ x : Vec n, Signed x ∧ Signed (applyRows A x)', '∃ x y : Vec n, Signed x ∧ Signed (applyRows A y)'],
    ['Signed x ∧ Signed (applyRows A x)', 'Signed x'],
    ['unpack bytes = some A', 'unpack [] = some A'],
    ['MatrixSAT (encodeCNFMatrix raw) ↔ CNFSAT raw', 'CNFSAT raw → MatrixSAT (encodeCNFMatrix raw)'],
    ['(raw : BitString) : MatrixSAT', '(raw : BitString) (valid : CNFSAT raw) : MatrixSAT'],
  ]) {
    assert.ok(s.includes(before), before);
    assert.ok(!contract(s.replace(before, after)), before);
  }
});

test('the target is imported by the ordinary proof root without using a result about P versus NP', async () => {
  const root = await readFile(new URL('../lean/PNP.lean', import.meta.url), 'utf8');
  assert.match(root, /^import PNP\.SignedTernary\.Encoding$/mu);
  const files = await modules();
  const external = new Set();
  for (const file of files) {
    const source = await readFile(file, 'utf8');
    const code = stripLeanCommentsAndStrings0(source);
    assert.ok(!hasLeanAssumptionDeclaration0(source), file.pathname.split('/').pop());
    assert.doesNotMatch(code, /\b(sorry|admit|sorryAx|unsafe|native_decide|implemented_by)\b/u);
    for (const [, line] of code.matchAll(/^import[ \t]+([^\n]+)/gmu)) {
      for (const name of line.trim().split(/\s+/u)) {
        if (!name.startsWith('PNP.SignedTernary.')) external.add(name);
      }
    }
  }
  assert.deepEqual([...external].sort(), ['PNP.Concrete.CNF', 'PNP.Concrete.CNFDecoderGrammar', 'Std']);
});
