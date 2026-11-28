import assert from 'node:assert/strict';
import { readFile, readdir } from 'node:fs/promises';
import { test } from 'node:test';
import { hasLeanAssumptionDeclaration0, stripLeanCommentsAndStrings0 } from './lean-source-declarations0.mjs';

const root = new URL('../', import.meta.url);
const read = path => readFile(new URL(path, root), 'utf8');
const strip = source => stripLeanCommentsAndStrings0(source).replace(/\s+/gu, '');
const fragments = [
  'decodebs=somep↔rangedp=true∧bs=encodep',
  'some(p,[])=>ifrangedp&&decide(encodep=bs)thensomepelsenone',
  'defThreeUseSAT(bs:BitString):Prop:=∃p,decodebs=somep∧restrictedp∧finiteFeasiblep.rows',
  '(List.rangep.width).all(funi=>decide(hitsi(labelsp.rows)=3))',
  'p.rows.all(funr=>decide(r.w.mapProd.fst).Nodup)&&markedBp.rows',
  'defverify(bsw:BitString):Bool:=matchdecodebswith|none=>false|somep=>shapeBp&&decide(w.length=3*p.width)&&p.rows.all(funr=>decide(eval(fun i=>loadVal i w)r.w=r.out))'.replaceAll(' ', ''),
  '(CNFSATbits↔ThreeUseSAT(compilebits))',
  '(compilebits).length≤8000*((bits.length+1)*(bits.length+1))',
  '∃w:BitString,w.length≤144*(bits.length+1)∧verify(compilebits)w=true',
  'f.Satisfied(sourceWordbits(funp=>loadValp.2w))',
];
const missing = text => fragments.filter(f => !text.includes(f));

test('the ordinary proof root reaches the concrete source-free three-use language', async () => {
  const dir = 'lean/PNP/ThreeUse/';
  const names = (await readdir(new URL(dir, root))).filter(n => n.endsWith('.lean'));
  assert.ok(names.includes('Witness.lean'));
  const modules = await Promise.all(names.map(n => read(dir + n)));
  for (const [i, source] of modules.entries()) {
    assert.equal(hasLeanAssumptionDeclaration0(source), false, names[i]);
    assert.doesNotMatch(stripLeanCommentsAndStrings0(source), /\b(sorry|admit|sorryAx|unsafe|native_decide|implemented_by)\b/u);
  }
  assert.match(await read('lean/PNP.lean'), /^import PNP\.ThreeUse\.Witness$/mu);
  const clean = modules.map(strip).join('\n');
  assert.deepEqual(missing(clean), []);
  // Exercise the same source contract after removing the full-word check, third use,
  // witness length, or reverse implication. Compiled fixtures independently test the semantics.
  for (const [index, from, to] of [[1, '(p,[])', '(p,_)'], [3, '=3)', '≤3)'],
    [5, 'w.length=3*p.width', 'w.length≤3*p.width'], [6, '↔', '→']]) {
    const original = fragments[index];
    assert.ok(missing(clean.replaceAll(original, original.replace(from, to))).includes(original));
  }
});
