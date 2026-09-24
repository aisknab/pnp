import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {CheckLeanAuditPath0,CheckLeanAxiomTranscript0} from '../scripts/check-lean-axioms.mjs';

const source='import PNP\n#print axioms PNP.Fixture.first\n#print axioms PNP.Fixture.second\n';
const inventory=[
  {name:'PNP.Fixture.first',kind:'theorem',axioms:['Quot.sound','propext']},
  {name:'PNP.Fixture.second',kind:'theorem',axioms:[]},
];
const transcript="'PNP.Fixture.first' depends on axioms: [propext,\n Quot.sound]\n"+
  "'PNP.Fixture.second' does not depend on any axioms\n";

test('shared Lean axiom check preserves exact names and complete compiled closures',()=>{
  assert.deepEqual(CheckLeanAxiomTranscript0(transcript,source,inventory),
    ['PNP.Fixture.first','PNP.Fixture.second']);
  assert.deepEqual(CheckLeanAxiomTranscript0(transcript.replaceAll('\n','\r\n'),source,inventory),
    ['PNP.Fixture.first','PNP.Fixture.second']);
});

test('shared Lean axiom check rejects omitted, extra and duplicate transcript declarations',()=>{
  for(const output of [
    transcript.split("'PNP.Fixture.second'")[0],
    transcript+"'PNP.Fixture.extra' does not depend on any axioms\n",
    transcript+"'PNP.Fixture.second' does not depend on any axioms\n",
    transcript.replace('PNP.Fixture.first','PNP.Fixture.renamed'),
  ])assert.throws(()=>CheckLeanAxiomTranscript0(output,source,inventory),
    /printed theorem set differs/u);
});

test('shared Lean axiom check rejects changed, missing or invented axiom closures',()=>{
  for(const output of [
    transcript.replace('propext,\n Quot.sound','propext'),
    transcript.replace('propext,\n Quot.sound','propext, Quot.sound, Classical.choice'),
    transcript.replace('propext,\n Quot.sound','propext, Quot.sound, PNP.Fixture.assumption'),
    transcript.replace("depends on axioms: [propext,\n Quot.sound]","does not depend on any axioms"),
    transcript.replace("does not depend on any axioms","depends on axioms: [propext]"),
  ])assert.throws(()=>CheckLeanAxiomTranscript0(output,source,inventory));
});

test('shared Lean axiom check requires unique theorem declarations from the compiled inventory',()=>{
  assert.throws(()=>CheckLeanAxiomTranscript0(transcript,source,[]),/missing or duplicate/u);
  assert.throws(()=>CheckLeanAxiomTranscript0(transcript,source,[...inventory,inventory[0]]),
    /missing or duplicate/u);
  const definition=structuredClone(inventory);definition[0].kind='definition';
  assert.throws(()=>CheckLeanAxiomTranscript0(transcript,source,definition));
  const missing=structuredClone(inventory);delete missing[0].axioms;
  assert.throws(()=>CheckLeanAxiomTranscript0(transcript,source,missing),/missing compiled axiom/u);
  const malformed=structuredClone(inventory);malformed[0].axioms=[1];
  assert.throws(()=>CheckLeanAxiomTranscript0(transcript,source,malformed));
});

test('shared Lean axiom check rejects empty or duplicate audit lists and stray diagnostics',()=>{
  assert.throws(()=>CheckLeanAxiomTranscript0('',"import PNP\n",inventory),/at least one/u);
  assert.throws(()=>CheckLeanAxiomTranscript0(transcript,
    source+'#print axioms PNP.Fixture.first\n',inventory),/duplicate audit theorem/u);
  assert.throws(()=>CheckLeanAxiomTranscript0(transcript+'unexpected diagnostic\n',source,inventory),
    /unclassified/u);
  assert.throws(()=>CheckLeanAxiomTranscript0(transcript+'error: unchecked axiom\n',source,inventory),
    /unclassified/u);
});

test('shared Lean axiom command accepts only a repository audit path',()=>{
  assert.equal(CheckLeanAuditPath0('lean-audit/PNPComputedR7HistoryAxiomAudit.lean'),
    'lean-audit/PNPComputedR7HistoryAxiomAudit.lean');
  for(const path of ['../audit.lean','/tmp/audit.lean','lean/PNP/Main.lean',
    'lean-audit/PNPBadAxiomAudit.lean; echo x','lean-audit/../PNPBadAxiomAudit.lean'])
    assert.throws(()=>CheckLeanAuditPath0(path));
});

test('shared Lean axiom runner retains warning errors, bounded execution and no duplicate root build',async()=>{
  const runner=await readFile(new URL('../scripts/check-lean-axioms.mjs',import.meta.url),'utf8');
  for(const fragment of [
    "spawnSync('lake',['env','lean','-DwarningAsError=true',audit]",
    'timeout:600_000,maxBuffer:4*1024*1024',
    "assert.equal(result.status,0","assert.equal(result.stderr,''",
    "'status/LEAN_THEOREM_INVENTORY.json'",'.declarations',
  ])assert.ok(runner.includes(fragment),fragment);
  assert.doesNotMatch(runner,/['"]build['"]|shell\s*:\s*true/u);
});
