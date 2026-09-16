#!/usr/bin/env node

import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {readFileSync} from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import {pathToFileURL} from 'node:url';

/**
 * Match every printed theorem's complete axiom closure to the compiled
 * inventory. This is orchestration, not theorem authority or a second build.
 */
export function CheckLeanAxiomTranscript0(output,auditSource,inventory) {
  assert.equal(typeof output,'string','Lean transcript must be text');
  assert.equal(typeof auditSource,'string','Lean audit source must be text');
  assert.ok(Array.isArray(inventory),'compiled milestone inventory is required');
  const names=[...auditSource.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)]
    .map(match=>match[1]);
  assert.ok(names.length>0,'audit must print at least one exact theorem');
  assert.equal(new Set(names).size,names.length,'duplicate audit theorem');
  const expected=names.map(name=>{
    const matching=inventory.filter(row=>row.name===name);
    assert.equal(matching.length,1,'missing or duplicate compiled theorem: '+name);
    const row=matching[0];
    assert.equal(row.kind,'theorem',name);
    assert.ok(Array.isArray(row.axioms),'missing compiled axiom closure: '+name);
    assert.ok(row.axioms.every(value=>typeof value==='string'),name);
    return [name,row.axioms];
  });
  const normalized=output.replace(/\r\n/gu,'\n').replace(/\n[ \t]+/gu,' ');
  const pattern=/^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$/gmu;
  const rows=[...normalized.matchAll(pattern)];
  assert.deepEqual(rows.map(row=>row[1]).sort(),names.slice().sort(),
    'printed theorem set differs from the audit');
  assert.equal(normalized.replace(pattern,'').trim(),'',
    'unclassified Lean audit output');
  const expectedAxioms=new Map(expected);
  for(const row of rows) {
    const actual=row[2]===undefined?[]:row[2].split(',').map(value=>value.trim()).sort();
    assert.deepEqual(actual,expectedAxioms.get(row[1]),row[1]);
  }
  return names;
}

export function CheckLeanAuditPath0(value) {
  assert.equal(typeof value,'string','audit path must be text');
  assert.match(value,/^lean-audit\/PNP[A-Za-z0-9]+AxiomAudit\.lean$/u,
    'expected a repository Lean axiom audit');
  return value;
}

function main0(args) {
  assert.equal(args.length,1,'Usage: node scripts/check-lean-axioms.mjs lean-audit/PNP...AxiomAudit.lean');
  const audit=CheckLeanAuditPath0(args[0]);
  const auditSource=readFileSync(audit,'utf8');
  const inventory=JSON.parse(readFileSync('status/LEAN_THEOREM_INVENTORY.json','utf8'))
    .milestoneCandidates;
  const result=spawnSync('lake',['env','lean','-DwarningAsError=true',audit],{
    cwd:process.cwd(),encoding:'utf8',timeout:600_000,maxBuffer:4*1024*1024,
  });
  if(result.stdout)process.stdout.write(result.stdout);
  if(result.stderr)process.stderr.write(result.stderr);
  assert.equal(result.error,undefined,'Lean audit could not complete');
  assert.equal(result.signal,null,'Lean audit terminated by signal');
  assert.equal(result.status,0,'Lean audit exited unsuccessfully');
  assert.equal(result.stderr,'','Lean audit emitted stderr');
  const names=CheckLeanAxiomTranscript0(result.stdout,auditSource,inventory);
  console.log('lean-axiom-transcript-valid: '+names.length+' exact declarations');
}

if(process.argv[1]&&import.meta.url===pathToFileURL(path.resolve(process.argv[1])).href) {
  try {main0(process.argv.slice(2));}
  catch(error) {console.error(error.message);process.exitCode=1;}
}
