import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Frozen after review of the complete arbitrary-dimension implementation.
// These are not computed expectations at test time. Any semantic source edit
// requires explicit review alongside the compiled-type and axiom contracts.
const SPECS = [
  {
    "suffix": "CausalBounds",
    "path": "lean/PNP/NANDWireDescendantCausalBounds.lean",
    "sourceContractSha256": "fe4c02c87fdc2da253920ca6ba19d76e3b00dbf254d557c721ce46ec669b965b",
    "heads": [
      {
        "kind": "theorem",
        "name": "closedHistory_dependencyInterfaceBound"
      },
      {
        "kind": "theorem",
        "name": "StageCompilation.output_dependency_bound"
      },
      {
        "kind": "theorem",
        "name": "CompiledRun.output_dependency_bound"
      },
      {
        "kind": "theorem",
        "name": "CompiledRun.extracted_causalInterfaceBound"
      },
      {
        "kind": "theorem",
        "name": "CompiledRun.extracted_compiles"
      }
    ],
    "reviewedNames": [
      "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_dependencyInterfaceBound",
      "PNP.DirectWire.WireDescendantHistory.StageCompilation.output_dependency_bound",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.output_dependency_bound",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.extracted_causalInterfaceBound",
      "PNP.DirectWire.WireDescendantHistory.CompiledRun.extracted_compiles"
    ],
    "regressionNames": [
      "WireHistoryArbitrarySupport.closedHistory_dependencyInterfaceBound",
      "StageCompilation.output_dependency_bound",
      "CompiledRun.output_dependency_bound",
      "CompiledRun.extracted_causalInterfaceBound",
      "CompiledRun.extracted_compiles"
    ]
  },
  {
    "suffix": "ProperSupport",
    "path": "lean/PNP/NANDWireDescendantProperSupport.lean",
    "sourceContractSha256": "03276dd64475d453cc01e3de3de67245cb6367618056406ecc4aafc1ec156f68",
    "heads": [
      {
        "kind": "def",
        "name": "localSource"
      },
      {
        "kind": "structure",
        "name": "SplicedRun"
      },
      {
        "kind": "theorem",
        "name": "proper_iff_exterior_positive"
      },
      {
        "kind": "def",
        "name": "result"
      },
      {
        "kind": "theorem",
        "name": "open_equivalent"
      },
      {
        "kind": "theorem",
        "name": "output"
      },
      {
        "kind": "theorem",
        "name": "field"
      },
      {
        "kind": "theorem",
        "name": "gateCount"
      },
      {
        "kind": "theorem",
        "name": "charge_accounting"
      },
      {
        "kind": "theorem",
        "name": "gain_iff_local_gain"
      },
      {
        "kind": "theorem",
        "name": "gain_iff_net_charges"
      },
      {
        "kind": "theorem",
        "name": "strictGain"
      },
      {
        "kind": "theorem",
        "name": "strictResidualDescent"
      },
      {
        "kind": "def",
        "name": "compile"
      },
      {
        "kind": "theorem",
        "name": "compile_complete"
      },
      {
        "kind": "theorem",
        "name": "compile_exists_iff"
      },
      {
        "kind": "theorem",
        "name": "compile_none_iff"
      }
    ],
    "reviewedNames": [
      "PNP.DirectWire.WireDescendantProperSupport.proper_iff_exterior_positive",
      "PNP.DirectWire.WireDescendantProperSupport.SplicedRun.open_equivalent",
      "PNP.DirectWire.WireDescendantProperSupport.SplicedRun.output",
      "PNP.DirectWire.WireDescendantProperSupport.SplicedRun.field",
      "PNP.DirectWire.WireDescendantProperSupport.SplicedRun.gateCount",
      "PNP.DirectWire.WireDescendantProperSupport.SplicedRun.charge_accounting",
      "PNP.DirectWire.WireDescendantProperSupport.SplicedRun.gain_iff_local_gain",
      "PNP.DirectWire.WireDescendantProperSupport.SplicedRun.gain_iff_net_charges",
      "PNP.DirectWire.WireDescendantProperSupport.SplicedRun.strictGain",
      "PNP.DirectWire.WireDescendantProperSupport.SplicedRun.strictResidualDescent",
      "PNP.DirectWire.WireDescendantProperSupport.compile_complete",
      "PNP.DirectWire.WireDescendantProperSupport.compile_exists_iff",
      "PNP.DirectWire.WireDescendantProperSupport.compile_none_iff"
    ],
    "regressionNames": [
      "proper_iff_exterior_positive",
      "SplicedRun.open_equivalent",
      "SplicedRun.output",
      "SplicedRun.field",
      "SplicedRun.gateCount",
      "SplicedRun.charge_accounting",
      "SplicedRun.gain_iff_local_gain",
      "SplicedRun.gain_iff_net_charges",
      "SplicedRun.strictGain",
      "SplicedRun.strictResidualDescent",
      "WireDescendantProperSupport.compile_complete",
      "WireDescendantProperSupport.compile_exists_iff",
      "WireDescendantProperSupport.compile_none_iff"
    ]
  },
  {
    "suffix": "Certificate",
    "path": "lean/PNP/NANDWireDescendantCertificate.lean",
    "sourceContractSha256": "484585170bfefb791e354e4f75e5fae6fa7f53a4dd938c81fa2471e1101127f6",
    "heads": [
      {
        "kind": "structure",
        "name": "RawCertificate"
      },
      {
        "kind": "structure",
        "name": "CheckedCertificate"
      },
      {
        "kind": "def",
        "name": "result"
      },
      {
        "kind": "theorem",
        "name": "records_source"
      },
      {
        "kind": "theorem",
        "name": "proper_support"
      },
      {
        "kind": "theorem",
        "name": "output"
      },
      {
        "kind": "theorem",
        "name": "field"
      },
      {
        "kind": "theorem",
        "name": "gateCount"
      },
      {
        "kind": "theorem",
        "name": "charge_accounting"
      },
      {
        "kind": "theorem",
        "name": "strictGain"
      },
      {
        "kind": "theorem",
        "name": "strictResidualDescent"
      },
      {
        "kind": "def",
        "name": "verify"
      },
      {
        "kind": "theorem",
        "name": "verify_complete"
      },
      {
        "kind": "theorem",
        "name": "verify_exists_iff"
      },
      {
        "kind": "theorem",
        "name": "verify_sound"
      },
      {
        "kind": "theorem",
        "name": "verify_decode_none"
      },
      {
        "kind": "theorem",
        "name": "verify_run_none"
      },
      {
        "kind": "theorem",
        "name": "verify_not_proper"
      },
      {
        "kind": "theorem",
        "name": "verify_no_gain"
      }
    ],
    "reviewedNames": [
      "PNP.DirectWire.WireDescendantCertificate.CheckedCertificate.records_source",
      "PNP.DirectWire.WireDescendantCertificate.CheckedCertificate.proper_support",
      "PNP.DirectWire.WireDescendantCertificate.CheckedCertificate.output",
      "PNP.DirectWire.WireDescendantCertificate.CheckedCertificate.field",
      "PNP.DirectWire.WireDescendantCertificate.CheckedCertificate.gateCount",
      "PNP.DirectWire.WireDescendantCertificate.CheckedCertificate.charge_accounting",
      "PNP.DirectWire.WireDescendantCertificate.CheckedCertificate.strictGain",
      "PNP.DirectWire.WireDescendantCertificate.CheckedCertificate.strictResidualDescent",
      "PNP.DirectWire.WireDescendantCertificate.verify_complete",
      "PNP.DirectWire.WireDescendantCertificate.verify_exists_iff",
      "PNP.DirectWire.WireDescendantCertificate.verify_sound",
      "PNP.DirectWire.WireDescendantCertificate.verify_decode_none",
      "PNP.DirectWire.WireDescendantCertificate.verify_run_none",
      "PNP.DirectWire.WireDescendantCertificate.verify_not_proper",
      "PNP.DirectWire.WireDescendantCertificate.verify_no_gain"
    ],
    "regressionNames": [
      "CheckedCertificate.records_source",
      "CheckedCertificate.proper_support",
      "CheckedCertificate.output",
      "CheckedCertificate.field",
      "CheckedCertificate.gateCount",
      "CheckedCertificate.charge_accounting",
      "CheckedCertificate.strictGain",
      "CheckedCertificate.strictResidualDescent",
      "verify_complete",
      "verify_exists_iff",
      "verify_sound",
      "verify_decode_none",
      "verify_run_none",
      "verify_not_proper",
      "verify_no_gain"
    ]
  }
];

const text0 = file => readFile(new URL('../' + file,import.meta.url),'utf8');
const compact0 = source => stripLeanCommentsAndStrings0(source).replace(/\s+/gu,' ').trim();
const digest0 = source => createHash('sha256').update(compact0(source)).digest('hex');
function inspect0(source,spec) {
  const failures=[],clean=compact0(source);
  if(hasLeanAssumptionDeclaration0(source))failures.push('assumption');
  if(hasUnauditedLeanDeclarationForm0(source))failures.push('unaudited-form');
  if(/\b(?:sorry|admit|unsafe|native_decide|noncomputable|Classical|implemented_by|csimp)\b|#(?:eval|reduce|guard|synth)\b/u.test(clean))
    failures.push('shortcut');
  if(JSON.stringify(explicitLeanDeclarationHeads0(source).map(({kind,name})=>({kind,name})))!==
      JSON.stringify(spec.heads))failures.push('closed-declarations');
  if(digest0(source)!==spec.sourceContractSha256)failures.push('reviewed-source-contract');
  return failures;
}
let loaded;
function sources0() {
  loaded??=Promise.all(SPECS.map(async spec=>({spec,source:await text0(spec.path)})));
  return loaded;
}
function mutate0(source,from,to) {
  assert.ok(source.includes(from),'mutation target exists: '+from);
  const changed=source.replace(from,to);
  assert.notEqual(changed,source);
  return changed;
}
async function rejectMutations0(suffix,mutations) {
  const {spec,source}=(await sources0()).find(row=>row.spec.suffix===suffix);
  for(const [label,from,to] of mutations)
    assert.ok(inspect0(mutate0(source,from,to),spec).length>0,label);
}

test('M268 source: reviewed causal, splice and source-only verifier contracts are closed',async()=>{
  assert.deepEqual(SPECS.map(spec=>spec.reviewedNames.length),[5,13,15]);
  const names=SPECS.flatMap(spec=>spec.reviewedNames);
  assert.equal(names.length,33);
  assert.equal(new Set(names).size,33);
  for(const {spec,source} of await sources0())assert.deepEqual(inspect0(source,spec),[],spec.path);
});

test('M268 source: hidden premises, private shortcuts and extra authority reject',async()=>{
  for(const {spec,source} of await sources0()) {
    for(const extra of [
      'axiom hiddenAuthority : True',
      'private axiom hiddenAuthority : True',
      'opaque hiddenAuthority : True',
      'variable (suppliedCorrectness : Prop)',
      'import PNP.Main',
      'unsafe def hiddenAuthority : Nat := 0',
      'private theorem hiddenAuthority : True := by trivial',
      'example : True := by trivial',
      'def hiddenAuthority : Nat := 0',
    ])assert.ok(inspect0(source+'\n'+extra+'\n',spec).length>0,spec.path+': '+extra);
    assert.deepEqual(inspect0(source+'\n/- prose: axiom suppliedCorrectness : True -/\n',spec),[]);
  }
});

test('M268 source: causal bounds cover arbitrary labels and derive actual outer compilation',async()=>{
  await rejectMutations0('CausalBounds',[
    ['arbitrary labels','(labels : Fin inputs → Nat)','(labels : Fin inputs → Nat) (supplied : True)'],
    ['actual stage result','CausalBound.outputLevel compiled.result.candidate labels output ≤',
      'CausalBound.outputLevel source.candidate labels output ≤'],
    ['complete run','induction run with','cases run'],
    ['actual compile witness','∃ compiled, ArbitrarySupportSplice.compile candidate records run.result.candidate =',
      '∃ compiled, ArbitrarySupportSplice.compile candidate records candidate ='],
    ['derived structural bound','(run.extracted_causalInterfaceBound candidate records)','(by assumption)'],
  ]);
});

test('M268 source: proper embedding retains the actual complete program and one-copy exterior',async()=>{
  await rejectMutations0('ProperSupport',[
    ['complete local source','(localSource carrier records) stages with','(localSource carrier records) (stages.take 1) with'],
    ['literal compiler','match compiledAt : ArbitrarySupportSplice.compile carrier.exposed.candidate records',
      'match compiledAt : suppliedCompiler carrier.exposed.candidate records'],
    ['derived acyclicity','run.extracted_compiles carrier.exposed.candidate records','suppliedOuterCompilation'],
    ['proper support','0 < (ArbitrarySupportSplice.exterior records).length','0 ≤ (ArbitrarySupportSplice.exterior records).length'],
    ['one exterior copy','(ArbitrarySupportSplice.exterior records).length + executed.run.result.gateCount',
      '2 * (ArbitrarySupportSplice.exterior records).length + executed.run.result.gateCount'],
  ]);
  await rejectMutations0('ProperSupport',[
    ['historical removals','executed.result.implementation.gateCount + executed.run.removedCount =',
      'executed.result.implementation.gateCount ='],
    ['historical charges','carrier.implementation.gateCount + executed.run.chargedCount :=',
      'carrier.implementation.gateCount :='],
    ['all ordinary outputs','(index : Fin outputs)','(index : Fin 1)'],
    ['all literal fields','(index : Fin fields)','(index : Fin 1)'],
    ['strict final saving','executed.run.chargedCount < executed.run.removedCount',
      'executed.run.chargedCount ≤ executed.run.removedCount'],
  ]);
});

test('M268 source: certificate contains only raw support records and raw stages',async()=>{
  await rejectMutations0('Certificate',[
    ['no supplied implementations','stages : List RawStage','stages : List RawStage\n  suppliedImplementation : Nat'],
    ['no supplied success receipt','stages : List RawStage','stages : List RawStage\n  suppliedCorrectness : Prop'],
    ['complete raw coordinates','(outputs + fields) 0 raw.records with','(outputs + fields) 0 (raw.records.take 1) with'],
    ['all actual observations','(outputs + fields) 0 raw.records with','outputs 0 raw.records with'],
    ['actual complete program','compile carrier records raw.stages with','compile carrier records (raw.stages.take 1) with'],
    ['properness required','if proper : 0 < (ArbitrarySupportSplice.exterior records).length then',
      'if proper : 0 ≤ (ArbitrarySupportSplice.exterior records).length then'],
    ['strict local saving','if smaller : executed.run.result.gateCount <',
      'if smaller : executed.run.result.gateCount ≤'],
    ['complete acceptance','∃ checked, verify carrier raw = some checked','∃ checked, verify carrier raw = none'],
    ['reject failed tail','have impossible := checked.executed.runAt.symm.trans rejected',
      'exact rfl'],
    ['fields not dropped','∀ valuation field, checked.result.fieldValue valuation field =',
      '∀ valuation field, carrier.fieldValue valuation field ='],
    ['derived outer compiler','WireDescendantProperSupport.compile_complete carrier records raw.stages run runAt',
      'suppliedSpliceReceipt'],
  ]);
});

test('M268 preflight: explicit root, audit and regression name families agree exactly',async()=>{
  const root=await text0('lean/PNP.lean');
  const audit=await text0('lean-audit/PNPProperDescendantCertificateAxiomAudit.lean');
  const printed=source=>[...source.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]);
  assert.match(audit,/^import PNP$/mu);
  assert.deepEqual(printed(audit),SPECS.flatMap(spec=>spec.reviewedNames));
  for(const spec of SPECS) {
    assert.ok(root.includes('import PNP.NANDWireDescendant'+spec.suffix));
    const fixture=await text0('lean-regression/PNPWireDescendant'+spec.suffix+'.lean');
    assert.deepEqual(printed(fixture),spec.regressionNames,spec.suffix);
    assert.ok(fixture.startsWith('import PNP.NANDWireDescendant'+spec.suffix+'\n'));
    assert.doesNotMatch(fixture,/\b(?:sorry|admit|native_decide|unsafe)\b|#eval!/u);
  }
});
