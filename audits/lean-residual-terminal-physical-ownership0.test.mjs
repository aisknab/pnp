import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';
import {
  DeriveFormalPublication0, MilestoneTheoremKernelTypeSha2560,
  REQUIRED_MILESTONE_THEOREMS0, stableStringify0,
} from '../formal-publication0.mjs';
import { validateProofProgress0 } from '../pcc-proof-progress0.mjs';

const SOURCE = 'lean/PNP/ResidualTerminalPhysicalOwnership.lean';
const AUDIT = 'lean-audit/PNPResidualTerminalPhysicalOwnershipAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPResidualTerminalPhysicalOwnership.lean';
const NAMES = [
  "terminalPhysicalOwner_none_iff",
  "terminalPhysicalOwner_first",
  "terminalOwnedPhysicalGates_partition",
  "terminalOwnedPhysicalGates_disjoint",
  "terminalOwnedPhysicalGates_restrict",
  "terminalOwnedPhysicalMaterializer_gateCount",
  "terminalOwnedPhysicalMaterializer_chargeIdentity",
  "terminalOwnedPhysicalMaterializer_semantics",
  "terminalOwnedPhysicalMaterializer_induced",
  "terminalOwnedPhysicalMaterializer_wholeCharge"
];
const SIGNATURES = [
  "theorem terminalPhysicalOwner_none_iff {gates ownerCount : Nat} (requests : Fin ownerCount → List (Fin gates)) (gate : Fin gates) : terminalPhysicalOwner requests gate = none ↔ ∀ owner, gate ∉ requests owner",
  "theorem terminalPhysicalOwner_first {gates ownerCount : Nat} (requests : Fin ownerCount → List (Fin gates)) (gate : Fin gates) (owner : Fin ownerCount) (assigned : terminalPhysicalOwner requests gate = some owner) : gate ∈ requests owner ∧ ∃ earlier later, allFin ownerCount = earlier ++ owner :: later ∧ ∀ previous, previous ∈ earlier → gate ∉ requests previous",
  "theorem terminalOwnedPhysicalGates_partition {inputs gates outputs profileWidth ownerCount : Nat} (requests : Fin ownerCount → List (Fin gates)) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (owner : Option (Fin ownerCount)) (gate : Fin gates) : gate ∈ terminalOwnedPhysicalGates requests records owner ↔ gate ∈ terminalSelectedGates records ∧ terminalPhysicalOwner requests gate = owner",
  "theorem terminalOwnedPhysicalGates_disjoint {inputs gates outputs profileWidth ownerCount : Nat} (requests : Fin ownerCount → List (Fin gates)) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (left right : Option (Fin ownerCount)) (different : left ≠ right) (gate : Fin gates) (inLeft : gate ∈ terminalOwnedPhysicalGates requests records left) : gate ∉ terminalOwnedPhysicalGates requests records right",
  "theorem terminalOwnedPhysicalGates_restrict {inputs gates outputs profileWidth ownerCount : Nat} (requests : Fin ownerCount → List (Fin gates)) (larger smaller : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (included : ∀ gate, gate ∈ terminalSelectedGates smaller → gate ∈ terminalSelectedGates larger) (owner : Option (Fin ownerCount)) (gate : Fin gates) (member : gate ∈ terminalOwnedPhysicalGates requests smaller owner) : gate ∈ terminalOwnedPhysicalGates requests larger owner",
  "theorem terminalOwnedPhysicalMaterializer_gateCount {inputs gates outputs profileWidth ownerCount : Nat} (candidate : Candidate inputs gates outputs) (requests : Fin ownerCount → List (Fin gates)) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (owner : Option (Fin ownerCount)) : (terminalOwnedPhysicalMaterializer candidate requests records owner).gateCount = (terminalOwnedPhysicalGates requests records owner).length",
  "theorem terminalOwnedPhysicalMaterializer_chargeIdentity {inputs gates outputs profileWidth ownerCount : Nat} (candidate : Candidate inputs gates outputs) (requests : Fin ownerCount → List (Fin gates)) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) : ((terminalPhysicalOwners ownerCount).map (fun owner => (terminalOwnedPhysicalMaterializer candidate requests records owner).gateCount)).sum = (extractTerminalSupport candidate records).gateCount",
  "theorem terminalOwnedPhysicalMaterializer_semantics {inputs gates outputs profileWidth ownerCount : Nat} (candidate : Candidate inputs gates outputs) (requests : Fin ownerCount → List (Fin gates)) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (owner : Option (Fin ownerCount)) (boundaryValuation : Valuation (terminalBoundaryPorts candidate.program (terminalOwnedPhysicalRecords requests records owner)).length) (output : Fin (terminalInterfacePorts candidate (terminalOwnedPhysicalRecords requests records owner)).length) : (terminalOwnedPhysicalMaterializer candidate requests records owner).extractedCandidate.semantics boundaryValuation output = terminalOpenSupportSemantics candidate (terminalOwnedPhysicalRecords requests records owner) boundaryValuation output",
  "theorem terminalOwnedPhysicalMaterializer_induced {inputs gates outputs profileWidth ownerCount : Nat} (candidate : Candidate inputs gates outputs) (requests : Fin ownerCount → List (Fin gates)) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (owner : Option (Fin ownerCount)) (input : Valuation inputs) (output : Fin (terminalInterfacePorts candidate (terminalOwnedPhysicalRecords requests records owner)).length) : (terminalOwnedPhysicalMaterializer candidate requests records owner).extractedCandidate.semantics (terminalInducedBoundaryValuation candidate (terminalOwnedPhysicalRecords requests records owner) input) output = candidate.program.eval input ((terminalInterfacePorts candidate (terminalOwnedPhysicalRecords requests records owner)).get output)",
  "theorem terminalOwnedPhysicalMaterializer_wholeCharge {inputs gates outputs profileWidth ownerCount : Nat} (candidate : Candidate inputs gates outputs) (requests : Fin ownerCount → List (Fin gates)) : ((terminalPhysicalOwners ownerCount).map (fun owner => (terminalOwnedPhysicalMaterializer candidate requests ((allFin gates).map (TerminalPrimitiveRecord.gate (profileWidth"
];
const PUBLIC_HEADS = [
  "terminalPhysicalOwner",
  "terminalPhysicalOwners",
  "terminalOwnedPhysicalGates",
  "terminalOwnedPhysicalRecords",
  "terminalOwnedPhysicalMaterializer",
  "terminalPhysicalOwner_none_iff",
  "terminalPhysicalOwner_first",
  "terminalOwnedPhysicalGates_partition",
  "terminalOwnedPhysicalGates_disjoint",
  "terminalOwnedPhysicalGates_restrict",
  "terminalOwnedPhysicalMaterializer_gateCount",
  "terminalOwnedPhysicalMaterializer_chargeIdentity",
  "terminalOwnedPhysicalMaterializer_semantics",
  "terminalOwnedPhysicalMaterializer_induced",
  "terminalOwnedPhysicalMaterializer_wholeCharge"
];

const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = value => stripLeanCommentsAndStrings0(value).replace(/\s+/gu, ' ').trim();
function block0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex(head => head.name === name);
  return index < 0 ? '' : source.slice(heads[index].index, heads[index + 1]?.index ?? source.length);
}
function validateSource0(source) {
  const failures = [];
  const require0 = (condition, category) => { if (!condition) failures.push(category); };
  const clean = compact0(source);
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|callerCertificate|suppliedWeight)\b/u
    .test(clean), 'shortcut-or-certificate');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]))
    === JSON.stringify(['PNP.DirectWireBaseline','PNP.ResidualTerminalSupportExtraction']), 'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head => head.name)) ===
    JSON.stringify(PUBLIC_HEADS), 'public-interface');
  for (const [index,name] of NAMES.entries())
    require0(compact0(block0(source,name)).startsWith(SIGNATURES[index] + ' := '),
      'signature:' + name);
  const owner = compact0(block0(source,'terminalPhysicalOwner'));
  require0(owner.includes('(requests : Fin ownerCount → List (Fin gates)) (gate : Fin gates) : Option (Fin ownerCount) :='),
    'support-independent-inputs');
  require0(owner.includes('(allFin ownerCount).find? fun owner => decide (gate ∈ requests owner)'),
    'computed-first-requester');
  require0(compact0(block0(source,'terminalPhysicalOwners')).includes(
    'none :: (allFin ownerCount).map some'), 'fixed-remainder');
  require0(compact0(block0(source,'terminalOwnedPhysicalGates')).includes(
    '(terminalSelectedGates records).filter fun gate => decide (terminalPhysicalOwner requests gate = owner)'),
    'computed-owned-gates');
  require0(compact0(block0(source,'terminalOwnedPhysicalRecords')).includes(
    '(terminalOwnedPhysicalGates requests records owner).map TerminalPrimitiveRecord.gate'),
    'physical-records-only');
  require0(compact0(block0(source,'terminalOwnedPhysicalMaterializer')).includes(
    'extractTerminalSupport candidate (terminalOwnedPhysicalRecords requests records owner)'),
    'actual-extracted-materializer');
  const count = compact0(block0(source,'terminalOwnedPhysicalMaterializer_gateCount'));
  for (const token of ['extractTerminalSupport_gateCount','ownership_selected_gate_records_length',
    'terminalSelectedGates_nodup records'])
    require0(count.includes(token), 'computed-physical-weight');
  const identity = compact0(block0(source,'terminalOwnedPhysicalMaterializer_chargeIdentity'));
  for (const token of ['terminalOwnedPhysicalMaterializer_gateCount candidate requests records owner',
    'extractTerminalSupport_gateCount','ownership_partition_length (terminalPhysicalOwners ownerCount)',
    'ownership_all_owners_distinct ownerCount','terminalPhysicalOwner requests',
    'ownership_all_owners_member'])
    require0(identity.includes(token), 'complete-exact-partition');
  for (const [name,dependency] of [
    ['terminalOwnedPhysicalMaterializer_semantics','extractTerminalSupport_semantics'],
    ['terminalOwnedPhysicalMaterializer_induced','extractTerminalSupport_induced'],
  ]) require0(compact0(block0(source,name)).includes(dependency+' candidate'),
    'actual-open-semantics');
  return [...new Set(failures)];
}

test('M241 derives support-independent physical ownership and all ten general materializer laws', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE)), []);
});

test('M241 explicit root, axiom audit and reviewed-name producers agree', async () => {
  const [source,audit,inventorySource,root] = await Promise.all([
    text0(SOURCE),text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean'),
  ]);
  for (const name of NAMES) {
    assert.equal(explicitLeanDeclarationHeads0(source).filter(head => head.name === name).length,1);
    const fullName = 'PNP.DirectWire.' + name;
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item => item === fullName).length,1);
    assert.equal(inventorySource.split(String.fromCharCode(96) + fullName + ',').length - 1,1);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),
    NAMES.map(name=>'PNP.DirectWire.'+name));
  assert.match(root,/^import PNP\.ResidualTerminalPhysicalOwnership\s*$/mu);
});

test('M241 regressions cover overlap, uncovered gates, restriction, metadata and cross-owner wiring without weakening transparency', async () => {
  const raw = await text0(REGRESSION), regression = compact0(raw);
  for (const name of NAMES) assert.ok(regression.includes(name + ' '),name);
  for (const token of [
    'candidate : Candidate 1 4 1','if owner.val = 0 then [0, 1] else [1, 2, 2]',
    'terminalPhysicalOwner requests 1 = some 0','terminalPhysicalOwner requests 3 = none',
    'restrictedRecords','reorderedRecords','metadataOnly','Fin.elim0 index',
    'emptyCandidate : Candidate 0 0 0','[.gate 0, .gate 1]',
    'terminalInducedBoundaryValuation candidate','transparent.uniqueMaterializerOwner',
    'terminalPhysicalOwner requests gate = owner ∧ ¬ TerminalTransparentSaturationStep',
    'counts == [1, 2, 1]','emptyCounts == [0, 0, 0]','throw (IO.userError',
  ]) assert.ok(regression.includes(token),token);
  assert.equal([...raw.matchAll(/^#eval\b/gmu)].length,1);
  assert.doesNotMatch(regression,/\b(?:sorry|admit|native_decide|Classical)\b/u);
  assert.doesNotMatch(raw.split('#eval')[1],/\breferenceMinimum\s/u);
  const balance = compact0(await text0('lean/PNP/ResidualTerminalSaturationCostBalance.lean'));
  assert.ok(balance.includes('(terminalSaturationEventOwners (terminalCandidateSaturationSystem candidate model) event).length = 1'));
  assert.ok(balance.includes('nonuniqueMaterializerOwner'));
  assert.ok(!balance.includes('terminalPhysicalOwner'));
});

test('M241 rejects supplied partition authority, finite-only or weakened charge and semantics types', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    ['(requests : Fin ownerCount → List (Fin gates)) (gate : Fin gates) :\n    Option (Fin ownerCount)',
      '(requests : Fin ownerCount → List (Fin gates)) (seed : List (Fin gates)) (gate : Fin gates) :\n    Option (Fin ownerCount)',
      'support-independent-inputs'],
    ['(requests : Fin ownerCount → List (Fin gates))',
      '(requests : Fin 2 → List (Fin gates))', 'signature:'+NAMES[0]],
    ['(records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :\n    ((terminalPhysicalOwners ownerCount)',
      '(records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))\n    (callerCertificate : True) :\n    ((terminalPhysicalOwners ownerCount)',
      'signature:'+NAMES[6]],
    ['(extractTerminalSupport candidate records).gateCount := by',
      '(extractTerminalSupport candidate records).gateCount + 1 := by', 'signature:'+NAMES[6]],
    ['boundaryValuation output =\n      terminalOpenSupportSemantics',
      'boundaryValuation output =\n      (fun _ _ => true)', 'signature:'+NAMES[7]],
  ];
  for (const [before,after,category] of mutations) {
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
});

test('M241 rejects dropped remainder charges, guessed weights and incorrect physical ownership/extraction', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    ['none :: (allFin ownerCount).map some','(allFin ownerCount).map some','fixed-remainder'],
    ['decide (gate ∈ requests owner)','decide (gate ∉ requests owner)','computed-first-requester'],
    ['decide (terminalPhysicalOwner requests gate = owner)','true','computed-owned-gates'],
    ['.map TerminalPrimitiveRecord.gate','.map (fun _ => TerminalPrimitiveRecord.profile 0)','physical-records-only'],
    ['extractTerminalSupport candidate (terminalOwnedPhysicalRecords requests records owner)',
      'extractTerminalSupport candidate records','actual-extracted-materializer'],
    ['ownership_partition_length (terminalPhysicalOwners ownerCount)',
      'suppliedWeight requests','complete-exact-partition'],
  ];
  for (const [before,after,category] of mutations) {
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n').includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n').includes('unaudited-form'));
});

test('M241 durable workflow includes source contracts, strict root audit and guarded regressions', async () => {
  const [packageText,surface,verifier,workflow] = await Promise.all([
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),text0('.github/workflows/lean-bridge.yml'),
  ]);
  const auditPath = 'audits/lean-residual-terminal-physical-ownership0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m241'],'node --test '+auditPath);
  assert.ok(surface.includes("'audit:m241': 'node --test "+auditPath+"'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test '+auditPath));
  for (const path of [auditPath,'docs/lean_residual_terminal_physical_ownership.md'])
    assert.equal(workflow.split("      - '"+path+"'").length-1,2);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});
const M241_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-12-241';
const M241_MILESTONE = 'residual-terminal-physical-ownership';
const M241_HASHES = Object.freeze({
  "PNP.DirectWire.terminalPhysicalOwner_none_iff": "ffc0ed143bf7e48c93f51515386fd85a50d91876ef9079208c85da56384caecc",
  "PNP.DirectWire.terminalPhysicalOwner_first": "ea71fecbc78798ce11593d9f1a9991444ed2441a909b02e9a9e64fdbb0791ac7",
  "PNP.DirectWire.terminalOwnedPhysicalGates_partition": "fcc78b43e37b2ecff81821ca824b6846cbd7dedbc034a964e02604780c234792",
  "PNP.DirectWire.terminalOwnedPhysicalGates_disjoint": "309b77fc6c02991fe447b18c499ffded34920f11e8e5738eb915edbdebceec60",
  "PNP.DirectWire.terminalOwnedPhysicalGates_restrict": "5ad710531d391c95b4159defd761557215dfc0bceefcbced744060569dee942f",
  "PNP.DirectWire.terminalOwnedPhysicalMaterializer_gateCount": "fa95da38296729083ca7fc691fb6ddb2519b8cb14a5cdd7131a56baacd838678",
  "PNP.DirectWire.terminalOwnedPhysicalMaterializer_chargeIdentity": "536ab6d2243bb5599225af8762bebc639928dd957692cc58a4e38c16f7d05fbe",
  "PNP.DirectWire.terminalOwnedPhysicalMaterializer_semantics": "8de6988c721b8734eea3bea0f9c66a58ef6b149f93a3366e195570422ca02c3b",
  "PNP.DirectWire.terminalOwnedPhysicalMaterializer_induced": "6382079281a6e01dc636253438900d6528f761ff9c5fc8e2001d02da554fac7a",
  "PNP.DirectWire.terminalOwnedPhysicalMaterializer_wholeCharge": "2cf21f36ac2063dd4093521f5eb5de20647af79da6848811ce8fae59b33b27a0"
});
const M241_STATUS_FIELDS = Object.freeze({
  "leanResidualTerminalPhysicalOwnershipFormalized": true,
  "leanResidualTerminalPhysicalOwnershipAxiomAuditPassed": true,
  "leanResidualTerminalPhysicalOwnershipAuditedDeclarationCount": 10,
  "leanResidualTerminalPhysicalOwnershipUnrequestedTheorem": "PNP.DirectWire.terminalPhysicalOwner_none_iff",
  "leanResidualTerminalPhysicalOwnershipFirstOwnerTheorem": "PNP.DirectWire.terminalPhysicalOwner_first",
  "leanResidualTerminalPhysicalOwnershipPartitionTheorem": "PNP.DirectWire.terminalOwnedPhysicalGates_partition",
  "leanResidualTerminalPhysicalOwnershipDisjointTheorem": "PNP.DirectWire.terminalOwnedPhysicalGates_disjoint",
  "leanResidualTerminalPhysicalOwnershipRestrictionTheorem": "PNP.DirectWire.terminalOwnedPhysicalGates_restrict",
  "leanResidualTerminalPhysicalOwnershipGateCountTheorem": "PNP.DirectWire.terminalOwnedPhysicalMaterializer_gateCount",
  "leanResidualTerminalPhysicalOwnershipChargeIdentityTheorem": "PNP.DirectWire.terminalOwnedPhysicalMaterializer_chargeIdentity",
  "leanResidualTerminalPhysicalOwnershipOpenSemanticsTheorem": "PNP.DirectWire.terminalOwnedPhysicalMaterializer_semantics",
  "leanResidualTerminalPhysicalOwnershipInducedSemanticsTheorem": "PNP.DirectWire.terminalOwnedPhysicalMaterializer_induced",
  "leanResidualTerminalPhysicalOwnershipWholeChargeTheorem": "PNP.DirectWire.terminalOwnedPhysicalMaterializer_wholeCharge",
  "leanResidualTerminalPhysicalOwnershipScope": "all-finite-candidates-raw-request-families-and-supports-first-requester-ambient-ownership-fixed-remainder-disjoint-stable-physical-pieces-actual-extracted-nand-counts-open-semantics-and-exact-charge-total-only"
});
const M241_AXIOMS = Object.freeze({
  "PNP.DirectWire.terminalPhysicalOwner_none_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalPhysicalOwner_first": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalOwnedPhysicalGates_partition": [
    "propext"
  ],
  "PNP.DirectWire.terminalOwnedPhysicalGates_disjoint": [
    "propext"
  ],
  "PNP.DirectWire.terminalOwnedPhysicalGates_restrict": [
    "propext"
  ],
  "PNP.DirectWire.terminalOwnedPhysicalMaterializer_gateCount": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalOwnedPhysicalMaterializer_chargeIdentity": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalOwnedPhysicalMaterializer_semantics": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalOwnedPhysicalMaterializer_induced": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalOwnedPhysicalMaterializer_wholeCharge": [
    "Quot.sound",
    "propext"
  ]
});

let compiledSourcesPromise0;
function compiledSources0() {
  compiledSourcesPromise0 ??= Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
    text0('status/LEAN_THEOREM_INVENTORY.json'),
    text0('status/PROOF_PROGRESS.json'),
    text0('publication/FORMAL_PUBLICATION_MAP.json'),
  ]).then(([status, inventory, progress, map]) => ({
    status:JSON.parse(status), inventory:JSON.parse(inventory),
    progress:JSON.parse(progress), map:JSON.parse(map), inventoryBytes:Buffer.from(inventory),
  }));
  return compiledSourcesPromise0;
}
const canonicalBytes0 = value => Buffer.from(stableStringify0(value) + '\n');
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();
function metrics0(progress) {
  const coverage = progress.formalArtefactCoverage, proof = progress.proofCompletion;
  return [
    'Formal artefact coverage: ' + coverage.earnedRows + ' of ' + coverage.totalRows
      + ' current scoped publication rows earned.',
    'Risk-weighted proof completion estimate: ' + proof.percent + '%.',
    'Uncertainty range: ' + proof.uncertaintyLowPercent + '% to ' + proof.uncertaintyHighPercent + '%.',
    'Global gates closed: ' + progress.globalGates.filter(gate => gate.status === 'closed').length
      + ' of ' + progress.globalGates.length + '.',
  ];
}

test('M241 compiled physical ownership and materializer interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M241_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M241_COORDINATE)
    assert.equal(map.coordinate, 'PNP-FORMAL-PUBLICATION-MAP-2026-09-12-241');
  assert.deepEqual(row.requiredTheorems, Object.keys(M241_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, 'PNP.ResidualTerminalPhysicalOwnership', name);
      assert.deepEqual(declaration.axioms, M241_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M241_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M241_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M241_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "support-independent physical ownership and charge partition kernel",
  "not the complete manuscript computational-record universe or proof of admissible materializer ownership",
  "canonical assignment does not discharge unique active ownership",
  "The existing production nonunique-owner rejection is unchanged",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M241 publication rejects weakened, supplied, assumption-backed and widened ownership/charge substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M241_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M241_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = 'PNP.DirectWire.' + NAMES[4];
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M241_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M241_MILESTONE
    ? {...row, nonClaim:'Canonical ownership proves every materializer admissible and unconditional polynomial ZeroSlack.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M241 adds physical partition coverage without admissible-materializer, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M241_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "general support-independent physical charge partition",
  "actual extracted NAND materializers",
  "not complete admissible materializer ownership",
  "No fixed weighted checkpoint or global gate changes",
  "evidence row changes coverage only"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M241_COORDINATE) return;
  assert.deepEqual(progress.tracks.map(track => track.pointsEarned), [13, 20, 2, 1, 4]);
  assert.equal(progress.proofCompletion.percent, 40);
  assert.deepEqual(inventory.projectAxioms, []);
  assert.deepEqual(progress.projectSpecificAxiomsRemaining, []);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.deepEqual(progress.rootTheorem, {
    name:'PNP.Main.p_eq_np', present:false, built:false, axiomAuditPassed:false,
  });
  const inflated = structuredClone(progress);
  inflated.proofCompletion.pointsEarned += 1;
  inflated.proofCompletion.percent += 1;
  assert.throws(() => validateProofProgress0(inflated, status, inventory),
    error => error.code === 'ProofCompletion.StoredEarned');
});

test('M241 current summaries distinguish physical partitioning from admissible materializers and global route completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_residual_terminal_physical_ownership.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "No assumption of disjoint or exhaustive requests is hidden in the theorem",
  "support-independent physical ownership and charge partition kernel",
  "not the complete manuscript computational-record universe or proof of admissible materializer ownership",
  "The existing production nonunique-owner rejection is unchanged",
  "Runtime execution is test evidence, not theorem authority",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-12-support-independent-physical-ownership.md'));
  assert.ok(plan.includes('Publication decision: defer'));
  if (progress.asOfCoordinate !== M241_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_residual_terminal_physical_ownership.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
