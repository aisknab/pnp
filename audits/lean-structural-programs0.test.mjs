import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {REQUIRED_MILESTONE_THEOREMS0} from '../formal-publication0.mjs';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Frozen from the reviewed general construction, not inferred by these tests.
const SPECS = [
  {"part":"ReindexingCausalBounds","path":"lean/PNP/NANDReindexingCausalBounds.lean","module":"PNP.NANDReindexingCausalBounds","sourceContractSha256":"81c1af843dcd136a8cbe63325c7d100bae7f9e2c5bcd133cb9b6d11e158da5ed","heads":[{"kind":"theorem","name":"result_gate_level"},{"kind":"theorem","name":"result_source_level"},{"kind":"theorem","name":"result_output_level"}],"theorems":["PNP.DirectWire.StructuralReindexing.result_gate_level","PNP.DirectWire.StructuralReindexing.result_source_level","PNP.DirectWire.StructuralReindexing.result_output_level"]},
  {"part":"WireStructuralReindexing","path":"lean/PNP/NANDWireStructuralReindexing.lean","module":"PNP.NANDWireStructuralReindexing","sourceContractSha256":"32620ea7397bdb259a91f7984f6bc6d9b765db5a6309e080bf31a5e7d7eb4f48","heads":[{"kind":"def","name":"reindex"},{"kind":"theorem","name":"reindex_exposed"},{"kind":"theorem","name":"reindex_gateCount"},{"kind":"def","name":"reindexForwardGate"},{"kind":"def","name":"reindexBackwardGate"},{"kind":"theorem","name":"reindex_backward_forward"},{"kind":"theorem","name":"reindex_forward_backward"},{"kind":"theorem","name":"reindex_output"},{"kind":"theorem","name":"reindex_field"},{"kind":"theorem","name":"reindex_field_source"},{"kind":"theorem","name":"reindex_exposed_level"},{"kind":"theorem","name":"reindex_output_level"},{"kind":"theorem","name":"reindex_field_level"},{"kind":"theorem","name":"reindex_causalBounds"}],"theorems":["PNP.DirectWire.WireCarrier.reindex_exposed","PNP.DirectWire.WireCarrier.reindex_gateCount","PNP.DirectWire.WireCarrier.reindex_backward_forward","PNP.DirectWire.WireCarrier.reindex_forward_backward","PNP.DirectWire.WireCarrier.reindex_output","PNP.DirectWire.WireCarrier.reindex_field","PNP.DirectWire.WireCarrier.reindex_field_source","PNP.DirectWire.WireCarrier.reindex_exposed_level","PNP.DirectWire.WireCarrier.reindex_output_level","PNP.DirectWire.WireCarrier.reindex_field_level","PNP.DirectWire.WireCarrier.reindex_causalBounds"]},
  {"part":"WireStructuralState","path":"lean/PNP/NANDWireStructuralState.lean","module":"PNP.NANDWireStructuralState","sourceContractSha256":"e6dc69958e1e62c4b79993e84088586d234dedec846334e37e65fe501e47641d","heads":[{"kind":"def","name":"reindex"},{"kind":"theorem","name":"reindex_pending"},{"kind":"theorem","name":"reindex_charged"},{"kind":"theorem","name":"reindex_removed"},{"kind":"theorem","name":"reindex_gateCount"},{"kind":"theorem","name":"reindex_causalInvariant"},{"kind":"structure","name":"Receipt"},{"kind":"def","name":"Receipt.next"},{"kind":"def","name":"execute"},{"kind":"theorem","name":"execute_isSome"},{"kind":"theorem","name":"execute_failure_iff"}],"theorems":["PNP.DirectWire.WireObligationHistory.State.reindex_pending","PNP.DirectWire.WireObligationHistory.State.reindex_charged","PNP.DirectWire.WireObligationHistory.State.reindex_removed","PNP.DirectWire.WireObligationHistory.State.reindex_gateCount","PNP.DirectWire.WireObligationHistory.State.reindex_causalInvariant","PNP.DirectWire.WireStructuralState.execute_isSome","PNP.DirectWire.WireStructuralState.execute_failure_iff"]},
  {"part":"WireStructuralOwnership","path":"lean/PNP/NANDWireStructuralOwnership.lean","module":"PNP.NANDWireStructuralOwnership","sourceContractSha256":"0c4734cbb46cf5ec43ac095cfcbf7d24eaa5dc06c9a2834b5b22c6e2ed4b0dad","heads":[{"kind":"def","name":"Receipt.ownership"},{"kind":"theorem","name":"ownership_origin"},{"kind":"theorem","name":"ownership_origin_forward"},{"kind":"theorem","name":"ownership_origin_injective"},{"kind":"theorem","name":"ownership_live_members"},{"kind":"theorem","name":"ownership_not_allocated"},{"kind":"theorem","name":"ownership_charged"},{"kind":"theorem","name":"ownership_removed"},{"kind":"theorem","name":"ownership_wellFormed"},{"kind":"theorem","name":"physical_ownership"}],"theorems":["PNP.DirectWire.WireStructuralState.Receipt.ownership_origin","PNP.DirectWire.WireStructuralState.Receipt.ownership_origin_forward","PNP.DirectWire.WireStructuralState.Receipt.ownership_origin_injective","PNP.DirectWire.WireStructuralState.Receipt.ownership_live_members","PNP.DirectWire.WireStructuralState.Receipt.ownership_not_allocated","PNP.DirectWire.WireStructuralState.Receipt.ownership_charged","PNP.DirectWire.WireStructuralState.Receipt.ownership_removed","PNP.DirectWire.WireStructuralState.Receipt.ownership_wellFormed","PNP.DirectWire.WireStructuralState.Receipt.physical_ownership"]},
  {"part":"WireStructuralProgram","path":"lean/PNP/NANDWireStructuralProgram.lean","module":"PNP.NANDWireStructuralProgram","sourceContractSha256":"3fb3e2dbdf0c3600b66dbcee1951d49bb8669b6c676e1351c1c59e5107eb12c5","heads":[{"kind":"theorem","name":"advance_structural_origin"},{"kind":"theorem","name":"advance_structural_charged"},{"kind":"theorem","name":"advance_structural_removed"}],"theorems":["PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_origin","PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_charged","PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_removed"]},
];
const REUSED_NAMES = [
  "PNP.DirectWire.WireOpenProgram.orderEvents_success_iff",
  "PNP.DirectWire.WireOpenProgram.orderEvents_failure_iff",
  "PNP.DirectWire.WireOpenProgram.execute_failed_tail",
  "PNP.DirectWire.WireOpenProgram.CompiledProgram.full_output",
  "PNP.DirectWire.WireOpenProgram.CompiledProgram.full_field",
  "PNP.DirectWire.WireOpenProgram.CompiledProgram.creation_lifecycle",
  "PNP.DirectWire.WireOpenProgram.CompiledProgram.executed_count",
  "PNP.DirectWire.WireOpenProgram.CompiledProgram.executed_identities_nodup",
  "PNP.DirectWire.WireOpenProgram.CompiledProgram.causalInvariant",
  "PNP.DirectWire.WireOpenProgram.CompiledProgram.physical_ownership",
  "PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_origin_injective",
  "PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_charge_origin",
  "PNP.DirectWire.WireOpenProgram.compile_exists_iff",
  "PNP.DirectWire.WireOpenProgram.compile_none_iff",
  "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.records_source",
  "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.proper_support",
  "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.output",
  "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.field",
  "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.charge_accounting",
  "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictGain",
  "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictResidualDescent",
  "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.physical_ownership",
  "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.closed_ledger",
  "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.creation_lifecycle",
  "PNP.DirectWire.WireOpenCertificate.verify_exists_iff",
  "PNP.DirectWire.WireOpenCertificate.verify_sound",
  "PNP.DirectWire.WireOpenCertificate.verify_decode_none",
  "PNP.DirectWire.WireOpenCertificate.verify_program_none",
  "PNP.DirectWire.WireOpenCertificate.verify_not_proper",
  "PNP.DirectWire.WireOpenCertificate.verify_no_gain",
];
const REGRESSIONS = [
  {"path":"lean-regression/PNPReindexingCausalBounds.lean","imports":["PNP.NANDReindexingCausalBounds"],"printedNames":["PNP.DirectWire.StructuralReindexing.result_gate_level","PNP.DirectWire.StructuralReindexing.result_source_level","PNP.DirectWire.StructuralReindexing.result_output_level"],"sourceContractSha256":"eca5a15e3f5b7f303a03de1a58081b46e44be9af1887e607e12604c6a306924c"},
  {"path":"lean-regression/PNPWireStructuralState.lean","imports":["PNP.NANDWireStructuralState"],"printedNames":["PNP.DirectWire.WireCarrier.reindex_field_source","PNP.DirectWire.WireCarrier.reindex_output","PNP.DirectWire.WireCarrier.reindex_field","PNP.DirectWire.WireCarrier.reindex_output_level","PNP.DirectWire.WireCarrier.reindex_field_level","PNP.DirectWire.WireObligationHistory.State.reindex_pending","PNP.DirectWire.WireObligationHistory.State.reindex_causalInvariant","PNP.DirectWire.WireStructuralState.execute_isSome","PNP.DirectWire.WireStructuralState.execute_failure_iff"],"sourceContractSha256":"fb2f848964969f2ec5a2dd41407ac31b967860fe4a4de15d275d0aaebde59f5a"},
  {"path":"lean-regression/PNPWireStructuralOwnership.lean","imports":["PNP.NANDWireStructuralOwnership"],"printedNames":["PNP.DirectWire.WireStructuralState.Receipt.ownership_origin_forward","PNP.DirectWire.WireStructuralState.Receipt.ownership_origin_injective","PNP.DirectWire.WireStructuralState.Receipt.ownership_live_members","PNP.DirectWire.WireStructuralState.Receipt.ownership_wellFormed","PNP.DirectWire.WireStructuralState.Receipt.physical_ownership"],"sourceContractSha256":"7d3f63cc2949c9b1bc7190b43e0ba84a95c5d1fdb86373b6c8ea2502c3d165f2"},
  {"path":"lean-regression/PNPWireStructuralProgram.lean","imports":["PNP.NANDWireStructuralProgram"],"printedNames":["PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_origin","PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_charged","PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_structural_removed","PNP.DirectWire.WireOpenProgram.CompiledProgram.physical_ownership","PNP.DirectWire.WireOpenProgram.CompiledProgram.creation_lifecycle","PNP.DirectWire.WireOpenProgram.CompiledProgram.causalInvariant"],"sourceContractSha256":"903c90b339554c3f9eccd9246db8ccf8421452029e3a4f099bd73650e3234f0b"},
  {"path":"lean-regression/PNPWireStructuralCertificate.lean","imports":["PNP.NANDWireOpenCertificate"],"printedNames":["PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictGain","PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictResidualDescent","PNP.DirectWire.WireOpenCertificate.CheckedCertificate.physical_ownership","PNP.DirectWire.WireOpenCertificate.CheckedCertificate.creation_lifecycle","PNP.DirectWire.WireOpenCertificate.verify_program_none","PNP.DirectWire.WireOpenCertificate.verify_not_proper","PNP.DirectWire.WireOpenCertificate.verify_no_gain"],"sourceContractSha256":"c7295e464190e416cf1f4d83dcc4390c4d3e31163bf3efc772678afdffcbb524"},
];
const AXIOM_NAMES = [...SPECS.flatMap(spec => spec.theorems), ...REUSED_NAMES];
const text0 = file => readFile(new URL('../' + file, import.meta.url), 'utf8');
const compact0 = source => stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
const digest0 = source => createHash('sha256').update(compact0(source)).digest('hex');
const printed0 = source => [...source.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(row => row[1]);
function inspect0(source, spec) {
  const failures = [], clean = compact0(source);
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('unaudited-form');
  if (/\b(?:sorry|admit|unsafe|native_decide|noncomputable|Classical|implemented_by|csimp)\b|#(?:eval|reduce|guard|synth)\b/u.test(clean))
    failures.push('shortcut');
  if (JSON.stringify(explicitLeanDeclarationHeads0(source).map(({kind, name}) => ({kind, name}))) !==
      JSON.stringify(spec.heads)) failures.push('closed-declarations');
  if (digest0(source) !== spec.sourceContractSha256) failures.push('reviewed-source-contract');
  return failures;
}
let loaded;
function sources0() {
  loaded ??= Promise.all(SPECS.map(async spec => ({spec, source: await text0(spec.path)})));
  return loaded;
}
async function rejectMutations0(part, mutations) {
  const found = (await sources0()).find(row => row.spec.part === part);
  assert.ok(found, part);
  for (const [label, from, to] of mutations) {
    assert.ok(found.source.includes(from), part + ': mutation target exists: ' + label);
    const changed = found.source.replace(from, to);
    assert.notEqual(changed, found.source, label);
    assert.ok(inspect0(changed, found.spec).length > 0, part + ': ' + label);
  }
}

test('M271 source: arbitrary-dimension implementations have closed reviewed contracts', async () => {
  assert.deepEqual(SPECS.map(row => row.part), [
    'ReindexingCausalBounds', 'WireStructuralReindexing', 'WireStructuralState',
    'WireStructuralOwnership', 'WireStructuralProgram',
  ]);
  assert.equal(AXIOM_NAMES.length, 63);
  assert.equal(new Set(AXIOM_NAMES).size, 63);
  for (const {spec, source} of await sources0()) assert.deepEqual(inspect0(source, spec), [], spec.path);
});

test('M271 source: supplied authority and hidden declaration changes reject', async () => {
  for (const {spec, source} of await sources0()) {
    for (const extra of [
      'axiom hiddenAuthority : True', 'private axiom hiddenAuthority : True',
      'opaque hiddenAuthority : True', 'variable (suppliedCorrectness : Prop)',
      'variable (suppliedOwnership : Nat)', 'import PNP.Main',
      'unsafe def hiddenAuthority : Nat := 0', 'private theorem hiddenAuthority : True := by trivial',
      'example : True := by trivial', 'def hiddenAuthority : Nat := 0',
    ]) assert.ok(inspect0(source + '\n' + extra + '\n', spec).length > 0, spec.path + ': ' + extra);
    assert.deepEqual(inspect0(source + '\n/- prose: axiom hiddenAuthority : True -/\n', spec), []);
  }
});

test('M271 source: causal bounds follow actual source wiring for arbitrary labels', async () => {
  await rejectMutations0('ReindexingCausalBounds', [
    ['all input labels', '(labels : Fin inputs → Nat)', '(labels : Fin 1 → Nat)'],
    ['actual gate sources', 'rw [result_sources]', 'rw [suppliedSources]'],
    ['all ordered outputs', '(output : Fin outputs)', '(output : Fin 1)'],
    ['actual source map', 'sourceMap (forwardGate original.program relabeling) wire',
      'sourceMap suppliedMap wire'],
  ]);
});

test('M271 source: carrier fields remain literal wires with derived physical inverses', async () => {
  await rejectMutations0('WireStructuralReindexing', [
    ['actual combined carrier', 'unpack (result carrier.exposed.candidate relabeling).toImplementation',
      'suppliedCarrier'],
    ['actual inverse placement', 'backwardGate carrier.exposed.candidate.program relabeling',
      'suppliedBackwardMap'],
    ['literal field source', 'sourceMap (carrier.reindexForwardGate relabeling) (carrier.source field)',
      '.constant false'],
    ['all field caps', '(fieldCaps : Fin fields → Nat)', '(fieldCaps : Fin 1 → Nat)'],
  ]);
});

test('M271 source: exact pending snapshots and current-carrier decoding cannot be relaxed', async () => {
  await rejectMutations0('WireStructuralState', [
    ['whole pending snapshot function', 'pending := state.pending', 'pending := fun _ => none'],
    ['historical charges', 'charged := state.charged', 'charged := 0'],
    ['historical removals', 'removed := state.removed', 'removed := 0'],
    ['current carrier bound', 'GateRenaming.decode before.current.implementation.gateCount code',
      'GateRenaming.decode source.implementation.gateCount code'],
    ['complete raw sequence', 'code with', '(code.take 1) with'],
    ['causal obligation invariant', 'bounded.1, bounded.2', 'bounded.1, suppliedInvariant'],
  ]);
});

test('M271 source: local ownership derives a physical bijection without invented cost', async () => {
  await rejectMutations0('WireStructuralOwnership', [
    ['actual backward owner', '.original (before.current.reindexBackwardGate receipt.relabeling gate)',
      '.original (suppliedOwner gate)'],
    ['no fresh allocations', 'charged := []', 'charged := suppliedCharges'],
    ['no invented removals', 'removed := []', 'removed := suppliedRemovals'],
    ['all physical gates', '(gate : Fin receipt.next.current.implementation.gateCount)',
      '(gate : Fin 1)'],
    ['injective origin map', 'Function.Injective receipt.ownership.origin', 'True'],
  ]);
});

test('M271 source: complete programs retain prior identities and charge/removal history', async () => {
  await rejectMutations0('WireStructuralProgram', [
    ['prior global identity', '= ledger.origin gate', '= .original gate'],
    ['prior charge list', 'ledger.charged := by', '[] := by'],
    ['prior removal list', 'ledger.removed := by', '[] := by'],
    ['actual physical permutation', 'before.current.reindexForwardGate receipt.relabeling gate',
      'suppliedForward gate'],
    ['ledger lifting', 'ledger.liftOrigin position', 'suppliedGlobalOwner'],
  ]);
});

test('M271 preflight: root, inventory producer, publication names and regressions agree', async () => {
  const [root, audit, probe, mapText] = await Promise.all([
    text0('lean/PNP.lean'), text0('lean-audit/PNPStructuralProgramsAxiomAudit.lean'),
    text0('lean-audit/PNPTheoremInventory.lean'), text0('publication/FORMAL_PUBLICATION_MAP.json'),
  ]);
  assert.match(audit, /^import PNP$/mu);
  assert.deepEqual(printed0(audit), AXIOM_NAMES);
  for (const spec of SPECS) assert.ok(root.split('\n').includes('import ' + spec.module), spec.path);
  const map = JSON.parse(mapText);
  const rows = map.milestones.filter(row => row.id === 'structural-open-program-integration');
  assert.equal(rows.length, 1);
  assert.deepEqual(rows[0].requiredTheorems, AXIOM_NAMES);
  for (const name of AXIOM_NAMES) {
    assert.equal(probe.split(String.fromCharCode(96) + name + ',').length - 1, 1, name);
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(value => value === name).length, 1, name);
    assert.ok(Object.hasOwn(map.earnedMilestoneTheoremKernelTypeSha256, name), name);
  }
  for (const spec of REGRESSIONS) {
    const source = await text0(spec.path);
    assert.equal(digest0(source), spec.sourceContractSha256, spec.path);
    assert.deepEqual(printed0(source), spec.printedNames, spec.path);
    assert.deepEqual([...source.matchAll(/^import (\S+)\s*$/gmu)].map(row => row[1]), spec.imports, spec.path);
    assert.doesNotMatch(stripLeanCommentsAndStrings0(source), /\b(?:sorry|admit|native_decide|unsafe)\b|#eval!/u);
  }
});
