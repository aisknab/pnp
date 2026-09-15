import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0, hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const sourceURL = new URL('../lean/PNP/NANDWireObligationHistoryR7.lean', import.meta.url);
function inspect(source) {
  const text = stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
  const failures = [];
  const require = (condition, name) => { if (!condition) failures.push(name); };
  require(!hasLeanAssumptionDeclaration0(source), 'no-assumptions');
  require(!hasUnauditedLeanDeclarationForm0(source), 'audited-declarations');
  require(!/\b(?:sorry|admit|unsafe|native_decide|noncomputable|Classical|implemented_by|csimp)\b/u.test(text), 'no-shortcuts');
  require(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head => head.name)) === JSON.stringify([
    'RawSupportRecord', 'decodeRecord', 'encodeRecord', 'decodeRecord_encode', 'decodeRecord_source',
    'decodeRecords', 'decodeRecords_encode', 'decodeRecords_source', 'R7Realization', 'computeR7', 'computeR7_isSome_iff', 'carrier', 'full_field', 'exact_charge', 'causalBounds',
    'restoreR7', 'restoreR7_gate_charge', 'restoreR7_full_value', 'restoreR7_other_pending',
  ]), 'closed-declarations');
  for (const [fragment, label] of [
    ['inductive RawSupportRecord where | gate (index : Nat) | boundary (index : Nat) | interface (index : Nat) deriving Repr, DecidableEq', 'raw-only-coordinates'],
    ['| .gate index => if valid : index < gates then some (.gate ⟨index, valid⟩) else none', 'gate-range'],
    ['| .boundary index => if valid : index < inputs then some (.boundary ⟨index, valid⟩) else none', 'boundary-range'],
    ['| .interface index => if valid : index < observations then some (.interface ⟨index, valid⟩) else none', 'interface-range'],
    ['raw.mapM (decodeRecord inputs gates observations)', 'every-coordinate-validated'],
    ['def computeR7 (original : WireCarrier inputs outputs fields) (raw : List RawSupportRecord) : Option (R7Realization original raw) :=', 'no-caller-certificate'],
    ['records.map encodeRecord = raw :=', 'complete-list-coordinate-contract'],
    ['(computeR7 original raw).isSome = true ↔', 'exact-recognition-contract'],
    ['theorem decodeRecord_source {inputs gates observations : Nat} (raw : RawSupportRecord) (record : TerminalPrimitiveRecord inputs gates observations 0) (accepted : decodeRecord inputs gates observations raw = some record) : encodeRecord record = raw :=', 'exact-decoded-coordinate-contract'],
    ['decodeRecords inputs original.implementation.gateCount (outputs + fields) raw', 'actual-carrier-widths'],
    ['if small : (WireUnaryArbitrarySupport.pulled original records).boundary.length ≤ 1 then some ⟨records, decoded, small⟩ else none', 'computed-boundary-recognition'],
    ['WireUnaryArbitrarySupport.expanded original realization.records realization.small', 'actual-r7-construction'],
    ['current := join state.current (materializer realization.carrier (keepExcept field)) (keepExcept field)', 'actual-r7-materializer'],
    ['charged := state.charged + (materializer realization.carrier (keepExcept field)).implementation.gateCount', 'full-physical-charge'],
    ['(realization.full_field valuation field).trans (snapshot.fullValue valuation)', 'captured-full-value'],
    ['setPending_other state.pending field none other different', 'other-snapshots-unchanged'],
    ['WireUnaryCausalBound.expanded_causalBounds original realization.records realization.small labels', 'source-derived-causality'],
  ]) require(text.includes(fragment), label);
  return failures;
}

test('M265 computes source-bound raw R7 recognition and charged full restoration', async () => {
  assert.deepEqual(inspect(await readFile(sourceURL, 'utf8')), []);
});

test('M265 rejects unchecked coordinates, supplied replacements, and unpaid restoration', async () => {
  const source = await readFile(sourceURL, 'utf8');
  for (const [before, after, category] of [
    ['index < gates', 'True', 'gate-range'],
    ['index < inputs', 'True', 'boundary-range'],
    ['index < observations', 'True', 'interface-range'],
    ['raw.mapM (decodeRecord inputs gates observations)', 'some []', 'every-coordinate-validated'],
    ['records.map encodeRecord = raw :=', 'records.map encodeRecord = [] :=', 'complete-list-coordinate-contract'],
    ['(computeR7 original raw).isSome = true ↔', '(computeR7 original raw).isSome = true →', 'exact-recognition-contract'],
    ['def computeR7 (original : WireCarrier inputs outputs fields)', 'def computeR7 (supplied : True) (original : WireCarrier inputs outputs fields)', 'no-caller-certificate'],
    ['original.implementation.gateCount (outputs + fields) raw', '0 (outputs + fields) raw', 'actual-carrier-widths'],
    ['(WireUnaryArbitrarySupport.pulled original records).boundary.length ≤ 1 then', 'True then', 'computed-boundary-recognition'],
    ['WireUnaryArbitrarySupport.expanded original realization.records realization.small', 'original', 'actual-r7-construction'],
    ['charged := state.charged + (materializer realization.carrier (keepExcept field)).implementation.gateCount', 'charged := state.charged', 'full-physical-charge'],
    ['(realization.full_field valuation field).trans (snapshot.fullValue valuation)', 'suppliedAgreement', 'captured-full-value'],
  ]) {
    assert.ok(source.includes(before), 'mutation anchor: ' + category);
    assert.ok(inspect(source.replaceAll(before, after)).includes(category), category);
  }
  assert.ok(inspect(source + '\naxiom assumedR7 : False\n').includes('no-assumptions'));
  assert.ok(inspect(source + '\ndef ignoredGuard : Bool := true\n').includes('closed-declarations'));
});
