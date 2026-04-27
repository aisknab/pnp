import test from 'node:test';
import assert from 'node:assert/strict';

import {
  ParserState,
  parseNat0,
  parseInt0,
  parseName0,
  COORD,
  MODE,
  TAG,
  SORT,
  KIND,
  name,
  nat,
  bytes,
  record,
  list,
  makeMinimalBootstrapContext,
  typeCheck0,
  checkModeUse0,
  checkNoHiddenMin0,
  installDeclarationSchema,
  computeRowKey0,
  checkDuplicateRows0,
  sha256,
  nfSerialize0,
} from '../pcc-core.mjs';

function expectErr(result, coord) {
  assert.equal(result.kind, 'err');
  assert.equal(result.coord, coord);
}

test('ParseNat0 rejects noncanonical leading-zero magnitude', () => {
  const bad = new Uint8Array([
    0x00, 0x00, 0x00, 0x02,
    0x00, 0x01,
  ]);

  const result = parseNat0(new ParserState(bad));
  expectErr(result, COORD.NAT_NONCANONICAL_LEADING_ZERO);
});

test('ParseInt0 rejects negative zero', () => {
  const bad = new Uint8Array([
    0x01,
    0x00, 0x00, 0x00, 0x00,
  ]);

  const result = parseInt0(new ParserState(bad));
  expectErr(result, COORD.INT_NEGATIVE_ZERO);
});

test('ParseName0 rejects invalid UTF-8', () => {
  const bad = new Uint8Array([
    0x00, 0x00, 0x00, 0x01, 0x01,
    0xff,
  ]);

  const result = parseName0(new ParserState(bad));
  expectErr(result, COORD.NAME_INVALID_UTF8);
});

test('TypeCheck0 rejects malformed RowKey arity', () => {
  const ctx = makeMinimalBootstrapContext();

  const badRowKey = record(TAG.RowKey, [], SORT.RowKey);
  const result = typeCheck0(ctx, badRowKey, SORT.RowKey);

  expectErr(result, COORD.PARSE_BAD_ARITY);
});

test('CheckModeUse0 rejects quotient equality consumed by replacement equality', () => {
  const result = checkModeUse0(MODE.QUOT, 'ReplacementEquality');
  expectErr(result, COORD.MODE_PROMOTION);
});

test('CheckNoHiddenMin0 rejects executable minimumEquivalent alias', () => {
  const ctx = makeMinimalBootstrapContext();

  ctx.resolveAlias = (name) => name;
  ctx.collectIdentifierOccurrences = () => [
    {
      name: 'minimumEquivalent',
      class: 'ExecCall',
      path: ['fakeProgram', 'call', 0],
    },
  ];

  const result = checkNoHiddenMin0(ctx, {});
  expectErr(result, COORD.HIDDEN_MIN_EXEC_CALL);
});

function makeDemoRow(ctx, selectedRouteName) {
  const packageId = 'Iface';
  const schemaId = 'SortDecl';

  installDeclarationSchema(ctx, packageId, schemaId, 'Sort');

  const rawObj = record(0x00030001, [
    name('DemoSort'),
    nat(0n),
  ]);

  const tempRow = {
    PackageID: packageId,
    SchemaID: schemaId,
    RawObj: rawObj,
  };

  const rowKey = computeRowKey0(ctx, tempRow);
  const hashKey = bytes(sha256(nfSerialize0(ctx, rowKey)));

  return record(TAG.Row, [
    name(packageId),
    name(schemaId),
    rawObj,
    rawObj,
    rowKey,
    name('TransportId'),
    list(0x00000008, [name('AcceptDecl'), name('RejectMalformed')]),
    list(0x00000008, [name('AcceptDecl')]),
    name(selectedRouteName),
    name('ProofRef.SortDeclWellTyped'),
    name('BoundsRef.BootFinite'),
    hashKey,
  ], SORT.Row);
}

test('CheckDuplicateRows0 rejects same RowKey with conflicting selected routes', () => {
  const ctx = makeMinimalBootstrapContext();

  const rowA = makeDemoRow(ctx, 'AcceptDecl');
  const rowB = makeDemoRow(ctx, 'RejectMalformed');

  const result = checkDuplicateRows0(ctx, [rowA, rowB]);
  expectErr(result, COORD.ROW_DUPLICATE_CONFLICT);
});
