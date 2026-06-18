import assert from 'node:assert/strict';
import test from 'node:test';

import {
  COORD,
  KIND,
  ParserState,
  SORT,
  TAG,
  bytesEqual,
  digestObject0,
  encodeName0,
  encodeNat0,
  isErr,
  isOk,
  makeMinimalBootstrapContext,
  name,
  parseNat0,
  parseTop0,
  record,
  typeCheck0,
} from '../pcc-core.mjs';

test('nat encoding round trips through the parser', () => {
  const encoded = encodeNat0(65537n);
  const parsed = parseNat0(new ParserState(encoded));

  assert.equal(isOk(parsed), true);
  assert.equal(parsed.value, 65537n);
  assert.equal(parsed.state.pos, encoded.length);
});

test('top-level name parsing rejects trailing bytes', () => {
  const ctx = makeMinimalBootstrapContext();
  const encoded = encodeName0('Proof');
  const withTrailingByte = new Uint8Array([...encoded, 0xff]);
  const parsed = parseTop0(ctx, withTrailingByte, SORT.Name);

  assert.equal(isErr(parsed), true);
  assert.equal(parsed.coord, COORD.PARSE_TRAILING_BYTES);
});

test('minimal context accepts a correctly shaped RowKey record', () => {
  const ctx = makeMinimalBootstrapContext();
  const rowKey = record(
    TAG.RowKey,
    Array.from({ length: 17 }, (_, index) => name(`field-${index}`)),
    SORT.RowKey
  );
  const checked = typeCheck0(ctx, rowKey, SORT.RowKey);

  assert.equal(isOk(checked), true);
});

test('digestObject0 produces deterministic digest records', () => {
  const ctx = makeMinimalBootstrapContext();
  const first = digestObject0(ctx, name('example'));
  const second = digestObject0(ctx, name('example'));

  assert.equal(first.kind, KIND.RECORD);
  assert.equal(first.fields.length, 4);
  assert.equal(bytesEqual(first.fields[3].value, second.fields[3].value), true);
});
