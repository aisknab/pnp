/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: implement the byte codec, typed object model, canonical normal form,
 * row identity, proof-reference lookup, route priority, mode-use firewall, and
 * core no-hidden-minimization scan.
 * Inputs: untrusted bytes, typed record objects, schema/bootstrap contexts, rows,
 * proof indexes, route sets, mode labels, and expanded identifier occurrences.
 * Outputs: `ok`/`err` values carrying deterministic coordinates, paths, witnesses,
 * parser state, and optional ledgers.
 * Invariants enforced: canonical integer/name encoding, complete top-level byte
 * consumption, declared record arity/sorts, idempotent normal forms, route-independent
 * row identity, full-key comparison after hash lookup, highest-priority routing,
 * and comparison-only use of quotient equality.
 * Assumptions not checked: mathematical theorem soundness, completeness of caller-
 * supplied schemas, correctness of expansion/occurrence collection, or absence of
 * equivalent brute-force search that is not classified as a forbidden occurrence.
 * Failure modes: malformed bytes or records return the first named `COORD`; some
 * programmer-facing encoders throw on invalid in-memory values.
 * Naming: `NF` means canonical normal form, `Quot` means projected/quotient mode,
 * and the suffix `0` is a schema version rather than a Boolean or arithmetic zero.
 */

import { createHash } from 'node:crypto';
import { TextDecoder, TextEncoder } from 'node:util';

const utf8Decoder = new TextDecoder('utf-8', { fatal: true });
const utf8Encoder = new TextEncoder();

export const RESULT = Object.freeze({
  OK: 'ok',
  ERR: 'err',
});

export const KIND = Object.freeze({
  UNIT: 'Unit',
  BOOL: 'Bool',
  NAT: 'Nat',
  INT: 'Int',
  BYTES: 'Bytes',
  NAME: 'Name',
  RECORD: 'Record',
  LIST: 'List',
  TUPLE: 'Tuple',
  SET: 'Set',
  MULTISET: 'Multiset',
  MAP: 'Map',
});

// Stable proof/checker mode labels. `Full` carries constructive semantics;
// `Quot` is projected comparison data; the remaining modes classify structural,
// arithmetic, and transport-only evidence. These strings can occur in serialized
// records, so changing them is not a comment-only refactor.
export const MODE = Object.freeze({
  FULL: 'Full',
  QUOT: 'Quot',
  STRUCT: 'Struct',
  ARITH: 'Arith',
  TRANSPORT: 'Transport',
});

export const COORD = Object.freeze({
  PARSE_TRUNCATED: 'Parse.Truncated',
  PARSE_TRAILING_BYTES: 'Parse.TrailingBytes',
  PARSE_UNKNOWN_TAG: 'Parse.UnknownTag',
  PARSE_TAG_RANGE: 'Parse.TagRange',
  PARSE_BAD_ARITY: 'Parse.BadArity',

  NAT_TRUNCATED: 'Parse.Nat.Truncated',
  NAT_LENGTH_OVERFLOW: 'Parse.Nat.LengthOverflow',
  NAT_NONCANONICAL_LEADING_ZERO: 'Parse.Nat.NonCanonicalLeadingZero',

  INT_BAD_SIGN: 'Parse.Int.BadSign',
  INT_NEGATIVE_ZERO: 'Parse.Int.NegativeZero',

  BYTES_TRUNCATED: 'Parse.Bytes.Truncated',

  NAME_INVALID_UTF8: 'Parse.Name.InvalidUTF8',
  NAME_NONCANONICAL_FORM: 'Parse.Name.NonCanonicalForm',

  MAP_DUPLICATE_KEY: 'Codec.Map.DuplicateKey',
  MAP_DUPLICATE_KEY_CONFLICT: 'Codec.Map.DuplicateKeyConflict',

  TYPE_SORT_MISMATCH: 'Type.SortMismatch',
  TYPE_BAD_FIELD: 'Type.BadField',
  TYPE_ROWKEY_ARITY: 'Type.RowKeyArity',
  TYPE_PROOFNODE_ARITY: 'Type.ProofNodeArity',
  TYPE_CORE_SELF_REFERENCE: 'Type.CoreSelfReference',
  MODE_QUOT_IN_FULL_FIELD: 'Mode.QuotInFullField',
  MODE_PROMOTION: 'Mode.Promotion',
  MODE_UNKNOWN_CONSUMER: 'Mode.UnknownConsumer',

  NF_NOT_IDEMPOTENT: 'NF.NotIdempotent',

  DIGEST_ALGORITHM_MISMATCH: 'Digest.AlgorithmMismatch',
  DIGEST_LENGTH_MISMATCH: 'Digest.LengthMismatch',
  DIGEST_HASH_MISMATCH: 'Digest.HashMismatch',
  DIGEST_EQUALITY_CLAIM: 'Digest.EqualityClaim',
  DIGEST_MISSING_FULL_KEY_COMPARE: 'Digest.MissingFullKeyCompare',

  ROW_SHAPE: 'Row.Shape',
  ROWKEY_MISMATCH: 'RowKey.Mismatch',
  ROWKEY_HASH_MISMATCH: 'RowKey.HashMismatch',
  ROW_DUPLICATE_CONFLICT: 'Row.DuplicateConflict',

  PROOFREF_MISSING: 'ProofRef.Missing',
  PROOFREF_AMBIGUOUS: 'ProofRef.Ambiguous',

  ROUTE_UNDECLARED: 'Route.Undeclared',
  ROUTE_PRIORITY_MISMATCH: 'Route.PriorityMismatch',
  ROUTE_EQUAL_PRIORITY_CONFLICT: 'Route.EqualPriorityConflict',
  ROUTE_CONSTRUCTIVE_DOWNGRADE: 'Route.ConstructiveDowngrade',

  HIDDEN_MIN_EXEC_CALL: 'HiddenMin.ExecCall',
});

export const TAG = Object.freeze({
  Unit: 0x00000001,
  BoolFalse: 0x00000002,
  BoolTrue: 0x00000003,
  Nat: 0x00000004,
  Int: 0x00000005,
  Bytes: 0x00000006,
  Name: 0x00000007,
  List: 0x00000008,
  Tuple: 0x00000009,
  Record: 0x0000000a,
  Ref: 0x0000000b,
  Digest: 0x0000000c,
  OptionNone: 0x0000000d,
  OptionSome: 0x0000000e,

  Row: 0x00030010,
  RowKey: 0x00030011,
  ProofNode: 0x00030020,
  CorePackage: 0x00030050,
});

export const SORT = Object.freeze({
  Unit: 'Unit',
  Bool: 'Bool',
  Nat: 'Nat',
  Int: 'Int',
  Bytes: 'Bytes',
  Name: 'Name',
  Record: 'Record',
  Row: 'Row',
  RowKey: 'RowKey',
  Route: 'Route',
  ProofRef: 'ProofRef',
  BoundsRef: 'BoundsRef',
  Any: 'Any',
});

export function ok(value, state = null, ledger = []) {
  return { kind: RESULT.OK, value, state, ledger };
}

export function err(coord, path = [], witness = null, state = null) {
  return { kind: RESULT.ERR, coord, path, witness, state };
}

export function isOk(result) {
  return result.kind === RESULT.OK;
}

export function isErr(result) {
  return result.kind === RESULT.ERR;
}

export class ParserState {
  constructor(bytes, pos = 0, path = []) {
    this.bytes = toUint8Array(bytes);
    this.pos = pos;
    this.limit = this.bytes.length;
    this.path = path;
  }

  remaining() {
    return this.limit - this.pos;
  }

  withPos(pos) {
    return new ParserState(this.bytes, pos, this.path);
  }

  withPath(component) {
    return new ParserState(this.bytes, this.pos, [...this.path, component]);
  }
}

export function toUint8Array(input) {
  if (input instanceof Uint8Array) return input;
  if (Array.isArray(input)) return new Uint8Array(input);
  if (Buffer.isBuffer(input)) return new Uint8Array(input);
  throw new TypeError('Expected Uint8Array, Buffer, or byte array');
}

export function concatBytes(...parts) {
  const total = parts.reduce((sum, part) => sum + part.length, 0);
  const out = new Uint8Array(total);
  let offset = 0;
  for (const part of parts) {
    out.set(part, offset);
    offset += part.length;
  }
  return out;
}

export function compareBytes(a, b) {
  const aa = toUint8Array(a);
  const bb = toUint8Array(b);
  const n = Math.min(aa.length, bb.length);
  for (let i = 0; i < n; i += 1) {
    if (aa[i] !== bb[i]) return aa[i] - bb[i];
  }
  return aa.length - bb.length;
}

export function bytesEqual(a, b) {
  return compareBytes(a, b) === 0;
}

export function u32be(n) {
  if (!Number.isInteger(n) || n < 0 || n > 0xffffffff) {
    throw new RangeError('u32be expects an unsigned 32-bit integer');
  }
  return new Uint8Array([
    (n >>> 24) & 0xff,
    (n >>> 16) & 0xff,
    (n >>> 8) & 0xff,
    n & 0xff,
  ]);
}

export function readU32BE(state) {
  if (state.remaining() < 4) {
    return err(COORD.PARSE_TRUNCATED, state.path, { need: 4 }, state);
  }

  const b = state.bytes;
  const p = state.pos;
  const n =
    b[p] * 2 ** 24 +
    b[p + 1] * 2 ** 16 +
    b[p + 2] * 2 ** 8 +
    b[p + 3];

  return ok(n, state.withPos(p + 4));
}

export function natToSafeNumber(n, coord, path) {
  if (n > BigInt(Number.MAX_SAFE_INTEGER)) {
    return err(coord, path, { value: n.toString() });
  }
  return ok(Number(n));
}

export function parseNat0(state) {
  const lenResult = readU32BE(state);
  if (isErr(lenResult)) return lenResult;

  const len = lenResult.value;
  let s = lenResult.state;

  if (len === 0) return ok(0n, s);

  if (s.remaining() < len) {
    return err(COORD.NAT_TRUNCATED, s.path, { len }, s);
  }

  const mag = s.bytes.slice(s.pos, s.pos + len);

  if (mag[0] === 0) {
    return err(COORD.NAT_NONCANONICAL_LEADING_ZERO, s.path, { len }, s);
  }

  let value = 0n;
  for (const byte of mag) {
    value = (value << 8n) + BigInt(byte);
  }

  return ok(value, s.withPos(s.pos + len));
}

export function parseInt0(state) {
  if (state.remaining() < 1) {
    return err(COORD.PARSE_TRUNCATED, state.path, { need: 1 }, state);
  }

  const sign = state.bytes[state.pos];
  if (sign !== 0 && sign !== 1) {
    return err(COORD.INT_BAD_SIGN, state.path, { sign }, state);
  }

  const magResult = parseNat0(state.withPos(state.pos + 1));
  if (isErr(magResult)) return magResult;

  const mag = magResult.value;
  if (sign === 1 && mag === 0n) {
    return err(COORD.INT_NEGATIVE_ZERO, state.path, null, magResult.state);
  }

  return ok(sign === 0 ? mag : -mag, magResult.state);
}

export function parseBytes0(state) {
  const lenResult = parseNat0(state);
  if (isErr(lenResult)) return lenResult;

  const lenNumber = natToSafeNumber(
    lenResult.value,
    COORD.NAT_LENGTH_OVERFLOW,
    lenResult.state.path
  );
  if (isErr(lenNumber)) return lenNumber;

  const len = lenNumber.value;
  const s = lenResult.state;

  if (s.remaining() < len) {
    return err(COORD.BYTES_TRUNCATED, s.path, { len }, s);
  }

  return ok(s.bytes.slice(s.pos, s.pos + len), s.withPos(s.pos + len));
}

export function parseName0(state) {
  const bytesResult = parseBytes0(state);
  if (isErr(bytesResult)) return bytesResult;

  let decoded;
  try {
    decoded = utf8Decoder.decode(bytesResult.value);
  } catch {
    return err(COORD.NAME_INVALID_UTF8, state.path, null, bytesResult.state);
  }

  const normalized = decoded.normalize('NFC');
  if (normalized !== decoded) {
    return err(COORD.NAME_NONCANONICAL_FORM, state.path, { decoded }, bytesResult.state);
  }

  return ok({ kind: KIND.NAME, value: decoded }, bytesResult.state);
}

export function encodeNat0(n) {
  const value = typeof n === 'bigint' ? n : BigInt(n);
  if (value < 0n) throw new RangeError('Nat cannot be negative');

  if (value === 0n) return u32be(0);

  const bytes = [];
  let x = value;
  while (x > 0n) {
    bytes.push(Number(x & 0xffn));
    x >>= 8n;
  }
  bytes.reverse();

  return concatBytes(u32be(bytes.length), new Uint8Array(bytes));
}

export function encodeInt0(z) {
  const value = typeof z === 'bigint' ? z : BigInt(z);

  if (value >= 0n) {
    return concatBytes(new Uint8Array([0]), encodeNat0(value));
  }

  return concatBytes(new Uint8Array([1]), encodeNat0(-value));
}

export function encodeBytes0(bytes) {
  const b = toUint8Array(bytes);
  return concatBytes(encodeNat0(BigInt(b.length)), b);
}

export function encodeName0(nameObject) {
  const value =
    typeof nameObject === 'string'
      ? nameObject
      : nameObject && nameObject.kind === KIND.NAME
        ? nameObject.value
        : null;

  if (typeof value !== 'string') {
    throw new TypeError('encodeName0 expects a string or Name object');
  }

  const normalized = value.normalize('NFC');
  if (normalized !== value) {
    throw new Error('Name is not canonical NFC');
  }

  return encodeBytes0(utf8Encoder.encode(value));
}

export function unit() {
  return { kind: KIND.UNIT };
}

export function bool(value) {
  return { kind: KIND.BOOL, value: Boolean(value) };
}

export function nat(value) {
  return { kind: KIND.NAT, value: typeof value === 'bigint' ? value : BigInt(value) };
}

export function int(value) {
  return { kind: KIND.INT, value: typeof value === 'bigint' ? value : BigInt(value) };
}

export function bytes(value) {
  return { kind: KIND.BYTES, value: toUint8Array(value) };
}

export function name(value) {
  return { kind: KIND.NAME, value };
}

export function record(tag, fields, sort = SORT.Record) {
  return { kind: KIND.RECORD, tag, fields, sort };
}

export function list(tag, items, sort = SORT.Any) {
  return { kind: KIND.LIST, tag, items, sort };
}

export function tuple(items, sort = SORT.Any) {
  return { kind: KIND.TUPLE, items, sort };
}

export function setObj(items, sort = SORT.Any) {
  return { kind: KIND.SET, items, sort };
}

export function multisetObj(items, sort = SORT.Any) {
  return { kind: KIND.MULTISET, items, sort };
}

export function mapObj(entries, sort = SORT.Any) {
  return { kind: KIND.MAP, entries, sort };
}

export function sortOfObject(obj) {
  if (!obj || typeof obj !== 'object') return null;
  switch (obj.kind) {
    case KIND.UNIT:
      return SORT.Unit;
    case KIND.BOOL:
      return SORT.Bool;
    case KIND.NAT:
      return SORT.Nat;
    case KIND.INT:
      return SORT.Int;
    case KIND.BYTES:
      return SORT.Bytes;
    case KIND.NAME:
      return SORT.Name;
    case KIND.RECORD:
      return obj.sort || SORT.Record;
    default:
      return obj.sort || SORT.Any;
  }
}

export function typeCheck0(ctx, obj, expectedSort = SORT.Any, path = []) {
  const actualSort = sortOfObject(obj);

  if (expectedSort !== SORT.Any && actualSort !== expectedSort) {
    if (!ctx.isSubtype || !ctx.isSubtype(actualSort, expectedSort)) {
      return err(COORD.TYPE_SORT_MISMATCH, path, { expectedSort, actualSort });
    }
  }

  if (obj.kind === KIND.RECORD) {
    const decl = ctx.recordByTag.get(obj.tag);
    if (!decl) return err(COORD.PARSE_UNKNOWN_TAG, path, { tag: obj.tag });

    if (obj.fields.length !== decl.fieldSorts.length) {
      return err(COORD.PARSE_BAD_ARITY, path, {
        tag: obj.tag,
        expected: decl.fieldSorts.length,
        actual: obj.fields.length,
      });
    }

    if (obj.tag === TAG.RowKey && obj.fields.length !== 17) {
      return err(COORD.TYPE_ROWKEY_ARITY, path, { actual: obj.fields.length });
    }

    if (obj.tag === TAG.ProofNode && obj.fields.length !== 12) {
      return err(COORD.TYPE_PROOFNODE_ARITY, path, { actual: obj.fields.length });
    }

    if (obj.tag === TAG.CorePackage) {
      if (obj.fields.length !== 14) {
        return err(COORD.PARSE_BAD_ARITY, path, { tag: obj.tag, actual: obj.fields.length });
      }
      if (containsTag(obj, ctx.tags.AcceptRun)) {
        return err(COORD.TYPE_CORE_SELF_REFERENCE, path, { tag: ctx.tags.AcceptRun });
      }
    }

    for (let i = 0; i < decl.fieldSorts.length; i += 1) {
      const fieldSort = decl.fieldSorts[i];
      const field = obj.fields[i];

      if (decl.requiresFull && decl.requiresFull.has(i) && isQuotEquality(field)) {
        return err(COORD.MODE_QUOT_IN_FULL_FIELD, [...path, i], null);
      }

      const r = typeCheck0(ctx, field, fieldSort, [...path, i]);
      if (isErr(r)) return r;
    }
  }

  return ok(true);
}

export function isQuotEquality(obj) {
  return Boolean(
    obj &&
      obj.kind === KIND.RECORD &&
      obj.fields &&
      obj.fields.some((field) => field && field.kind === KIND.NAME && field.value === MODE.QUOT)
  );
}

export function containsTag(obj, tag) {
  if (!tag || !obj || typeof obj !== 'object') return false;
  if (obj.kind === KIND.RECORD && obj.tag === tag) return true;

  const children = [];
  if (Array.isArray(obj.fields)) children.push(...obj.fields);
  if (Array.isArray(obj.items)) children.push(...obj.items);
  if (Array.isArray(obj.entries)) {
    for (const entry of obj.entries) {
      children.push(entry.key, entry.value);
    }
  }

  return children.some((child) => containsTag(child, tag));
}

export function parseObject0(ctx, state, expectedSort = SORT.Any) {
  if (expectedSort === SORT.Nat) {
    const r = parseNat0(state);
    return isOk(r) ? ok(nat(r.value), r.state) : r;
  }

  if (expectedSort === SORT.Int) {
    const r = parseInt0(state);
    return isOk(r) ? ok(int(r.value), r.state) : r;
  }

  if (expectedSort === SORT.Bytes) {
    const r = parseBytes0(state);
    return isOk(r) ? ok(bytes(r.value), r.state) : r;
  }

  if (expectedSort === SORT.Name) {
    return parseName0(state);
  }

  const tagResult = parseNat0(state);
  if (isErr(tagResult)) return tagResult;

  const tagNumber = natToSafeNumber(tagResult.value, COORD.PARSE_TAG_RANGE, tagResult.state.path);
  if (isErr(tagNumber)) return tagNumber;

  const tag = tagNumber.value;
  let s = tagResult.state;

  const arityResult = parseNat0(s);
  if (isErr(arityResult)) return arityResult;

  const arityNumber = natToSafeNumber(arityResult.value, COORD.PARSE_BAD_ARITY, arityResult.state.path);
  if (isErr(arityNumber)) return arityNumber;

  const arity = arityNumber.value;
  s = arityResult.state;

  const decl = ctx.recordByTag.get(tag) || ctx.constructorByTag.get(tag);
  if (!decl) return err(COORD.PARSE_UNKNOWN_TAG, s.path, { tag }, s);

  if (ctx.tagRangeOf && !ctx.tagRangeOf(tag).valid) {
    return err(COORD.PARSE_TAG_RANGE, s.path, { tag }, s);
  }

  if (decl.fieldSorts.length !== arity) {
    return err(COORD.PARSE_BAD_ARITY, s.path, {
      tag,
      expected: decl.fieldSorts.length,
      actual: arity,
    }, s);
  }

  const fields = [];
  for (let i = 0; i < arity; i += 1) {
    const fieldState = s.withPath(i);
    const fieldResult = parseObject0(ctx, fieldState, decl.fieldSorts[i]);
    if (isErr(fieldResult)) return fieldResult;
    fields.push(fieldResult.value);
    s = fieldResult.state;
  }

  const obj = record(tag, fields, decl.outputSort || SORT.Record);
  const tc = typeCheck0(ctx, obj, expectedSort, state.path);
  if (isErr(tc)) return tc;

  return ok(obj, s);
}

/**
 * Parses exactly one top-level typed object and rejects any trailing bytes.
 * Input: bootstrap/schema context, untrusted bytes, and the expected output sort.
 * Output: `ok(parsedObject, finalState)` or a named parse/type `err`.
 * Enforces: declared tags/arities/sorts, canonical primitive encodings, and complete
 * byte consumption.
 * Does not check: mathematical meaning of the parsed certificate or completeness of
 * the caller-provided declaration context.
 * Failure modes: truncation, unknown/out-of-range tag, bad arity/sort, noncanonical
 * primitive encoding, or `Parse.TrailingBytes`.
 */
export function parseTop0(ctx, inputBytes, expectedSort) {
  const state = new ParserState(inputBytes);
  const result = parseObject0(ctx, state, expectedSort);
  if (isErr(result)) return result;

  if (result.state.pos !== result.state.limit) {
    return err(COORD.PARSE_TRAILING_BYTES, result.state.path, {
      pos: result.state.pos,
      limit: result.state.limit,
    }, result.state);
  }

  return ok(result.value, result.state, result.ledger);
}

export function nf0(ctx, obj) {
  switch (obj.kind) {
    case KIND.UNIT:
    case KIND.BOOL:
    case KIND.NAT:
    case KIND.INT:
    case KIND.BYTES:
      return obj;

    case KIND.NAME:
      if (obj.value.normalize('NFC') !== obj.value) {
        throw new Error(COORD.NAME_NONCANONICAL_FORM);
      }
      return obj;

    case KIND.LIST:
      return list(obj.tag, obj.items.map((item) => nf0(ctx, item)), obj.sort);

    case KIND.TUPLE:
      return tuple(obj.items.map((item) => nf0(ctx, item)), obj.sort);

    case KIND.RECORD:
      return record(obj.tag, obj.fields.map((field) => nf0(ctx, field)), obj.sort);

    case KIND.SET: {
      const normalized = obj.items.map((item) => nf0(ctx, item));
      normalized.sort((a, b) => compareBytes(encodeObject0(ctx, a), encodeObject0(ctx, b)));
      const unique = [];
      for (const item of normalized) {
        if (unique.length === 0 || !bytesEqual(encodeObject0(ctx, unique[unique.length - 1]), encodeObject0(ctx, item))) {
          unique.push(item);
        }
      }
      return setObj(unique, obj.sort);
    }

    case KIND.MULTISET: {
      const normalized = obj.items.map((item) => nf0(ctx, item));
      normalized.sort((a, b) => compareBytes(encodeObject0(ctx, a), encodeObject0(ctx, b)));
      return multisetObj(normalized, obj.sort);
    }

    case KIND.MAP: {
      const entries = obj.entries.map((entry) => ({
        key: nf0(ctx, entry.key),
        value: nf0(ctx, entry.value),
      }));

      entries.sort((a, b) => compareBytes(encodeObject0(ctx, a.key), encodeObject0(ctx, b.key)));

      for (let i = 1; i < entries.length; i += 1) {
        const prev = entries[i - 1];
        const curr = entries[i];
        if (bytesEqual(encodeObject0(ctx, prev.key), encodeObject0(ctx, curr.key))) {
          if (!bytesEqual(encodeObject0(ctx, prev.value), encodeObject0(ctx, curr.value))) {
            throw new Error(COORD.MAP_DUPLICATE_KEY_CONFLICT);
          }
          throw new Error(COORD.MAP_DUPLICATE_KEY);
        }
      }

      return mapObj(entries, obj.sort);
    }

    default:
      throw new Error(`Unknown object kind: ${obj.kind}`);
  }
}

export function assertNFIdempotent(ctx, obj) {
  const y = nf0(ctx, obj);
  const yy = nf0(ctx, y);

  if (!bytesEqual(encodeObjectRaw0(ctx, y), encodeObjectRaw0(ctx, yy))) {
    return err(COORD.NF_NOT_IDEMPOTENT, [], { first: y, second: yy });
  }

  return ok(y);
}

export function encodeObjectRaw0(ctx, obj) {
  switch (obj.kind) {
    case KIND.UNIT:
      return concatBytes(encodeNat0(TAG.Unit), encodeNat0(0n));

    case KIND.BOOL:
      return concatBytes(encodeNat0(obj.value ? TAG.BoolTrue : TAG.BoolFalse), encodeNat0(0n));

    case KIND.NAT:
      return encodeNat0(obj.value);

    case KIND.INT:
      return encodeInt0(obj.value);

    case KIND.BYTES:
      return encodeBytes0(obj.value);

    case KIND.NAME:
      return encodeName0(obj);

    case KIND.RECORD:
      return concatBytes(
        encodeNat0(BigInt(obj.tag)),
        encodeNat0(BigInt(obj.fields.length)),
        ...obj.fields.map((field) => encodeObject0(ctx, field))
      );

    case KIND.LIST:
      return concatBytes(
        encodeNat0(BigInt(TAG.List)),
        encodeNat0(BigInt(obj.items.length + 1)),
        encodeNat0(BigInt(obj.tag)),
        ...obj.items.map((item) => encodeObject0(ctx, item))
      );

    case KIND.TUPLE:
      return concatBytes(
        encodeNat0(BigInt(TAG.Tuple)),
        encodeNat0(BigInt(obj.items.length)),
        ...obj.items.map((item) => encodeObject0(ctx, item))
      );

    case KIND.SET:
      return concatBytes(
        encodeNat0(BigInt(TAG.List)),
        encodeNat0(BigInt(obj.items.length)),
        ...obj.items.map((item) => encodeObject0(ctx, item))
      );

    case KIND.MULTISET:
      return concatBytes(
        encodeNat0(BigInt(TAG.List)),
        encodeNat0(BigInt(obj.items.length)),
        ...obj.items.map((item) => encodeObject0(ctx, item))
      );

    case KIND.MAP:
      return concatBytes(
        encodeNat0(BigInt(TAG.List)),
        encodeNat0(BigInt(obj.entries.length)),
        ...obj.entries.flatMap((entry) => [
          encodeObject0(ctx, entry.key),
          encodeObject0(ctx, entry.value),
        ])
      );

    default:
      throw new Error(`Cannot encode unknown object kind: ${obj.kind}`);
  }
}

export function encodeObject0(ctx, obj) {
  return encodeObjectRaw0(ctx, nf0(ctx, obj));
}

export function nfSerialize0(ctx, obj) {
  return encodeObject0(ctx, nf0(ctx, obj));
}

export function sha256(bytesIn) {
  return new Uint8Array(createHash('sha256').update(Buffer.from(bytesIn)).digest());
}

export function digestObject0(ctx, obj) {
  const serialized = nfSerialize0(ctx, obj);
  return record(ctx.tags.DigestRecord, [
    name('SHA256-CANONICAL-BYTES'),
    name(sortOfObject(obj) || SORT.Any),
    nat(BigInt(serialized.length)),
    bytes(sha256(serialized)),
  ], ctx.sorts.Digest || SORT.Record);
}

/**
 * Uses SHA-256 only to select a bucket, then compares full canonical key bytes.
 * Input: context, digest-bucket index, lookup key, and candidate-key accessor.
 * Output: all candidates whose full canonical keys equal the requested key plus an
 * audit ledger of bucket size and comparisons.
 * Enforces: hash-as-index rather than hash-as-semantic-equality discipline.
 * Does not check: uniqueness of returned candidates or soundness of `keyOf`.
 * Failure modes: caller/runtime serialization errors; ambiguity is handled by the
 * consumer that knows the expected conclusion or row semantics.
 */
export function hashIndexLookup0(ctx, index, key, keyOf) {
  const keyBytes = nfSerialize0(ctx, key);
  const h = Buffer.from(sha256(keyBytes)).toString('hex');
  const bucket = index.get(h) || [];

  const candidates = [];
  const fullKeyComparisons = [];

  for (const candidate of bucket) {
    const candidateKey = keyOf(candidate);
    const candidateKeyBytes = nfSerialize0(ctx, candidateKey);
    const equal = bytesEqual(keyBytes, candidateKeyBytes);
    fullKeyComparisons.push({ candidate, equal });
    if (equal) candidates.push(candidate);
  }

  return ok(candidates, null, [{ h, bucketSize: bucket.length, fullKeyComparisons }]);
}

/**
 * Recomputes the 17-field canonical identity of a generated row.
 * Input: schema context and a parsed row with package/schema IDs and raw object.
 * Output: a typed `RowKey` record.
 * Enforces: normalization plus interface, kind, arity, mode, frontier, semantics,
 * incidence, dependency, profile, charge, obligation, budget, activation, rank, and
 * payload identity; selected route is deliberately excluded.
 * Does not check: correctness of schema key functions or the row's proof/theorem.
 * Failure modes: unknown schema or exceptions from caller-supplied schema functions.
 */
export function computeRowKey0(ctx, row) {
  const schema = ctx.getSchema(row.PackageID, row.SchemaID);
  if (!schema) throw new Error(`Unknown schema ${row.PackageID}:${row.SchemaID}`);

  const normalized = schema.normalize
    ? schema.normalize(ctx, row.RawObj)
    : nf0(ctx, row.RawObj);

  const fields = [
    ctx.ifaceHash,
    name(String(row.PackageID)),
    name(String(row.SchemaID)),
    schema.kindKey(ctx, normalized),
    schema.arityKey(ctx, normalized),
    schema.modeKey(ctx, normalized),
    schema.frontKey ? schema.frontKey(ctx, normalized) : ctx.empty.FrontKey,
    schema.semanticKey ? schema.semanticKey(ctx, normalized) : ctx.empty.SemanticKey,
    schema.incidenceKey ? schema.incidenceKey(ctx, normalized) : ctx.empty.IncidenceKey,
    schema.dependencyKey ? schema.dependencyKey(ctx, normalized) : ctx.empty.DependencyKey,
    schema.profileKey ? schema.profileKey(ctx, normalized) : ctx.empty.ProfileKey,
    schema.chargeKey ? schema.chargeKey(ctx, normalized) : ctx.empty.ChargeKey,
    schema.obligationKey ? schema.obligationKey(ctx, normalized) : ctx.empty.ObligationKey,
    schema.budgetKey ? schema.budgetKey(ctx, normalized) : ctx.empty.BudgetKey,
    schema.activationKey ? schema.activationKey(ctx, normalized) : ctx.empty.ActivationKey,
    schema.rankKey ? schema.rankKey(ctx, normalized) : ctx.empty.RankKey,
    schema.payloadKey(ctx, normalized),
  ];

  return record(TAG.RowKey, fields, SORT.RowKey);
}

export function parseRowRecord(ctx, rowRecord) {
  if (!rowRecord || rowRecord.kind !== KIND.RECORD || rowRecord.tag !== TAG.Row) {
    return err(COORD.ROW_SHAPE, [], { rowRecord });
  }

  if (rowRecord.fields.length !== 12) {
    return err(COORD.ROW_SHAPE, [], { fieldCount: rowRecord.fields.length });
  }

  const [
    PackageID,
    SchemaID,
    RawObj,
    NormObj,
    RowKey,
    TransportProof,
    CandidateRoutes,
    ActiveRouteSet,
    SelectedRoute,
    ProofRef,
    BoundsRef,
    HashKey,
  ] = rowRecord.fields;

  return ok({
    PackageID: primitiveNameOrNumber(PackageID),
    SchemaID: primitiveNameOrNumber(SchemaID),
    RawObj,
    NormObj,
    RowKey,
    TransportProof,
    CandidateRoutes,
    ActiveRouteSet,
    SelectedRoute,
    ProofRef,
    BoundsRef,
    HashKey,
    original: rowRecord,
  });
}

export function primitiveNameOrNumber(obj) {
  if (obj.kind === KIND.NAME) return obj.value;
  if (obj.kind === KIND.NAT) return Number(obj.value);
  if (obj.kind === KIND.INT) return Number(obj.value);
  return obj;
}

/**
 * Checks both the displayed full row key and its displayed SHA-256 hash.
 * Input: schema context and an untrusted serialized row record.
 * Output: `ok(true)` or a specific row-shape/key/hash `err`.
 * Enforces: equality with a recomputed canonical row key before accepting the hash.
 * Does not check: route priority, proof-reference soundness, or theorem correctness.
 * Failure modes: malformed row, `RowKey.Mismatch`, or `RowKey.HashMismatch`.
 */
export function checkRowKey0(ctx, rowRecord) {
  const parsed = parseRowRecord(ctx, rowRecord);
  if (isErr(parsed)) return parsed;

  const row = parsed.value;
  const computed = computeRowKey0(ctx, row);

  if (!bytesEqual(nfSerialize0(ctx, computed), nfSerialize0(ctx, row.RowKey))) {
    return err(COORD.ROWKEY_MISMATCH, [], {
      computed,
      displayed: row.RowKey,
    });
  }

  const expectedHash = Buffer.from(sha256(nfSerialize0(ctx, row.RowKey))).toString('hex');
  const displayedHash = objectHashHex(ctx, row.HashKey);

  if (displayedHash !== expectedHash) {
    return err(COORD.ROWKEY_HASH_MISMATCH, [], {
      expectedHash,
      displayedHash,
    });
  }

  return ok(true);
}

export function objectHashHex(ctx, obj) {
  if (obj.kind === KIND.BYTES) {
    return Buffer.from(obj.value).toString('hex');
  }

  if (obj.kind === KIND.RECORD && obj.tag === ctx.tags.DigestRecord) {
    const hashField = obj.fields[3];
    if (hashField && hashField.kind === KIND.BYTES) {
      return Buffer.from(hashField.value).toString('hex');
    }
  }

  return Buffer.from(sha256(nfSerialize0(ctx, obj))).toString('hex');
}

export function checkDuplicateRows0(ctx, rowRecords) {
  const groups = new Map();

  for (const rowRecord of rowRecords) {
    const keyCheck = checkRowKey0(ctx, rowRecord);
    if (isErr(keyCheck)) return keyCheck;

    const parsed = parseRowRecord(ctx, rowRecord);
    if (isErr(parsed)) return parsed;

    const row = parsed.value;
    const keyBytes = Buffer.from(nfSerialize0(ctx, row.RowKey)).toString('hex');
    if (!groups.has(keyBytes)) groups.set(keyBytes, []);
    groups.get(keyBytes).push(row);
  }

  const compareFields = [
    'NormObj',
    'TransportProof',
    'CandidateRoutes',
    'ActiveRouteSet',
    'SelectedRoute',
    'ProofRef',
    'BoundsRef',
  ];

  for (const rows of groups.values()) {
    if (rows.length <= 1) continue;

    const first = rows[0];
    for (let i = 1; i < rows.length; i += 1) {
      const current = rows[i];
      for (const field of compareFields) {
        if (!bytesEqual(nfSerialize0(ctx, first[field]), nfSerialize0(ctx, current[field]))) {
          return err(COORD.ROW_DUPLICATE_CONFLICT, [], {
            first: first.original,
            second: current.original,
            field,
          });
        }
      }
    }
  }

  return ok(true);
}

export function checkProofRefKey0(ctx, proofIndex, ref, neededConclusion) {
  const lookup = hashIndexLookup0(ctx, proofIndex, ref, (candidate) => candidate.key);
  if (isErr(lookup)) return lookup;

  const matches = [];
  for (const candidate of lookup.value) {
    if (bytesEqual(nfSerialize0(ctx, candidate.conclusion), nfSerialize0(ctx, neededConclusion))) {
      matches.push(candidate);
    }
  }

  if (matches.length === 0) {
    return err(COORD.PROOFREF_MISSING, [], { ref, neededConclusion });
  }

  if (matches.length > 1) {
    const uniqueConclusions = new Set(
      matches.map((candidate) => Buffer.from(nfSerialize0(ctx, candidate.conclusion)).toString('hex'))
    );
    if (uniqueConclusions.size > 1) {
      return err(COORD.PROOFREF_AMBIGUOUS, [], { ref, matches });
    }
  }

  return ok(matches[0]);
}

export function checkRoutePriority0(ctx, routeSet, activeSet, selected, priority) {
  const routeIds = new Set(routeSet.map((route) => route.id));
  const activeIds = new Set(activeSet.map((route) => route.id));

  for (const route of routeSet) {
    if (!ctx.declaredRoutes.has(route.id)) {
      return err(COORD.ROUTE_UNDECLARED, [], { route });
    }
  }

  for (const route of activeSet) {
    if (!routeIds.has(route.id)) {
      return err(COORD.ROUTE_UNDECLARED, [], { route });
    }
  }

  const priorityRank = new Map(priority.map((routeId, index) => [routeId, index]));

  for (const route of routeSet) {
    if (!priorityRank.has(route.id)) {
      return err(COORD.ROUTE_PRIORITY_MISMATCH, [], { route, priority });
    }
  }

  const activeRoutes = routeSet.filter((route) => activeIds.has(route.id));
  if (activeRoutes.length === 0) {
    return err(COORD.ROUTE_PRIORITY_MISMATCH, [], { reason: 'empty active set' });
  }

  activeRoutes.sort((a, b) => priorityRank.get(a.id) - priorityRank.get(b.id));
  const expected = activeRoutes[0];

  const equalTop = activeRoutes.filter((route) => priorityRank.get(route.id) === priorityRank.get(expected.id));
  if (equalTop.length > 1 && incompatibleRoutes(equalTop)) {
    return err(COORD.ROUTE_EQUAL_PRIORITY_CONFLICT, [], { routes: equalTop });
  }

  if (selected.id !== expected.id) {
    return err(COORD.ROUTE_PRIORITY_MISMATCH, [], { selected, expected });
  }

  const constructiveActive = activeRoutes.some((route) => route.class === 'ConstructiveGain');
  if (constructiveActive && selected.class !== 'ConstructiveGain') {
    return err(COORD.ROUTE_CONSTRUCTIVE_DOWNGRADE, [], { selected, activeRoutes });
  }

  return ok(true);
}

export function incompatibleRoutes(routes) {
  const encoded = new Set(routes.map((route) => JSON.stringify(route.payload ?? null)));
  return encoded.size > 1;
}

/**
 * Applies the central allowlist for equality-mode consumers.
 * Input: equality mode and the named operation that wants to consume it.
 * Output: `ok(true)` for allowed combinations or a named mode error.
 * Enforces: constructive/exact consumers require `Full`; listed comparison consumers
 * may use quotient information.
 * Does not check: existence/correctness of a full lift, obligation discharge, or the
 * truth of the equality itself; owning checkers must establish those records.
 * Failure modes: `Mode.Promotion` or `Mode.UnknownConsumer`.
 */
export function checkModeUse0(eqMode, consumerKind) {
  const fullRequired = new Set([
    'ReplacementEquality',
    'ObligationDischarge',
    'ExactMinimum',
    'NeutralOverlay',
    'VerifyDWGain',
    'SATThreshold',
  ]);

  const quotientAllowed = new Set([
    'QuotSignature',
    'QuotRequest',
    'ProjectionDefect',
    'ActivationAccounting',
    'ObligationCreation',
    'QuotObstruction',
  ]);

  if (fullRequired.has(consumerKind)) {
    if (eqMode !== MODE.FULL) {
      return err(COORD.MODE_PROMOTION, [], { eqMode, consumerKind });
    }
    return ok(true);
  }

  if (quotientAllowed.has(consumerKind)) {
    return ok(true);
  }

  return err(COORD.MODE_UNKNOWN_CONSUMER, [], { consumerKind });
}

/**
 * Rejects classified executable occurrences of forbidden minimization identifiers.
 * Input: a context supplying expansion, occurrence collection, alias resolution, and
 * forbidden-symbol set, plus the object/AST to scan.
 * Output: `ok(true)` or `HiddenMin.ExecCall` at the occurrence path.
 * Enforces: scanning after the expansion supplied by the context and alias-aware name
 * comparison for executable/branch-control occurrences.
 * Does not check: completeness of expansion/classification or semantically equivalent
 * exhaustive search that uses no forbidden identifier.
 * Failure modes: first forbidden executable occurrence; malformed caller hooks may
 * throw as programmer errors.
 */
export function checkNoHiddenMin0(ctx, ast) {
  const expanded = ctx.expandAll ? ctx.expandAll(ast) : ast;
  const occurrences = ctx.collectIdentifierOccurrences
    ? ctx.collectIdentifierOccurrences(expanded)
    : [];

  for (const occurrence of occurrences) {
    const canonicalName = ctx.resolveAlias
      ? ctx.resolveAlias(occurrence.name)
      : occurrence.name;

    if (
      ctx.forbiddenExecSymbols.has(canonicalName) &&
      (occurrence.class === 'ExecCall' || occurrence.class === 'BranchControl')
    ) {
      return err(COORD.HIDDEN_MIN_EXEC_CALL, occurrence.path, {
        identifier: occurrence.name,
        canonicalName,
      });
    }
  }

  return ok(true);
}

export function makeMinimalBootstrapContext() {
  const recordByTag = new Map();

  recordByTag.set(TAG.Row, {
    fieldSorts: [
      SORT.Any,
      SORT.Any,
      SORT.Any,
      SORT.Any,
      SORT.RowKey,
      SORT.Any,
      SORT.Any,
      SORT.Any,
      SORT.Route,
      SORT.ProofRef,
      SORT.BoundsRef,
      SORT.Any,
    ],
    outputSort: SORT.Row,
  });

  recordByTag.set(TAG.RowKey, {
    fieldSorts: Array.from({ length: 17 }, () => SORT.Any),
    outputSort: SORT.RowKey,
  });

  recordByTag.set(TAG.ProofNode, {
    fieldSorts: Array.from({ length: 12 }, () => SORT.Any),
    outputSort: 'ProofNode',
  });

  recordByTag.set(TAG.CorePackage, {
    fieldSorts: Array.from({ length: 14 }, () => SORT.Any),
    outputSort: 'CorePackage',
  });

  const ctx = {
    recordByTag,
    constructorByTag: new Map(),
    tags: {
      DigestRecord: TAG.Digest,
      AcceptRun: 0x000a0101,
    },
    sorts: {
      Digest: 'Digest',
    },
    ifaceHash: name('IfaceHash0'),
    empty: {
      FrontKey: name('EmptyFront'),
      SemanticKey: name('EmptySemantic'),
      IncidenceKey: name('EmptyIncidence'),
      DependencyKey: name('EmptyDependency'),
      ProfileKey: name('EmptyProfile'),
      ChargeKey: name('EmptyCharge'),
      ObligationKey: name('EmptyObligation'),
      BudgetKey: name('EmptyBudget'),
      ActivationKey: name('EmptyActivation'),
      RankKey: name('EmptyRank'),
    },
    declaredRoutes: new Set(['AcceptDecl', 'RejectMalformed']),
    forbiddenExecSymbols: new Set([
      'mu',
      'mu*',
      'mu#',
      'Can',
      'argmin',
      'max_G',
      'minimumEquivalent',
      'optimalCircuit',
      'exactMinSearch',
      'canonicalMinimizer',
      'maximizeGain',
    ]),
    isSubtype(actual, expected) {
      return expected === SORT.Any || actual === expected;
    },
    tagRangeOf(tag) {
      return { valid: Number.isInteger(tag) && tag >= 0 };
    },
    getSchema(packageId, schemaId) {
      const key = `${packageId}:${schemaId}`;
      return this.schemas.get(key);
    },
    schemas: new Map(),
  };

  return ctx;
}
export function installDeclarationSchema(ctx, packageId, schemaId, kindName) {
  const key = `${packageId}:${schemaId}`;

  if (!ctx.schemas) {
    ctx.schemas = new Map();
  }

  ctx.schemas.set(key, {
    normalize(innerCtx, rawObj) {
      return nf0(innerCtx, rawObj);
    },

    kindKey() {
      return name(kindName);
    },

    arityKey(innerCtx, normObj) {
      if (normObj && normObj.kind === KIND.RECORD && Array.isArray(normObj.fields)) {
        return nat(BigInt(normObj.fields.length));
      }

      if (normObj && Array.isArray(normObj.items)) {
        return nat(BigInt(normObj.items.length));
      }

      return nat(0n);
    },

    modeKey() {
      return name(MODE.STRUCT);
    },

    payloadKey(innerCtx, normObj) {
      return digestObject0(innerCtx, normObj);
    },
  });

  return ctx.schemas.get(key);
}

export function installTruthEvalSchema(ctx, packageId, schemaId) {
  const key = `${packageId}:${schemaId}`;

  if (!ctx.schemas) {
    ctx.schemas = new Map();
  }

  ctx.schemas.set(key, {
    normalize(innerCtx, rawObj) {
      return nf0(innerCtx, rawObj);
    },

    kindKey() {
      return name('TruthEvalKernel');
    },

    arityKey(innerCtx, normObj) {
      return digestObject0(innerCtx, normObj);
    },

    modeKey() {
      return name(MODE.FULL);
    },

    semanticKey() {
      return name('TruthEvalKernelSemantic');
    },

    payloadKey(innerCtx, normObj) {
      return digestObject0(innerCtx, normObj);
    },
  });

  return ctx.schemas.get(key);
}
export function Parse0(inputBytes) {
  const parsed = parseVerifierFrag0ScalarBytes0(inputBytes);

  if (parsed.tag === 'reject') {
    return parsed;
  }

  return parsed.value;
}

export function Encode0(value) {
  if (!value || typeof value !== 'object') {
    throw new TypeError('Encode0 expects a tagged object');
  }

  const tag = String(value.tag ?? value.kind ?? '').trim().toLowerCase();

  if (tag === 'nat') {
    return encodeNat0(BigInt(value.value));
  }

  if (tag === 'int') {
    return encodeInt0(BigInt(value.value));
  }

  if (tag === 'name') {
    return encodeName0(String(value.value));
  }

  if (tag === 'bytes') {
    return encodeBytes0(value.value);
  }

  throw new TypeError(`Encode0 does not know how to encode tag ${String(value.tag ?? value.kind)}`);
}

export function DigestObject0(value) {
  const canonical = verifierFrag0StableString0(value);
  const hex = createHash('sha256').update(canonical, 'utf8').digest('hex');

  return {
    tag: 'Digest0',
    alg: 'SHA256',
    bytes: 'canonical-json-v0',
    hex,
  };
}

export function ComputeRowKey0(row) {
  const material = verifierFrag0RowKeyMaterial0(row);
  const hex = createHash('sha256')
    .update(verifierFrag0StableString0(material), 'utf8')
    .digest('hex');

  return {
    tag: 'RowKey0',
    alg: 'SHA256',
    material,
    hex,
  };
}

export function CheckRowKey0(row, rowKey) {
  if (!row || typeof row !== 'object' || Array.isArray(row)) {
    return verifierFrag0Reject0('Type.Row.Shape', [], {
      reason: 'row must be an object',
    });
  }

  if (!Number.isInteger(row.ArityKey) || row.ArityKey < 0) {
    return verifierFrag0Reject0('Type.RowKeyArity', ['ArityKey'], {
      expected: 'non-negative integer',
      actual: row.ArityKey,
    });
  }

  const expected = ComputeRowKey0(row);

  if (verifierFrag0StableString0(expected) !== verifierFrag0StableString0(rowKey)) {
    return verifierFrag0Reject0('RowKey.Mismatch', ['RowKey'], {
      expected,
      actual: rowKey,
    });
  }

  return verifierFrag0Accept0({
    checker: 'CheckRowKey0',
    rowKey: expected,
  });
}

export function CheckDuplicateRows0(ctxOrRows, maybeRows) {
  const rows = maybeRows === undefined ? ctxOrRows : maybeRows;

  if (Array.isArray(rows)) {
    const seen = new Map();

    for (let index = 0; index < rows.length; index += 1) {
      const row = rows[index];
      const key = verifierFrag0StableString0(
        row && typeof row === 'object' && 'RowKey' in row
          ? row.RowKey
          : ComputeRowKey0(row)
      );

      const route = row && typeof row === 'object'
        ? row.SelectedRoute ?? row.selectedRoute ?? row.route ?? null
        : null;

      if (seen.has(key)) {
        const previous = seen.get(key);

        if (verifierFrag0StableString0(previous.route) !== verifierFrag0StableString0(route)) {
          return verifierFrag0Reject0('Row.DuplicateConflict', ['rows', index], {
            previousIndex: previous.index,
            index,
            rowKey: row && typeof row === 'object' ? row.RowKey : key,
            previousRoute: previous.route,
            route,
          });
        }
      } else {
        seen.set(key, {
          index,
          route,
        });
      }
    }

    return verifierFrag0Accept0({
      checker: 'CheckDuplicateRows0',
      rowCount: rows.length,
    });
  }

  return verifierFrag0FromCoreResult0(checkDuplicateRows0(ctxOrRows, maybeRows));
}

export function CheckModeUse0(modeOrRecord, maybeConsumerKind) {
  let eqMode = modeOrRecord;
  let consumerKind = maybeConsumerKind;

  if (
    maybeConsumerKind === undefined &&
    modeOrRecord !== null &&
    typeof modeOrRecord === 'object' &&
    !Array.isArray(modeOrRecord)
  ) {
    eqMode =
      modeOrRecord.eqMode ??
      modeOrRecord.mode ??
      modeOrRecord.equalityKind;

    consumerKind =
      modeOrRecord.consumerKind ??
      modeOrRecord.consumer ??
      modeOrRecord.consumedAs ??
      modeOrRecord.use;
  }

  const normalizedMode = verifierFrag0NormalizeMode0(eqMode);
  const normalizedConsumer = verifierFrag0NormalizeConsumer0(consumerKind);

  const coreResult = checkModeUse0(normalizedMode, normalizedConsumer);
  const converted = verifierFrag0FromCoreResult0(coreResult);

  if (
    converted.tag === 'accept' &&
    normalizedMode === MODE.QUOT &&
    normalizedConsumer === 'replacement-equality'
  ) {
    return verifierFrag0Reject0('Mode.QuotientAsReplacementEquality', ['mode'], {
      mode: normalizedMode,
      consumerKind: normalizedConsumer,
    });
  }

  return converted;
}

export function CheckNoHiddenMin0(ctxOrAst, maybeAst) {
  const ast = maybeAst === undefined ? ctxOrAst : maybeAst;
  const hit = verifierFrag0FindForbiddenExecutableSymbol0(ast);

  if (hit !== null) {
    return verifierFrag0Reject0('HiddenMin.ExecCall', hit.path, {
      symbol: hit.symbol,
    });
  }

  if (maybeAst === undefined) {
    return verifierFrag0FromCoreResult0(checkNoHiddenMin0({}, ast));
  }

  return verifierFrag0FromCoreResult0(checkNoHiddenMin0(ctxOrAst, maybeAst));
}

function parseVerifierFrag0ScalarBytes0(inputBytes) {
  const bytes = toUint8Array(inputBytes);

  if (bytes.length < 4) {
    return verifierFrag0Reject0('Parse.Truncated', [], {
      need: 4,
      actual: bytes.length,
    });
  }

  const len =
    bytes[0] * 2 ** 24 +
    bytes[1] * 2 ** 16 +
    bytes[2] * 2 ** 8 +
    bytes[3];

  const available = bytes.length - 4;

  if (available < len) {
    return verifierFrag0Reject0('Parse.Truncated', [], {
      len,
      available,
    });
  }

  if (available > len) {
    return verifierFrag0Reject0('Parse.TrailingBytes', [], {
      pos: 4 + len,
      limit: bytes.length,
    });
  }

  if (len === 0) {
    return {
      tag: 'accept',
      value: {
        tag: 'nat',
        value: 0,
      },
    };
  }

  const magnitude = bytes.slice(4, 4 + len);

  if (magnitude[0] === 0) {
    return verifierFrag0Reject0('Parse.Nat.NonCanonicalLeadingZero', [], {
      len,
    });
  }

  let decoded = null;

  try {
    decoded = utf8Decoder.decode(magnitude);
  } catch {
    return verifierFrag0Reject0('Parse.Name.InvalidUTF8', [], {
      len,
    });
  }

  if (decoded.normalize('NFC') !== decoded) {
    return verifierFrag0Reject0('Parse.Name.NonCanonicalForm', [], {
      decoded,
    });
  }

  if (/^[\x20-\x7e]*$/.test(decoded) && /[A-Za-z_./:-]/.test(decoded)) {
    return {
      tag: 'accept',
      value: {
        tag: 'name',
        value: decoded,
      },
    };
  }

  let n = 0n;

  for (const byte of magnitude) {
    n = (n << 8n) + BigInt(byte);
  }

  return {
    tag: 'accept',
    value: {
      tag: 'nat',
      value: Number(n),
    },
  };
}

function verifierFrag0RowKeyMaterial0(row) {
  if (!row || typeof row !== 'object' || Array.isArray(row)) {
    return {
      malformed: true,
      value: row,
    };
  }

  return {
    PackageID: row.PackageID ?? null,
    SchemaID: row.SchemaID ?? null,
    KindKey: row.KindKey ?? null,
    ArityKey: row.ArityKey ?? null,
    ModeKey: row.ModeKey ?? null,
    FrontKey: row.FrontKey ?? null,
    SemanticKey: row.SemanticKey ?? null,
    IncidenceKey: row.IncidenceKey ?? null,
    DependencyKey: row.DependencyKey ?? null,
    ProfileKey: row.ProfileKey ?? null,
    ChargeKey: row.ChargeKey ?? null,
    ObligationKey: row.ObligationKey ?? null,
    BudgetKey: row.BudgetKey ?? null,
    ActivationKey: row.ActivationKey ?? null,
    RankKey: row.RankKey ?? null,
    PayloadKey: row.PayloadKey ?? null,
  };
}

function verifierFrag0FromCoreResult0(result) {
  if (result && typeof result === 'object') {
    const kind = String(result.kind ?? result.tag ?? '').trim().toLowerCase();

    if (kind === RESULT.ERR || kind === 'err' || kind === 'reject') {
      return verifierFrag0Reject0(result.coord ?? 'Core.Reject', result.path ?? [], {
        result,
      });
    }

    if (kind === RESULT.OK || kind === 'ok' || kind === 'accept') {
      return verifierFrag0Accept0({
        result,
      });
    }
  }

  return verifierFrag0Accept0({
    result,
  });
}

function verifierFrag0Accept0(value = {}) {
  return {
    tag: 'accept',
    kind: 'accept',
    value,
  };
}

function verifierFrag0Reject0(coord, path = [], witness = null) {
  return {
    tag: 'reject',
    kind: 'reject',
    coord,
    path,
    witness,
  };
}

function verifierFrag0NormalizeMode0(value) {
  if (typeof value !== 'string') {
    return value;
  }

  const normalized = value.trim().toLowerCase();

  if (
    normalized === 'quot' ||
    normalized === 'quotient' ||
    normalized === 'quotequality' ||
    normalized === 'quotient-equality'
  ) {
    return MODE.QUOT;
  }

  if (
    normalized === 'full' ||
    normalized === 'fullequality' ||
    normalized === 'full-equality' ||
    normalized === 'replacement'
  ) {
    return MODE.FULL;
  }

  return value;
}

function verifierFrag0NormalizeConsumer0(value) {
  if (typeof value !== 'string') {
    return value;
  }

  const normalized = value.trim().toLowerCase();

  if (
    normalized === 'replacement' ||
    normalized === 'replacement-equality' ||
    normalized === 'replacementequality' ||
    normalized === 'full-replacement'
  ) {
    return 'replacement-equality';
  }

  return normalized;
}

function verifierFrag0FindForbiddenExecutableSymbol0(value, path = []) {
  const forbidden = new Set([
    'µ',
    'µ*',
    'µ#',
    'Can',
    'argmin',
    'maxG',
    'minimumEquivalent',
    'optimalCircuit',
    'exactMinSearch',
    'canonicalMinimizer',
    'maximizeGain',
  ]);

  if (typeof value === 'string') {
    return forbidden.has(value)
      ? {
          symbol: value,
          path,
        }
      : null;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = verifierFrag0FindForbiddenExecutableSymbol0(value[index], [...path, index]);

      if (hit !== null) {
        return hit;
      }
    }

    return null;
  }

  if (value && typeof value === 'object') {
    for (const key of Object.keys(value)) {
      const hit = verifierFrag0FindForbiddenExecutableSymbol0(value[key], [...path, key]);

      if (hit !== null) {
        return hit;
      }
    }
  }

  return null;
}

function verifierFrag0StableString0(value) {
  return JSON.stringify(verifierFrag0Canonical0(value, new WeakSet()));
}

function verifierFrag0Canonical0(value, stack) {
  if (value === null) {
    return null;
  }

  if (value === undefined) {
    return {
      type: 'undefined',
    };
  }

  if (typeof value === 'boolean' || typeof value === 'string') {
    return value;
  }

  if (typeof value === 'number') {
    if (Number.isNaN(value)) {
      return {
        type: 'number',
        value: 'NaN',
      };
    }

    if (value === Infinity) {
      return {
        type: 'number',
        value: 'Infinity',
      };
    }

    if (value === -Infinity) {
      return {
        type: 'number',
        value: '-Infinity',
      };
    }

    if (Object.is(value, -0)) {
      return {
        type: 'number',
        value: '-0',
      };
    }

    return value;
  }

  if (typeof value === 'bigint') {
    return {
      type: 'bigint',
      value: value.toString(10),
    };
  }

  if (value instanceof Uint8Array) {
    return {
      type: 'bytes',
      hex: Buffer.from(value).toString('hex'),
    };
  }

  if (Array.isArray(value)) {
    if (stack.has(value)) {
      return {
        type: 'cycle',
      };
    }

    stack.add(value);
    const out = value.map((entry) => verifierFrag0Canonical0(entry, stack));
    stack.delete(value);
    return out;
  }

  if (typeof value === 'object') {
    if (stack.has(value)) {
      return {
        type: 'cycle',
      };
    }

    stack.add(value);
    const out = {};

    for (const key of Object.keys(value).sort()) {
      out[key] = verifierFrag0Canonical0(value[key], stack);
    }

    stack.delete(value);
    return out;
  }

  return {
    type: typeof value,
    value: String(value),
  };
}
