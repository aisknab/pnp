import assert from 'node:assert/strict';

function jsonReplacer(_key, value) {
  return typeof value === 'bigint' ? value.toString() : value;
}

export function expectAccept(record, {
  checker,
  inspect = () => ({}),
} = {}) {
  assert.equal(record?.tag, 'accept', JSON.stringify(record, jsonReplacer, 2));
  if (checker) assert.equal(record.checker, checker);
  return {
    status: 'accept',
    checker: record.checker ?? null,
    ...inspect(record),
  };
}

export function expectReject(record, {
  checker,
  coord,
  path,
  reason,
} = {}) {
  assert.equal(record?.tag, 'reject', JSON.stringify(record, jsonReplacer, 2));
  if (checker) assert.equal(record.checker, checker);
  if (coord) assert.equal(record.Coord, coord);
  if (path) assert.deepEqual(record.Path, path);
  if (reason) assert.equal(record.Witness?.reason, reason);
  return {
    status: 'reject',
    checker: record.checker ?? null,
    coord: record.Coord ?? null,
    path: record.Path ?? null,
    reason: record.Witness?.reason ?? null,
  };
}

export function expectCoreOk(result, inspect = () => ({})) {
  assert.equal(result?.kind, 'ok', JSON.stringify(result, jsonReplacer, 2));
  return {
    status: 'ok',
    ...inspect(result),
  };
}

export function expectCoreErr(result, {
  coord,
  path,
  inspect = () => ({}),
} = {}) {
  assert.equal(result?.kind, 'err', JSON.stringify(result, jsonReplacer, 2));
  if (coord) assert.equal(result.coord, coord);
  if (path) assert.deepEqual(result.path, path);
  return {
    status: 'err',
    coord: result.coord ?? null,
    path: result.path ?? null,
    witness: result.witness ?? null,
    ...inspect(result),
  };
}

export function printExample({
  id,
  concept,
  humanInput,
  expectedCertificate,
  passingCase,
  failingCase,
  proves,
  doesNotProve,
}) {
  process.stdout.write(`${JSON.stringify({
    id,
    concept,
    humanInput,
    expectedCertificate,
    passingCase,
    failingCase,
    proves,
    doesNotProve,
  }, jsonReplacer, 2)}\n`);
}
