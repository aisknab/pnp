/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: provide the common finite audit-case harness and canonical JSON digest
 * helpers used by higher-level checkers.
 * Inputs: JavaScript audit-case descriptors and ordinary JavaScript values.
 * Outputs: deterministic accept/reject records, ledgers, canonical strings, and
 * SHA-256 metadata records.
 * Invariants enforced: unique case identifiers, declared expectation/polarity,
 * first failing case reporting, sorted object keys, and explicit canonical forms
 * for values such as BigInt, byte arrays, errors, and non-finite numbers.
 * Assumptions not checked: the mathematical truth of a case description, the
 * soundness of a callback supplied by a caller, or the cryptographic/runtime
 * correctness of Node.js SHA-256 and JSON handling.
 * Failure modes: malformed case definitions throw during construction; a suite
 * mismatch returns a reject record with a coordinate, path, witness, and ledger.
 * Naming: the suffix `0` denotes the version-zero record/checker schema; `Frag`
 * means a finite verifier fragment, not a proof of the repository's theorem.
 */

import { createHash } from 'node:crypto';

const CHECKER_ID = 'CheckVerifierFrag0';
const CHECKER_VERSION = 0;

const VALID_EXPECTATIONS = new Set(['test-pass', 'accept', 'reject']);
const VALID_POLARITIES = new Set(['positive', 'negative']);

export function makeAuditCase({
  id,
  target = 'unspecified',
  polarity = 'positive',
  expected = 'test-pass',
  description = '',
  run,
}) {
  if (!isNonEmptyString(id)) {
    throw new TypeError('VerifierFrag0 case id must be a non-empty string');
  }

  if (!VALID_POLARITIES.has(polarity)) {
    throw new TypeError(`VerifierFrag0 case ${id} has invalid polarity ${String(polarity)}`);
  }

  if (!VALID_EXPECTATIONS.has(expected)) {
    throw new TypeError(`VerifierFrag0 case ${id} has invalid expectation ${String(expected)}`);
  }

  if (typeof run !== 'function') {
    throw new TypeError(`VerifierFrag0 case ${id} must provide a run function`);
  }

  return Object.freeze({
    id,
    target,
    polarity,
    expected,
    description,
    run,
  });
}

export function makeAcceptCase({
  id,
  target = 'unspecified',
  polarity = 'positive',
  description = '',
  run,
}) {
  return makeAuditCase({
    id,
    target,
    polarity,
    expected: 'accept',
    description,
    run,
  });
}

export function makeRejectCase({
  id,
  target = 'unspecified',
  polarity = 'negative',
  description = '',
  run,
}) {
  return makeAuditCase({
    id,
    target,
    polarity,
    expected: 'reject',
    description,
    run,
  });
}

/**
 * Runs a finite suite of positive/negative audit cases.
 * Input: a `VerifierFrag0`-shaped object whose callbacks return, reject, or throw.
 * Output: an accept record if every observation matches its declared expectation;
 * otherwise a reject record for the first mismatching case.
 * Enforces: case-shape, unique IDs, declared polarity/expectation, deterministic
 * coordinates, and a ledger digest for every executed case.
 * Does not check: whether the callbacks cover a theorem or whether an accepted child
 * checker is mathematically sound.
 * Failure modes: malformed suite input or a callback result/throw inconsistent with
 * the declared expectation.
 */
export async function CheckVerifierFrag0(fragment = {}) {
  const inputCheck = validateFragmentShape(fragment);

  if (!inputCheck.ok) {
    return makeRejectRecord({
      coord: `${CHECKER_ID}.input`,
      path: inputCheck.path,
      witness: {
        reason: inputCheck.reason,
        detail: inputCheck.detail,
      },
      ledger: [],
    });
  }

  const suiteId = fragment.suiteId ?? 'VerifierFrag0';
  const cases = fragment.cases;
  const ledger = [];

  for (let index = 0; index < cases.length; index += 1) {
    const auditCase = cases[index];
    const coord = `${CHECKER_ID}.case.${String(index).padStart(4, '0')}.${safeCoord(auditCase.id)}`;
    const execution = await executeAuditCase(auditCase);

    const entry = {
      index,
      id: auditCase.id,
      target: auditCase.target,
      polarity: auditCase.polarity,
      expected: auditCase.expected,
      coord,
      status: execution.pass ? 'pass' : 'fail',
      observed: execution.observed,
      resultDigest: digestCanonical0(execution.resultForDigest),
    };

    ledger.push(entry);

    if (!execution.pass) {
      return makeRejectRecord({
        coord,
        path: ['cases', index, auditCase.id],
        witness: {
          id: auditCase.id,
          target: auditCase.target,
          polarity: auditCase.polarity,
          expected: auditCase.expected,
          observed: execution.observed,
          reason: execution.reason,
          detail: execution.detail,
        },
        ledger,
      });
    }
  }

  const nf = {
    kind: 'VerifierFrag0AuditNF',
    checker: CHECKER_ID,
    version: CHECKER_VERSION,
    suiteId,
    caseCount: cases.length,
    positiveCount: cases.filter((entry) => entry.polarity === 'positive').length,
    negativeCount: cases.filter((entry) => entry.polarity === 'negative').length,
    targets: sortedUnique(cases.map((entry) => entry.target)),
    cases: ledger,
  };

  const digest = digestCanonical0(nf);

  return {
    tag: 'accept',
    kind: 'accept',
    checker: CHECKER_ID,
    version: CHECKER_VERSION,
    NF: nf,
    Digest: digest,
    Ledger: ledger,
    nf,
    digest,
    ledger,
  };
}

async function executeAuditCase(auditCase) {
  if (auditCase.expected === 'test-pass') {
    return executeTestPassCase(auditCase);
  }

  if (auditCase.expected === 'accept') {
    return executeExpectedAcceptCase(auditCase);
  }

  if (auditCase.expected === 'reject') {
    return executeExpectedRejectCase(auditCase);
  }

  return {
    pass: false,
    observed: 'invalid-expectation',
    reason: 'invalid expectation',
    detail: auditCase.expected,
    resultForDigest: {
      expected: auditCase.expected,
    },
  };
}

async function executeTestPassCase(auditCase) {
  try {
    const value = await auditCase.run();

    if (isExplicitFailedTestResult(value)) {
      return {
        pass: false,
        observed: 'test-fail-record',
        reason: value.reason ?? 'case returned explicit test failure',
        detail: sanitizeForLedger(value),
        resultForDigest: sanitizeForLedger(value),
      };
    }

    return {
      pass: true,
      observed: 'test-pass',
      reason: 'case completed',
      detail: sanitizeForLedger(value),
      resultForDigest: sanitizeForLedger(value),
    };
  } catch (error) {
    const normalized = normalizeError(error);

    return {
      pass: false,
      observed: 'throw',
      reason: normalized.message,
      detail: normalized,
      resultForDigest: normalized,
    };
  }
}

async function executeExpectedAcceptCase(auditCase) {
  try {
    const value = await auditCase.run();

    if (isExplicitFailedTestResult(value)) {
      return {
        pass: false,
        observed: 'test-fail-record',
        reason: value.reason ?? 'case returned explicit test failure',
        detail: sanitizeForLedger(value),
        resultForDigest: sanitizeForLedger(value),
      };
    }

    const verdict = classifyVerifierVerdict(value);

    if (verdict === 'reject') {
      return {
        pass: false,
        observed: 'reject-record',
        reason: 'expected accept but observed reject',
        detail: sanitizeForLedger(value),
        resultForDigest: sanitizeForLedger(value),
      };
    }

    return {
      pass: true,
      observed: verdict === 'accept' ? 'accept-record' : 'completed-without-reject',
      reason: 'accepted',
      detail: sanitizeForLedger(value),
      resultForDigest: sanitizeForLedger(value),
    };
  } catch (error) {
    const normalized = normalizeError(error);

    return {
      pass: false,
      observed: 'throw',
      reason: normalized.message,
      detail: normalized,
      resultForDigest: normalized,
    };
  }
}

async function executeExpectedRejectCase(auditCase) {
  try {
    const value = await auditCase.run();

    if (isExplicitPassedRejectResult(value)) {
      return {
        pass: true,
        observed: 'reject-confirmed-by-test',
        reason: 'negative case confirmed rejection',
        detail: sanitizeForLedger(value),
        resultForDigest: sanitizeForLedger(value),
      };
    }

    if (isExplicitFailedTestResult(value)) {
      return {
        pass: false,
        observed: 'test-fail-record',
        reason: value.reason ?? 'case returned explicit test failure',
        detail: sanitizeForLedger(value),
        resultForDigest: sanitizeForLedger(value),
      };
    }

    const verdict = classifyVerifierVerdict(value);

    if (verdict === 'reject') {
      return {
        pass: true,
        observed: 'reject-record',
        reason: 'rejected',
        detail: sanitizeForLedger(value),
        resultForDigest: sanitizeForLedger(value),
      };
    }

    return {
      pass: false,
      observed: verdict === 'accept' ? 'accept-record' : 'completed-without-reject',
      reason: 'expected reject but operation did not reject',
      detail: sanitizeForLedger(value),
      resultForDigest: sanitizeForLedger(value),
    };
  } catch (error) {
    const normalized = normalizeError(error);

    return {
      pass: true,
      observed: 'throw',
      reason: 'throw is accepted as rejection for a negative case',
      detail: normalized,
      resultForDigest: normalized,
    };
  }
}

function validateFragmentShape(fragment) {
  if (!isPlainObject(fragment)) {
    return {
      ok: false,
      path: [],
      reason: 'fragment must be an object',
      detail: typeof fragment,
    };
  }

  if (fragment.kind !== undefined && fragment.kind !== 'VerifierFrag0') {
    return {
      ok: false,
      path: ['kind'],
      reason: 'fragment kind must be VerifierFrag0 when present',
      detail: fragment.kind,
    };
  }

  if (fragment.version !== undefined && fragment.version !== CHECKER_VERSION) {
    return {
      ok: false,
      path: ['version'],
      reason: `fragment version must be ${CHECKER_VERSION} when present`,
      detail: fragment.version,
    };
  }

  if (!Array.isArray(fragment.cases)) {
    return {
      ok: false,
      path: ['cases'],
      reason: 'fragment cases must be an array',
      detail: typeof fragment.cases,
    };
  }

  const seenIds = new Set();

  for (let index = 0; index < fragment.cases.length; index += 1) {
    const auditCase = fragment.cases[index];

    if (!isPlainObject(auditCase)) {
      return {
        ok: false,
        path: ['cases', index],
        reason: 'case must be an object',
        detail: typeof auditCase,
      };
    }

    if (!isNonEmptyString(auditCase.id)) {
      return {
        ok: false,
        path: ['cases', index, 'id'],
        reason: 'case id must be a non-empty string',
        detail: auditCase.id,
      };
    }

    if (seenIds.has(auditCase.id)) {
      return {
        ok: false,
        path: ['cases', index, 'id'],
        reason: 'case ids must be unique',
        detail: auditCase.id,
      };
    }

    seenIds.add(auditCase.id);

    if (!VALID_POLARITIES.has(auditCase.polarity)) {
      return {
        ok: false,
        path: ['cases', index, 'polarity'],
        reason: 'case polarity must be positive or negative',
        detail: auditCase.polarity,
      };
    }

    if (!VALID_EXPECTATIONS.has(auditCase.expected)) {
      return {
        ok: false,
        path: ['cases', index, 'expected'],
        reason: 'case expectation must be test-pass, accept, or reject',
        detail: auditCase.expected,
      };
    }

    if (typeof auditCase.run !== 'function') {
      return {
        ok: false,
        path: ['cases', index, 'run'],
        reason: 'case run field must be a function',
        detail: typeof auditCase.run,
      };
    }
  }

  return {
    ok: true,
  };
}

function makeRejectRecord({
  coord,
  path,
  witness,
  ledger,
}) {
  const rejectNF = {
    kind: 'VerifierFrag0RejectNF',
    checker: CHECKER_ID,
    version: CHECKER_VERSION,
    coord,
    path,
    witness,
    ledger,
  };

  const digest = digestCanonical0(rejectNF);

  return {
    tag: 'reject',
    kind: 'reject',
    checker: CHECKER_ID,
    version: CHECKER_VERSION,
    Coord: coord,
    Path: path,
    Witness: witness,
    Digest: digest,
    Ledger: ledger,
    coord,
    path,
    witness,
    digest,
    ledger,
  };
}

function classifyVerifierVerdict(value) {
  if (!isPlainObject(value)) {
    return 'unknown';
  }

  const raw =
    value.tag ??
    value.kind ??
    value.verdict ??
    value.status ??
    value.result ??
    value.outcome;

  if (typeof raw !== 'string') {
    return 'unknown';
  }

  const normalized = raw.trim().toLowerCase();

  if (
    normalized === 'accept' ||
    normalized === 'accepted' ||
    normalized === 'ok' ||
    normalized === 'pass' ||
    normalized === 'passed'
  ) {
    return 'accept';
  }

  if (
    normalized === 'reject' ||
    normalized === 'rejected' ||
    normalized === 'err' ||
    normalized === 'error' ||
    normalized === 'fail' ||
    normalized === 'failed'
  ) {
    return 'reject';
  }

  return 'unknown';
}

function isExplicitFailedTestResult(value) {
  return isPlainObject(value) && value.pass === false;
}

function isExplicitPassedRejectResult(value) {
  return (
    isPlainObject(value) &&
    value.pass === true &&
    (
      value.observed === 'reject' ||
      value.observed === 'reject-record' ||
      value.observed === 'throw' ||
      value.expected === 'reject'
    )
  );
}

/**
 * Computes SHA-256 over this module's canonical JSON representation.
 * Input: any JavaScript value supported by `canonicalize`.
 * Output: `{ alg, bytes, hex }` metadata; it is an identity/index record only.
 * Enforces: sorted object keys and explicit encodings for non-JSON primitive cases.
 * Does not check: semantic equality, theorem correctness, or collision impossibility.
 * Failure modes: underlying runtime/hash failures; cycles are represented explicitly
 * rather than recursively traversed forever.
 */
export function digestCanonical0(value) {
  const canonical = stableStringify0(value);
  const hex = createHash('sha256').update(canonical, 'utf8').digest('hex');

  return {
    alg: 'SHA256',
    bytes: 'canonical-json-v0',
    hex,
  };
}

/**
 * Serializes a JavaScript value after deterministic canonicalization.
 * Input: a supported JavaScript value.
 * Output: a JSON string with stable key order and explicit special-value records.
 * Enforces: deterministic representation within this version-zero JSON convention.
 * Does not check: compatibility with the byte codec in `pcc-core.mjs` or semantic
 * correctness of the represented object.
 * Failure modes: JSON/runtime errors for values outside the handled convention.
 */
export function stableStringify0(value) {
  return JSON.stringify(canonicalize(value, new WeakSet()));
}

function canonicalize(value, stack) {
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

  if (typeof value === 'symbol') {
    return {
      type: 'symbol',
      value: String(value.description ?? ''),
    };
  }

  if (typeof value === 'function') {
    return {
      type: 'function',
      name: value.name || 'anonymous',
    };
  }

  if (value instanceof Error) {
    return normalizeError(value);
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
    const out = value.map((entry) => canonicalize(entry, stack));
    stack.delete(value);
    return out;
  }

  if (isPlainObject(value)) {
    if (stack.has(value)) {
      return {
        type: 'cycle',
      };
    }

    stack.add(value);

    const out = {};
    for (const key of Object.keys(value).sort()) {
      out[key] = canonicalize(value[key], stack);
    }

    stack.delete(value);
    return out;
  }

  return {
    type: Object.prototype.toString.call(value),
    value: String(value),
  };
}

function normalizeError(error) {
  if (error instanceof Error) {
    return {
      name: error.name,
      message: error.message,
      code: error.code ?? null,
    };
  }

  return {
    name: 'ThrownValue',
    message: String(error),
    code: null,
  };
}

function sanitizeForLedger(value) {
  return canonicalize(value, new WeakSet());
}

function sortedUnique(values) {
  return Array.from(new Set(values.map((value) => String(value)))).sort();
}

function safeCoord(value) {
  return String(value).replace(/[^A-Za-z0-9_.:/-]/g, '_');
}

function isNonEmptyString(value) {
  return typeof value === 'string' && value.length > 0;
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}
