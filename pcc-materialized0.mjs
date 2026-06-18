import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_FORBIDDEN_TEXT0 = Object.freeze([
  'synthetic',
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

export const MATERIALIZED_FORBIDDEN_NOTE_KEYS0 = Object.freeze([
  'note',
  'notes',
  'placeholder',
  'stub',
  'mock',
  'todo',
]);

export const MATERIALIZED_DIGEST_HEX_KEYS0 = Object.freeze([
  'hex',
  'digestHex',
  'hashHex',
  'displayedHash',
  'expectedHash',
]);

export function makeMaterializedGateConfig0(overrides = {}) {
  return {
    kind: 'MaterializedGateConfig0',
    version: CHECKER_VERSION,
    rejectSyntheticText: true,
    rejectPlaceholderNotes: true,
    rejectInvalidDigestHex: true,
    rejectOpaqueProofMaterial: true,
    ...overrides,
  };
}

export async function CheckMaterialized0(value, config = makeMaterializedGateConfig0()) {
  const checker = 'CheckMaterialized0';
  const ledger = [];

  const cfg = makeMaterializedGateConfig0(config);
  const shape = validateMaterializedConfig0(cfg);

  ledger.push({
    phase: 'config',
    status: shape.ok ? 'pass' : 'fail',
    digest: digestCanonical0(shape.nf ?? shape.witness ?? null),
  });

  if (!shape.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.config`,
      path: shape.path,
      witness: shape.witness,
      ledger,
    });
  }

  const scan = scanMaterialized0(value, cfg, []);

  ledger.push({
    phase: 'scan',
    status: scan.ok ? 'pass' : 'fail',
    digest: digestCanonical0(scan.nf ?? scan.witness ?? null),
  });

  if (!scan.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.scan`,
      path: scan.path,
      witness: scan.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'Materialized0NF',
    checker,
    version: CHECKER_VERSION,
    scanned: true,
    configDigest: digestCanonical0(cfg),
    objectDigest: digestCanonical0(value),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateMaterializedConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedGateConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedGateConfig0') {
    return validationReject0(['kind'], 'MaterializedGateConfig0 kind must be MaterializedGateConfig0 when present', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedGateConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'rejectSyntheticText',
    'rejectPlaceholderNotes',
    'rejectInvalidDigestHex',
    'rejectOpaqueProofMaterial',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedGateConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedGateConfig0NF',
  });
}

function scanMaterialized0(value, config, path) {
  if (value === null || value === undefined) {
    return validationAccept0({
      kind: 'MaterializedScanLeaf0NF',
    });
  }

  if (typeof value === 'string') {
    if (config.rejectSyntheticText) {
      const hit = firstForbiddenTextHit0(value);

      if (hit !== null) {
        return validationReject0(path, 'materialized mode rejects synthetic or placeholder text', {
          value,
          hit,
        });
      }
    }

    return validationAccept0({
      kind: 'MaterializedScanString0NF',
    });
  }

  if (
    typeof value === 'number' ||
    typeof value === 'boolean' ||
    typeof value === 'bigint'
  ) {
    return validationAccept0({
      kind: 'MaterializedScanPrimitive0NF',
    });
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const result = scanMaterialized0(value[index], config, [...path, index]);

      if (!result.ok) {
        return result;
      }
    }

    return validationAccept0({
      kind: 'MaterializedScanArray0NF',
      length: value.length,
    });
  }

  if (!isPlainObject(value)) {
    return validationAccept0({
      kind: 'MaterializedScanOther0NF',
    });
  }

  for (const key of Object.keys(value)) {
    const childPath = [...path, key];
    const normalizedKey = normalizeKey0(key);

    if (config.rejectOpaqueProofMaterial && isOpaqueProofMaterialKey0(key)) {
      return validationReject0(childPath, 'materialized mode rejects opaque proof material', {
        key,
      });
    }

    if (
      config.rejectPlaceholderNotes &&
      MATERIALIZED_FORBIDDEN_NOTE_KEYS0.includes(normalizedKey)
    ) {
      return validationReject0(childPath, 'materialized mode rejects placeholder note fields', {
        key,
        value: value[key],
      });
    }

    if (
      config.rejectInvalidDigestHex &&
      MATERIALIZED_DIGEST_HEX_KEYS0.includes(key) &&
      typeof value[key] === 'string' &&
      !isSha256Hex0(value[key])
    ) {
      return validationReject0(childPath, 'materialized mode requires SHA256 hex digest fields to be concrete', {
        key,
        value: value[key],
      });
    }

    const result = scanMaterialized0(value[key], config, childPath);

    if (!result.ok) {
      return result;
    }
  }

  return validationAccept0({
    kind: 'MaterializedScanObject0NF',
    keyCount: Object.keys(value).length,
  });
}

function firstForbiddenTextHit0(value) {
  const normalized = value.toLowerCase();

  for (const hit of MATERIALIZED_FORBIDDEN_TEXT0) {
    if (normalized.includes(hit)) {
      return hit;
    }
  }

  return null;
}

function normalizeKey0(key) {
  return String(key).replace(/[_\-\s]/g, '').toLowerCase();
}

function isOpaqueProofMaterialKey0(key) {
  const normalized = normalizeKey0(key);

  return (
    normalized === 'opaqueproof' ||
    normalized === 'opaqueproofblob' ||
    normalized === 'proofblob' ||
    normalized === 'trustedblob' ||
    normalized === 'trustedproofblob' ||
    normalized === 'assumeproof'
  );
}

function isSha256Hex0(value) {
  return /^[0-9a-f]{64}$/.test(value);
}

function makeAcceptRecord({
  checker,
  nf,
  ledger,
}) {
  const digest = digestCanonical0(nf);

  return {
    tag: 'accept',
    kind: 'accept',
    checker,
    version: CHECKER_VERSION,
    NF: nf,
    Digest: digest,
    Ledger: ledger,
    nf,
    digest,
    ledger,
  };
}

function makeRejectRecord({
  checker,
  coord,
  path,
  witness,
  ledger,
}) {
  const rejectNF = {
    kind: `${checker}RejectNF`,
    checker,
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
    checker,
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

function validationAccept0(nf) {
  return {
    ok: true,
    nf,
  };
}

function validationReject0(path, reason, detail) {
  return {
    ok: false,
    path,
    witness: {
      reason,
      detail,
    },
  };
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}