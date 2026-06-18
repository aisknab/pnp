import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  LoadMaterializedPCCPackShellFile0,
} from './pcc-materialized-loader0.mjs';

import {
  CheckMaterializedProofRefs0,
  makeMaterializedProofRefShell0,
} from './pcc-materialized-proof-refs0.mjs';

import {
  sha256Utf8DigestRecord0,
} from './pcc-materialized-pack0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_BOUNDS_POLICY0 = Object.freeze({
  kind: 'MaterializedBoundsPolicy0',
  version: CHECKER_VERSION,
  finite: true,
  polynomial: true,
  publicSchedule: true,
  noPrivateSchedule: true,
  dependencyBoundsPublic: true,
  globalExponent: 64,
});

export const MATERIALIZED_BOUNDS_REQUIRED_FIELDS0 = Object.freeze([
  'kind',
  'version',
  'artefactName',
  'finite',
  'polynomial',
  'publicSchedule',
  'noPrivateSchedule',
  'exponent',
  'dependencyBoundRefs',
  'scheduleRef',
  'digest',
]);

export function makeMaterializedArtefactBounds0({
  artefactName,
  exponent,
  dependencyBoundRefs = [],
  scheduleRef = 'MaterializedPublicSchedule0',
  overrides = {},
}) {
  if (typeof artefactName !== 'string' || artefactName.length === 0) {
    throw new TypeError('makeMaterializedArtefactBounds0 requires a non-empty artefactName');
  }

  if (!Number.isInteger(exponent) || exponent <= 0) {
    throw new TypeError('makeMaterializedArtefactBounds0 requires a positive integer exponent');
  }

  if (!Array.isArray(dependencyBoundRefs)) {
    throw new TypeError('makeMaterializedArtefactBounds0 dependencyBoundRefs must be an array');
  }

  const material = {
    kind: 'MaterializedArtefactBounds0',
    version: CHECKER_VERSION,
    artefactName,
    finite: true,
    polynomial: true,
    publicSchedule: true,
    noPrivateSchedule: true,
    exponent,
    dependencyBoundRefs: [...dependencyBoundRefs],
    scheduleRef,
    ...overrides,
  };

  return {
    ...material,
    digest: sha256Utf8DigestRecord0(stableStringify0(material)),
  };
}

export function makeMaterializedBoundsShell0(overrides = {}) {
  const shell = makeMaterializedProofRefShell0();
  const packObject = JSON.parse(shell.PackBytes);
  const artefactOrder = packObject.Manifest.artefactOrder;
  const artefactBounds = {};

  for (let index = 0; index < artefactOrder.length; index += 1) {
    const artefactName = artefactOrder[index];
    const deps = packObject.Manifest.artefactDependencies[artefactName] ?? [];
    const bounds = makeMaterializedArtefactBounds0({
      artefactName,
      exponent: 8 + index,
      dependencyBoundRefs: deps,
    });

    artefactBounds[artefactName] = bounds;

    if (artefactName !== 'Core' && artefactName !== 'Manifest') {
      packObject[artefactName] = {
        ...packObject[artefactName],
        bounds,
      };
    }
  }

  packObject.Manifest = {
    ...packObject.Manifest,
    boundsPolicy: {
      ...MATERIALIZED_BOUNDS_POLICY0,
    },
    artefactBounds,
  };

  shell.PackBytes = stableStringify0(packObject);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  return {
    ...shell,
    ...overrides,
  };
}

export async function CheckMaterializedBounds0(shell, config = {}) {
  const checker = 'CheckMaterializedBounds0';
  const ledger = [];

  const proofRefsRecord = await CheckMaterializedProofRefs0(shell, config.proofRefsConfig ?? {});
  const proofRefs = recordToValidation0(proofRefsRecord, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedProofRefs0',
    status: proofRefs.ok ? 'pass' : 'fail',
    digest: proofRefsRecord.Digest ?? proofRefsRecord.digest ?? digestCanonical0(proofRefsRecord),
  });

  if (!proofRefs.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.proofRefs`,
      path: proofRefs.path,
      witness: proofRefs.witness,
      ledger,
    });
  }

  const manifest = proofRefsRecord.Manifest;
  const packObject = proofRefsRecord.PackObject;

  const policy = validateBoundsPolicy0(manifest);

  ledger.push({
    phase: 'boundsPolicy',
    status: policy.ok ? 'pass' : 'fail',
    digest: digestCanonical0(policy.nf ?? policy.witness ?? null),
  });

  if (!policy.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.boundsPolicy`,
      path: policy.path,
      witness: policy.witness,
      ledger,
    });
  }

  const manifestBounds = validateManifestArtefactBounds0(manifest);

  ledger.push({
    phase: 'manifestArtefactBounds',
    status: manifestBounds.ok ? 'pass' : 'fail',
    digest: digestCanonical0(manifestBounds.nf ?? manifestBounds.witness ?? null),
  });

  if (!manifestBounds.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.manifestArtefactBounds`,
      path: manifestBounds.path,
      witness: manifestBounds.witness,
      ledger,
    });
  }

  const artefactBounds = validateArtefactBounds0(packObject, manifest);

  ledger.push({
    phase: 'artefactBounds',
    status: artefactBounds.ok ? 'pass' : 'fail',
    digest: digestCanonical0(artefactBounds.nf ?? artefactBounds.witness ?? null),
  });

  if (!artefactBounds.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.artefactBounds`,
      path: artefactBounds.path,
      witness: artefactBounds.witness,
      ledger,
    });
  }

  const dependencyBounds = validateDependencyBoundRefs0(manifest);

  ledger.push({
    phase: 'dependencyBoundRefs',
    status: dependencyBounds.ok ? 'pass' : 'fail',
    digest: digestCanonical0(dependencyBounds.nf ?? dependencyBounds.witness ?? null),
  });

  if (!dependencyBounds.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.dependencyBoundRefs`,
      path: dependencyBounds.path,
      witness: dependencyBounds.witness,
      ledger,
    });
  }

  const digestCheck = validateBoundsDigests0(manifest, packObject);

  ledger.push({
    phase: 'boundsDigests',
    status: digestCheck.ok ? 'pass' : 'fail',
    digest: digestCanonical0(digestCheck.nf ?? digestCheck.witness ?? null),
  });

  if (!digestCheck.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.boundsDigests`,
      path: digestCheck.path,
      witness: digestCheck.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedBounds0NF',
    checker,
    version: CHECKER_VERSION,
    artefactCount: manifest.artefactOrder.length,
    globalExponent: manifest.boundsPolicy.globalExponent,
    boundsDigest: digestCanonical0(manifest.artefactBounds),
    manifestDigest: digestCanonical0(manifest),
    packDigest: shell.PackDigest,
    artefactBounds: manifest.artefactOrder.map((artefactName) => ({
      artefactName,
      exponent: manifest.artefactBounds[artefactName].exponent,
      dependencyBoundRefs: manifest.artefactBounds[artefactName].dependencyBoundRefs,
      digest: manifest.artefactBounds[artefactName].digest,
    })),
  };

  return {
    ...makeAcceptRecord({
      checker,
      nf,
      ledger,
    }),
    Manifest: manifest,
    PackObject: packObject,
    manifest,
    packObject,
  };
}

export async function CheckMaterializedBoundsFile0(filePath, config = {}) {
  const checker = 'CheckMaterializedBoundsFile0';
  const ledger = [];

  const loaded = await LoadMaterializedPCCPackShellFile0(filePath, config.loaderConfig ?? {});
  const loadResult = recordToValidation0(loaded, ['file']);

  ledger.push({
    phase: 'load',
    status: loadResult.ok ? 'pass' : 'fail',
    digest: loaded.Digest ?? loaded.digest ?? digestCanonical0(loaded),
  });

  if (!loadResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.load`,
      path: loadResult.path,
      witness: loadResult.witness,
      ledger,
    });
  }

  const checked = await CheckMaterializedBounds0(loaded.Shell, config);
  const checkResult = recordToValidation0(checked, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedBounds0',
    status: checkResult.ok ? 'pass' : 'fail',
    digest: checked.Digest ?? checked.digest ?? digestCanonical0(checked),
  });

  if (!checkResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.bounds`,
      path: checkResult.path,
      witness: checkResult.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedBoundsFile0NF',
    checker,
    version: CHECKER_VERSION,
    filePath: loaded.NF.filePath,
    byteLength: loaded.NF.byteLength,
    fileDigest: loaded.NF.fileDigest,
    boundsDigest: checked.Digest ?? checked.digest,
    artefactCount: checked.NF.artefactCount,
    globalExponent: checked.NF.globalExponent,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateBoundsPolicy0(manifest) {
  const policy = manifest.boundsPolicy;

  if (!isPlainObject(policy)) {
    return validationReject0(['PackBytes', 'Manifest', 'boundsPolicy'], 'Pack.Manifest boundsPolicy must be an object', {
      actual: typeof policy,
    });
  }

  if (policy.kind !== 'MaterializedBoundsPolicy0') {
    return validationReject0(['PackBytes', 'Manifest', 'boundsPolicy', 'kind'], 'boundsPolicy kind mismatch', {
      expected: 'MaterializedBoundsPolicy0',
      actual: policy.kind,
    });
  }

  if (policy.version !== CHECKER_VERSION) {
    return validationReject0(['PackBytes', 'Manifest', 'boundsPolicy', 'version'], `boundsPolicy version must be ${CHECKER_VERSION}`, {
      actual: policy.version,
    });
  }

  for (const field of [
    'finite',
    'polynomial',
    'publicSchedule',
    'noPrivateSchedule',
    'dependencyBoundsPublic',
  ]) {
    if (policy[field] !== true) {
      return validationReject0(['PackBytes', 'Manifest', 'boundsPolicy', field], `boundsPolicy must certify ${field}`, {
        actual: policy[field],
      });
    }
  }

  if (!Number.isInteger(policy.globalExponent) || policy.globalExponent <= 0) {
    return validationReject0(['PackBytes', 'Manifest', 'boundsPolicy', 'globalExponent'], 'boundsPolicy globalExponent must be a positive integer', {
      actual: policy.globalExponent,
    });
  }

  return validationAccept0({
    kind: 'MaterializedBoundsPolicy0NF',
    globalExponent: policy.globalExponent,
  });
}

function validateManifestArtefactBounds0(manifest) {
  if (!isPlainObject(manifest.artefactBounds)) {
    return validationReject0(['PackBytes', 'Manifest', 'artefactBounds'], 'Pack.Manifest artefactBounds must be an object', {
      actual: typeof manifest.artefactBounds,
    });
  }

  for (const artefactName of manifest.artefactOrder) {
    if (!Object.prototype.hasOwnProperty.call(manifest.artefactBounds, artefactName)) {
      return validationReject0(['PackBytes', 'Manifest', 'artefactBounds', artefactName], 'Pack.Manifest artefactBounds is missing an artefact bound', {
        artefactName,
      });
    }

    const result = validateSingleBoundsRecord0(
      manifest.artefactBounds[artefactName],
      ['PackBytes', 'Manifest', 'artefactBounds', artefactName],
      artefactName,
      manifest.boundsPolicy.globalExponent,
    );

    if (!result.ok) {
      return result;
    }
  }

  return validationAccept0({
    kind: 'MaterializedManifestArtefactBounds0NF',
    artefactCount: manifest.artefactOrder.length,
  });
}

function validateArtefactBounds0(packObject, manifest) {
  for (const artefactName of manifest.artefactOrder) {
    if (artefactName === 'Core' || artefactName === 'Manifest') {
      continue;
    }

    const artefact = packObject[artefactName];

    if (!isPlainObject(artefact)) {
      return validationReject0(['PackBytes', artefactName], 'materialized artefact must be an object before bounds checking', {
        artefactName,
        actual: typeof artefact,
      });
    }

    if (!Object.prototype.hasOwnProperty.call(artefact, 'bounds')) {
      return validationReject0(['PackBytes', artefactName, 'bounds'], 'materialized artefact must declare bounds', {
        artefactName,
      });
    }

    const result = validateSingleBoundsRecord0(
      artefact.bounds,
      ['PackBytes', artefactName, 'bounds'],
      artefactName,
      manifest.boundsPolicy.globalExponent,
    );

    if (!result.ok) {
      return result;
    }

    if (stableStringify0(artefact.bounds) !== stableStringify0(manifest.artefactBounds[artefactName])) {
      return validationReject0(['PackBytes', artefactName, 'bounds'], 'materialized artefact bounds must match Pack.Manifest artefactBounds', {
        artefactName,
        expected: manifest.artefactBounds[artefactName],
        actual: artefact.bounds,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedArtefactBounds0NF',
  });
}

function validateSingleBoundsRecord0(bounds, path, artefactName, globalExponent) {
  if (!isPlainObject(bounds)) {
    return validationReject0(path, 'materialized bounds record must be an object', {
      artefactName,
      actual: typeof bounds,
    });
  }

  for (const field of MATERIALIZED_BOUNDS_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(bounds, field)) {
      return validationReject0([...path, field], 'materialized bounds record is missing a required field', {
        artefactName,
        field,
      });
    }
  }

  if (bounds.kind !== 'MaterializedArtefactBounds0') {
    return validationReject0([...path, 'kind'], 'materialized bounds kind mismatch', {
      artefactName,
      actual: bounds.kind,
    });
  }

  if (bounds.version !== CHECKER_VERSION) {
    return validationReject0([...path, 'version'], `materialized bounds version must be ${CHECKER_VERSION}`, {
      artefactName,
      actual: bounds.version,
    });
  }

  if (bounds.artefactName !== artefactName) {
    return validationReject0([...path, 'artefactName'], 'materialized bounds artefactName mismatch', {
      expected: artefactName,
      actual: bounds.artefactName,
    });
  }

  for (const field of [
    'finite',
    'polynomial',
    'publicSchedule',
    'noPrivateSchedule',
  ]) {
    if (bounds[field] !== true) {
      return validationReject0([...path, field], `materialized bounds must certify ${field}`, {
        artefactName,
        actual: bounds[field],
      });
    }
  }

  if (!Number.isInteger(bounds.exponent) || bounds.exponent <= 0) {
    return validationReject0([...path, 'exponent'], 'materialized bounds exponent must be a positive integer', {
      artefactName,
      actual: bounds.exponent,
    });
  }

  if (bounds.exponent > globalExponent) {
    return validationReject0([...path, 'exponent'], 'materialized bounds exponent must not exceed globalExponent', {
      artefactName,
      exponent: bounds.exponent,
      globalExponent,
    });
  }

  if (!Array.isArray(bounds.dependencyBoundRefs)) {
    return validationReject0([...path, 'dependencyBoundRefs'], 'materialized bounds dependencyBoundRefs must be an array', {
      artefactName,
      actual: typeof bounds.dependencyBoundRefs,
    });
  }

  if (typeof bounds.scheduleRef !== 'string' || bounds.scheduleRef.length === 0) {
    return validationReject0([...path, 'scheduleRef'], 'materialized bounds scheduleRef must be a non-empty string', {
      artefactName,
      actual: bounds.scheduleRef,
    });
  }

  if (!isDigestRecord0(bounds.digest)) {
    return validationReject0([...path, 'digest'], 'materialized bounds digest must be a concrete SHA256 digest record', {
      artefactName,
      actual: bounds.digest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedSingleBoundsRecord0NF',
    artefactName,
    exponent: bounds.exponent,
  });
}

function validateDependencyBoundRefs0(manifest) {
  const orderIndex = new Map(manifest.artefactOrder.map((artefactName, index) => [artefactName, index]));

  for (const artefactName of manifest.artefactOrder) {
    const bounds = manifest.artefactBounds[artefactName];
    const expectedDeps = manifest.artefactDependencies[artefactName] ?? [];

    if (stableStringify0(bounds.dependencyBoundRefs) !== stableStringify0(expectedDeps)) {
      return validationReject0(['PackBytes', 'Manifest', 'artefactBounds', artefactName, 'dependencyBoundRefs'], 'bounds dependencyBoundRefs must match artefactDependencies', {
        artefactName,
        expected: expectedDeps,
        actual: bounds.dependencyBoundRefs,
      });
    }

    for (let index = 0; index < bounds.dependencyBoundRefs.length; index += 1) {
      const dep = bounds.dependencyBoundRefs[index];

      if (dep === 'AcceptRun' || dep === 'AcceptRun0') {
        return validationReject0(['PackBytes', 'Manifest', 'artefactBounds', artefactName, 'dependencyBoundRefs', index], 'bounds dependencyBoundRefs must not reference AcceptRun', {
          artefactName,
          dep,
        });
      }

      if (!orderIndex.has(dep)) {
        return validationReject0(['PackBytes', 'Manifest', 'artefactBounds', artefactName, 'dependencyBoundRefs', index], 'bounds dependencyBoundRefs target is unknown', {
          artefactName,
          dep,
        });
      }

      if (orderIndex.get(dep) >= orderIndex.get(artefactName)) {
        return validationReject0(['PackBytes', 'Manifest', 'artefactBounds', artefactName, 'dependencyBoundRefs', index], 'bounds dependencyBoundRefs must point to an earlier artefact', {
          artefactName,
          dep,
          artefactIndex: orderIndex.get(artefactName),
          dependencyIndex: orderIndex.get(dep),
        });
      }
    }
  }

  return validationAccept0({
    kind: 'MaterializedDependencyBoundRefs0NF',
  });
}

function validateBoundsDigests0(manifest, packObject) {
  for (const artefactName of manifest.artefactOrder) {
    const manifestBounds = manifest.artefactBounds[artefactName];
    const manifestExpected = expectedBoundsDigest0(manifestBounds);

    if (!sameDigestRecord0(manifestBounds.digest, manifestExpected)) {
      return validationReject0(['PackBytes', 'Manifest', 'artefactBounds', artefactName, 'digest'], 'manifest artefact bounds digest mismatch', {
        artefactName,
        expected: manifestExpected,
        actual: manifestBounds.digest,
      });
    }

    if (artefactName === 'Core' || artefactName === 'Manifest') {
      continue;
    }

    const artefactBounds = packObject[artefactName].bounds;
    const artefactExpected = expectedBoundsDigest0(artefactBounds);

    if (!sameDigestRecord0(artefactBounds.digest, artefactExpected)) {
      return validationReject0(['PackBytes', artefactName, 'bounds', 'digest'], 'artefact bounds digest mismatch', {
        artefactName,
        expected: artefactExpected,
        actual: artefactBounds.digest,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedBoundsDigest0NF',
  });
}

function expectedBoundsDigest0(bounds) {
  const material = {};

  for (const key of Object.keys(bounds).sort()) {
    if (key !== 'digest') {
      material[key] = bounds[key];
    }
  }

  return sha256Utf8DigestRecord0(stableStringify0(material));
}

function isDigestRecord0(value) {
  return (
    isPlainObject(value) &&
    value.alg === 'SHA256' &&
    typeof value.hex === 'string' &&
    /^[0-9a-f]{64}$/.test(value.hex)
  );
}

function sameDigestRecord0(actual, expected) {
  return (
    isPlainObject(actual) &&
    actual.alg === expected.alg &&
    actual.bytes === expected.bytes &&
    actual.hex === expected.hex
  );
}

function recordToValidation0(record, path) {
  if (isRejectRecord0(record)) {
    return validationReject0(path, `${record.checker} rejected`, {
      inner: compactReject0(record),
    });
  }

  return validationAccept0(record.NF ?? record.nf ?? record);
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

function isRejectRecord0(value) {
  return classifyRecord0(value) === 'reject';
}

function classifyRecord0(value) {
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

function compactReject0(value) {
  if (!isPlainObject(value)) {
    return value;
  }

  return {
    checker: value.checker ?? null,
    coord: value.Coord ?? value.coord ?? null,
    path: value.Path ?? value.path ?? null,
    witness: value.Witness ?? value.witness ?? null,
    digest: value.Digest ?? value.digest ?? null,
  };
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}