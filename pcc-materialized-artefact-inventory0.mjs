import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  PCCPACK_REQUIRED_FIELDS0,
} from './pcc-pack-sufficiency0.mjs';

import {
  LoadMaterializedPCCPackShellFile0,
} from './pcc-materialized-loader0.mjs';

import {
  CheckMaterializedPhaseManifest0,
  makeMaterializedPhaseManifestShell0,
} from './pcc-materialized-phase-manifest0.mjs';

import {
  sha256Utf8DigestRecord0,
} from './pcc-materialized-pack0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_ARTEFACT_REQUIRED_SEAL_FIELDS0 = Object.freeze([
  'kind',
  'version',
  'artefactName',
  'materialized',
  'canonicalByteEquality',
  'digest',
]);

export function makeMaterializedArtefactRecord0(artefactName, overrides = {}) {
  if (typeof artefactName !== 'string' || artefactName.length === 0) {
    throw new TypeError('makeMaterializedArtefactRecord0 requires a non-empty artefactName');
  }

  const material = {
    kind: `${artefactName}MaterializedArtefact0`,
    version: CHECKER_VERSION,
    artefactName,
    materialized: true,
    canonicalByteEquality: true,
    proofStatus: 'external-required',
    checkStatus: 'pending-real-certificate',
  };

  return {
    ...material,
    digest: sha256Utf8DigestRecord0(stableStringify0(material)),
    ...overrides,
  };
}

export function makeMaterializedArtefactInventoryShell0(overrides = {}) {
  const shell = makeMaterializedPhaseManifestShell0();
  const packObject = JSON.parse(shell.PackBytes);

  for (const artefactName of PCCPACK_REQUIRED_FIELDS0) {
    if (artefactName === 'Core' || artefactName === 'Manifest') {
      continue;
    }

    packObject[artefactName] = makeMaterializedArtefactRecord0(artefactName);
  }

  shell.PackBytes = stableStringify0(packObject);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  return {
    ...shell,
    ...overrides,
  };
}

export async function CheckMaterializedArtefactInventory0(shell, config = {}) {
  const checker = 'CheckMaterializedArtefactInventory0';
  const ledger = [];

  const manifestRecord = await CheckMaterializedPhaseManifest0(shell, config.phaseManifestConfig ?? {});
  const manifestResult = recordToValidation0(manifestRecord, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedPhaseManifest0',
    status: manifestResult.ok ? 'pass' : 'fail',
    digest: manifestRecord.Digest ?? manifestRecord.digest ?? digestCanonical0(manifestRecord),
  });

  if (!manifestResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.manifest`,
      path: manifestResult.path,
      witness: manifestResult.witness,
      ledger,
    });
  }

  const packObject = manifestRecord.PackObject;
  const coreObject = manifestRecord.CoreObject;
  const manifest = manifestRecord.Manifest;

  const packBoundary = validateNoAcceptRunInPack0(packObject, coreObject);

  ledger.push({
    phase: 'packBoundary',
    status: packBoundary.ok ? 'pass' : 'fail',
    digest: digestCanonical0(packBoundary.nf ?? packBoundary.witness ?? null),
  });

  if (!packBoundary.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.packBoundary`,
      path: packBoundary.path,
      witness: packBoundary.witness,
      ledger,
    });
  }

  const inventory = validateArtefactInventory0(packObject, manifest);

  ledger.push({
    phase: 'artefactInventory',
    status: inventory.ok ? 'pass' : 'fail',
    digest: digestCanonical0(inventory.nf ?? inventory.witness ?? null),
  });

  if (!inventory.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.artefactInventory`,
      path: inventory.path,
      witness: inventory.witness,
      ledger,
    });
  }

  const sealCheck = validateArtefactSeals0(packObject, manifest);

  ledger.push({
    phase: 'artefactSeals',
    status: sealCheck.ok ? 'pass' : 'fail',
    digest: digestCanonical0(sealCheck.nf ?? sealCheck.witness ?? null),
  });

  if (!sealCheck.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.artefactSeals`,
      path: sealCheck.path,
      witness: sealCheck.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedArtefactInventory0NF',
    checker,
    version: CHECKER_VERSION,
    artefactCount: manifest.requiredArtefacts.length,
    artefacts: manifest.requiredArtefacts,
    packDigest: shell.PackDigest,
    manifestDigest: digestCanonical0(manifest),
    packObjectDigest: digestCanonical0(packObject),
    coreObjectDigest: digestCanonical0(coreObject),
    artefactDigests: manifest.requiredArtefacts.map((artefactName) => ({
      artefactName,
      digest: digestCanonical0(packObject[artefactName]),
      seal: artefactSeal0(packObject[artefactName]),
    })),
  };

  return {
    ...makeAcceptRecord({
      checker,
      nf,
      ledger,
    }),
    Manifest: manifest,
    CoreObject: coreObject,
    PackObject: packObject,
    manifest,
    coreObject,
    packObject,
  };
}

export async function CheckMaterializedArtefactInventoryFile0(filePath, config = {}) {
  const checker = 'CheckMaterializedArtefactInventoryFile0';
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

  const checked = await CheckMaterializedArtefactInventory0(loaded.Shell, config);
  const checkResult = recordToValidation0(checked, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedArtefactInventory0',
    status: checkResult.ok ? 'pass' : 'fail',
    digest: checked.Digest ?? checked.digest ?? digestCanonical0(checked),
  });

  if (!checkResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.inventory`,
      path: checkResult.path,
      witness: checkResult.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedArtefactInventoryFile0NF',
    checker,
    version: CHECKER_VERSION,
    filePath: loaded.NF.filePath,
    byteLength: loaded.NF.byteLength,
    fileDigest: loaded.NF.fileDigest,
    inventoryDigest: checked.Digest ?? checked.digest,
    artefactCount: checked.NF.artefactCount,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateNoAcceptRunInPack0(packObject, coreObject) {
  if (containsAcceptRun0(coreObject)) {
    return validationReject0(['Core'], 'Core artefact must not contain AcceptRun', null);
  }

  if (Object.prototype.hasOwnProperty.call(packObject, 'AcceptRun')) {
    return validationReject0(['PackBytes', 'AcceptRun'], 'PackBytes must not contain AcceptRun as a package artefact', null);
  }

  if (Object.prototype.hasOwnProperty.call(packObject, 'AcceptRun0')) {
    return validationReject0(['PackBytes', 'AcceptRun0'], 'PackBytes must not contain AcceptRun0 as a package artefact', null);
  }

  return validationAccept0({
    kind: 'MaterializedPackBoundary0NF',
  });
}

function validateArtefactInventory0(packObject, manifest) {
  if (!isPlainObject(packObject)) {
    return validationReject0(['PackBytes'], 'PackBytes must decode to an object', {
      actual: typeof packObject,
    });
  }

  if (!isPlainObject(manifest)) {
    return validationReject0(['PackBytes', 'Manifest'], 'Pack.Manifest must be an object', {
      actual: typeof manifest,
    });
  }

  if (!Array.isArray(manifest.requiredArtefacts)) {
    return validationReject0(['PackBytes', 'Manifest', 'requiredArtefacts'], 'Pack.Manifest requiredArtefacts must be an array', {
      actual: typeof manifest.requiredArtefacts,
    });
  }

  const seen = new Set();

  for (let index = 0; index < manifest.requiredArtefacts.length; index += 1) {
    const artefactName = manifest.requiredArtefacts[index];

    if (typeof artefactName !== 'string' || artefactName.length === 0) {
      return validationReject0(['PackBytes', 'Manifest', 'requiredArtefacts', index], 'required artefact name must be a non-empty string', {
        actual: artefactName,
      });
    }

    if (seen.has(artefactName)) {
      return validationReject0(['PackBytes', 'Manifest', 'requiredArtefacts', index], 'required artefact names must be unique', {
        artefactName,
      });
    }

    seen.add(artefactName);

    if (!Object.prototype.hasOwnProperty.call(packObject, artefactName)) {
      return validationReject0(['PackBytes', artefactName], 'PackBytes is missing a required top-level artefact', {
        artefactName,
      });
    }

    if (!isPlainObject(packObject[artefactName])) {
      return validationReject0(['PackBytes', artefactName], 'required top-level artefact must be an object', {
        artefactName,
        actual: typeof packObject[artefactName],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedArtefactInventoryShape0NF',
    artefactCount: manifest.requiredArtefacts.length,
  });
}

function validateArtefactSeals0(packObject, manifest) {
  for (const artefactName of manifest.requiredArtefacts) {
    const artefact = packObject[artefactName];

    if (artefactName === 'Core') {
      continue;
    }

    if (artefactName === 'Manifest') {
      continue;
    }

    for (const field of MATERIALIZED_ARTEFACT_REQUIRED_SEAL_FIELDS0) {
      if (!Object.prototype.hasOwnProperty.call(artefact, field)) {
        return validationReject0(['PackBytes', artefactName, field], 'materialized artefact object is missing a required seal field', {
          artefactName,
          field,
        });
      }
    }

    if (typeof artefact.kind !== 'string' || artefact.kind.length === 0) {
      return validationReject0(['PackBytes', artefactName, 'kind'], 'materialized artefact kind must be a non-empty string', {
        artefactName,
        actual: artefact.kind,
      });
    }

    if (artefact.version !== CHECKER_VERSION) {
      return validationReject0(['PackBytes', artefactName, 'version'], `materialized artefact version must be ${CHECKER_VERSION}`, {
        artefactName,
        actual: artefact.version,
      });
    }

    if (artefact.artefactName !== artefactName) {
      return validationReject0(['PackBytes', artefactName, 'artefactName'], 'materialized artefact name mismatch', {
        expected: artefactName,
        actual: artefact.artefactName,
      });
    }

    if (artefact.materialized !== true) {
      return validationReject0(['PackBytes', artefactName, 'materialized'], 'materialized artefact must certify materialized=true', {
        artefactName,
        actual: artefact.materialized,
      });
    }

    if (artefact.canonicalByteEquality !== true) {
      return validationReject0(['PackBytes', artefactName, 'canonicalByteEquality'], 'materialized artefact must certify canonicalByteEquality=true', {
        artefactName,
        actual: artefact.canonicalByteEquality,
      });
    }

    if (!isDigestRecord0(artefact.digest)) {
      return validationReject0(['PackBytes', artefactName, 'digest'], 'materialized artefact digest must be a concrete SHA256 digest record', {
        artefactName,
        actual: artefact.digest,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedArtefactSeals0NF',
    artefactCount: manifest.requiredArtefacts.length,
  });
}

function artefactSeal0(artefact) {
  if (isPlainObject(artefact) && isDigestRecord0(artefact.digest)) {
    return artefact.digest;
  }

  return null;
}

function isDigestRecord0(value) {
  return (
    isPlainObject(value) &&
    value.alg === 'SHA256' &&
    typeof value.hex === 'string' &&
    /^[0-9a-f]{64}$/.test(value.hex)
  );
}

function containsAcceptRun0(value) {
  if (value === null || value === undefined) {
    return false;
  }

  if (typeof value === 'string') {
    return value === 'AcceptRun' || value === 'AcceptRun0';
  }

  if (Array.isArray(value)) {
    return value.some((entry) => containsAcceptRun0(entry));
  }

  if (!isPlainObject(value)) {
    return false;
  }

  for (const key of Object.keys(value)) {
    if (key === 'AcceptRun' || key === 'AcceptRun0') {
      return true;
    }

    if (containsAcceptRun0(value[key])) {
      return true;
    }
  }

  return false;
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