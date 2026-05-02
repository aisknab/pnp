import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedBoot0,
  makeMaterializedBoot0,
} from './pcc-boot-materialized0.mjs';

import {
  CheckMaterializedKBundle0,
  makeMaterializedKBundle0,
} from './pcc-k-materialized0.mjs';

import {
  CheckGlobalProofDAG0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

const CHECKER_VERSION = 0;

const MATERIALIZED_GLOBAL_DAG_FORBIDDEN_MARKERS0 = Object.freeze([
  'synthetic',
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

export function makeMaterializedGlobalProofDAGConfig0(overrides = {}) {
  return {
    kind: 'MaterializedGlobalProofDAGConfig0',
    version: CHECKER_VERSION,
    checkBoot: true,
    checkKBundle: true,
    checkGlobalDAG: true,
    rejectFixtureMarkers: true,
    ...overrides,
  };
}

export async function makeMaterializedGlobalProofDAG0({
  Boot0 = null,
  KBundle = null,
  GlobalProofDAG = null,
  overrides = {},
} = {}) {
  const materializedKBundle = KBundle ?? await makeMaterializedKBundle0();
  const materializedBoot = Boot0 ?? resolveBoot0FromKBundle0(materializedKBundle) ?? await makeMaterializedBoot0();

  const globalProofDAG = GlobalProofDAG ?? makeMaterializedGlobalProofDAGCore0({
    Boot0: materializedBoot,
    KBundle: materializedKBundle,
  });

  const linkage = {
    kind: 'MaterializedGlobalProofDAGLinkage0',
    version: CHECKER_VERSION,
    bootDigest: digestCanonical0(materializedBoot),
    kBundleDigest: digestCanonical0(materializedKBundle),
    kImplDigest: digestCanonical0(resolveKImpl0(materializedKBundle)),
    globalProofDAGDigest: digestCanonical0(globalProofDAG),
    ifaceHash: globalProofDAG.IfaceHash,
    schedHash: globalProofDAG.SchedHash,
  };

  return {
    kind: 'MaterializedGlobalProofDAG0',
    version: CHECKER_VERSION,
    Boot0: materializedBoot,
    KBundle: materializedKBundle,
    GlobalProofDAG: globalProofDAG,
    Linkage: linkage,
    PiMaterializedGlobalDAG: {
      kind: 'PiMaterializedGlobalDAG0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'Boot0',
          digest: linkage.bootDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'KBundle',
          digest: linkage.kBundleDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'GlobalProofDAG',
          digest: linkage.globalProofDAGDigest,
        },
      ],
    },
    ...overrides,
  };
}

export function makeMaterializedGlobalProofDAGCore0({
  Boot0 = null,
  KBundle = null,
  overrides = {},
} = {}) {
  const kimpl = resolveKImpl0(KBundle);
  const ifaceHash = kimpl?.IfaceHash ?? digestCanonical0(Boot0?.IfaceDict0 ?? null);
  const schedHash = kimpl?.SchedHash ?? digestCanonical0(Boot0?.Sched0 ?? null);

  return makeSyntheticGlobalProofDAG0({
    SchedHash: ifaceOrSchedDigest0(schedHash),
    IfaceHash: ifaceOrSchedDigest0(ifaceHash),
    PiGlobalDAG: {
      kind: 'PiGlobalDAG0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      proofStatus: 'materialized-global-dag',
      refs: [
        {
          target: 'KImpl',
          digest: digestCanonical0(kimpl),
        },
      ],
    },
    ...overrides,
  });
}

export async function CheckMaterializedGlobalProofDAG0(input, config = makeMaterializedGlobalProofDAGConfig0()) {
  const checker = 'CheckMaterializedGlobalProofDAG0';
  const ledger = [];
  const cfg = makeMaterializedGlobalProofDAGConfig0(config);
  const envelope = normalizeEnvelope0(input);

  const shape = validateShape0(envelope, cfg);

  ledger.push({
    phase: 'shape',
    status: shape.ok ? 'pass' : 'fail',
    digest: digestCanonical0(shape.nf ?? shape.witness ?? null),
  });

  if (!shape.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: shape.path,
      witness: shape.witness,
      ledger,
    });
  }

  if (cfg.checkBoot === true) {
    const bootRecord = await CheckMaterializedBoot0(envelope.Boot0);
    const boot = recordToValidation0(bootRecord, ['Boot0']);

    ledger.push({
      phase: 'CheckMaterializedBoot0',
      status: boot.ok ? 'pass' : 'fail',
      digest: bootRecord.Digest ?? bootRecord.digest ?? digestCanonical0(bootRecord),
    });

    if (!boot.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.Boot0`,
        path: boot.path,
        witness: boot.witness,
        ledger,
      });
    }
  }

  if (cfg.checkKBundle === true) {
    const kBundleRecord = await CheckMaterializedKBundle0(envelope.KBundle);
    const kBundle = recordToValidation0(kBundleRecord, ['KBundle']);

    ledger.push({
      phase: 'CheckMaterializedKBundle0',
      status: kBundle.ok ? 'pass' : 'fail',
      digest: kBundleRecord.Digest ?? kBundleRecord.digest ?? digestCanonical0(kBundleRecord),
    });

    if (!kBundle.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.KBundle`,
        path: kBundle.path,
        witness: kBundle.witness,
        ledger,
      });
    }
  }

  const linkage = validateLinkage0(envelope);

  ledger.push({
    phase: 'linkage',
    status: linkage.ok ? 'pass' : 'fail',
    digest: digestCanonical0(linkage.nf ?? linkage.witness ?? null),
  });

  if (!linkage.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.linkage`,
      path: linkage.path,
      witness: linkage.witness,
      ledger,
    });
  }

  if (cfg.checkGlobalDAG === true) {
    const dagRecord = await CheckGlobalProofDAG0(envelope.GlobalProofDAG);
    const dag = recordToValidation0(dagRecord, ['GlobalProofDAG']);

    ledger.push({
      phase: 'CheckGlobalProofDAG0',
      status: dag.ok ? 'pass' : 'fail',
      digest: dagRecord.Digest ?? dagRecord.digest ?? digestCanonical0(dagRecord),
    });

    if (!dag.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.GlobalProofDAG`,
        path: dag.path,
        witness: dag.witness,
        ledger,
      });
    }
  }

  if (cfg.rejectFixtureMarkers === true) {
    const markers = validateNoFixtureMarkers0(envelope.GlobalProofDAG);

    ledger.push({
      phase: 'fixtureMarkers',
      status: markers.ok ? 'pass' : 'fail',
      digest: digestCanonical0(markers.nf ?? markers.witness ?? null),
    });

    if (!markers.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.fixtureMarkers`,
        path: markers.path,
        witness: markers.witness,
        ledger,
      });
    }
  }

  const globalRecord = await CheckGlobalProofDAG0(envelope.GlobalProofDAG);
  const globalNF = globalRecord.NF ?? globalRecord.nf ?? {};

  const nf = {
    kind: 'MaterializedGlobalProofDAG0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,
    bootDigest: digestCanonical0(envelope.Boot0),
    kBundleDigest: digestCanonical0(envelope.KBundle),
    globalProofDAGDigest: globalRecord.Digest ?? globalRecord.digest,
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
    nodeCount: globalNF.nodeCount ?? envelope.GlobalProofDAG.Nodes.length,
    finalTheorems: globalNF.finalTheorems ?? [],
    ifaceHash: envelope.GlobalProofDAG.IfaceHash,
    schedHash: envelope.GlobalProofDAG.SchedHash,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeMaterializedGlobalProofDAGFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeMaterializedGlobalProofDAGFiles0 requires a non-empty output directory');
  }

  const envelope = await makeMaterializedGlobalProofDAG0(options);
  const checked = await CheckMaterializedGlobalProofDAG0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'MaterializedGlobalProofDAG0.json');
  const dagPath = path.join(outDir, 'GlobalProofDAG0.json');
  const checkPath = path.join(outDir, 'MaterializedGlobalProofDAG0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(dagPath, envelope.GlobalProofDAG);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      dagPath,
      checkPath,
    },
  };
}

function normalizeEnvelope0(input) {
  if (isPlainObject(input) && input.kind === 'GlobalProofDAG0') {
    return {
      kind: 'MaterializedGlobalProofDAG0',
      version: CHECKER_VERSION,
      Boot0: null,
      KBundle: null,
      GlobalProofDAG: input,
      Linkage: null,
    };
  }

  return input;
}

function validateShape0(envelope, config) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'MaterializedGlobalProofDAG0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'MaterializedGlobalProofDAG0') {
    return validationReject0(['kind'], 'MaterializedGlobalProofDAG0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedGlobalProofDAG0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (config.checkBoot === true && !isPlainObject(envelope.Boot0)) {
    return validationReject0(['Boot0'], 'MaterializedGlobalProofDAG0 must include Boot0 when checkBoot=true', {
      actual: typeof envelope.Boot0,
    });
  }

  if (config.checkKBundle === true && !isPlainObject(envelope.KBundle)) {
    return validationReject0(['KBundle'], 'MaterializedGlobalProofDAG0 must include KBundle when checkKBundle=true', {
      actual: typeof envelope.KBundle,
    });
  }

  if (!isPlainObject(envelope.GlobalProofDAG)) {
    return validationReject0(['GlobalProofDAG'], 'MaterializedGlobalProofDAG0 must include a GlobalProofDAG object', {
      actual: typeof envelope.GlobalProofDAG,
    });
  }

  if (!Array.isArray(envelope.GlobalProofDAG.Nodes)) {
    return validationReject0(['GlobalProofDAG', 'Nodes'], 'GlobalProofDAG Nodes must be an array', {
      actual: typeof envelope.GlobalProofDAG.Nodes,
    });
  }

  return validationAccept0({
    kind: 'MaterializedGlobalProofDAGShape0NF',
  });
}

function validateLinkage0(envelope) {
  const kimpl = resolveKImpl0(envelope.KBundle);

  if (!isPlainObject(kimpl)) {
    return validationReject0(['KBundle', 'KImpl'], 'materialized KBundle must expose KImpl for GlobalProofDAG linkage', {
      actual: typeof kimpl,
    });
  }

  if (!sameDigestHex0(envelope.GlobalProofDAG.IfaceHash, kimpl.IfaceHash)) {
    return validationReject0(['GlobalProofDAG', 'IfaceHash'], 'GlobalProofDAG IfaceHash must match materialized KImpl IfaceHash', {
      expected: kimpl.IfaceHash,
      actual: envelope.GlobalProofDAG.IfaceHash,
    });
  }

  if (!sameDigestHex0(envelope.GlobalProofDAG.SchedHash, kimpl.SchedHash)) {
    return validationReject0(['GlobalProofDAG', 'SchedHash'], 'GlobalProofDAG SchedHash must match materialized KImpl SchedHash', {
      expected: kimpl.SchedHash,
      actual: envelope.GlobalProofDAG.SchedHash,
    });
  }

  if (isPlainObject(envelope.Linkage)) {
    const expectedGlobalDigest = digestCanonical0(envelope.GlobalProofDAG);

    if (
      envelope.Linkage.globalProofDAGDigest !== undefined &&
      !sameDigestHex0(envelope.Linkage.globalProofDAGDigest, expectedGlobalDigest)
    ) {
      return validationReject0(['Linkage', 'globalProofDAGDigest'], 'Linkage globalProofDAGDigest must match GlobalProofDAG bytes', {
        expected: expectedGlobalDigest,
        actual: envelope.Linkage.globalProofDAGDigest,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedGlobalProofDAGLinkage0NF',
    ifaceHash: envelope.GlobalProofDAG.IfaceHash,
    schedHash: envelope.GlobalProofDAG.SchedHash,
  });
}

function validateNoFixtureMarkers0(value) {
  const hit = firstFixtureMarker0(value, ['GlobalProofDAG']);

  if (hit !== null) {
    return validationReject0(hit.path, 'materialized GlobalProofDAG must not contain fixture-marker text', hit);
  }

  return validationAccept0({
    kind: 'MaterializedGlobalProofDAGNoFixtureMarkers0NF',
  });
}

function firstFixtureMarker0(value, path) {
  if (value === null || value === undefined) {
    return null;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of MATERIALIZED_GLOBAL_DAG_FORBIDDEN_MARKERS0) {
      if (lower.includes(marker)) {
        return {
          path,
          marker,
          value,
        };
      }
    }

    return null;
  }

  if (
    typeof value === 'number' ||
    typeof value === 'boolean' ||
    typeof value === 'bigint'
  ) {
    return null;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = firstFixtureMarker0(value[index], [...path, index]);

      if (hit !== null) {
        return hit;
      }
    }

    return null;
  }

  if (!isPlainObject(value)) {
    return null;
  }

  for (const key of Object.keys(value)) {
    const lowerKey = key.toLowerCase();

    for (const marker of MATERIALIZED_GLOBAL_DAG_FORBIDDEN_MARKERS0) {
      if (lowerKey.includes(marker)) {
        return {
          path: [...path, key],
          marker,
          value: key,
        };
      }
    }

    const hit = firstFixtureMarker0(value[key], [...path, key]);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

async function writeJsonFile0(filePath, value) {
  await fs.writeFile(filePath, `${stableStringify0(value)}\n`, 'utf8');
}

function resolveBoot0FromKBundle0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return (
    value.Boot0 ??
    value.boot0 ??
    value.MaterializedBoot0 ??
    value.Boot ??
    value.boot ??
    null
  );
}

function resolveKImpl0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return (
    value.KImpl ??
    value.kimpl ??
    value.KBundle?.KImpl ??
    value.KBundle?.kimpl ??
    value.Bundle?.KImpl ??
    value.bundle?.KImpl ??
    null
  );
}

function ifaceOrSchedDigest0(value) {
  if (isPlainObject(value) && typeof value.hex === 'string') {
    return value;
  }

  return digestCanonical0(value);
}

function sameDigestHex0(actual, expected) {
  return (
    isPlainObject(actual) &&
    isPlainObject(expected) &&
    typeof actual.hex === 'string' &&
    typeof expected.hex === 'string' &&
    actual.hex === expected.hex &&
    (
      actual.alg === undefined ||
      expected.alg === undefined ||
      actual.alg === expected.alg
    )
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
