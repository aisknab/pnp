import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import * as publicEntry0 from './index.mjs';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

const CHECKER_VERSION = 0;
const REPO_ROOT = path.dirname(fileURLToPath(import.meta.url));

export const PUBLIC_ENTRY_EXPORT_KEYS0 = Object.freeze([
  'ACCEPT_RUN_PHASES0',
  'CheckAcceptRun0',
  'CheckIntegratedPipeline0',
  'CheckReleaseAudit0',
  'CheckRunAll0',
  'EmitFinalVerdict0',
  'INTEGRATED_PIPELINE_PHASES0',
  'RELEASE_AUDIT_REQUIRED_EXPORTS0',
  'RELEASE_AUDIT_REQUIRED_MODULES0',
  'RELEASE_AUDIT_REQUIRED_SCRIPTS0',
  'RELEASE_AUDIT_REQUIRED_TESTS0',
  'RUNALL_CHECKER_COVERAGE0',
  'RUNALL_PUBLIC_CONCLUSION0',
  'ReplayAcceptRun0',
  'RunAll0',
  'RunIntegratedPCC0',
  'makeReleaseAuditConfig0',
  'makeSyntheticAcceptRun0',
  'makeSyntheticIntegratedPipeline0',
  'makeSyntheticRejectAcceptRun0',
  'makeSyntheticRunAllInput0',
  'CheckMaterializedFinalCertificate0',
  'makeMaterializedFinalCertificate0',
  'makeMaterializedFinalCertificateConfig0',
  'writeMaterializedFinalCertificateFiles0',
  'CheckFinalCertificatePublicStatus0',
  'FINAL_CERTIFICATE_PUBLIC_STATUS_PHASES0',
  'makeFinalCertificatePublicStatus0',
  'makeFinalCertificatePublicStatusConfig0',
  'writeFinalCertificatePublicStatusFiles0',
  'CheckReleaseAuditFinalCertificateGate0',
  'RELEASE_AUDIT_FINAL_CERTIFICATE_GATE_PHASES0',
  'makeReleaseAuditFinalCertificateGate0',
  'makeReleaseAuditFinalCertificateGateConfig0',
  'writeReleaseAuditFinalCertificateGateFiles0',
].sort());

export const PUBLIC_PACKAGE_EXPORTS0 = Object.freeze({
  '.': './index.mjs',
  './accept-run0': './pcc-accept-run0.mjs',
  './integrated-pipeline0': './pcc-integrated-pipeline0.mjs',
  './release-audit0': './pcc-release-audit0.mjs',
  './runall0': './pcc-runall0.mjs',
});

export const PUBLIC_PACKAGE_BIN0 = Object.freeze({
  'pnp-release-audit0': './bin/release-audit0.mjs',
  'pnp-runall0': './bin/runall0.mjs',
});

export const PUBLIC_PACKAGE_SCRIPT_TARGETS0 = Object.freeze({
  check: 'node --check pcc-core.mjs',
  'materialized:accept-run': 'node ./bin/check-materialized-accept-run0.mjs',
  'materialized:accept-run:full': 'node ./bin/check-materialized-accept-run0.mjs --full',
  'materialized:aggregate': 'node ./bin/check-materialized-aggregate0.mjs',
  'materialized:aggregate:full': 'node ./bin/check-materialized-aggregate0.mjs --full',
  'materialized:bridge': 'node ./bin/check-materialized-acceptance-bridge0.mjs',
  'materialized:bridge:full': 'node ./bin/check-materialized-acceptance-bridge0.mjs --full',
  'materialized:final-verdict': 'node ./bin/check-materialized-final-verdict0.mjs',
  'materialized:final-verdict:full': 'node ./bin/check-materialized-final-verdict0.mjs --full',
  'materialized:public-status': 'node ./bin/check-materialized-public-status0.mjs',
  'materialized:public-status:full': 'node ./bin/check-materialized-public-status0.mjs --full',
  'materialized:public-status-roundtrip': 'node ./bin/check-materialized-public-status-roundtrip0.mjs',
  'materialized:public-status-roundtrip:full': 'node ./bin/check-materialized-public-status-roundtrip0.mjs --full',
  'materialized:resolve-digest': 'node ./bin/resolve-materialized-digest0.mjs',
  'materialized:resolve-digest:full': 'node ./bin/resolve-materialized-digest0.mjs --full',
  'materialized:shell': 'node ./bin/check-materialized-shell0.mjs',
  'materialized:shell:full': 'node ./bin/check-materialized-shell0.mjs --full',
  'materialized:write-accept-runs': 'node ./bin/write-materialized-accept-run-fixtures0.mjs',
  'materialized:write-accept-runs:full': 'node ./bin/write-materialized-accept-run-fixtures0.mjs --full',
  'materialized:write-fixtures': 'node ./bin/write-materialized-fixtures0.mjs',
  'materialized:write-fixtures:full': 'node ./bin/write-materialized-fixtures0.mjs --full',
  'materialized:write-final-runs': 'node ./bin/write-materialized-final-run-fixtures0.mjs',
  'materialized:write-final-runs:full': 'node ./bin/write-materialized-final-run-fixtures0.mjs --full',
  'release:audit': 'node ./bin/release-audit0.mjs',
  'release:audit:full': 'node ./bin/release-audit0.mjs --full',
  runall: 'node ./bin/runall0.mjs',
  smoke: 'node ./bin/runall0.mjs',
  'smoke:full': 'node ./bin/runall0.mjs --full',
  test: 'node --test',
  validate: 'npm run check && npm test',
  'materialized:final-certificate': 'node ./bin/write-materialized-final-certificate0.mjs',
  'materialized:final-certificate:full': 'node ./bin/write-materialized-final-certificate0.mjs --full',
  'materialized:final-certificate-public-status': 'node ./bin/write-final-certificate-public-status0.mjs',
  'materialized:final-certificate-public-status:full': 'node ./bin/write-final-certificate-public-status0.mjs --full',
  'release:audit:final-certificate-gate': 'node ./bin/write-release-audit-final-certificate-gate0.mjs',
  'release:audit:final-certificate-gate:full': 'node ./bin/write-release-audit-final-certificate-gate0.mjs --full',  
});

export const PUBLIC_PACKAGE_SCRIPT_KEYS0 = Object.freeze(Object.keys(PUBLIC_PACKAGE_SCRIPT_TARGETS0).sort());

export function makePublicSurfaceFreezeConfig0(overrides = {}) {
  return {
    kind: 'PublicSurfaceFreezeConfig0',
    version: CHECKER_VERSION,
    rootDir: REPO_ROOT,
    publicEntryOverride: null,
    packageJsonOverride: null,
    ...overrides,
  };
}

export async function CheckPublicEntryReleaseSurface0(config = makePublicSurfaceFreezeConfig0()) {
  const checker = 'CheckPublicEntryReleaseSurface0';
  const ledger = [];
  const cfg = makePublicSurfaceFreezeConfig0(config);

  const configCheck = validateConfig0(cfg);

  ledger.push({
    phase: 'config',
    status: configCheck.ok ? 'pass' : 'fail',
    digest: digestCanonical0(configCheck.nf ?? configCheck.witness ?? null),
  });

  if (!configCheck.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.config`,
      path: configCheck.path,
      witness: configCheck.witness,
      ledger,
    });
  }

  const entry = cfg.publicEntryOverride ?? publicEntry0;

  const entrySurface = validateExactKeys0(
    entry,
    PUBLIC_ENTRY_EXPORT_KEYS0,
    ['index.mjs', 'exports'],
  );

  ledger.push({
    phase: 'publicEntryExports',
    status: entrySurface.ok ? 'pass' : 'fail',
    digest: digestCanonical0(entrySurface.nf ?? entrySurface.witness ?? null),
  });

  if (!entrySurface.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.publicEntryExports`,
      path: entrySurface.path,
      witness: entrySurface.witness,
      ledger,
    });
  }

  const packageJson = cfg.packageJsonOverride ?? await readPackageJson0(cfg.rootDir);

  if (isRejectLike0(packageJson)) {
    ledger.push({
      phase: 'readPackageJson',
      status: 'fail',
      digest: digestCanonical0(packageJson.witness),
    });

    return makeRejectRecord({
      checker,
      coord: `${checker}.packageJson`,
      path: packageJson.path,
      witness: packageJson.witness,
      ledger,
    });
  }

  const main = validatePackageMain0(packageJson);

  ledger.push({
    phase: 'packageMain',
    status: main.ok ? 'pass' : 'fail',
    digest: digestCanonical0(main.nf ?? main.witness ?? null),
  });

  if (!main.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.packageMain`,
      path: main.path,
      witness: main.witness,
      ledger,
    });
  }

  const exportsSurface = validateExactMapping0(
    packageJson.exports,
    PUBLIC_PACKAGE_EXPORTS0,
    ['package.json', 'exports'],
  );

  ledger.push({
    phase: 'packageExports',
    status: exportsSurface.ok ? 'pass' : 'fail',
    digest: digestCanonical0(exportsSurface.nf ?? exportsSurface.witness ?? null),
  });

  if (!exportsSurface.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.packageExports`,
      path: exportsSurface.path,
      witness: exportsSurface.witness,
      ledger,
    });
  }

  const binSurface = validateExactMapping0(
    packageJson.bin,
    PUBLIC_PACKAGE_BIN0,
    ['package.json', 'bin'],
  );

  ledger.push({
    phase: 'packageBin',
    status: binSurface.ok ? 'pass' : 'fail',
    digest: digestCanonical0(binSurface.nf ?? binSurface.witness ?? null),
  });

  if (!binSurface.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.packageBin`,
      path: binSurface.path,
      witness: binSurface.witness,
      ledger,
    });
  }

  const scriptSurface = validateExactMapping0(
    packageJson.scripts,
    PUBLIC_PACKAGE_SCRIPT_TARGETS0,
    ['package.json', 'scripts'],
  );

  ledger.push({
    phase: 'packageScripts',
    status: scriptSurface.ok ? 'pass' : 'fail',
    digest: digestCanonical0(scriptSurface.nf ?? scriptSurface.witness ?? null),
  });

  if (!scriptSurface.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.packageScripts`,
      path: scriptSurface.path,
      witness: scriptSurface.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'PublicEntryReleaseSurface0NF',
    checker,
    version: CHECKER_VERSION,
    publicEntryExportCount: PUBLIC_ENTRY_EXPORT_KEYS0.length,
    publicEntryExportKeys: PUBLIC_ENTRY_EXPORT_KEYS0,
    packageExportCount: Object.keys(PUBLIC_PACKAGE_EXPORTS0).length,
    packageExportKeys: Object.keys(PUBLIC_PACKAGE_EXPORTS0).sort(),
    packageBinCount: Object.keys(PUBLIC_PACKAGE_BIN0).length,
    packageBinKeys: Object.keys(PUBLIC_PACKAGE_BIN0).sort(),
    packageScriptCount: PUBLIC_PACKAGE_SCRIPT_KEYS0.length,
    packageScriptKeys: PUBLIC_PACKAGE_SCRIPT_KEYS0,
    packageMain: './index.mjs',
    packageType: 'module',
    surfaceFrozen: true,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'PublicSurfaceFreezeConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'PublicSurfaceFreezeConfig0') {
    return validationReject0(['kind'], 'PublicSurfaceFreezeConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `PublicSurfaceFreezeConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  if (typeof config.rootDir !== 'string' || config.rootDir.length === 0) {
    return validationReject0(['rootDir'], 'PublicSurfaceFreezeConfig0 rootDir must be a non-empty string', {
      actual: config.rootDir,
    });
  }

  if (
    config.publicEntryOverride !== null &&
    (typeof config.publicEntryOverride !== 'object' || config.publicEntryOverride === null)
  ) {
    return validationReject0(['publicEntryOverride'], 'PublicSurfaceFreezeConfig0 publicEntryOverride must be null or an object', {
      actual: typeof config.publicEntryOverride,
    });
  }

  if (
    config.packageJsonOverride !== null &&
    !isPlainObject(config.packageJsonOverride)
  ) {
    return validationReject0(['packageJsonOverride'], 'PublicSurfaceFreezeConfig0 packageJsonOverride must be null or a plain object', {
      actual: typeof config.packageJsonOverride,
    });
  }

  return validationAccept0({
    kind: 'PublicSurfaceFreezeConfig0NF',
  });
}

function validatePackageMain0(packageJson) {
  if (!isPlainObject(packageJson)) {
    return validationReject0(['package.json'], 'package.json must be an object', {
      actual: typeof packageJson,
    });
  }

  if (packageJson.type !== 'module') {
    return validationReject0(['package.json', 'type'], 'package.json type must remain module', {
      expected: 'module',
      actual: packageJson.type,
    });
  }

  if (packageJson.main !== './index.mjs') {
    return validationReject0(['package.json', 'main'], 'package.json main must remain ./index.mjs', {
      expected: './index.mjs',
      actual: packageJson.main,
    });
  }

  return validationAccept0({
    kind: 'PackageMainSurface0NF',
  });
}

function validateExactMapping0(actual, expected, path) {
  const keyCheck = validateExactKeys0(actual, Object.keys(expected).sort(), path);

  if (!keyCheck.ok) {
    return keyCheck;
  }

  for (const key of Object.keys(expected).sort()) {
    if (actual[key] !== expected[key]) {
      return validationReject0([...path, key], 'public release surface mapping value changed', {
        key,
        expected: expected[key],
        actual: actual[key],
      });
    }
  }

  return validationAccept0({
    kind: 'PublicSurfaceExactMapping0NF',
    keys: Object.keys(expected).sort(),
  });
}

function validateExactKeys0(value, expectedKeys, path) {
  if (value === null || typeof value !== 'object') {
    return validationReject0(path, 'public release surface target must be an object', {
      actual: typeof value,
    });
  }

  const actualKeys = Object.keys(value).sort();
  const frozenExpected = [...expectedKeys].sort();

  if (stableStringify0(actualKeys) !== stableStringify0(frozenExpected)) {
    return validationReject0(path, 'public release surface keys changed', {
      expectedKeys: frozenExpected,
      actualKeys,
      missingKeys: frozenExpected.filter((key) => !actualKeys.includes(key)),
      extraKeys: actualKeys.filter((key) => !frozenExpected.includes(key)),
    });
  }

  return validationAccept0({
    kind: 'PublicSurfaceExactKeys0NF',
    keys: actualKeys,
  });
}

async function readPackageJson0(rootDir) {
  try {
    const text = await fs.readFile(path.join(rootDir, 'package.json'), 'utf8');

    return JSON.parse(text);
  } catch (error) {
    return {
      tag: 'rejectLike',
      path: ['package.json'],
      witness: {
        reason: 'package.json must be readable JSON',
        detail: {
          rootDir,
          error: error.message,
        },
      },
    };
  }
}

function isRejectLike0(value) {
  return isPlainObject(value) && value.tag === 'rejectLike';
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