import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckRunAll0,
  RUNALL_CHECKER_COVERAGE0,
  RUNALL_PUBLIC_CONCLUSION0,
  RunAll0,
  makeSyntheticRunAllInput0,
} from './pcc-runall0.mjs';

const CHECKER_VERSION = 0;
const REPO_ROOT = path.dirname(fileURLToPath(import.meta.url));

export const RELEASE_AUDIT_REQUIRED_MODULES0 = Object.freeze([
  'index.mjs',
  'pcc-core.mjs',
  'pcc-verifier-frag0.mjs',
  'pcc-boot0.mjs',
  'pcc-kimpl0.mjs',
  'pcc-hard0.mjs',
  'pcc-rows0.mjs',
  'pcc-global-proof-dag0.mjs',
  'pcc-local-packages0.mjs',
  'pcc-global-firewalls0.mjs',
  'pcc-gpack0.mjs',
  'pcc-final-framework0.mjs',
  'pcc-final0.mjs',
  'pcc-pack-sufficiency0.mjs',
  'pcc-accept-run0.mjs',
  'pcc-integrated-pipeline0.mjs',
  'pcc-runall0.mjs',
  'pcc-release-audit0.mjs',
  'bin/runall0.mjs',
  'bin/release-audit0.mjs',
  'pcc-materialized0.mjs',
  'pcc-fixture-digests0.mjs',
  'pcc-synthetic-marker-inventory0.mjs',
  'pcc-materialized-pack0.mjs',
  'pcc-materialized-loader0.mjs',
  'bin/check-materialized-shell0.mjs',     
  'pcc-materialized-core-extractor0.mjs',
  'pcc-materialized-phase-manifest0.mjs',
  'pcc-materialized-artefact-inventory0.mjs',
  'pcc-materialized-artefact-deps0.mjs',
  'pcc-materialized-proof-refs0.mjs',
  'pcc-materialized-bounds0.mjs',
  'pcc-materialized-no-hidden-min0.mjs',
  'pcc-materialized-imports0.mjs',
  'pcc-materialized-aggregate0.mjs',
  'bin/check-materialized-aggregate0.mjs',
  'pcc-materialized-acceptance-bridge0.mjs',
  'bin/check-materialized-acceptance-bridge0.mjs',
  'pcc-materialized-fixture-writer0.mjs',
  'bin/write-materialized-fixtures0.mjs',                           
]);

export const RELEASE_AUDIT_REQUIRED_TESTS0 = Object.freeze([
  'pcc-core.test.mjs',
  'pcc-core.negative.test.mjs',
  'pcc-release-audit0-negative.test.mjs',
  'pcc-verifier-frag0.test.mjs',
  'pcc-verifier-frag0-current-suite.test.mjs',
  'pcc-boot0.test.mjs',
  'pcc-boot0-batch0-coverage.test.mjs',
  'pcc-kimpl0.test.mjs',
  'pcc-hard0.test.mjs',
  'pcc-public-api0.test.mjs',
  'pcc-rows0.test.mjs',
  'pcc-global-proof-dag0.test.mjs',
  'pcc-local-packages0.test.mjs',
  'pcc-global-firewalls0.test.mjs',
  'pcc-gpack0.test.mjs',
  'pcc-final-framework0.test.mjs',
  'pcc-final0.test.mjs',
  'pcc-pack-sufficiency0.test.mjs',
  'pcc-accept-run0.test.mjs',
  'pcc-integrated-pipeline0.test.mjs',
  'pcc-runall0.test.mjs',
  'pcc-public-entry0.test.mjs',
  'pcc-release-audit0.test.mjs',
  'pcc-integrated-pipeline-tamper0.test.mjs',
  'pcc-materialized0.test.mjs',
  'pcc-fixture-digests0.test.mjs',
  'pcc-synthetic-marker-inventory0.test.mjs',
  'pcc-materialized-pack0.test.mjs',
  'pcc-materialized-loader0.test.mjs',
  'pcc-materialized-core-extractor0.test.mjs',
  'pcc-materialized-phase-manifest0.test.mjs',              
  'pcc-materialized-artefact-inventory0.test.mjs',
  'pcc-materialized-artefact-deps0.test.mjs',
  'pcc-materialized-proof-refs0.test.mjs',
  'pcc-materialized-bounds0.test.mjs',
  'pcc-materialized-no-hidden-min0.test.mjs',
  'pcc-materialized-imports0.test.mjs',
  'pcc-materialized-aggregate0.test.mjs',
  'pcc-materialized-aggregate-cli0.test.mjs',
  'pcc-materialized-acceptance-bridge0.test.mjs',
  'pcc-materialized-acceptance-bridge-cli0.test.mjs',
  'pcc-materialized-path-readme0.test.mjs',
  'pcc-materialized-fixture-writer0.test.mjs',                  
]);

export const RELEASE_AUDIT_REQUIRED_EXPORTS0 = Object.freeze([
  '.',
  './runall0',
  './integrated-pipeline0',
  './accept-run0',
  './release-audit0',
]);

export const RELEASE_AUDIT_REQUIRED_SCRIPTS0 = Object.freeze([
  'smoke',
  'smoke:full',
  'runall',
  'release:audit',
  'materialized:shell',
  'materialized:shell:full',
  'materialized:aggregate',
  'materialized:aggregate:full',
  'materialized:bridge',
  'materialized:bridge:full',
  'materialized:write-fixtures',
  'materialized:write-fixtures:full',  
]);

export function makeReleaseAuditConfig0(overrides = {}) {
  return {
    kind: 'ReleaseAuditConfig0',
    version: CHECKER_VERSION,
    rootDir: REPO_ROOT,
    runSyntaxCheck: true,
    runRunAll: true,
    runMutationCheck: true,
    runCliSmoke: false,
    mutationInputFactory: null,
    mutationRunner: null,
    ...overrides,
  };
}

export async function CheckReleaseAudit0(config = makeReleaseAuditConfig0()) {
  const checker = 'CheckReleaseAudit0';
  const ledger = [];
  const cfg = makeReleaseAuditConfig0(config);

  const phases = [
    ['shape', `${checker}.input`, () => validateConfig0(cfg)],
    ['requiredFiles', `${checker}.requiredFiles`, () => validateRequiredFiles0(cfg)],
    ['staleSrc', `${checker}.staleSrc`, () => validateNoStaleSrcDuplicates0(cfg)],
    ['packageJson', `${checker}.packageJson`, () => validatePackageJson0(cfg)],
    ['testInventory', `${checker}.testInventory`, () => validateTestInventory0(cfg)],
    ['readme', `${checker}.readme`, () => validateReadme0(cfg)],
    ['syntax', `${checker}.syntax`, () => validateSyntax0(cfg)],
    ['runAllDeterminism', `${checker}.runAllDeterminism`, () => validateRunAllDeterminism0(cfg)],
    ['runAllMutation', `${checker}.runAllMutation`, () => validateRunAllMutation0(cfg)],
    ['cliSmoke', `${checker}.cliSmoke`, () => validateCliSmoke0(cfg)],
  ];

  for (const [phase, coord, run] of phases) {
    const result = await run();

    ledger.push({
      phase,
      status: result.ok ? 'pass' : 'fail',
      digest: digestCanonical0(result.nf ?? result.witness ?? null),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  const nf = {
    kind: 'ReleaseAudit0NF',
    checker,
    version: CHECKER_VERSION,
    rootDir: cfg.rootDir,
    moduleCount: RELEASE_AUDIT_REQUIRED_MODULES0.length,
    testCount: RELEASE_AUDIT_REQUIRED_TESTS0.length,
    requiredExports: RELEASE_AUDIT_REQUIRED_EXPORTS0,
    requiredScripts: RELEASE_AUDIT_REQUIRED_SCRIPTS0,
    checkerCoverageCount: RUNALL_CHECKER_COVERAGE0.length,
    publicConclusion: RUNALL_PUBLIC_CONCLUSION0,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateConfig0(cfg) {
  if (!isPlainObject(cfg)) {
    return validationReject0([], 'ReleaseAuditConfig0 must be an object', {
      actual: typeof cfg,
    });
  }

  if (!isNonEmptyString(cfg.rootDir)) {
    return validationReject0(['rootDir'], 'ReleaseAuditConfig0 rootDir must be a non-empty string', {
      actual: cfg.rootDir,
    });
  }

  return validationAccept0({
    kind: 'ReleaseAuditConfig0NF',
  });
}

async function validateRequiredFiles0(cfg) {
  for (const relativeFile of [
    ...RELEASE_AUDIT_REQUIRED_MODULES0,
    ...RELEASE_AUDIT_REQUIRED_TESTS0.map((file) => path.join('test', file)),
    'package.json',
    'README.md',
  ]) {
    const absoluteFile = path.join(cfg.rootDir, relativeFile);

    if (!(await pathExists0(absoluteFile))) {
      return validationReject0(['files', relativeFile], 'required release-audit file is missing', {
        relativeFile,
      });
    }
  }

  return validationAccept0({
    kind: 'ReleaseRequiredFiles0NF',
    moduleCount: RELEASE_AUDIT_REQUIRED_MODULES0.length,
    testCount: RELEASE_AUDIT_REQUIRED_TESTS0.length,
  });
}

async function validateNoStaleSrcDuplicates0(cfg) {
  const srcDir = path.join(cfg.rootDir, 'src');

  if (!(await pathExists0(srcDir))) {
    return validationAccept0({
      kind: 'NoStaleSrcDuplicates0NF',
      staleDuplicateCount: 0,
    });
  }

  const srcFiles = await walkFiles0(srcDir);
  const staleDuplicates = [];

  for (const srcFile of srcFiles) {
    if (!srcFile.endsWith('.mjs')) {
      continue;
    }

    const basename = path.basename(srcFile);
    const rootSibling = path.join(cfg.rootDir, basename);

    if (await pathExists0(rootSibling)) {
      staleDuplicates.push({
        srcFile: path.relative(cfg.rootDir, srcFile),
        rootSibling: basename,
      });
    }
  }

  if (staleDuplicates.length > 0) {
    return validationReject0(['src'], 'stale duplicate ES module exists under src', {
      staleDuplicates,
      fix: 'delete or move the stale src duplicate so the root module remains the single active implementation',
    });
  }

  return validationAccept0({
    kind: 'NoStaleSrcDuplicates0NF',
    staleDuplicateCount: 0,
  });
}

async function validatePackageJson0(cfg) {
  const pkg = await readJsonFile0(path.join(cfg.rootDir, 'package.json'));

  if (!pkg.ok) {
    return validationReject0(['package.json'], 'package.json must be readable JSON', pkg.witness);
  }

  const value = pkg.value;

  if (value.main !== './index.mjs') {
    return validationReject0(['package.json', 'main'], 'package.json main must point to ./index.mjs', {
      actual: value.main,
    });
  }

  if (!isPlainObject(value.exports)) {
    return validationReject0(['package.json', 'exports'], 'package.json exports must be an object', {
      actual: typeof value.exports,
    });
  }

  const expectedExports = {
    '.': './index.mjs',
    './runall0': './pcc-runall0.mjs',
    './integrated-pipeline0': './pcc-integrated-pipeline0.mjs',
    './accept-run0': './pcc-accept-run0.mjs',
    './release-audit0': './pcc-release-audit0.mjs',
  };

  for (const [key, expected] of Object.entries(expectedExports)) {
    if (value.exports[key] !== expected) {
      return validationReject0(['package.json', 'exports', key], 'package export mismatch', {
        expected,
        actual: value.exports[key],
      });
    }
  }

  if (!isPlainObject(value.bin)) {
    return validationReject0(['package.json', 'bin'], 'package.json bin must be an object', {
      actual: typeof value.bin,
    });
  }

  if (value.bin['pnp-runall0'] !== './bin/runall0.mjs') {
    return validationReject0(['package.json', 'bin', 'pnp-runall0'], 'pnp-runall0 bin target mismatch', {
      actual: value.bin['pnp-runall0'],
    });
  }

  if (value.bin['pnp-release-audit0'] !== './bin/release-audit0.mjs') {
    return validationReject0(['package.json', 'bin', 'pnp-release-audit0'], 'pnp-release-audit0 bin target mismatch', {
      actual: value.bin['pnp-release-audit0'],
    });
  }

  if (!isPlainObject(value.scripts)) {
    return validationReject0(['package.json', 'scripts'], 'package.json scripts must be an object', {
      actual: typeof value.scripts,
    });
  }

  for (const script of RELEASE_AUDIT_REQUIRED_SCRIPTS0) {
    if (!isNonEmptyString(value.scripts[script])) {
      return validationReject0(['package.json', 'scripts', script], 'required package script is missing', {
        script,
      });
    }
  }

  return validationAccept0({
    kind: 'PackageJsonReleaseSurface0NF',
  });
}

async function validateTestInventory0(cfg) {
  const testDir = path.join(cfg.rootDir, 'test');
  const actualTests = (await fs.readdir(testDir))
    .filter((file) => file.endsWith('.test.mjs'))
    .sort();

  for (const required of RELEASE_AUDIT_REQUIRED_TESTS0) {
    if (!actualTests.includes(required)) {
      return validationReject0(['test', required], 'required test file is missing', {
        required,
      });
    }
  }

  for (const testFile of actualTests) {
    const expectedModule = expectedModuleForTest0(testFile);

    if (expectedModule === null) {
      continue;
    }

    const modulePath = path.join(cfg.rootDir, expectedModule);

    if (!(await pathExists0(modulePath))) {
      return validationReject0(['test', testFile], 'test file appears orphaned because its expected module is missing', {
        testFile,
        expectedModule,
      });
    }
  }

  return validationAccept0({
    kind: 'TestInventory0NF',
    testCount: actualTests.length,
  });
}

async function validateReadme0(cfg) {
  const readmePath = path.join(cfg.rootDir, 'README.md');
  const text = await fs.readFile(readmePath, 'utf8');

  const requiredSnippets = [
    'Public RunAll0 entry point',
    'CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP',
    'The generator is untrusted',
    'canonical bytes rather than digest equality',
    'Release audit',
  ];

  for (const snippet of requiredSnippets) {
    if (!text.includes(snippet)) {
      return validationReject0(['README.md'], 'README is missing required public release wording', {
        snippet,
      });
    }
  }

  return validationAccept0({
    kind: 'ReadmeReleaseWording0NF',
  });
}

async function validateSyntax0(cfg) {
  if (cfg.runSyntaxCheck !== true) {
    return validationAccept0({
      kind: 'SyntaxCheckSkipped0NF',
    });
  }

  for (const relativeFile of RELEASE_AUDIT_REQUIRED_MODULES0) {
    const absoluteFile = path.join(cfg.rootDir, relativeFile);
    const child = spawnSync(process.execPath, ['--check', absoluteFile], {
      cwd: cfg.rootDir,
      encoding: 'utf8',
    });

    if (child.status !== 0) {
      return validationReject0(['syntax', relativeFile], 'node --check failed for release module', {
        relativeFile,
        stdout: child.stdout,
        stderr: child.stderr,
      });
    }
  }

  return validationAccept0({
    kind: 'SyntaxCheck0NF',
    checkedCount: RELEASE_AUDIT_REQUIRED_MODULES0.length,
  });
}

async function validateRunAllDeterminism0(cfg) {
  if (cfg.runRunAll !== true) {
    return validationAccept0({
      kind: 'RunAllDeterminismSkipped0NF',
    });
  }

  const first = await RunAll0();
  const second = await RunAll0();

  if (first.tag !== 'accept') {
    return validationReject0(['RunAll0', 'first'], 'first RunAll0 execution did not accept', compactReject0(first));
  }

  if (second.tag !== 'accept') {
    return validationReject0(['RunAll0', 'second'], 'second RunAll0 execution did not accept', compactReject0(second));
  }

  if (stableStringify0(first.Digest) !== stableStringify0(second.Digest)) {
    return validationReject0(['RunAll0', 'Digest'], 'RunAll0 is not deterministic across fresh executions', {
      first: first.Digest,
      second: second.Digest,
    });
  }

  return validationAccept0({
    kind: 'RunAllDeterminism0NF',
    digest: first.Digest,
  });
}

async function validateRunAllMutation0(cfg) {
  if (cfg.runMutationCheck !== true) {
    return validationAccept0({
      kind: 'RunAllMutationCheckSkipped0NF',
    });
  }

  const input = typeof cfg.mutationInputFactory === 'function'
    ? cfg.mutationInputFactory()
    : makeSyntheticRunAllInput0();

  const runner = typeof cfg.mutationRunner === 'function'
    ? cfg.mutationRunner
    : CheckRunAll0;

  const before = stableStringify0(input);
  const out = await runner(input);
  const after = stableStringify0(input);

  if (out.tag !== 'accept') {
    return validationReject0(['CheckRunAll0'], 'CheckRunAll0 did not accept the mutation-check input', compactReject0(out));
  }

  if (before !== after) {
    return validationReject0(['CheckRunAll0', 'mutation'], 'CheckRunAll0 mutated its input object', {
      beforeDigest: digestCanonical0(before),
      afterDigest: digestCanonical0(after),
    });
  }

  return validationAccept0({
    kind: 'RunAllMutationCheck0NF',
    digest: out.Digest,
  });
}

async function validateCliSmoke0(cfg) {
  if (cfg.runCliSmoke !== true) {
    return validationAccept0({
      kind: 'CliSmokeSkipped0NF',
    });
  }

  const commands = [
    ['bin/runall0.mjs'],
    ['bin/runall0.mjs', '--full'],
    ['bin/release-audit0.mjs'],
  ];

  for (const args of commands) {
    const child = spawnSync(process.execPath, args.map((entry) => path.join(cfg.rootDir, entry)), {
      cwd: cfg.rootDir,
      encoding: 'utf8',
    });

    if (child.status !== 0) {
      return validationReject0(['cli', args[0]], 'release CLI smoke command failed', {
        args,
        stdout: child.stdout,
        stderr: child.stderr,
      });
    }

    let parsed;

    try {
      parsed = JSON.parse(child.stdout);
    } catch (error) {
      return validationReject0(['cli', args[0]], 'release CLI did not emit JSON', {
        args,
        stdout: child.stdout,
        error: error.message,
      });
    }

    if (parsed.tag !== 'accept') {
      return validationReject0(['cli', args[0]], 'release CLI emitted a non-accept record', {
        args,
        parsed,
      });
    }
  }

  return validationAccept0({
    kind: 'CliSmoke0NF',
    commandCount: commands.length,
  });
}

function expectedModuleForTest0(testFile) {
  const stem = testFile.replace(/\.test\.mjs$/, '');

  const explicit = {
    'pcc-core': 'pcc-core.mjs',
    'pcc-core.negative': 'pcc-core.mjs',
    'pcc-core-negative': 'pcc-core.mjs',
    'pcc-verifier-frag0-current-suite': 'pcc-verifier-frag0.mjs',
    'pcc-boot0-batch0-coverage': 'pcc-boot0.mjs',
    'pcc-public-entry0': 'index.mjs',
    'pcc-public-api0': 'index.mjs',
    'pcc-integrated-pipeline-tamper0': 'pcc-integrated-pipeline0.mjs',
    'pcc-release-audit0-negative': 'pcc-release-audit0.mjs',
    'pcc-materialized-aggregate-cli0': 'bin/check-materialized-aggregate0.mjs',
    'pcc-materialized-acceptance-bridge-cli0': 'bin/check-materialized-acceptance-bridge0.mjs',
    'pcc-materialized-path-readme0': 'README.md',
  };

  if (Object.prototype.hasOwnProperty.call(explicit, stem)) {
    return explicit[stem];
  }

  return `${stem}.mjs`;
}

async function readJsonFile0(filePath) {
  try {
    const text = await fs.readFile(filePath, 'utf8');
    return {
      ok: true,
      value: JSON.parse(text),
    };
  } catch (error) {
    return {
      ok: false,
      witness: {
        filePath,
        error: error.message,
      },
    };
  }
}

async function walkFiles0(dir) {
  const out = [];
  const entries = await fs.readdir(dir, {
    withFileTypes: true,
  });

  for (const entry of entries) {
    const absolute = path.join(dir, entry.name);

    if (entry.isDirectory()) {
      out.push(...await walkFiles0(absolute));
    } else if (entry.isFile()) {
      out.push(absolute);
    }
  }

  return out;
}

async function pathExists0(filePath) {
  try {
    await fs.access(filePath);
    return true;
  } catch {
    return false;
  }
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