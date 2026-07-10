#!/usr/bin/env node

import { mkdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckFormalPublicSurface0';
const VERSION = 0;
const COORDINATE = 'PUBLIC-SURFACE-BASELINE-2026-07-10-PINNED-LEAN-ROOT-03';
const OUTPUT_PATH = 'artifacts/formal-public-surface/latest-verdict.json';

export const CURRENT_PACKAGE_EXPORTS0 = Object.freeze({
  '.': './index.mjs',
  './formal-status': './pcc-formal-reconstruction-status0.mjs',
  './formal-public-surface': './pcc-formal-public-surface0.mjs',
  './legacy-v0-archive': './pcc-legacy-v0-archive0.mjs',
});

export const CURRENT_PACKAGE_SCRIPTS0 = Object.freeze({
  check: 'node --check index.mjs && node --check pcc-formal-reconstruction-status0.mjs && node --check pcc-formal-public-surface0.mjs && node --check pcc-legacy-v0-archive0.mjs && node --check scripts/pnp-verify-all.mjs && node --check scripts/replay-legacy-v0.mjs',
  test: 'node --test audits/formal-reconstruction-status0.test.mjs audits/formal-public-surface0.test.mjs audits/lean-root-target0.test.mjs audits/legacy-v0-archive0.test.mjs test/current-package-surface0.test.mjs test/current-verifier0.test.mjs test/replay-legacy-v0.test.mjs',
  validate: 'npm run check && npm test && npm run pnp:verify -- --no-write',
  'formal:status': 'node pcc-formal-reconstruction-status0.mjs --json',
  'formal:surface': 'node pcc-formal-public-surface0.mjs --json',
  'pnp:verify': 'node scripts/pnp-verify-all.mjs --json',
  'legacy:v0:check': 'node pcc-legacy-v0-archive0.mjs --json',
  'legacy:v0:replay': 'node scripts/replay-legacy-v0.mjs',
});

export const CURRENT_PUBLIC_EXPORTS0 = Object.freeze([
  'CURRENT_PACKAGE_EXPORTS0',
  'CURRENT_PACKAGE_SCRIPTS0',
  'CURRENT_PUBLIC_EXPORTS0',
  'CheckFormalPublicSurface0',
  'CheckFormalReconstructionStatus0',
  'CheckLegacyV0Archive0',
  'FORMAL_RECONSTRUCTION_BLOCKERS0',
  'LEGACY_V0_ARCHIVE_PINS0',
]);

const FORBIDDEN_ACTIVE_SURFACE_TOKENS = Object.freeze([
  'RunAll0',
  'CheckAcceptRun0',
  'CheckIntegratedPipeline0',
  'CheckReleaseAudit0',
  'CheckFinalPNPProofReport0',
  'CheckFinalPNPReleaseGate0',
  'CheckPCCPackexp0',
  'GeneratePCCPack0',
  './bin/',
  './pcc-runall',
  './pcc-accept-run',
  './pcc-release-audit',
  './pcc-final-',
]);

export async function CheckFormalPublicSurface0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const pkg = options.packageJsonOverride ?? JSON.parse(await readFile(path.join(root, 'package.json'), 'utf8'));
    const indexSource = options.indexSourceOverride ?? await readFile(path.join(root, 'index.mjs'), 'utf8');

    if (pkg.private !== true) {
      return finish0(root, outputPath, writeOutput, reject0(
        'FormalPublicSurface.PackagePrivate',
        ['package.json', 'private'],
        'the reconstruction package must remain private',
      ));
    }

    if (!sameObject0(pkg.exports, CURRENT_PACKAGE_EXPORTS0)) {
      return finish0(root, outputPath, writeOutput, reject0(
        'FormalPublicSurface.PackageExports',
        ['package.json', 'exports'],
        'package exports must contain only current status and archive-verification surfaces',
        { expected: CURRENT_PACKAGE_EXPORTS0, actual: pkg.exports ?? null },
      ));
    }
    if (Object.hasOwn(pkg, 'bin')) {
      return finish0(root, outputPath, writeOutput, reject0(
        'FormalPublicSurface.PackageBin',
        ['package.json', 'bin'],
        'the active package must not install legacy theorem-checker executables',
      ));
    }
    if (!sameObject0(pkg.scripts, CURRENT_PACKAGE_SCRIPTS0)) {
      return finish0(root, outputPath, writeOutput, reject0(
        'FormalPublicSurface.PackageScripts',
        ['package.json', 'scripts'],
        'package scripts must match the closed current-authority command surface',
        { expected: CURRENT_PACKAGE_SCRIPTS0, actual: pkg.scripts ?? null },
      ));
    }

    const indexText = String(indexSource);
    const leaked = FORBIDDEN_ACTIVE_SURFACE_TOKENS.filter((token) => indexText.includes(token));
    if (leaked.length !== 0) {
      return finish0(root, outputPath, writeOutput, reject0(
        'FormalPublicSurface.LegacyExport',
        ['index.mjs'],
        'legacy checker routes must not be re-exported by the active package',
        { leaked },
      ));
    }

    const parsedExports = parseIndexExports0(indexText);
    const actualPublicExports = parsedExports.names.sort();
    const expectedPublicExports = [...CURRENT_PUBLIC_EXPORTS0].sort();
    if (parsedExports.unparsedExportSyntax
      || actualPublicExports.length !== expectedPublicExports.length
      || !expectedPublicExports.every((name, index) => actualPublicExports[index] === name)) {
      return finish0(root, outputPath, writeOutput, reject0(
        'FormalPublicSurface.IndexExports',
        ['index.mjs', 'exports'],
        'root entry point exports must match the closed current-authority API',
        {
          expected: expectedPublicExports,
          actual: actualPublicExports,
          unparsedExportSyntax: parsedExports.unparsedExportSyntax,
        },
      ));
    }

    return finish0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORDINATE,
      claimStatus: 'formal-reconstruction-in-progress',
      currentStatusAuthority: true,
      mathematicalTheoremEstablished: false,
      checkerAcceptanceIsMathematicalProof: false,
      publicTheoremEmissionAllowed: false,
      publicTheoremStatement: null,
      publicTheoremConclusion: null,
      finalTheoremReady: false,
      legacyV0CheckerExportedAsCurrentAuthority: false,
      legacyV0ReplayRequiresDesignatedCommand: true,
      packageExports: { ...CURRENT_PACKAGE_EXPORTS0 },
      packageScripts: { ...CURRENT_PACKAGE_SCRIPTS0 },
      packageBinKeys: [],
    });
  } catch (error) {
    return finish0(root, outputPath, writeOutput, reject0(
      'FormalPublicSurface.UnhandledException',
      [],
      'public-surface checker threw unexpectedly',
      normalizeError0(error),
    ));
  }
}

function reject0(coord, pathArray, reason, witness = {}) {
  return {
    tag: 'reject',
    kind: 'reject',
    checker: CHECKER,
    version: VERSION,
    coord,
    path: pathArray,
    witness: { reason, ...witness },
    mathematicalTheoremEstablished: false,
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
  };
}

async function finish0(root, outputPath, enabled, verdict) {
  const rendered = { ...verdict, outputPath: enabled ? outputPath : null };
  if (enabled) {
    const absolute = path.join(root, outputPath);
    await mkdir(path.dirname(absolute), { recursive: true });
    await writeFile(absolute, `${JSON.stringify(rendered, null, 2)}\n`, 'utf8');
  }
  return rendered;
}

function sameObject0(actual, expected) {
  if (actual === null || typeof actual !== 'object' || Array.isArray(actual)) return false;
  const actualKeys = Object.keys(actual);
  const expectedKeys = Object.keys(expected);
  return actualKeys.length === expectedKeys.length
    && expectedKeys.every((key) => Object.hasOwn(actual, key) && actual[key] === expected[key]);
}

function parseIndexExports0(source) {
  const names = [];
  const exportList = /export\s*\{([\s\S]*?)\}\s*from\s*(['"])[^'"]+\2\s*;/gu;
  const remainder = String(source).replace(exportList, (_whole, body) => {
    for (const raw of body.split(',')) {
      const item = raw.trim();
      if (item === '') continue;
      const alias = /^(?:[A-Za-z_$][\w$]*)(?:\s+as\s+([A-Za-z_$][\w$]*))?$/u.exec(item);
      if (alias === null) names.push(`!unparsed:${item}`);
      else names.push(alias[1] ?? item);
    }
    return '';
  });
  return {
    names,
    unparsedExportSyntax: /\bexport\b/u.test(remainder) || names.some((name) => name.startsWith('!unparsed:')),
  };
}

function normalizeError0(error) {
  return {
    name: error?.name ?? 'Error',
    message: error?.message ?? String(error),
    code: error?.code ?? null,
  };
}

function parseArgs0(argv) {
  const options = { json: false, writeOutput: true };
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') {
      const value = argv[++i];
      if (value === undefined) throw new Error('--root requires a value');
      options.root = value;
    } else if (arg === '--output') {
      const value = argv[++i];
      if (value === undefined) throw new Error('--output requires a value');
      options.outputPath = value;
    }
    else if (arg === '--help' || arg === '-h') options.help = true;
    else throw new Error(`unknown argument: ${arg}`);
  }
  return options;
}

async function main0() {
  let options;
  try {
    options = parseArgs0(process.argv.slice(2));
    if (options.help) {
      console.log('Usage: node pcc-formal-public-surface0.mjs [--json] [--no-write] [--root <path>] [--output <path>]');
      return;
    }
  } catch (error) {
    console.error(JSON.stringify(reject0('FormalPublicSurface.CliArgument', [], 'invalid command-line argument', normalizeError0(error)), null, 2));
    process.exitCode = 2;
    return;
  }
  const verdict = await CheckFormalPublicSurface0(options);
  console.log(JSON.stringify(verdict, null, 2));
  process.exitCode = verdict.tag === 'accept' ? 0 : 1;
}

if (import.meta.url === `file://${process.argv[1]}`) await main0();
