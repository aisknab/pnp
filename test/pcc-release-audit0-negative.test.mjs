import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckReleaseAudit0,
  RELEASE_AUDIT_REQUIRED_MODULES0,
  RELEASE_AUDIT_REQUIRED_TESTS0,
} from '../pcc-release-audit0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

test('CheckReleaseAudit0 rejects stale duplicate ES modules under src', async (t) => {
  const rootDir = await makeMiniReleaseRepo0(t);

  await fs.mkdir(path.join(rootDir, 'src'), {
    recursive: true,
  });

  await fs.writeFile(
    path.join(rootDir, 'src', 'pcc-runall0.mjs'),
    'export const stale = true;\n',
  );

  const out = await CheckReleaseAudit0({
    rootDir,
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.staleSrc');
  assert.deepEqual(out.Path, ['src']);
  assert.equal(out.Witness.reason, 'stale duplicate ES module exists under src');
});

test('CheckReleaseAudit0 rejects missing package exports', async (t) => {
  const rootDir = await makeMiniReleaseRepo0(t);
  const packageJsonPath = path.join(rootDir, 'package.json');
  const pkg = JSON.parse(await fs.readFile(packageJsonPath, 'utf8'));

  delete pkg.exports['./runall0'];

  await fs.writeFile(packageJsonPath, `${JSON.stringify(pkg, null, 2)}\n`);

  const out = await CheckReleaseAudit0({
    rootDir,
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.packageJson');
  assert.deepEqual(out.Path, ['package.json', 'exports', './runall0']);
  assert.equal(out.Witness.reason, 'package export mismatch');
});

test('CheckReleaseAudit0 rejects orphaned tests', async (t) => {
  const rootDir = await makeMiniReleaseRepo0(t);

  await fs.writeFile(
    path.join(rootDir, 'test', 'pcc-orphan0.test.mjs'),
    'import test from "node:test"; test("orphan", () => {});\n',
  );

  const out = await CheckReleaseAudit0({
    rootDir,
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.testInventory');
  assert.deepEqual(out.Path, ['test', 'pcc-orphan0.test.mjs']);
  assert.equal(out.Witness.reason, 'test file appears orphaned because its expected module is missing');
});

test('CheckReleaseAudit0 rejects a RunAll0 checker that mutates its input', async () => {
  const out = await CheckReleaseAudit0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: true,
    runCliSmoke: false,
    mutationInputFactory: () => ({
      kind: 'RunAllInput0',
      version: 0,
      Pipeline: {
        kind: 'IntegratedPipeline0',
        version: 0,
      },
      RequiredPhaseOrder: [],
      RequiredCheckers: [],
      RequiredPublicConclusion: {
        antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
        consequent: 'P = NP',
        conditional: true,
      },
    }),
    mutationRunner: async (input) => {
      input.Pipeline.version = 999;

      return {
        tag: 'accept',
        kind: 'accept',
        checker: 'MutatingRunAll0',
        NF: {
          kind: 'MutatingRunAll0NF',
        },
        Digest: digestCanonical0({
          kind: 'MutatingRunAll0NF',
        }),
        Ledger: [],
      };
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.runAllMutation');
  assert.deepEqual(out.Path, ['CheckRunAll0', 'mutation']);
  assert.equal(out.Witness.reason, 'CheckRunAll0 mutated its input object');
});

async function makeMiniReleaseRepo0(t) {
  const rootDir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-release-audit-negative-'));

  t.after(async () => {
    await fs.rm(rootDir, {
      recursive: true,
      force: true,
    });
  });

  await fs.mkdir(path.join(rootDir, 'bin'), {
    recursive: true,
  });

  await fs.mkdir(path.join(rootDir, 'test'), {
    recursive: true,
  });

  for (const relativeFile of RELEASE_AUDIT_REQUIRED_MODULES0) {
    const absoluteFile = path.join(rootDir, relativeFile);

    await fs.mkdir(path.dirname(absoluteFile), {
      recursive: true,
    });

    await fs.writeFile(absoluteFile, 'export {};\n');
  }

  for (const testFile of RELEASE_AUDIT_REQUIRED_TESTS0) {
    await fs.writeFile(
      path.join(rootDir, 'test', testFile),
      'import test from "node:test"; test("placeholder", () => {});\n',
    );
  }

  await fs.writeFile(
    path.join(rootDir, 'package.json'),
    `${JSON.stringify(makeMiniPackageJson0(), null, 2)}\n`,
  );

  await fs.writeFile(
    path.join(rootDir, 'README.md'),
    [
      '# Mini release fixture',
      '',
      '## Public RunAll0 entry point',
      '',
      'CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP',
      '',
      'The generator is untrusted.',
      '',
      'The checker compares canonical bytes rather than digest equality.',
      '',
      '## Release audit',
      '',
      'Release audit fixture.',
      '',
    ].join('\n'),
  );

  return rootDir;
}

function makeMiniPackageJson0() {
  return {
    name: '@aisknab/pnp-mini-release-fixture',
    version: '0.0.0',
    type: 'module',
    main: './index.mjs',
    exports: {
      '.': './index.mjs',
      './runall0': './pcc-runall0.mjs',
      './integrated-pipeline0': './pcc-integrated-pipeline0.mjs',
      './accept-run0': './pcc-accept-run0.mjs',
      './release-audit0': './pcc-release-audit0.mjs',
    },
    bin: {
      'pnp-runall0': './bin/runall0.mjs',
      'pnp-release-audit0': './bin/release-audit0.mjs',
    },
    scripts: {
      smoke: 'node ./bin/runall0.mjs',
      'smoke:full': 'node ./bin/runall0.mjs --full',
      runall: 'node ./bin/runall0.mjs',
      'release:audit': 'node ./bin/release-audit0.mjs',
      'release:audit:full': 'node ./bin/release-audit0.mjs --full',

      'materialized:shell': 'node ./bin/check-materialized-shell0.mjs',
      'materialized:shell:full': 'node ./bin/check-materialized-shell0.mjs --full',

      'materialized:aggregate': 'node ./bin/check-materialized-aggregate0.mjs',
      'materialized:aggregate:full': 'node ./bin/check-materialized-aggregate0.mjs --full',

      'materialized:bridge': 'node ./bin/check-materialized-acceptance-bridge0.mjs',
      'materialized:bridge:full': 'node ./bin/check-materialized-acceptance-bridge0.mjs --full',

      'materialized:write-fixtures': 'node ./bin/write-materialized-fixtures0.mjs',
      'materialized:write-fixtures:full': 'node ./bin/write-materialized-fixtures0.mjs --full',

      'materialized:resolve-digest': 'node ./bin/resolve-materialized-digest0.mjs',
      'materialized:resolve-digest:full': 'node ./bin/resolve-materialized-digest0.mjs --full',

      'materialized:accept-run': 'node ./bin/check-materialized-accept-run0.mjs',
      'materialized:accept-run:full': 'node ./bin/check-materialized-accept-run0.mjs --full',

      'materialized:write-accept-runs': 'node ./bin/write-materialized-accept-run-fixtures0.mjs',
      'materialized:write-accept-runs:full': 'node ./bin/write-materialized-accept-run-fixtures0.mjs --full',

      'materialized:final-verdict': 'node ./bin/check-materialized-final-verdict0.mjs',
      'materialized:final-verdict:full': 'node ./bin/check-materialized-final-verdict0.mjs --full',
    },
  };
}