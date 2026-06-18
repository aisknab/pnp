import { createHash } from 'node:crypto';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const REPO_ROOT = path.dirname(fileURLToPath(import.meta.url));

const STATIC_DIGEST_FIELD_RE0 =
  /\b(hex|digestHex|hashHex|displayedHash|expectedHash)\s*:\s*(['"])([^'"]+)\2/g;

export function fixtureDigestHex0(label) {
  return createHash('sha256')
    .update(`pnp-fixture-digest-v0:${String(label)}`, 'utf8')
    .digest('hex');
}

export function fixtureDigestRecord0(label) {
  return {
    alg: 'SHA256',
    hex: fixtureDigestHex0(label),
  };
}

export function isSha256Hex0(value) {
  return typeof value === 'string' && /^[0-9a-f]{64}$/.test(value);
}

export async function findInvalidFixtureDigestHexLiterals0({
  rootDir = REPO_ROOT,
} = {}) {
  const files = await implementationFiles0(rootDir);
  const invalid = [];

  for (const relativeFile of files) {
    const absoluteFile = path.join(rootDir, relativeFile);
    const text = await fs.readFile(absoluteFile, 'utf8');

    for (const match of text.matchAll(STATIC_DIGEST_FIELD_RE0)) {
      const field = match[1];
      const value = match[3];

      if (!isSha256Hex0(value)) {
        invalid.push({
          file: relativeFile,
          field,
          value,
          index: match.index,
        });
      }
    }
  }

  return invalid;
}

async function implementationFiles0(rootDir) {
  const rootEntries = await fs.readdir(rootDir, {
    withFileTypes: true,
  });

  const files = [];

  for (const entry of rootEntries) {
    if (
      entry.isFile() &&
      entry.name.endsWith('.mjs') &&
      (
        entry.name === 'index.mjs' ||
        entry.name.startsWith('pcc-')
      )
    ) {
      files.push(entry.name);
    }
  }

  const binDir = path.join(rootDir, 'bin');

  try {
    const binEntries = await fs.readdir(binDir, {
      withFileTypes: true,
    });

    for (const entry of binEntries) {
      if (entry.isFile() && entry.name.endsWith('.mjs')) {
        files.push(path.join('bin', entry.name));
      }
    }
  } catch {
    // No bin directory means no bin files to scan.
  }

  return files.sort();
}