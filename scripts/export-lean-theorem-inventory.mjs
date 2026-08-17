#!/usr/bin/env node

import { execFile } from 'node:child_process';
import { lstat, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';
import { promisify } from 'node:util';

import {
  LEAN_INVENTORY_PATH0,
  LEAN_INVENTORY_PUBLIC_PATH0,
  ValidateLeanTheoremInventory0,
  stableStringify0,
} from '../formal-publication0.mjs';

const execFileAsync = promisify(execFile);
const PROBE = 'lean-audit/PNPTheoremInventory.lean';
const BUILD_TIMEOUT_MS = 1_800_000;
const PROBE_TIMEOUT_MS = 600_000;

export function ParseLeanInventoryProbe0(result) {
  if (result.timedOut === true) throw new Error('Lean environment inventory probe timed out');
  if (result.exitCode !== 0) {
    const detail = typeof result.stderr === 'string'
      ? result.stderr.trim().slice(-4000)
      : '';
    throw new Error(`Lean environment inventory probe exited ${result.exitCode}${detail === '' ? '' : `:\n${detail}`}`);
  }
  if (typeof result.stderr !== 'string' || result.stderr !== '') {
    throw new Error('Lean environment inventory probe emitted stderr');
  }
  if (typeof result.stdout !== 'string' || result.stdout.trim() === '') {
    throw new Error('Lean environment inventory probe emitted empty stdout');
  }
  let inventory;
  try {
    inventory = JSON.parse(result.stdout);
  } catch (error) {
    throw new Error(`Lean environment inventory probe emitted malformed JSON: ${error.message}`);
  }
  ValidateLeanTheoremInventory0(inventory);
  const canonical = `${stableStringify0(inventory)}\n`;
  if (canonical !== result.stdout) {
    throw new Error('Lean environment inventory probe output is not canonical JSON');
  }
  return { inventory, bytes: Buffer.from(canonical, 'utf8') };
}

export async function RunLeanInventoryProbe0(root) {
  await execFileAsync('lake', ['build', 'PNP'], {
    cwd: root,
    encoding: 'utf8',
    timeout: BUILD_TIMEOUT_MS,
    maxBuffer: 32 * 1024 * 1024,
  });
  try {
    const { stdout, stderr } = await execFileAsync('lake', [
      'env', 'lean', '-DwarningAsError=true', PROBE,
    ], {
      cwd: root,
      encoding: 'utf8',
      timeout: PROBE_TIMEOUT_MS,
      maxBuffer: 32 * 1024 * 1024,
    });
    return ParseLeanInventoryProbe0({ stdout, stderr, exitCode: 0, timedOut: false });
  } catch (error) {
    return ParseLeanInventoryProbe0({
      stdout: error.stdout ?? '',
      stderr: error.stderr ?? error.message,
      exitCode: Number.isInteger(error.code) ? error.code : 1,
      timedOut: error.killed === true,
    });
  }
}

async function safeExistingFile0(root, relative) {
  const absolute = path.resolve(root, relative);
  const prefix = `${path.resolve(root)}${path.sep}`;
  if (!absolute.startsWith(prefix)) throw new Error(`inventory path escaped repository root: ${relative}`);
  try {
    const info = await lstat(absolute);
    if (info.isSymbolicLink()) throw new Error(`inventory path must not be a symlink: ${relative}`);
  } catch (error) {
    if (error.code !== 'ENOENT') throw error;
  }
  return absolute;
}

async function main0() {
  const args = process.argv.slice(2);
  const check = args.includes('--check');
  if (args.some((arg) => arg !== '--check')) throw new Error('Usage: node scripts/export-lean-theorem-inventory.mjs [--check]');
  const root = process.cwd();
  const result = await RunLeanInventoryProbe0(root);
  const targets = [LEAN_INVENTORY_PATH0, LEAN_INVENTORY_PUBLIC_PATH0];
  for (const relative of targets) {
    const absolute = await safeExistingFile0(root, relative);
    if (check) {
      const committed = await readFile(absolute);
      if (!committed.equals(result.bytes)) throw new Error(`${relative} drifted from the live compiled Lean environment`);
    } else {
      await writeFile(absolute, result.bytes);
    }
  }
  process.stdout.write(`${JSON.stringify({
    status: check ? 'current' : 'written',
    declarationCount: result.inventory.declarationCount,
    theoremCount: result.inventory.theoremCount,
    assumptionFreeTheoremCount: result.inventory.assumptionFreeTheoremCount,
    axiomCount: result.inventory.axiomCount,
  }, null, 2)}\n`);
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main0().catch((error) => {
    console.error(error.message);
    process.exitCode = 1;
  });
}
