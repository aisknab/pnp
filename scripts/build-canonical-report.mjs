#!/usr/bin/env node

import { execFile } from 'node:child_process';
import { lstat, mkdtemp, readFile, readdir, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import process from 'node:process';
import { promisify } from 'node:util';

const execFileAsync = promisify(execFile);
const REPORT_TEX = 'canonical_proof_report.tex';
const REPORT_PDF = 'canonical_proof_report.pdf';
const FIXED_ENV = Object.freeze({
  SOURCE_DATE_EPOCH: '1783641600',
  FORCE_SOURCE_DATE: '1',
  TZ: 'UTC',
});

const REQUIRED_TEXT = Object.freeze([
  'The repository does not currently establish P = NP .',
  'Compiled Lean theorem inventory',
  'Concrete publication gate',
  'Historical report provenance',
]);

const FORBIDDEN_TEXT = Object.freeze([
  'Accepted proof-report boundary',
  'Complete machine-checkable proof report',
  'This paper proves',
  'Hence the final conclusion of this paper is',
]);

async function run0(file, args, options = {}) {
  return execFileAsync(file, args, {
    cwd: options.cwd,
    encoding: 'utf8',
    timeout: options.timeout ?? 120_000,
    maxBuffer: 32 * 1024 * 1024,
    env: { ...process.env, ...FIXED_ENV, ...options.env },
  });
}

async function buildOnce0(root, parent, requiredText) {
  const output = await mkdtemp(path.join(parent, 'build-'));
  await run0('latexmk', [
    '-pdf',
    '-halt-on-error',
    '-interaction=nonstopmode',
    `-outdir=${output}`,
    REPORT_TEX,
  ], { cwd: root });
  const pdf = path.join(output, REPORT_PDF);
  const log = await readFile(path.join(output, 'canonical_proof_report.log'), 'utf8');
  if (/Overfull \\[hv]box|Missing character|undefined (?:citations?|references?)|multiply defined|Fatal error/iu.test(log)) {
    throw new Error('canonical report LaTeX log contains a layout or reference defect');
  }
  const { stdout: info } = await run0('pdfinfo', [pdf], { cwd: root });
  const pages = Number(/^Pages:\s+(\d+)$/mu.exec(info)?.[1]);
  if (!Number.isInteger(pages) || pages < 1) throw new Error('canonical report page count is invalid');
  if (!/^Page size:\s+595\.276 x 841\.89 pts \(A4\)$/mu.test(info)) throw new Error('canonical report must render on A4 pages');
  if (!/^Encrypted:\s+no$/mu.test(info)) throw new Error('canonical report must not be encrypted');
  const { stdout: text } = await run0('pdftotext', ['-layout', pdf, '-'], { cwd: root });
  const normalizedText = text.replace(/\s+/gu, ' ').trim();
  for (const required of requiredText) {
    if (!normalizedText.includes(required)) throw new Error(`canonical report PDF is missing required text: ${required}`);
  }
  for (const forbidden of FORBIDDEN_TEXT) {
    if (normalizedText.includes(forbidden)) throw new Error(`canonical report PDF contains forbidden historical claim text: ${forbidden}`);
  }
  const renderPrefix = path.join(output, 'page');
  await run0('pdftoppm', ['-png', '-r', '150', pdf, renderPrefix], { cwd: root });
  const renderedPages = (await readdir(output)).filter((name) => /^page-\d+\.png$/u.test(name)).length;
  if (renderedPages !== pages) throw new Error('canonical report did not render every PDF page to PNG');
  return { output, pdf, pages, bytes: await readFile(pdf) };
}

async function safeTarget0(root) {
  const target = path.join(root, REPORT_PDF);
  try {
    const info = await lstat(target);
    if (info.isSymbolicLink()) throw new Error(`${REPORT_PDF} must not be a symlink`);
  } catch (error) {
    if (error.code !== 'ENOENT') throw error;
  }
  return target;
}

async function main0() {
  const args = process.argv.slice(2);
  const check = args.includes('--check');
  if (args.some((arg) => arg !== '--check')) throw new Error('Usage: node scripts/build-canonical-report.mjs [--check]');
  const root = process.cwd();
  await run0(process.execPath, ['scripts/generate-formal-publication.mjs', '--check'], { cwd: root });
  const status = JSON.parse(await readFile(path.join(root, 'status/FORMAL_RECONSTRUCTION_STATUS.json'), 'utf8'));
  if (typeof status.leanTheoremInventorySha256 !== 'string'
      || !/^[0-9a-f]{64}$/u.test(status.leanTheoremInventorySha256)) {
    throw new Error('formal status is missing a valid Lean theorem inventory digest');
  }
  const requiredText = [...REQUIRED_TEXT, status.leanTheoremInventorySha256];
  const temp = await mkdtemp(path.join(os.tmpdir(), 'pnp-canonical-report-'));
  try {
    const first = await buildOnce0(root, temp, requiredText);
    const second = await buildOnce0(root, temp, requiredText);
    if (!first.bytes.equals(second.bytes)) throw new Error('canonical report PDF build is not byte-deterministic');
    const target = await safeTarget0(root);
    if (check) {
      const committed = await readFile(target);
      if (!committed.equals(first.bytes)) throw new Error('canonical_proof_report.pdf drifted from deterministic TeX build');
    } else {
      await writeFile(target, first.bytes);
    }
    process.stdout.write(`${JSON.stringify({
      status: check ? 'current' : 'written',
      pages: first.pages,
      bytes: first.bytes.length,
      everyPageRenderedForQa: true,
    }, null, 2)}\n`);
  } finally {
    await rm(temp, { recursive: true, force: true });
  }
}

main0().catch((error) => {
  console.error(error.message);
  process.exitCode = 1;
});
