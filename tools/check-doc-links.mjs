#!/usr/bin/env node

import {
  existsSync,
  readFileSync,
  readdirSync,
  statSync,
} from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');

const ROOT_DOCUMENTS = [
  'README.md',
  'REPRODUCE.md',
  'REVIEWER_MAP.md',
  'EXTERNAL_REVIEW_STATUS.md',
  'AGENTS.md',
  'examples/minimal/README.md',
];

function walkMarkdown(directory, output = []) {
  if (!existsSync(directory)) return output;

  for (const entry of readdirSync(directory, { withFileTypes: true })) {
    if (entry.name === '.git' || entry.name === 'node_modules') continue;
    const full = path.join(directory, entry.name);
    if (entry.isDirectory()) walkMarkdown(full, output);
    else if (entry.isFile() && entry.name.endsWith('.md')) output.push(full);
  }

  return output;
}

function withoutCode(text) {
  return text
    .replace(/```[\s\S]*?```/gu, '')
    .replace(/~~~[\s\S]*?~~~/gu, '')
    .replace(/`[^`\r\n]*`/gu, '');
}

function normalizeTarget(rawTarget) {
  let target = rawTarget.trim();
  if (target.startsWith('<') && target.endsWith('>')) {
    target = target.slice(1, -1);
  }
  return target.replaceAll('&amp;', '&');
}

function isExternalOrAnchor(target) {
  return (
    target === ''
    || target.startsWith('#')
    || target.startsWith('//')
    || /^[a-z][a-z0-9+.-]*:/iu.test(target)
  );
}

function collectTargets(text) {
  const targets = [];
  const stripped = withoutCode(text);

  const inline = /!?\[[^\]]*\]\((<[^>]+>|[^\s)]+)(?:\s+["'][^"']*["'])?\)/gu;
  for (const match of stripped.matchAll(inline)) targets.push(match[1]);

  const references = /^ {0,3}\[[^\]]+\]:\s*(<[^>]+>|\S+)/gmu;
  for (const match of stripped.matchAll(references)) targets.push(match[1]);

  const html = /\b(?:href|src)=["']([^"']+)["']/giu;
  for (const match of stripped.matchAll(html)) targets.push(match[1]);

  return targets;
}

function resolveLocalTarget(documentPath, rawTarget) {
  const normalized = normalizeTarget(rawTarget);
  if (isExternalOrAnchor(normalized)) return null;

  const withoutFragment = normalized.split('#', 1)[0].split('?', 1)[0];
  if (withoutFragment === '') return null;

  let decoded;
  try {
    decoded = decodeURIComponent(withoutFragment);
  } catch {
    decoded = withoutFragment;
  }

  const absolute = decoded.startsWith('/')
    ? path.resolve(ROOT, decoded.slice(1))
    : path.resolve(path.dirname(documentPath), decoded);

  const relative = path.relative(ROOT, absolute);
  if (relative.startsWith('..') || path.isAbsolute(relative)) {
    throw new Error(`link escapes repository root: ${rawTarget}`);
  }

  return absolute;
}

const documents = [
  ...ROOT_DOCUMENTS.map((file) => path.join(ROOT, file)),
  ...walkMarkdown(path.join(ROOT, 'docs')),
];

const uniqueDocuments = [...new Set(documents)].sort();
const failures = [];
let checkedLinks = 0;

for (const documentPath of uniqueDocuments) {
  const relativeDocument = path.relative(ROOT, documentPath).replaceAll(path.sep, '/');

  if (!existsSync(documentPath) || !statSync(documentPath).isFile()) {
    failures.push(`${relativeDocument}: documentation file is missing`);
    continue;
  }

  const text = readFileSync(documentPath, 'utf8');
  for (const rawTarget of collectTargets(text)) {
    let targetPath;
    try {
      targetPath = resolveLocalTarget(documentPath, rawTarget);
    } catch (error) {
      failures.push(`${relativeDocument}: ${error.message}`);
      continue;
    }

    if (targetPath === null) continue;
    checkedLinks += 1;

    if (!existsSync(targetPath)) {
      const relativeTarget = path.relative(ROOT, targetPath).replaceAll(path.sep, '/');
      failures.push(`${relativeDocument}: ${rawTarget} -> missing ${relativeTarget}`);
    }
  }
}

if (failures.length > 0) {
  console.error(`Documentation link check failed (${failures.length} issue${failures.length === 1 ? '' : 's'}):`);
  for (const failure of failures) console.error(`- ${failure}`);
  process.exit(1);
}

console.log(JSON.stringify({
  status: 'ok',
  documentsChecked: uniqueDocuments.length,
  localLinksChecked: checkedLinks,
  scope: [
    ...ROOT_DOCUMENTS,
    'docs/**/*.md',
  ],
}, null, 2));
