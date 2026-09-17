import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFile, readdir } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const LEAN_ROOT = path.join(ROOT, 'lean');
const EXPECTED_AXIOMS = Object.freeze([]);
// Only these explicit imports belong to the already pinned Lean toolchain.
// The project-source closure must still reject unknown external namespaces.
const PINNED_TOOLCHAIN_IMPORTS = new Set([
  'Init.Data.List.Erase',
  'Init.Data.List.FinRange',
  'Init.Data.List.Sort.Lemmas',
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

async function leanSources0() {
  const files = await filesBelow0(LEAN_ROOT);
  return Object.fromEntries(await Promise.all(files
    .filter((file) => file.endsWith('.lean'))
    .sort()
    .map(async (file) => [path.relative(ROOT, file).replaceAll(path.sep, '/'), await readFile(file, 'utf8')])));
}

async function filesBelow0(directory) {
  const entries = await readdir(directory, { withFileTypes: true });
  const nested = await Promise.all(entries.map((entry) => {
    const child = path.join(directory, entry.name);
    return entry.isDirectory() ? filesBelow0(child) : [child];
  }));
  return nested.flat();
}

function declarationInventory0(sources) {
  const declarations = [];
  const forbiddenTokens = [];
  for (const [file, original] of Object.entries(sources)) {
    const source = stripLeanCommentsAndStrings0(original);
    const namespace = /^\s*namespace\s+([A-Za-z_][\w.]*)/mu.exec(source)?.[1] ?? '';
    for (const match of source.matchAll(/^\s*(?:@\[[^\]\n]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*(axiom|constant|opaque)\s+(«[^»\n]+»|[^\s(:]+)(?=\s*[:({\[])/gmu)) {
      declarations.push({
        file,
        kind: match[1],
        name: namespace === '' ? match[2] : `${namespace}.${match[2]}`,
      });
    }
    for (const match of source.matchAll(/\b(sorry|admit|unsafe|native_decide)\b/gu)) {
      forbiddenTokens.push({ file, token: match[1] });
    }
  }
  return { declarations, forbiddenTokens };
}

function stripLeanCommentsAndStrings0(source) {
  let out = '';
  let index = 0;
  let blockDepth = 0;
  let lineComment = false;
  let string = false;
  while (index < source.length) {
    const here = source[index];
    const next = source[index + 1] ?? '';
    if (lineComment) {
      if (here === '\n') {
        lineComment = false;
        out += '\n';
      } else out += ' ';
      index += 1;
      continue;
    }
    if (blockDepth > 0) {
      if (here === '/' && next === '-') {
        blockDepth += 1;
        out += '  ';
        index += 2;
      } else if (here === '-' && next === '/') {
        blockDepth -= 1;
        out += '  ';
        index += 2;
      } else {
        out += here === '\n' ? '\n' : ' ';
        index += 1;
      }
      continue;
    }
    if (string) {
      if (here === '\\') {
        out += '  ';
        index += Math.min(2, source.length - index);
      } else if (here === '"') {
        string = false;
        out += ' ';
        index += 1;
      } else {
        out += here === '\n' ? '\n' : ' ';
        index += 1;
      }
      continue;
    }
    if (here === '-' && next === '-') {
      lineComment = true;
      out += '  ';
      index += 2;
    } else if (here === '/' && next === '-') {
      blockDepth = 1;
      out += '  ';
      index += 2;
    } else if (here === '"') {
      string = true;
      out += ' ';
      index += 1;
    } else {
      out += here;
      index += 1;
    }
  }
  return out;
}

function importedModules0(source) {
  return [...source.matchAll(/^\s*import\s+([A-Za-z_][\w.]*)\s*$/gmu)].map((match) => match[1]);
}

function modulePath0(moduleName) {
  if (moduleName === 'PNP') return 'lean/PNP.lean';
  if (!moduleName.startsWith('PNP.')) return null;
  return `lean/${moduleName.replaceAll('.', '/')}.lean`;
}

function importClosure0(sources, rootModule) {
  const seen = new Set();
  const pending = [rootModule];
  while (pending.length !== 0) {
    const moduleName = pending.pop();
    if (PINNED_TOOLCHAIN_IMPORTS.has(moduleName)) continue;
    if (seen.has(moduleName)) continue;
    seen.add(moduleName);
    const file = modulePath0(moduleName);
    assert.notEqual(file, null, `non-PNP import in root closure: ${moduleName}`);
    assert.equal(Object.hasOwn(sources, file), true, `missing module source: ${moduleName}`);
    pending.push(...importedModules0(sources[file]));
  }
  return [...seen].map(modulePath0).sort();
}

test('Lean toolchain, library root, and root status are explicit and non-theorem-bearing', async () => {
  assert.equal((await text0('lean-toolchain')).trim(), 'leanprover/lean4:v4.31.0');

  const lakefile = await text0('lakefile.lean');
  assert.match(lakefile, /@\[default_target\]\s*\nlean_lib PNP where/u);
  assert.match(lakefile, /roots\s*:=\s*#\[`PNP\]/u);

  const aggregate = await text0('lean/PNP.lean');
  assert.match(aggregate, /^import PNP\.Main$/mu);

  const main = await text0('lean/PNP/Main.lean');
  assert.doesNotMatch(main, /^\s*import\s+/mu);
  assert.match(main, /namespace PNP\.Main/u);
  assert.match(main, /standardStatementFormalized\s*:=\s*true/u);
  assert.match(main, /unconditionalProofPresent\s*:=\s*false/u);
  assert.match(main, /externalAssumptionsRemain\s*:=\s*true/u);
  assert.match(main, /publicTheoremReleased\s*:=\s*false/u);
  assert.doesNotMatch(main, /\b(?:PEqualsNP|PClass|NPClass|p_eq_np|axiom|constant|opaque|sorry|admit)\b/u);
});

test('PNP root import closure covers every tracked Lean source module', async () => {
  const sources = await leanSources0();
  const closure = importClosure0(sources, 'PNP');
  assert.deepEqual(closure, Object.keys(sources).sort());
});

test('root closure separates reviewed pinned-toolchain imports from project source', () => {
  const sources = {
    'lean/PNP.lean': 'import PNP.Leaf\nimport Init.Data.List.FinRange\n',
    'lean/PNP/Leaf.lean': 'import Init.Data.List.Erase\nimport Init.Data.List.FinRange\n',
  };
  assert.deepEqual(importClosure0(sources, 'PNP'), Object.keys(sources).sort());
});

test('root closure still rejects unknown external imports and missing project modules', () => {
  for (const moduleName of [
    'Unreviewed.Package',
    'Init.Data.List.Unreviewed',
    'Init.Data.List.Erase.Unreviewed',
    'Std.Unreviewed',
  ]) {
    assert.throws(() => importClosure0({
      'lean/PNP.lean': 'import ' + moduleName + '\n',
    }, 'PNP'), /non-PNP import in root closure/u);
  }
  assert.throws(() => importClosure0({
    'lean/PNP.lean': 'import PNP.Missing\n',
  }, 'PNP'), /missing module source: PNP.Missing/u);
});

test('Lean source has no project axioms or hidden placeholders', async () => {
  const inventory = declarationInventory0(await leanSources0());
  assert.deepEqual(inventory.forbiddenTokens, []);
  assert.deepEqual(inventory.declarations.filter(({ kind }) => kind !== 'axiom'), []);
  assert.deepEqual(inventory.declarations.map(({ name }) => name).sort(), [...EXPECTED_AXIOMS]);
});

test('Lean axiom audit distinguishes assumption-free status data from the conditional bridge', async () => {
  const audit = await text0('lean-audit/PNPBridgeAxiomAudit.lean');
  assert.equal(importedModules0(audit).includes('PNP'), true);
  for (const declaration of [
    'PNP.Main.rootTheoremStatus',
    'PNP.Main.rootTheoremStatus_not_released',
    'PNP.Main.rootTheoremStatus_has_external_assumptions',
    'PNP.Main.ConcretePEqualsNP',
    'PNP.Main.concretePEqualsNP_iff',
    'PNP.Main.locked_nand_threshold',
    'PNP.accepted_generated_package_implies_p_eq_np',
    'PNP.final_report_bridge',
  ]) assert.match(audit, new RegExp(`#print axioms ${declaration.replaceAll('.', '\\.')}\\b`, 'u'));
  assert.doesNotMatch(audit, /PNP\.Main\.p_eq_np/u);
});

test('Lean workflow pins the installer and performs one real explicit-root build', async () => {
  const [workflow, inventoryExporter] = await Promise.all([
    text0('.github/workflows/lean-bridge.yml'),
    text0('scripts/export-lean-theorem-inventory.mjs'),
  ]);
  assert.match(workflow, /runs-on: ubuntu-24\.04/u);
  assert.match(workflow, /actions\/checkout@9c091bb21b7c1c1d1991bb908d89e4e9dddfe3e0/u);
  assert.match(workflow, /leanprover\/elan\/releases\/download\/v4\.2\.3\/elan-x86_64-unknown-linux-gnu\.tar\.gz/u);
  assert.match(workflow, /df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2/u);
  assert.match(workflow, /Lean \(version 4\.31\.0/u);
  assert.match(workflow, /68218e876d2a38b1985b8590fff244a83c321783/u);
  assert.match(workflow, /Lake version 5\.0\.0-src\+68218e8/u);
  assert.match(workflow, /run: npm run formal:inventory:check/u);
  assert.match(inventoryExporter,
    /execFileAsync\('lake', \['build', 'PNP'\]/u);
  assert.match(inventoryExporter, /const BUILD_TIMEOUT_MS = 1_800_000;/u);
  assert.match(inventoryExporter, /const PROBE_TIMEOUT_MS = 600_000;/u);
  assert.match(inventoryExporter,
    /export const INVENTORY_MAX_BUFFER_BYTES = 128 \* 1024 \* 1024;/u);
  assert.match(inventoryExporter,
    /\['build', 'PNP'\][\s\S]*?timeout: BUILD_TIMEOUT_MS/u);
  assert.equal((inventoryExporter.match(/maxBuffer: INVENTORY_MAX_BUFFER_BYTES/gu)
    ?? []).length, 2);
  assert.doesNotMatch(workflow, /run: lake build PNP/u);
  assert.match(workflow, /lake env lean -DwarningAsError=true lean-audit\/PNPBridgeAxiomAudit\.lean/u);
  assert.doesNotMatch(workflow, /lean4:stable|elan\/master|\brun: lake build\s*$/mu);
});

test('Lean declaration inventory fails closed on an extra axiom or placeholder', async () => {
  const sources = await leanSources0();
  const extraAxiom = structuredClone(sources);
  extraAxiom['lean/PNP/Main.lean'] += '\naxiom p_eq_np : True\n';
  const axiomInventory = declarationInventory0(extraAxiom);
  assert.equal(axiomInventory.declarations.some(({ name }) => name === 'PNP.Main.p_eq_np'), true);
  assert.notDeepEqual(axiomInventory.declarations.map(({ name }) => name).sort(), [...EXPECTED_AXIOMS]);

  const privateAxiom = structuredClone(sources);
  privateAxiom['lean/PNP/Main.lean'] += '\nprivate axiom hidden_private : True\n';
  assert.equal(declarationInventory0(privateAxiom).declarations.some(({ name }) => name === 'PNP.Main.hidden_private'), true);

  const quotedAxiom = structuredClone(sources);
  quotedAxiom['lean/PNP/Main.lean'] += '\naxiom «hidden-name» : True\n';
  assert.equal(declarationInventory0(quotedAxiom).declarations.some(({ name }) => name === 'PNP.Main.«hidden-name»'), true);

  const unicodeAxiom = structuredClone(sources);
  unicodeAxiom['lean/PNP/Main.lean'] += '\naxiom 隠し : True\n';
  assert.equal(declarationInventory0(unicodeAxiom).declarations.some(({ name }) => name === 'PNP.Main.隠し'), true);

  const placeholder = structuredClone(sources);
  placeholder['lean/PNP/Main.lean'] += '\ntheorem hidden : True := by sorry\n';
  assert.deepEqual(declarationInventory0(placeholder).forbiddenTokens, [
    { file: 'lean/PNP/Main.lean', token: 'sorry' },
  ]);
});

// Fail before provider-side workflow rejection, with headroom below 500 KiB.
// Provider limit: https://docs.github.com/en/actions/reference/limits
const WORKFLOW_REVIEW_BYTES = 480_000;

function workflowSizeAccepted0(source) {
  return Buffer.byteLength(source, 'utf8') <= WORKFLOW_REVIEW_BYTES;
}

test('durable workflow files retain reviewed provider size headroom', async () => {
  const entries = await readdir(path.join(ROOT, '.github/workflows'));
  for (const file of entries.filter((name) => /\.ya?ml$/u.test(name))) {
    const source = await text0('.github/workflows/' + file);
    assert.equal(workflowSizeAccepted0(source), true,
      file + ' exceeds the 480,000-byte review budget; compact orchestration without removing checks');
  }
});

test('workflow size guard counts encoded bytes and rejects oversized input', () => {
  assert.equal(workflowSizeAccepted0('x'.repeat(WORKFLOW_REVIEW_BYTES)), true);
  assert.equal(workflowSizeAccepted0('x'.repeat(WORKFLOW_REVIEW_BYTES + 1)), false);
  assert.equal(workflowSizeAccepted0('é'.repeat(WORKFLOW_REVIEW_BYTES / 2)), true);
  assert.equal(workflowSizeAccepted0('é'.repeat(WORKFLOW_REVIEW_BYTES / 2 + 1)), false);
});

test('Lean workflow keeps current-milestone trigger families compact', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.equal((workflow.match(/^      - 'audits\/lean-\*\.test\.mjs'$/gmu) ?? []).length, 2);
  assert.equal((workflow.match(/^      - 'docs\/lean_\*\.md'$/gmu) ?? []).length, 2);
  assert.equal((workflow.match(/^      - 'docs\/plans\/\*\.md'$/gmu) ?? []).length, 2);
  assert.doesNotMatch(workflow, /^      - 'docs\/plans\/[^*'\n]+\.md'$/mu);
  assert.doesNotMatch(workflow, /^      - 'audits\/lean-[^/*]+\.test\.mjs'$/mu);
  assert.doesNotMatch(workflow, /^      - 'docs\/lean_[^/*]+\.md'$/mu);
});

// This deliberately parses only literal YAML run blocks, not arbitrary YAML.
// Unsupported multiline styles fail closed instead of silently losing coverage.
function literalWorkflowRunBlocks0(source) {
  const lines = source.replaceAll('\r\n', '\n').split('\n');
  const blocks = [];
  for (let index = 0; index < lines.length; index += 1) {
    const header = /^( *)(?:- +)?run: *([|>][^#]*)(?:#.*)?$/u.exec(lines[index]);
    if (header === null) continue;
    const style = header[2].trim();
    assert.match(style, /^\|[+-]?$/u, 'unsupported multiline workflow run style');
    const keyIndent = lines[index].indexOf('run:');
    let bodyIndent = null;
    let end = index + 1;
    const body = [];
    for (; end < lines.length; end += 1) {
      if (lines[end].trim() === '') {
        body.push('');
        continue;
      }
      const indent = /^ */u.exec(lines[end])[0].length;
      if (indent <= keyIndent) break;
      bodyIndent ??= indent;
      assert.ok(indent >= bodyIndent, 'inconsistent literal workflow block indentation');
      body.push(lines[end].slice(bodyIndent));
    }
    assert.notEqual(bodyIndent, null, 'empty literal workflow run block');
    let script = body.join('\n');
    if (style !== '|+') script = script.replace(/\n+$/u, '');
    if (style !== '|-') script += '\n';
    blocks.push({ line: index + 1, script });
    index = end - 1;
  }
  return blocks;
}

function bashSyntax0(script) {
  return spawnSync('bash', ['--noprofile', '--norc', '-n'], {
    input: script,
    encoding: 'utf8',
    timeout: 5_000,
    maxBuffer: 64 * 1024,
  });
}

function anchoredAxiomFilter0(line) {
  return line.endsWith("\\]$' || true)\"");
}

test('all durable literal workflow run blocks pass Bash syntax before proof builds', async () => {
  const entries = (await readdir(path.join(ROOT, '.github/workflows')))
    .filter((name) => /\.ya?ml$/u.test(name)).sort();
  let checked = 0;
  for (const file of entries) {
    const source = await text0('.github/workflows/' + file);
    for (const match of source.matchAll(/^ *shell: *(.+)$/gmu)) {
      assert.equal(match[1].trim(), 'bash', 'review non-Bash workflow syntax separately');
    }
    const blocks = literalWorkflowRunBlocks0(source);
    for (const block of blocks) {
      const result = bashSyntax0(block.script);
      assert.equal(result.error, undefined, 'Bash syntax-check launch failed');
      assert.equal(result.status, 0, file + ':' + block.line + '\n' + result.stderr);
      checked += 1;
    }
  }
  assert.ok(checked > 0, 'workflow syntax coverage must not be empty');
});

test('workflow block extraction preserves complete heredocs, nesting and boundaries', () => {
  const body = [
    'if true; then',
    "  cat <<'TEXT'",
    '  run: |',
    'TEXT',
    'fi',
  ].join('\n');
  const source = [
    'steps:',
    '  - run: |-',
    ...body.split('\n').map((line) => '      ' + line),
    '    env:',
    '      MODE: regression',
    '  - name: next',
    '    run: |',
    '      exit 97',
    '',
  ].join('\n');
  const blocks = literalWorkflowRunBlocks0(source);
  assert.equal(blocks.length, 2);
  assert.equal(blocks[0].script, body);
  assert.equal(blocks[1].script, 'exit 97\n');
  assert.equal(bashSyntax0(blocks[0].script).status, 0);
  // Syntax-only verification must not execute the workflow's commands.
  assert.equal(bashSyntax0(blocks[1].script).status, 0);
  assert.throws(() => literalWorkflowRunBlocks0('run: >\n  echo folded\n'),
    /unsupported multiline workflow run style/u);
  assert.throws(() => literalWorkflowRunBlocks0('run: |\n'),
    /empty literal workflow run block/u);
  assert.throws(() => literalWorkflowRunBlocks0('run: |\n    echo one\n  echo two\n'),
    /inconsistent literal workflow block indentation/u);
});

test('workflow syntax guard rejects unmatched quotes, substitutions and incomplete branches', () => {
  for (const script of [
    "printf '%s\\n' 'unterminated\n",
    'value="$(printf test"\n',
    'if true; then\n  printf test\n',
  ]) {
    const result = bashSyntax0(script);
    assert.equal(result.error, undefined);
    assert.notEqual(result.status, 0);
  }
});

test('standard-axiom exclusion filters retain their closing quote and end anchor', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const filters = workflow.split('\n')
    .filter((line) => line.includes("grep -Ev 'depends on axioms: "));
  assert.ok(filters.length > 0, 'axiom-filter coverage must not be empty');
  for (const line of filters) assert.equal(anchoredAxiomFilter0(line), true, line);
  const valid = filters[0];
  const unclosed = valid.replace("\\]$'", () => '\\]');
  assert.equal(anchoredAxiomFilter0(unclosed), false);
  assert.notEqual(bashSyntax0(unclosed).status, 0);
  const unanchored = valid.replace("\\]$'", () => "\\]'");
  assert.equal(bashSyntax0(unanchored).status, 0);
  assert.equal(anchoredAxiomFilter0(unanchored), false,
    'valid shell syntax must not excuse a weakened axiom filter');
});
