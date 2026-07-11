import assert from 'node:assert/strict';
import { readFile, readdir } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const LEAN_ROOT = path.join(ROOT, 'lean');
const EXPECTED_AXIOMS = Object.freeze([
  'PNP.CheckPCCPackexp',
  'PNP.GeneratePCCPack',
  'PNP.LockedNANDThreshold',
  'PNP.ResidualBandExactMinimization',
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
    for (const match of source.matchAll(/^\s*(?:@\[[^\]\n]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*(axiom|constant|opaque)\s+(«[^»\n]+»|[^\s(:]+)/gmu)) {
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

test('Lean source has exactly four disclosed project axioms and no hidden placeholders', async () => {
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
    'PNP.accepted_generated_package_implies_p_eq_np',
    'PNP.final_report_bridge',
  ]) assert.match(audit, new RegExp(`#print axioms ${declaration.replaceAll('.', '\\.')}\\b`, 'u'));
  assert.doesNotMatch(audit, /PNP\.Main\.p_eq_np/u);
});

test('Lean workflow pins the installer and performs a real explicit-root build', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow, /runs-on: ubuntu-24\.04/u);
  assert.match(workflow, /actions\/checkout@9c091bb21b7c1c1d1991bb908d89e4e9dddfe3e0/u);
  assert.match(workflow, /leanprover\/elan\/releases\/download\/v4\.2\.3\/elan-x86_64-unknown-linux-gnu\.tar\.gz/u);
  assert.match(workflow, /df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2/u);
  assert.match(workflow, /Lean \(version 4\.31\.0/u);
  assert.match(workflow, /68218e876d2a38b1985b8590fff244a83c321783/u);
  assert.match(workflow, /Lake version 5\.0\.0-src\+68218e8/u);
  assert.match(workflow, /run: lake build PNP/u);
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
