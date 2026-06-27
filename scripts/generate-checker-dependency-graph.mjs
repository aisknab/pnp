#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'GenerateCheckerDependencyGraph0';
const VERSION = 0;
const COORDINATE = 'PNP-CHECKER-DEPENDENCY-GRAPH-2026-06-27-01';
const DEFAULT_OUTPUT_DIR = 'artifacts/checker-dependency-graph';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const SKIP_DIRS = new Set(['.git', '.github', 'node_modules', 'artifacts', 'proof-artifacts', 'successor-report-seals']);
const REQUIRED_CHECKERS = ['CheckMinimalKernel0', 'CheckTrustBase0', 'CheckTrustBaseShrinkPlan0', 'CheckPublicEntryReleaseSurface0', 'CheckRuleFamilyCoverage0'];

export async function GenerateCheckerDependencyGraph0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputDir = options.outputDir ?? DEFAULT_OUTPUT_DIR;
  const writeOutput = options.writeOutput ?? true;

  try {
    const files = [];
    const walk = await walkMjs0(root, '.', files);
    if (walk.tag === 'reject') return writeAndReturn0(root, outputDir, writeOutput, walk);

    const modules = await scanModules0(root, files);
    if (modules.tag === 'reject') return writeAndReturn0(root, outputDir, writeOutput, modules);

    const graph = buildGraph0(modules.modules);
    const validation = validateGraph0(graph);
    if (validation.tag === 'reject') return writeAndReturn0(root, outputDir, writeOutput, validation);

    const jsonText = `${JSON.stringify(graph, null, 2)}\n`;
    const dotText = renderDot0(graph);
    const svgText = renderSvg0(graph);

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORDINATE,
      claimStatus: 'checker-dependency-graph-generated',
      graphPath: `${outputDir}/checker-dependency-graph.json`,
      dotPath: `${outputDir}/checker-dependency-graph.dot`,
      svgPath: `${outputDir}/checker-dependency-graph.svg`,
      graphSha256: sha256Hex0(Buffer.from(jsonText, 'utf8')),
      dotSha256: sha256Hex0(Buffer.from(dotText, 'utf8')),
      svgSha256: sha256Hex0(Buffer.from(svgText, 'utf8')),
      checkerCount: graph.checkerCount,
      dependencyEdgeCount: graph.dependencyEdgeCount,
      moduleImportEdgeCount: graph.moduleImportEdgeCount,
      graphCycleAuditRequired: true,
      noCircularAuthorityProved: false,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputDir: writeOutput ? outputDir : null,
    };

    if (writeOutput) {
      const absoluteDir = path.join(root, outputDir);
      await mkdir(absoluteDir, { recursive: true });
      await writeFile(path.join(absoluteDir, 'checker-dependency-graph.json'), jsonText, 'utf8');
      await writeFile(path.join(absoluteDir, 'checker-dependency-graph.dot'), dotText, 'utf8');
      await writeFile(path.join(absoluteDir, 'checker-dependency-graph.svg'), svgText, 'utf8');
      await writeFile(path.join(absoluteDir, 'latest-verdict.json'), `${JSON.stringify(verdict, null, 2)}\n`, 'utf8');
    }

    return verdict;
  } catch (error) {
    return writeAndReturn0(root, outputDir, writeOutput, reject0('CheckerDependencyGraph.UnhandledException', [], 'checker dependency graph generation threw unexpectedly', normalizeError0(error)));
  }
}

async function walkMjs0(root, relativeDir, files) {
  let entries;
  try {
    entries = await readdir(path.join(root, relativeDir), { withFileTypes: true });
  } catch (error) {
    return reject0('CheckerDependencyGraph.DirectoryReadFailed', [relativeDir], 'could not read repository directory while scanning modules', normalizeError0(error));
  }

  for (const entry of entries.sort((left, right) => left.name.localeCompare(right.name))) {
    const child = relativeDir === '.' ? entry.name : `${relativeDir}/${entry.name}`;
    if (entry.isDirectory()) {
      if (SKIP_DIRS.has(entry.name)) continue;
      const nested = await walkMjs0(root, child, files);
      if (nested.tag === 'reject') return nested;
    } else if (entry.isFile() && entry.name.endsWith('.mjs')) {
      files.push(normalizePath0(child));
    } else if (entry.isSymbolicLink()) {
      return reject0('CheckerDependencyGraph.SymlinkForbidden', [child], 'checker dependency graph scan rejects symlinks');
    }
  }
  return { tag: 'accept' };
}

async function scanModules0(root, files) {
  const modules = [];
  for (const file of files.sort()) {
    let text;
    try {
      text = await readFile(path.join(root, file), 'utf8');
    } catch (error) {
      return reject0('CheckerDependencyGraph.SourceReadFailed', [file], 'could not read source file while scanning dependency graph', normalizeError0(error));
    }
    modules.push({
      file,
      checkerExports: parseCheckerExports0(text),
      imports: parseLocalImports0(file, text),
    });
  }
  return { tag: 'accept', modules };
}

function parseCheckerExports0(text) {
  const pattern = /export\s+(?:async\s+)?function\s+(Check[A-Za-z0-9_]*0)\s*\(/gu;
  const exports = [];
  let match;
  while ((match = pattern.exec(text)) !== null) exports.push(match[1]);
  return [...new Set(exports)].sort();
}

function parseLocalImports0(file, text) {
  const imports = new Set();
  const patterns = [
    /import\s+(?:[^'";]*?\s+from\s+)?['"]([^'"]+)['"]/gu,
    /export\s+[^'";]*?\s+from\s+['"]([^'"]+)['"]/gu,
  ];
  for (const pattern of patterns) {
    let match;
    while ((match = pattern.exec(text)) !== null) {
      const spec = match[1];
      if (!spec.startsWith('.')) continue;
      const resolved = resolveLocalMjs0(file, spec);
      if (resolved !== null) imports.add(resolved);
    }
  }
  return [...imports].sort();
}

function resolveLocalMjs0(file, spec) {
  const fromDir = path.posix.dirname(file);
  let resolved = normalizePath0(path.posix.normalize(path.posix.join(fromDir, spec)));
  if (!resolved.endsWith('.mjs')) resolved += '.mjs';
  if (resolved.startsWith('../') || resolved.startsWith('/')) return null;
  return resolved;
}

function buildGraph0(modules) {
  const modulesByFile = new Map(modules.map((mod) => [mod.file, mod]));
  const checkersByFile = new Map(modules.map((mod) => [mod.file, mod.checkerExports]));
  const nodes = [];
  const edges = [];
  const moduleEdges = [];
  const duplicateTracker = new Map();

  for (const mod of modules) {
    for (const exportName of mod.checkerExports) {
      nodes.push({ id: exportName, file: mod.file });
      duplicateTracker.set(exportName, [...(duplicateTracker.get(exportName) ?? []), mod.file]);
    }
  }

  for (const mod of modules) {
    for (const importedFile of mod.imports) {
      if (!modulesByFile.has(importedFile)) continue;
      moduleEdges.push({ fromFile: mod.file, toFile: importedFile });
      const fromCheckers = checkersByFile.get(mod.file) ?? [];
      const toCheckers = checkersByFile.get(importedFile) ?? [];
      for (const from of fromCheckers) {
        for (const to of toCheckers) {
          if (from !== to) edges.push({ from, to, fromFile: mod.file, toFile: importedFile, kind: 'static-local-import' });
        }
      }
    }
  }

  const uniqueEdges = dedupeEdges0(edges);
  const duplicateExportNames = [...duplicateTracker.entries()]
    .filter(([, files]) => files.length > 1)
    .map(([exportName, files]) => ({ exportName, files: files.sort() }))
    .sort((left, right) => left.exportName.localeCompare(right.exportName));

  return {
    kind: 'PNPCheckerDependencyGraph0',
    version: VERSION,
    coordinate: COORDINATE,
    status: 'checker-dependency-graph-ready',
    generatedFrom: 'current-checkout-static-esm-scan',
    claimBoundary: {
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
    },
    graphReady: true,
    graphCycleAuditRequired: true,
    noCircularAuthorityProved: false,
    checkerCount: nodes.length,
    uniqueCheckerNameCount: new Set(nodes.map((node) => node.id)).size,
    duplicateExportNameCount: duplicateExportNames.length,
    dependencyEdgeCount: uniqueEdges.length,
    moduleFileCount: modules.length,
    moduleImportEdgeCount: moduleEdges.length,
    nodes: nodes.sort((left, right) => left.id.localeCompare(right.id) || left.file.localeCompare(right.file)),
    edges: uniqueEdges.sort((left, right) => left.from.localeCompare(right.from) || left.to.localeCompare(right.to)),
    moduleEdges: moduleEdges.sort((left, right) => left.fromFile.localeCompare(right.fromFile) || left.toFile.localeCompare(right.toFile)),
    duplicateExportNames,
  };
}

function validateGraph0(graph) {
  if (graph.kind !== 'PNPCheckerDependencyGraph0') return reject0('CheckerDependencyGraph.Kind', ['kind'], 'dependency graph kind mismatch');
  if (graph.coordinate !== COORDINATE) return reject0('CheckerDependencyGraph.Coordinate', ['coordinate'], 'dependency graph coordinate mismatch');
  if (graph.graphReady !== true) return reject0('CheckerDependencyGraph.ReadyFlag', ['graphReady'], 'graphReady must be true');
  if (graph.graphCycleAuditRequired !== true) return reject0('CheckerDependencyGraph.CycleAuditFlag', ['graphCycleAuditRequired'], 'graphCycleAuditRequired must be true');
  if (graph.noCircularAuthorityProved !== false) return reject0('CheckerDependencyGraph.NoCircularAuthorityFlag', ['noCircularAuthorityProved'], 'graph generation cannot claim no circular authority');
  const boundary = graph.claimBoundary;
  if (boundary?.publicTheoremEmissionAllowed !== false) return reject0('CheckerDependencyGraph.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary?.finalTheoremReady !== false) return reject0('CheckerDependencyGraph.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary?.activeFinalNodeIds, [])) return reject0('CheckerDependencyGraph.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary?.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('CheckerDependencyGraph.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact');
  const nodeIds = graph.nodes.map((node) => node.id);
  for (const required of REQUIRED_CHECKERS) {
    if (!nodeIds.includes(required)) return reject0('CheckerDependencyGraph.RequiredCheckerMissing', ['nodes'], 'required checker missing from dependency graph', { required });
  }
  for (const edge of graph.edges) {
    if (!nodeIds.includes(edge.from) || !nodeIds.includes(edge.to)) return reject0('CheckerDependencyGraph.DanglingEdge', ['edges'], 'dependency graph contains dangling checker edge', { edge });
  }
  return { tag: 'accept' };
}

function dedupeEdges0(edges) {
  const map = new Map();
  for (const edge of edges) map.set(`${edge.from}->${edge.to}`, edge);
  return [...map.values()];
}

function renderDot0(graph) {
  const lines = [
    'digraph PNPCheckerDependencyGraph0 {',
    '  graph [rankdir=LR];',
    '  node [shape=box, fontsize=10];',
  ];
  for (const node of graph.nodes) lines.push(`  "${dotEscape0(node.id)}" [label="${dotEscape0(node.id)}\\n${dotEscape0(node.file)}"];`);
  for (const edge of graph.edges) lines.push(`  "${dotEscape0(edge.from)}" -> "${dotEscape0(edge.to)}";`);
  lines.push('}');
  return `${lines.join('\n')}\n`;
}

function renderSvg0(graph) {
  const nodes = graph.nodes;
  const columns = 4;
  const boxWidth = 260;
  const boxHeight = 42;
  const xGap = 35;
  const yGap = 18;
  const margin = 20;
  const rows = Math.max(1, Math.ceil(nodes.length / columns));
  const width = margin * 2 + columns * boxWidth + (columns - 1) * xGap;
  const height = margin * 2 + rows * (boxHeight + yGap) + 90;
  const positions = new Map();
  const lines = [`<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" viewBox="0 0 ${width} ${height}">`, '<rect width="100%" height="100%" fill="white"/>', `<text x="${margin}" y="22" font-family="monospace" font-size="16">${xmlEscape0(COORDINATE)}</text>`, `<text x="${margin}" y="43" font-family="monospace" font-size="12">checkerCount=${graph.checkerCount}; dependencyEdgeCount=${graph.dependencyEdgeCount}; cycleAuditRequired=true</text>`];
  nodes.forEach((node, index) => {
    const col = index % columns;
    const row = Math.floor(index / columns);
    const x = margin + col * (boxWidth + xGap);
    const y = margin + 70 + row * (boxHeight + yGap);
    positions.set(node.id, { x, y });
  });
  for (const edge of graph.edges.slice(0, 300)) {
    const from = positions.get(edge.from);
    const to = positions.get(edge.to);
    if (!from || !to) continue;
    lines.push(`<line x1="${from.x + boxWidth}" y1="${from.y + boxHeight / 2}" x2="${to.x}" y2="${to.y + boxHeight / 2}" stroke="#999" stroke-width="0.6" opacity="0.35"/>`);
  }
  for (const node of nodes) {
    const pos = positions.get(node.id);
    lines.push(`<rect x="${pos.x}" y="${pos.y}" width="${boxWidth}" height="${boxHeight}" fill="#f8f8f8" stroke="#333" stroke-width="0.8"/>`);
    lines.push(`<text x="${pos.x + 6}" y="${pos.y + 16}" font-family="monospace" font-size="10">${xmlEscape0(node.id)}</text>`);
    lines.push(`<text x="${pos.x + 6}" y="${pos.y + 31}" font-family="monospace" font-size="8">${xmlEscape0(node.file)}</text>`);
  }
  lines.push('</svg>');
  return `${lines.join('\n')}\n`;
}

function dotEscape0(text) { return String(text).replace(/\\/gu, '\\\\').replace(/"/gu, '\\"'); }
function xmlEscape0(text) { return String(text).replace(/&/gu, '&amp;').replace(/</gu, '&lt;').replace(/>/gu, '&gt;').replace(/"/gu, '&quot;'); }

function reject0(coord, pathArray, reason, witness = {}) {
  return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...EXPECTED_BLOCKERS] };
}

async function writeAndReturn0(root, outputDir, writeOutput, verdict) {
  if (writeOutput) {
    const absoluteDir = path.join(root, outputDir);
    await mkdir(absoluteDir, { recursive: true });
    await writeFile(path.join(absoluteDir, 'latest-verdict.json'), `${JSON.stringify(verdict, null, 2)}\n`, 'utf8');
  }
  return { ...verdict, outputDir: writeOutput ? outputDir : null };
}

function normalizePath0(p) { return p.replace(/\\/gu, '/').replace(/^\.\//u, ''); }
function sameArray0(left, right) { return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]); }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }

function parseArgs0(argv) {
  const options = { root: process.cwd(), outputDir: DEFAULT_OUTPUT_DIR, writeOutput: true, json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') options.root = requireValue0(argv, ++index, '--root');
    else if (arg === '--output-dir') options.outputDir = requireValue0(argv, ++index, '--output-dir');
    else if (arg === '--help' || arg === '-h') { printHelp0(); process.exit(0); }
    else throw new Error(`unknown argument: ${arg}`);
  }
  return options;
}

function requireValue0(argv, index, flag) { if (index >= argv.length) throw new Error(`${flag} requires a value`); return argv[index]; }
function printHelp0() { console.log(`Usage: node scripts/generate-checker-dependency-graph.mjs [options]\n\nOptions:\n  --json                Emit verdict JSON.\n  --no-write            Do not write graph artifacts.\n  --root <path>         Repository root. Defaults to cwd.\n  --output-dir <path>   Artifact directory relative to root.\n`); }

async function main0() {
  let options;
  try { options = parseArgs0(process.argv.slice(2)); }
  catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad checker dependency graph CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }
  const verdict = await GenerateCheckerDependencyGraph0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
