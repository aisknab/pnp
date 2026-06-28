#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import { GenerateCheckerDependencyGraph0 } from './generate-checker-dependency-graph.mjs';

const CHECKER = 'AuditCheckerCycles0';
const VERSION = 0;
const MANIFEST_PATH = 'checker-cycles/CHECKER_AUTHORITY_GRAPH.json';
const DEFAULT_OUTPUT_DIR = 'artifacts/checker-cycles';
const EXPECTED_COORDINATE = 'PNP-CHECKER-AUTHORITY-GRAPH-2026-06-27-01';
const EXPECTED_DEPENDENCY_GRAPH_COORDINATE = 'PNP-CHECKER-DEPENDENCY-GRAPH-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_NODE_IDS = [
  'CheckPublicEntryReleaseSurface0',
  'CheckMinimalKernel0',
  'CheckTrustBase0',
  'CheckTrustBaseShrinkPlan0',
  'CheckRuleFamilyCoverage0',
  'AuditCheckerTotality0',
  'AuditNegativeCheckerMutations0',
  'GenerateCheckerDependencyGraph0',
  'AuditCheckerCycles0',
  'RunPNPVerifyAll0',
];

export async function AuditCheckerCycles0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const manifestPath = options.manifestPath ?? MANIFEST_PATH;
  const outputDir = options.outputDir ?? DEFAULT_OUTPUT_DIR;
  const writeOutput = options.writeOutput ?? true;

  try {
    const manifestRead = await readManifest0({ root, manifestPath, override: options.manifestOverride });
    if (manifestRead.tag === 'reject') return writeAndReturn0(root, outputDir, writeOutput, manifestRead);

    const manifestCheck = validateManifest0(manifestRead.manifest);
    if (manifestCheck.tag === 'reject') return writeAndReturn0(root, outputDir, writeOutput, manifestCheck);

    const generatedGraph = await GenerateCheckerDependencyGraph0({
      root,
      outputDir: `${outputDir}/generated-dependency-graph`,
      writeOutput,
    });
    if (generatedGraph.tag !== 'accept') {
      return writeAndReturn0(root, outputDir, writeOutput, reject0('CheckerCycles.DependencyGraphGenerationFailed', ['dependencyGraph'], 'checker dependency graph generation failed', { generatedGraph }));
    }

    const graphCheck = await validateGeneratedGraph0({ root, outputDir, writeOutput, generatedGraph });
    if (graphCheck.tag === 'reject') return writeAndReturn0(root, outputDir, writeOutput, graphCheck);

    const cycleCheck = detectAuthorityCycle0(manifestRead.manifest);
    if (cycleCheck.tag === 'reject') return writeAndReturn0(root, outputDir, writeOutput, cycleCheck);

    const graphArtifactText = graphCheck.graphText ?? '';
    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      dependencyGraphCoordinate: EXPECTED_DEPENDENCY_GRAPH_COORDINATE,
      claimStatus: 'checker-authority-graph-acyclic',
      manifestPath,
      manifestSha256: sha256Hex0(manifestRead.bytes),
      generatedDependencyGraphSha256: graphArtifactText.length === 0 ? generatedGraph.graphSha256 : sha256Hex0(Buffer.from(graphArtifactText, 'utf8')),
      authorityGraphReady: true,
      noCircularAuthorityProved: true,
      fullStaticImportCycleFreedomProved: false,
      staticDependencyCyclesAreAuthorityOnlyWhenDeclared: true,
      nodeCount: manifestRead.manifest.nodes.length,
      authorityEdgeCount: manifestRead.manifest.authorityEdges.length,
      checkedCycleCount: 0,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputDir: writeOutput ? outputDir : null,
    };

    return writeAndReturn0(root, outputDir, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputDir, writeOutput, reject0('CheckerCycles.UnhandledException', [], 'checker cycle audit threw unexpectedly', normalizeError0(error)));
  }
}

async function readManifest0({ root, manifestPath, override }) {
  if (override !== undefined) {
    const bytes = Buffer.from(JSON.stringify(override, null, 2) + '\n', 'utf8');
    return { tag: 'accept', manifest: override, bytes };
  }
  try {
    const bytes = await readFile(path.join(root, manifestPath));
    return { tag: 'accept', manifest: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('CheckerCycles.ManifestReadOrParseFailed', [manifestPath], 'could not read or parse checker authority graph manifest', normalizeError0(error));
  }
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('CheckerCycles.ManifestShape', [], 'manifest must be an object');
  if (manifest.kind !== 'PNPCheckerAuthorityGraph0') return reject0('CheckerCycles.ManifestKind', ['kind'], 'manifest kind mismatch');
  if (manifest.version !== VERSION) return reject0('CheckerCycles.ManifestVersion', ['version'], 'manifest version mismatch');
  if (manifest.coordinate !== EXPECTED_COORDINATE) return reject0('CheckerCycles.ManifestCoordinate', ['coordinate'], 'manifest coordinate mismatch', { expected: EXPECTED_COORDINATE, actual: manifest.coordinate });
  if (manifest.status !== 'checker-authority-graph-ready') return reject0('CheckerCycles.ManifestStatus', ['status'], 'manifest status mismatch');
  if (manifest.dependencyGraphCoordinate !== EXPECTED_DEPENDENCY_GRAPH_COORDINATE) return reject0('CheckerCycles.DependencyGraphCoordinate', ['dependencyGraphCoordinate'], 'linked dependency graph coordinate mismatch');
  if (manifest.authorityGraphReady !== true) return reject0('CheckerCycles.AuthorityReadyFlag', ['authorityGraphReady'], 'authorityGraphReady must be true');
  if (manifest.noCircularAuthorityProved !== true) return reject0('CheckerCycles.NoCircularAuthorityFlag', ['noCircularAuthorityProved'], 'cycle audit must prove no circular authority for declared authority edges');
  if (manifest.fullStaticImportCycleFreedomProved !== false) return reject0('CheckerCycles.StaticCycleFreedomFlag', ['fullStaticImportCycleFreedomProved'], 'authority audit must not claim full static import cycle freedom');
  if (manifest.staticDependencyCyclesAreAuthorityOnlyWhenDeclared !== true) return reject0('CheckerCycles.StaticAuthorityDisciplineFlag', ['staticDependencyCyclesAreAuthorityOnlyWhenDeclared'], 'static dependency cycles must be authority only when explicitly declared');

  const boundary = validateBoundary0(manifest.claimBoundary);
  if (boundary.tag === 'reject') return boundary;

  if (!Array.isArray(manifest.nodes)) return reject0('CheckerCycles.NodesShape', ['nodes'], 'nodes must be an array');
  const nodeIds = manifest.nodes.map((node) => node?.id);
  if (!sameArray0(nodeIds, EXPECTED_NODE_IDS)) return reject0('CheckerCycles.NodeIds', ['nodes'], 'authority graph node ids must stay exact and ordered', { expected: EXPECTED_NODE_IDS, actual: nodeIds });
  const nodeIdSet = new Set(nodeIds);
  for (let index = 0; index < manifest.nodes.length; index += 1) {
    const node = manifest.nodes[index];
    const nodePath = ['nodes', index];
    if (!plain0(node)) return reject0('CheckerCycles.NodeShape', nodePath, 'authority graph node must be an object');
    for (const field of ['id', 'type', 'file', 'conclusion']) {
      if (!nonempty0(node[field])) return reject0('CheckerCycles.NodeField', [...nodePath, field], 'authority graph node field must be a non-empty string');
    }
    if (!['checker', 'audit', 'generator', 'runner'].includes(node.type)) return reject0('CheckerCycles.NodeType', [...nodePath, 'type'], 'authority graph node type mismatch', { type: node.type });
    if (!node.file.endsWith('.mjs')) return reject0('CheckerCycles.NodeFile', [...nodePath, 'file'], 'authority graph node file must be an .mjs path');
  }

  if (!Array.isArray(manifest.authorityEdges) || manifest.authorityEdges.length === 0) return reject0('CheckerCycles.EdgesShape', ['authorityEdges'], 'authorityEdges must be a non-empty array');
  const edgeKeys = new Set();
  for (let index = 0; index < manifest.authorityEdges.length; index += 1) {
    const edge = manifest.authorityEdges[index];
    const edgePath = ['authorityEdges', index];
    if (!plain0(edge)) return reject0('CheckerCycles.EdgeShape', edgePath, 'authority edge must be an object');
    for (const field of ['from', 'to', 'kind', 'description']) {
      if (!nonempty0(edge[field])) return reject0('CheckerCycles.EdgeField', [...edgePath, field], 'authority edge field must be a non-empty string');
    }
    if (edge.kind !== 'authority-premise') return reject0('CheckerCycles.EdgeKind', [...edgePath, 'kind'], 'authority edge kind must be authority-premise');
    if (!nodeIdSet.has(edge.from)) return reject0('CheckerCycles.EdgeUnknownFrom', [...edgePath, 'from'], 'authority edge references unknown source node', { from: edge.from });
    if (!nodeIdSet.has(edge.to)) return reject0('CheckerCycles.EdgeUnknownTo', [...edgePath, 'to'], 'authority edge references unknown target node', { to: edge.to });
    if (edge.from === edge.to) return reject0('CheckerCycles.SelfEdge', edgePath, 'authority graph cannot contain self-edge', { edge });
    const key = `${edge.from}->${edge.to}`;
    if (edgeKeys.has(key)) return reject0('CheckerCycles.DuplicateEdge', edgePath, 'authority graph cannot contain duplicate edges', { key });
    edgeKeys.add(key);
  }

  if (!plain0(manifest.audit)) return reject0('CheckerCycles.AuditShape', ['audit'], 'audit must be an object');
  const expectedAudit = {
    checker: CHECKER,
    script: 'scripts/audit-checker-cycles.mjs',
    command: 'npm run checker:cycles',
    expectedAcceptTag: 'accept',
  };
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (manifest.audit[key] !== expected) return reject0('CheckerCycles.AuditField', ['audit', key], 'audit field mismatch', { expected, actual: manifest.audit[key] });
  }

  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('CheckerCycles.BoundaryShape', ['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('CheckerCycles.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('CheckerCycles.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('CheckerCycles.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('CheckerCycles.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact');
  return { tag: 'accept' };
}

async function validateGeneratedGraph0({ root, outputDir, writeOutput, generatedGraph }) {
  if (generatedGraph.coordinate !== EXPECTED_DEPENDENCY_GRAPH_COORDINATE) return reject0('CheckerCycles.GeneratedGraphCoordinate', ['generatedDependencyGraph', 'coordinate'], 'generated checker dependency graph coordinate mismatch', { actual: generatedGraph.coordinate });
  if (generatedGraph.graphCycleAuditRequired !== true) return reject0('CheckerCycles.GeneratedGraphCycleFlag', ['generatedDependencyGraph', 'graphCycleAuditRequired'], 'dependency graph must require cycle audit');
  if (generatedGraph.noCircularAuthorityProved !== false) return reject0('CheckerCycles.GeneratedGraphOverclaim', ['generatedDependencyGraph', 'noCircularAuthorityProved'], 'dependency graph generation must not itself claim no circular authority');

  if (!writeOutput) return { tag: 'accept', graphText: '' };

  try {
    const graphPath = path.join(root, outputDir, 'generated-dependency-graph', 'checker-dependency-graph.json');
    const graphText = await readFile(graphPath, 'utf8');
    const graph = JSON.parse(graphText);
    const nodeIds = new Set((graph.nodes ?? []).map((node) => node.id));
    for (const required of ['CheckPublicEntryReleaseSurface0', 'CheckMinimalKernel0', 'CheckTrustBase0', 'CheckTrustBaseShrinkPlan0', 'CheckRuleFamilyCoverage0']) {
      if (!nodeIds.has(required)) return reject0('CheckerCycles.RequiredCheckerMissingFromStaticGraph', ['generatedDependencyGraph', 'nodes'], 'required checker missing from generated static dependency graph', { required });
    }
    return { tag: 'accept', graphText };
  } catch (error) {
    return reject0('CheckerCycles.GeneratedGraphReadFailed', ['generatedDependencyGraph'], 'could not read generated dependency graph artifact', normalizeError0(error));
  }
}

function detectAuthorityCycle0(manifest) {
  const adjacency = new Map(manifest.nodes.map((node) => [node.id, []]));
  for (const edge of manifest.authorityEdges) adjacency.get(edge.from).push(edge.to);

  const color = new Map(manifest.nodes.map((node) => [node.id, 'white']));
  const stack = [];

  function visit(node) {
    color.set(node, 'gray');
    stack.push(node);
    for (const next of adjacency.get(node) ?? []) {
      if (color.get(next) === 'gray') {
        const start = stack.indexOf(next);
        const cycle = [...stack.slice(start), next];
        return reject0('CheckerCycles.AuthorityCycleDetected', ['authorityEdges'], 'checker conclusion re-enters its own premise chain through declared authority edges', { cycle });
      }
      if (color.get(next) === 'white') {
        const nested = visit(next);
        if (nested.tag === 'reject') return nested;
      }
    }
    stack.pop();
    color.set(node, 'black');
    return { tag: 'accept' };
  }

  for (const node of manifest.nodes.map((entry) => entry.id)) {
    if (color.get(node) === 'white') {
      const result = visit(node);
      if (result.tag === 'reject') return result;
    }
  }
  return { tag: 'accept' };
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
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    activeFinalNodeIds: [],
    remainingBlockers: [...EXPECTED_BLOCKERS],
  };
}

async function writeAndReturn0(root, outputDir, writeOutput, verdict) {
  if (writeOutput) {
    const absoluteDir = path.join(root, outputDir);
    await mkdir(absoluteDir, { recursive: true });
    await writeFile(path.join(absoluteDir, 'latest-verdict.json'), `${JSON.stringify(verdict, null, 2)}\n`, 'utf8');
  }
  return { ...verdict, outputDir: writeOutput ? outputDir : null };
}

function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function sameArray0(left, right) { return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]); }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function nonempty0(value) { return typeof value === 'string' && value.length > 0; }

function parseArgs0(argv) {
  const options = { root: process.cwd(), manifestPath: MANIFEST_PATH, outputDir: DEFAULT_OUTPUT_DIR, writeOutput: true, json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') options.root = requireValue0(argv, ++index, '--root');
    else if (arg === '--manifest') options.manifestPath = requireValue0(argv, ++index, '--manifest');
    else if (arg === '--output-dir') options.outputDir = requireValue0(argv, ++index, '--output-dir');
    else if (arg === '--help' || arg === '-h') { printHelp0(); process.exit(0); }
    else throw new Error(`unknown argument: ${arg}`);
  }
  return options;
}

function requireValue0(argv, index, flag) { if (index >= argv.length) throw new Error(`${flag} requires a value`); return argv[index]; }
function printHelp0() { console.log(`Usage: node scripts/audit-checker-cycles.mjs [options]\n\nOptions:\n  --json                Emit verdict JSON.\n  --no-write            Do not write artifacts/checker-cycles/latest-verdict.json.\n  --root <path>         Repository root. Defaults to cwd.\n  --manifest <path>     Checker authority graph manifest path relative to root.\n  --output-dir <path>   Artifact directory relative to root.\n`); }

async function main0() {
  let options;
  try { options = parseArgs0(process.argv.slice(2)); }
  catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad checker cycle audit CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }
  const verdict = await AuditCheckerCycles0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
