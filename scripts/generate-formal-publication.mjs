#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { lstat, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import {
  ComputeLeanSourceClosureSha2560,
  DeriveFormalPublication0,
  FORMAL_PUBLICATION_MAP_PATH0,
  LEAN_INVENTORY_PATH0,
  LEAN_INVENTORY_PUBLIC_PATH0,
} from '../formal-publication0.mjs';
import { BuildFormalReconstructionBaseStatus0 } from '../pcc-formal-reconstruction-status0.mjs';

const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const SITE_PATH = 'public/pnp-status.json';
const TEMPLATE_PATH = 'publication/canonical_proof_report.template.tex';
const REPORT_TEX_PATH = 'canonical_proof_report.tex';
const STATUS_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-14-34';
const PUBLIC_SURFACE_COORDINATE = 'PUBLIC-SURFACE-BASELINE-2026-07-14-COOK-LEVIN-TABLEAU-33';
const REPORT_COORDINATE = 'PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-14-34';

const NEW_NON_CLAIMS = Object.freeze([
  'The compiled Lean theorem inventory is declaration and axiom-dependency evidence; it does not widen any theorem beyond its exact type and stated scope.',
  'PNP.PEqualsNP uses abstract string-handle witnesses rather than a concrete standard complexity model and is categorically ineligible for public theorem activation.',
  'PNP.Main.ConcretePEqualsNP now names the inactive finite charged-pipeline target, while PNP.Main.p_eq_np remains absent.',
  'All five reviewed activation fingerprints remain intentionally unset, so target presence alone cannot open the concrete publication gate.',
  'The current canonical TeX and PDF are generated non-claiming reconstruction reports; the historical 56-page direct-claim report remains historical audit material only.',
]);

const NEW_COMMANDS = Object.freeze([
  'node scripts/export-lean-theorem-inventory.mjs --check',
  'node scripts/generate-formal-publication.mjs --check',
  'node --test audits/lean-theorem-inventory0.test.mjs audits/formal-publication0.test.mjs',
  'npm run report:check',
]);

export async function BuildFormalPublication0(root) {
  const [inventoryBytes, publicInventoryBytes, mapBytes, template] = await Promise.all([
    readFile(path.join(root, LEAN_INVENTORY_PATH0)),
    readFile(path.join(root, LEAN_INVENTORY_PUBLIC_PATH0)),
    readFile(path.join(root, FORMAL_PUBLICATION_MAP_PATH0)),
    readFile(path.join(root, TEMPLATE_PATH), 'utf8'),
  ]);
  if (!inventoryBytes.equals(publicInventoryBytes)) throw new Error('Lean theorem inventory public mirror is not byte-identical');
  const inventory = JSON.parse(inventoryBytes.toString('utf8'));
  const publicationMap = JSON.parse(mapBytes.toString('utf8'));
  const baseStatus = BuildFormalReconstructionBaseStatus0();
  const sourceClosureSha256 = await ComputeLeanSourceClosureSha2560(root, inventory);
  const publication = DeriveFormalPublication0(
    inventory,
    publicationMap,
    inventoryBytes,
    sourceClosureSha256,
  );
  if (publication.gate.passed !== false) throw new Error('Release-33 publication gate must remain intentionally fail-closed');
  const mapSha256 = sha256Bytes0(mapBytes);
  const rootCandidate = inventory.compatibilityRootCandidate;
  const status = {
    ...baseStatus,
    coordinate: STATUS_COORDINATE,
    ...publication.emissionFields,
    activeFinalNodeIds: publication.gate.passed ? [publication.gate.compatibilityRootName] : [],
    remainingFormalObligations: publication.gate.passed ? [] : [...baseStatus.remainingFormalObligations],
    remainingBlockers: publication.gate.passed ? [] : [...baseStatus.remainingBlockers],
    rootLeanTheorem: publication.gate.compatibilityRootName,
    rootLeanTheoremPresent: rootCandidate !== null,
    rootLeanTheoremBuilt: rootCandidate !== null
      && publication.gate.subchecks.compatibilityRootIsTheorem
      && publication.gate.subchecks.compatibilityRootHasExactConcreteType,
    rootLeanTheoremAxiomAuditPassed: rootCandidate !== null
      && publication.gate.subchecks.compatibilityRootIsTheorem
      && publication.gate.subchecks.compatibilityRootHasExactConcreteType
      && rootCandidate.axioms.every((name) => publication.gate.allowedLeanStandardAxioms.includes(name)),
    sorryOrAdmitInRootDependencyClosure: rootCandidate === null
      ? null
      : rootCandidate.axioms.some((name) => name === 'sorryAx'),
    standardComplexityModelFormalized: publication.gate.subchecks.standardComplexityModelEligible,
    abstractPEqualsNPPublicationEligible: false,
    publicationStatusDerivedOnlyFromConcreteGate: true,
    concretePublicationGate: publication.gate,
    leanTheoremInventoryCoordinate: inventory.coordinate,
    leanTheoremInventoryPath: LEAN_INVENTORY_PATH0,
    leanTheoremInventoryPublicPath: LEAN_INVENTORY_PUBLIC_PATH0,
    leanTheoremInventorySha256: publication.inventorySha256,
    leanTheoremInventoryGeneratedFromCompiledEnvironment: true,
    leanTheoremInventoryUsesEnvironmentConstants: true,
    leanTheoremInventoryUsesCollectAxioms: true,
    leanTheoremInventoryDeclarationCount: inventory.declarationCount,
    leanTheoremInventoryExcludedPrivateDeclarationCount: inventory.excludedPrivateDeclarationCount,
    leanTheoremInventoryTheoremCount: inventory.theoremCount,
    leanTheoremInventoryAssumptionFreeTheoremCount: inventory.assumptionFreeTheoremCount,
    leanTheoremInventorySourceClosureModuleCount: inventory.sourceClosureModuleCount,
    leanSourceClosureSha256: sourceClosureSha256,
    formalPublicationMapCoordinate: publicationMap.coordinate,
    formalPublicationMapPath: FORMAL_PUBLICATION_MAP_PATH0,
    formalPublicationMapSha256: mapSha256,
    formalPublicationMilestones: publication.milestones,
    canonicalReportCoordinate: REPORT_COORDINATE,
    canonicalReportSource: REPORT_TEX_PATH,
    canonicalReportPdf: 'canonical_proof_report.pdf',
    canonicalReportDerivedFromLeanInventory: true,
    publicSurfaceBaselineCoordinate: PUBLIC_SURFACE_COORDINATE,
    projectSpecificAxiomsRemaining: inventory.projectAxioms.length !== 0,
    projectSpecificAxiomInventory: [...inventory.projectAxioms],
    verificationCommands: unique0([...baseStatus.verificationCommands, ...NEW_COMMANDS]),
    nonClaims: unique0([...baseStatus.nonClaims, ...NEW_NON_CLAIMS]),
    subordinateLegacySurfaces: baseStatus.subordinateLegacySurfaces.filter(
      (entry) => entry !== 'canonical_proof_report.tex' && entry !== 'canonical_proof_report.pdf',
    ),
  };
  const statusOutput = Buffer.from(`${JSON.stringify(status, null, 2)}\n`, 'utf8');
  const reportOutput = Buffer.from(renderReport0(template, status, inventory, publication), 'utf8');
  return { status, publication, inventory, statusOutput, reportOutput };
}

function renderReport0(template, status, inventory, publication) {
  const modules = new Map();
  for (const entry of inventory.declarations) {
    const count = modules.get(entry.module) ?? { declarations: 0, theorems: 0 };
    count.declarations += 1;
    if (entry.kind === 'theorem') count.theorems += 1;
    modules.set(entry.module, count);
  }
  const replacements = new Map([
    ['@@STATUS_COORDINATE@@', texEscape0(status.coordinate)],
    ['@@DECLARATION_COUNT@@', String(inventory.declarationCount)],
    ['@@THEOREM_COUNT@@', String(inventory.theoremCount)],
    ['@@ASSUMPTION_FREE_COUNT@@', String(inventory.assumptionFreeTheoremCount)],
    ['@@AXIOM_COUNT@@', String(inventory.axiomCount)],
    ['@@INVENTORY_SHA@@', texEscape0(publication.inventorySha256)],
    ['@@INVENTORY_COORDINATE@@', texEscape0(inventory.coordinate)],
    ['@@MILESTONE_SOURCE_SHA@@', texEscape0(status.leanSourceClosureSha256)],
    ['@@MODULE_COUNT@@', String(inventory.sourceClosureModuleCount)],
    ['@@DETAILED_MILESTONE_COUNT@@', String(inventory.milestoneCandidates.length)],
    ['@@EXCLUDED_PRIVATE_COUNT@@', String(inventory.excludedPrivateDeclarationCount)],
    ['@@GATE_ROWS@@', Object.entries(publication.gate.subchecks)
      .map(([name, value]) => `${texEscape0(name)} & ${value ? '\\statustrue' : '\\statusfalse'} \\\\`)
      .join('\n')],
    ['@@AXIOM_ITEMS@@', inventory.projectAxioms.map((name) => `\\item \\code{${texEscape0(name)}}`).join('\n')],
    ['@@MILESTONE_ROWS@@', publication.milestones.map((milestone) => [
      texEscape0(milestone.title),
      texEscape0(milestone.status),
      texEscape0(milestone.scope),
      texEscape0(milestone.nonClaim),
    ].join(' & ') + ' \\\\').join('\n')],
    ['@@MODULE_ROWS@@', [...modules.entries()].sort(([left], [right]) => left.localeCompare(right))
      .map(([name, counts]) => `${texEscape0(name)} & ${counts.declarations} & ${counts.theorems} \\\\`)
      .join('\n')],
    ['@@BLOCKER_ITEMS@@', status.remainingBlockers.map((name) => `\\item \\code{${texEscape0(name)}}`).join('\n')],
  ]);
  let output = template;
  for (const [token, value] of replacements) output = output.split(token).join(value);
  const leftovers = [...output.matchAll(/@@[A-Z0-9_]+@@/gu)].map((match) => match[0]);
  if (leftovers.length !== 0) throw new Error(`unreplaced report template tokens: ${leftovers.join(', ')}`);
  return output.endsWith('\n') ? output : `${output}\n`;
}

function texEscape0(value) {
  return String(value)
    .replaceAll('\\', '\\textbackslash{}')
    .replaceAll('&', '\\&')
    .replaceAll('%', '\\%')
    .replaceAll('$', '\\$')
    .replaceAll('#', '\\#')
    .replaceAll('_', '\\_')
    .replaceAll('{', '\\{')
    .replaceAll('}', '\\}')
    .replaceAll('~', '\\textasciitilde{}')
    .replaceAll('^', '\\textasciicircum{}');
}

function unique0(values) {
  return [...new Set(values)];
}

function sha256Bytes0(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

async function assertSafeTarget0(root, relative) {
  const absolute = path.resolve(root, relative);
  if (!absolute.startsWith(`${path.resolve(root)}${path.sep}`)) throw new Error(`${relative} escaped repository root`);
  try {
    const info = await lstat(absolute);
    if (info.isSymbolicLink()) throw new Error(`${relative} must not be a symlink`);
  } catch (error) {
    if (error.code !== 'ENOENT') throw error;
  }
  return absolute;
}

async function main0() {
  const args = process.argv.slice(2);
  const check = args.includes('--check');
  if (args.some((arg) => arg !== '--check')) throw new Error('Usage: node scripts/generate-formal-publication.mjs [--check]');
  const root = process.cwd();
  const built = await BuildFormalPublication0(root);
  const outputs = [
    [STATUS_PATH, built.statusOutput],
    [SITE_PATH, built.statusOutput],
    [REPORT_TEX_PATH, built.reportOutput],
  ];
  for (const [relative, expected] of outputs) {
    const absolute = await assertSafeTarget0(root, relative);
    if (check) {
      const actual = await readFile(absolute);
      if (!actual.equals(expected)) throw new Error(`${relative} drifted from the compiled formal publication inventory`);
    } else {
      await writeFile(absolute, expected);
    }
  }
  process.stdout.write(`${JSON.stringify({
    status: check ? 'current' : 'written',
    statusCoordinate: built.status.coordinate,
    inventorySha256: built.publication.inventorySha256,
    publicationGatePassed: built.publication.gate.passed,
    milestoneCount: built.publication.milestones.length,
  }, null, 2)}\n`);
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main0().catch((error) => {
    console.error(error.message);
    process.exitCode = 1;
  });
}
