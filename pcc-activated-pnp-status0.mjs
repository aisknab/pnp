#!/usr/bin/env node

import process from 'node:process';
import { CheckFormalReconstructionStatus0 } from './pcc-formal-reconstruction-status0.mjs';

const CHECKER = 'CheckActivatedPNPStatus0';

export async function CheckActivatedPNPStatus0(options = {}) {
  const out = await CheckFormalReconstructionStatus0(options);
  if (out.tag !== 'accept') return { ...out, checker: CHECKER, compatibilityAlias: true, activatedPNPStatusAccepted: false, activationSuperseded: false, publicTheoremEmissionAllowed: false, finalTheoremReady: false };
  return { ...out, checker: CHECKER, claimStatus: 'legacy-activated-status-path-superseded', compatibilityAlias: true, activatedPNPStatusAccepted: false, activationSuperseded: true, publicTheoremEmissionAllowed: false, publicTheoremStatement: null, publicTheoremConclusion: null, finalTheoremReady: false, formalReleaseGatePassed: false };
}

function parseArgs0(argv) { const out = { json: false, writeOutput: true }; for (const arg of argv) { if (arg === '--json') out.json = true; else if (arg === '--no-write') out.writeOutput = false; else throw new Error(`unknown argument: ${arg}`); } return out; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { console.error(JSON.stringify({ tag: 'reject', checker: CHECKER, coord: 'ActivatedPNPStatus.CliBadArgument', witness: { reason: error.message }, publicTheoremEmissionAllowed: false }, null, 2)); process.exit(2); } const verdict = await CheckActivatedPNPStatus0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
