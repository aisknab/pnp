import process from 'node:process';

export const LEGACY_REPLAY_FLAG0 = '--historical-replay';

export function IsHistoricalReplay0(options) {
  return options?.historicalReplay === true;
}

export function EnforceHistoricalReplayCli0({ entrypoint, argv = process.argv } = {}) {
  const index = argv.indexOf(LEGACY_REPLAY_FLAG0, 2);
  if (index >= 0) {
    argv.splice(index, 1);
    return { tag: 'accept', historicalReplay: true };
  }

  const verdict = {
    tag: 'reject',
    kind: 'reject',
    checker: 'LegacyReplayGate0',
    coord: 'LegacyReplayGate0.ExplicitOptInRequired',
    path: [entrypoint ?? 'legacy-entrypoint'],
    witness: {
      reason: `superseded assertion-checker entrypoint requires ${LEGACY_REPLAY_FLAG0}`,
      currentStatus: 'status/FORMAL_RECONSTRUCTION_STATUS.json',
    },
    mathematicalTheoremEstablished: false,
    publicTheoremEmissionAllowed: false,
    publicTheoremStatement: null,
    publicTheoremConclusion: null,
    finalTheoremReady: false,
  };
  console.error(JSON.stringify(verdict, null, 2));
  process.exit(1);
}

export function LegacyReplayRequiredReject0(checker, blockers = []) {
  return {
    tag: 'reject',
    kind: 'reject',
    checker,
    coord: `${checker}.HistoricalReplayRequired`,
    path: ['historicalReplay'],
    witness: {
      reason: 'this superseded assertion-checker route is available only with explicit historicalReplay: true',
      currentStatus: 'status/FORMAL_RECONSTRUCTION_STATUS.json',
    },
    mathematicalTheoremEstablished: false,
    publicTheoremEmissionAllowed: false,
    publicTheoremStatement: null,
    publicTheoremConclusion: null,
    finalTheoremReady: false,
    activeFinalNodeIds: [],
    remainingBlockers: [...blockers],
  };
}
