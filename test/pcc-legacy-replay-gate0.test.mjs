import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

const GATED_ENTRYPOINTS0 = [
  'pcc-uniform-final-soundness-target0.mjs',
  'pcc-uniform-input-family0.mjs',
  'pcc-uniform-locked-nand-construction0.mjs',
  'pcc-uniform-locked-nand-threshold0.mjs',
  'pcc-uniform-residual-band-minimizer0.mjs',
  'pcc-uniform-zeroslack-closure0.mjs',
  'pcc-no-hidden-oracle-semantic0.mjs',
  'pcc-uniform-complexity-conclusion0.mjs',
  'bin/runall0.mjs',
  'bin/release-audit0.mjs',
  'bin/write-materialized-final-certificate0.mjs',
  'bin/write-final-certificate-public-status0.mjs',
  'bin/write-release-audit-final-certificate-gate0.mjs',
  'bin/write-release-audit-concrete-final-certificate-gate0.mjs',
  'bin/write-concrete-release-appendix0.mjs',
  'bin/write-concrete-final-acceptance-replay0.mjs',
  'bin/write-final-pnp-certificate0.mjs',
  'bin/write-final-pnp-release-gate0.mjs',
  'bin/write-final-pnp-proof-report0.mjs',
  'scripts/pnp-verify-and-upload.mjs',
];

for (const entrypoint of GATED_ENTRYPOINTS0) {
  test(`${entrypoint} rejects without explicit historical replay`, () => {
    const cliPath = fileURLToPath(new URL(`../${entrypoint}`, import.meta.url));
    const child = spawnSync(process.execPath, [cliPath], { encoding: 'utf8' });

    assert.equal(child.status, 1, child.stdout);
    const out = JSON.parse(child.stderr);
    assert.equal(out.tag, 'reject');
    assert.equal(out.checker, 'LegacyReplayGate0');
    assert.equal(out.coord, 'LegacyReplayGate0.ExplicitOptInRequired');
    assert.deepEqual(out.path, [entrypoint]);
    assert.equal(out.mathematicalTheoremEstablished, false);
    assert.equal(out.publicTheoremEmissionAllowed, false);
    assert.equal(out.publicTheoremStatement, null);
    assert.equal(out.finalTheoremReady, false);
  });
}
