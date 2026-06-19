import { spawnSync } from 'node:child_process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const directory = fileURLToPath(new URL('./', import.meta.url));
const scripts = [
  '01-locked-nand.mjs',
  '02-residual-slack.mjs',
  '03-mode-firewall.mjs',
  '04-no-hidden-minimization.mjs',
  '05-canonical-parser.mjs',
  '06-zero-slack.mjs',
  '07-pccpack.mjs',
  '08-release-seal.mjs',
];

for (const script of scripts) {
  process.stdout.write(`\n=== ${script} ===\n`);
  const result = spawnSync(process.execPath, [path.join(directory, script)], {
    cwd: path.resolve(directory, '../..'),
    stdio: 'inherit',
  });

  if (result.error) throw result.error;
  if (result.status !== 0) {
    process.exitCode = result.status ?? 1;
    break;
  }
}

if (!process.exitCode) {
  process.stdout.write(`\nMinimal reviewer examples passed: ${scripts.length}/${scripts.length}.\n`);
}
