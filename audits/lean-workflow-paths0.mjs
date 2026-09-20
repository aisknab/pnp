import assert from 'node:assert/strict';

// Parse only the reviewed shared trigger layout; reject unsupported or ambiguous YAML.
export function leanTriggerPaths0(workflow) {
  assert.equal((workflow.match(/^on:$/gmu) ?? []).length, 1, 'one trigger section required');
  const section = /^on:\n[\s\S]*?(?=^permissions:\n)/mu.exec(workflow)?.[0];
  assert.ok(section, 'missing bounded trigger section');
  const match = /^on:\n  pull_request:\n    paths: &([A-Za-z_][A-Za-z0-9_]*)\n((?:      - '[^'\n]+'\n)+)  push:\n    branches:\n      - main\n    paths: \*([A-Za-z_][A-Za-z0-9_]*)\n  workflow_dispatch:\n*$/u.exec(section);
  assert.ok(match, 'unsupported or ambiguous trigger layout');
  assert.equal(match[1], match[3], 'push must resolve the pull-request path anchor');
  const paths = [...match[2].matchAll(/^      - '([^'\n]+)'$/gmu)].map((entry) => entry[1]);
  assert.equal(new Set(paths).size, paths.length, 'duplicate trigger paths');
  return { pull_request: paths, push: [...paths] };
}


export function assertLeanWorkflowPathCoverage0(workflow, sourcePath) {
  const pattern = sourcePath
    .replace(/^audits\/lean-[^/]+\.test\.mjs$/u, 'audits/lean-*.test.mjs')
    .replace(/^docs\/lean_[^/]+\.md$/u, 'docs/lean_*.md')
    .replace(/^docs\/plans\/[^/]+\.md$/u, 'docs/plans/*.md')
    .replace(/^lean\/.*$/u, 'lean/**')
    .replace(/^lean-audit\/.*$/u, 'lean-audit/**')
    .replace(/^lean-regression\/.*$/u, 'lean-regression/**');
  const resolved = leanTriggerPaths0(workflow);
  for (const event of ['pull_request', 'push']) {
    assert.equal(resolved[event].filter((entry) => entry === pattern).length, 1,
      sourcePath + ': missing or duplicated ' + event + ' trigger');
  }
}
