# Agent Instructions

These instructions apply to the whole repository.

## Remote Builder Policy

The local workstation is memory-constrained. Treat it as an edit-and-inspection
host, not as a build host.

- Run full or clean Lean builds, Lean regression/axiom audits, `npm test`, broad
  repository checks, report/PDF generation, and clean-clone reproduction on the
  configured SSH host alias `pnpbuilder`.
- Use the `pnp-builder` account's user-level `systemd-run` resource limits for
  remote jobs. Do not bypass those limits for a large verification command.
- Never silently fall back to a heavyweight local command when the remote builder
  is unavailable. Stop and report the connection problem instead.
- Local commands should be limited to source edits and lightweight inspection,
  such as `rg`, `sed`, `git diff`, `git status`, and targeted syntax checks that
  cannot consume substantial memory.
- Keep host, proxy, key, and network details in the user's SSH configuration;
  do not copy private connection data into this repository.

### SSH and remote-job preflight

- Before starting a long remote job, test the configured identity without opening
  an interactive credential prompt:

  ```bash
  ssh -o BatchMode=yes -o ConnectTimeout=10 pnpbuilder true
  ```

- For a target reached through `ProxyJump`, inspect the effective configuration
  for both the destination and jump host with `ssh -G`. A destination key being
  loaded does not establish that the jump-host key is loaded. Before asking the
  user to unlock anything, compare the configured public-key fingerprints with
  the identities already available from the user's existing agent sockets. If
  one existing socket contains both exact identities, use that socket for the
  run. Otherwise ask for the specific missing configured key, not the destination
  key generically.
- Make nested probes non-interactive at both hops. Top-level `BatchMode=yes` is
  not reliably inherited by the implicit jump process, so use an explicit
  non-interactive proxy command when necessary and disable askpass for the probe.
  A successful probe must produce no wallet dialog or passphrase prompt.
- If that probe reports a missing or locked identity, stop and ask the user to
  unlock or add the already-configured key in their own terminal. Do not create a
  KDE Wallet, generate a replacement key, rewrite SSH configuration, or repeatedly
  launch GUI askpass dialogs on the user's behalf.
- Create one named remote temporary checkout per verification run. Print its path,
  checked commit, checked tree, command exit status, and the final `systemd-run`
  resource summary. This makes truncated terminal output diagnosable without
  rerunning an expensive suite.
- Never let concurrent agents build in the same remote Lean checkout. Lake's
  mutable `.olean`/`.ilean` outputs can race, disappear, or leave an import
  observing an older declaration set even when a leaf source build was green.
  Give every concurrent proof or audit worker its own named checkout; perform
  the final dependency, root, and axiom builds serially in one clean checkout.
- If a remote runner references auxiliary scripts or fixtures, copy each one to
  its exact runtime filename and verify every referenced remote path is readable
  before launching the bounded job. Do not rely on a directory-only `scp`
  destination when the runner expects a different basename.
- Probe optional observability wrappers such as `/usr/bin/time` before putting
  them in the service command. A missing wrapper must fail during launch
  preflight, not after the clean checkout is prepared; when it is absent, retain
  the resource summary already emitted by `systemd-run --wait` instead of
  installing or assuming another package.
- A user-level `systemd-run` service may not inherit the login shell's toolchain
  path. Before the first proof phase, verify the exact `lake` and `lean` binaries
  visible inside the service environment and set the already-installed toolchain
  path explicitly when needed. Treat status 127 with `command not found` as a
  launch-environment failure, not a theorem failure.
- A fresh checkout has no `.olean` cache. A cache may be seeded from another
  checkout only after its source tree and pinned toolchain have been shown to
  match exactly. Then rebuild the modified dependency chain and root import
  incrementally before running an audit that imports the root; otherwise the
  audit can see a stale namespace even though the new leaf module compiled.
- Give long remote commands phase markers or retain their full log in the remote
  temporary directory. Return concise success markers; on failure, return the
  failing phase and a useful tail of its log.
- Size `TasksMax` for the command being run, not just for a single Lean process.
  Node's test runner may create one worker process per test file; either give
  that bounded fan-out explicit headroom or cap test concurrency deliberately.
  A cluster of worker `SIGABRT`/`ERR_TEST_FAILURE` results with low memory and
  CPU use and `TasksCurrent` at the service ceiling is an orchestration-limit
  failure, not failed test assertions. Mark that run non-evidence and rerun with
  a reviewed task limit before changing source or fixtures.
- A successful dependency-build line inside a multi-phase or append-only log is
  not the job result. Before reporting a checkpoint as green, require the
  wrapper's final success marker or recorded zero exit status, confirm the
  `systemd-run` unit has reached its terminal state, and inspect the complete
  log for output appended by later phases.

### Temporary-artifact lifecycle

Temporary means temporary. Every agent-created checkout, fixture directory, log,
archive, patch, generated helper, and orchestration script on both the local host
and `pnpbuilder` must have an explicit cleanup point.

- Record each temporary path when it is created. Prefer one task-specific parent
  directory so the cleanup scope is exact and reviewable.
- Keep temporary evidence only while a run is active or while diagnosing a current
  failure. If anything must remain across turns, tell the user its exact path and
  why it is still needed.
- After the relevant verification, merge, deployment check, or failure diagnosis
  is complete, remove every temporary artifact created for that work on both
  hosts. Do not leave old clean clones, mutation fixtures, logs, archives, or
  helper scripts for a future agent to discover.
- Before deleting, resolve and validate every target. Delete only exact named
  task paths; never use a broad `/tmp`, `/var/tmp`, home-directory, or workspace
  wildcard, and never touch system, application, or user-owned temporary entries.
- Use a cleanup trap for short-lived scripts where it will not erase evidence
  needed to diagnose a failed run. For long verification work, perform an explicit
  end-of-run cleanup after recording the checked commit, tree, exit status, and
  resource summary.
- Finish with a lightweight residual check for the task prefix on both hosts and
  report any intentional remainder. A successful task should normally leave none.

### Package-manager preflight

- Inspect `package.json` and the repository lockfiles before choosing an install
  command. Run `npm ci` only when the checkout has the required lockfile and the
  repository documentation calls for it; do not assume every sibling repository
  uses the same package-manager layout.
- Do not install dependencies merely as a ritual before a dependency-free script.
  Prefer the repository's documented verification command and treat a missing
  lockfile as a preflight finding, not as a reason to generate one.

### Fresh-checkout Lean command order

- A fresh checkout has no compiled `PNP.olean`. Run `lake build PNP` before any
  standalone `lake env lean` axiom audit or regression that imports `PNP.*`.
- If such an audit reports `unknown module prefix 'PNP'` before the root build,
  classify it as a verification-order failure, not as a theorem regression.
  Build the root first, then rerun the targeted audit and regression.

## GitHub Actions Policy

Do not create temporary self-mutating GitHub Actions workflows.

Specifically, do not add workflows that:

- commit, push, tag, or delete files from inside GitHub Actions;
- patch the branch and then try to clean up their own tooling;
- use `git commit`, `git push`, `git rm`, `gh workflow`, or write-capable repository automation;
- use `permissions: contents: write` unless the user explicitly asks for a release/publishing workflow;
- run only on one temporary step branch such as `*-step-*`;
- have names like `finalize-*`, `diagnose-*`, `check-*-step-*`, or similar temporary branch automation.

This repository already has the durable online workflow shape:

- `.github/workflows/ci.yml` is the automatic read-only PR/push verification.
- `.github/workflows/legacy-v0-replay.yml` is the manual, non-authoritative pinned replay path.

Prefer those workflows. If more CI coverage is needed, extend the durable workflow in
a small read-only way instead of adding branch-specific finalizer workflows.

## How To Apply Generated Changes

If a task needs generated or mechanical edits:

- run the generator locally or in the agent environment;
- commit only the final source/documentation changes that should be reviewed;
- do not commit temporary generators, diagnostics, or one-off workflow files;
- do not rely on GitHub Actions to transform the PR branch into its final form.

Before finishing a PR branch, make sure its diff contains only the intended files.
Temporary files under `.github/workflows/`, `tools/`, diagnostics directories, or
generated helper scripts must be removed unless the user explicitly asked to keep
them as product code.

## Cross-Repository Publication And Deployment

Every formal milestone published through both this repository and PNPLabs must
pass a full PNPLabs publication-surface audit. This is a release invariant, not
the mathematical subject or direction of the selected core milestone. Reconcile
the homepage (including its current bottom line), formal status and complete
milestone ledger, FAQ and editorial-percentage explanation, updates page, feed,
progress graphic, paper and architecture pages, README, reviewer and audit
documentation, source links, download metadata, browser-rendered status, and
negative tests. Preserve historical milestone coordinates, and keep the
editorial progress estimate distinct from the number of earned formal-publication
rows.

Use the following publication order:

1. Finish the core source, audits, regression tests, generated artefacts, and
   clean-clone verification before opening or updating the publication sync.
2. Merge the core PR first. Fetch `origin/main` and record the resulting merge
   commit and tree; never bind PNPLabs to the feature-branch tip merely because
   its file tree happens to match.
3. Synchronize PNPLabs from a clean checkout of that exact core merge commit.
   Treat theorem pins, non-claim text, counts, coordinates, sizes, and digests as
   exact generated data. Do not paraphrase or independently retype them in test
   fixtures.
4. Run PNPLabs source-bound checks with `PNP_SOURCE_DIR` pointing at that exact
   core checkout. A test that skips because the source checkout is absent is not
   cross-repository verification evidence.
5. Run targeted checks first, then the complete remote suite, then a fresh
   clean-clone reproduction. This catches cheap syntax or fixture failures before
   consuming a full verification run.
6. Merge the PNPLabs PR only after its durable read-only checks are green. Fetch
   PNPLabs `origin/main` and use the PNPLabs merge commit—not its feature tip—as
   the deployment coordinate.
7. Keep privileged production deployment user-owned unless the user explicitly
   authorizes otherwise. After the user runs the pinned one-line deployment,
   independently run the read-only production verifier from a clean checkout of
   the exact PNPLabs merge commit.

Generated counts, theorem totals, hashes, page counts, byte sizes, and coordinates
are outputs of the generators and verifiers. Do not preselect them. Regenerate
after the source has stabilized, then record the values that the tools actually
produce.

### Reconcile expected values before expensive verification

When a source or generator change predictably changes a count, page total,
coordinate, byte size, digest, or similar checked value, update the complete
expectation chain before running a broad test:

1. Identify the authoritative source or generator and derive the new value from
   it. Never change a test merely to accept an unexplained observed result.
2. Search source, documentation, tests, generated fixtures, and durable workflow
   shell blocks for the old exact value.
3. Dump a structured summary of every changed generated field and check it
   field-by-field against the focused test fixture. Do not rely only on searching
   for old values: a missed adjacent field may use a common number that also
   appears legitimately in historical material.
4. Regenerate authoritative artefacts first, then update every derived assertion
   and fixture from that output in the same change.
5. Run the smallest targeted check that exercises the changed expectation.
6. Only after that targeted check passes, run the full remote suite and
   clean-clone reproduction.

For example, if a generated inventory now contains 43 entries where the previous
release contained 42, establish that the added authoritative entry is intended,
regenerate the inventory, update the assertions that consume its generated
count, and run the focused inventory/publication check before `npm test` or a
full Lean build. This ordering avoids spending a heavyweight run on a stale
known expectation while preserving fail-closed tests.

For documentation assertions, compare semantic text after normalizing whitespace
when line wrapping is not part of the contract. Do not make a broad verification
run fail merely because an unchanged sentence was reflowed across Markdown
lines.

### Cross-repository audit preflight

- Before running `npm test` in any fresh core-repository clone, enumerate the
  annotated tag names in `archive/legacy-v0/ARCHIVE.json`, fetch those exact
  tags, and verify that their pinned tag objects, commits, and trees resolve.
  A `--single-branch` or filtered clone can omit these required historical
  refs; treat that as a clone-preflight failure rather than a product
  regression.
- Remember that a normal fresh clone records remote branches under
  `refs/remotes/origin/...`; it does not create a matching local
  `refs/heads/...` branch until one is checked out. Verify a pushed feature tip
  with its remote-tracking ref or `git ls-remote`, and reserve local-head checks
  for branches the verifier explicitly creates.
- Before a source-bound PNPLabs audit, enumerate the refs named by its
  `docs/audit_targets.json` and verify that every current and historical ref
  resolves inside `PNP_SOURCE_DIR`. A single-branch checkout may omit required
  historical tags, and a reused checkout may retain a fetch refspec for a deleted
  feature branch. Prefer a fresh checkout of the exact core merge or fetch the
  named tags explicitly before starting an expensive audit.
- When a generated boundary value changes, search durable workflow shell blocks
  as well as source, documentation, and tests for the previous exact value. Run
  the equivalent of every changed workflow assertion on `pnpbuilder` before
  pushing; changing a step label does not update an embedded assertion.
- For every added or edited YAML `run: |` shell block, extract that exact block
  into an uncommitted temporary script and run `bash -n` before an expensive
  workflow. Then execute the exact block after its prerequisites are built.
  A hand-written equivalent command does not detect quoting, parenthesis, or
  pipeline syntax defects in the durable workflow itself.
- Treat a reviewed theorem-pin set as one interface with several synchronized
  producers and consumers. Before running the expensive inventory probe, update
  the Lean-side `reviewedMilestoneTheoremNames`, the JavaScript required-name
  contract, the publication milestone, and its fingerprint-key set together;
  then run a lightweight name-set comparison. Do not discover a stale producer
  only after rebuilding the compiled inventory.
- A clean-clone result is evidence only for the commit that was checked. If any
  follow-up fix changes the PR head, including a workflow-only fix, repeat the
  exact-head clean-clone reproduction before merging.
- When a durable sequential workflow grows, compare its expected duration with
  recent successful runs and preserve meaningful timeout headroom. A job can
  finish its final substantive command successfully yet be reported as
  cancelled when cleanup crosses the exact job timeout; update the durable
  timeout before rerunning instead of changing theorem checks or treating that
  boundary race as a proof failure.
- Keep remote command quoting shallow. Avoid placing command substitutions,
  `awk` programs, or regular expressions through several nested local-shell,
  SSH, `systemd-run`, and `bash -lc` quoting layers. Prefer checked-in commands or
  separate simple remote commands; if orchestration is necessary, use an
  uncommitted temporary script in the named remote verification directory and
  confirm that the intended job actually launched before interpreting its exit.

Before switching branches, staging, or committing in either repository, inspect
`git status`. Treat pre-existing untracked files as user-owned and exclude them
from the change unless the user explicitly places them in scope. After a PR has
merged, fetch `origin/main` and start follow-up work on a new branch from that
merge; do not continue stacking unrelated work on the already-merged feature
branch.

### Verification ordering and generated expectations

- When a source change intentionally changes an exact count, coordinate, list,
  or generated boundary, update the durable expectation or generator input
  before running the targeted test. Do not spend a verification run proving
  that a known stale literal is stale.
- When adding or removing an npm script or a file named by an existing script,
  update the closed `CURRENT_PACKAGE_SCRIPTS0` fixture in
  `pcc-formal-public-surface0.mjs` in the same edit, then run
  `audits/formal-public-surface0.test.mjs` before any multi-file or full suite.
- Run the cheapest source-shape and targeted regression checks before broad
  suites. Regenerate exact outputs only after source and expectation inputs
  stabilize, then run check mode against those generated bytes.
- Remember that `git diff --check` ignores untracked files. Before generating a
  source-closure hash or any downstream sealed artefact, explicitly check every
  intended new file (or stage only the reviewed paths and run
  `git diff --cached --check`). Even a later whitespace-only source edit changes
  the source-closure digest and invalidates the inventory, publication map,
  status, TeX/PDF, and every consumer of those identities.
- A direct command such as `lake env lean path/to/Module.lean` type-checks the
  source file but does not necessarily refresh the `.olean` that a later
  `import` reads from Lake's build directory. Before an axiom transcript or
  regression imports a changed module, run `lake build Exact.Module.Name` (or
  the containing root target) and only then interpret the imported result.
- If an audit result appears inconsistent with the source that just compiled,
  compare source and build-artifact timestamps or rebuild the exact imported
  module before changing proof code.

### Lean elaboration and axiom-closure preflight

- If a small leaf theorem suddenly consumes gigabytes or remains in
  `mem_cgroup_handle_over_high`, do not wait indefinitely or raise the configured
  limits. Mark that run non-evidence, then compile bounded import-only,
  definition-only, and declaration-prefix slices to distinguish import pressure
  from one elaboration hotspot. After the source fix, rebuild the permanent Lake
  target and use that terminal run as evidence.
- A clean root build can also stall because Lake launches several independently
  ready high-RSS modules together. If the retained log has no completed action
  for an extended interval, several Lean processes collectively exceed
  `MemoryHigh`, and `memory.events` shows sustained `high` growth without an OOM,
  classify that orchestration attempt as non-evidence. Stop only its exact named
  unit, prebuild the identified contending modules one at a time in the same
  checkout, then resume the root build so the valid completed cache is retained.
  Do not guess a jobs flag: pinned Lake 5 does not accept `lake build -j`; inspect
  the pinned help before changing invocation syntax. The resumed root build must
  still reach its own final green marker and terminal zero status.
- Avoid `change` when it would delta-reduce a machine-valued
  `PolynomialReduction`, `PolynomialTimeFunction`, or `FunctionProgram`
  composition. Prove a small private projection equality with `rfl`, rewrite by
  it, and use the public projection theorem such as
  `PolynomialTimeFunction.compose_output` or
  `FunctionProgram.RawRefinement.compose`. This preserves the kernel statement
  without normalizing the complete machine graph.
- Treat the simplifier as part of the axiom boundary. In an impossible list
  branch, a broad `simp` over a length equality can select convenience lemmas
  such as `Nat.right_eq_add`, whose implementation may introduce
  `Classical.propDecidable` and `Classical.choice`. Prefer
  `simp only [List.length_nil, List.length_cons]` followed by constructive
  arithmetic, then run a focused `#print axioms` or dependency-path probe before
  launching the complete generated audit.

### Mathematical milestone selection

- Ground each new mathematical milestone in a named theorem, lemma, or blocker
  from the pinned legacy report, and state exactly which dependency edge it
  closes.
- Prefer one theorem over an arbitrary finite family to a sequence of
  hard-coded instance coordinates. A proposed next step must have a finite path
  to a named global obligation; if the same shape can be repeated indefinitely
  without closing that obligation, it is a regression fixture rather than an
  earned roadmap milestone.
- Keep fixed small circuits, token positions, and schedule prefixes as
  regression tests for general definitions. Do not use another fixed-slot
  extension as theorem-progress credit when the legacy argument requires an
  all-input, all-gate, or all-formula construction.
- Before implementation, record the legacy anchor, the unbounded abstraction,
  the exact theorem type, and the remaining downstream blockers. A failed
  general proof stops the milestone; it must not be replaced by another finite
  prefix or by an added assumption.

### Legacy-theory reconstruction priority

- Treat the canonical manuscript pinned by
  `archive/legacy-v0/ARCHIVE.json`, especially the document tag
  `final-pnp-proof-report-docs-hardened-7072f8d-sealed`, as the project's
  intended correct mathematical route, construction specification, and default
  dependency order for the Lean reconstruction.
- Reconstruct its definitions, carrier conventions, objects, and theorem
  dependencies faithfully. Do not silently replace the manuscript route merely
  because a different statement or construction is easier to formalize.
- The manuscript and its historical checker remain specification and provenance
  evidence, not Lean theorem authority. Only the kernel-checked Lean statements
  establish the reconstructed results.
- An innovative alternative is allowed when Lean gives a concrete counterexample,
  proves a conflicting statement, exposes an ill-typed or inconsistent
  definition, or demonstrates that a stated step is false under its stated
  premises. Difficulty finding a proof is not by itself such evidence.
- Before departing from the manuscript, record the exact section or theorem,
  the minimal formal failure, whether the issue is a transcription error,
  missing premise, or mathematical contradiction, the replacement construction,
  and every new proof obligation. Preserve the intended external theorem
  interface where it remains coherent, and rerun the complete axiom and
  publication audits. Never bridge a discrepancy with a project axiom, `sorry`,
  `admit`, a weakened theorem, or a caller-supplied correctness certificate.

## Workflow Version And Permission Rules

When editing workflows:

- use current action majors already used by this repo, such as `actions/checkout@v7`
  and `actions/setup-node@v6`;
- keep default permissions read-only with `permissions: contents: read`;
- do not use artifact upload for normal CI unless the artifact is genuinely needed
  for a manual/debug workflow;
- never make an artifact/debug directory part of a changed-path gate.

## Verification Expectations

For ordinary PRs, the online CI should stay lightweight. Prefer:

- `npm run check`
- `npm test`
- `npm run pnp:verify -- --no-write`
- `npm run legacy:v0:check`
- the current public-surface tests used by `.github/workflows/ci.yml`

Current `npm test` is deliberately small. The expensive historical 1,121-test validation is available
only through the manual `legacy-v0-replay` workflow with its `full` input. That replay is historical
predicate evidence, not current theorem authority.

## Comment-Only Or Documentation-Like Source Changes

For comment-only source changes, prove that the JavaScript diff is comment-only
before pushing:

- compare against `origin/main`;
- reject deletions in the touched source files;
- allow only blank lines or lines beginning with `/**`, `*`, `*/`, or `//`;
- run syntax checks for every touched module.

Do this locally. Do not create a `finalize-*` workflow to apply comments, validate
them, commit them, and remove itself.

## If A Temporary Workflow Already Exists

If a branch already contains temporary workflows or tooling from another agent:

- do not try to repair the self-mutating workflow unless the user explicitly asks;
- apply the intended final source changes directly;
- remove the temporary workflow/tooling files from the branch;
- push the cleaned branch and rely on the durable `ci / current-authority` check;
- if the workflow was registered in GitHub Actions, disable it after it is no longer
  needed.
