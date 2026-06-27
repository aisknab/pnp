# Independent verifier no-shared-code policy

The independent verifier track exists to make checker agreement more meaningful than a second invocation of the same JavaScript code. An independent verifier may consume repository artifacts as data, but it must not import or execute the JavaScript checker implementation it is meant to redundantly check.

## Current policy coordinate

```text
PNP-INDEPENDENT-VERIFIERS-NO-SHARED-CODE-2026-06-27-01
```

The machine-readable policy is `independent-verifiers/NO_SHARED_CODE_POLICY.json`.

## What is allowed

Independent verifiers may read stable JSON artifacts and byte hashes as data inputs. The current Python verifier is expected to read:

```text
kernel/PNP_MINIMAL_KERNEL.json
report-bindings/REPORT_THEOREM_BINDINGS.json
```

It may check that declared files such as checker paths exist in the checkout. File-existence checks are not proof imports.

## What is forbidden

Independent verifiers must not:

- import `pcc-*.mjs`, `index.mjs`, or any JavaScript checker module as executable code;
- spawn `node`, `npm`, `deno`, `bun`, or another JavaScript runtime to obtain a verdict;
- use the JavaScript checker source as an oracle for semantics;
- use dynamic execution such as Python `eval` or `exec` to bypass the import policy.

## Audit command

```bash
npm run independent:no-shared-code
```

The audit scans the independent verifier roots, validates the policy JSON, checks source imports, rejects forbidden executable patterns, and preserves the public-review boundary:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

## Boundary

This policy is a redundancy-strengthening layer. It does not clear the remaining blockers and does not activate public theorem emission.
