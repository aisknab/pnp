# Formal reconstruction notice

**Effective: 10 July 2026**

## Current status

The target theorem is `P = NP`. It is **not currently established by this repository**.

Public theorem emission is disabled while the project is reconstructed around a concrete,
assumption-audited Lean theorem. The active machine-readable status is
[`status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json).

Use `node pcc-formal-reconstruction-status0.mjs --json` to verify the active status boundary. The
current `npm run pnp:verify` command checks that boundary, the fail-closed public surface, syntax,
and regression suites. The old audit pipeline is excluded from its default step plan; acceptance by
any retained legacy checker test does not change the formal reconstruction status.

Use `node pcc-formal-public-surface0.mjs --json` to verify that superseded activation and final
release CLIs reject unless the caller explicitly supplies `--historical-replay`.

## Why the earlier activation was withdrawn

The legacy JavaScript stack checks the shape, linkage, digests, and declared fields of finite
records. Several central mathematical obligations are represented by assertion-bearing fields
or trust objects rather than derivations of the named propositions. Acceptance of those records
therefore does not establish the mathematical truth of the locked-NAND reduction, residual-band
minimizer, ZeroSlack theorem, or final complexity conclusion.

The current Lean development makes parts of the intended route explicit and proves several local
Boolean identities. It does not yet provide the required concrete complexity model, executable SAT
development, complete locked-NAND threshold theorem, residual-band exact minimizer, ZeroSlack
proof, or polynomial runtime and certificate-size bounds. It also does not expose a root theorem
`PNP.Main.p_eq_np` with an acceptable axiom audit.

## The only acceptable future activation gate

Public theorem emission may be reconsidered only when all of the following are mechanically true:

1. an exactly pinned Lean environment builds the explicit root target;
2. `PNP.Main.p_eq_np` exists and proves the concrete target theorem;
3. the root theorem's dependency closure contains no `sorry` or `admit` placeholders;
4. no PNP-specific axiom or trust parameter assumes any substantive part of the result;
5. SAT, P, NP, reductions, machines, correctness, and cost are concrete;
6. the SAT decider is executable and its polynomial bound is proved in the selected machine model;
7. the locked-NAND, residual-band, and ZeroSlack obligations are proved rather than asserted; and
8. public status and paper claims are generated from the checked Lean theorem inventory.

External review can provide useful independent audit evidence, but it is not a mathematical premise
and is not part of this gate.

## Historical material

The previous assertion-checker stack, sealed report, and activated coordinates remain available
for auditability. They are historical evidence about what the implemented checkers accepted. They
are not current theorem-status authority.

This notice supersedes the following coordinates as proof or publication authority:

```text
PNP-ACTIVATED-STATUS-2026-07-05-01
PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01
PNP-UNRESTRICTED-FINAL-SOUNDNESS-RELEASE-2026-07-05-01
```

Their files and Git history may still be inspected as legacy assertion-checker evidence until the
archive milestone relocates them. They must not be used to infer current theorem status.
