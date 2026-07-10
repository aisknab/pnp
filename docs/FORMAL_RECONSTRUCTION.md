# Formal reconstruction notice

**Effective: 10 July 2026**

## Current status

The target theorem is `P = NP`. It is **not currently established by this repository**.

Public theorem emission is disabled while the project is reconstructed around a concrete,
assumption-audited Lean theorem. The active machine-readable status is
[`status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json).

Use `node pcc-formal-reconstruction-status0.mjs --json` to verify the active status boundary. The
current `npm run pnp:verify` command checks that boundary, the closed active package surface, the
pinned legacy-v0 archive identity, and the small current-authority suite. It cannot be configured to
execute the historical replay; replay acceptance does not change formal-reconstruction status.

Use `node pcc-formal-public-surface0.mjs --json` to verify that superseded activation, release,
materialized, and theorem-checker routes are absent from the active package exports, scripts, and bins.

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

The repository now pins `leanprover/lean4:v4.31.0` and builds the explicit `PNP` library root. That
root imports every tracked Lean source module. `PNP.Main.rootTheoremStatus` is assumption-free data
recording that the theorem is not released; it is not the target theorem. The current conditional
bridge still depends on five disclosed project-specific axioms: `PNP.SAT`,
`PNP.LockedNANDThreshold`, `PNP.ResidualBandExactMinimization`, `PNP.GeneratePCCPack`, and
`PNP.CheckPCCPackexp`.

The first concrete foundation is now checked in `PNP.DirectWire`: intrinsically topological direct-wire
NAND programs, total Boolean evaluation, gate-count size, ordered output wiring, and elementary
projection/constant/repeated-output/NAND/NOT/AND laws. Its dedicated axiom audit is clean. This does
not by itself discharge any of the seven machine-recorded activation blockers: the concrete
complexity model, concrete SAT, locked-NAND threshold, residual-band minimizer, ZeroSlack,
polynomial bounds, and the root theorem/axiom audit remain incomplete.

The next constructive layer enumerates every well-typed direct-wire implementation at fixed input,
gate, and output widths, including the unique empty output tuple and both orders of every NAND input
pair. Its completeness theorems and certificate are axiom-free. The enumerator is intentionally not
canonical or claimed duplicate-free, and it does not decide semantic equivalence or minimum size;
enumeration was a tracked reconstruction milestone rather than a separate blocker ID, so the same
seven substantive activation blockers remain.

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

Their files and Git history remain inspectable as subordinate legacy assertion-checker evidence.
The byte-exact source, artifact, and document coordinates are recorded under
[`archive/legacy-v0/`](../archive/legacy-v0/README.md). They must not be used to infer current theorem
status.
