# Compiled Lean theorem inventory and publication gate

The current formal-publication inputs are generated from the compiled Lean environment, not by
parsing Lean source text. After `lake build PNP`, `lean-audit/PNPTheoremInventory.lean` traverses
`Lean.Environment.constants` for the public `PNP.*` declarations in the explicit `PNP` import
closure. It calls `Lean.collectAxioms` for each included declaration and emits a canonical,
lexically ordered JSON inventory.

The generated inventory is mirrored byte-for-byte at:

- [`status/LEAN_THEOREM_INVENTORY.json`](../status/LEAN_THEOREM_INVENTORY.json), the status-side
  mirror; and
- [`public/pnp-theorem-inventory.json`](../public/pnp-theorem-inventory.json), the public mirror.

The inventory records the pinned toolchain and root module, declaration kinds, each declaration's
compiled axiom closure, the source-module closure, configured detailed milestone theorem types,
excluded private compiler auxiliaries, and the compiled project-specific axiom inventory. Declaration,
theorem, assumption-free-theorem, module, and excluded-private counts are generated from the
compiled environment and are intentionally not copied into this prose. Deterministic ordering and canonical JSON encoding
make the two mirrors and their digest reproducible. This inventory is evidence about the compiled
environment; it does **not** establish `P = NP` or make an abstract theorem publication-eligible.

## Separate concrete publication gate

[`publication/FORMAL_PUBLICATION_MAP.json`](../publication/FORMAL_PUBLICATION_MAP.json) defines a
separate, fail-closed publication gate. Its compatibility declaration is
`PNP.Main.p_eq_np`, and its required concrete target is `PNP.Main.ConcretePEqualsNP`. The
report-facing `PNP.PEqualsNP` name now aliases the same concrete finite-pipeline proposition, but
that compatibility alias is not the eligible root theorem and does not activate publication.

The gate requires all of its concrete-model, declaration-kind, exact-type, compiled-kernel
fingerprint, axiom-closure, source-closure, and standard-axiom-allowlist checks to pass. In this
migration step the expected target type, target value, compatibility-root type, axiom-closure, and
source-closure fingerprints are intentionally `null`. An unset fingerprint fails its configured
subcheck; two unset values never count as a match. `PNP.Main.ConcretePEqualsNP` now exists as an
axiom-free definition for mutual inclusion in the finite charged-pipeline model, but its activation
fingerprints remain unset. The compatibility/root theorem `PNP.Main.p_eq_np` is absent. The
pipeline development now proves all-input compilation, target termination from a supplied
polynomial-time machine, ordinary output equality, external-input-size polynomial bounds, and
recursive function/decision-program `RawRefinement`. Those machine-link results still do not
provide a deterministic polynomial-time CNF-SAT decider, concrete CNF-SAT NP-hardness, a
locked-NAND decider, the residual-minimization chain, or the absent compatibility theorem.
Consequently the gate is false, and every theorem-emission field derived from it remains false or
`null`.

The direct CNF development does not change that fail-closed result. It defines one finite raw
machine that directly consumes `BitString.pair input certificate`, proves universal accept/reject
correctness and no timeout under an explicit polynomial bound, constructs a `.paired`
`PolynomialTimeVerifier CNFSAT`, and proves
`PNP.Concrete.FinalUniversalDesign.cnfSATInNP : InNP CNFSAT`. This establishes `CNFSAT ∈ NP`.
It does not establish `CNFSAT ∈ P`, NP-hardness, NP-completeness, or `P = NP`.

The locked-NAND semantic milestones follow the unbounded legacy Section 17 dependency through complete
candidate assembly, global baseline distinctness, and the unsatisfiable branch. For every finite
topologically ordered NAND circuit, `PNP.LockedNANDGlobalCandidates` constructs the exact square
`B`-gate/`B`-output baseline and `B + 4`-gate/`B + 1`-output extension, preserves every baseline
output, and proves the final coordinate is `z ∧ TraceChecks ∧ T_out`. Five further theorems prove
the baseline outputs are nonconstant, nonprojections, and pairwise semantically distinct, fixing
its exhaustive reference minimum at `B`.

`PNP.LockedNANDGlobalUnsatisfiableFinalZero` then proves that an unsatisfiable source makes the
full final coordinate false on the whole carrier and fixes the full exhaustive reference minimum
at `B`. Its two-theorem transcript uses exactly `propext` and `Quot.sound`, with no
`Classical.choice` or project axiom.

`PNP.LockedNANDGlobalSemanticThreshold` proves the remaining satisfiable final conditions by
toggling only the fresh final lock around a satisfying coherent trace. It packages all six
conditional premises for the same answer-independent candidate, proves satisfiable minimum bounds
`B + 1 ≤ minimum ≤ B + 4`, proves residual slack at most four for every source, and proves
satisfiability iff the exhaustive minimum is at least `B + 1`. Its eight-declaration transcript
uses exactly `propext` and `Quot.sound`.

`PNP.Concrete.LockedNANDEncoding` and `PNP.Concrete.LockedNANDReduction` now fix a strict
version-zero bit grammar, normalize the legacy output forms, round-trip circuits and complete
candidates, reject malformed words, and prove a pure all-bitstring transformation correct. This
semantic module remains an encoded boundary rather than an executable machine. The following
strict-v0 source-parser milestone supplies the literal validator, total exact accept/reject and
byte-preserving-or-empty output behavior, the compiled cubic non-timeout theorem, polynomial-time
machine/function witnesses, and its leaf raw-machine refinement. The following target-emitter
milestone supplies one fixed grammar-only controller, exact raw target bytes, all-input polynomial
runtime and output-size bounds, compiled non-timeout, polynomial machine/function witnesses, a
leaf raw refinement, and strict parser/emitter composition computing the established pure
reduction. The composition is packaged as
`PolynomialReduction EncodedNANDSAT EncodedLockedNANDThreshold`. A separate fixed
all-input compiler computes the exact encoded CNF-to-NAND translation in polynomial time,
retains raw refinement, packages `PolynomialReduction CNFSAT EncodedNANDSAT`, and exposes
the composed locked-NAND reduction. M186 makes the report-level `PNP.SAT` and
`PNP.LockedNANDThreshold` names exact concrete definitions and reuses that compiled composed
reduction without caller-supplied trust. A locked-NAND decider, CNFSAT-in-P theorem, remaining
NP-hardness/NP-completeness transport, and `P = NP` root remain absent.

M187 additionally makes `PNP.ResidualBandExactMinimization` the exact concrete encoded
direct-wire minimum-threshold language and replaces the supplied locked-to-residual edge with
the identity polynomial reduction. At that coordinate, two project-specific axioms remained.
M188 replaces both with transparent typed definitions over an explicit
`PCCMinLoopCertificate`; the current independent inventory is:

```text
[]
```

The current bridge declarations use only the publication gate's permitted
Lean-standard axiom allowlist. This does not construct the explicit certificate
or discharge its theorem premises. `PNP.SAT` is now definitionally the concrete
`PNP.Concrete.CNFSAT` bitstring language; this identity supplies no deterministic
decider or NP-hardness theorem by itself.

M189 adds `PNP.PCCMinTotalOracleLoop`. Its dependent outcome type contains only
proof-bearing gain, exact-minimum, and ZeroSlack branches; its transparent
recursive runner terminates by strict residual-slack descent and returns an
equivalent global minimum with a gain-iteration bound. The eight declarations
in the focused audit have empty axiom closure. The total oracle is an explicit
argument, not an inventory axiom or an executable construction, so this does
not establish unconditional ZeroSlack, the complete PCCMin algorithm, or
polynomial runtime.

M190 adds `PNP.PCCMinNormalizeOracleComposition`. Its proof-bearing normalizer
has only direct-gain and semantically equivalent non-increasing normal-form
outcomes. The composition lifts later oracle gains to strict gains from the
pre-normalized implementation, transports exact and ZeroSlack endpoints, and
reuses the M189 recursive runner. The ten declarations in the focused audit
have empty axiom closure. Both stages remain explicit arguments rather than
inventory axioms or executable constructions, so this does not establish
unconditional ZeroSlack, the complete PCCMin algorithm, or polynomial runtime.

M191 adds `PNP.PCCMinRankOrderedOracle`. It separates HResolve,
BudgetResolve, and arbitrary finite selector-rank rows, scans every canonical
rank, and makes the ZeroSlack branch consume a complete typed-blocker ledger.
`PCCMinRankOrderedOracleBuilder.toTotalOracle` connects that structure to the
M190/M189 loop, whose public endpoint retains exactness and the gain-iteration
bound. The fifteen focused declarations contain no project-specific axiom or
`Classical.choice`; executable list membership uses permitted Lean-standard
`propext` and `Quot.sound` where required. The resolver algorithms, rows,
realizer, blocker meanings, and ZeroSlack closure remain explicit supplied
boundaries, so this does not establish unconditional ZeroSlack, the complete
PCCMin algorithm, or polynomial runtime.

M192 adds `PNP.PCCMinCheckedPacketRankedSelector`. Its all-claim checker
validates data-only gain or typed-blocker claims at every canonical handle in
one supplied Packet family, and its exact-rank row constructor filters that
complete handle list by the table-owned rank. The resulting adapter supplies
M191 with checked outcomes rather than arbitrary caller rows and a
proof-bearing realizer. The fifteen focused declarations contain no
project-specific axiom or `Classical.choice`; only permitted Lean-standard
`propext` and `Quot.sound` occur where required. The family, ranks, claims,
resolver algorithms, blocker semantics, and ZeroSlack closure remain explicit
supplied boundaries, so this does not derive terminal data, establish
unconditional ZeroSlack, construct complete PCCMin, or prove polynomial
runtime.

M193 adds `PNP.PCCMinCheckedPacketHBZeroSlackBridge`. It reflects complete
checked rank-row silence into the executable selector-silence checker and
combines that result with checked HB no-outcome closure to prove every
canonical handle nonfaithful. One explicit positive-slack-to-faithful-selector
premise then yields conditional ZeroSlack and constructs M192's former closure
field. The fifteen focused declarations contain no project-specific axiom or
`Classical.choice`; only permitted Lean-standard `propext` and `Quot.sound`
occur where required. The positive-slack bridge, terminal data, resolver
algorithms, normalizer, and encoded-size polynomial construction remain
supplied or open, so unconditional ZeroSlack and complete polynomial PCCMin are
not established.

M198 adds `PNP.ResidualTerminalBN6CanonicalCutLedger` and
`PNP.PCCMinCheckedPacketBN6BCELCanonicalCutLedger`. For every finite checked
same-candidate BCEL nucleus and supplied raw positive-cell ledger, it proves
that canonical duplicate-footprint coalescing preserves the direct crossing-
mass sum on every cut. The checked PCCMin endpoint therefore exposes the
surviving proper-cut activation mismatch directly against that raw ledger. The
nine reviewed declarations contain no project-specific axiom or
`Classical.choice`; only permitted Lean-standard `propext` and `Quot.sound`
appear where required. Raw cells, payloads, terminal construction, the
constant-activation equation, gain and global rank-decrease semantics, and
encoded-size polynomial bounds remain supplied or open, so this does not
establish unconditional ZeroSlack, complete PCCMin, or polynomial runtime.

M199 adds `PNP.ResidualTerminalV53CanonicalConstantCutBasis` and
`PNP.PCCMinCheckedPacketBN6BCELCanonicalConstantCutBasis`. It proves that a
shape-specific sparse basis is equivalent to the complete V53 proper-cut
constant equation on every carrier of size at least two, implements a total
typed classifier without a carrier-powerset scan, and feeds accepted evidence
directly into the checked Packet/BN6/BCEL/HB conditional ZeroSlack boundary.
The twenty-two reviewed declarations contain no project-specific axiom or
`Classical.choice`; only permitted Lean-standard `propext` and `Quot.sound`
appear where required. Raw cells, payloads, terminal construction, gain and
global rank-decrease semantics, and complete encoded-size polynomial bounds
remain supplied or open, so this does not establish unconditional ZeroSlack,
complete PCCMin, or polynomial runtime.

## Reviewed intermediate milestone bindings

Intermediate milestone credit has a separate evidence boundary from theorem publication. Every
configured candidate must have its reviewed per-name, domain-separated compiled kernel-type
SHA-256 in the publication map, use only the fixed permitted Lean-standard axiom closure, and match
by exact declaration name and theorem kind. The milestone source-closure hash must also match. That closure
covers all modules under `lean/**/*.lean` plus `lean-toolchain`, `lakefile.lean`,
`lake-manifest.json`, and the compiled inventory probe. A same-name theorem with a weakened type,
or a change to any Lean source or pin, revokes milestone credit until the reviewed map is
deliberately updated. These non-null milestone pins are independent of the intentionally null
concrete-gate activation fingerprints.

## Deterministic publication outputs

The formal status, public status mirror, TeX report, and PDF report are generated from the checked
inventory and publication map. The root
[`canonical_proof_report.pdf`](../canonical_proof_report.pdf) is the current concise formal
reconstruction report. It is a non-activation report, not the historical claim manuscript. The
historical 56-page claim artifact is available only through the pinned legacy source coordinate;
its immutable coordinates are recorded under [`archive/legacy-v0/`](../archive/legacy-v0/README.md).

The PDF check performs two builds in the same installed environment and requires identical bytes,
then compares those bytes with the committed PDF and renders every page through Poppler. The hosted
runner's TeX and Poppler package versions are not cryptographically pinned, so this is a
same-environment determinism and fail-closed exact-byte check, not a universal cross-toolchain
reproducibility claim.

Check the committed outputs without rewriting them:

```bash
lake build PNP
node scripts/export-lean-theorem-inventory.mjs --check
node scripts/generate-formal-publication.mjs --check
node pcc-formal-reconstruction-status0.mjs --json --no-write
npm run report:check
```

Regeneration uses the corresponding commands without `--check`, followed by
`npm run report:build`. A successful inventory, status, or PDF check is not proof verification and
cannot activate theorem emission while the concrete gate remains false.
