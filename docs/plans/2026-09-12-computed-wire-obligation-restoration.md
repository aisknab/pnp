# M251: computed wire-backed projection obligations and charged restoration

## Legacy anchor and dependency edge

Use the manuscript pinned by `archive/legacy-v0/ARCHIVE.json`: section 4
touch-to-charge and unique materializer ownership, section 5's full/quotient
firewall, and section 6.1's R5 creation and full-mode R8 discharge requirements.
The structural lifecycle contract in `docs/semantic_kernel_phase9.md` is
supporting specification, not mathematical authority.

M250 preserves computational carrier wires when every required field remains
visible. Projection can forget a required wire, and a smaller projected program
does not by itself reconstruct that lost value. Build a concrete full-lift and
physical charge witness for this lost-wire case. Derive the obligations from
the actual finite projection mask, not from a supplied list of closed flags.

This is the computational lost-wire slice of R5/R8. It does not establish the
domain semantics of every finite-kernel rewrite, R6/R7 cancellation, arbitrary
obligation-dependency DAGs, or the complete manuscript carrier.

## Actual input and constructions

The inputs are an actual `WireCarrier inputs outputs fields` and a finite
Boolean keep mask `Fin fields → Bool`. No observer, truth function, correct
replacement, restoration program, charge ledger, or discharge trace is supplied.

1. Form the actual projected word: retain ordinary outputs and kept field
   wires. Any padding used for omitted coordinates is quotient-only and is
   never a proof of full-field agreement. Projection adds no physical gate.
2. Normalize that projected word with the existing concrete three-pass closure.
3. Build one hidden-field materializer from the original program and all
   forgotten field sources, with no ordinary outputs. Normalize that actual
   word. Shared source gates are charged once for the entire materializer,
   not once per record or output occurrence.
4. Append the materializer to the projected result using literal common-input
   NAND wiring. Reconstruct ordinary outputs from the prefix, kept fields from
   the prefix, and forgotten fields from the materializer suffix.
5. Enumerate exactly the forgotten coordinates and generate their R5 creation
   and full-mode R8 discharge records. Each discharge binds its coordinate and
   the actual restored source to a kernel-checked all-input equality. Records
   themselves provide no Boolean source and add no fictional gate charge.
6. Permit a gain result only if the actual combined gate count is strictly
   smaller than the original carrier implementation.

No exhaustive semantic minimization belongs in these constructors. The
materializer may be nonminimal, and restoration may cost more than the source.

## Required general targets

Use namespace `PNP.DirectWire.WireObligationRestoration`. The exact central
targets are:

```lean
theorem restored_output
    {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (restored carrier keep).implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output

theorem restored_field
    {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (valuation : Valuation inputs) (field : Fin fields) :
    (restored carrier keep).fieldValue valuation field =
      carrier.fieldValue valuation field

theorem restored_exact_gate_charge
    {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (restored carrier keep).implementation.gateCount =
      (projected carrier keep).implementation.gateCount +
      (materializer carrier keep).implementation.gateCount
```

Here `projected`, `materializer`, and `restored` are the actual constructions
above, including the specified normalization. These conclusions require no
caller-supplied full-field equality or correctness certificate.

Also prove:

- every retained field and ordinary output is preserved by the actual projected
  construction, while the materializer computes every forgotten field;
- creation and discharge records contain a coordinate exactly when its mask
  says forgotten, with no omitted, duplicated, or invented coordinate;
- every generated discharge has the actual full-value witness, and replay of
  the generated ordered lifecycle ends with no open obligation;
- record generation never substitutes a quotient equality for a full witness;
- the actual restored program has at most twice the original number of gates,
  using the existing normalization count bounds;
- any returned strict-gain result pays the complete materializer charge and
  preserves every original computational observation.

The gate bound is an output-size fact only. It is not a total encoded-size
polynomial execution or certificate-complexity theorem.

## Regressions and hostile contracts

Prepare intended source/type and claim-boundary expectations with the source.
Cover every finite dimension through the general theorems; bounded executable
fixtures are regression evidence, never theorem authority.

Fixtures must include hidden-only gate producers, all-kept and all-forgotten
masks, repeated field wires sharing one materializer, primary-input and constant
fields, zero fields, zero ordinary outputs, empty circuits, a projected saving
that must pay a nonzero restoration cost, and a case with no net gain.

Reject dropped/reordered fields, zero or duplicated charges, input-dependent
values fabricated as constants, supplied observers/restoration results/traces,
unbound discharge records, quotient-only full-use claims, finite-only or weakened
theorem types, unauthorized axiom dependencies, changed fingerprints, and any
claim of complete Package E, global closure, or polynomial PCCMin.

## Source and expectation chain

Keep inherited proof code and claims unchanged. Add one focused source module
and its regression/audit, root import, theorem-name producers, source/compiled
contracts, publication row, status fields, current core documentation and
generated artifacts under existing conventions.

Update package-script fixtures and workflow/test consumers in the same change.
Run root import-closure and source contracts before sealing inventory. Extract
and syntax-check the exact new durable workflow block, then execute that block
after the explicit root build. Derive type fingerprints, axiom closures, counts
and digests only from successful compiled evidence.

After proof source is frozen, generate inventory, publication/status and progress
mirrors, reconcile every changed field, and run the focused positive and hostile
contracts before the report and one deduplicated complete core suite.

## Release, progress and publication

Work in a separate source/toolchain-matched checkout. Reuse unchanged successful
evidence, including the seed cache, while rebuilding each changed dependency and
the explicit root. Normal PR/post-merge checks and exact-object reproduction
remain separate release boundaries. Do not repeat Lean or report builds for an
identical verified release tree.

Queue release behind the actual verified M250 merge; reanchoring must preserve
the tested tree. Remove task-created checkouts, fixtures, logs, patches and helpers
after the complete release and record any intentionally retained active paths.

Verified M250 development baseline: formal artefact coverage 226 of 228 scoped
rows; risk-weighted proof completion estimate 40%; uncertainty 20% to 40%;
global gates closed 0 of 5. These are separate measures. No fixed checkpoint is
expected to close here; do not award proof-completion credit for new local rows.

Publication decision: defer PNPLabs. A computational lost-wire restoration
component does not complete the manuscript carrier or the full obligation
calculus and does not change the coherent published M231 bottom line. Continue
meaningful verified submilestone notifications independently of website cadence.
