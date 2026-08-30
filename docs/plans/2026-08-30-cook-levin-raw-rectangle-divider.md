# Cook-Levin literal raw rectangle-divider milestone

## Legacy anchor

The concrete Cook-Levin route must become one uniform polynomial-time raw
formula builder. M209 supplied a fixed all-coordinate raw header comparator,
and M210 supplied the exact semantic post-header clause/token decoder plus the
literal comparator remainder. The next load-bearing arithmetic dependency is
to perform the clause-width quotient/remainder calculation in a fixed finite
work machine rather than in host arithmetic.

## Unbounded abstraction

The M211 machine is fixed finite syntax. It ranges over every natural dividend,
every positive natural width, and every quotient/remainder outcome. Its input
is a literal unary dividend and width; its output retains a consumed-dividend
ledger, the strict remainder, the restored divisor, and a unary quotient
ledger. No dividend, width, quotient, remainder, clause coordinate, token
coordinate, or successful execution trace is supplied as proof authority.

## Exact theorem boundary

Add `PNP.Concrete.CookLevin.BuilderPostHeaderRawDivider` with:

1. one collision-free fixed work-machine table for repeated unary subtraction;
2. exact pair, complete-pass, terminal-cleanup, and all-cycle work traces;
3. exact quotient/remainder output for every dividend and positive width;
4. reconstruction and strict-remainder laws, including agreement with natural
   quotient and remainder;
5. exact compilation to the concrete three-symbol machine and a conservative
   polynomial step bound;
6. an in-range rectangle theorem turning the raw quotient and remainder into
   the same typed clause/token coordinates used by M210; and
7. a public checked endpoint covering the fixed machine, its exact output, the
   arithmetic laws, and its M210 semantic linkage.

## Downstream blockers

M211 is a standalone literal raw divider. It does not splice the divider onto
M209's terminal tape, preserve the surrounding builder workspace through that
splice, emit the selected body token, integrate emission into M208's complete
cursor, append the final encoded bit, provide builder
`FunctionProgram.RawRefinement`, or package the concrete
`PolynomialReduction`.

Concrete CNF-SAT NP-hardness and NP-completeness, deterministic `CNFSAT in P`,
the locked-NAND-to-residual-band route, the residual-band minimiser,
unconditional ZeroSlack, polynomial PCCMin, the eligible root theorem, and the
publication gate remain open.

## Conservative progress decision

This retires the standalone raw quotient/remainder arithmetic dependency but
does not close the fixed complete-builder checkpoint or any global proof gate.
The risk-weighted proof-completion estimate remains 35 percent with the 20 to
40 percent uncertainty range. Formal artefact coverage is regenerated from the
authoritative publication ledger after the new row is reconciled.

## Regression and hostile evidence

- Compile exact zero-dividend, strict-remainder, exact-multiple, multi-cycle,
  and general quotient/remainder traces.
- Exercise width one and positive widths larger than the dividend.
- Check the literal finite table, exact compiled trace, one-step-short timeout,
  arithmetic reconstruction, and M210 rectangle-coordinate agreement.
- Derive the axiom transcript from every public declaration in the module.
- Reject zero-width claims, fixed dividend or width fixtures, supplied quotient
  or trace premises, semantic-only division, a variable program table, hidden
  enumeration, or wording that calls the standalone divider a complete raw
  formula builder.

## Release gates

Run the focused Lean regression and axiom audit first, followed by the focused
hostile audit. Reconcile the root import, reviewed theorem-name interface,
compiled inventory, publication map, formal status, canonical report,
proof-progress ledger, durable workflow, and current documentation. Run one
complete capped remote verification, publish a focused draft PR, require every
normal check, merge manually, and reproduce the exact merge from a fresh clean
remote checkout. Synchronize that exact core merge into PNPLabs, perform its
full publication-surface audit without rebuilding Lean, merge and reproduce
the site commit, deploy it through the narrow deployer, and independently
verify production provenance and bytes.
