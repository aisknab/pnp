# Finite BN4 activation-exact cancellation kernel

`PNP.ResidualTerminalBN4ActivationCancellation` consumes the canonical atom
identity space produced by a successful finite BN3 request envelope and closes
the finite same-key cancellation kernel required immediately above it.

The current BN3 construction has one exact singleton minimal consumer per
request atom. BN4 therefore uses `[[atom]]` as that request's canonical active
antichain code. Lean proves code equality if and only if the induced activation
predicates agree on every cut. The reverse proof evaluates the singleton
witness cut only; it does not enumerate all cuts.

Each finite signed cell carries one complete typed key:

- the canonical request atom;
- an explicit semantic signature; and
- an explicit transport type.

Key equality is equivalent to activation-function equality plus literal
equality of both remaining fields. The executable classifier totals positive
and negative natural-number masses only at one exact key. It returns balance,
one strictly positive residual, or one strictly negative residual. Lean proves
that the residual integer contribution is exactly the input positive mass less
negative mass, retains the complete key, and can never contain an
opposite-sign pair.

The duplicate-free canonical key universe is computed from the input ledger.
The total pipeline wrapper preserves the four existing proof-bearing BN3/BCEL
failure classes, rejects a ledger that mentions an atom outside the successful
nucleus, and constructs all cancellation proofs on the accepted branch.

## Deliberate boundary

This is a finite cancellation kernel over an explicit typed cell ledger. It
does not derive those cells, semantic signatures, or transport labels from the
four-corner bases. Consequently it is not the full historical
`BN4.ActivationExact` theorem and carries no polynomial construction or size
bound. It also does not construct BN5, PkgC, or BN6; connect local failures to a
complete decreasing global route system; prove selector/realizer completeness;
establish ZeroSlack or PCCMin; put SAT in P; remove any disclosed project
assumption; or prove `P = NP`.

## Reproduction

```bash
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalBN4ActivationCancellationAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalBN4ActivationCancellation.lean
node --test audits/lean-residual-terminal-bn4-activation-cancellation0.test.mjs
```
