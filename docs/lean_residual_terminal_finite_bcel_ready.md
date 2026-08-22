# Checked finite SaturatePositive-to-BCEL-ready composition

`PNP.ResidualTerminalFiniteBCELReady` connects the existing finite terminal
`SaturatePositive` classifier to the existing computed BCEL anchor-nucleus
classifier. `checkTerminalFiniteBCELReady` reruns the production classifier and
accepts only the positive-projection branch whose nested BCEL result is
`ready`.

The accepted `TerminalFiniteBCELReadyCertificate` retains the safe saturation
trace, positive final full slack, positive whole-support projection defect,
computed minimum positive nucleus, and the exact classifier equality that
selected those proof objects. The named endpoint
`terminal_finite_saturate_positive_bcel_ready_checked_complete` reconstructs
that certificate from the checker equation. Its projection theorems expose the
at-least-two anchor bound, exact constant-cut equation, and complete local
full/quotient BN2 conclusion for every oriented nonempty proper cut.

The finite terminal candidate, saturation model, candidate-derived anchor
problem, and initial positive full-slack premise remain supplied. Rejecting
other local classifier branches does not map them into the complete manuscript
route system. This milestone does not derive positivity from residual slack,
construct BN3--BN6 data, derive constant activation, establish manuscript-wide
`SaturatePositive` or `BCELReady`, prove unconditional ZeroSlack or PCCMin,
bound polynomial runtime, put SAT in P, remove a project assumption, or prove
`P = NP`.

## Verification

```bash
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalFiniteBCELReadyAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalFiniteBCELReady.lean
node --test audits/lean-residual-terminal-finite-bcel-ready0.test.mjs
```

The axiom transcript covers every public declaration at this bridge. The
hostile audit rejects generic nested-branch acceptance, fail-open fallback,
caller-supplied success devices, detached results, assumptions, and widened
claims.
