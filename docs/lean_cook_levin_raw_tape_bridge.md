# Concrete Cook–Levin raw-tape bridge

`lean/PNP/Concrete/CookLevinRawTapeBridge.lean` connects the intrinsic finite
rows encoded by the Cook–Levin CNF to the repository's ordinary focused
single-tape machine.

The bridge gives `Tape` an absolute observation function. Its left zipper
list is read nearest-head first, its right list is read in ordinary order, and
missing cells on either side are blank. The proved write and movement laws
cover both explicitly materialized blanks and implicit exterior blanks.

For a finite row and raw configuration, `FiniteRow.Represents` requires the
same control-state number and equality of every cell in the fixed finite
window. `FiniteRow.next_represents_advance` then proves that the literal
finite-row successor represents the totalized raw `step?` successor. This
uses the same designated-halt test, first matching rule, missing-rule stutter,
write, and head movement as the raw interpreter.

The head starts at the centered coordinate `uniformFuel`. After `n` finite
steps, `finiteRun_head_bounds` proves that it is at most `n` cells from that
coordinate. Consequently, every step with `n < uniformFuel` has a positive
left coordinate and a right successor strictly inside the allocated tape
width. A genuine raw move therefore never encounters the finite model's
clamping branch.

Both verifier input modes have exact initial-tape proofs. For paired mode,
`certificateOf` reconstructs an ordinary bitstring from the selected unary
length and fixed-width certificate-bit coordinates;
`certificateOf_certificate` proves the reverse embedding for every bounded
ordinary certificate.

The endpoint theorems are:

- `PNP.Concrete.CookLevin.VerifierTableauProblem.hasFiniteAccepting_iff_language`
- `PNP.Concrete.CookLevin.VerifierTableauProblem.formula_satisfiable_iff_language`
- `PNP.Concrete.CookLevin.VerifierTableauProblem.encodedFormula_mem_CNFSAT_iff_language`

Thus the generated formula is semantically equivalent to the concrete raw
verifier execution for each verifier and source input.

This milestone does not yet prove polynomial bounds for the external encoded
formula size or the formula-construction runtime, does not package the
builder as a concrete `PolynomialReduction`, and does not establish CNFSAT
NP-completeness, CNFSAT in P, or P = NP. The publication gate remains false.
