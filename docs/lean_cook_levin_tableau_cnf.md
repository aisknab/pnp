# Finite whole-tableau Cook–Levin CNF syntax

`PNP.Concrete.CookLevinTableauCNF` constructs one concrete CNF formula from a
uniform bounded verifier-tableau problem.  The construction is
answer-independent: it inspects the fixed verifier machine, source input, and
explicit polynomial bounds, but never calls SAT or asks the caller whether the
source instance is accepted.

The layer constructs and proves scoped:

- one-hot tape-symbol, head-position, and machine-state variables for every
  finite time row;
- first-match transition implications derived from the raw machine rule list;
- preservation implications for every cell away from the active head;
- the exact input-only initial row;
- the paired initial row with one-hot certificate length and symbolic
  certificate-bit variables;
- the exact initial state and centered head position;
- the designated accepting state at the padded final time; and
- canonical CNF encoding and decoding, exact local-program satisfaction
  reflection, and exact emitted clause counting.

The complete 81-declaration kernel audit has empty axiom closure.

This milestone proves the finite formula syntax and its local-clause
reflection only.  It does not yet prove that satisfiability is equivalent to
an accepting raw verifier execution, give external input-size polynomials for
the encoded output and construction runtime, define a concrete polynomial
reduction, prove `PNP.Concrete.cnfSATNPComplete`, prove CNFSAT in P, or
establish P = NP.  The concrete publication gate remains false.
