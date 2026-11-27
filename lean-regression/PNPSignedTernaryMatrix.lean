import PNP.SignedTernary.Encoding

namespace PNP.SignedTernary.Regression

open PNP.Concrete PNP.SignedTernary.Field PNP.SignedTernary.Linear
open PNP.SignedTernary.Codec PNP.SignedTernary.Encoding

private def cell (a : F3) : Rows 1 1 := ((a, ()), ())

-- These are literal target words, not generated instances. The valid single-cell
-- identity has a common signed vector. Its zero counterpart has none.
example : MatrixSAT [true, false, false, true] := by
  refine ⟨⟨1, cell .o⟩, rfl, ⟨(.o, ()), ?_, ?_⟩⟩
  all_goals exact ⟨by decide, True.intro⟩

example : ¬ MatrixSAT [true, false, false, false] := by
  rintro ⟨A, h, hw⟩
  change some (⟨1, cell .z⟩ : Square) = some A at h
  cases h
  obtain ⟨x, _, hy⟩ := hw
  exact hy.1 rfl

-- Each row can be made nonzero on its own, but the two rows require
-- opposite relationships between the SAME signed input coordinates.
private def opposed : Rows 2 2 :=
  ((.o, (.o, ())), ((.o, (.t, ())), ()))

example : ¬ MatrixSAT (pack 2 opposed) := by
  rintro ⟨A, h, hw⟩
  rw [unpack_pack 1 opposed] at h
  cases h
  obtain ⟨⟨a, b, u⟩, hw⟩ := hw
  cases u
  cases a <;> cases b <;>
    first | exact hw.1.1 rfl | exact hw.1.2.1 rfl | exact hw.2.1 rfl | exact hw.2.2.1 rfl

-- Zero width, illegal trit 11, truncation, and an otherwise valid word
-- with one trailing bit must all be rejected before asking for a witness.
example : unpack [false] = none := rfl
example : unpack [true,false,true,true] = none := rfl
example : unpack [true,false,true] = none := rfl
example : unpack [true,false,false,true,false] = none := rfl

example : ¬ MatrixSAT (encodeCNFMatrix []) := malformed_source_has_no_solution
example : MatrixSAT (encodeCNFMatrix (encodeCNF ⟨0, []⟩)) := empty_conjunction_has_solution

-- These are valid source encodings with negative answers, not parse failures.
private theorem noCanonicalSolution (f : CNFFormula) (h : ¬ f.Satisfiable) :
    ¬ MatrixSAT (encodeCNFMatrix (encodeCNF f)) := by
  intro positive
  obtain ⟨parsed, hd, witness⟩ := (matrixSAT_encodeCNFMatrix_iff _).mp positive
  rw [decodeEncodedCNF_canonical] at hd
  cases hd
  exact h witness

example : ¬ MatrixSAT (encodeCNFMatrix (encodeCNF ⟨0, [[]]⟩)) :=
  noCanonicalSolution _ (by
    rintro ⟨_, _, clauses⟩
    exact clauses.1)

example (polarity : Bool) (index : Nat) :
    ¬ MatrixSAT (encodeCNFMatrix (encodeCNF ⟨0, [[⟨polarity, index⟩]]⟩)) :=
  noCanonicalSolution _ (by
    rintro ⟨word, width, clauses⟩
    cases word with
    | nil =>
      obtain h | h := clauses.1
      · change (none : Option Bool) = some polarity at h
        cases h
      · exact h
    | cons b bs => cases width)

-- A genuinely open-ended size claim: not a fixture-specific length.
example (raw : BitString) :
    (encodeCNFMatrix raw).length =
      dimension raw + 1 + 2 * (dimension raw * dimension raw) := canonical_length raw

end PNP.SignedTernary.Regression
