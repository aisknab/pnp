import PNP.Concrete.NANDFrontendMarkers

namespace PNP.Concrete.NANDFrontend

example (base next failure : Nat) (token : LockedNAND.Token) :
    (markerCode base token next failure).length = 12 := markerCode_length _ _ _ _
example (suffix : BitString) :
    matchScan LockedNAND.Token.gateEnd.bits (false :: true :: true :: true :: suffix) =
      ⟨8, suffix, true⟩ := by
  exact matchScan_prefix LockedNAND.Token.gateEnd.bits suffix
example : (matchScan LockedNAND.Token.programEnd.bits []).valid = false := rfl
example : (matchScan LockedNAND.Token.programEnd.bits [true, false]).valid = false := rfl
example : (matchScan LockedNAND.Token.programEnd.bits [false]).fuel = 2 := rfl
example (token : LockedNAND.Token) (input : BitString) :
    (matchScan token.bits input).fuel ≤ 8 := by
  have h := (matchScan_bounds token.bits input).1
  have len : token.bits.length = 4 := by cases token <;> rfl
  rw [len] at h
  exact h

#print axioms expectTree_size
#print axioms expectTree_depth
#print axioms expectTree_scan
#print axioms expect_run
#print axioms matchScan_bounds
#print axioms matchScan_prefix
#print axioms matchScan_success
#print axioms markerCode_length
#print axioms marker_run
#print axioms marker_canonical

end PNP.Concrete.NANDFrontend
