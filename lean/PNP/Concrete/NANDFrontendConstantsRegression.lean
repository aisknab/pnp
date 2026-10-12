import PNP.Concrete.NANDFrontendConstants

namespace PNP.Concrete.NANDFrontend

example (base next : Nat) : (constantsCode base next).length = 64 := constantsCode_length _ _
example (p : BitRegister.Program 9) (base next : Nat) (r : Registers)
    (placed : Segment p base (constantsCode base next)) :
    BitRegister.run p (constantsFuel r) (r.state base) = (withConstants r).state next :=
  constants_run p base next r placed
example (n : Nat) : (constantBits n).length = 12 * n + 38 := constantBits_length n
example (n : Nat) (positive : Bool) :
    (encodeTokenPairs (encodeClauseTokens (unitClause n positive))).length = 6 * n + 16 :=
  unitBits_length n positive

#print axioms constantsCode_length
#print axioms constants_run
#print axioms unitBits_length
#print axioms constantBits_length

end PNP.Concrete.NANDFrontend
