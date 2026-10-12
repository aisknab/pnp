import PNP.Concrete.NormalizerOccurrenceTokens

namespace PNP.Concrete.NormalizerBlocks

example (values : List CNFToken) (r : Occurrence.Registers) :
    ∃ fuel, Exec Occurrence.loop ({r with input := encodeTokenPairs values}).store fuel
      (Occurrence.tokenScan values r).store := Occurrence.tokenScan_exec values r
example (n k e : Nat) (target sign reserved output : BitString) (rest : List CNFToken) :
    Occurrence.tokenScan (encodeUnaryTokens k ++ rest) (Occurrence.counting target n e sign reserved output) =
      Occurrence.tokenScan (.f :: rest) (Occurrence.counting target (n - k) (e + (k - n)) sign reserved output) :=
  Occurrence.tokenScan_unary k n e target sign reserved output rest
example : (Occurrence.tokenScan [.t, .t, .f, .finish]
    (Occurrence.counting [true, true] 2 0 [false] [] [false])).output = [true, false] := rfl
example : (Occurrence.tokenScan [.t, .t, .t, .f, .finish]
    (Occurrence.counting [true, true] 2 0 [false] [] [false])).output = [false] := rfl

#print axioms Occurrence.token_result_input
#print axioms Occurrence.pair_token_exec
#print axioms Occurrence.tokenScan_exec
#print axioms Occurrence.tokenScan_unary

end PNP.Concrete.NormalizerBlocks
