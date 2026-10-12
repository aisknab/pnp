import PNP.Concrete.NormalizerOwnerTokens

namespace PNP.Concrete.NormalizerBlocks

example (values : List CNFToken) (r : Occurrence.Registers) :
    ∃ fuel, Exec TableOwner.loop ({r with input := encodeTokenPairs values}).store fuel
      (TableOwner.tokenScan values r).store := TableOwner.tokenScan_exec values r
example (values : List CNFToken) (r : Occurrence.Registers) (stopped : r.active = []) :
    TableOwner.tokenScan values r = {r with input := encodeTokenPairs values} :=
  TableOwner.tokenScan_inactive values r stopped
example (index remaining excess : Nat) (target sign reserved output : BitString) (rest : List CNFToken) :
    TableOwner.tokenScan (encodeUnaryTokens index ++ rest)
      (Occurrence.counting target remaining excess sign reserved output) =
      TableOwner.tokenScan (.f :: rest)
        (Occurrence.counting target (remaining-index) (excess+(index-remaining)) sign reserved output) :=
  TableOwner.tokenScan_unary index remaining excess target sign reserved output rest

#print axioms TableOwner.tokenScan_inactive
#print axioms TableOwner.pair_token_exec
#print axioms TableOwner.tokenScan_exec
#print axioms TableOwner.tokenScan_unary
#print axioms TableOwner.tokenScan_literal

end PNP.Concrete.NormalizerBlocks
