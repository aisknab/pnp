import PNP.Concrete.NormalizerTableTokens

namespace PNP.Concrete.NormalizerBlocks

example (values : List CNFToken) (r : Occurrence.Registers) :
    ∃ fuel, Exec TableWrite.loop ({r with input := encodeTokenPairs values}).store fuel
      (TableWrite.tokenScan values r).store := TableWrite.tokenScan_exec values r
example (values : List CNFToken) (r : Occurrence.Registers) (inactive : r.active = []) :
    TableWrite.tokenScan values r = {r with input := encodeTokenPairs values} :=
  TableWrite.tokenScan_inactive values r inactive

#print axioms TableWrite.pair_token_exec
#print axioms TableWrite.tokenScan_exec
#print axioms TableWrite.tokenScan_inactive

end PNP.Concrete.NormalizerBlocks
