import PNP.Concrete.NormalizerCutPrepared
namespace PNP.Concrete.NormalizerBlocks
example (width : Nat) (formula : List (List CNFLiteral)) :
    (CutDriver.prepared (MatchingDriver.encode width formula)).core.width = List.replicate width true :=
  (CutDriver.prepared_canonical width formula).widthRead
example (width : Nat) (formula : List (List CNFLiteral)) :
    (CutDriver.prepared (MatchingDriver.encode width formula)).core.table =
      MatchingTable.encode (MatchingLoop.fullTable width formula) :=
  (CutDriver.prepared_canonical width formula).matchingRead
example (input : BitString) :
    (CutDriver.prepared input).trace = (CutDriver.initialized input).trace :=
  (CutDriver.prepared_frame input).2.2.2
#print axioms CutDriver.prepare_exec
#print axioms CutDriver.initialized_data
#print axioms CutDriver.prepared_canonical
#print axioms CutDriver.prepared_frame
end PNP.Concrete.NormalizerBlocks
