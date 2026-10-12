import PNP.Concrete.NormalizerTableData

namespace PNP.Concrete.NormalizerBlocks

example (value : Nat) :
    (encodeTokenPairs (encodeUnaryTokens value)).reverse =
      false :: false :: List.replicate (2 * value) true := TableWrite.unary_reversed value
example (value : Nat) :
    (encodeTokenPairs (encodeClauseTokens [⟨true, value⟩])).reverse =
      false :: true :: false :: false ::
        (List.replicate (2 * value) true ++ [true, true, true, false]) :=
  TableWrite.replacement_bytes value
example (values : List CNFToken) (index value : Nat) (buffer : BitString) (r : Occurrence.Registers) :
    (TableWrite.tokenScan values (TableWrite.tableState index value buffer [false] r)).excess =
      (encodeTokenPairs values).reverse ++ buffer := TableWrite.tokenScan_done values index value buffer r

#print axioms TableWrite.unary_reversed
#print axioms TableWrite.replacement_bytes
#print axioms TableWrite.tokenScan_skip_data
#print axioms TableWrite.tokenScan_copy_data
#print axioms TableWrite.tokenScan_done
#print axioms TableWrite.tokenScan_select_zero
#print axioms TableWrite.tokenScan_select_succ
#print axioms TableWrite.tokenScan_finish_selected
#print axioms TableWrite.tokenScan_finish_before

end PNP.Concrete.NormalizerBlocks
