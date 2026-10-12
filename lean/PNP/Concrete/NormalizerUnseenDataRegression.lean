import PNP.Concrete.NormalizerUnseenData

namespace PNP.Concrete.NormalizerBlocks

example (v : CNFLiteral) (tail : List CNFLiteral) :
    SearchVertices.encodeVertices (v :: tail) = UnseenData.entry v ++ SearchVertices.encodeVertices tail :=
  UnseenData.encoded_cons v tail
example (v : CNFLiteral) (tail : BitString) :
    UnseenData.next (UnseenData.entry v ++ tail) = tail := (UnseenData.parsed_canonical v tail).2.1
example (v : CNFLiteral) (tail : BitString) :
    UnseenData.index (UnseenData.entry v ++ tail) = List.replicate v.variableIndex true :=
  (UnseenData.parsed_canonical v tail).1
example : Extraction.value [] [none] [] [⟨false, 3⟩, ⟨true, 0⟩, ⟨false, 8⟩] =
    some ((⟨true, 0⟩, none), [⟨false, 3⟩, ⟨false, 8⟩]) := by decide

#print axioms UnseenData.entry_shape
#print axioms UnseenData.encoded_cons
#print axioms UnseenData.encoded_prefix
#print axioms UnseenData.prefix_append
#print axioms UnseenData.scan_input_bound
#print axioms UnseenData.scan_output_bound
#print axioms UnseenData.scan_true_pairs_input
#print axioms UnseenData.index_bound
#print axioms UnseenData.next_shorter
#print axioms UnseenData.parsed_canonical

end PNP.Concrete.NormalizerBlocks
