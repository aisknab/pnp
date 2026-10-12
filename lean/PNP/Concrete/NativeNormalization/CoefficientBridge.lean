import PNP.Concrete.NativeNormalization.SourceCheckBridge
import PNP.Concrete.NormalizerCoefficientPacket
import PNP.Concrete.NativeNormalization.MeasuredCompanion
import PNP.Concrete.NativeNormalization.NativeSystemCodec

namespace PNP.Concrete.NativeNormalization.CoefficientSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks
open NativeBasis NativeSource SourceCacheSourceBridge CandidateSourceBridge

def context {S : Selection n c} (cache : MeasuredCache.Cache S) (failed : Fin c) : Coefficient.Context :=
  ⟨literalRows cache,ownerCells cache,slotCells cache,modeCells cache,List.ofFn (sigma S),failed.val⟩

theorem mode_lookup {S : Selection n c} (cache : MeasuredCache.Cache S) (i : Fin c) :
    MatchingTable.read (modeCells cache) i.val = (S.mode i).map slotIndex := by
  unfold modeCells
  rw [cache.mode_eq,List.map_ofFn]
  unfold MatchingTable.read
  rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact i.isLt),List.getElem_ofFn]
  rfl

def decodedLiteral {S : Selection n c} (cache : MeasuredCache.Cache S) (failed i : Fin c) (s : Slot) :
    (context cache failed).Literal i.val (slotIndex s) where
  leading := match s with
    | .first => []
    | .middle => [eraseLiteral (S.literal i .first)]
    | .last => [eraseLiteral (S.literal i .first),eraseLiteral (S.literal i .middle)]
  lit := eraseLiteral (S.literal i s)
  rest := match s with
    | .first => [eraseLiteral (S.literal i .middle),eraseLiteral (S.literal i .last)]
    | .middle => [eraseLiteral (S.literal i .last)]
    | .last => []
  owner := (S.owner (S.literal i s).index).val
  position_eq := by cases s <;> rfl
  clause_eq := by cases s <;> exact literal_lookup cache i
  owner_eq := owner_lookup cache (S.literal i s).index

def sourceLiterals {S : Selection n c} (cache : MeasuredCache.Cache S) (failed i : Fin c) :
    (context cache failed).RowLiterals i.val :=
  ⟨decodedLiteral cache failed i .first,decodedLiteral cache failed i .middle,
    decodedLiteral cache failed i .last⟩
def eraseRow (r : NativeEquations.Row c) : Coefficient.Row := (r.1.val,r.2)
def eraseRows (xs : NativeCoefficients.Coefficients c) : List Coefficient.Row := xs.map eraseRow

theorem ell_source {S : Selection n c} (cache : MeasuredCache.Cache S) (failed : Fin c) (v : Fin n) :
    Coefficient.ellRows (S.owner v).val (MatchingTable.read (slotCells cache) v.val)
      (MatchingTable.read (modeCells cache) (S.owner v).val) =
      eraseRows (NativeCoefficients.ellTerms S failed v) := by
  rw [slot_lookup,mode_lookup]
  cases hs : S.slot v <;> cases hm : S.mode (S.owner v) with
  | none =>
      simp only [Coefficient.ellRows,OrdinalTest.ordinalMatches,slotIndex,NativeCoefficients.ellTerms,
        NativeCoefficients.variableRow,NativeCoefficients.auxiliaryRow,NativeBasis.row,eraseRows,hs,hm]
      all_goals rfl
  | some mode =>
      cases mode <;> simp only [Coefficient.ellRows,OrdinalTest.ordinalMatches,slotIndex,NativeCoefficients.ellTerms,
        NativeCoefficients.variableRow,NativeCoefficients.auxiliaryRow,NativeBasis.row,eraseRows,hs,hm]
      all_goals rfl

theorem decoded_ell {S : Selection n c} (cache : MeasuredCache.Cache S) (failed i : Fin c) (s : Slot) :
    (decodedLiteral cache failed i s).ell =
      eraseRows (NativeCoefficients.ellTerms S failed (S.literal i s).index) :=
  ell_source cache failed (S.literal i s).index

theorem anchor_source {S : Selection n c} (cache : MeasuredCache.Cache S) (failed : Fin c) :
    (context cache failed).anchorRows (decodedLiteral cache failed failed .first) =
      eraseRows (NativeCoefficients.bTerms S failed) := by
  change (failed.val,false)::(decodedLiteral cache failed failed .first).ell = _
  rw [decoded_ell]
  rfl

theorem literal_source {S : Selection n c} (cache : MeasuredCache.Cache S) (failed i : Fin c) (s : Slot) :
    (context cache failed).literalRows (decodedLiteral cache failed failed .first)
      (decodedLiteral cache failed i s) = eraseRows (NativeCoefficients.literalTerms S failed i s) := by
  unfold Coefficient.Context.literalRows
  change (if (List.ofFn (sigma S))[(S.literal i s).index.val]?.getD false = (S.literal i s).positive
    then (decodedLiteral cache failed i s).ell
    else (decodedLiteral cache failed i s).ell ++
      (context cache failed).anchorRows (decodedLiteral cache failed failed .first)) = _
  rw [CheckSourceBridge.assignment_get,decoded_ell,anchor_source]
  change (if sigma S (S.literal i s).index = (S.literal i s).positive then _ else _) =
    (NativeCoefficients.ellTerms S failed (S.literal i s).index ++
      NativeCoefficients.masked (Bool.xor (sigma S (S.literal i s).index) (S.literal i s).positive)
        (NativeCoefficients.bTerms S failed)).map eraseRow
  rw [List.map_append]
  cases sigma S (S.literal i s).index <;> cases (S.literal i s).positive <;>
    simp only [Bool.xor_false,Bool.xor_true,Bool.not_false,Bool.not_true,NativeCoefficients.masked,
      Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,List.map_nil,List.append_nil,eraseRows]

theorem auxiliary_source {S : Selection n c} (cache : MeasuredCache.Cache S) (failed i : Fin c) :
    (context cache failed).auxiliaryRows (decodedLiteral cache failed failed .first)
      (decodedLiteral cache failed i .middle) = eraseRows (NativeCoefficients.auxiliaryTerms S failed i) := by
  unfold Coefficient.Context.auxiliaryRows
  change (i.val,!OrdinalTest.ordinalMatches 2 (MatchingTable.read (modeCells cache) i.val))::
    (if OrdinalTest.ordinalMatches 2 (MatchingTable.read (modeCells cache) i.val)
    then (context cache failed).literalRows (decodedLiteral cache failed failed .first)
      (decodedLiteral cache failed i .middle) else []) = _
  rw [mode_lookup,literal_source]
  cases hm : S.mode i with
  | none =>
      simp only [OrdinalTest.ordinalMatches,NativeCoefficients.auxiliaryTerms,hm,eraseRows,
        NativeCoefficients.auxiliaryRow,NativeBasis.row]
      rfl
  | some mode =>
      cases mode <;> simp only [OrdinalTest.ordinalMatches,NativeCoefficients.auxiliaryTerms,
        hm,eraseRows,NativeCoefficients.auxiliaryRow,NativeBasis.row]
      all_goals rfl

theorem companion_source {S : Selection n c} (cache : MeasuredCache.Cache S)
    (failed i : Fin c) (tag : Bool) :
    (context cache failed).companionRows (decodedLiteral cache failed failed .first)
      (sourceLiterals cache failed i) tag =
      eraseRows (NativeCoefficients.companionTerms S failed (i,tag)) := by
  unfold Coefficient.Context.companionRows
  dsimp only [sourceLiterals]
  change (if tag then
    if OrdinalTest.ordinalMatches 2 (MatchingTable.read (modeCells cache) i.val)
    then (context cache failed).auxiliaryRows (decodedLiteral cache failed failed .first)
      (decodedLiteral cache failed i .middle)
    else (context cache failed).literalRows (decodedLiteral cache failed failed .first)
      (decodedLiteral cache failed i .last)
  else if OrdinalTest.ordinalMatches 1 (MatchingTable.read (modeCells cache) i.val)
    then (context cache failed).literalRows (decodedLiteral cache failed failed .first)
      (decodedLiteral cache failed i .first)
    else if OrdinalTest.ordinalMatches 2 (MatchingTable.read (modeCells cache) i.val)
      then (context cache failed).literalRows (decodedLiteral cache failed failed .first)
        (decodedLiteral cache failed i .first)
      else (context cache failed).literalRows (decodedLiteral cache failed failed .first)
        (decodedLiteral cache failed i .middle) ++
        (context cache failed).auxiliaryRows (decodedLiteral cache failed failed .first)
          (decodedLiteral cache failed i .middle)) = _
  rw [mode_lookup,auxiliary_source,literal_source,literal_source,literal_source]
  cases tag <;> cases hm : S.mode i with
  | none =>
      simp only [OrdinalTest.ordinalMatches,NativeCoefficients.companionTerms,hm,eraseRows]
      all_goals first | rfl | exact List.map_append.symm
  | some mode =>
      cases mode <;> simp only [OrdinalTest.ordinalMatches,NativeCoefficients.companionTerms,
        hm,eraseRows]
      all_goals first | rfl | exact List.map_append.symm


theorem b_emits {S : Selection n c} (cache : MeasuredCache.Cache S) (failed : Fin c)
    (r : Coefficient.State) (encoded : (context cache failed).Encoded r) :
    Coefficient.Emits r (Coefficient.bTerms.result r) (eraseRows (NativeCoefficients.bTerms S failed)) := by
  have checked := Coefficient.anchor_emits (context cache failed)
    (decodedLiteral cache failed failed .first) r encoded
  rw [anchor_source] at checked
  exact checked

theorem a_emits {S : Selection n c} (cache : MeasuredCache.Cache S) (failed i : Fin c)
    (tag : Bool) (r : Coefficient.State) (encoded : (context cache failed).Encoded r)
    (selected : r.row = List.replicate i.val true) :
    Coefficient.Emits r ((Coefficient.aTerms tag).result r)
      (eraseRows (NativeCoefficients.aTerms S failed (i,tag))) := by
  have checked := Coefficient.aTerms_emits (context cache failed)
    (decodedLiteral cache failed failed .first) i.val (sourceLiterals cache failed i) tag r encoded selected
  rw [companion_source] at checked
  exact checked

theorem image_emits {S : Selection n c} (cache : MeasuredCache.Cache S) (failed i : Fin c)
    (r : Coefficient.State) (encoded : (context cache failed).Encoded r)
    (selected : r.row = List.replicate i.val true) :
    Coefficient.Emits r (Coefficient.imageTerms.result r)
      (eraseRows (NativeCoefficients.imageTerms S failed i)) := by
  have checked := Coefficient.imageTerms_emits (context cache failed)
    (decodedLiteral cache failed failed .first) i.val (decodedLiteral cache failed i .first) r encoded selected
  exact (congrArg (fun rows : List Coefficient.Row =>
    Coefficient.Emits r (Coefficient.imageTerms.result r) ((i.val,false)::rows))
    (literal_source cache failed i .first)).mp checked

theorem row_bytes (r : NativeEquations.Row c) :
    CoefficientRow.bits r.1.val r.2 = (NativeSystemCodec.rowCodec c).encode r := by
  change List.replicate r.1.val true ++ [false,r.2] =
    (List.replicate r.1.val true ++ [false]) ++ [r.2]
  rw [List.append_assoc]
  rfl
theorem stream_bytes (rows : NativeCoefficients.Coefficients c) :
    Coefficient.stream (eraseRows rows) =
      NativeBitCodec.encodeSeq (NativeSystemCodec.rowCodec c).encode rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      change CoefficientRow.bits row.1.val row.2 ++ Coefficient.stream (eraseRows rest) =
        (NativeSystemCodec.rowCodec c).encode row ++
          NativeBitCodec.encodeSeq (NativeSystemCodec.rowCodec c).encode rest
      rw [row_bytes,ih]
theorem coefficient_bytes (rows : NativeCoefficients.Coefficients c) :
    Coefficient.encodeRows (eraseRows rows) = (NativeSystemCodec.coefficientsCodec c).encode rows := by
  unfold Coefficient.encodeRows
  have size : (eraseRows rows).length = rows.length := List.length_map eraseRow
  rw [size,stream_bytes]
  change List.replicate rows.length true ++ false::_ =
    (List.replicate rows.length true ++ [false]) ++ _
  rw [List.append_assoc]
  rfl

theorem b_packet {S : Selection n c} (cache : MeasuredCache.Cache S) (failed : Fin c)
    (r : Coefficient.State) (encoded : (context cache failed).Encoded r) :
    ((Coefficient.packet Coefficient.bTerms).result r).registers.output =
      (NativeSystemCodec.coefficientsCodec c).encode (NativeCoefficients.bTerms S failed) := by
  have emitted := b_emits cache failed (Coefficient.started r)
    (encoded.transport (Coefficient.start_data r))
  rw [Coefficient.packet_output _ r _ emitted,coefficient_bytes]
theorem a_packet {S : Selection n c} (cache : MeasuredCache.Cache S) (failed i : Fin c)
    (tag : Bool) (r : Coefficient.State) (encoded : (context cache failed).Encoded r)
    (selected : r.row = List.replicate i.val true) :
    ((Coefficient.packet (Coefficient.aTerms tag)).result r).registers.output =
      (NativeSystemCodec.coefficientsCodec c).encode (NativeCoefficients.aTerms S failed (i,tag)) := by
  have emitted := a_emits cache failed i tag (Coefficient.started r)
    (encoded.transport (Coefficient.start_data r)) selected
  rw [Coefficient.packet_output _ r _ emitted,coefficient_bytes]
theorem image_packet {S : Selection n c} (cache : MeasuredCache.Cache S) (failed i : Fin c)
    (r : Coefficient.State) (encoded : (context cache failed).Encoded r)
    (selected : r.row = List.replicate i.val true) :
    ((Coefficient.packet Coefficient.imageTerms).result r).registers.output =
      (NativeSystemCodec.coefficientsCodec c).encode (NativeCoefficients.imageTerms S failed i) := by
  have emitted := image_emits cache failed i (Coefficient.started r)
    (encoded.transport (Coefficient.start_data r)) selected
  rw [Coefficient.packet_output _ r _ emitted,coefficient_bytes]

theorem b_measured_packet {S : Selection n c} (cache : MeasuredCache.Cache S) (failed : Fin c)
    (r : Coefficient.State) (encoded : (context cache failed).Encoded r) :
    ((Coefficient.packet Coefficient.bTerms).result r).registers.output =
      (NativeSystemCodec.coefficientsCodec c).encode
        (MeasuredTerms.bTerms (MeasuredCache.operations cache) failed).value := by
  rw [MeasuredTerms.bTerms_value]
  exact b_packet cache failed r encoded
theorem a_measured_packet {S : Selection n c} (cache : MeasuredCache.Cache S) (failed i : Fin c)
    (tag : Bool) (r : Coefficient.State) (encoded : (context cache failed).Encoded r)
    (selected : r.row = List.replicate i.val true) :
    ((Coefficient.packet (Coefficient.aTerms tag)).result r).registers.output =
      (NativeSystemCodec.coefficientsCodec c).encode
        (MeasuredCompanion.aTerms (MeasuredCache.operations cache) failed (i,tag)).value := by
  rw [MeasuredCompanion.aTerms_value]
  exact a_packet cache failed i tag r encoded selected
theorem image_measured_packet {S : Selection n c} (cache : MeasuredCache.Cache S) (failed i : Fin c)
    (r : Coefficient.State) (encoded : (context cache failed).Encoded r)
    (selected : r.row = List.replicate i.val true) :
    ((Coefficient.packet Coefficient.imageTerms).result r).registers.output =
      (NativeSystemCodec.coefficientsCodec c).encode
        (MeasuredCompanion.imageTerms (MeasuredCache.operations cache) failed i).value := by
  rw [MeasuredCompanion.imageTerms_value]
  exact image_packet cache failed i r encoded selected

end PNP.Concrete.NativeNormalization.CoefficientSourceBridge
