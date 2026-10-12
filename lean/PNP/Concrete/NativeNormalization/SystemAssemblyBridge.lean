import PNP.Concrete.NativeNormalization.CoefficientBridge
import PNP.Concrete.NormalizerSystemAssembly
import PNP.Concrete.NativeNormalization.MeasuredAssembly

namespace PNP.Concrete.NativeNormalization.SystemRowsSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks
open NativeBasis NativeSource SourceCacheSourceBridge CandidateSourceBridge CoefficientSourceBridge

theorem bytes_map (encode : α → BitString) (xs : List α) :
    SystemRows.bytes (xs.map encode) = NativeBitCodec.encodeSeq encode xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change encode x ++ SystemRows.bytes (xs.map encode) = encode x ++ NativeBitCodec.encodeSeq encode xs
      rw [ih]
theorem packets_map (codec : NativeBitCodec.Codec α) (xs : List α) :
    SystemRows.encodePackets (xs.map codec.encode) = (NativeBitCodec.listCodec codec).encode xs := by
  unfold SystemRows.encodePackets
  rw [List.length_map,bytes_map]
  change List.replicate xs.length true ++ false::_ =
    (List.replicate xs.length true ++ [false]) ++ _
  rw [List.append_assoc]
  rfl
theorem entry_bytes {S : Selection n c} (cache : MeasuredCache.Cache S) (failed i : Fin c) (tag : Bool) :
    SystemRows.aPacket (context cache failed) (decodedLiteral cache failed failed .first)
      i.val (sourceLiterals cache failed i) tag =
      (NativeSystemCodec.entryCodec c).encode ((i,tag),NativeCoefficients.aTerms S failed (i,tag)) := by
  unfold SystemRows.aPacket
  rw [companion_source]
  change CoefficientRow.bits i.val tag ++ Coefficient.encodeRows
    (eraseRows (NativeCoefficients.aTerms S failed (i,tag))) = _
  rw [row_bytes (i,tag),coefficient_bytes]
  rfl
theorem image_bytes {S : Selection n c} (cache : MeasuredCache.Cache S) (failed i : Fin c) :
    SystemRows.imageBytes (context cache failed) (decodedLiteral cache failed failed .first)
      i.val (decodedLiteral cache failed i .first) =
      (NativeSystemCodec.coefficientsCodec c).encode (NativeCoefficients.imageTerms S failed i) := by
  unfold SystemRows.imageBytes
  have source := congrArg (fun xs : List Coefficient.Row => Coefficient.encodeRows ((i.val,false)::xs))
    (literal_source cache failed i .first)
  exact source.trans (coefficient_bytes (NativeCoefficients.imageTerms S failed i))
theorem eligible_source {S : Selection n c} (cache : MeasuredCache.Cache S) (failed i : Fin c) :
    SystemRows.eligible (context cache failed) i.val =
      decide (S.mode i = none ∧ i ≠ failed) := by
  apply Bool.eq_iff_iff.mpr
  rw [SystemRows.eligible_iff,decide_eq_true_eq]
  change MatchingTable.read (modeCells cache) i.val = none ∧ i.val ≠ failed.val ↔ _
  rw [mode_lookup]
  constructor
  · rintro ⟨mode,index⟩
    have none : S.mode i = none := by
      cases h : S.mode i with
      | none => rfl
      | some value => rw [h] at mode; cases mode
    exact ⟨none,fun same => index (congrArg Fin.val same)⟩
  · rintro ⟨mode,index⟩
    exact ⟨by rw [mode]; rfl,fun same => index (Fin.ext same)⟩

def aPackets {S : Selection n c} (_cache : MeasuredCache.Cache S) (failed : Fin c) (row : Nat) : List BitString :=
  if h : row < c then
    let i : Fin c := ⟨row,h⟩
    [(NativeSystemCodec.entryCodec c).encode ((i,false),NativeCoefficients.aTerms S failed (i,false)),
     (NativeSystemCodec.entryCodec c).encode ((i,true),NativeCoefficients.aTerms S failed (i,true))]
  else []
def ePackets {S : Selection n c} (_cache : MeasuredCache.Cache S) (failed : Fin c) (row : Nat) : List BitString :=
  if h : row < c then
    let i : Fin c := ⟨row,h⟩
    if decide (S.mode i = none ∧ i ≠ failed)
    then [(NativeSystemCodec.coefficientsCodec c).encode (NativeCoefficients.imageTerms S failed i)] else []
  else []

theorem a_step {S : Selection n c} (cache : MeasuredCache.Cache S) (failed i : Fin c)
    (r : SystemRows.State) (encoded : (context cache failed).Encoded r.core)
    (counter : r.counter = List.replicate i.val true) :
    SystemRows.Produced r (SystemRows.aResult r) (aPackets cache failed i.val) := by
  have checked := SystemRows.a_produced (context cache failed) (decodedLiteral cache failed failed .first)
    i.val (sourceLiterals cache failed i) r encoded counter
  rw [entry_bytes,entry_bytes] at checked
  simpa only [aPackets,dif_pos i.isLt] using checked
theorem e_step {S : Selection n c} (cache : MeasuredCache.Cache S) (failed i : Fin c)
    (r : SystemRows.State) (encoded : (context cache failed).Encoded r.core)
    (counter : r.counter = List.replicate i.val true) :
    SystemRows.Produced r (SystemRows.eResult r) (ePackets cache failed i.val) := by
  have checked := SystemRows.e_produced (context cache failed) (decodedLiteral cache failed failed .first)
    i.val (decodedLiteral cache failed i .first) r encoded counter
  rw [eligible_source,image_bytes] at checked
  simpa only [ePackets,dif_pos i.isLt] using checked

theorem flatMap_filter (xs : List α) (keep : α → Bool) (f : α → β) :
    xs.flatMap (fun x => if keep x then [f x] else []) = (xs.filter keep).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases h : keep x <;>
        simp only [List.flatMap_cons,List.filter_cons,h,Bool.false_eq_true,ite_false,ite_true,
          List.map_cons,List.cons_append,List.nil_append,ih]

theorem complete_a {S : Selection n c} (cache : MeasuredCache.Cache S) (failed : Fin c)
    (r : SystemRows.State) (encoded : (context cache failed).Encoded r.core)
    (rows : r.rows.length = c) :
    (SystemRows.listResult SystemRows.aIteration r).registers.output =
      (NativeBitCodec.listCodec (NativeSystemCodec.entryCodec c)).encode
        (NativeSparseSystem.assemble S failed).a := by
  have step : ∀ s index, (context cache failed).Encoded s.core →
      s.counter = List.replicate index true → index < r.rows.length →
      SystemRows.Produced s (SystemRows.aIteration.result s) (aPackets cache failed index) := by
    intro s index encoded counter within
    have inside : index < c := by rw [rows] at within; exact within
    exact a_step cache failed ⟨index,inside⟩ s encoded counter
  rw [SystemRows.list_packets_from SystemRows.aIteration (context cache failed)
    (aPackets cache failed) r encoded step,rows,SystemRows.packetsFrom_finRange]
  have point : (fun i : Fin c => aPackets cache failed (0+i.val)) =
      (fun i => [(NativeSystemCodec.entryCodec c).encode ((i,false),NativeCoefficients.aTerms S failed (i,false)),
       (NativeSystemCodec.entryCodec c).encode ((i,true),NativeCoefficients.aTerms S failed (i,true))]) := by
    funext i
    simp only [Nat.zero_add,aPackets,dif_pos i.isLt]
  rw [point,← packets_map]
  congr 1
  simp only [NativeSparseSystem.assemble,NativeSparseSystem.allRows,List.map_flatMap,
    List.map_cons,List.map_nil]

theorem complete_e {S : Selection n c} (cache : MeasuredCache.Cache S) (failed : Fin c)
    (r : SystemRows.State) (encoded : (context cache failed).Encoded r.core)
    (rows : r.rows.length = c) :
    (SystemRows.listResult SystemRows.eIteration r).registers.output =
      (NativeBitCodec.listCodec (NativeSystemCodec.coefficientsCodec c)).encode
        (NativeSparseSystem.assemble S failed).e := by
  have step : ∀ s index, (context cache failed).Encoded s.core →
      s.counter = List.replicate index true → index < r.rows.length →
      SystemRows.Produced s (SystemRows.eIteration.result s) (ePackets cache failed index) := by
    intro s index encoded counter within
    have inside : index < c := by rw [rows] at within; exact within
    exact e_step cache failed ⟨index,inside⟩ s encoded counter
  rw [SystemRows.list_packets_from SystemRows.eIteration (context cache failed)
    (ePackets cache failed) r encoded step,rows,SystemRows.packetsFrom_finRange]
  have point : (fun i : Fin c => ePackets cache failed (0+i.val)) =
      (fun i => if decide (S.mode i = none ∧ i ≠ failed)
        then [(NativeSystemCodec.coefficientsCodec c).encode (NativeCoefficients.imageTerms S failed i)] else []) := by
    funext i
    simp only [Nat.zero_add,ePackets,dif_pos i.isLt]
  rw [point,flatMap_filter,← packets_map]
  congr 1
  simp only [NativeSparseSystem.assemble,NativeSparseSystem.remaining,List.map_map,Function.comp_def]


theorem complete_system {S : Selection n c} (cache : MeasuredCache.Cache S) (failed : Fin c)
    (r : SystemAssembly.State) (encoded : (context cache failed).Encoded r.core.core)
    (rows : r.core.rows.length = c) :
    (SystemAssembly.result r).registers.output =
      (NativeSystemCodec.systemCodec c).encode (NativeSparseSystem.assemble S failed) := by
  have b : (SystemAssembly.bRoutine.result r).registers.output =
      (NativeSystemCodec.coefficientsCodec c).encode (NativeCoefficients.bTerms S failed) := by
    change (SystemRows.result (Coefficient.packet Coefficient.bTerms) r.core).registers.output = _
    rw [SystemRows.result_output]
    exact CoefficientSourceBridge.b_packet cache failed (SystemRows.input r.core)
      (SystemRows.input_encoded (context cache failed) r.core encoded)
  have aEncoded : (context cache failed).Encoded (SystemAssembly.afterB r).core.core :=
    SystemRows.encoded_transport (context cache failed) r.core (SystemAssembly.afterB r).core
      encoded (SystemAssembly.afterB_shared r)
  have aRows : (SystemAssembly.afterB r).core.rows.length = c := by
    rw [SystemAssembly.afterB_rows,rows]
  have a := complete_a cache failed (SystemAssembly.afterB r).core aEncoded aRows
  have eEncoded : (context cache failed).Encoded (SystemAssembly.afterA r).core.core :=
    SystemRows.encoded_transport (context cache failed) r.core (SystemAssembly.afterA r).core
      encoded (SystemAssembly.afterA_shared r)
  have eRows : (SystemAssembly.afterA r).core.rows.length = c := by
    rw [SystemAssembly.afterA_rows,rows]
  have e := complete_e cache failed (SystemAssembly.afterA r).core eEncoded eRows
  rw [SystemAssembly.result_output,b]
  change _ ++ ((SystemRows.listResult SystemRows.aIteration (SystemAssembly.afterB r).core).registers.output ++
    (SystemRows.listResult SystemRows.eIteration (SystemAssembly.afterA r).core).registers.output) = _
  rw [a,e]
  rfl

theorem complete_measured_system {S : Selection n c} (cache : MeasuredCache.Cache S) (failed : Fin c)
    (r : SystemAssembly.State) (encoded : (context cache failed).Encoded r.core.core)
    (rows : r.core.rows.length = c) :
    (SystemAssembly.result r).registers.output =
      (NativeSystemCodec.systemCodec c).encode (MeasuredAssembly.assemble (MeasuredCache.operations cache) failed).value := by
  rw [MeasuredAssembly.assemble_value]
  exact complete_system cache failed r encoded rows

end PNP.Concrete.NativeNormalization.SystemRowsSourceBridge
