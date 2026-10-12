import PNP.Concrete.NativeNormalization.MeasuredParity

namespace PNP.Concrete.NativeNormalization.MeasuredWitness

open MeasuredReach MeasuredOperations NativeBasis NativeEquations

def bit {S : Selection n c} (ops : Operations S) (failed : Fin c)
    (read : Row c → Measured Bool) (e : Bool) (v : Fin n) : Measured Bool :=
  let terms := MeasuredTerms.ellTerms ops failed v
  let value := MeasuredParity.eval read terms.value
  let sign := MeasuredCandidate.sigma ops v
  ⟨Bool.xor value.value (sign.value && e),terms.cost+value.cost+sign.cost+2⟩

theorem bit_value {S : Selection n c} (ops : Operations S) (failed : Fin c)
    (read : Row c → Measured Bool) (e : Bool) (v : Fin n) :
    (bit ops failed read e v).value =
      Bool.xor (ellFrom S (pick S failed (fun r => (read r).value)) v)
        (NativeBasis.sigma S v && e) := by
  simp only [bit,MeasuredParity.eval_ell,MeasuredCandidate.sigma_value]

theorem bit_correct {S : Selection n c} (ops : Operations S) (failed : Fin c)
    (read : Row c → Measured Bool) (v : Fin n) :
    (bit ops failed read (MeasuredParity.eval read (MeasuredTerms.bTerms ops failed).value).value v).value =
      (recovered S failed (fun r => (read r).value)).x v := by
  rw [bit_value,MeasuredParity.eval_b]
  rfl

def bitBound (L O D M R : Nat) : Nat :=
  MeasuredTerms.ellBound O D M+(R+2)*2+1+(O+D+L+1)+2

theorem bit_cost {S : Selection n c} (ops : Operations S) (failed : Fin c)
    (read : Row c → Measured Bool) (e : Bool) (L O D M R : Nat)
    (bounds : Bounded ops L O D M) (hr : ∀ r, (read r).cost ≤ R) (v : Fin n) :
    (bit ops failed read e v).cost ≤ bitBound L O D M R := by
  have ht := MeasuredTerms.ellTerms_cost ops L O D M bounds failed v
  have hv := MeasuredParity.eval_cost read (MeasuredTerms.ellTerms ops failed v).value R hr
  have hs := MeasuredCandidate.sigma_cost ops L O D M bounds v
  have hlen := MeasuredTerms.ellTerms_length ops failed v
  have hlinear := Nat.mul_le_mul_left (R+2) hlen
  simp only [bit,bitBound]
  omega

/-- The shared extra coordinate is evaluated once before all original-variable bits. -/
def recover {S : Selection n c} (ops : Operations S) (failed : Fin c)
    (read : Row c → Measured Bool) : Measured (List Bool) :=
  let terms := MeasuredTerms.bTerms ops failed
  let e := MeasuredParity.eval read terms.value
  let indices := MeasuredCollections.range n
  let bits := MeasuredCollections.map (bit ops failed read e.value) indices.value
  ⟨bits.value,terms.cost+e.cost+indices.cost+bits.cost+1⟩

theorem recover_value {S : Selection n c} (ops : Operations S) (failed : Fin c)
    (read : Row c → Measured Bool) :
    (recover ops failed read).value = List.ofFn (recovered S failed (fun r => (read r).value)).x := by
  simp only [recover,MeasuredCollections.map_value,MeasuredCollections.range_value,bit_correct]
  simp [List.finRange,List.map_ofFn,Function.comp_def]

theorem recover_length {S : Selection n c} (ops : Operations S) (failed : Fin c)
    (read : Row c → Measured Bool) :
    (recover ops failed read).value.length = n := by
  rw [recover_value,List.length_ofFn]

def recoverBound (B L O D M R : Nat) : Nat :=
  MeasuredTerms.bBound L O D M+(R+2)*3+3*B*B+(bitBound L O D M R+2)*B+4

theorem recover_cost {S : Selection n c} (ops : Operations S) (failed : Fin c)
    (read : Row c → Measured Bool) (B L O D M R : Nat) (hn : n ≤ B)
    (bounds : Bounded ops L O D M) (hr : ∀ r, (read r).cost ≤ R) :
    (recover ops failed read).cost ≤ recoverBound B L O D M R := by
  have hb := MeasuredTerms.bTerms_cost ops L O D M bounds failed
  have he := MeasuredParity.eval_cost read (MeasuredTerms.bTerms ops failed).value R hr
  have hlen := MeasuredTerms.bTerms_length ops failed
  have hle := Nat.mul_le_mul_left (R+2) hlen
  have hi := MeasuredCollections.range_cost n
  have hm := MeasuredCollections.map_cost
    (bit ops failed read (MeasuredParity.eval read (MeasuredTerms.bTerms ops failed).value).value)
    (MeasuredCollections.range n).value (bitBound L O D M R)
    (bit_cost ops failed read _ L O D M R bounds hr)
  rw [MeasuredCollections.range_value,List.length_finRange] at hm
  have hnn := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hn hn)
  have hlinear := Nat.mul_le_mul_left (bitBound L O D M R+2) hn
  simp only [recover,recoverBound]
  simp only [MeasuredCollections.range_value,Nat.mul_assoc] at *
  omega

/-- A concrete finite input list replaces arbitrary-cost row-value function evaluation. -/
def fromBits {S : Selection n c} (ops : Operations S) (failed : Fin c)
    (a : PNP.Concrete.BitString) : Measured (List Bool) :=
  recover ops failed (MeasuredBits.readRow a)

theorem fromBits_value {S : Selection n c} (ops : Operations S) (failed : Fin c)
    (a : PNP.Concrete.BitString) :
    (fromBits ops failed a).value =
      List.ofFn (recovered S failed (MeasuredBits.rowValues c a)).x := by
  simp only [fromBits,recover_value,MeasuredBits.readRow_value]

theorem fromBits_length {S : Selection n c} (ops : Operations S) (failed : Fin c)
    (a : PNP.Concrete.BitString) : (fromBits ops failed a).value.length = n :=
  recover_length ops failed (MeasuredBits.readRow a)

theorem fromBits_cost {S : Selection n c} (ops : Operations S) (failed : Fin c)
    (a : PNP.Concrete.BitString) (B L O D M : Nat) (hn : n ≤ B) (hc : c ≤ B)
    (bounds : Bounded ops L O D M) :
    (fromBits ops failed a).cost ≤ recoverBound B L O D M (2*B+4) :=
  recover_cost ops failed (MeasuredBits.readRow a) B L O D M (2*B+4)
    hn bounds (fun r => MeasuredBits.readRow_cost a r B hc)


end PNP.Concrete.NativeNormalization.MeasuredWitness
