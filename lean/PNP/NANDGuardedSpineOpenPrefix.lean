import PNP.NANDGuardedSpineCounts
import PNP.NANDGuardedSpineMinimum

set_option autoImplicit false
set_option Elab.async false

/-! The actual open signed prefix, including its exact essential boundary.
All valuations here are independent assignments to the production boundary.
The first exported component is derived from proper records, not supplied. -/

namespace PNP.DirectWire.GuardedSpineOpenPrefix
open GuardedSpineFamily (candidate coreValue)
open EssentialInputBound TightDemandSymmetry

variable {profileWidth : Nat}

/-- Every gate up to the given physical coordinate is selected. -/
def Through (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (last : Nat) : Prop :=
  ∀ node : Fin (n + 2), node.val ≤ last → terminalGateSelected records node = true

private theorem primary_member (n k : Nat) (bound : k ≤ n)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (through : Through n records k) (index : Fin (k + 1)) :
    TerminalSupportWire.input (⟨index.val,by have h := index.isLt; omega⟩ : Fin (n + 1)) ∈
      terminalBoundaryPorts (candidate n).program records := by
  by_cases zero : index.val = 0
  · have same : (⟨index.val,by have h := index.isLt; omega⟩ : Fin (n + 1)) = 0 :=
      Fin.ext zero
    rw [same,GuardedSpineCuts.guard_boundary_iff]
    exact Or.inl (through 0 (by simp only [Fin.val_zero]; omega))
  · apply (GuardedSpineCuts.fresh_boundary_iff n records _ (Nat.pos_of_ne_zero zero)).mpr
    apply through
    have h := index.isLt
    change index.val ≤ k
    omega

/-- Position of a prefix variable in the actual canonical physical boundary. -/
def prefixPort (n k : Nat) (bound : k ≤ n)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (through : Through n records k) (index : Fin (k + 1)) :
    Fin (terminalBoundaryPorts (candidate n).program records).length :=
  ⟨(terminalBoundaryPorts (candidate n).program records).idxOf
      (.input ⟨index.val,by have h := index.isLt; omega⟩),
    List.idxOf_lt_length_of_mem (primary_member n k bound records through index)⟩

theorem prefixPort_get (n k : Nat) (bound : k ≤ n)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (through : Through n records k) (index : Fin (k + 1)) :
    (terminalBoundaryPorts (candidate n).program records).get
      (prefixPort n k bound records through index) =
        .input ⟨index.val,by have h := index.isLt; omega⟩ := by
  have found := List.findIdx_getElem
    (xs := terminalBoundaryPorts (candidate n).program records)
    (p := fun wire => wire == TerminalSupportWire.input
      (⟨index.val,by have h := index.isLt; omega⟩ : Fin (n + 1)))
    (w := List.idxOf_lt_length_of_mem (primary_member n k bound records through index))
  exact beq_iff_eq.mp found

theorem prefixPort_injective (n k : Nat) (bound : k ≤ n)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (through : Through n records k) :
    Function.Injective (prefixPort n k bound records through) := by
  intro left right same
  have wires := congrArg (fun port => (terminalBoundaryPorts (candidate n).program records).get port) same
  rw [prefixPort_get,prefixPort_get] at wires
  have indices := TerminalSupportWire.input.inj wires
  have values := congrArg (fun index : Fin (n + 1) => index.val) indices
  exact Fin.ext values

private theorem open_prefix (n k : Nat) (bound : k ≤ n)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (through : Through n records k)
    (valuation : Valuation (terminalBoundaryPorts (candidate n).program records).length) :
    terminalOpenGateEvaluation (candidate n) records valuation ⟨k,by omega⟩ =
      coreValue k (fun index => terminalOpenWireValue (candidate n) records valuation
        (.input ⟨index.val,by have h := index.isLt; omega⟩)) := by
  induction k with
  | zero =>
      rw [terminalOpenGateEvaluation_sourceEquation,through _ (by exact Nat.le_refl _),
        GuardedSpineCuts.sources]
      simp only [if_true]
      rfl
  | succ k ih =>
      have notZero : k + 1 ≠ 0 := by omega
      have notLast : k + 1 ≠ n + 1 := by omega
      rw [terminalOpenGateEvaluation_sourceEquation,through _ (by exact Nat.le_refl _),
        GuardedSpineCuts.sources]
      simp only [dif_neg notZero,dif_neg notLast,if_true]
      change boolNand
        (terminalOpenWireValue (candidate n) records valuation (.gate ⟨k,by omega⟩))
        (terminalOpenWireValue (candidate n) records valuation (.input ⟨k + 1,by omega⟩)) = _
      have predecessor :
          terminalOpenWireValue (candidate n) records valuation (.gate ⟨k,by omega⟩) =
          terminalOpenGateEvaluation (candidate n) records valuation ⟨k,by omega⟩ := by
        change (if terminalGateSelected records ⟨k,by omega⟩ then _ else _) = _
        rw [through _ (by change k ≤ k + 1; omega)]
        rfl
      rw [predecessor,ih (by omega) (fun node before => through node (by omega))]
      rfl

/-- Exact open value, with independent inputs read from their actual ports. -/
theorem prefix_value (n k : Nat) (bound : k ≤ n)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (through : Through n records k)
    (valuation : Valuation (terminalBoundaryPorts (candidate n).program records).length) :
    terminalOpenGateEvaluation (candidate n) records valuation ⟨k,by omega⟩ =
      coreValue k (fun index => valuation (prefixPort n k bound records through index)) := by
  rw [open_prefix n k bound records through valuation]
  apply congrArg (coreValue k)
  funext index
  have read := terminalOpenWireValue_boundary_get (candidate n) records valuation
    (prefixPort n k bound records through index)
  rw [prefixPort_get] at read
  exact read

private def extendPrefix (n k : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (input : Valuation (k + 1)) :
    Valuation (terminalBoundaryPorts (candidate n).program records).length :=
  fun port => match (terminalBoundaryPorts (candidate n).program records).get port with
    | .input index => if early : index.val < k + 1 then input ⟨index.val,early⟩ else false
    | .gate _ => false

private theorem extendPrefix_port (n k : Nat) (bound : k ≤ n)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (through : Through n records k) (input : Valuation (k + 1)) (index : Fin (k + 1)) :
    extendPrefix n k records input (prefixPort n k bound records through index) = input index := by
  simp only [extendPrefix,prefixPort_get,dif_pos index.isLt]

private theorem boundary_get_injective (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth)) :
    Function.Injective (fun port : Fin (terminalBoundaryPorts (candidate n).program records).length =>
      (terminalBoundaryPorts (candidate n).program records).get port) := by
  intro left right same
  apply Fin.ext
  exact (List.getElem_inj (terminalBoundaryPorts_nodup (candidate n).program records)).mp same

/-- No extra gate-boundary or later primary input is essential to this output. -/
theorem prefix_essential_iff (n k : Nat) (bound : k ≤ n)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (through : Through n records k)
    (port : Fin (terminalBoundaryPorts (candidate n).program records).length) :
    Essential (fun valuation => terminalOpenGateEvaluation (candidate n) records valuation
      ⟨k,by omega⟩) port ↔
      ∃ index : Fin (k + 1), prefixPort n k bound records through index = port := by
  constructor
  · intro essential
    by_cases found : ∃ index : Fin (k + 1), prefixPort n k bound records through index = port
    · exact found
    · exfalso
      rcases essential with ⟨left,right,agree,unequal⟩
      apply unequal
      dsimp only
      rw [prefix_value n k bound records through,prefix_value n k bound records through]
      apply congrArg (coreValue k)
      funext index
      exact agree _ (fun same => found ⟨index,same⟩)
  · rintro ⟨index,rfl⟩
    rcases GuardedSpineMinimum.value_essential k index with ⟨left,right,agree,unequal⟩
    refine ⟨extendPrefix n k records left,extendPrefix n k records right,?_,?_⟩
    · intro other different
      unfold extendPrefix
      cases found : (terminalBoundaryPorts (candidate n).program records).get other with
      | gate _ => rfl
      | input primary =>
          by_cases early : primary.val < k + 1
          · simp only [dif_pos early]
            apply agree
            intro same
            apply different
            apply boundary_get_injective n records
            dsimp only
            rw [found,prefixPort_get]
            apply congrArg TerminalSupportWire.input
            have values := congrArg (fun i : Fin (k + 1) => i.val) same
            exact Fin.ext values
          · simp only [dif_neg early]
    · dsimp only
      rw [prefix_value n k bound records through,prefix_value n k bound records through]
      have leftRead : (fun index => extendPrefix n k records left
          (prefixPort n k bound records through index)) = left := by
        funext index
        exact extendPrefix_port n k bound records through left index
      have rightRead : (fun index => extendPrefix n k records right
          (prefixPort n k bound records through index)) = right := by
        funext index
        exact extendPrefix_port n k bound records through right index
      rw [leftRead,rightRead]
      exact unequal

theorem prefix_false (n k : Nat) (bound : k ≤ n)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (through : Through n records k) :
    terminalOpenGateEvaluation (candidate n) records (fun _ => false) ⟨k,by omega⟩ = true := by
  rw [prefix_value n k bound records through]
  exact GuardedSpineMinimum.value_false k

/-- Every pair of distinct essential actual boundary inputs breaks symmetry. -/
theorem prefix_asymmetric (n k : Nat) (bound : k ≤ n)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (through : Through n records k)
    (left right : Fin (terminalBoundaryPorts (candidate n).program records).length)
    (different : left ≠ right)
    (leftEssential : Essential (fun valuation =>
      terminalOpenGateEvaluation (candidate n) records valuation ⟨k,by omega⟩) left)
    (rightEssential : Essential (fun valuation =>
      terminalOpenGateEvaluation (candidate n) records valuation ⟨k,by omega⟩) right) :
    ∃ valuation, terminalOpenGateEvaluation (candidate n) records valuation ⟨k,by omega⟩ ≠
      terminalOpenGateEvaluation (candidate n) records
        (inputSwap left right valuation) ⟨k,by omega⟩ := by
  rcases (prefix_essential_iff n k bound records through left).mp leftEssential with ⟨first,rfl⟩
  rcases (prefix_essential_iff n k bound records through right).mp rightEssential with ⟨second,rfl⟩
  have distinct : first ≠ second := fun same => different (congrArg _ same)
  rcases GuardedSpineMinimum.value_asymmetric k first second distinct with ⟨input,unequal⟩
  refine ⟨extendPrefix n k records input,?_⟩
  rw [prefix_value n k bound records through,prefix_value n k bound records through]
  have portEq (a b : Fin (k + 1)) :
      prefixPort n k bound records through a = prefixPort n k bound records through b ↔ a = b :=
    ⟨fun same => prefixPort_injective n k bound records through same,fun same => congrArg _ same⟩
  have original : (fun index => extendPrefix n k records input
      (prefixPort n k bound records through index)) = input := by
    funext index
    exact extendPrefix_port n k bound records through input index
  have swapped : (fun index => inputSwap
      (prefixPort n k bound records through first) (prefixPort n k bound records through second)
      (extendPrefix n k records input) (prefixPort n k bound records through index)) =
      inputSwap first second input := by
    funext index
    simp only [inputSwap,portEq,extendPrefix_port]
  rw [original,swapped]
  exact unequal

private theorem first_fall {width : Nat} (selected : Fin (width + 1) → Bool)
    (first : selected 0 = true) (missing : ∃ node, selected node = false) :
    ∃ last : Fin width,
      (∀ node : Fin (width + 1), node.val ≤ last.val → selected node = true) ∧
      selected last.succ = false := by
  induction width with
  | zero =>
      rcases missing with ⟨node,outside⟩
      have same : node = 0 := Fin.ext (by change node.val = 0; have h := node.isLt; omega)
      rw [same,first] at outside
      cases outside
  | succ width ih =>
      cases second : selected (0 : Fin (width + 1)).succ with
      | false =>
          refine ⟨0,?_,second⟩
          intro node before
          have same : node = 0 := Fin.ext (by change node.val = 0; change node.val ≤ 0 at before; omega)
          rw [same]
          exact first
      | true =>
          have tailMissing : ∃ node : Fin (width + 1), selected node.succ = false := by
            rcases missing with ⟨node,outside⟩
            have positive : 0 < node.val := by
              by_cases zero : node.val = 0
              · have same : node = 0 := Fin.ext zero
                rw [same,first] at outside
                cases outside
              · omega
            refine ⟨⟨node.val - 1,by have h := node.isLt; omega⟩,?_⟩
            have same : (⟨node.val - 1,by have h := node.isLt; omega⟩ : Fin (width + 1)).succ = node :=
              Fin.ext (by simp only [Fin.val_succ]; omega)
            rw [same]
            exact outside
          rcases ih (fun node => selected node.succ) second tailMissing with ⟨last,through,after⟩
          refine ⟨last.succ,?_,after⟩
          intro node before
          by_cases zero : node.val = 0
          · have same : node = 0 := Fin.ext zero
            rw [same]
            exact first
          · let earlier : Fin (width + 1) := ⟨node.val - 1,by have h := node.isLt; omega⟩
            have same : earlier.succ = node := Fin.ext (by change node.val - 1 + 1 = node.val; omega)
            rw [← same]
            apply through
            change node.val - 1 ≤ last.val
            change node.val ≤ last.val + 1 at before
            omega

/-- Proper arbitrary records determine an exported selected initial component. -/
theorem proper_prefix_export (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (first : terminalGateSelected records 0 = true)
    (proper : ∃ node, terminalGateSelected records node = false) :
    ∃ last : Fin (n + 1), Through n records last.val ∧
      last.castSucc ∈ terminalInterfacePorts (candidate n) records := by
  rcases first_fall (terminalGateSelected records) first proper with ⟨last,through,after⟩
  refine ⟨last,through,?_⟩
  apply (GuardedSpineCuts.interface_succ_iff n records last).mpr
  exact ⟨through last.castSucc (Nat.le_refl _),after⟩

/-- The real extracted output, not just the auxiliary evaluator, has this value. -/
theorem exported_value (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (last : Fin (n + 1)) (through : Through n records last.val)
    (output : Fin (terminalInterfacePorts (candidate n) records).length)
    (origin : (terminalInterfacePorts (candidate n) records).get output = last.castSucc)
    (valuation : Valuation (terminalBoundaryPorts (candidate n).program records).length) :
    (extractTerminalSupport (candidate n) records).extractedCandidate.semantics valuation output =
      coreValue last.val (fun index => valuation
        (prefixPort n last.val (by have h := last.isLt; omega) records through index)) := by
  rw [extractTerminalSupport_semantics]
  change terminalOpenGateEvaluation (candidate n) records valuation
    ((terminalInterfacePorts (candidate n) records).get output) = _
  rw [origin]
  exact prefix_value n last.val (by have h := last.isLt; omega) records through valuation

end PNP.DirectWire.GuardedSpineOpenPrefix
