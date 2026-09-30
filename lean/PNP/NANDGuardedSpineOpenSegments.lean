import PNP.NANDGuardedSpineOpenPrefix
import PNP.NANDReadOnceTerm

set_option autoImplicit false
set_option Elab.async false

/-! Actual open components after an omitted gate. Their independent variables
are the incoming cut wire, subsequent fresh primaries and, when present, the
final guard. Read-once syntax is proved from those physical identities. -/

namespace PNP.DirectWire.GuardedSpineOpenSegments
open GuardedSpineFamily (candidate)
open EssentialInputBound
open NormalizationTerm (Term value)
open DemandForest (extendInput)
open GuardedSpineOpenPrefix (Through)

variable {profileWidth : Nat}

/-- A cut coordinate is omitted and the following physical interval is selected. -/
def CutSpan (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (start length : Nat) : Prop :=
  (∀ node : Fin (n + 2), node.val = start → terminalGateSelected records node = false) ∧
  ∀ node : Fin (n + 2), start < node.val → node.val ≤ start + length →
    terminalGateSelected records node = true

/-- Actual physical inputs of the component, in its NAND evaluation order. -/
def segmentWire (n start length : Nat) (bound : start + length ≤ n + 1)
    (index : Fin (length + 1)) : TerminalSupportWire (n + 1) (n + 2) :=
  if zero : index.val = 0 then .gate ⟨start,by omega⟩
  else if final : start + index.val = n + 1 then .input 0
  else .input ⟨start + index.val,by have h := index.isLt; omega⟩

theorem segmentWire_injective (n start length : Nat) (bound : start + length ≤ n + 1) :
    Function.Injective (segmentWire n start length bound) := by
  intro left right same
  by_cases lzero : left.val = 0
  · by_cases rzero : right.val = 0
    · exact Fin.ext (lzero.trans rzero.symm)
    · simp only [segmentWire,dif_pos lzero,dif_neg rzero] at same
      split at same <;> cases same
  · by_cases rzero : right.val = 0
    · simp only [segmentWire,dif_neg lzero,dif_pos rzero] at same
      split at same <;> cases same
    · simp only [segmentWire,dif_neg lzero,dif_neg rzero] at same
      by_cases lfinal : start + left.val = n + 1
      · rw [dif_pos lfinal] at same
        by_cases rfinal : start + right.val = n + 1
        · apply Fin.ext
          omega
        · rw [dif_neg rfinal] at same
          have indices := TerminalSupportWire.input.inj same
          have values := congrArg (fun i : Fin (n + 1) => i.val) indices
          change 0 = start + right.val at values
          exfalso
          omega
      · rw [dif_neg lfinal] at same
        by_cases rfinal : start + right.val = n + 1
        · rw [dif_pos rfinal] at same
          have indices := TerminalSupportWire.input.inj same
          have values := congrArg (fun i : Fin (n + 1) => i.val) indices
          change start + left.val = 0 at values
          exfalso
          omega
        · rw [dif_neg rfinal] at same
          have indices := TerminalSupportWire.input.inj same
          have values := congrArg (fun i : Fin (n + 1) => i.val) indices
          apply Fin.ext
          change start + left.val = start + right.val at values
          omega

theorem segmentWire_member (n start length : Nat) (bound : start + length ≤ n + 1)
    (positive : 0 < length)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (span : CutSpan n records start length) (index : Fin (length + 1)) :
    segmentWire n start length bound index ∈ terminalBoundaryPorts (candidate n).program records := by
  unfold segmentWire
  split
  · apply (GuardedSpineCuts.gate_boundary_iff n records _).mpr
    refine ⟨span.1 _ rfl,⟨⟨start + 1,by omega⟩,rfl,?_⟩⟩
    exact span.2 _ (by change start < start + 1; omega) (by change start + 1 ≤ start + length; omega)
  · rename_i notZero
    split
    · rename_i final
      apply (GuardedSpineCuts.guard_boundary_iff n records).mpr
      apply Or.inr
      apply span.2
      · change start < n + 1
        omega
      · change n + 1 ≤ start + length
        have h := index.isLt
        omega
    · rename_i notFinal
      apply (GuardedSpineCuts.fresh_boundary_iff n records _ (by change 0 < start + index.val; omega)).mpr
      apply span.2
      · change start < start + index.val
        omega
      · change start + index.val ≤ start + length
        have h := index.isLt
        omega

def segmentPort (n start length : Nat) (bound : start + length ≤ n + 1)
    (positive : 0 < length)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (span : CutSpan n records start length) (index : Fin (length + 1)) :
    Fin (terminalBoundaryPorts (candidate n).program records).length :=
  ⟨(terminalBoundaryPorts (candidate n).program records).idxOf
      (segmentWire n start length bound index),
    List.idxOf_lt_length_of_mem (segmentWire_member n start length bound positive records span index)⟩

theorem segmentPort_get (n start length : Nat) (bound : start + length ≤ n + 1)
    (positive : 0 < length)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (span : CutSpan n records start length) (index : Fin (length + 1)) :
    (terminalBoundaryPorts (candidate n).program records).get
      (segmentPort n start length bound positive records span index) =
        segmentWire n start length bound index := by
  have found := List.findIdx_getElem
    (xs := terminalBoundaryPorts (candidate n).program records)
    (p := fun wire => wire == segmentWire n start length bound index)
    (w := List.idxOf_lt_length_of_mem
      (segmentWire_member n start length bound positive records span index))
  exact beq_iff_eq.mp found

theorem segmentPort_injective (n start length : Nat) (bound : start + length ≤ n + 1)
    (positive : 0 < length)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (span : CutSpan n records start length) :
    Function.Injective (segmentPort n start length bound positive records span) := by
  intro left right same
  have wires := congrArg (fun port => (terminalBoundaryPorts (candidate n).program records).get port) same
  rw [segmentPort_get,segmentPort_get] at wires
  exact segmentWire_injective n start length bound wires

/-- Unsimplified read-once NAND chain; this is proof syntax, not a second extractor. -/
def chainTerm : Nat → Term
  | 0 => .input 0
  | length + 1 => .node (chainTerm length) (.input (length + 1))

private theorem chain_variables (length : Nat) :
    ReadOnceTerm.variables (chainTerm length) = List.range (length + 1) := by
  induction length with
  | zero => rfl
  | succ length ih =>
      change ReadOnceTerm.variables (chainTerm length) ++ [length + 1] = _
      rw [ih]
      exact List.range_succ.symm

private theorem chain_constants (length : Nat) : DemandForest.constants (chainTerm length) = 0 := by
  induction length with
  | zero => rfl
  | succ length ih =>
      change DemandForest.constants (chainTerm length) + 0 = 0
      exact ih

private theorem chain_natural_sound (length : Nat) (input : Nat → Bool) :
    value input (chainTerm length) =
      value (extendInput (fun index : Fin (length + 1) => input index.val)) (chainTerm length) := by
  apply ReadOnceTerm.value_congr
  intro index member
  have bound : index < length + 1 := List.mem_range.mp ((chain_variables length) ▸ member)
  unfold extendInput
  rw [dif_pos bound]

private theorem singleton_distinct (index : Nat) : ([index] : List Nat).Nodup := by
  constructor
  · intro other member
    cases member
  · constructor

private theorem chain_distinct (length : Nat) :
    (ReadOnceTerm.variables (chainTerm length)).Nodup := by
  induction length with
  | zero => exact singleton_distinct _
  | succ length ih =>
      change (ReadOnceTerm.variables (chainTerm length) ++ [length + 1]).Nodup
      apply List.nodup_append.mpr
      refine ⟨ih,singleton_distinct _,?_⟩
      intro left member right single
      have same : right = length + 1 := List.mem_singleton.mp single
      subst right
      have before : left < length + 1 := List.mem_range.mp ((chain_variables length) ▸ member)
      exact Nat.ne_of_lt before

private theorem chain_essential (length : Nat) (index : Fin (length + 1)) :
    Essential (fun input : Valuation (length + 1) => value (extendInput input) (chainTerm length)) index := by
  have member : index.val ∈ ReadOnceTerm.variables (chainTerm length) := by
    rw [chain_variables]
    exact List.mem_range.mpr index.isLt
  have distinct := chain_distinct length
  obtain ⟨left,right,agree,changed⟩ :=
    ReadOnceTerm.essential_witness (chainTerm length) (chain_constants length) distinct index.val member
  refine ⟨fun other => left other.val,fun other => right other.val,?_,?_⟩
  · intro other different
    exact agree other.val (fun same => different (Fin.ext same))
  · intro same
    apply changed
    exact (chain_natural_sound length left).trans (same.trans (chain_natural_sound length right).symm)

private def extendMap {small large : Nat} (mapping : Fin small → Fin large)
    (input : Valuation small) : Valuation large :=
  fun port => match (allFin small).find? (fun index => mapping index == port) with
    | none => false
    | some index => input index

private theorem extendMap_at {small large : Nat} (mapping : Fin small → Fin large)
    (injective : Function.Injective mapping) (input : Valuation small) (index : Fin small) :
    extendMap mapping input (mapping index) = input index := by
  unfold extendMap
  cases found : (allFin small).find? (fun other => mapping other == mapping index) with
  | none =>
      have impossible := (List.find?_eq_none.mp found) index (mem_allFin index)
      exact False.elim (impossible (beq_iff_eq.mpr rfl))
  | some actual =>
      have hit := List.find?_some (p := fun other => mapping other == mapping index) found
      have same : actual = index := injective (beq_iff_eq.mp hit)
      rw [same]

private theorem embedded_essential_iff {small large : Nat}
    (function : Valuation small → Bool) (essential : ∀ index, Essential function index)
    (mapping : Fin small → Fin large) (injective : Function.Injective mapping)
    (port : Fin large) :
    Essential (fun input : Valuation large => function (fun index => input (mapping index))) port ↔
      ∃ index, mapping index = port := by
  constructor
  · intro important
    by_cases found : ∃ index, mapping index = port
    · exact found
    · exfalso
      rcases important with ⟨left,right,agree,changed⟩
      apply changed
      apply congrArg function
      funext index
      exact agree _ (fun same => found ⟨index,same⟩)
  · rintro ⟨index,rfl⟩
    rcases essential index with ⟨left,right,agree,changed⟩
    refine ⟨extendMap mapping left,extendMap mapping right,?_,?_⟩
    · intro other different
      unfold extendMap
      cases found : (allFin small).find? (fun i => mapping i == other) with
      | none => rfl
      | some actual =>
          apply agree
          intro same
          apply different
          have hit := List.find?_some (p := fun i => mapping i == other) found
          have matched : mapping actual = other := beq_iff_eq.mp hit
          exact matched.symm.trans (congrArg mapping same)
    · dsimp only
      have leftRead : (fun i => extendMap mapping left (mapping i)) = left := by
        funext i
        exact extendMap_at mapping injective left i
      have rightRead : (fun i => extendMap mapping right (mapping i)) = right := by
        funext i
        exact extendMap_at mapping injective right i
      rw [leftRead,rightRead]
      exact changed

private theorem nand_comm (left right : Bool) : boolNand left right = boolNand right left := by
  cases left <;> cases right <;> rfl

private theorem segment_prefix_value (n start length : Nat) (bound : start + length ≤ n + 1)
    (positive : 0 < length)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (span : CutSpan n records start length)
    (valuation : Valuation (terminalBoundaryPorts (candidate n).program records).length)
    (steps : Nat) (within : steps ≤ length) :
    terminalOpenWireValue (candidate n) records valuation (.gate ⟨start + steps,by omega⟩) =
      value (extendInput (fun index => valuation
        (segmentPort n start length bound positive records span index))) (chainTerm steps) := by
  have portRead (index : Fin (length + 1)) :
      terminalOpenWireValue (candidate n) records valuation
        (segmentWire n start length bound index) =
      valuation (segmentPort n start length bound positive records span index) := by
    have read := terminalOpenWireValue_boundary_get (candidate n) records valuation
      (segmentPort n start length bound positive records span index)
    rw [segmentPort_get] at read
    exact read
  induction steps with
  | zero =>
      have read := portRead (0 : Fin (length + 1))
      simp only [segmentWire,Fin.val_zero] at read
      change terminalOpenWireValue (candidate n) records valuation (.gate ⟨start,by omega⟩) =
        extendInput _ 0
      rw [show (0 : Nat) = (0 : Fin (length + 1)).val by simp only [Fin.val_zero],
        DemandForest.extendInput_at]
      exact read
  | succ steps ih =>
      have selected : terminalGateSelected records ⟨start + (steps + 1),by omega⟩ = true :=
        span.2 _ (by change start < start + (steps + 1); omega)
          (by change start + (steps + 1) ≤ start + length; omega)
      have openSelected :
          terminalOpenWireValue (candidate n) records valuation (.gate ⟨start + (steps + 1),by omega⟩) =
          terminalOpenGateEvaluation (candidate n) records valuation ⟨start + (steps + 1),by omega⟩ := by
        change (if terminalGateSelected records ⟨start + (steps + 1),by omega⟩ then _ else _) = _
        rw [selected]
        rfl
      rw [openSelected,terminalOpenGateEvaluation_sourceEquation,selected,GuardedSpineCuts.sources]
      have notZero : start + (steps + 1) ≠ 0 := by omega
      simp only [dif_neg notZero,if_true]
      have predecessor : start + (steps + 1) - 1 = start + steps := by omega
      have read := portRead (⟨steps + 1,by omega⟩ : Fin (length + 1))
      have indexNotZero : steps + 1 ≠ 0 := by omega
      simp only [segmentWire,dif_neg indexNotZero] at read
      change _ = boolNand
        (value (extendInput _) (chainTerm steps))
        (extendInput _ (steps + 1))
      have lastRead : extendInput
          (fun index => valuation (segmentPort n start length bound positive records span index))
          (steps + 1) =
          valuation (segmentPort n start length bound positive records span ⟨steps + 1,by omega⟩) :=
        DemandForest.extendInput_at _ ⟨steps + 1,by omega⟩
      rw [lastRead]
      by_cases final : start + (steps + 1) = n + 1
      · rw [dif_pos final] at read ⊢
        change boolNand (terminalOpenWireValue (candidate n) records valuation (.input 0))
          (terminalOpenWireValue (candidate n) records valuation (.gate ⟨n,by omega⟩)) = _
        have priorIndex : (⟨n,by omega⟩ : Fin (n + 2)) = ⟨start + steps,by omega⟩ := Fin.ext (by change n = start + steps; omega)
        rw [priorIndex,nand_comm,ih (by omega),read]
      · rw [dif_neg final] at read ⊢
        change boolNand
          (terminalOpenWireValue (candidate n) records valuation
            (.gate ⟨start + (steps + 1) - 1,by omega⟩))
          (terminalOpenWireValue (candidate n) records valuation
            (.input ⟨start + (steps + 1),by omega⟩)) = _
        have priorIndex : (⟨start + (steps + 1) - 1,by omega⟩ : Fin (n + 2)) =
            ⟨start + steps,by omega⟩ := Fin.ext predecessor
        rw [priorIndex,ih (by omega),read]

/-- Independent-boundary semantics of every selected component after a cut. -/
theorem segment_value (n start length : Nat) (bound : start + length ≤ n + 1)
    (positive : 0 < length)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (span : CutSpan n records start length)
    (valuation : Valuation (terminalBoundaryPorts (candidate n).program records).length) :
    terminalOpenGateEvaluation (candidate n) records valuation ⟨start + length,by omega⟩ =
      value (extendInput (fun index => valuation
        (segmentPort n start length bound positive records span index))) (chainTerm length) := by
  have result := segment_prefix_value n start length bound positive records span valuation length (Nat.le_refl _)
  have selected : terminalGateSelected records ⟨start + length,by omega⟩ = true :=
    span.2 _ (by change start < start + length; omega) (Nat.le_refl _)
  change (if terminalGateSelected records ⟨start + length,by omega⟩ then _ else _) = _ at result
  rw [selected] at result
  exact result

/-- Exact essential ports; neither syntax occurrence nor completeness is supplied. -/
theorem segment_essential_iff (n start length : Nat) (bound : start + length ≤ n + 1)
    (positive : 0 < length)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (span : CutSpan n records start length)
    (port : Fin (terminalBoundaryPorts (candidate n).program records).length) :
    Essential (fun valuation => terminalOpenGateEvaluation (candidate n) records valuation
      ⟨start + length,by omega⟩) port ↔
      ∃ index : Fin (length + 1), segmentPort n start length bound positive records span index = port := by
  have same : (fun valuation => terminalOpenGateEvaluation (candidate n) records valuation
      ⟨start + length,by omega⟩) =
      (fun valuation => value (extendInput (fun index => valuation
        (segmentPort n start length bound positive records span index))) (chainTerm length)) := by
    funext valuation
    exact segment_value n start length bound positive records span valuation
  rw [same]
  exact embedded_essential_iff _ (chain_essential length)
    (segmentPort n start length bound positive records span)
    (segmentPort_injective n start length bound positive records span) port

/-- Every selected coordinate is either in the initial component or follows a
derived omitted coordinate. No connectedness or supplied partition is assumed. -/
theorem selected_component (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (last : Nat) (bound : last < n + 2)
    (selected : terminalGateSelected records ⟨last,bound⟩ = true) :
    Through n records last ∨
      ∃ start length : Nat, 0 < length ∧ start + length = last ∧ CutSpan n records start length := by
  induction last with
  | zero =>
      apply Or.inl
      intro node before
      have same : node = (⟨0,bound⟩ : Fin (n + 2)) := Fin.ext (by change node.val = 0; omega)
      rw [same]
      exact selected
  | succ last ih =>
      cases previous : terminalGateSelected records ⟨last,by omega⟩ with
      | false =>
          apply Or.inr
          refine ⟨last,1,by omega,rfl,?_,?_⟩
          · intro node atCut
            have same : node = (⟨last,by omega⟩ : Fin (n + 2)) := Fin.ext atCut
            rw [same]
            exact previous
          · intro node after before
            have same : node = (⟨last + 1,bound⟩ : Fin (n + 2)) := Fin.ext (by change node.val = last + 1; omega)
            rw [same]
            exact selected
      | true =>
          rcases ih (by omega) previous with initial | ⟨start,length,positive,total,span⟩
          · apply Or.inl
            intro node before
            by_cases earlier : node.val ≤ last
            · exact initial node earlier
            · have same : node = (⟨last + 1,bound⟩ : Fin (n + 2)) := Fin.ext (by change node.val = last + 1; omega)
              rw [same]
              exact selected
          · apply Or.inr
            refine ⟨start,length + 1,by omega,by omega,span.1,?_⟩
            intro node after before
            by_cases earlier : node.val ≤ last
            · exact span.2 node after (by omega)
            · have same : node = (⟨last + 1,bound⟩ : Fin (n + 2)) := Fin.ext (by change node.val = last + 1; omega)
              rw [same]
              exact selected


/-- A proper selection containing the final gate has a derived final cut component. -/
theorem proper_final_component (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (finalSelected : terminalGateSelected records (Fin.last (n + 1)) = true)
    (proper : ∃ node, terminalGateSelected records node = false) :
    ∃ start length : Nat, 0 < length ∧ start + length = n + 1 ∧ CutSpan n records start length := by
  rcases selected_component n records (n + 1) (by omega) finalSelected with initial | component
  · rcases proper with ⟨node,outside⟩
    have selected := initial node (by have h := node.isLt; omega)
    rw [selected] at outside
    cases outside
  · exact component

/-- The initial and final components of a proper selection have exactly one
shared essential physical boundary wire: the original guard input. -/
theorem prefix_final_common_port (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 profileWidth))
    (last : Fin (n + 1)) (through : Through n records last.val)
    (finalSelected : terminalGateSelected records (Fin.last (n + 1)) = true)
    (proper : ∃ node, terminalGateSelected records node = false)
    (port : Fin (terminalBoundaryPorts (candidate n).program records).length) :
    (Essential (fun valuation => terminalOpenGateEvaluation (candidate n) records valuation
        last.castSucc) port ∧
      Essential (fun valuation => terminalOpenGateEvaluation (candidate n) records valuation
        (Fin.last (n + 1))) port) ↔
      (terminalBoundaryPorts (candidate n).program records).get port = .input 0 := by
  rcases proper_final_component n records finalSelected proper with
    ⟨start,length,positive,total,span⟩
  have bound : start + length ≤ n + 1 := Nat.le_of_eq total
  have initialBound : last.val ≤ n := by have h := last.isLt; omega
  have after : last.val < start := by
    by_cases before : start ≤ last.val
    · have outside := span.1 ⟨start,by omega⟩ rfl
      have inside := through ⟨start,by omega⟩ before
      rw [inside] at outside
      cases outside
    · omega
  have finalIndex : (⟨start + length,by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) :=
    Fin.ext total
  have lookupInjective : Function.Injective (fun index : Fin
      (terminalBoundaryPorts (candidate n).program records).length =>
      (terminalBoundaryPorts (candidate n).program records).get index) := by
    intro left right same
    apply Fin.ext
    exact (List.getElem_inj (terminalBoundaryPorts_nodup (candidate n).program records)).mp same
  constructor
  · rintro ⟨initialEssential,finalEssential⟩
    rcases (GuardedSpineOpenPrefix.prefix_essential_iff n last.val initialBound records through port).mp
      initialEssential with ⟨initialIndex,initialPort⟩
    have converted : Essential (fun valuation => terminalOpenGateEvaluation (candidate n) records valuation
        ⟨start + length,by omega⟩) port := by
      rw [finalIndex]
      exact finalEssential
    rcases (segment_essential_iff n start length bound positive records span port).mp converted with
      ⟨index,finalPort⟩
    have initialWire : (terminalBoundaryPorts (candidate n).program records).get port =
        .input (⟨initialIndex.val,by have h := initialIndex.isLt; omega⟩ : Fin (n + 1)) := by
      rw [← initialPort,GuardedSpineOpenPrefix.prefixPort_get]
    have finalWire : (terminalBoundaryPorts (candidate n).program records).get port =
        segmentWire n start length bound index := by
      rw [← finalPort,segmentPort_get]
    unfold segmentWire at finalWire
    by_cases zero : index.val = 0
    · rw [dif_pos zero] at finalWire
      have impossible := initialWire.symm.trans finalWire
      cases impossible
    · rw [dif_neg zero] at finalWire
      by_cases final : start + index.val = n + 1
      · rw [dif_pos final] at finalWire
        exact finalWire
      · rw [dif_neg final] at finalWire
        have indices := TerminalSupportWire.input.inj (initialWire.symm.trans finalWire)
        have values := congrArg (fun i : Fin (n + 1) => i.val) indices
        have upper := initialIndex.isLt
        change initialIndex.val = start + index.val at values
        exfalso
        omega
  · intro guard
    constructor
    · apply (GuardedSpineOpenPrefix.prefix_essential_iff n last.val initialBound records through port).mpr
      refine ⟨0,?_⟩
      apply lookupInjective
      dsimp only
      rw [GuardedSpineOpenPrefix.prefixPort_get,guard]
      rfl
    · have finalEssential : Essential (fun valuation => terminalOpenGateEvaluation (candidate n) records valuation
          ⟨start + length,by omega⟩) port := by
        apply (segment_essential_iff n start length bound positive records span port).mpr
        refine ⟨Fin.last length,?_⟩
        apply lookupInjective
        dsimp only
        rw [segmentPort_get,guard]
        have nonzero : length ≠ 0 := by omega
        simp only [segmentWire,Fin.val_last,dif_neg nonzero,dif_pos total]
      rw [finalIndex] at finalEssential
      exact finalEssential

end PNP.DirectWire.GuardedSpineOpenSegments
