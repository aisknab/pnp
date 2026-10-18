import PNP.Concrete.ResidualReduction.SourceNativeSystemParse

/-! Literal final serialization. Each protected reverse buffer is traversed by
instructions, and both unary headers are written from the constructed counters.
The exact result is the family packet expected by the verified history runner. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeSystemSerialize
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceNativeSystemState

def reverseInto (field : Field) : Block 24 := .seq (load field 3) (core ClauseQuery.reverseLoop)
def reverseFuel (field : Field) (s : Saved) : Nat := 4 * (field.word s).length + 2

theorem reverseInto_exec (field : Field) (input out : BitString) (s : Saved) :
    Exec (reverseInto field) (work input out s) (reverseFuel field s)
      (work input ((field.word s).reverse ++ out) s) := by
  let base := {SourceScalarState.work input with output := out}
  let ready := {base with excess := field.word s}
  have first := load_exec field (Frame.join base.store (Store.empty 5)) s 3
  have updated : (Frame.join base.store (Store.empty 5)).set 3 (field.word s) =
      Frame.join ready.store (Store.empty 5) := by rfl
  rw [updated] at first
  have last : Exec ClauseQuery.reverseLoop ready.store (4 * (field.word s).length + 1)
      ({base with excess := [],output := (field.word s).reverse ++ out}).store :=
    ClauseQuery.reverse_exec base (field.word s)
  have cost : reverseFuel field s = 1 + (4 * (field.word s).length + 1) := by unfold reverseFuel; omega
  simpa only [reverseInto,cost,base,ready,work,withCore,SourceScalarState.work] using Exec.seq first (core_exec last s)

def word (s : Saved) : BitString :=
  s.dimension.reverse ++ (false :: (s.total.reverse ++ (false :: (s.rows.reverse ++ s.products.reverse))))
def block : Block 24 := .seq (reverseInto .products)
  (.seq (reverseInto .rows)
    (.seq (.action (.push 8 false))
      (.seq (reverseInto .total) (.seq (.action (.push 8 false)) (reverseInto .dimension)))))
def fuel (s : Saved) : Nat :=
  4 * (s.products.length + s.rows.length + s.total.length + s.dimension.length) + 10

theorem block_exec (input : BitString) (s : Saved) :
    Exec block (work input [] s) (fuel s) (work input (word s) s) := by
  let rows := s.rows.reverse ++ s.products.reverse
  let total := s.total.reverse ++ false :: rows
  have products : Exec (reverseInto .products) (work input [] s) (reverseFuel .products s)
      (work input s.products.reverse s) := by
    simpa only [Field.word,List.append_nil] using reverseInto_exec .products input [] s
  have linear : Exec (reverseInto .rows) (work input s.products.reverse s) (reverseFuel .rows s)
      (work input rows s) := reverseInto_exec .rows input s.products.reverse s
  have rowTag : Exec (.action (.push (8 : Fin 24) false)) (work input rows s) 1
      (work input (false :: rows) s) := .action _ _
  have count : Exec (reverseInto .total) (work input (false :: rows) s) (reverseFuel .total s)
      (work input total s) := reverseInto_exec .total input (false :: rows) s
  have dimensionTag : Exec (.action (.push (8 : Fin 24) false)) (work input total s) 1
      (work input (false :: total) s) := .action _ _
  have dimension : Exec (reverseInto .dimension) (work input (false :: total) s) (reverseFuel .dimension s)
      (work input (word s) s) := reverseInto_exec .dimension input (false :: total) s
  have checked := Exec.seq products (Exec.seq linear (Exec.seq rowTag
    (Exec.seq count (Exec.seq dimensionTag dimension))))
  have cost : fuel s = reverseFuel .products s +
      (reverseFuel .rows s + (1 + (reverseFuel .total s + (1 + reverseFuel .dimension s)))) := by
    simp only [fuel,reverseFuel,Field.word]
    omega
  simpa only [block,cost] using checked

theorem fuel_bound (s : Saved) (limit : Nat)
    (products : s.products.length ≤ limit) (rows : s.rows.length ≤ limit)
    (total : s.total.length ≤ limit) (dimension : s.dimension.length ≤ limit) :
    fuel s ≤ 16 * limit + 10 := by unfold fuel; omega

theorem canonical_word {c : Nat} (D : NativeSparseSystem.System c) :
    word (SourceNativeSystemParse.canonical D []) = SourceNativeEncoding.familyPacket D := by
  simp only [word,SourceNativeSystemParse.canonical_dimension,SourceNativeSystemParse.canonical_total,
    SourceNativeSystemParse.canonical_rows,SourceNativeSystemParse.canonical_products,
    List.reverse_replicate,List.reverse_reverse,SourceNativeEncoding.familyPacket,
    SourceNativeEncoding.familyBits,natural,List.append_assoc,List.singleton_append]

end PNP.Concrete.ResidualReduction.SourceNativeSystemSerialize
