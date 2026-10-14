import Std

/-!
Finite, same-vertex port encoding of a fixed elimination tree.

The vertex names `Fin n` are in a topological numbering: parents have smaller
indices. `FixedOrder.vertices` is an independent ordering, used for every bag.
No agreement of these two orders is assumed. The tree parent relation is not
required to be a graph edge. Relation symbols and both directions are separate
bits. Inherited ports with all relation bits false remain in the encoding.

This file proves an actual codec, not an assumed encoding equivalence. It does
not formalize MSO, canonical-tree selection, reindexing an abstract tree,
first-child/next-sibling conversion, or algebraicity of a series.
-/
namespace StackSorting.FinitePort

abbrev Vertex (n : Nat) := Fin n

structure RootedTree (n : Nat) where
  parent : Vertex n → Vertex n
  parent_lt : ∀ v, v.val ≠ 0 → (parent v).val < v.val

inductive Ancestor {n : Nat} (T : RootedTree n) : Vertex n → Vertex n → Prop
  | refl (v) : Ancestor T v v
  | step {u v} : v.val ≠ 0 → Ancestor T u (T.parent v) → Ancestor T u v

namespace Ancestor

theorem val_le {n} {T : RootedTree n} {u v} (h : Ancestor T u v) :
    u.val ≤ v.val := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step v hv _ ih => have := T.parent_lt v hv; omega

theorem trans {n} {T : RootedTree n} {u v w}
    (huv : Ancestor T u v) (hvw : Ancestor T v w) : Ancestor T u w := by
  induction hvw with
  | refl => exact huv
  | step hv _ ih => exact .step hv ih

theorem parent_of_ne {n} {T : RootedTree n} {u v}
    (h : Ancestor T u v) (hne : u ≠ v) : Ancestor T u (T.parent v) := by
  cases h with
  | refl => exact False.elim (hne rfl)
  | step _ hp => exact hp

theorem ne_zero_of_strict {n} {T : RootedTree n} {u v}
    (h : Ancestor T u v) (hne : u ≠ v) : v.val ≠ 0 := by
  intro hz
  have hu := h.val_le
  have he : u.val = v.val := by omega
  exact hne (Fin.ext he)

end Ancestor

structure FixedOrder (n : Nat) where
  vertices : List (Vertex n)
  nodup : vertices.Nodup
  complete : ∀ v, v ∈ vertices

/-- `colors` and `relations` are arbitrary fixed finite vocabularies. -/
structure Diagram (n colors relations : Nat) where
  color : Vertex n → Fin colors → Bool
  rel : Fin relations → Vertex n → Vertex n → Bool

def Adjacent {n colors relations} (G : Diagram n colors relations) (u v : Vertex n) : Prop :=
  ∃ r, G.rel r u v = true ∨ G.rel r v u = true

def Loopless {n colors relations} (G : Diagram n colors relations) : Prop :=
  ∀ r v, G.rel r v v = false

def Eliminates {n colors relations} (T : RootedTree n) (G : Diagram n colors relations) : Prop :=
  ∀ u v, Adjacent G u v → Ancestor T u v ∨ Ancestor T v u

/-- The exact inherited part of the induced elimination bag. -/
def Inherited {n colors relations} (T : RootedTree n) (G : Diagram n colors relations)
    (v u : Vertex n) : Prop :=
  Ancestor T u v ∧ u ≠ v ∧ ∃ z, Ancestor T v z ∧ Adjacent G u z

noncomputable def inherited {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) (v : Vertex n) : List (Vertex n) :=
  @List.filter _ (fun u => @decide (Inherited T G v u) (Classical.propDecidable _)) O.vertices

noncomputable def bag {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) (v : Vertex n) : List (Vertex n) :=
  v :: inherited T O G v

@[simp] theorem mem_inherited {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) (v u : Vertex n) :
    u ∈ inherited T O G v ↔ Inherited T G v u := by
  classical
  simp [inherited, O.complete]

@[simp] theorem mem_bag {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) (v u : Vertex n) :
    u ∈ bag T O G v ↔ u = v ∨ Inherited T G v u := by
  simp [bag]

theorem bag_nodup {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) (v : Vertex n) :
    (bag T O G v).Nodup := by
  classical
  apply List.nodup_cons.mpr
  constructor
  · simpa [Inherited] using (show ¬ Inherited T G v v by simp [Inherited])
  · exact O.nodup.filter _

theorem inherited_root_empty {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) (v : Vertex n)
    (hv : v.val = 0) : inherited T O G v = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro u hu
  obtain ⟨ha, hn, _⟩ := (mem_inherited T O G v u).mp hu
  exact (ha.ne_zero_of_strict hn) hv

/-- Parent-bag containment is derived from the exact descendant-neighbor
formula. In particular it does not require the parent link to be an edge. -/
theorem inherited_parent_mem {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) {v u : Vertex n}
    (hu : u ∈ inherited T O G v) : u ∈ bag T O G (T.parent v) := by
  obtain ⟨ha, hn, z, hz, he⟩ := (mem_inherited T O G v u).mp hu
  apply (mem_bag T O G (T.parent v) u).mpr
  by_cases hp : u = T.parent v
  · exact .inl hp
  · right
    refine ⟨ha.parent_of_ne hn, hp, z, ?_, he⟩
    exact (Ancestor.step (ha.ne_zero_of_strict hn) (Ancestor.refl (T.parent v))).trans hz

/-- One entry per inherited port, even when its entire bit vector is zero. -/
structure PortEntry (relations : Nat) where
  parentPort : Nat
  bit : Fin relations → Bool → Bool

structure NodeLabel (colors relations : Nat) where
  color : Fin colors → Bool
  ports : List (PortEntry relations)

abbrev Code (n colors relations : Nat) := Vertex n → NodeLabel colors relations

noncomputable def entry {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) (v u : Vertex n) : PortEntry relations where
  parentPort := (bag T O G (T.parent v)).idxOf u
  bit := fun r forward => if forward then G.rel r v u else G.rel r u v

noncomputable def encode {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) : Code n colors relations :=
  fun v => ⟨G.color v, (inherited T O G v).map (entry T O G v)⟩

/-- Port 0 is the node itself. Every inherited port follows the encoded map
one parent step. `fuel = n` suffices on an n-vertex tree. -/
def readPort {n colors relations} (T : RootedTree n) (C : Code n colors relations) :
    Nat → Vertex n → Nat → Option (Vertex n)
  | _, v, 0 => some v
  | 0, _, _ + 1 => none
  | fuel + 1, v, i + 1 => (C v).ports[i]?.bind (fun e => readPort T C fuel (T.parent v) e.parentPort)

theorem getElem?_idxOf_of_mem {α} [BEq α] [LawfulBEq α]
    {xs : List α} {u : α} (hu : u ∈ xs) : xs[xs.idxOf u]? = some u := by
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hu)]
  simp

/-- The all-size port recovery theorem, with a quantitative termination bound. -/
theorem readPort_encode {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) (fuel : Nat)
    (v u : Vertex n) (i : Nat) (hv : v.val ≤ fuel)
    (hi : (bag T O G v)[i]? = some u) :
    readPort T (encode T O G) fuel v i = some u := by
  induction fuel generalizing v u i with
  | zero =>
    have hroot := inherited_root_empty T O G v (by omega)
    cases i with
    | zero => simpa [readPort, bag] using hi
    | succ i => simp [bag, hroot] at hi
  | succ fuel ih =>
    cases i with
    | zero => simpa [readPort, bag] using hi
    | succ i =>
      have hi' : (inherited T O G v)[i]? = some u := hi
      have hu := List.mem_of_getElem? hi'
      have ha := (mem_inherited T O G v u).mp hu
      have hparent := T.parent_lt v (ha.1.ne_zero_of_strict ha.2.1)
      have hmem := inherited_parent_mem T O G hu
      have hind := ih (T.parent v) u ((bag T O G (T.parent v)).idxOf u)
        (by omega) (getElem?_idxOf_of_mem hmem)
      simpa [readPort, encode, List.getElem?_map, hi', entry] using hind

/-- Every valid port has its unique original-vertex identity. -/
theorem encoded_port_identity {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations)
    (v u : Vertex n) (i : Nat) (hi : (bag T O G v)[i]? = some u) :
    readPort T (encode T O G) n v i = some u :=
  readPort_encode T O G n v u i (Nat.le_of_lt v.isLt) hi

def EdgeAt {n colors relations} (T : RootedTree n) (C : Code n colors relations)
    (v u : Vertex n) (r : Fin relations) (forward : Bool) : Prop :=
  ∃ i e, (C v).ports[i]? = some e ∧
    readPort T C n v (i + 1) = some u ∧ e.bit r forward = true

/-- Every decoded relation has one deeper owner; the two disjuncts express
the two possible directions of the same input relation symbol. -/
def DecodedRel {n colors relations} (T : RootedTree n) (C : Code n colors relations)
    (r : Fin relations) (a b : Vertex n) : Prop :=
  EdgeAt T C a b r true ∨ EdgeAt T C b a r false

theorem edgeAt_encode_iff {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations)
    (v u : Vertex n) (r : Fin relations) (forward : Bool) :
    EdgeAt T (encode T O G) v u r forward ↔
      u ∈ inherited T O G v ∧ (if forward then G.rel r v u else G.rel r u v) = true := by
  constructor
  · rintro ⟨i, e, he, hr, hb⟩
    have hm : ((inherited T O G v)[i]?).map (entry T O G v) = some e := by
      simpa [encode] using he
    obtain ⟨w, hw, hwe⟩ := Option.map_eq_some_iff.mp hm
    have hread := encoded_port_identity T O G v w (i + 1) hw
    have hwu : w = u := Option.some.inj (hread.symm.trans hr)
    subst w
    subst e
    exact ⟨List.mem_of_getElem? hw, hb⟩
  · rintro ⟨hu, hb⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hu
    refine ⟨i, entry T O G v u, ?_, ?_, hb⟩
    · simp [encode, hi]
    · exact encoded_port_identity T O G v u (i + 1) hi

theorem adjacent_symm {n colors relations} (G : Diagram n colors relations)
    {a b : Vertex n} (h : Adjacent G a b) : Adjacent G b a := by
  obtain ⟨r, h⟩ := h
  exact ⟨r, h.symm⟩

/-- Exact decoding of every relation symbol and direction, at every size. -/
theorem decode_encode_relation {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations)
    (hloop : Loopless G) (helim : Eliminates T G)
    (r : Fin relations) (a b : Vertex n) :
    DecodedRel T (encode T O G) r a b ↔ G.rel r a b = true := by
  rw [DecodedRel, edgeAt_encode_iff, edgeAt_encode_iff]
  change (b ∈ inherited T O G a ∧ G.rel r a b = true) ∨
    (a ∈ inherited T O G b ∧ G.rel r a b = true) ↔ G.rel r a b = true
  constructor
  · intro h
    rcases h with h | h <;> exact h.2
  · intro hrel
    have hne : a ≠ b := by
      intro he
      subst b
      have := hloop r a
      simp [this] at hrel
    have he : Adjacent G a b := ⟨r, .inl hrel⟩
    rcases helim a b he with hab | hba
    · right
      refine ⟨(mem_inherited T O G b a).mpr ?_, hrel⟩
      exact ⟨hab, hne, b, .refl b, he⟩
    · left
      refine ⟨(mem_inherited T O G a b).mpr ?_, hrel⟩
      exact ⟨hba, Ne.symm hne, a, .refl a, adjacent_symm G he⟩

noncomputable def decode {n colors relations} (T : RootedTree n)
    (C : Code n colors relations) : Diagram n colors relations where
  color := fun v => (C v).color
  rel := fun r a b => @decide (DecodedRel T C r a b) (Classical.propDecidable _)

/-- Same-node identity: the decoded diagram is definitionally on the original
`Fin n`, and equals the source diagram, rather than merely an isomorphic copy. -/
theorem decode_encode {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations)
    (hloop : Loopless G) (helim : Eliminates T G) :
    decode T (encode T O G) = G := by
  have hrel : (decode T (encode T O G)).rel = G.rel := by
    funext r a b
    have h := decode_encode_relation T O G hloop helim r a b
    simp only [decode]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using h
  cases G with
  | mk color rel =>
    change Diagram.mk color _ = Diagram.mk color rel
    exact congrArg (Diagram.mk color) hrel

/-- Encoding has no multiplicity when the tree and fixed order are given. -/
theorem encode_injective {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G H : Diagram n colors relations)
    (hGl : Loopless G) (hGe : Eliminates T G)
    (hHl : Loopless H) (hHe : Eliminates T H)
    (hcode : encode T O G = encode T O H) : G = H := by
  rw [← decode_encode T O G hGl hGe, hcode, decode_encode T O H hHl hHe]

def WidthAtMost {n colors relations} (T : RootedTree n) (O : FixedOrder n)
    (G : Diagram n colors relations) (W : Nat) : Prop :=
  ∀ v, (inherited T O G v).length ≤ W

def BoundedCode {n colors relations} (C : Code n colors relations) (W : Nat) : Prop :=
  ∀ v, (C v).ports.length ≤ W ∧ ∀ e ∈ (C v).ports, e.parentPort ≤ W

/-- Width bounds both the number of ports and every stored parent-port index.
Together with the two finite bit-vector fields, this is a finite alphabet. -/
theorem encode_bounded {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) (W : Nat)
    (hW : WidthAtMost T O G W) : BoundedCode (encode T O G) W := by
  intro v
  constructor
  · simpa [encode] using hW v
  · intro e he
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
    have hp := inherited_parent_mem T O G hu
    have hi := List.idxOf_lt_length_of_mem hp
    have hw := hW (T.parent v)
    have hb : (bag T O G (T.parent v)).length = (inherited T O G (T.parent v)).length + 1 := rfl
    change (bag T O G (T.parent v)).idxOf u ≤ W
    omega

/-- A zero-edge inherited port still has a concrete entry and is recovered.
No positive edge bit is a premise of this theorem. -/
theorem every_inherited_port_is_kept {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) (v u : Vertex n)
    (hu : Inherited T G v u) :
    ∃ i, (encode T O G v).ports[i]? = some (entry T O G v u) ∧
      readPort T (encode T O G) n v (i + 1) = some u := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ((mem_inherited T O G v u).mpr hu)
  exact ⟨i, by simp [encode, hi], encoded_port_identity T O G v u (i + 1) hi⟩

#print axioms readPort_encode
#print axioms decode_encode_relation
#print axioms decode_encode
#print axioms encode_injective
#print axioms encode_bounded
#print axioms every_inherited_port_is_kept

end StackSorting.FinitePort
