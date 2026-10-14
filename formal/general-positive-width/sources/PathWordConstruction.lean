import BiInterfaceGraph
import BagNaming
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# A genuine small-piece word from an ordered path decomposition

The arity is the supplied **bag-cardinality bound** `k`, so a conventional
pathwidth bound `w` gives arity `w + 1`.  Original vertices have arbitrary names.
Every letter is the graph induced on one bag, with partial interfaces on its
intersection with the previous and next bags.  A final empty letter handles the
empty decomposition uniformly and makes the literal word nonempty.

`Packed.eval` uses the actual quotient operation from `BiInterfaceGraph`, not
union of labels.  The reconstruction theorem constructs its vertex equivalence;
it does not assume naming, reconstruction, or guidance witnesses.
-/

universe u v
namespace StackSorting.BiInterface.PathWord

variable {V : Type u} [DecidableEq V] {k : ℕ}

/-- Membership somewhere in an ordered bag list. -/
def Occurs (bs : List (Finset V)) (v : V) : Prop := ∃ B ∈ bs, v ∈ B

omit [DecidableEq V] in
@[simp] theorem occurs_nil (v : V) : ¬ Occurs ([] : List (Finset V)) v := by
  simp [Occurs]

omit [DecidableEq V] in
@[simp] theorem occurs_cons (B : Finset V) (bs : List (Finset V)) (v : V) :
    Occurs (B :: bs) v ↔ v ∈ B ∨ Occurs bs v := by
  simp [Occurs, or_and_right, exists_or]

/-- Occurrences are interval-contiguous: at every cut, a vertex seen on both
sides belongs to the intervening bag. This is a condition on supplied bags,
not a reconstruction witness. -/
def Convex (bs : List (Finset V)) : Prop :=
  ∀ before middle after, bs = before ++ middle :: after →
    ∀ v, Occurs before v → Occurs after v → v ∈ middle

omit [DecidableEq V] in
theorem convex_tail {B : Finset V} {bs : List (Finset V)}
    (h : Convex (B :: bs)) : Convex bs := by
  intro before middle after he v hvb hva
  apply h (B :: before) middle after (by simp [he]) v
  · exact (occurs_cons B before v).mpr (Or.inr hvb)
  · exact hva

omit [DecidableEq V] in
/-- The precise separator fact needed for reconstruction: an original vertex
in the head bag and somewhere later already occurs in the next bag. -/
theorem head_bridge {B C : Finset V} {bs : List (Finset V)}
    (h : Convex (B :: C :: bs)) {v : V}
    (hvB : v ∈ B) (hv : Occurs (C :: bs) v) : v ∈ C := by
  rcases (occurs_cons C bs v).mp hv with hvC | hvs
  · exact hvC
  · exact h [B] C bs rfl v (by simpa using hvB) hvs

/-- A simple graph with arbitrary original vertex names. -/
structure Original (V : Type u) where
  Adj : V → V → Prop
  symm : ∀ {v w}, Adj v w → Adj w v
  loopless : ∀ v, ¬ Adj v v

/-- A supplied finite, ordered path decomposition. -/
structure Decomposition (G : Original V) (k : ℕ) where
  bags : List (Finset V)
  bound : ∀ B ∈ bags, B.card ≤ k
  vertex : ∀ v, Occurs bags v
  edge : ∀ {v w}, G.Adj v w → ∃ B ∈ bags, v ∈ B ∧ w ∈ B
  interval : Convex bags

/-- The name inversion restricted to one overlap. -/
noncomputable def port (B : NamedBag V k) (S : Finset V) (i : Fin k) : Option B.bag :=
  by
    classical
    exact if h : ∃ v : B.bag, B.name v = i ∧ v.val ∈ S then some h.choose else none

@[simp] theorem port_eq_some (B : NamedBag V k) (S : Finset V)
    (i : Fin k) (v : B.bag) :
    port B S i = some v ↔ B.name v = i ∧ v.val ∈ S := by
  classical
  unfold port
  split
  · rename_i h
    have hh := h.choose_spec
    constructor
    · intro he
      have hcv : h.choose = v := Option.some.inj he
      simpa [hcv] using hh
    · intro hv
      have hcv : h.choose = v := B.name.injective (hh.1.trans hv.1.symm)
      rw [hcv]
  · rename_i h
    constructor
    · intro he; cases he
    · intro hv; exact (h ⟨v,hv⟩).elim

@[simp] theorem port_empty (B : NamedBag V k) (i : Fin k) :
    port B ∅ i = none := by
  classical
  simp [port]

noncomputable def piece (G : Original V) (prev : Finset V)
    (B : NamedBag V k) (next : Finset V) : Graph k B.bag where
  Adj := fun v w => G.Adj v.val w.val
  symm := G.symm
  loopless := fun v => G.loopless v.val
  left := port B prev
  right := port B next
  left_inj := by
    intro i j v hi hj
    exact ((port_eq_some B prev i v).mp hi).1.symm.trans
      ((port_eq_some B prev j v).mp hj).1
  right_inj := by
    intro i j v hi hj
    exact ((port_eq_some B next i v).mp hi).1.symm.trans
      ((port_eq_some B next j v).mp hj).1
  cross := by
    intro i j v hi hj
    exact ((port_eq_some B prev i v).mp hi).1.symm.trans
      ((port_eq_some B next j v).mp hj).1

/-- Heterogeneous finite graphs are only packaging. The multiplication below
is still literal quotient gluing. -/
structure Packed (k : ℕ) where
  Vertex : Type u
  finite : Finite Vertex
  graph : Graph k Vertex

attribute [instance] Packed.finite

namespace Packed

noncomputable def empty (k : ℕ) : Packed.{u} k where
  Vertex := PEmpty
  finite := inferInstance
  graph := {
    Adj := fun _ _ => False
    symm := fun h => h
    loopless := fun _ h => h
    left := fun _ => none
    right := fun _ => none
    left_inj := by intro i j v; exact v.elim
    right_inj := by intro i j v; exact v.elim
    cross := by intro i j v; exact v.elim }

noncomputable def mul (P Q : Packed.{u} k) : Packed.{u} k where
  Vertex := Glued P.graph Q.graph
  finite := inferInstance
  graph := glue P.graph Q.graph

/-- Nonempty right-associated multiplication, with an empty fallback only
for the otherwise unused empty literal word. -/
noncomputable def eval : List (Packed.{u} k) → Packed.{u} k
  | [] => empty k
  | [P] => P
  | P :: Q :: rest => mul P (eval (Q :: rest))

@[simp] theorem eval_singleton (P : Packed.{u} k) : eval [P] = P := rfl

theorem eval_cons (P : Packed.{u} k) (ps : List (Packed.{u} k)) (h : ps ≠ []) :
    eval (P :: ps) = mul P (eval ps) := by
  cases ps with
  | nil => exact (h rfl).elim
  | cons Q rest => rfl

end Packed

noncomputable def letter (G : Original V) (prev : Finset V)
    (B : NamedBag V k) (next : Finset V) : Packed.{u} k where
  Vertex := B.bag
  finite := inferInstance
  graph := piece G prev B next

def headBag : List (NamedBag V k) → Finset V
  | [] => ∅
  | B :: _ => B.bag

/-- The literal word consists of the named bag pieces followed by one empty
piece. The sentinel adds no vertices and has size zero. -/
noncomputable def word (G : Original V) (prev : Finset V) :
    List (NamedBag V k) → List (Packed.{u} k)
  | [] => [Packed.empty k]
  | B :: bs => letter G prev B (headBag bs) :: word G B.bag bs

@[simp] theorem word_ne_nil (G : Original V) (prev : Finset V)
    (bs : List (NamedBag V k)) : word G prev bs ≠ [] := by
  cases bs <;> simp [word]

@[simp] theorem word_length (G : Original V) (prev : Finset V)
    (bs : List (NamedBag V k)) : (word G prev bs).length = bs.length + 1 := by
  induction bs generalizing prev with
  | nil => simp [word]
  | cons B bs ih => simp [word, ih, Nat.add_assoc]

theorem word_small (G : Original V) (prev : Finset V)
    (bs : List (NamedBag V k)) (hb : ∀ B ∈ bs, B.bag.card ≤ k) :
    ∀ P ∈ word G prev bs, Nat.card P.Vertex ≤ k := by
  induction bs generalizing prev with
  | nil =>
    intro P hP
    have he : P = Packed.empty k := by simpa [word] using hP
    subst P
    simp [Packed.empty, Nat.card_eq_fintype_card]
  | cons B bs ih =>
    intro P hP
    rcases List.mem_cons.mp hP with he | ht
    · subst P
      simpa [letter, Nat.card_eq_fintype_card] using hb B (by simp)
    · exact ih B.bag (by intro C hC; exact hb C (by simp [hC])) P ht

/-- Right-associated product, definitionally suitable for the reconstruction
induction. The next theorem identifies it with evaluation of the literal word. -/
noncomputable def product (G : Original V) (prev : Finset V) :
    List (NamedBag V k) → Packed.{u} k
  | [] => Packed.empty k
  | B :: bs => Packed.mul (letter G prev B (headBag bs)) (product G B.bag bs)

theorem eval_word (G : Original V) (prev : Finset V) (bs : List (NamedBag V k)) :
    Packed.eval (word G prev bs) = product G prev bs := by
  induction bs generalizing prev with
  | nil => rfl
  | cons B bs ih =>
    rw [word, Packed.eval_cons _ _ (word_ne_nil G B.bag bs), ih]
    rfl

/-- Original-vertex form of the left interface of the first letter. -/
noncomputable def headPort (prev : Finset V) :
    List (NamedBag V k) → Fin k → Option V
  | [], _ => none
  | B :: _, i => (port B prev i).map Subtype.val

/-- An edge covered by at least one of these bags. -/
def CoveredEdge (G : Original V) (bs : List (Finset V)) (v w : V) : Prop :=
  ∃ B ∈ bs, v ∈ B ∧ w ∈ B ∧ G.Adj v w

omit [DecidableEq V] in
@[simp] theorem coveredEdge_nil (G : Original V) (v w : V) :
    ¬ CoveredEdge G [] v w := by simp [CoveredEdge]

omit [DecidableEq V] in
@[simp] theorem coveredEdge_cons (G : Original V) (B : Finset V)
    (bs : List (Finset V)) (v w : V) :
    CoveredEdge G (B :: bs) v w ↔
      (v ∈ B ∧ w ∈ B ∧ G.Adj v w) ∨ CoveredEdge G bs v w := by
  simp [CoveredEdge, or_and_right, exists_or]

/-- All properties are proved for the concrete product, including its actual
vertex map. `left` is its surviving outer interface in original vertex names. -/
structure Evaluation (G : Original V) (prev : Finset V)
    (bs : List (NamedBag V k)) where
  realize : (product G prev bs).Vertex → V
  injective : Function.Injective realize
  range : ∀ v, (∃ x, realize x = v) ↔ Occurs (bs.map NamedBag.bag) v
  adj : ∀ x y, (product G prev bs).graph.Adj x y ↔
    CoveredEdge G (bs.map NamedBag.bag) (realize x) (realize y)
  left : ∀ i, ((product G prev bs).graph.left i).map realize =
    headPort prev bs i
  right : ∀ i, (product G prev bs).graph.right i = none

/-- The seam in the real quotient is exactly equality of original vertices.
The reverse implication is where interval contiguity is essential. -/
theorem seam_iff (G : Original V) (prev : Finset V)
    (B : NamedBag V k) (bs : List (NamedBag V k))
    (hc : (B :: bs).IsChain NamedBag.Compatible)
    (hv : Convex ((B :: bs).map NamedBag.bag))
    (E : Evaluation G B.bag bs)
    (x : B.bag) (y : (product G B.bag bs).Vertex) :
    Seam (piece G prev B (headBag bs)) (product G B.bag bs).graph x y ↔
      x.val = E.realize y := by
  classical
  cases bs with
  | nil => exact y.elim
  | cons C cs =>
    have hBC : NamedBag.Compatible B C := (List.isChain_cons_cons.mp hc).1
    constructor
    · rintro ⟨i, hxi, hyi⟩
      have hx := (port_eq_some B C.bag i x).mp hxi
      have hy : (port C B.bag i).map Subtype.val = some (E.realize y) := by
        change headPort B.bag (C :: cs) i = some (E.realize y)
        rw [← E.left i, hyi]
        rfl
      obtain ⟨z,hzi,hzy⟩ := Option.map_eq_some_iff.mp hy
      have hz := (port_eq_some C B.bag i z).mp hzi
      have hname : C.name ⟨x.val,hx.2⟩ = C.name z :=
        (hBC x.val x.property hx.2).symm.trans (hx.1.trans hz.1.symm)
      have hxz := congrArg Subtype.val (C.name.injective hname)
      exact hxz.trans hzy
    · intro hxy
      have hyocc := (E.range (E.realize y)).mp ⟨y,rfl⟩
      have hxocc : Occurs (C.bag :: cs.map NamedBag.bag) x.val := by
        simpa [hxy] using hyocc
      have hxC : x.val ∈ C.bag := head_bridge hv x.property hxocc
      let z : C.bag := ⟨x.val,hxC⟩
      let i := B.name x
      have hxi : port B C.bag i = some x :=
        (port_eq_some B C.bag i x).mpr ⟨rfl,hxC⟩
      have hzi : port C B.bag i = some z :=
        (port_eq_some C B.bag i z).mpr
          ⟨(hBC x.val x.property hxC).symm,x.property⟩
      have hmap : ((product G B.bag (C :: cs)).graph.left i).map E.realize =
          some (E.realize y) := by
        rw [E.left i]
        change (port C B.bag i).map Subtype.val = some (E.realize y)
        rw [hzi]
        exact congrArg some hxy
      obtain ⟨y',hyi,he⟩ := Option.map_eq_some_iff.mp hmap
      have hyy : y' = y := E.injective he
      exact ⟨i,hxi,hyy ▸ hyi⟩

/-- Recursive reconstruction of every suffix. No graph isomorphism is an
input: the map is the universal map of the actual gluing quotient. -/
theorem evaluation_exists (G : Original V) (prev : Finset V)
    (bs : List (NamedBag V k))
    (hc : bs.IsChain NamedBag.Compatible)
    (hv : Convex (bs.map NamedBag.bag)) : Nonempty (Evaluation G prev bs) := by
  classical
  induction bs generalizing prev with
  | nil =>
    refine ⟨{
      realize := PEmpty.elim
      injective := ?_
      range := ?_
      adj := ?_
      left := ?_
      right := ?_ }⟩
    · intro x; exact x.elim
    · intro v
      constructor
      · rintro ⟨x,_⟩; exact x.elim
      · intro h; exact (occurs_nil v h).elim
    · intro x; exact x.elim
    · intro i; rfl
    · intro i; rfl
  | cons B bs ih =>
    obtain ⟨E⟩ := ih B.bag hc.tail (convex_tail hv)
    let P := piece G prev B (headBag bs)
    let Q := product G B.bag bs
    have hs : ∀ x y, Seam P Q.graph x y ↔ x.val = E.realize y :=
      seam_iff G prev B bs hc hv E
    let f : Glued P Q.graph → V :=
      glueLift P Q.graph Subtype.val E.realize (fun x y h => (hs x y).mp h)
    have hf : Function.Injective f :=
      glueLift_injective P Q.graph Subtype.val E.realize _ Subtype.val_injective
        E.injective (fun x y h => (hs x y).mpr h)
    refine ⟨{
      realize := f
      injective := hf
      range := ?_
      adj := ?_
      left := ?_
      right := ?_ }⟩
    · intro v
      change (∃ x, f x = v) ↔ Occurs (B.bag :: bs.map NamedBag.bag) v
      rw [occurs_cons]
      constructor
      · rintro ⟨z,hz⟩
        induction z using Quotient.inductionOn with | h z =>
          cases z with
          | inl x =>
            left
            change x.val = v at hz
            exact hz ▸ x.property
          | inr y =>
            right
            exact (E.range v).mp ⟨y,hz⟩
      · rintro (hvB | hvs)
        · exact ⟨inLeft P Q.graph ⟨v,hvB⟩,rfl⟩
        · obtain ⟨y,hy⟩ := (E.range v).mpr hvs
          exact ⟨inRight P Q.graph y,hy⟩
    · intro x y
      change gluedAdj P Q.graph x y ↔
        CoveredEdge G (B.bag :: bs.map NamedBag.bag) (f x) (f y)
      rw [coveredEdge_cons]
      constructor
      · rintro (⟨a,b,hab,ha,hb⟩ | ⟨a,b,hab,ha,hb⟩)
        · have hfa : a.val = f x := congrArg f ha
          have hfb : b.val = f y := congrArg f hb
          exact Or.inl ⟨hfa ▸ a.property,hfb ▸ b.property,
            hfa ▸ hfb ▸ hab⟩
        · have hfa : E.realize a = f x := congrArg f ha
          have hfb : E.realize b = f y := congrArg f hb
          exact Or.inr (hfa ▸ hfb ▸ (E.adj a b).mp hab)
      · rintro (⟨hxB,hyB,hxy⟩ | hxy)
        · let a : B.bag := ⟨f x,hxB⟩
          let b : B.bag := ⟨f y,hyB⟩
          exact Or.inl ⟨a,b,hxy,hf rfl,hf rfl⟩
        · obtain ⟨C,hC,hxC,hyC,hG⟩ := hxy
          obtain ⟨a,ha⟩ := (E.range (f x)).mpr ⟨C,hC,hxC⟩
          obtain ⟨b,hb⟩ := (E.range (f y)).mpr ⟨C,hC,hyC⟩
          refine Or.inr ⟨a,b,?_,hf ha,hf hb⟩
          apply (E.adj a b).mpr
          have hcovered : CoveredEdge G (bs.map NamedBag.bag) (f x) (f y) :=
            ⟨C,hC,hxC,hyC,hG⟩
          simpa only [ha,hb] using hcovered
    · intro i
      change ((P.left i).map (inLeft P Q.graph)).map f =
        (port B prev i).map Subtype.val
      rw [Option.map_map]
      rfl
    · intro i
      change (Q.graph.right i).map (inRight P Q.graph) = none
      rw [E.right i]
      rfl

/-- The graph carried by the product is the original graph, with both outer
interfaces empty. All data concern actual vertices, not merely torso codes. -/
structure Reconstruction (G : Original V) (P : Packed.{v} k) where
  vertex : P.Vertex ≃ V
  adj : ∀ x y, P.graph.Adj x y ↔ G.Adj (vertex x) (vertex y)
  left : ∀ i, P.graph.left i = none
  right : ∀ i, P.graph.right i = none

/-- Every supplied finite ordered path decomposition with bag bound `k` gives
an actual nonempty word of `k`-small bi-interface graphs, and an isomorphism
from their genuine quotient product to the original graph. Compatible names
and the reconstruction equivalence are both constructed, not assumed. -/
theorem exists_small_word_reconstruction (G : Original V) (D : Decomposition G k) :
    ∃ ws : List (Packed.{u} k), ws ≠ [] ∧
      (∀ P ∈ ws, Nat.card P.Vertex ≤ k) ∧
      ws.length = D.bags.length + 1 ∧ Nonempty (Reconstruction G (Packed.eval ws)) := by
  classical
  obtain ⟨ns,hns,hc⟩ := name_bag_list D.bags D.bound
  have hv : Convex (ns.map NamedBag.bag) := by rw [hns]; exact D.interval
  obtain ⟨E⟩ := evaluation_exists G ∅ ns hc hv
  have hsurj : Function.Surjective E.realize := by
    intro v
    apply (E.range v).mpr
    rw [hns]
    exact D.vertex v
  refine ⟨word G ∅ ns,word_ne_nil G ∅ ns,?_,?_,?_⟩
  · apply word_small
    intro B hB
    apply D.bound B.bag
    rw [← hns]
    exact List.mem_map.mpr ⟨B,hB,rfl⟩
  · rw [word_length, ← hns, List.length_map]
  · have heval := eval_word G ∅ ns
    rw [heval]
    refine ⟨{
      vertex := Equiv.ofBijective E.realize ⟨E.injective,hsurj⟩
      adj := ?_
      left := ?_
      right := E.right }⟩
    · intro x y
      change (product G ∅ ns).graph.Adj x y ↔ G.Adj (E.realize x) (E.realize y)
      rw [E.adj x y]
      constructor
      · rintro ⟨B,_,_,_,hxy⟩; exact hxy
      · intro hxy
        obtain ⟨B,hB,hxB,hyB⟩ := D.edge hxy
        exact ⟨B,by simpa [hns] using hB,hxB,hyB,hxy⟩
    · intro i
      apply (Option.map_eq_none_iff (f := E.realize)).mp
      rw [E.left i]
      cases ns <;> simp [headPort]

#print axioms exists_small_word_reconstruction
end StackSorting.BiInterface.PathWord
