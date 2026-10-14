import TorsoPaths
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/-! Constructive guidance supports. A connected support is converted below to
an actual spanning tree. Different roots of one color have disjoint supports.
The ambient allowed set makes vertex deletion explicit without changing names. -/
namespace StackSorting.GuidedPathwidth
open BiInterface
universe u
variable {V : Type u} (G : SimpleGraph V)

def ReachIn (S : Set V) (x y : V) : Prop :=
  x ∈ S ∧ y ∈ S ∧ Through G.Adj S x y

namespace ReachIn
variable {G} {S T : Set V} {x y z : V}
theorem refl (hx : x ∈ S) : ReachIn G S x x := ⟨hx,hx,.refl x⟩
theorem trans (h : ReachIn G S x y) (h' : ReachIn G S y z) : ReachIn G S x z :=
  ⟨h.1,h'.2.1,.join h.2.2 h.2.1 h'.2.2⟩
theorem symm (h : ReachIn G S x y) : ReachIn G S y x :=
  ⟨h.2.1,h.1,h.2.2.reverse (fun _ _ h => G.adj_symm h)⟩
theorem mono (h : ReachIn G S x y) (hST : S ⊆ T) : ReachIn G T x y :=
  ⟨hST h.1,hST h.2.1,h.2.2.mono (fun _ _ h => h) hST⟩

/-- A restricted finite walk is an ordinary walk of the actual induced graph. -/
theorem induced (h : ReachIn G S x y) :
    Nonempty ((G.induce S).Walk ⟨x,h.1⟩ ⟨y,h.2.1⟩) := by
  rcases h with ⟨hx,hy,h⟩
  revert hx hy
  induction h with
  | refl => intro hx hy; exact ⟨.nil⟩
  | @edge a b h =>
    intro hx hy
    exact ⟨.cons (show (G.induce S).Adj ⟨a,hx⟩ ⟨b,hy⟩ from h) .nil⟩
  | @join a b c hab hb hbc ihab ihbc =>
    intro hx hy
    obtain ⟨p⟩ := ihab hx hb
    obtain ⟨q⟩ := ihbc hb hy
    exact ⟨p.append q⟩
end ReachIn

/-- One color, with a possibly empty connected support for each possible root.
Each nonempty support is witnessed by finite walks in that support. -/
structure Color (P : Set V) where
  support : V → Set V
  inside : ∀ r, support r ⊆ P
  reaches : ∀ r x, x ∈ support r → ReachIn G (support r) x r
  unique : ∀ r s x, x ∈ support r → x ∈ support s → r = s

namespace Color
variable {G} {P Q : Set V} (C : Color G P)
theorem root_mem {r x : V} (hx : x ∈ C.support r) : r ∈ C.support r :=
  (C.reaches r x hx).2.1

theorem connected {r : V} (hr : r ∈ C.support r) :
    (G.induce (C.support r)).Connected := by
  let : Nonempty (C.support r) := ⟨⟨r,hr⟩⟩
  refine ⟨?_⟩
  intro x y
  exact ((C.reaches r x x.property).trans
    (C.reaches r y y.property).symm).induced

/-- Actual acyclic spanning tree on every nonempty guide support. Its edges
are original graph edges, and its root is the specified original vertex. -/
theorem exists_tree {r x : V} (hx : x ∈ C.support r) :
    ∃ T : SimpleGraph (C.support r), T ≤ G.induce (C.support r) ∧ T.IsTree := by
  exact (C.connected (C.root_mem hx)).exists_isTree_le

/-- Enlarging the allowed vertex set changes no guide or root. -/
def enlarge (hPQ : P ⊆ Q) : Color G Q where
  support := C.support
  inside := fun r => (C.inside r).trans hPQ
  reaches := C.reaches
  unique := C.unique

/-- The empty color is valid even in an empty ambient graph. -/
def empty (G : SimpleGraph V) (P : Set V) : Color G P where
  support := fun _ => ∅
  inside := by simp
  reaches := by simp
  unique := by simp
end Color

abbrev System (P : Set V) (c : Nat) := Fin c → Color G P

def Captures {P : Set V} {c : Nat} (C : System G P c) (B : Set V) : Prop :=
  B.Nonempty → ∃ x, ∀ r ∈ B, ∃ i, x ∈ (C i).support r

/-- An empty bag is harmless, including on an empty graph. -/
theorem captures_empty {P : Set V} {c : Nat} (C : System G P c) : Captures G C ∅ := by
  intro h
  exact h.ne_empty rfl |>.elim

/-- Genuine capture forces every bag vertex to be an allowed graph vertex. -/
theorem captures_subset {P : Set V} {c : Nat} (C : System G P c) {B : Set V}
    (h : Captures G C B) : B ⊆ P := by
  intro r hr
  obtain ⟨x,hx⟩ := h ⟨r,hr⟩
  obtain ⟨i,hi⟩ := hx r hr
  exact (C i).inside r ((C i).root_mem hi)

#print axioms Color.exists_tree
end StackSorting.GuidedPathwidth
