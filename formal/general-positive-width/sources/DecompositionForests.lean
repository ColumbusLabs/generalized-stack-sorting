import GuidanceCaptureBound
import GuidanceDeletion
import GuidanceAddition

namespace StackSorting.GuidedPathwidth
open BiInterface
universe u v w
variable {V : Type u} {N : Type v} {I : Type w}

/-- Disjoint actual copies of an index forest, retaining every original node. -/
def forestCopies (T : SimpleGraph N) (I : Type w) : SimpleGraph (I × N) where
  Adj x y := x.1 = y.1 ∧ T.Adj x.2 y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2.ne rfl⟩

theorem forestCopies_support {T : SimpleGraph N} {x y : I × N}
    (p : (forestCopies T I).Walk x y) {z : I × N} (hz : z ∈ p.support) : z.1 = x.1 := by
  revert hz
  induction p with
  | @nil x =>
    intro hz
    have he : z = x := by simpa using hz
    exact congrArg Prod.fst he
  | @cons x y w hxy p ih =>
    intro hz
    simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hz
    rcases hz with rfl | hz
    · rfl
    · exact (ih hz).trans hxy.1.symm

theorem forestCopies_acyclic {T : SimpleGraph N} (hT : T.IsAcyclic) :
    (forestCopies T I).IsAcyclic := by
  intro x p hp
  let S : Set (I × N) := {y | y.1 = x.1}
  have hs : ∀ z ∈ p.support, z ∈ S := fun z hz => forestCopies_support p hz
  let q := p.induce S hs
  have hq : q.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map
      (f := (SimpleGraph.Embedding.induce (G := forestCopies T I) S).toHom)
    simpa [q] using hp
  let f : (forestCopies T I).induce S →g T := {
    toFun := fun y => y.val.2
    map_rel' := by intro a b h; exact h.2 }
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact Prod.ext (a.property.trans b.property.symm) he
  exact hT (q.map f) (hq.map hf)

/-- A genuine finite graph decomposition indexed by an actual finite forest.
Empty bags are allowed. Occurrence connectivity is an explicit finite walk. -/
structure Decomposition (G : SimpleGraph V) (P : Set V) where
  Node : Type u
  finiteNode : Finite Node
  forest : SimpleGraph Node
  acyclic : forest.IsAcyclic
  bag : Node → Set V
  inside : ∀ a, bag a ⊆ P
  vertex : ∀ x ∈ P, ∃ a, x ∈ bag a
  edge : ∀ {x y}, G.Adj x y → x ∈ P → y ∈ P → ∃ a, x ∈ bag a ∧ y ∈ bag a
  running : ∀ x a b, x ∈ bag a → x ∈ bag b →
    ReachIn forest {a | x ∈ bag a} a b
attribute [instance] Decomposition.finiteNode

/-- Bags and the real same-color rooted supports are retained together. -/
structure GuidedDecomposition (G : SimpleGraph V) (P : Set V) (c : Nat) where
  decomposition : Decomposition G P
  guides : System G P c
  captured : ∀ a, Captures G guides (decomposition.bag a)

namespace GuidedDecomposition
variable {G : SimpleGraph V} {P : Set V} {c : Nat}
theorem bag_card_le (D : GuidedDecomposition G P c) (a : D.decomposition.Node) :
    Nat.card (D.decomposition.bag a) ≤ c := capture_card_le D.guides (D.captured a)
end GuidedDecomposition

/-- Capture is hereditary in bags, without changing trees or their colors. -/
theorem captures_mono {G : SimpleGraph V} {P B B' : Set V} {c : Nat}
    (C : System G P c) (h : Captures G C B) (hsub : B' ⊆ B) : Captures G C B' := by
  intro hn
  obtain ⟨x,hx⟩ := h (hn.mono hsub)
  exact ⟨x,fun r hr => hx r (hsub hr)⟩

/-- Every captured bag lies in one actual connected component of the graph. -/
theorem captures_connected {G : SimpleGraph V} {P B : Set V} {c : Nat}
    (C : System G P c) (h : Captures G C B) {r s : V} (hr : r ∈ B) (hs : s ∈ B) :
    ReachIn G P r s := by
  obtain ⟨x,hx⟩ := h ⟨r,hr⟩
  obtain ⟨i,hi⟩ := hx r hr
  obtain ⟨j,hj⟩ := hx s hs
  exact (((C i).reaches r x hi).mono ((C i).inside r)).symm.trans
    (((C j).reaches s x hj).mono ((C j).inside s))

end StackSorting.GuidedPathwidth
