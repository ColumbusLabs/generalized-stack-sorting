import DecompositionIntroduction
import Mathlib.Data.Finset.Max

namespace StackSorting.GraphWidth.Nested
open FinitePort
variable {n t : Nat} {G : Graph n} {T : RootedTree t}

/-- A clique uses the actual underlying graph adjacency. -/
def Clique (G : Graph n) (A : Finset (Fin n)) : Prop :=
  ∀ u ∈ A, ∀ v ∈ A, u ≠ v → G.Adj u v

def Covers (D : Decomposition G T) (A : Finset (Fin n)) (x : Fin t) : Prop :=
  ∀ v ∈ A, v ∈ D.bag x

/-- The attachment bag is root-nearest among all covering bags. There may
be many covering bags; no uniqueness of the covering bag is assumed. -/
def RootNearest (D : Decomposition G T) (A : Finset (Fin n)) (x : Fin t) : Prop :=
  Covers D A x ∧ ∀ y, Covers D A y → Ancestor T x y

@[simp] theorem covers_empty (D : Decomposition G T) (x : Fin t) : Covers D ∅ x := by
  intro v hv
  simp at hv

/-- Every nonempty actual clique has a covering bag above every other
covering bag, constructed using the greatest introduction index in the clique. -/
theorem exists_rootNearest (D : Decomposition G T) (A : Finset (Fin n))
    (hA : A.Nonempty) (hcl : Clique G A) : ∃ x, RootNearest D A x := by
  classical
  obtain ⟨a,ha,hm⟩ := A.exists_max_image (fun v => (introductionNode D v).val) hA
  refine ⟨introductionNode D a,?_,?_⟩
  · intro u hu
    by_cases he : u=a
    · subst u; exact (introduction_spec D a).1
    · have hadj := hcl u hu a ha he
      have hanc : Ancestor T (introductionNode D u) (introductionNode D a) := by
        rcases edge_introductions_comparable D hadj with h | h
        · exact h
        · have eq : introductionNode D u = introductionNode D a :=
            Fin.ext (Nat.le_antisymm (hm u hu) h.val_le)
          rw [eq]
          exact .refl _
      exact frontier_mem_introduction_bag D hanc (.refl _) hadj
  · intro y hy
    exact introduction_ancestor D (hy a ha)

theorem rootNearest_unique (D : Decomposition G T) (A : Finset (Fin n))
    {x y : Fin t} (hx : RootNearest D A x) (hy : RootNearest D A y) : x=y :=
  TreeAncestry.antisymm (hx.2 y hy.1) (hy.2 x hx.1)

theorem exists_unique_rootNearest (D : Decomposition G T) (A : Finset (Fin n))
    (hA : A.Nonempty) (hcl : Clique G A) : ∃! x, RootNearest D A x := by
  obtain ⟨x,hx⟩ := exists_rootNearest D A hA hcl
  exact ⟨x,hx,fun y hy => rootNearest_unique D A hy hx⟩

/-- An actual parent-chain walk through every interval-closed predicate. -/
theorem ancestor_chain_walk {a b : Fin t} (h : Ancestor T a b)
    {P : Fin t → Prop} (hP : ∀ x, Ancestor T a x → Ancestor T x b → P x) :
    Walk (TreeAdj T) P a b := by
  induction h with
  | refl => exact .refl (hP a (.refl _) (.refl _))
  | @step v hv hap ih =>
    have hp : Walk (TreeAdj T) P a (T.parent v) :=
      ih (fun x hax hxp => hP x hax (.step hv hxp))
    exact hp.trans (.step (hP _ hap (.step hv (.refl _)))
      (Or.inr ⟨hv,rfl⟩) (.refl (hP v (.step hv hap) (.refl _))))

/-- All bags containing a nonempty clique form an actual connected subtree. -/
theorem clique_cover_connected (D : Decomposition G T) (A : Finset (Fin n))
    (hA : A.Nonempty) (hcl : Clique G A) {x y : Fin t}
    (hx : Covers D A x) (hy : Covers D A y) :
    Walk (TreeAdj T) (Covers D A) x y := by
  obtain ⟨r,hr⟩ := exists_rootNearest D A hA hcl
  have fromRoot : ∀ z, Covers D A z → Walk (TreeAdj T) (Covers D A) r z := by
    intro z hz
    apply ancestor_chain_walk (hr.2 z hz)
    intro i hri hiz u hu
    exact TreeAncestry.walk_convex (T := T) (P := fun j => u ∈ D.bag j)
      (x := r) (a := i) (y := z) (D.running (hr.1 u hu) (hz u hu)) hri hiz
  exact ((fromRoot x hx).reverse (treeAdj_symm T)).trans (fromRoot y hy)

/-- Local root/parent noncoverage characterizes the exact root-nearest
attachment. This can be expressed by the literal bag and parent predicates. -/
theorem rootNearest_iff_parent_not_cover (D : Decomposition G T)
    (A : Finset (Fin n)) (hA : A.Nonempty) (hcl : Clique G A) (x : Fin t) :
    RootNearest D A x ↔ Covers D A x ∧ (x.val=0 ∨ ¬ Covers D A (T.parent x)) := by
  constructor
  · intro hx
    refine ⟨hx.1,?_⟩
    by_cases hz : x.val=0
    · exact Or.inl hz
    · right
      intro hp
      have hle := (hx.2 _ hp).val_le
      have hlt := T.parent_lt x hz
      omega
  · rintro ⟨hx,hp⟩
    obtain ⟨r,hr⟩ := exists_rootNearest D A hA hcl
    have hrx := hr.2 x hx
    have heq : r=x := by
      by_contra hn
      have hz := hrx.ne_zero_of_strict hn
      have hpc : Covers D A (T.parent x) := by
        intro u hu
        exact TreeAncestry.walk_convex (T := T) (P := fun j => u ∈ D.bag j)
          (x := r) (a := T.parent x) (y := x)
          (D.running (hr.1 u hu) (hx u hu))
          (hrx.parent_of_ne hn) (.step hz (.refl _))
      rcases hp with h | h
      · exact hz h
      · exact h hpc
    simpa only [heq] using hr

#print axioms exists_unique_rootNearest
#print axioms clique_cover_connected
#print axioms rootNearest_iff_parent_not_cover
end StackSorting.GraphWidth.Nested
