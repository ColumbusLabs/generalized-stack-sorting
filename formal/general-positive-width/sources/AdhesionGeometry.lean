import DecompositionIntroduction
import GuidanceForestRealization
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

namespace StackSorting.AdhesionGuidance
open GraphWidth FinitePort
attribute [local instance] Classical.propDecidable
variable {n t : Nat} {G : Graph n} {T : RootedTree t}

/-- Original edge adapter; no completion edges are introduced. -/
def originalGraph (G : Graph n) : SimpleGraph (Fin n) where
  Adj := G.Adj
  symm := ⟨fun _ _ h => G.symm h⟩
  loopless := ⟨G.loopless⟩

def adhesion (D : Decomposition G T) (x : Fin t) : Set (Fin n) :=
  {v | x.val ≠ 0 ∧ v ∈ D.bag x ∧ v ∈ D.bag (T.parent x)}

def margin (D : Decomposition G T) (x : Fin t) : Set (Fin n) :=
  {v | v ∈ D.bag x ∧ v ∉ adhesion D x}

/-- The ordinary union-of-descendant-bags minus the adhesion. -/
def component (D : Decomposition G T) (x : Fin t) : Set (Fin n) :=
  {v | (∃ z, Ancestor T x z ∧ v ∈ D.bag z) ∧ v ∉ adhesion D x}

theorem adhesion_introduction (D : Decomposition G T) {x v}
    (h : v ∈ adhesion D x) :
    Ancestor T (introductionNode D v) x ∧ introductionNode D v ≠ x := by
  refine ⟨introduction_ancestor D h.2.1, ?_⟩
  intro he
  have hi := (introduction_ancestor D h.2.2).val_le
  rw [he] at hi
  have hp := T.parent_lt x h.1
  omega

theorem component_iff (D : Decomposition G T) (x v) :
    v ∈ component D x ↔ Ancestor T x (introductionNode D v) := by
  constructor
  · rintro ⟨⟨z,hxz,hvz⟩,hn⟩
    rcases TreeAncestry.comparable hxz (introduction_ancestor D hvz) with h | h
    · exact h
    · by_cases he : introductionNode D v = x
      · rw [he]; exact .refl _
      · have hp := h.parent_of_ne he
        have hnzero : x.val ≠ 0 := by
          intro hz
          have hi := h.val_le
          have heq : introductionNode D v = x := Fin.ext (by omega)
          exact he heq
        apply False.elim
        apply hn
        refine ⟨hnzero, ?_, ?_⟩
        · exact TreeAncestry.walk_convex (T := T) (P := fun i => v ∈ D.bag i)
            (D.running (introduction_spec D v).1 hvz) h hxz
        · exact TreeAncestry.walk_convex (T := T) (P := fun i => v ∈ D.bag i)
            (D.running (introduction_spec D v).1 hvz) hp
            ((Ancestor.step hnzero (.refl _)).trans hxz)
  · intro h
    refine ⟨⟨introductionNode D v,h,(introduction_spec D v).1⟩,?_⟩
    intro ha
    obtain ⟨hi,hne⟩ := adhesion_introduction D ha
    exact hne (TreeAncestry.antisymm hi h)

theorem introduction_component (D : Decomposition G T) (v) :
    v ∈ component D (introductionNode D v) :=
  (component_iff D _ _).mpr (.refl _)

theorem margin_component (D : Decomposition G T) {x v}
    (h : v ∈ margin D x) : v ∈ component D x :=
  ⟨⟨x,.refl _,h.1⟩,h.2⟩

theorem component_comparable (D : Decomposition G T) {x y v}
    (hx : v ∈ component D x) (hy : v ∈ component D y) :
    Ancestor T x y ∨ Ancestor T y x :=
  TreeAncestry.comparable ((component_iff D _ _).mp hx)
    ((component_iff D _ _).mp hy)

/-- A finite index retains multiplicities across different base nodes. -/
abbrev Index (D : Decomposition G T) :=
  {p : Fin t × Fin n // p.2 ∈ adhesion D p.1}

structure Paths (D : Decomposition G T) where
  representative : Fin t → Fin n
  representative_mem : ∀ x, representative x ∈ margin D x
  walk : ∀ i : Index D, (originalGraph G).Walk (representative i.val.1) i.val.2
  contained : ∀ i v, v ∈ (walk i).support → v ≠ i.val.2 → v ∈ component D i.val.1

namespace Paths
variable {D : Decomposition G T} (P : Paths D)

def Conflict (i j : Index D) : Prop :=
  i.val.2 ≠ j.val.2 ∧ ∃ v, v ∈ (P.walk i).support ∧ v ∈ (P.walk j).support

theorem conflict_symm {i j} (h : P.Conflict i j) : P.Conflict j i :=
  ⟨h.1.symm, by obtain ⟨v,hi,hj⟩ := h.2; exact ⟨v,hj,hi⟩⟩

/-- The literal finite conflict graph on indexed original-edge walks. -/
def conflictGraph : SimpleGraph (Index D) where
  Adj := P.Conflict
  symm := ⟨fun _ _ h => P.conflict_symm h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem conflict_comparable {i j} (h : P.Conflict i j) :
    Ancestor T i.val.1 j.val.1 ∨ Ancestor T j.val.1 i.val.1 := by
  obtain ⟨hne,v,hi,hj⟩ := h
  by_cases hei : v = i.val.2
  · subst v
    have hc := (component_iff D _ _).mp (P.contained j _ hj hne)
    exact Or.inr (hc.trans (adhesion_introduction D i.property).1)
  · by_cases hej : v = j.val.2
    · subst v
      have hc := (component_iff D _ _).mp (P.contained i _ hi hei)
      exact Or.inl (hc.trans (adhesion_introduction D j.property).1)
    · exact component_comparable D (P.contained i _ hi hei) (P.contained j _ hj hej)

noncomputable def based (x : Fin t) : Finset (Index D) := by
  classical
  exact Finset.univ.filter (fun i => i.val.1 = x)

/-- Each base fiber is bijective to the actual adhesion, with different
bases retaining separate copies of repeated targets. -/
theorem based_card (x : Fin t) :
    (based (D := D) x).card = ((adhesion D x).toFinset).card := by
  classical
  apply Finset.card_bij (fun i _ => i.val.2)
  · intro i hi
    have he : i.val.1 = x := (Finset.mem_filter.mp hi).2
    simpa only [Set.mem_toFinset,← he] using i.property
  · intro i hi j hj he
    apply Subtype.ext
    apply Prod.ext
    · exact ((Finset.mem_filter.mp hi).2).trans ((Finset.mem_filter.mp hj).2).symm
    · exact he
  · intro v hv
    have hv' : v ∈ adhesion D x := Set.mem_toFinset.mp hv
    exact ⟨⟨(x,v),hv'⟩,by simp [based],rfl⟩

noncomputable def load (x : Fin t) : Finset (Index D) := by
  classical
  exact Finset.univ.filter (fun i => Ancestor T i.val.1 x ∧ i.val.1 ≠ x ∧
    ∃ v, v ∈ (P.walk i).support ∧ v ∈ component D x)

/-- No coloring or intersection-degree bound is supplied by this input. -/
def Bounded (k L : Nat) : Prop :=
  (∀ x, (based (D := D) x).card ≤ k) ∧ ∀ x, (P.load x).card ≤ L

end Paths
end StackSorting.AdhesionGuidance
