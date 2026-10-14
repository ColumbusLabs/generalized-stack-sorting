import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace StackSorting.BiInterface

/-- Finite walks whose internal vertices lie in I. The reflexive constructor
is retained for reachability; torso adjacency will additionally require distinct
endpoints. Thus this relation does not confuse adjacency with identity. -/
inductive Through {V : Type*} (R : V → V → Prop) (I : Set V) : V → V → Prop
  | refl (x) : Through R I x x
  | edge {x y} : R x y → Through R I x y
  | join {x y z} : Through R I x y → y ∈ I → Through R I y z → Through R I x z

namespace Through
variable {V : Type*} {R Q : V → V → Prop} {I J : Set V} {x y z : V}

theorem mono (h : Through R I x y) (hR : ∀ a b, R a b → Q a b)
    (hI : I ⊆ J) : Through Q J x y := by
  induction h with
  | refl a => exact .refl a
  | edge h => exact .edge (hR _ _ h)
  | join _ hm _ ih₁ ih₂ => exact .join ih₁ (hI hm) ih₂

theorem map {W : Type*} {Q : W → W → Prop} {J : Set W}
    (f : V → W) (h : Through R I x y)
    (hR : ∀ a b, R a b → Q (f a) (f b))
    (hI : ∀ a, a ∈ I → f a ∈ J) : Through Q J (f x) (f y) := by
  induction h with
  | refl a => exact .refl (f a)
  | edge h => exact .edge (hR _ _ h)
  | join _ hm _ ih₁ ih₂ => exact .join ih₁ (hI _ hm) ih₂

theorem reverse (h : Through R I x y) (hs : ∀ a b, R a b → R b a) :
    Through R I y x := by
  induction h with
  | refl a => exact .refl a
  | edge h => exact .edge (hs _ _ h)
  | join _ hm _ ih₁ ih₂ => exact .join ih₂ hm ih₁

private theorem nested_prepend (p : Through R I x y) (hy : y ∈ I)
    (q : Through (Through R I) J y z) : Through (Through R I) J x z := by
  induction q with
  | refl => exact .edge p
  | edge h => exact .edge (.join p hy h)
  | join _ hm q ih₁ _ => exact .join (ih₁ p hy) hm q

private theorem nested_join (p : Through (Through R I) J x y)
    (hy : y ∈ I) (q : Through (Through R I) J y z) :
    Through (Through R I) J x z := by
  induction p with
  | refl => exact q
  | edge h => exact nested_prepend h hy q
  | join p hm _ _ ih₂ => exact .join p hm (ih₂ hy q)

/-- Eliminating internal vertices in two stages equals eliminating their union.
This is the torso compositionality law at the actual finite-walk level. -/
theorem eliminate_union :
    Through (Through R I) J x y ↔ Through R (I ∪ J) x y := by
  constructor
  · intro h
    induction h with
    | refl a => exact .refl a
    | edge h => exact h.mono (by intros; assumption) Set.subset_union_left
    | join _ hm _ ih₁ ih₂ => exact .join ih₁ (Or.inr hm) ih₂
  · intro h
    induction h with
    | refl a => exact .refl a
    | edge h => exact .edge (.edge h)
    | join _ hm _ ih₁ ih₂ =>
      rcases hm with hi | hj
      · exact nested_join ih₁ hi ih₂
      · exact .join ih₁ hj ih₂

/-- Nested torsos have precisely the original interface-avoiding paths. -/
theorem eliminate_subset (hJI : J ⊆ I) :
    Through (Through R J) I x y ↔ Through R I x y := by
  rw [eliminate_union, Set.union_eq_self_of_subset_left hJI]

theorem through_empty : Through R ∅ x y ↔ x = y ∨ R x y := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | edge h => exact Or.inr h
    | join _ hm _ _ _ => exact hm.elim
  · rintro (rfl | h)
    · exact .refl _
    · exact .edge h

/-- Different vertices on a path through a retained interface need not be
adjacent in its torso. This definition keeps the internal-vertex restriction. -/
def TorsoAdj (R : V → V → Prop) (boundary : Set V) (x y : V) : Prop :=
  x ≠ y ∧ x ∈ boundary ∧ y ∈ boundary ∧ Through R boundaryᶜ x y

end Through
end StackSorting.BiInterface
