import RootedForestPathExtraction
import FiniteIndexTreeAdapter

namespace StackSorting.ConnectedConeNormalization
open GraphWidth SameVertexForest
variable {n : Nat} {α : Type}

def LiftLink (O : RankedOrder n) (f : Fin n → α) (x y : α) : Prop :=
  ∃ u v, x = f u ∧ y = f v ∧ ParentAdj O u v

def LiftRoot (O : RankedOrder n) (f : Fin n → α) (x : α) : Prop :=
  ∃ u, x = f u ∧ O.parent u = u

/-- Extra incidence elements cannot enter a selected-forest walk: every
selected link has endpoints in the retained original-vertex embedding. -/
theorem lift_walk_iff (O : RankedOrder n) (f : Fin n → α) (hf : Function.Injective f)
    (P : α → Prop) (u v : Fin n) :
    Walk (LiftLink O f) P (f u) (f v) ↔ Walk (ParentAdj O) (fun z => P (f z)) u v := by
  constructor
  · have descend : ∀ {x y}, Walk (LiftLink O f) P x y →
        ∀ a b, x = f a → y = f b → Walk (ParentAdj O) (fun z => P (f z)) a b := by
      intro x y p
      induction p with
      | refl hp =>
        intro a b ha hb
        have he : a = b := hf (ha.symm.trans hb)
        subst b
        exact .refl (ha ▸ hp)
      | @step x z y hp hxz tail ih =>
        intro a b ha hb
        obtain ⟨c,d,hxc,hzd,hcd⟩ := hxz
        have he : c = a := hf (hxc.symm.trans ha)
        subst c
        exact .step (ha ▸ hp) hcd (ih d b hzd hb)
    intro p
    exact descend p u v rfl rfl
  · intro p
    exact IndexTreeAdapter.map_guarded f
      (fun a b h => ⟨a,b,rfl,rfl,h⟩) (fun _ h => h) p

theorem lifted_rootSeparator_iff (O : RankedOrder n) (f : Fin n → α)
    (hf : Function.Injective f) (x y : Fin n) :
    (∀ r, LiftRoot O f r → Walk (LiftLink O f) (fun _ => True) (f y) r →
      ¬ Walk (LiftLink O f) (fun z => z ≠ f x) (f y) r) ↔ Cone O x y := by
  rw [← rootSeparator_iff O x y]
  constructor
  · intro h r hr hp havoid
    apply h (f r) ⟨r,rfl,hr⟩ ((lift_walk_iff O f hf _ _ _).mpr hp)
    apply (lift_walk_iff O f hf _ _ _).mpr
    exact havoid.mono (fun z hz he => hz (hf he))
  · intro h r hroot hp havoid
    obtain ⟨r,rfl,hr⟩ := hroot
    apply h r hr ((lift_walk_iff O f hf _ _ _).mp hp)
    exact ((lift_walk_iff O f hf _ _ _).mp havoid).mono
      (fun z hz he => hz (congrArg f he))

#print axioms lift_walk_iff
#print axioms lifted_rootSeparator_iff
end StackSorting.ConnectedConeNormalization
