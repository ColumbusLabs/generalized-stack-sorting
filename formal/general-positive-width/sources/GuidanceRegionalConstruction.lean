import GuidanceComponents

namespace StackSorting.GuidedPathwidth
universe u v
variable {V : Type u} {J : Type v} {G : SimpleGraph V} {P : Set V} {c : Nat}

/-- A concrete family of windows, roots and finite colors. Equal-color windows
may overlap only when they are routing to the same actual original vertex. -/
structure RegionalData (G : SimpleGraph V) (P : Set V) (c : Nat) (J : Type v) where
  window : J → Set V
  root : J → V
  color : J → Fin c
  inside : ∀ j, window j ⊆ P
  noncollision : ∀ j k, color j = color k → root j ≠ root k → Disjoint (window j) (window k)

namespace RegionalData
variable (D : RegionalData G P c J)

/-- The supports are constructed as unions of actual window-reachable root
components. Shared roots cause no ambiguity and require no extra color. -/
noncomputable def guides : System G P c := fun i => {
  support := fun r => {x | ∃ j, D.color j = i ∧ D.root j = r ∧ ReachIn G (D.window j) x r}
  inside := by
    intro r x hx
    obtain ⟨j,_,_,hj⟩ := hx
    exact D.inside j hj.1
  reaches := by
    intro r x hx
    obtain ⟨j,hji,hjr,hjx⟩ := hx
    apply (reachIn_component hjx).mono
    intro y hy
    exact ⟨j,hji,hjr,hy⟩
  unique := by
    intro r s x hr hs
    obtain ⟨j,hj,hjr,hjx⟩ := hr
    obtain ⟨k,hk,hks,hkx⟩ := hs
    by_contra hrs
    have hd := D.noncollision j k (hj.trans hk.symm) (by simpa [hjr,hks] using hrs)
    exact Set.disjoint_left.mp hd hjx.1 hkx.1 }

/-- Every actual finite route staying within one prescribed window is captured
by the guide constructed for that window's root. -/
theorem routes {j : J} {x : V} (h : ReachIn G (D.window j) x (D.root j)) :
    x ∈ (D.guides (D.color j)).support (D.root j) := ⟨j,rfl,rfl,h⟩

/-- Simultaneously route a bag from one real graph vertex, using the explicit
window witnesses. No capture predicate is postulated in RegionalData. -/
theorem captures {B : Set V} (h : B.Nonempty → ∃ x, ∀ r ∈ B,
    ∃ j, D.root j = r ∧ ReachIn G (D.window j) x r) : Captures G D.guides B := by
  intro hb
  obtain ⟨x,hx⟩ := h hb
  refine ⟨x,?_⟩
  intro r hr
  obtain ⟨j,hj,hpath⟩ := hx r hr
  exact ⟨D.color j,j,rfl,hj,hpath⟩
end RegionalData

#print axioms RegionalData.routes
end StackSorting.GuidedPathwidth
