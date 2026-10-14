import ReplacementComponents

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} {old : V → E → Prop} {inserted : V → F → Prop}
variable {s t : V}

/-- An unaffected component is exactly preserved, including all vertex names.
The hypothesis describes the old actual component, not an assumed replacement
component correspondence. Both directions are constructed from finite walks. -/
theorem unaffected_component_replacement_iff (removed : E)
    (hr : Cutedge old s t removed)
    (O K : Set V) (anchor : V) (ha : old anchor removed)
    (old_support : ∀ x e, old x e → x ∈ O)
    (new_support : ∀ x f, inserted x f → x ∈ K)
    (overlap : ∀ x, x ∈ O → x ∈ K → old x removed)
    (connected : ∀ a b, old a removed → old b removed → Nonempty (HWalk inserted a b))
    (hs : s ∈ O) (ht : t ∈ O) (x : V) (hx : x ∈ O)
    (avoids : ∀ y, SameCutedgeComponent old s t x y → ¬ old y removed)
    (y : V) :
    SameCutedgeComponent (ReplacementIncidence old inserted removed) s t x y ↔
      SameCutedgeComponent old s t x y :=
  ⟨unaffected_component_replacement_subset removed O K anchor ha old_support
      new_support overlap hs ht x hx avoids,
    old_component_survives_replacement removed hr connected⟩

/-- Every enlargement of an old component occurs at the removed edge.
This is an actual vertex-level localization of the replacement surgery. -/
theorem replacement_component_enlargement_touches_removed (removed : E)
    (O K : Set V) (anchor : V) (ha : old anchor removed)
    (old_support : ∀ x e, old x e → x ∈ O)
    (new_support : ∀ x f, inserted x f → x ∈ K)
    (overlap : ∀ x, x ∈ O → x ∈ K → old x removed)
    (hs : s ∈ O) (ht : t ∈ O) (x : V) (hx : x ∈ O)
    {y : V}
    (h : SameCutedgeComponent (ReplacementIncidence old inserted removed) s t x y)
    (not_old : ¬ SameCutedgeComponent old s t x y) :
    ∃ z, SameCutedgeComponent old s t x z ∧ old z removed := by
  classical
  by_contra hn
  push Not at hn
  exact not_old (unaffected_component_replacement_subset removed O K anchor ha
    old_support new_support overlap hs ht x hx hn h)

/-- Old component walks stay inside the old supported vertex set. -/
theorem old_component_supported (O : Set V)
    (support : ∀ x e, old x e → x ∈ O) {x y : V}
    (hx : x ∈ O) (h : SameCutedgeComponent old s t x y) : y ∈ O := by
  obtain ⟨w⟩ := h
  revert hx
  induction w with
  | nil => exact fun hx => hx
  | cons e hae hbe tail ih =>
    intro _
    exact ih (support _ _ hbe.1)

/-- An unchanged old component cannot even touch an inserted hyperedge. This
supplies the negative boundary condition needed for unchanged bridges and
appendices, and is stronger than mere preservation of old connectivity. -/
theorem unaffected_component_no_inserted_touch (removed : E)
    (O K : Set V) (anchor : V) (ha : old anchor removed)
    (old_support : ∀ x e, old x e → x ∈ O)
    (new_support : ∀ x f, inserted x f → x ∈ K)
    (overlap : ∀ x, x ∈ O → x ∈ K → old x removed)
    (hs : s ∈ O) (ht : t ∈ O) (x : V) (hx : x ∈ O)
    (avoids : ∀ y, SameCutedgeComponent old s t x y → ¬ old y removed)
    (f : F) :
    ¬ ComponentTouches (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) x (.cut (.inr f)) := by
  rintro ⟨y, hy, hxy⟩
  have hold := unaffected_component_replacement_subset removed O K anchor ha
    old_support new_support overlap hs ht x hx avoids hxy
  exact avoids y hold (overlap y (old_component_supported O old_support hx hold)
    (new_support y f hy))

/-- Touching every surviving old edge is invariant for unaffected components. -/
theorem unaffected_old_boundary_touch_iff (removed : E)
    (hr : Cutedge old s t removed)
    (O K : Set V) (anchor : V) (ha : old anchor removed)
    (old_support : ∀ x e, old x e → x ∈ O)
    (new_support : ∀ x f, inserted x f → x ∈ K)
    (overlap : ∀ x, x ∈ O → x ∈ K → old x removed)
    (connected : ∀ a b, old a removed → old b removed → Nonempty (HWalk inserted a b))
    (hs : s ∈ O) (ht : t ∈ O) (x : V) (hx : x ∈ O)
    (avoids : ∀ y, SameCutedgeComponent old s t x y → ¬ old y removed)
    (f : {e : E // e ≠ removed}) :
    ComponentTouches (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) x (.cut (.inl f)) ↔
    ComponentTouches (inc := old) (s := s) (t := t) x (.cut f.val) := by
  have hcomp := unaffected_component_replacement_iff removed hr O K anchor ha
    old_support new_support overlap connected hs ht x hx avoids
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, (hcomp y).mp hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, (hcomp y).mpr hxy⟩

end FiniteFlow.Hypergraph
