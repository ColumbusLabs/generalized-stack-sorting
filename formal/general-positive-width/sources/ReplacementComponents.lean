import ReplacementWalkProjection

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} {old : V → E → Prop} {inserted : V → F → Prop}
variable {s t : V}

/-- A component walk cannot use the deleted edge when that edge is a cutedge.
It embeds directly into the replacement using only surviving old identifiers. -/
noncomputable def embedOldNoncutWalk (removed : E) (hr : Cutedge old s t removed)
    (connected : ∀ a b, old a removed → old b removed → Nonempty (HWalk inserted a b))
    {a b : V} : HWalk (NoncutIncidence old s t) a b →
      HWalk (NoncutIncidence (ReplacementIncidence old inserted removed) s t) a b
  | .nil x => .nil x
  | .cons e hx hy tail => by
    have hne : e ≠ removed := fun h => hx.2 (h.symm ▸ hr)
    let f : {e : E // e ≠ removed} := ⟨e,hne⟩
    have hn : ¬ Cutedge (ReplacementIncidence old inserted removed) s t (.inl f) :=
      fun h => hx.2 (replacement_cutedge_old_implies removed connected f h)
    exact .cons (.inl f) ⟨hx.1,hn⟩ ⟨hy.1,hn⟩
      (embedOldNoncutWalk removed hr connected tail)

theorem old_component_survives_replacement (removed : E) (hr : Cutedge old s t removed)
    (connected : ∀ a b, old a removed → old b removed → Nonempty (HWalk inserted a b))
    {a b : V} (h : SameCutedgeComponent old s t a b) :
    SameCutedgeComponent (ReplacementIncidence old inserted removed) s t a b := by
  obtain ⟨w⟩ := h
  exact ⟨embedOldNoncutWalk removed hr connected w⟩

/-- An old component avoiding the removed edge cannot acquire an inserted
vertex through a noncutedge walk. Every traversed step remains an old noncut
step, so this proves equality of the unaffected actual component. -/
theorem unaffected_component_replacement_subset (removed : E)
    (O K : Set V) (anchor : V) (ha : old anchor removed)
    (old_support : ∀ x e, old x e → x ∈ O)
    (new_support : ∀ x f, inserted x f → x ∈ K)
    (overlap : ∀ x, x ∈ O → x ∈ K → old x removed)
    (hs : s ∈ O) (ht : t ∈ O)
    (x : V) (hx : x ∈ O)
    (avoids : ∀ y, SameCutedgeComponent old s t x y → ¬ old y removed)
    {y : V} (h : SameCutedgeComponent (ReplacementIncidence old inserted removed) s t x y) :
    SameCutedgeComponent old s t x y := by
  obtain ⟨w⟩ := h
  suffices step : ∀ {a b : V}
      (w : HWalk (NoncutIncidence (ReplacementIncidence old inserted removed) s t) a b),
      a ∈ O → SameCutedgeComponent old s t x a → SameCutedgeComponent old s t x b by
    exact step w hx (sameCutedgeComponent_refl old s t x)
  intro a b w
  induction w with
  | nil a => exact fun _ h => h
  | @cons a b c e hae hbe tail ih =>
    intro haO hxa
    cases e with
    | inl e =>
      have hn : ¬ Cutedge old s t e.val := by
        intro he
        exact hae.2 (old_cutedge_replacement removed O K anchor ha
          old_support new_support overlap hs ht e he)
      have hab := sameCutedgeComponent_of_noncut_edge old s t hae.1 hbe.1 hn
      exact ih (old_support b e.val hbe.1) (sameCutedgeComponent_trans old s t hxa hab)
    | inr f =>
      exact (avoids a hxa (overlap a haO (new_support a f hae.1))).elim

end FiniteFlow.Hypergraph
