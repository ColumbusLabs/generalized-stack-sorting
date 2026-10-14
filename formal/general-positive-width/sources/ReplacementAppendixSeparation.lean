import ReplacementBoundaryNeighbors

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} {inc : V → E → Prop} {s t : V}

/-- An appendix cannot be left along a walk that avoids its sole cutedge. -/
theorem appendix_walk_avoiding_stays {e : E} {x y : V}
    (hx : AppendixRegion (inc := inc) (s := s) (t := t) e x)
    (w : HWalk inc x y) (he : e ∉ w.edges) : SameCutedgeComponent inc s t x y := by
  classical
  suffices step : ∀ {a b : V} (q : HWalk inc a b), e ∉ q.edges →
      SameCutedgeComponent inc s t x a → SameCutedgeComponent inc s t x b by
    exact step w he (sameCutedgeComponent_refl inc s t x)
  intro a b q
  induction q with
  | nil => exact fun _ h => h
  | @cons a b c f ha hb tail ih =>
    intro hn hxa
    have hnf : ¬ Cutedge inc s t f := by
      intro hf
      have hfe := (hx (.cut f) hf).mp ⟨a,ha,hxa⟩
      have hEq : f = e := CutBoundary.cut.inj hfe
      exact hn (by simp [HWalk.edges,hEq])
    exact ih (fun hm => hn (by simp [HWalk.edges,hm]))
      (sameCutedgeComponent_trans inc s t hxa
        (sameCutedgeComponent_of_noncut_edge inc s t ha hb hnf))

theorem appendix_avoiding_source_impossible {e : E} {x : V}
    (hx : AppendixRegion (inc := inc) (s := s) (t := t) e x)
    (w : HWalk inc x s) (he : e ∉ w.edges) : False := by
  have bad := (hx .source trivial).mp (appendix_walk_avoiding_stays hx w he)
  cases bad

theorem appendix_avoiding_sink_impossible {e : E} {x : V}
    (hx : AppendixRegion (inc := inc) (s := s) (t := t) e x)
    (w : HWalk inc x t) (he : e ∉ w.edges) : False := by
  have bad := (hx .sink trivial).mp (appendix_walk_avoiding_stays hx w he)
  cases bad

namespace ReplacementFrame
variable [DecidableEq E] {old : V → E → Prop} {inserted : V → F → Prop} {removed : E}

/-- A new appendix at a surviving old cutedge cannot meet the inserted network,
provided every inserted vertex has an actual inserted walk to the old anchor.
This is the ordinary connected replacement premise, stated explicitly. -/
theorem surviving_appendix_avoids_inserted
    (R : ReplacementFrame old inserted s t removed) (p : Path old s t)
    (new_to_anchor : ∀ x ∈ R.newVertices, Nonempty (HWalk inserted x R.anchor))
    (e : E) (he : Cutedge old s t e) (hne : e ≠ removed)
    (x : V) (hx : x ∈ R.newVertices)
    (hregion : AppendixRegion (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) (.inl ⟨e,hne⟩) x) : False := by
  classical
  let f : {e : E // e ≠ removed} := ⟨e,hne⟩
  obtain ⟨w⟩ := new_to_anchor x hx
  let q := w.mapEdges (inc := inserted) (inc' := ReplacementIncidence old inserted removed) Sum.inr (fun _ _ h => h)
  have havoid : Sum.inl f ∉ q.edges := by
    change Sum.inl f ∉ (w.mapEdges (inc := inserted) (inc' := ReplacementIncidence old inserted removed) Sum.inr (fun _ _ h => h)).edges
    rw [HWalk.edges_mapEdges (inc := inserted) (inc' := ReplacementIncidence old inserted removed) Sum.inr (fun _ _ h => h)]
    simp
  have hxa := appendix_walk_avoiding_stays hregion q havoid
  have ha : AppendixRegion (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) (.inl f) R.anchor := by
    intro b hb
    exact (componentTouches_congr hxa b).symm.trans (hregion b hb)
  have hidx : p.walk.edges.idxOf removed ≠ p.walk.edges.idxOf e := by
    intro hh
    exact hne ((List.idxOf_inj (R.removed_cutedge p)).mp hh).symm
  rcases lt_or_gt_of_ne hidx with hlt | hgt
  · obtain ⟨pre,hpre⟩ := earlier_incidence_prefix p R.removed_cutedge he hlt R.anchor_incident
    let lifted := liftReplacement removed R.inserted_connects pre.reverse
    have hn : Sum.inl f ∉ lifted.edges := by
      intro hm
      have hem := (liftReplacement_old_mem removed R.inserted_connects pre.reverse f).mp hm
      exact hpre (by simpa using hem)
    exact appendix_avoiding_source_impossible ha lifted hn
  · obtain ⟨suf,hsuf⟩ := later_incidence_suffix p he R.removed_cutedge hgt R.anchor_incident
    let lifted := liftReplacement removed R.inserted_connects suf
    have hn : Sum.inl f ∉ lifted.edges := by
      intro hm
      exact hsuf ((liftReplacement_old_mem removed R.inserted_connects suf f).mp hm)
    exact appendix_avoiding_sink_impossible ha lifted hn

end ReplacementFrame
end FiniteFlow.Hypergraph
