import CutedgeComponents
import CutedgeOrder

namespace FiniteFlow.Hypergraph

variable {V E : Type*} {inc : V → E → Prop} {s t : V}

/-- A component cannot join opposite sides of an unavoidable edge. -/
theorem component_cannot_bypass {e : E} (he : Cutedge inc s t e)
    {a b : V} (pre : HWalk inc s a) (suffix : HWalk inc b t)
    (hp : e ∉ pre.edges) (hq : e ∉ suffix.edges)
    (h : SameCutedgeComponent inc s t a b) : False :=
  cutedge_split_separates inc s t he pre suffix hp hq h

/-- Every vertex of an earlier edge can be reached before a later cutedge. -/
theorem earlier_incidence_prefix [DecidableEq E] (p : Path inc s t)
    {e f : E} (he : Cutedge inc s t e) (_hf : Cutedge inc s t f)
    (hlt : p.walk.edges.idxOf e < p.walk.edges.idxOf f)
    {x : V} (hx : inc x e) :
    ∃ w : HWalk inc s x, f ∉ w.edges := by
  obtain ⟨a, b, pre, suffix, ha, _, hp, hpe, _, _, _⟩ :=
    p.walk.split_at_edge_nodup p.edges_nodup (he p)
  have hne : f ≠ e := by
    intro h
    subst f
    exact Nat.lt_irrefl _ hlt
  have hnot : f ∉ pre.edges := by
    intro hm
    have hh := (mem_pre_iff_idxOf_lt pre.edges suffix.edges f e hpe).mp hm
    rw [← hp] at hh
    exact Nat.lt_asymm hlt hh
  refine ⟨pre.append (.cons e ha hx (.nil x)), ?_⟩
  simpa only [HWalk.edges_append, HWalk.edges, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] using
    (show ¬ (f ∈ pre.edges ∨ f = e) from fun h => h.elim hnot hne)

/-- Every vertex of a later edge can reach the sink after an earlier cutedge. -/
theorem later_incidence_suffix [DecidableEq E] (p : Path inc s t)
    {e f : E} (_he : Cutedge inc s t e) (hf : Cutedge inc s t f)
    (hlt : p.walk.edges.idxOf e < p.walk.edges.idxOf f)
    {x : V} (hx : inc x f) :
    ∃ w : HWalk inc x t, e ∉ w.edges := by
  obtain ⟨a, b, pre, suffix, _, hb, hp, hpf, _, _, _⟩ :=
    p.walk.split_at_edge_nodup p.edges_nodup (hf p)
  have hem : e ∈ pre.edges := by
    apply (mem_pre_iff_idxOf_lt pre.edges suffix.edges e f hpf).mpr
    simpa only [← hp] using hlt
  have hall : (pre.edges ++ f :: suffix.edges).Nodup := hp ▸ p.edges_nodup
  have hnot : e ∉ f :: suffix.edges := by
    intro hm
    exact (List.pairwise_append.mp hall).2.2 e hem e hm rfl
  exact ⟨.cons f hx hb suffix, hnot⟩

/-- Two cutedges touched by one component have no cutedge strictly between them.
This is the nonterminal no-gap assertion in Lemma 5.4. -/
theorem component_no_intermediate_cutedge [DecidableEq E] (p : Path inc s t)
    {e f g : E} (he : Cutedge inc s t e) (hf : Cutedge inc s t f)
    (hg : Cutedge inc s t g)
    (hef : p.walk.edges.idxOf e < p.walk.edges.idxOf f)
    (hfg : p.walk.edges.idxOf f < p.walk.edges.idxOf g)
    {x y : V} (hx : inc x e) (hy : inc y g)
    (hc : SameCutedgeComponent inc s t x y) : False := by
  obtain ⟨pre, hp⟩ := earlier_incidence_prefix p he hf hef hx
  obtain ⟨suffix, hq⟩ := later_incidence_suffix p hf hg hfg hy
  exact component_cannot_bypass hf pre suffix hp hq hc

/-- A source component cannot touch a cutedge after any other cutedge. -/
theorem source_component_no_earlier_cutedge [DecidableEq E] (p : Path inc s t)
    {e f : E} (he : Cutedge inc s t e) (hf : Cutedge inc s t f)
    (hlt : p.walk.edges.idxOf e < p.walk.edges.idxOf f)
    {x : V} (hx : inc x f) (hc : SameCutedgeComponent inc s t s x) : False := by
  obtain ⟨suffix, hq⟩ := later_incidence_suffix p he hf hlt hx
  exact component_cannot_bypass he (.nil s) suffix (by simp [HWalk.edges]) hq hc

/-- A sink component cannot touch a cutedge before any other cutedge. -/
theorem sink_component_no_later_cutedge [DecidableEq E] (p : Path inc s t)
    {e f : E} (he : Cutedge inc s t e) (hf : Cutedge inc s t f)
    (hlt : p.walk.edges.idxOf e < p.walk.edges.idxOf f)
    {x : V} (hx : inc x e) (hc : SameCutedgeComponent inc s t x t) : False := by
  obtain ⟨pre, hp⟩ := earlier_incidence_prefix p he hf hlt hx
  exact component_cannot_bypass hf pre (.nil t) hp (by simp [HWalk.edges]) hc

/-- If both terminals lie in one component, there are no cutedges. -/
theorem terminal_component_has_no_cutedge
    (hc : SameCutedgeComponent inc s t s t) {e : E}
    (he : Cutedge inc s t e) : False :=
  component_cannot_bypass he (.nil s) (.nil t)
    (by simp [HWalk.edges]) (by simp [HWalk.edges]) hc

/-- Following any walk to a target either stays in the component or meets an
unavoidable edge at the first place where the component is left. -/
theorem component_reaches_target_or_cutedge {x y : V} (w : HWalk inc x y) :
    SameCutedgeComponent inc s t x y ∨
      ∃ e z, Cutedge inc s t e ∧ inc z e ∧ SameCutedgeComponent inc s t x z := by
  classical
  induction w with
  | nil x => exact Or.inl (sameCutedgeComponent_refl inc s t x)
  | @cons x a y e hx ha tail ih =>
    by_cases he : Cutedge inc s t e
    · exact Or.inr ⟨e, x, he, hx, sameCutedgeComponent_refl inc s t x⟩
    · have hxa := sameCutedgeComponent_of_noncut_edge inc s t hx ha he
      rcases ih with h | ⟨f, z, hf, hz, hc⟩
      · exact Or.inl (sameCutedgeComponent_trans inc s t hxa h)
      · exact Or.inr ⟨f, z, hf, hz, sameCutedgeComponent_trans inc s t hxa hc⟩

/-- In a connected network a component meets an actual cutedge, or it contains
both terminals. In particular a terminal singleton cannot be its sole boundary.
The no-cutedge case is included explicitly. -/
theorem component_meets_cutedge_or_both_terminals
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (x : V) :
    (∃ e z, Cutedge inc s t e ∧ inc z e ∧ SameCutedgeComponent inc s t x z) ∨
      (SameCutedgeComponent inc s t x s ∧ SameCutedgeComponent inc s t x t) := by
  obtain ⟨ws⟩ := connected x s
  obtain ⟨wt⟩ := connected x t
  rcases component_reaches_target_or_cutedge ws with hs | hs
  · rcases component_reaches_target_or_cutedge wt with ht | ht
    · exact Or.inr ⟨hs, ht⟩
    · exact Or.inl ht
  · exact Or.inl hs

end FiniteFlow.Hypergraph
