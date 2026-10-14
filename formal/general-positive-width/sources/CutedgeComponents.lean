import CutedgePrefix

/-! # Actual connected components after deletion of every cutedge -/
namespace FiniteFlow.Hypergraph

variable {V E : Type*} (inc : V → E → Prop) (s t : V)

def NoncutIncidence (x : V) (e : E) : Prop :=
  inc x e ∧ ¬ Cutedge inc s t e

def SameCutedgeComponent (x y : V) : Prop :=
  Nonempty (HWalk (NoncutIncidence inc s t) x y)

theorem sameCutedgeComponent_refl (x : V) : SameCutedgeComponent inc s t x x :=
  ⟨.nil x⟩

theorem sameCutedgeComponent_symm {x y : V}
    (h : SameCutedgeComponent inc s t x y) : SameCutedgeComponent inc s t y x := by
  obtain ⟨w⟩ := h
  exact ⟨w.reverse⟩

theorem sameCutedgeComponent_trans {x y z : V}
    (h : SameCutedgeComponent inc s t x y)
    (h' : SameCutedgeComponent inc s t y z) : SameCutedgeComponent inc s t x z := by
  obtain ⟨w⟩ := h
  obtain ⟨w'⟩ := h'
  exact ⟨w.append w'⟩

def cutedgeComponentSetoid : Setoid V where
  r := SameCutedgeComponent inc s t
  iseqv := ⟨sameCutedgeComponent_refl inc s t,
    sameCutedgeComponent_symm inc s t, sameCutedgeComponent_trans inc s t⟩

theorem noncut_walk_avoids {x y : V}
    (w : HWalk (NoncutIncidence inc s t) x y) {e : E}
    (he : Cutedge inc s t e) : e ∉ w.edges := by
  intro hm
  obtain ⟨a, b, pre, suf, ha, _, _⟩ := w.split_at_edge hm
  exact ha.2 he

theorem sameCutedgeComponent_of_noncut_edge {x y : V} {e : E}
    (hx : inc x e) (hy : inc y e) (he : ¬ Cutedge inc s t e) :
    SameCutedgeComponent inc s t x y :=
  ⟨.cons e ⟨hx, he⟩ ⟨hy, he⟩ (.nil y)⟩

/-- The entry and exit vertices of a cutedge on a simple path cannot already
be connected using only the remaining edges. -/
theorem cutedge_split_separates {e : E}
    (he : Cutedge inc s t e) {a b : V}
    (pre : HWalk inc s a) (suf : HWalk inc b t)
    (hp : e ∉ pre.edges) (hq : e ∉ suf.edges) :
    ¬ SameCutedgeComponent inc s t a b := by
  intro h
  obtain ⟨w⟩ := h
  let full := w.mono (fun _ _ h => h.1)
  let splice := pre.append (full.append suf)
  have hm := (cutedge_iff_every_walk inc s t e).mp he splice
  have hn : e ∉ full.edges := by
    simpa only [full, HWalk.edges_mono] using noncut_walk_avoids inc s t w he
  have : e ∈ pre.edges ++ (full.edges ++ suf.edges) := by
    simpa only [splice, HWalk.edges_append] using hm
  simp only [List.mem_append] at this
  rcases this with h | h | h
  · exact hp h
  · exact hn h
  · exact hq h

/-- Every unavoidable edge on an actual path has incidences in two distinct
cutedge components. No simplicity of a contracted hypergraph is assumed. -/
theorem cutedge_meets_distinct_components (p : Path inc s t) {e : E}
    (he : Cutedge inc s t e) :
    ∃ a b, inc a e ∧ inc b e ∧ ¬ SameCutedgeComponent inc s t a b := by
  obtain ⟨a, b, pre, suf, ha, hb, _, hp, hq, _, _⟩ :=
    p.walk.split_at_edge_nodup p.edges_nodup (he p)
  exact ⟨a, b, ha, hb, cutedge_split_separates inc s t he pre suf hp hq⟩

end FiniteFlow.Hypergraph
