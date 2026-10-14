import HyperpathRouteSplicing

namespace FiniteFlow.Hypergraph
variable {V E : Type} {inc : V → E → Prop}
namespace HWalk

theorem exists_traversal_of_edge {s t : V} (w : HWalk inc s t) {e : E}
    (he : e ∈ w.edges) : ∃ a b, (a,e,b) ∈ w.traversals := by
  rw [← w.traversal_edges] at he
  obtain ⟨tr,htr,he⟩ := List.mem_map.mp he
  exact ⟨tr.1,tr.2.2,he ▸ htr⟩

theorem traversal_unique {s t : V} (w : HWalk inc s t) (hn : w.edges.Nodup)
    {a b c d : V} {e : E} (ha : (a,e,b) ∈ w.traversals) (hc : (c,e,d) ∈ w.traversals) :
    a = c ∧ b = d := by
  induction w with
  | nil => simp [traversals] at ha
  | @cons s u t f hs hu tail ih =>
    have hnodup := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ha with ha | ha
    · have hea : a = s ∧ e = f ∧ b = u := by simpa using ha
      rcases List.mem_cons.mp hc with hc | hc
      · have hec : c = s ∧ e = f ∧ d = u := by simpa using hc
        exact ⟨hea.1.trans hec.1.symm,hea.2.2.trans hec.2.2.symm⟩
      · have he : e ∈ tail.edges := by
          rw [← tail.traversal_edges]
          exact List.mem_map.mpr ⟨(c,e,d),hc,rfl⟩
        exact (hnodup.1 (hea.2.1 ▸ he)).elim
    · rcases List.mem_cons.mp hc with hc | hc
      · have hec : c = s ∧ e = f ∧ d = u := by simpa using hc
        have he : e ∈ tail.edges := by
          rw [← tail.traversal_edges]
          exact List.mem_map.mpr ⟨(a,e,b),ha,rfl⟩
        exact (hnodup.1 (hec.2.1 ▸ he)).elim
      · exact ih hnodup.2 ha hc

structure Traversal (w : HWalk inc s t) (e : E) where
  before : V
  after : V
  occurs : (before,e,after) ∈ w.traversals

noncomputable def chooseTraversal {s t : V} (w : HWalk inc s t) (e : E) (he : e ∈ w.edges) :
    Traversal w e := by
  classical
  have hex := w.exists_traversal_of_edge he
  exact ⟨Classical.choose hex,Classical.choose (Classical.choose_spec hex),
    Classical.choose_spec (Classical.choose_spec hex)⟩

theorem chooseTraversal_incident {s t : V} (w : HWalk inc s t) (e : E) (he : e ∈ w.edges) :
    inc (w.chooseTraversal e he).before e ∧ inc (w.chooseTraversal e he).after e :=
  w.traversal_incident (w.chooseTraversal e he).occurs

end HWalk
end FiniteFlow.Hypergraph
