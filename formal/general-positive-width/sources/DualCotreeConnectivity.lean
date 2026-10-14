import TreeSupportedCuts

namespace StackSorting.GraphWidth.UCurve.PlaneGrid
open FinitePort

def FullDualAdj {α V F} (I : IncidenceMap α V F) (a b : Fin F) : Prop :=
  ∃ d : α, I.face d=a ∧ I.face (I.reverse d)=b

def CotreeAdj {α V F} (I : IncidenceMap α V F) (T : RootedTree V) (a b : Fin F) : Prop :=
  ∃ d : α, I.face d=a ∧ I.face (I.reverse d)=b ∧ ¬ TreeAdj T (I.tail d) (I.tail (I.reverse d))

theorem fullDualAdj_symm {α V F} (I : IncidenceMap α V F) {a b} (h : FullDualAdj I a b) :
    FullDualAdj I b a := by
  obtain ⟨d,rfl,rfl⟩ := h
  exact ⟨I.reverse d,rfl,by rw [I.reverse_reverse]⟩

theorem cotreeAdj_symm {α V F} (I : IncidenceMap α V F) (T : RootedTree V)
    {a b} (h : CotreeAdj I T a b) : CotreeAdj I T b a := by
  obtain ⟨d,rfl,rfl,ht⟩ := h
  refine ⟨I.reverse d,rfl,by rw [I.reverse_reverse],?_⟩
  intro hh
  rw [I.reverse_reverse] at hh
  exact ht (treeAdj_symm T hh)

theorem walk_preserves_value {α β : Type} {adj : α → α → Prop} (value : α → β)
    (hedge : ∀ a b, adj a b → value a=value b) {a b}
    (h : Walk adj (fun _ => True) a b) : value a=value b := by
  induction h with
  | refl => rfl
  | @step a b c _ hs _ ih => exact (hedge a b hs).trans ih

/-- Removing primal tree edges leaves the actual dual adjacency connected.
The hypotheses are original dual connectivity and local vertex-cycle cut
continuation; no cotree connectivity, Euler identity or width is assumed. -/
theorem dual_complement_tree_connected {α V F} (I : IncidenceMap α V F)
    (T : RootedTree V) (hc : CutContinues I)
    (hdual : ∀ a b, Walk (FullDualAdj I) (fun _ => True) a b) (a b : Fin F) :
    Walk (CotreeAdj I T) (fun _ => True) a b := by
  classical
  let P : Fin F → Prop := fun x => Walk (CotreeAdj I T) (fun _ => True) a x
  let color : Fin F → Bool := fun x => decide (P x)
  have hs : ∀ d, FaceCut I color d → TreeAdj T (I.tail d) (I.tail (I.reverse d)) := by
    intro d hd
    apply Classical.byContradiction
    intro hn
    have he : Walk (CotreeAdj I T) (fun _ => True) (I.face d) (I.face (I.reverse d)) :=
      .step trivial ⟨d,rfl,rfl,hn⟩ (.refl trivial)
    have hp : P (I.face d) ↔ P (I.face (I.reverse d)) :=
      ⟨fun h => h.trans he,fun h => h.trans (he.reverse (cotreeAdj_symm I T))⟩
    apply hd
    change decide (P (I.face d))=decide (P (I.face (I.reverse d)))
    rw [propext hp]
  have hall : ∀ d, color (I.face d)=color (I.face (I.reverse d)) := by
    intro d
    apply Classical.byContradiction
    intro hd
    exact tree_supported_cut_false I T hc color hs d hd
  have heq : color a=color b := by
    apply walk_preserves_value color (h := hdual a b)
    intro x y h
    obtain ⟨d,rfl,rfl⟩ := h
    exact hall d
  have ha : color a=true := by
    change decide (P a)=true
    exact decide_eq_true (.refl trivial)
  have hb : color b=true := heq.symm.trans ha
  exact of_decide_eq_true hb

end StackSorting.GraphWidth.UCurve.PlaneGrid
