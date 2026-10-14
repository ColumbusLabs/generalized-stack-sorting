import AdhesionColoring
import RealizedGuidedDecomposition

namespace StackSorting.AdhesionGuidance
open GraphWidth FinitePort GuidedPathwidth
variable {n t : Nat} {G : Graph n} {T : RootedTree t}
variable {D : GraphWidth.Decomposition G T}

/-- A literal original-edge walk yields restricted reachability. -/
theorem walk_reach {V : Type} {H : SimpleGraph V} {a b : V}
    (w : H.Walk a b) (S : Set V) (hs : ∀ v ∈ w.support, v ∈ S) :
    ReachIn H S a b := by
  induction w with
  | nil => exact ReachIn.refl (hs _ (by simp))
  | @cons a z b haz tail ih =>
    have ha : a ∈ S := hs _ (by simp)
    have hz : z ∈ S := hs _ (by simp [tail.start_mem_support])
    have ht : ReachIn H S z b := ih (fun v hv => hs v (by simp [hv]))
    exact ReachIn.trans ⟨ha,hz,.edge haz⟩ ht

namespace Paths
variable (P : Paths D)

/-- Same-color paths ending at one root are merged on their literal supports. -/
def merged {c : Nat} (f : Index D → Fin c) (color : Fin c) (r : Fin n) : Set (Fin n) :=
  {v | ∃ i, f i = color ∧ i.val.2 = r ∧ v ∈ (P.walk i).support}

noncomputable def guide {c : Nat} (f : Index D → Fin c)
    (hf : ∀ i j, P.Conflict i j → f i ≠ f j) (color : Fin c) :
    Color (originalGraph G) Set.univ where
  support := P.merged f color
  inside := by simp
  reaches := by
    intro r v hv
    obtain ⟨i,hic,hir,hvi⟩ := hv
    subst r
    have hreach := walk_reach ((P.walk i).dropUntil v hvi)
      (P.merged f color i.val.2) (by
        intro z hz
        exact ⟨i,hic,rfl,(P.walk i).support_dropUntil_subset_support hvi hz⟩)
    exact hreach
  unique := by
    intro r s v hr hs
    obtain ⟨i,hic,hir,hvi⟩ := hr
    obtain ⟨j,hjc,hjs,hvj⟩ := hs
    by_contra hne
    have htargets : i.val.2 ≠ j.val.2 := by simpa [hir,hjs] using hne
    exact hf i j ⟨htargets,v,hvi,hvj⟩ (hic.trans hjc.symm)

theorem guide_captures_at {c : Nat} (f : Index D → Fin c)
    (hf : ∀ i j, P.Conflict i j → f i ≠ f j) (x : Fin t) :
    ∀ r ∈ adhesion D x, ∃ color,
      P.representative x ∈ (P.guide f hf color).support r := by
  intro r hr
  let i : Index D := ⟨(x,r),hr⟩
  exact ⟨f i,i,rfl,rfl,(P.walk i).start_mem_support⟩

/-- The output consists of actual rooted acyclic subgraphs of the ORIGINAL
 graph, capturing each actual adhesion at the input representative. No global
 bag capture or global guided-treewidth conclusion appears. -/
theorem exists_adhesion_forests {k L : Nat} (hb : P.Bounded k L) :
    ∃ C : Fin (2 * L + 2 * k) → RootedColor (originalGraph G) Set.univ,
      ∀ x r, r ∈ adhesion D x → ∃ color,
        r ∈ (C color).roots ∧ P.representative x ∈ (C color).selected ∧
        r ∈ (C color).selected ∧ (C color).graph.Reachable (P.representative x) r := by
  obtain ⟨f,hf⟩ := P.exists_coloring hb
  refine ⟨fun color => (P.guide f hf color).realize,?_⟩
  intro x r hr
  obtain ⟨color,h⟩ := P.guide_captures_at f hf x r hr
  exact ⟨color,((P.guide f hf color).realize_rootRelation _ _).mpr h⟩

theorem exists_adhesion_capture {k L : Nat} (hb : P.Bounded k L) :
    ∃ C : Fin (2 * L + 2 * k) → RootedColor (originalGraph G) Set.univ,
      ∀ x, ForestCaptures C (adhesion D x) := by
  obtain ⟨C,hC⟩ := P.exists_adhesion_forests hb
  exact ⟨C,fun x _ => ⟨P.representative x,hC x⟩⟩

/-- The paper's palette follows only after a SEPARATE construction supplies
 an actual family with ancestral indexed load at most 2*k^3. -/
theorem exists_paper_palette {k : Nat} (hb : P.Bounded k (2 * k^3)) :
    ∃ C : Fin (4 * k^3 + 2 * k) → RootedColor (originalGraph G) Set.univ,
      ∀ x, ForestCaptures C (adhesion D x) := by
  have he : 2 * (2 * k^3) + 2 * k = 4 * k^3 + 2 * k := by omega
  rw [← he]
  exact P.exists_adhesion_capture hb

#print axioms exists_adhesion_forests
#print axioms exists_adhesion_capture
#print axioms exists_paper_palette
end Paths
end StackSorting.AdhesionGuidance
