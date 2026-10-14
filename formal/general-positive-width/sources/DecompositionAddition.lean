import ForestAttachment

namespace StackSorting.GuidedPathwidth
open BiInterface
universe u
variable {V : Type u} {G : SimpleGraph V} {P : Set V} {c : Nat}

namespace System
/-- Enlarging the allowed set preserves every concrete capture witness. -/
theorem enlarge_captures {P Q B : Set V} (C : System G P c) (hPQ : P ⊆ Q)
    (h : Captures G C B) : Captures G (fun i => (C i).enlarge hPQ) B := h
end System

namespace GuidedDecomposition

/-- Restore a vertex using actual componentwise copies, a spanning forest
retaining every old index edge, and one newly rooted graph guide. -/
theorem exists_restoreVertex [Finite V] (u : V) (D : GuidedDecomposition G (P \ {u}) c) :
    Nonempty (GuidedDecomposition G P (c+1)) := by
  classical
  let Q := P \ {u}
  let E := D.decomposition.restrictComponents (Set.Subset.refl Q)
  let M : Set E.Node := {a | ∃ x ∈ componentFiber G Q a.1, ReachIn G P x u}
  have hM : ∀ {a b}, E.forest.Adj a b → a ∈ M → b ∈ M := by
    intro a b hab ha
    change (∃ x ∈ componentFiber G Q a.1, ReachIn G P x u) at ha
    change ∃ x ∈ componentFiber G Q b.1, ReachIn G P x u
    rw [← hab.1]
    exact ha
  obtain ⟨F⟩ := exists_attached_forest E.acyclic hM
  let bag : Option E.Node → Set V := fun a => match a with
    | none => {u} ∩ P
    | some a => E.bag a ∪ if a ∈ M then {u} else ∅
  have old_not_u : ∀ a, u ∉ E.bag a := fun a hu => (E.inside a hu).2 rfl
  have marked_reaches : ∀ a ∈ M, ∀ x ∈ E.bag a, ReachIn G P x u := by
    intro a ha x hx
    obtain ⟨y,hy,hyu⟩ := ha
    exact (componentFiber_connected a.1 hx.2 hy).mono Set.sdiff_subset |>.trans hyu
  have bag_inside : ∀ a, bag a ⊆ P := by
    intro a x hx
    cases a with
    | none => exact hx.2
    | some a =>
      rcases hx with hx | hx
      · exact (E.inside a hx).1
      · by_cases ha : a ∈ M
        · have he : x = u := by simpa [ha] using hx
          obtain ⟨y,hy,hyu⟩ := ha
          exact he.symm ▸ hyu.2.1
        · simp [ha] at hx
  have old_captured : ∀ a, Captures G D.guides (E.bag a) := by
    intro a
    exact captures_mono D.guides (D.captured a.2) Set.inter_subset_left
  have bag_connected : ∀ a r, r ∈ bag a → ∀ s, s ∈ bag a → ReachIn G P r s := by
    intro a r hr s hs
    cases a with
    | none =>
      have hru : r = u := hr.1
      have hsu : s = u := hs.1
      subst r; subst s
      exact ReachIn.refl hr.2
    | some a =>
      by_cases ha : a ∈ M
      · have reaches : ∀ x ∈ bag (some a), ReachIn G P x u := by
          intro x hx
          rcases hx with hx | hx
          · exact marked_reaches a ha x hx
          · have he : x = u := by simpa [ha] using hx
            subst x
            exact ReachIn.refl (bag_inside (some a) (Or.inr (by simp [ha])))
        exact (reaches r hr).trans (reaches s hs).symm
      · have hr' : r ∈ E.bag a := by simpa [bag,ha] using hr
        have hs' : s ∈ E.bag a := by simpa [bag,ha] using hs
        exact (captures_connected D.guides (old_captured a) hr' hs').mono Set.sdiff_subset
  let T : Decomposition G P := {
    Node := Option E.Node
    finiteNode := inferInstance
    forest := F.graph
    acyclic := F.acyclic
    bag := bag
    inside := bag_inside
    vertex := by
      intro x hx
      by_cases he : x = u
      · exact ⟨none,he,hx⟩
      · obtain ⟨a,ha⟩ := E.vertex x ⟨hx,he⟩
        exact ⟨some a,Or.inl ha⟩
    edge := by
      intro x y hxy hx hy
      by_cases hxu : x = u
      · subst x
        have hyu : y ≠ u := hxy.ne.symm
        obtain ⟨a,ha⟩ := E.vertex y ⟨hy,hyu⟩
        have hm : a ∈ M := ⟨y,ha.2,hy,hx,.edge hxy.symm⟩
        exact ⟨some a,Or.inr (by simp [hm]),Or.inl ha⟩
      · by_cases hyu : y = u
        · subst y
          obtain ⟨a,ha⟩ := E.vertex x ⟨hx,hxu⟩
          have hm : a ∈ M := ⟨x,ha.2,hx,hy,.edge hxy⟩
          exact ⟨some a,Or.inl ha,Or.inr (by simp [hm])⟩
        · obtain ⟨a,ha,hb⟩ := E.edge hxy ⟨hx,hxu⟩ ⟨hy,hyu⟩
          exact ⟨some a,Or.inl ha,Or.inl hb⟩
    running := by
      intro x a b ha hb
      by_cases he : x = u
      · subst x
        have hup : u ∈ P := bag_inside a ha
        have root_path : ∀ d, u ∈ bag d → ReachIn F.graph {d | u ∈ bag d} none d := by
          intro d hd
          cases d with
          | none => exact ReachIn.refl ⟨rfl,hup⟩
          | some d =>
            have hm : d ∈ M := by
              rcases hd with hd | hd
              · exact (old_not_u d hd).elim
              · by_contra hm; simp [hm] at hd
            apply (F.markedConnected d hm).mono
            intro z hz
            cases z with
            | none => exact ⟨rfl,hup⟩
            | some z =>
              change z ∈ M at hz
              exact Or.inr (by simp [hz])
        exact (root_path a ha).symm.trans (root_path b hb)
      · have old_occurs : ∀ d, x ∈ bag d → ∃ n, d = some n ∧ x ∈ E.bag n := by
          intro d hd
          cases d with
          | none => exact (he hd.1).elim
          | some d =>
            refine ⟨d,rfl,?_⟩
            rcases hd with hd | hd
            · exact hd
            · by_cases hm : d ∈ M
              · exact (he (by simpa [hm] using hd)).elim
              · simp [hm] at hd
        obtain ⟨a,rfl,haOld⟩ := old_occurs a ha
        obtain ⟨b,rfl,hbOld⟩ := old_occurs b hb
        have h := E.running x a b haOld hbOld
        refine ⟨Or.inl haOld,Or.inl hbOld,?_⟩
        exact h.2.2.map Option.some
          (fun _ _ he => F.oldEdges he) (fun _ hn => Or.inl hn) }
  refine ⟨⟨T,System.addRoot (fun i => (D.guides i).enlarge Set.sdiff_subset) u,?_⟩⟩
  intro a
  apply System.addRoot_captures
  · exact bag_connected a
  · cases a with
    | none =>
      have hzero : bag none \ {u} = ∅ := by ext x; simp [bag]; tauto
      rw [hzero]
      exact captures_empty _ _
    | some a =>
      apply System.enlarge_captures
      apply captures_mono D.guides (old_captured a)
      intro x hx
      rcases hx.1 with hx' | hx'
      · exact hx'
      · by_cases hm : a ∈ M
        · exact (hx.2 (by simpa [hm] using hx')).elim
        · simp [hm] at hx'
end GuidedDecomposition

#print axioms GuidedDecomposition.exists_restoreVertex
end StackSorting.GuidedPathwidth
