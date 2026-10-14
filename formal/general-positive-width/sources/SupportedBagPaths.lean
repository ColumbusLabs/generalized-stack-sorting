import SupportedVertexWalks

namespace FiniteFlow.Hypergraph
variable {V E : Type*} [Fintype V] [DecidableEq V]

noncomputable def supportedFinset (S : Set V) (P : Finset V) : Finset S := by
  classical
  exact Finset.univ.filter (fun x => x.val ∈ P)

@[simp] theorem mem_supportedFinset (S : Set V) (P : Finset V) (x : S) :
    x ∈ supportedFinset S P ↔ x.val ∈ P := by
  classical
  simp [supportedFinset]

theorem supportedFinset_card_le (S : Set V) (P : Finset V) :
    (supportedFinset S P).card ≤ P.card := by
  classical
  have hsub : (supportedFinset S P).image Subtype.val ⊆ P := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact (mem_supportedFinset S P y).mp hy
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcard
  exact hcard

namespace BagPath
variable {P : Finset V} {b : Nat}
noncomputable def onSupport (D : BagPath P b) (S : Set V) : BagPath (supportedFinset S P) b where
  last := D.last
  bag := fun i => supportedFinset S (D.bag i)
  inside := by
    intro i hi x hx
    exact (mem_supportedFinset S P x).mpr (D.inside i hi ((mem_supportedFinset S (D.bag i) x).mp hx))
  bounded := fun i hi => (supportedFinset_card_le S (D.bag i)).trans (D.bounded i hi)
  vertex := by
    intro x hx
    obtain ⟨i,hi,hx⟩ := D.vertex x.val ((mem_supportedFinset S P x).mp hx)
    exact ⟨i,hi,(mem_supportedFinset S (D.bag i) x).mpr hx⟩
  interval := by
    intro i j k hij hjk hk x hxi hxk
    exact (mem_supportedFinset S (D.bag j) x).mpr (D.interval i j k hij hjk hk x.val
      ((mem_supportedFinset S (D.bag i) x).mp hxi) ((mem_supportedFinset S (D.bag k) x).mp hxk))

theorem onSupport_covers (D : BagPath P b) (S : Set V) {inc : V → E → Prop}
    (h : D.Covers inc) : (D.onSupport S).Covers (SupportedIncidence (inc := inc) S) := by
  intro e
  obtain ⟨i,hi,he⟩ := h e
  exact ⟨i,hi,fun x hx hxe => (mem_supportedFinset S (D.bag i) x).mpr
    (he x.val ((mem_supportedFinset S P x).mp hx) hxe)⟩
end BagPath
end FiniteFlow.Hypergraph
