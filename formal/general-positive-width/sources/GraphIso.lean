import TorsoAbstraction
import AssociativeGluing

namespace StackSorting.BiInterface
variable {k : ℕ} {V W : Type*}

structure Iso (G : Graph k V) (H : Graph k W) where
  vertex : V ≃ W
  adj : ∀ v w, H.Adj (vertex v) (vertex w) ↔ G.Adj v w
  left : ∀ i, (G.left i).map vertex = H.left i
  right : ∀ i, (G.right i).map vertex = H.right i

namespace Iso
variable {G : Graph k V} {H : Graph k W} (e : Iso G H)

theorem port (p : Port k) : (G.port p).map e.vertex = H.port p := by
  obtain ⟨b,i⟩ := p
  cases b
  · exact e.left i
  · exact e.right i

theorem port_some (p : Port k) (v : V) :
    H.port p = some (e.vertex v) ↔ G.port p = some v := by
  rw [← e.port p, Option.map_eq_some_iff]
  constructor
  · rintro ⟨w,hw,he⟩
    exact (e.vertex.injective he) ▸ hw
  · intro h
    exact ⟨v,h,rfl⟩

theorem boundary_iff (v : V) : e.vertex v ∈ H.boundary ↔ v ∈ G.boundary := by
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p,(e.port_some p v).mp hp⟩
  · rintro ⟨p,hp⟩
    exact ⟨p,(e.port_some p v).mpr hp⟩

theorem through_iff (v w : V) :
    Through H.Adj H.boundaryᶜ (e.vertex v) (e.vertex w) ↔
      Through G.Adj G.boundaryᶜ v w := by
  constructor
  · intro h
    have hh := h.map (J := G.boundaryᶜ) e.vertex.symm
      (by
        intro a b hab
        apply (e.adj (e.vertex.symm a) (e.vertex.symm b)).mp
        simpa using hab)
      (by
        intro a ha hmem
        apply ha
        simpa using (e.boundary_iff (e.vertex.symm a)).mpr hmem)
    simpa using hh
  · intro h
    exact h.map e.vertex (by intro a b hab; exact (e.adj a b).mpr hab)
      (by intro a ha hm; exact ha ((e.boundary_iff a).mp hm))

/-- Isomorphic bi-interface graphs have equal finite torso codes. -/
theorem abstraction_eq (e : Iso G H) : abstraction G = abstraction H := by
  apply Prod.ext
  · funext p
    apply Bool.eq_iff_iff.mpr
    rw [abstraction_presence, abstraction_presence]
    constructor
    · rintro ⟨v,hv⟩
      exact ⟨e.vertex v,(e.port_some p v).mpr hv⟩
    · rintro ⟨w,hw⟩
      refine ⟨e.vertex.symm w, (e.port_some p (e.vertex.symm w)).mp ?_⟩
      simpa using hw
  · apply Prod.ext
    · funext p q
      apply Bool.eq_iff_iff.mpr
      rw [abstraction_identity, abstraction_identity]
      constructor
      · rintro ⟨v,hv,hw⟩
        exact ⟨e.vertex v,(e.port_some p v).mpr hv,(e.port_some q v).mpr hw⟩
      · rintro ⟨w,hv,hw⟩
        refine ⟨e.vertex.symm w,?_,?_⟩
        · apply (e.port_some p _).mp; simpa using hv
        · apply (e.port_some q _).mp; simpa using hw
    · funext p q
      apply Bool.eq_iff_iff.mpr
      rw [abstraction_edge, abstraction_edge]
      constructor
      · rintro ⟨v,w,hv,hw,hne,hp⟩
        exact ⟨e.vertex v,e.vertex w,(e.port_some p v).mpr hv,
          (e.port_some q w).mpr hw,fun h => hne (e.vertex.injective h),
          (e.through_iff v w).mpr hp⟩
      · rintro ⟨v,w,hv,hw,hne,hp⟩
        refine ⟨e.vertex.symm v,e.vertex.symm w,?_,?_,?_,?_⟩
        · apply (e.port_some p _).mp; simpa using hv
        · apply (e.port_some q _).mp; simpa using hw
        · intro h; exact hne (e.vertex.symm.injective h)
        · apply (e.through_iff _ _).mp; simpa using hp
end Iso

noncomputable def associatorIso {U : Type*} (G : Graph k U) (H : Graph k V) (K : Graph k W) :
    Iso (glue (glue G H) K) (glue G (glue H K)) where
  vertex := associator G H K
  adj := associator_adj G H K
  left := associator_left G H K
  right := associator_right G H K

theorem abstraction_glue_assoc {U : Type*} (G : Graph k U) (H : Graph k V) (K : Graph k W) :
    abstraction (glue (glue G H) K) = abstraction (glue G (glue H K)) :=
  (associatorIso G H K).abstraction_eq

end StackSorting.BiInterface
