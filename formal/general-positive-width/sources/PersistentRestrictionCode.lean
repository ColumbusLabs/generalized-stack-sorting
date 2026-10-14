import InterfaceRestriction

namespace StackSorting.BiInterface.RepeatedColumn
variable {k : ℕ} {V W : Type*}

theorem persistentAt_code (G : Graph k V) (i : Fin k) :
    PersistentAt G i ↔ (abstraction G).2.1 (false,i) (true,i) = true :=
  (abstraction_identity G (false,i) (true,i)).symm

private theorem remove_presence (G : Graph k V) (p : Port k) :
    (∃ v, (removePersistent G).port p = some v) ↔
      (∃ v, G.port p = some v) ∧ ¬ PersistentAt G p.2 := by
  constructor
  · rintro ⟨v,hv⟩
    have hp := (restrictGraph_port_some G (Persistent G)ᶜ p v).mp hv
    exact ⟨⟨v.val,hp⟩,fun hi => v.property ((persistent_of_port G p hp).mpr hi)⟩
  · rintro ⟨⟨v,hv⟩,hn⟩
    have hv' : v ∉ Persistent G := fun hm => hn ((persistent_of_port G p hv).mp hm)
    exact ⟨⟨v,hv'⟩,(restrictGraph_port_some G (Persistent G)ᶜ p ⟨v,hv'⟩).mpr hv⟩

private theorem remove_identity (G : Graph k V) (p q : Port k) :
    (∃ v, (removePersistent G).port p = some v ∧ (removePersistent G).port q = some v) ↔
      (∃ v, G.port p = some v ∧ G.port q = some v) ∧
        ¬ PersistentAt G p.2 ∧ ¬ PersistentAt G q.2 := by
  constructor
  · rintro ⟨v,hv,hw⟩
    have hp := (restrictGraph_port_some G (Persistent G)ᶜ p v).mp hv
    have hq := (restrictGraph_port_some G (Persistent G)ᶜ q v).mp hw
    exact ⟨⟨v.val,hp,hq⟩,fun hi => v.property ((persistent_of_port G p hp).mpr hi),
      fun hi => v.property ((persistent_of_port G q hq).mpr hi)⟩
  · rintro ⟨⟨v,hv,hw⟩,hn,_⟩
    have hv' : v ∉ Persistent G := fun hm => hn ((persistent_of_port G p hv).mp hm)
    exact ⟨⟨v,hv'⟩,(restrictGraph_port_some G (Persistent G)ᶜ p ⟨v,hv'⟩).mpr hv,
      (restrictGraph_port_some G (Persistent G)ᶜ q ⟨v,hv'⟩).mpr hw⟩

private theorem remove_edge (G : Graph k V) (p q : Port k) :
    (∃ v w, (removePersistent G).port p = some v ∧ (removePersistent G).port q = some w ∧
      v ≠ w ∧ Through (removePersistent G).Adj (removePersistent G).boundaryᶜ v w) ↔
      (∃ v w, G.port p = some v ∧ G.port q = some w ∧ v ≠ w ∧
        Through G.Adj G.boundaryᶜ v w) ∧ ¬ PersistentAt G p.2 ∧ ¬ PersistentAt G q.2 := by
  have hkeep : G.boundaryᶜ ⊆ (Persistent G)ᶜ := by
    intro v hv hp
    exact hv (persistent_boundary G hp)
  constructor
  · rintro ⟨v,w,hv,hw,hne,hpath⟩
    have hp := (restrictGraph_port_some G (Persistent G)ᶜ p v).mp hv
    have hq := (restrictGraph_port_some G (Persistent G)ᶜ q w).mp hw
    exact ⟨⟨v.val,w.val,hp,hq,fun he => hne (Subtype.ext he),
      (through_restrict_iff G (Persistent G)ᶜ hkeep v w).mp hpath⟩,
      fun hi => v.property ((persistent_of_port G p hp).mpr hi),
      fun hi => w.property ((persistent_of_port G q hq).mpr hi)⟩
  · rintro ⟨⟨v,w,hv,hw,hne,hpath⟩,hnp,hnq⟩
    have hv' : v ∉ Persistent G := fun hm => hnp ((persistent_of_port G p hv).mp hm)
    have hw' : w ∉ Persistent G := fun hm => hnq ((persistent_of_port G q hw).mp hm)
    exact ⟨⟨v,hv'⟩,⟨w,hw'⟩,(restrictGraph_port_some G (Persistent G)ᶜ p ⟨v,hv'⟩).mpr hv,
      (restrictGraph_port_some G (Persistent G)ᶜ q ⟨w,hw'⟩).mpr hw,
      fun he => hne (congrArg Subtype.val he),
      (through_restrict_iff G (Persistent G)ᶜ hkeep ⟨v,hv'⟩ ⟨w,hw'⟩).mpr hpath⟩

/-- Removing all persistent interface vertices is determined entirely by the
actual torso code. The proof projects presence, identities, and real torso
walks separately, rather than assuming a deletion congruence. -/
theorem removePersistent_code_congr (G : Graph k V) (H : Graph k W)
    (h : abstraction G = abstraction H) :
    abstraction (removePersistent G) = abstraction (removePersistent H) := by
  have hat (i : Fin k) : PersistentAt G i ↔ PersistentAt H i := by
    rw [persistentAt_code,persistentAt_code,h]
  apply Prod.ext
  · funext p
    apply Bool.eq_iff_iff.mpr
    rw [abstraction_presence,abstraction_presence,remove_presence,remove_presence,
      ← abstraction_presence,← abstraction_presence,h,hat]
  · apply Prod.ext
    · funext p q
      apply Bool.eq_iff_iff.mpr
      rw [abstraction_identity,abstraction_identity,remove_identity,remove_identity,
        ← abstraction_identity,← abstraction_identity,h,hat,hat]
    · funext p q
      apply Bool.eq_iff_iff.mpr
      rw [abstraction_edge,abstraction_edge,remove_edge,remove_edge,
        ← abstraction_edge,← abstraction_edge,h,hat,hat]

#print axioms removePersistent_code_congr
end StackSorting.BiInterface.RepeatedColumn
