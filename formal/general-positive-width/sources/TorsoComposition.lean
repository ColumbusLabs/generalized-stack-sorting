import TorsoGluingEmbedding

namespace StackSorting.BiInterface
variable {k : ℕ} {V W : Type*}

/-- Interface-preserving injective compression with exact torso paths preserves
the entire finite abstraction, including absent names and shared identities. -/
theorem abstraction_eq_of_compression (G : Graph k V) (H : Graph k W)
    (f : V → W) (hf : Function.Injective f)
    (hport : ∀ p, (G.port p).map f = H.port p)
    (hpath : ∀ v w, Through G.Adj G.boundaryᶜ v w ↔ Through H.Adj H.boundaryᶜ (f v) (f w)) :
    abstraction G = abstraction H := by
  apply Prod.ext
  · funext p
    apply Bool.eq_iff_iff.mpr
    rw [abstraction_presence, abstraction_presence]
    constructor
    · rintro ⟨v,hv⟩
      exact ⟨f v,by rw [← hport p,hv]; rfl⟩
    · rintro ⟨w,hw⟩
      rw [← hport p] at hw
      obtain ⟨v,hv,_⟩ := Option.map_eq_some_iff.mp hw
      exact ⟨v,hv⟩
  · apply Prod.ext
    · funext p q
      apply Bool.eq_iff_iff.mpr
      rw [abstraction_identity, abstraction_identity]
      constructor
      · rintro ⟨v,hv,hw⟩
        exact ⟨f v,by rw [← hport p,hv]; rfl,by rw [← hport q,hw]; rfl⟩
      · rintro ⟨w,hv,hw⟩
        rw [← hport p] at hv
        rw [← hport q] at hw
        obtain ⟨u,hu,heu⟩ := Option.map_eq_some_iff.mp hv
        obtain ⟨v,hv,hev⟩ := Option.map_eq_some_iff.mp hw
        have he := hf (heu.trans hev.symm)
        subst v
        exact ⟨u,hu,hv⟩
    · funext p q
      apply Bool.eq_iff_iff.mpr
      rw [abstraction_edge, abstraction_edge]
      constructor
      · rintro ⟨v,w,hv,hw,hne,hp⟩
        exact ⟨f v,f w,by rw [← hport p,hv]; rfl,by rw [← hport q,hw]; rfl,
          fun h => hne (hf h),(hpath v w).mp hp⟩
      · rintro ⟨v,w,hv,hw,hne,hp⟩
        rw [← hport p] at hv
        rw [← hport q] at hw
        obtain ⟨a,ha,hea⟩ := Option.map_eq_some_iff.mp hv
        obtain ⟨b,hb,heb⟩ := Option.map_eq_some_iff.mp hw
        subst v w
        exact ⟨a,b,ha,hb,fun h => hne (congrArg f h),(hpath a b).mpr hp⟩

/-- Replacing each factor by its actual torso leaves the glued abstraction
unchanged. This is a genuine compositionality step, not a hypothesis. -/
theorem abstraction_glue_torsos (G : Graph k V) (H : Graph k W) :
    abstraction (glue (torso G) (torso H)) = abstraction (glue G H) :=
  abstraction_eq_of_compression _ _ (torsoGlueEmbed G H) (torsoGlueEmbed_injective G H)
    (torsoGlueEmbed_port G H) (torsoGlueEmbed_through G H)

#print axioms abstraction_glue_torsos
end StackSorting.BiInterface
