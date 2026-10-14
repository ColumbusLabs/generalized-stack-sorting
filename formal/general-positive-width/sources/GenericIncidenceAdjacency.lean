import GenericGuidanceIncidence

namespace StackSorting.GuidedPathwidth.GenericIncidence.System
variable {n : Nat} {H : SimpleGraph (Fin n)} (S : System H)

theorem adjacency_iff (u v : Fin n) : H.Adj u v ↔
    u≠v ∧ ∃ e : S.Element, S.isEdge e ∧ S.incident (.inl u) e ∧ S.incident (.inl v) e := by
  constructor
  · intro h
    obtain ⟨e,he | he⟩ := S.complete h
    · exact ⟨H.ne_of_adj h,.inr e,trivial,Or.inl he.1.symm,Or.inr he.2.symm⟩
    · exact ⟨H.ne_of_adj h,.inr e,trivial,Or.inr he.2.symm,Or.inl he.1.symm⟩
  · rintro ⟨hne,e,he,hu,hv⟩
    cases e with
    | inl e => exact he.elim
    | inr e =>
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact (hne (hu.trans hv.symm)).elim
      · simpa only [hu,hv] using S.sound e
      · simpa only [hu,hv] using (S.sound e).symm
      · exact (hne (hu.trans hv.symm)).elim

#print axioms adjacency_iff
end StackSorting.GuidedPathwidth.GenericIncidence.System
