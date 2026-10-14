import PhysicalModelLeastSelector

namespace StackSorting.SparseEndpointMSO.CanonicalChoice

/-- Pull a finite tuple back through an actual domain isomorphism, cutting
away all irrelevant off-domain names explicitly. -/
def pullbackTuple {D E : Model} (iso : Isomorphism D E)
    (X : Fin k → Nat → Prop) : Fin k → Nat → Prop :=
  fun i x => x∈D.domain ∧ X i (iso.toFun x)

theorem pullbackTuple_supported {D E : Model} (iso : Isomorphism D E)
    (X : Fin k → Nat → Prop) : SupportedTuple D (pullbackTuple iso X) :=
  fun _ _ h => h.1

/-- The literal formula itself is unchanged by chronological naming. This
covers every individual/set binder and every original I/R/S/M atom. -/
theorem pullbackTuple_eval {D E : Model} (iso : Isomorphism D E)
    (f : Formula 0 k) (X : Fin k → Nat → Prop) :
    Eval D f Fin.elim0 (pullbackTuple iso X) ↔ Eval E f Fin.elim0 X := by
  apply iso.eval f Fin.elim0 Fin.elim0 (pullbackTuple iso X) X
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i x hx
    simp only [pullbackTuple,hx,true_and]

/-- It suffices to construct supported witnesses on the actual canonical time
models. Arbitrary domain names and duplicate domain-list entries are handled
by the already-proved physical isomorphism, without ordering Nat names. -/
theorem canonical_witnesses_cover_accepted (f : Formula 0 k) (r s : Nat)
    (h : ∀ n output, output.Perm (List.range n) →
      Generalized.Run r s [] (List.range n) output [] →
      ∃ X, SupportedTuple (canonicalDiagram output) X ∧
        Eval (canonicalDiagram output) f Fin.elim0 X) :
    ∀ D : Model, Satisfies D (fullAcceptedSentence r s) →
      ∃ X, SupportedTuple D X ∧ Eval D f Fin.elim0 X := by
  intro D hD
  obtain ⟨n,output,hp,hr,⟨iso⟩⟩ := (fullAcceptedSentence_iff_generated D r s).mp hD
  obtain ⟨X,_,hX⟩ := h n output hp hr
  exact ⟨pullbackTuple iso X,pullbackTuple_supported iso X,
    (pullbackTuple_eval iso f X).mpr hX⟩

/-- The inverse naming map used above also preserves literal physical
chronology, rather than identifying it with the numerical order of names. -/
theorem chronological_naming_exact {D E : Model} {n : Nat}
    (iso : Isomorphism D E) (hp : TimePath E n) (u v : Fin n) :
    OrderEval D chronologicalBefore
      ((orderedDomainOfTimeIsomorphism iso hp).vertex u).val
      ((orderedDomainOfTimeIsomorphism iso hp).vertex v).val ↔ u<v :=
  (orderedDomainOfTimeIsomorphism iso hp).before_iff u v

#print axioms canonical_witnesses_cover_accepted
#print axioms chronological_naming_exact
end StackSorting.SparseEndpointMSO.CanonicalChoice
