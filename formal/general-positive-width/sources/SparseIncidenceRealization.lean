import SparseIncidenceInterpretation
import SparseFiniteCopyRealization

namespace StackSorting.SparseEndpointMSO.IncidenceOwnership

def realization {D : Model} (h : Laws D) :
    FiniteCopy.Realization interpretation D (Element D) AtomEval where
  rep q a := Represents D q.1 q.2 a
  valid q _ hr := (interpretation_domain D q).mpr (represents_valid hr)
  cover a := by
    obtain ⟨c, x, hr⟩ := element_has_code h a
    exact ⟨(c, x), hr⟩
  complete q hq := code_has_element h ((interpretation_domain D q).mp hq)
  equal q p a b ha hb := by
    constructor
    · intro he
      subst p
      exact represented_element_unique h ha hb
    · intro he
      subst b
      have hh := code_unique ha hb
      exact Prod.ext hh.1 hh.2
  atom A env actual hr := atomFormula_correct h A (fun i => (env i).1)
    (fun i => (env i).2) actual hr

/-- Arbitrary incidence-MSO sentences over the real simple undirected physical
graph translate to the original sparse vertex-MSO vocabulary. All first-order
and monadic quantifiers are included; each incidence set is three vertex sets. -/
theorem accepted_incidence_sentence {D : Model} {r s : Nat}
    (h : Satisfies D (fullAcceptedSentence r s))
    (p : FiniteCopy.CopyFormula IncidenceAtom 0 0) :
    Satisfies D (FiniteCopy.compile interpretation p Fin.elim0 Fin.elim0 Fin.elim0) ↔
      FiniteCopy.ActualEval (AtomEval (D := D)) p Fin.elim0 Fin.elim0 := by
  have hc := FiniteCopy.eval_compile interpretation D p Fin.elim0 Fin.elim0
    Fin.elim0 Fin.elim0 Fin.elim0
  apply hc.trans
  exact (realization (laws_of_fullAcceptedSentence h)).eval p
    _ _ _ _ (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

#print axioms realization
#print axioms accepted_incidence_sentence
end StackSorting.SparseEndpointMSO.IncidenceOwnership
