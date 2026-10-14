import NormalForestCodec
import PhysicalSelectedForest

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.SparseEndpointMSO.CanonicalChoice
open EliminationSyntax GraphWidth FinitePort
variable {n k colors relations : Nat}

theorem named_successor_walk {D : Model}
    (e : Fin n ≃ {x // x ∈ D.domain}) (H : Graph n)
    (hH : ∀ u v, H.Adj u v ↔ ModelAdjacent D (e u).val (e v).val)
    {x y : Nat} (hx : x ∈ D.domain) (hy : y ∈ D.domain) (w : SparseEndpointMSO.Walk D x y) :
    GraphWidth.Walk H.Adj (fun _ => True) (e.symm ⟨x,hx⟩) (e.symm ⟨y,hy⟩) := by
  induction w with
  | refl => exact .refl trivial
  | @step p q hp hq hs ih =>
    have he : H.Adj (e.symm ⟨p,hp.mem⟩) (e.symm ⟨q,hq⟩) := by
      apply (hH _ _).mpr
      simpa only [Equiv.apply_symm_apply,ModelAdjacent] using (Or.inl hs : ModelAdjacent D p q)
    exact (ih hp.mem).trans (.step trivial he (.refl trivial))

/-- Actual physical successor chronology makes the sparse graph connected,
including arbitrary names and repeated entries in its domain presentation. -/
theorem physical_named_connected {D : Model} {r s : Nat}
    (hD : Satisfies D (fullAcceptedSentence r s))
    (e : Fin n ≃ {x // x ∈ D.domain}) (H : Graph n)
    (hH : ∀ u v, H.Adj u v ↔ ModelAdjacent D (e u).val (e v).val) :
    ∀ u v, GraphWidth.Walk H.Adj (fun _ => True) u v := by
  obtain ⟨_,output,_,_,⟨iso⟩⟩ := (fullAcceptedSentence_iff_generated D r s).mp hD
  have ht := eventDiagram_path (Generalized.canonicalEvents 0 output)
  intro u v
  have hu := iso.to_mem (e u).val (e u).property
  have hv := iso.to_mem (e v).val (e v).property
  have lift {a b : Fin n}
      (hw : SparseEndpointMSO.Walk (canonicalDiagram output)
        (iso.toFun (e a).val) (iso.toFun (e b).val)) :
      GraphWidth.Walk H.Adj (fun _ => True) a b := by
    have hh := iso.symm.walk hw
    simp only [Isomorphism.symm,iso.left_inv _ (e a).property,
      iso.left_inv _ (e b).property] at hh
    have hw := named_successor_walk e H hH (e a).property (e b).property hh
    have he (z : Fin n) : e.symm ⟨(e z).val,(e z).property⟩=z := e.symm_apply_apply z
    rw [he a,he b] at hw
    exact hw
  rcases Nat.le_total (iso.toFun (e u).val) (iso.toFun (e v).val) with h | h
  · exact lift ((walk_iff_le _ _ ht hu hv).mpr h)
  · exact (lift ((walk_iff_le _ _ ht hv hu).mpr h)).reverse H.symm

/-- Conditional only on literal admissibility existence: the selected physical
parent has an actual normal finite-port encoder, with original chronology
preserved and no assumed graph connectedness or numbered tree. -/
theorem physical_exists_normal_selected_codec {D : Model} {r s : Nat}
    (hD : Satisfies D (fullAcceptedSentence r s))
    (e : Fin n ≃ {x // x ∈ D.domain}) (earlier : Formula 2 k) (b : Nat)
    (H : Graph n) (hH : ∀ u v, H.Adj u v ↔ ModelAdjacent D (e u).val (e v).val)
    (G : Diagram n colors relations) (hG : ∀ u v, H.Adj u v ↔ Adjacent G u v)
    (hl : Loopless G) (hn : 0<n) (chronology : FixedOrder n)
    (hex : ∃ X, SupportedTuple D X ∧ Eval D (admissibleSentence earlier b) Fin.elim0 X) :
    ∃ (P : Fin n → Fin n) (E : NormalForestCodec G (b-1) P chronology),
      ∀ u v, RelationEval D (selectedParent (admissibleSentence earlier b) earlier)
        Fin.elim0 (e u).val (e v).val ↔
          (E.index v).val≠0 ∧ E.tree.parent (E.index v)=E.index u := by
  obtain ⟨O,hparent,hedge,hbound⟩ := physical_exists_selected_forest hD e earlier b H hH hex
  obtain ⟨E⟩ := forest_has_normal_codec G H hG hl O.ranked hedge hbound
    (physical_named_connected hD e H hH) hn chronology
  exact ⟨O.ranked.parent,E,fun u v => (hparent u v).trans (E.proper_parent_exact u v).symm⟩

#print axioms physical_named_connected
#print axioms physical_exists_normal_selected_codec
end StackSorting.SparseEndpointMSO.CanonicalChoice
