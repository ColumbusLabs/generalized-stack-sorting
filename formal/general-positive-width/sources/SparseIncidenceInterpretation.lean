import SparseIncidenceTemplates
import SparseFiniteCopy

namespace StackSorting.SparseEndpointMSO.IncidenceOwnership

inductive IncidenceAtom : Nat → Type where
  | vertex : IncidenceAtom 1
  | edge : IncidenceAtom 1
  | incidence : IncidenceAtom 2
  | insert : IncidenceAtom 1
  | remove : IncidenceAtom 1

def IsVertex {D : Model} : Element D → Prop
  | .inl _ => True
  | .inr _ => False

def IsEdge {D : Model} : Element D → Prop
  | .inl _ => False
  | .inr _ => True

def ElementIncident {D : Model} : Element D → Element D → Prop
  | .inl v, .inr e => Incident v e
  | _, _ => False

def ElementInsert {D : Model} : Element D → Prop
  | .inl v => D.I v.val
  | .inr _ => False

def ElementRemove {D : Model} : Element D → Prop
  | .inl v => D.R v.val
  | .inr _ => False

def AtomEval {D : Model} {r : Nat} : IncidenceAtom r → (Fin r → Element D) → Prop
  | .vertex, env => IsVertex (env 0)
  | .edge, env => IsEdge (env 0)
  | .incidence, env => ElementIncident (env 0) (env 1)
  | .insert, env => ElementInsert (env 0)
  | .remove, env => ElementRemove (env 0)

def atomFormula {r : Nat} : IncidenceAtom r → (Fin r → Fin 3) → Formula r 0
  | .vertex, tags => if tags 0 = 0 then .truth else .neg .truth
  | .edge, tags => if tags 0 = 0 then .neg .truth else .truth
  | .incidence, tags => incidenceFormula (tags 0) (tags 1)
  | .insert, tags => if tags 0 = 0 then .insert 0 else .neg .truth
  | .remove, tags => if tags 0 = 0 then .remove 0 else .neg .truth

def interpretation : FiniteCopy.Interpretation IncidenceAtom 3 where
  domain := domainFormula
  atom := atomFormula

theorem interpretation_domain (D : Model) (q : FiniteCopy.Element 3) :
    FiniteCopy.InDomain interpretation D q ↔ ValidCode D q.1 q.2 :=
  domainFormula_correct D q.1 q.2

theorem represents_vertex_tag {D : Model} {c : Fin 3} {x : Nat} {a : Element D}
    (hr : Represents D c x a) : c = 0 ↔ IsVertex a := by
  cases a with
  | inl v => simp [IsVertex, hr.1]
  | inr e =>
    rcases hr.2 with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [IsVertex]

theorem represents_edge_tag {D : Model} {c : Fin 3} {x : Nat} {a : Element D}
    (hr : Represents D c x a) : c ≠ 0 ↔ IsEdge a := by
  cases a with
  | inl v => simp [IsEdge, hr.1]
  | inr e =>
    rcases hr.2 with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [IsEdge]

theorem represented_element_incidence {D : Model} (h : Laws D)
    {a b : Element D} {c d : Fin 3} {x y : Nat}
    (ha : Represents D c x a) (hb : Represents D d y b) :
    CodeIncident D c d x y ↔ ElementIncident a b := by
  cases a with
  | inl v =>
    cases b with
    | inl w => simp [CodeIncident, hb.1, ElementIncident]
    | inr e => exact represented_incidence h v e ha hb
  | inr e =>
    have hc : c ≠ 0 := (represents_edge_tag ha).mpr True.intro
    cases b <;> simp [CodeIncident, hc, ElementIncident]

/-- Every interpreted atom has its real incidence meaning under the exact
representation. The interpretation never receives semantic oracle atoms. -/
theorem atomFormula_correct {D : Model} (h : Laws D) {r : Nat}
    (A : IncidenceAtom r) (tags : Fin r → Fin 3) (env : Fin r → Nat)
    (actual : Fin r → Element D)
    (hr : ∀ i, Represents D (tags i) (env i) (actual i)) :
    Eval D (atomFormula A tags) env Fin.elim0 ↔ AtomEval A actual := by
  classical
  cases A with
  | vertex =>
    have he := represents_vertex_tag (hr 0)
    simp only [atomFormula, AtomEval]
    by_cases hc : tags 0 = 0 <;> simp [hc, Eval, ← he]
  | edge =>
    have he := represents_edge_tag (hr 0)
    simp only [atomFormula, AtomEval]
    by_cases hc : tags 0 = 0 <;> simp [hc, Eval, ← he]
  | incidence =>
    exact (incidenceFormula_correct D _ _ env).trans
      (represented_element_incidence h (hr 0) (hr 1))
  | insert =>
    have hh := hr 0
    cases he : actual 0 with
    | inl v =>
      rw [he] at hh
      simp [atomFormula, AtomEval, he, ElementInsert, hh.1, hh.2, Eval]
    | inr e =>
      rw [he] at hh
      have hc : tags 0 ≠ 0 := (represents_edge_tag hh).mpr True.intro
      simp [atomFormula, AtomEval, he, ElementInsert, hc, Eval]
  | remove =>
    have hh := hr 0
    cases he : actual 0 with
    | inl v =>
      rw [he] at hh
      simp [atomFormula, AtomEval, he, ElementRemove, hh.1, hh.2, Eval]
    | inr e =>
      rw [he] at hh
      have hc : tags 0 ≠ 0 := (represents_edge_tag hh).mpr True.intro
      simp [atomFormula, AtomEval, he, ElementRemove, hc, Eval]

#print axioms interpretation_domain
#print axioms atomFormula_correct
end StackSorting.SparseEndpointMSO.IncidenceOwnership
