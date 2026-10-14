import SparseLeastSelector
import FiniteLexChoice
import Mathlib.Data.Fintype.EquivFin

namespace StackSorting.SparseEndpointMSO.CanonicalChoice

variable {P : Type} {k : Nat}

/-- A supplied definable linear order on the actual vertex carrier.
This is independent of any decomposition or encoding witness. -/
structure OrderedDomain (D : Model) (before : Formula 2 0) (P : Type) [LT P] where
  vertex : P ≃ {x : Nat // x ∈ D.domain}
  before_iff : ∀ p q, OrderEval D before (vertex p).val (vertex q).val ↔ p < q

namespace OrderedDomain
variable {D : Model} {before : Formula 2 0} [LinearOrder P]
variable (J : OrderedDomain D before P)

noncomputable def lift (A : StackSorting.CanonicalChoice.Witness P k) : Fin k → Nat → Prop :=
  fun i x => ∃ hx : x ∈ D.domain, A i (J.vertex.symm ⟨x, hx⟩) = true

noncomputable def read (X : Fin k → Nat → Prop) : StackSorting.CanonicalChoice.Witness P k :=
  by
    classical
    exact fun i p => decide (X i (J.vertex p).val)

theorem lift_supported (A : StackSorting.CanonicalChoice.Witness P k) :
    SupportedTuple D (J.lift A) := fun _ _ h => h.choose

@[simp] theorem lift_vertex (A : StackSorting.CanonicalChoice.Witness P k) (i : Fin k) (p : P) :
    J.lift A i (J.vertex p).val ↔ A i p = true := by
  simp [lift, (J.vertex p).property]

@[simp] theorem read_lift (A : StackSorting.CanonicalChoice.Witness P k) :
    J.read (J.lift A) = A := by
  classical
  funext i p
  simp [read]

theorem lift_read (X : Fin k → Nat → Prop) (hX : SupportedTuple D X) :
    J.lift (J.read X) = X := by
  classical
  funext i x
  apply propext
  simp only [lift, read, decide_eq_true_eq]
  constructor
  · rintro ⟨hx, h⟩
    simpa using h
  · intro h
    refine ⟨hX i x h, ?_⟩
    simpa using h

theorem lift_injective : Function.Injective (J.lift (k := k)) := by
  intro A B h
  have hh := congrArg J.read h
  simpa only [J.read_lift] using hh

private theorem bool_eq_iff (a b : Bool) : (a = true ↔ b = true) ↔ a = b := by
  cases a <;> cases b <;> decide

theorem before_lift_iff (A B : StackSorting.CanonicalChoice.Witness P k) :
    BeforeSets D before (J.lift A) (J.lift B) ↔
      StackSorting.CanonicalChoice.Before A B := by
  classical
  rw [StackSorting.CanonicalChoice.before_explicit]
  constructor
  · rintro ⟨i, hi, p, hp, hd, he⟩
    let q := J.vertex.symm ⟨p, hp⟩
    have hq : (J.vertex q).val = p := by simp [q]
    refine ⟨i, ?_, q, ?_, ?_, ?_⟩
    · intro j hj
      funext x
      exact (bool_eq_iff _ _).mp (by simpa using hi j hj (J.vertex x).val (J.vertex x).property)
    · intro x hx
      exact (bool_eq_iff _ _).mp (by
        have h := he (J.vertex x).val (J.vertex x).property
          (by rw [← hq]; exact (J.before_iff x q).mpr hx)
        simpa using h)
    · have h := hd.1
      rw [← hq, J.lift_vertex] at h
      cases e : A i q <;> simp_all
    · have h := hd.2
      rw [← hq, J.lift_vertex] at h
      exact h
  · rintro ⟨i, hi, p, he, ha, hb⟩
    refine ⟨i, ?_, (J.vertex p).val, (J.vertex p).property, ?_, ?_⟩
    · intro j hj x hx
      let q := J.vertex.symm ⟨x,hx⟩
      have hq : (J.vertex q).val = x := by simp [q]
      rw [← hq, J.lift_vertex, J.lift_vertex, hi j hj]
    · simp [ha, hb]
    · intro x hx hxp
      let q := J.vertex.symm ⟨x,hx⟩
      have hq : (J.vertex q).val = x := by simp [q]
      have hqp : q < p := (J.before_iff q p).mp (by simpa only [hq] using hxp)
      rw [← hq, J.lift_vertex, J.lift_vertex, he q hqp]

/-- The explicit original sparse-MSO selector has a unique supported witness
whenever an admissible supported witness exists. There is no decomposition,
encoding, recognizability or assumed-uniqueness premise. -/
theorem exists_unique_leastSelector [Fintype P]
    (J : OrderedDomain D before P) (f : Formula 0 k)
    (hex : ∃ X, SupportedTuple D X ∧ Eval D f Fin.elim0 X) :
    ∃! X, SupportedTuple D X ∧ Eval D (leastSelector before f) Fin.elim0 X := by
  classical
  let valid : StackSorting.CanonicalChoice.Witness P k → Prop :=
    fun A => Eval D f Fin.elim0 (J.lift A)
  have hv : ∃ A, valid A := by
    obtain ⟨X,hX,hf⟩ := hex
    refine ⟨J.read X, ?_⟩
    simpa only [valid, J.lift_read X hX] using hf
  obtain ⟨A,hA,huniq⟩ := StackSorting.CanonicalChoice.exists_unique_selected valid hv
  have hsel (B : StackSorting.CanonicalChoice.Witness P k) :
      Eval D (leastSelector before f) Fin.elim0 (J.lift B) ↔
        StackSorting.CanonicalChoice.Selected valid B := by
    rw [eval_leastSelector]
    apply and_congr_right
    intro _
    constructor
    · intro h C hC
      exact fun hCB => h (J.lift C) (J.lift_supported C) hC
        ((J.before_lift_iff C B).mpr hCB)
    · intro h Y hY hf hYB
      have hC : valid (J.read Y) := by simpa only [valid, J.lift_read Y hY] using hf
      apply h (J.read Y) hC
      apply (J.before_lift_iff _ B).mp
      simpa only [J.lift_read Y hY] using hYB
  refine ⟨J.lift A, ⟨J.lift_supported A, (hsel A).mpr hA⟩, ?_⟩
  intro Y hY
  have hy : StackSorting.CanonicalChoice.Selected valid (J.read Y) :=
    (hsel (J.read Y)).mp (by simpa only [J.lift_read Y hY.1] using hY.2)
  have he := huniq (J.read Y) hy
  have hh := congrArg J.lift he
  simpa only [J.lift_read Y hY.1] using hh

#print axioms before_lift_iff
#print axioms exists_unique_leastSelector
end OrderedDomain
end StackSorting.SparseEndpointMSO.CanonicalChoice
