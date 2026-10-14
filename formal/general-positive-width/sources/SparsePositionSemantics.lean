import SparseEndpointMSO
import Mathlib.Data.Fintype.EquivFin

/-! A type-valued semantics for the exact accepted sparse graph syntax.
Every point of the carrier is a vertex; monadic variables range over all subsets.
The transport theorem compares this semantics with the original finite Nat domain,
including domain-restricted set quantification and arbitrary blocks of FO binders. -/
namespace StackSorting.SparseEndpointMSO

universe u
structure Relations (P : Type u) where
  insert : P → Prop
  remove : P → Prop
  successor : P → P → Prop
  matching : P → P → Prop

def Formula.EvalOn {P : Type u} (R : Relations P) : Formula a b →
    (Fin a → P) → (Fin b → P → Bool) → Prop
  | .truth, _, _ => True
  | .equal i j, env, _ => env i = env j
  | .member i X, env, sets => sets X (env i) = true
  | .insert i, env, _ => R.insert (env i)
  | .remove i, env, _ => R.remove (env i)
  | .successor i j, env, _ => R.successor (env i) (env j)
  | .matching i j, env, _ => R.matching (env i) (env j)
  | .neg f, env, sets => ¬ f.EvalOn R env sets
  | .conj f g, env, sets => f.EvalOn R env sets ∧ g.EvalOn R env sets
  | .implies f g, env, sets => f.EvalOn R env sets → g.EvalOn R env sets
  | .existsFO k f, env, sets => ∃ values : Fin k → P,
      f.EvalOn R (Fin.addCases values env) sets
  | .allFO k f, env, sets => ∀ values : Fin k → P,
      f.EvalOn R (Fin.addCases values env) sets
  | .allSet f, env, sets => ∀ X : P → Bool,
      f.EvalOn R env (Fin.cons X sets)

/-- Only an equivalence with the actual finite domain is required. The source
list need not be duplicate-free for this purely logical statement. -/
structure DomainInterpretation (D : Model) {P : Type u} (R : Relations P) where
  vertex : P ≃ {x : Nat // x ∈ D.domain}
  insert_iff : ∀ p, D.I (vertex p).val ↔ R.insert p
  remove_iff : ∀ p, D.R (vertex p).val ↔ R.remove p
  successor_iff : ∀ p q, D.S (vertex p).val (vertex q).val ↔ R.successor p q
  matching_iff : ∀ p q, D.M (vertex p).val (vertex q).val ↔ R.matching p q

namespace DomainInterpretation
variable {P : Type u} {D : Model} {R : Relations P}

theorem vertex_value_injective (J : DomainInterpretation D R) :
    Function.Injective (fun p => (J.vertex p).val) := by
  intro p q h
  exact J.vertex.injective (Subtype.ext h)

/-- Complete syntactic induction; in particular no formula recognizability or
sentence-level equivalence is included among the hypotheses. -/
theorem eval (J : DomainInterpretation D R) (f : Formula a b)
    (envD : Fin a → Nat) (envP : Fin a → P)
    (setsD : Fin b → Nat → Prop) (setsP : Fin b → P → Bool)
    (henv : ∀ i, envD i = (J.vertex (envP i)).val)
    (hsets : ∀ X p, setsD X (J.vertex p).val ↔ setsP X p = true) :
    Eval D f envD setsD ↔ f.EvalOn R envP setsP := by
  classical
  induction f with
  | truth => rfl
  | equal i j =>
    simp only [Eval, Formula.EvalOn, henv]
    exact ⟨(fun h => J.vertex_value_injective h), congrArg (fun p => (J.vertex p).val)⟩
  | member i X => simpa only [Eval, Formula.EvalOn, henv] using hsets X (envP i)
  | insert i => simpa only [Eval, Formula.EvalOn, henv] using J.insert_iff (envP i)
  | remove i => simpa only [Eval, Formula.EvalOn, henv] using J.remove_iff (envP i)
  | successor i j =>
    simpa only [Eval, Formula.EvalOn, henv] using J.successor_iff (envP i) (envP j)
  | matching i j =>
    simpa only [Eval, Formula.EvalOn, henv] using J.matching_iff (envP i) (envP j)
  | neg f ih => exact not_congr (ih _ _ _ _ henv hsets)
  | conj f g ihf ihg => exact and_congr (ihf _ _ _ _ henv hsets) (ihg _ _ _ _ henv hsets)
  | implies f g ihf ihg => exact imp_congr (ihf _ _ _ _ henv hsets) (ihg _ _ _ _ henv hsets)
  | existsFO k f ih =>
    constructor
    · rintro ⟨v, hv, hf⟩
      let w : Fin k → P := fun i => J.vertex.symm ⟨v i, hv i⟩
      refine ⟨w, (ih _ _ _ _ ?_ hsets).mp hf⟩
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [w]
      · simpa using henv j
    · rintro ⟨w, hf⟩
      let v : Fin k → Nat := fun i => (J.vertex (w i)).val
      refine ⟨v, (fun i => (J.vertex (w i)).property), (ih _ _ _ _ ?_ hsets).mpr hf⟩
      intro i
      exact Fin.addCases (fun j => by simp [v]) (fun j => by simpa using henv j) i
  | allFO k f ih =>
    constructor
    · intro h w
      let v : Fin k → Nat := fun i => (J.vertex (w i)).val
      apply (ih _ _ _ _ ?_ hsets).mp (h v (fun i => (J.vertex (w i)).property))
      intro i
      exact Fin.addCases (fun j => by simp [v]) (fun j => by simpa using henv j) i
    · intro h v hv
      let w : Fin k → P := fun i => J.vertex.symm ⟨v i, hv i⟩
      apply (ih _ _ _ _ ?_ hsets).mpr (h w)
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [w]
      · simpa using henv j
  | allSet f ih =>
    constructor
    · intro h Y
      let X : Nat → Prop := fun x => ∃ hx : x ∈ D.domain,
        Y (J.vertex.symm ⟨x, hx⟩) = true
      have hX : ∀ x, X x → x ∈ D.domain := fun _ hx => hx.choose
      apply (ih _ _ _ _ henv ?_).mp (h X hX)
      intro Z p
      refine Fin.cases ?_ (fun Z => ?_) Z
      · simp [X, (J.vertex p).property]
      · simpa using hsets Z p
    · intro h X _hX
      let Y : P → Bool := fun p => decide (X (J.vertex p).val)
      apply (ih _ _ _ _ henv ?_).mpr (h Y)
      intro Z p
      refine Fin.cases ?_ (fun Z => ?_) Z
      · simp [Y]
      · simpa using hsets Z p

theorem satisfies (J : DomainInterpretation D R) (f : Formula 0 0) :
    Satisfies D f ↔ f.EvalOn R Fin.elim0 Fin.elim0 :=
  J.eval f Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0
    (fun i => Fin.elim0 i) (fun X => Fin.elim0 X)
end DomainInterpretation

#print axioms DomainInterpretation.eval
#print axioms DomainInterpretation.satisfies
end StackSorting.SparseEndpointMSO
