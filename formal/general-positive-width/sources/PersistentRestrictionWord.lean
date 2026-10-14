import PersistentRestrictionIdempotent

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord
variable {k : ℕ}

noncomputable def removePackedPersistent (P : Packed k) : Packed k where
  Vertex := ↥((Persistent P.graph)ᶜ)
  finite := inferInstance
  graph := removePersistent P.graph

/-- Exact whole-word commutation: the evaluated word of reduced factors is
isomorphic to deleting the persistent vertices from the original evaluated
word. This includes the actual surviving interfaces and adjacency. -/
noncomputable def restrictionEvalIso (e : Abstract k) (he : e * e = e)
    (ps : List (Packed.{0} k)) (hne : ps ≠ [])
    (hp : ∀ P ∈ ps, abstractGraph P.graph = e) :
    Iso (Packed.eval (ps.map removePackedPersistent)).graph
      (removePersistent (Packed.eval ps).graph) := by
  induction ps with
  | nil => exact (hne rfl).elim
  | cons P ps ih =>
    cases ps with
    | nil => exact identIso _
    | cons Q qs =>
      have htail : ∀ R ∈ Q :: qs, abstractGraph R.graph = e := by
        intro R hR
        exact hp R (by simp [hR])
      have hP : abstractGraph P.graph = e := hp P (by simp)
      have hT : abstractGraph (Packed.eval (Q :: qs)).graph = e :=
        eval_homogeneous_idempotent e he (Q :: qs) (by simp) htail
      have hcode : abstraction P.graph = abstraction (Packed.eval (Q :: qs)).graph :=
        congrArg Subtype.val (hP.trans hT.symm)
      have hmask (i : Fin k) : PersistentAt P.graph i ↔ PersistentAt (Packed.eval (Q :: qs)).graph i := by
        rw [persistentAt_code,persistentAt_code,hcode]
      exact transIso ((identIso (removePersistent P.graph)).glue (ih (by simp) htail))
        (restrictionGlueIso P.graph (Packed.eval (Q :: qs)).graph hmask)

/-- Persistent vertices have injective original port names. -/
noncomputable def persistentName {V : Type*} (G : Graph k V) (v : Persistent G) : Fin k :=
  Classical.choose v.property

theorem persistentName_spec {V : Type*} (G : Graph k V) (v : Persistent G) :
    G.left (persistentName G v) = some v.val := (Classical.choose_spec v.property).1

theorem persistentName_injective {V : Type*} (G : Graph k V) :
    Function.Injective (persistentName G) := by
  intro v w h
  apply Subtype.ext
  apply Option.some.inj
  exact (persistentName_spec G v).symm.trans
    ((congrArg G.left h).trans (persistentName_spec G w))

noncomputable instance persistentFintype {V : Type*} (G : Graph k V) : Fintype (Persistent G) :=
  Fintype.ofInjective (persistentName G) (persistentName_injective G)

/-- At most k actual vertices are deleted, independent of the number or size
of the factors. The bound concerns the actual product's persistent vertex set. -/
theorem persistent_card_le {V : Type*} (G : Graph k V) :
    Fintype.card (Persistent G) ≤ k := by
  simpa using Fintype.card_le_of_injective (persistentName G) (persistentName_injective G)

#print axioms restrictionEvalIso
#print axioms persistent_card_le
end StackSorting.BiInterface.RepeatedColumn
