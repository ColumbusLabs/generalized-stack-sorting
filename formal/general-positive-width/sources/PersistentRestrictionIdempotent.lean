import PersistentRestrictionGluing
import OrderedColumns

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord
variable {k : ℕ} {V : Type}

/-- Persistent-interface deletion preserves genuine semigroup idempotence.
This closes the extra premise needed to apply radius-one locality after the
persistent vertices have been removed. -/
theorem removePersistent_idempotent (G : Graph k V)
    (he : abstractGraph G * abstractGraph G = abstractGraph G) :
    abstractGraph (removePersistent G) * abstractGraph (removePersistent G) =
      abstractGraph (removePersistent G) := by
  have hcode : abstraction (glue G G) = abstraction G :=
    congrArg Subtype.val ((abstractGraph_glue G G).trans he)
  have hiso := restrictionGlueIso G G (fun _ => Iff.rfl)
  apply Subtype.ext
  calc
    (abstractGraph (removePersistent G) * abstractGraph (removePersistent G)).val =
        abstraction (glue (removePersistent G) (removePersistent G)) :=
      congrArg Subtype.val (abstractGraph_glue (removePersistent G) (removePersistent G)).symm
    _ = abstraction (removePersistent (glue G G)) := hiso.abstraction_eq
    _ = abstraction (removePersistent G) := removePersistent_code_congr _ _ hcode

/-- A homogeneous idempotent value has one homogeneous idempotent value after
persistent-interface deletion. Representatives supply a value, while exact
code congruence proves independence for every actual factor in the word. -/
theorem exists_removed_common_idempotent (e : Abstract k) (he : e * e = e)
    (ps : List (Packed.{0} k)) (hp : ∀ P ∈ ps, abstractGraph P.graph = e) :
    ∃ e' : Abstract k, e' * e' = e' ∧
      ∀ P ∈ ps, abstractGraph (removePersistent P.graph) = e' := by
  let G := Abstract.representative e
  have hG : abstractGraph G = e := Subtype.ext (Abstract.representative_spec e)
  refine ⟨abstractGraph (removePersistent G),?_,?_⟩
  · apply removePersistent_idempotent G
    rw [hG,he]
  · intro P hP
    apply Subtype.ext
    apply removePersistent_code_congr
    exact congrArg Subtype.val ((hp P hP).trans hG.symm)

#print axioms removePersistent_idempotent
#print axioms exists_removed_common_idempotent
end StackSorting.BiInterface.RepeatedColumn
