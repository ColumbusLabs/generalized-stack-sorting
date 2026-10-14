import GluingIso
import TorsoCodeIso
import TorsoComposition

namespace StackSorting.BiInterface
variable {k : ℕ} {U V W X : Type*}

/-- The finite torso code is an actual congruence for partial-interface gluing.
Its proof reconstructs torso isomorphisms and compresses real quotient paths. -/
theorem abstraction_glue_congr (G : Graph k U) (G' : Graph k V)
    (H : Graph k W) (H' : Graph k X)
    (hG : abstraction G = abstraction G') (hH : abstraction H = abstraction H') :
    abstraction (glue G H) = abstraction (glue G' H') := by
  calc
    abstraction (glue G H) = abstraction (glue (torso G) (torso H)) :=
      (abstraction_glue_torsos G H).symm
    _ = abstraction (glue (torso G') (torso H')) :=
      ((torsoIsoOfCode hG).glue (torsoIsoOfCode hH)).abstraction_eq
    _ = abstraction (glue G' H') := abstraction_glue_torsos G' H'

#print axioms abstraction_glue_congr
end StackSorting.BiInterface
