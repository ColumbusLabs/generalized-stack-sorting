import WordBlockEmbedding

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord
variable {k : ℕ}

noncomputable def rightWindowEmbed (H R : Packed k) (rs : List (Packed k)) :
    Glued H.graph R.graph → Glued H.graph (Packed.eval (R :: rs)).graph :=
  mapSeam H.graph R.graph H.graph (Packed.eval (R :: rs)).graph id (firstColumn R rs)
    (by intro i; simp) (firstColumn_left R rs)

private theorem rightWindowEmbed_left (H R : Packed k) (rs : List (Packed k)) (i : Fin k) :
    ((glue H.graph R.graph).left i).map (rightWindowEmbed H R rs) =
      (glue H.graph (Packed.eval (R :: rs)).graph).left i := by
  change ((H.graph.left i).map (inLeft H.graph R.graph)).map _ = _
  rw [Option.map_map]
  rfl

/-- The literal three-factor window embedded in its surrounding actual
quotient. Its left/right factors are precisely the last/first neighboring
letters of the surrounding words. -/
noncomputable def windowEmbed (ls : List (Packed k)) (L H R : Packed k)
    (rs : List (Packed k)) : Glued L.graph (glue H.graph R.graph) →
      Glued (Packed.eval (ls ++ [L])).graph (glue H.graph (Packed.eval (R :: rs)).graph) :=
  mapSeam L.graph (glue H.graph R.graph) (Packed.eval (ls ++ [L])).graph
    (glue H.graph (Packed.eval (R :: rs)).graph)
    (lastColumn ls L) (rightWindowEmbed H R rs)
    (lastColumn_right ls L) (rightWindowEmbed_left H R rs)

/-- The three genuine neighboring column images, allowing adjacent images to
overlap on their actual gluing seam. -/
def threeColumnSet (ls : List (Packed k)) (L H R : Packed k) (rs : List (Packed k)) :
    Set (Glued (Packed.eval (ls ++ [L])).graph (glue H.graph (Packed.eval (R :: rs)).graph)) :=
  Set.range (fun v => inLeft (Packed.eval (ls ++ [L])).graph
    (glue H.graph (Packed.eval (R :: rs)).graph) (lastColumn ls L v)) ∪
  Set.range (middleColumn (Packed.eval (ls ++ [L])).graph H.graph (Packed.eval (R :: rs)).graph) ∪
  Set.range (fun v => inRight (Packed.eval (ls ++ [L])).graph
    (glue H.graph (Packed.eval (R :: rs)).graph)
    (inRight H.graph (Packed.eval (R :: rs)).graph (firstColumn R rs v)))

theorem windowEmbed_injective (ls : List (Packed k)) (L H R : Packed k)
    (rs : List (Packed k)) : Function.Injective (windowEmbed ls L H R rs) := by
  apply mapSeam_injective
  · exact lastColumn_injective ls L
  · exact mapSeam_injective _ _ _ _ _ _ _ _ Function.injective_id (firstColumn_injective R rs)

theorem windowEmbed_adj (ls : List (Packed k)) (L H R : Packed k) (rs : List (Packed k))
    {x y} (h : (glue L.graph (glue H.graph R.graph)).Adj x y) :
    (glue (Packed.eval (ls ++ [L])).graph (glue H.graph (Packed.eval (R :: rs)).graph)).Adj
      (windowEmbed ls L H R rs x) (windowEmbed ls L H R rs y) := by
  apply mapSeam_adj _ _ _ _ _ _ _ _ (fun _ _ h => lastColumn_adj ls L h) ?_ h
  intro a b hab
  exact mapSeam_adj _ _ _ _ _ _ _ _ (by intros; assumption)
    (fun _ _ h => firstColumn_adj R rs h) hab

theorem windowEmbed_mem (ls : List (Packed k)) (L H R : Packed k)
    (rs : List (Packed k)) (q : Glued L.graph (glue H.graph R.graph)) :
    windowEmbed ls L H R rs q ∈ threeColumnSet ls L H R rs := by
  induction q using Quotient.inductionOn with | h q =>
    cases q with
    | inl v => exact Or.inl (Or.inl ⟨v,rfl⟩)
    | inr q =>
      induction q using Quotient.inductionOn with | h q =>
        cases q with
        | inl v => exact Or.inl (Or.inr ⟨v,rfl⟩)
        | inr v => exact Or.inr ⟨v,rfl⟩

@[simp] theorem windowEmbed_middle (ls : List (Packed k)) (L H R : Packed k)
    (rs : List (Packed k)) (v : H.Vertex) :
    windowEmbed ls L H R rs (middleColumn L.graph H.graph R.graph v) =
      middleColumn (Packed.eval (ls ++ [L])).graph H.graph (Packed.eval (R :: rs)).graph v := rfl

/-- Radius one in the original graph, not only a path in a surrogate torso:
every globally connected pair in the selected middle column has an actual
finite walk all of whose internal vertices lie in the three neighboring
column images. No locality or path witness is assumed as input. -/
theorem idempotent_restricted_three_column_walk (e : Abstract k) (he : e * e = e)
    (ls rs : List (Packed.{0} k)) (L H R : Packed.{0} k)
    (hls : ∀ P ∈ ls ++ [L], abstractGraph P.graph = e)
    (hrs : ∀ P ∈ R :: rs, abstractGraph P.graph = e)
    (x y : H.Vertex)
    (hxy : Reach (glue (Packed.eval (ls ++ [L])).graph
      (glue H.graph (Packed.eval (R :: rs)).graph)).Adj
      (middleColumn (Packed.eval (ls ++ [L])).graph H.graph (Packed.eval (R :: rs)).graph x)
      (middleColumn (Packed.eval (ls ++ [L])).graph H.graph (Packed.eval (R :: rs)).graph y)) :
    Through (glue (Packed.eval (ls ++ [L])).graph
      (glue H.graph (Packed.eval (R :: rs)).graph)).Adj
      (threeColumnSet ls L H R rs)
      (middleColumn (Packed.eval (ls ++ [L])).graph H.graph (Packed.eval (R :: rs)).graph x)
      (middleColumn (Packed.eval (ls ++ [L])).graph H.graph (Packed.eval (R :: rs)).graph y) := by
  have hp := (idempotent_three_factor_locality e he (ls ++ [L]) (R :: rs)
    (by simp) (by simp) hls hrs L H R (by simp) (by simp) x y).mp hxy
  exact hp.map (windowEmbed ls L H R rs)
    (fun _ _ h => windowEmbed_adj ls L H R rs h)
    (fun q _ => windowEmbed_mem ls L H R rs q)

#print axioms idempotent_restricted_three_column_walk
end StackSorting.BiInterface.RepeatedColumn
