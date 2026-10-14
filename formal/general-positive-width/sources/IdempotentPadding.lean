import OrderedColumns

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord
variable {k : ℕ} {U V W X Y : Type*}

/-- The actual inclusion of the middle of three quotient-glued factors. -/
noncomputable def middleColumn (G : Graph k U) (H : Graph k V) (K : Graph k W) (v : V) :
    Glued G (glue H K) := inRight G (glue H K) (inLeft H K v)

/-- Both sides may be replaced independently by equal-abstraction factors.
This statement preserves arbitrary interior endpoints in the middle factor. -/
theorem replace_both_padding (G : Graph k U) (H : Graph k V) (K : Graph k W)
    (G' : Graph k X) (K' : Graph k Y)
    (hG : abstraction G = abstraction G') (hK : abstraction K = abstraction K')
    (x y : V) :
    Reach (glue G (glue H K)).Adj (middleColumn G H K x) (middleColumn G H K y) ↔
      Reach (glue G' (glue H K')).Adj (middleColumn G' H K' x) (middleColumn G' H K' y) := by
  have hl := replace_left_padding G (glue H K) G' hG (inLeft H K x) (inLeft H K y)
  have ha := reach_iso_iff (associatorIso G' H K)
    (inLeft (glue G' H) K (inRight G' H x))
    (inLeft (glue G' H) K (inRight G' H y))
  have hr := replace_right_padding (glue G' H) K K' hK (inRight G' H x) (inRight G' H y)
  have hb := reach_iso_iff (associatorIso G' H K')
    (inLeft (glue G' H) K' (inRight G' H x))
    (inLeft (glue G' H) K' (inRight G' H y))
  exact hl.trans (ha.trans (hr.trans hb.symm))

/-- A homogeneous idempotent nonempty padding word has the exact code of
any one of its pieces, not just an assumed semantic summary. -/
theorem homogeneous_padding_code (e : Abstract k) (he : e * e = e)
    (ps : List (Packed.{0} k)) (hne : ps ≠ [])
    (hp : ∀ P ∈ ps, abstractGraph P.graph = e)
    (P : Packed.{0} k) (hP : abstractGraph P.graph = e) :
    abstraction (Packed.eval ps).graph = abstraction P.graph := by
  exact congrArg Subtype.val ((eval_homogeneous_idempotent e he ps hne hp).trans hP.symm)

/-- Genuine radius-one padding reduction for a repeated idempotent block:
the whole nonempty left and right blocks can be replaced by their neighboring
letters. The conclusion is an actual finite walk in a three-factor quotient.
The center itself need not have the common abstraction. -/
theorem idempotent_three_factor_locality (e : Abstract k) (he : e * e = e)
    (ls rs : List (Packed.{0} k)) (hl : ls ≠ []) (hr : rs ≠ [])
    (hls : ∀ P ∈ ls, abstractGraph P.graph = e)
    (hrs : ∀ P ∈ rs, abstractGraph P.graph = e)
    (L H R : Packed.{0} k)
    (hL : L ∈ ls) (hR : R ∈ rs) (x y : H.Vertex) :
    Reach (glue (Packed.eval ls).graph (glue H.graph (Packed.eval rs).graph)).Adj
      (middleColumn (Packed.eval ls).graph H.graph (Packed.eval rs).graph x)
      (middleColumn (Packed.eval ls).graph H.graph (Packed.eval rs).graph y) ↔
    Reach (glue L.graph (glue H.graph R.graph)).Adj
      (middleColumn L.graph H.graph R.graph x)
      (middleColumn L.graph H.graph R.graph y) :=
  replace_both_padding _ _ _ _ _
    (homogeneous_padding_code e he ls hl hls L (hls L hL))
    (homogeneous_padding_code e he rs hr hrs R (hrs R hR)) x y

/-- The boundary-column variant needs only its one neighboring factor. -/
theorem idempotent_first_factor_locality (e : Abstract k) (he : e * e = e)
    (rs : List (Packed.{0} k)) (hr : rs ≠ [])
    (hrs : ∀ P ∈ rs, abstractGraph P.graph = e)
    (H R : Packed.{0} k) (hR : R ∈ rs) (x y : H.Vertex) :
    Reach (glue H.graph (Packed.eval rs).graph).Adj
      (inLeft H.graph (Packed.eval rs).graph x) (inLeft H.graph (Packed.eval rs).graph y) ↔
    Reach (glue H.graph R.graph).Adj
      (inLeft H.graph R.graph x) (inLeft H.graph R.graph y) :=
  replace_right_padding _ _ _ (homogeneous_padding_code e he rs hr hrs R (hrs R hR)) x y

/-- The symmetric boundary-column variant. -/
theorem idempotent_last_factor_locality (e : Abstract k) (he : e * e = e)
    (ls : List (Packed.{0} k)) (hl : ls ≠ [])
    (hls : ∀ P ∈ ls, abstractGraph P.graph = e)
    (L H : Packed.{0} k) (hL : L ∈ ls) (x y : H.Vertex) :
    Reach (glue (Packed.eval ls).graph H.graph).Adj
      (inRight (Packed.eval ls).graph H.graph x) (inRight (Packed.eval ls).graph H.graph y) ↔
    Reach (glue L.graph H.graph).Adj
      (inRight L.graph H.graph x) (inRight L.graph H.graph y) :=
  replace_left_padding _ _ _ (homogeneous_padding_code e he ls hl hls L (hls L hL)) x y

#print axioms idempotent_three_factor_locality
#print axioms idempotent_first_factor_locality
#print axioms idempotent_last_factor_locality
end StackSorting.BiInterface.RepeatedColumn
