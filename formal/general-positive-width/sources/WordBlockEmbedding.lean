import IdempotentPadding

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord
variable {k : ℕ} {A B C D : Type*}
variable (G : Graph k A) (H : Graph k B) (G' : Graph k C) (H' : Graph k D)
variable (f : A → C) (g : B → D)
variable (hfr : ∀ i, (G.right i).map f = G'.right i)
variable (hgl : ∀ i, (H.left i).map g = H'.left i)

/-- A map of two actual quotient gluings needs preservation only of the two
interfaces used by the seam. The unused outer interfaces may change. -/
def mapSeam : Glued G H → Glued G' H' :=
  glueLift G H (fun a => inLeft G' H' (f a)) (fun b => inRight G' H' (g b)) (by
    rintro a b ⟨i,hi,hj⟩
    apply (inLeft_eq_inRight G' H' _ _).mpr
    refine ⟨i,?_,?_⟩
    · rw [← hfr i,hi]; rfl
    · rw [← hgl i,hj]; rfl)

@[simp] theorem mapSeam_left (a : A) :
    mapSeam G H G' H' f g hfr hgl (inLeft G H a) = inLeft G' H' (f a) := rfl
@[simp] theorem mapSeam_right (b : B) :
    mapSeam G H G' H' f g hfr hgl (inRight G H b) = inRight G' H' (g b) := rfl

theorem mapSeam_injective (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (mapSeam G H G' H' f g hfr hgl) := by
  apply glueLift_injective
  · exact (inLeft_injective G' H').comp hf
  · exact (inRight_injective G' H').comp hg
  · intro a b hab
    obtain ⟨i,hi,hj⟩ := (inLeft_eq_inRight G' H' _ _).mp hab
    rw [← hfr i] at hi
    rw [← hgl i] at hj
    obtain ⟨a',ha',hea⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨b',hb',heb⟩ := Option.map_eq_some_iff.mp hj
    have ea : a' = a := hf hea
    have eb : b' = b := hg heb
    exact ⟨i,ea ▸ ha',eb ▸ hb'⟩

theorem mapSeam_adj (hf : ∀ a b, G.Adj a b → G'.Adj (f a) (f b))
    (hg : ∀ a b, H.Adj a b → H'.Adj (g a) (g b))
    {a b} (hab : (glue G H).Adj a b) :
    (glue G' H').Adj (mapSeam G H G' H' f g hfr hgl a)
      (mapSeam G H G' H' f g hfr hgl b) := by
  rcases hab with ⟨x,y,hxy,rfl,rfl⟩ | ⟨x,y,hxy,rfl,rfl⟩
  · exact Or.inl ⟨f x,f y,hf x y hxy,rfl,rfl⟩
  · exact Or.inr ⟨g x,g y,hg x y hxy,rfl,rfl⟩

variable {G H G' H' f g hfr hgl}

theorem blockLeft_left (xs ys : List (Packed k)) (hx : xs ≠ []) (hy : ys ≠ []) (i : Fin k) :
    ((Packed.eval xs).graph.left i).map (blockLeft xs ys hx hy) =
      (Packed.eval (xs ++ ys)).graph.left i := by
  have h := (evalAppendIso xs ys hx hy).left i
  apply Option.map_injective (evalAppendIso xs ys hx hy).vertex.injective
  rw [Option.map_map]
  simpa [blockLeft, Function.comp_def, glue] using h.symm

theorem blockRight_right (xs ys : List (Packed k)) (hx : xs ≠ []) (hy : ys ≠ []) (i : Fin k) :
    ((Packed.eval ys).graph.right i).map (blockRight xs ys hx hy) =
      (Packed.eval (xs ++ ys)).graph.right i := by
  have h := (evalAppendIso xs ys hx hy).right i
  apply Option.map_injective (evalAppendIso xs ys hx hy).vertex.injective
  rw [Option.map_map]
  simpa [blockRight, Function.comp_def, glue] using h.symm

/-- The last factor of a nonempty word, retaining its surviving right ports. -/
noncomputable def lastColumn (xs : List (Packed k)) (P : Packed k) :
    P.Vertex → (Packed.eval (xs ++ [P])).Vertex := by
  cases xs with
  | nil => exact id
  | cons Q qs => exact blockRight (Q :: qs) [P] (by simp) (by simp)

/-- The first factor of a nonempty word, retaining its surviving left ports. -/
noncomputable def firstColumn (P : Packed k) (xs : List (Packed k)) :
    P.Vertex → (Packed.eval (P :: xs)).Vertex :=
  (Occurrence.head xs).column

theorem lastColumn_injective (xs : List (Packed k)) (P : Packed k) :
    Function.Injective (lastColumn xs P) := by
  cases xs with
  | nil => exact Function.injective_id
  | cons Q qs => exact blockRight_injective _ _ _ _

theorem firstColumn_injective (P : Packed k) (xs : List (Packed k)) :
    Function.Injective (firstColumn P xs) := Occurrence.column_injective _

theorem lastColumn_adj (xs : List (Packed k)) (P : Packed k) {v w}
    (hp : P.graph.Adj v w) :
    (Packed.eval (xs ++ [P])).graph.Adj (lastColumn xs P v) (lastColumn xs P w) := by
  cases xs with
  | nil => exact hp
  | cons Q qs => exact blockRight_adj _ _ _ _ hp

theorem firstColumn_adj (P : Packed k) (xs : List (Packed k)) {v w}
    (hp : P.graph.Adj v w) :
    (Packed.eval (P :: xs)).graph.Adj (firstColumn P xs v) (firstColumn P xs w) :=
  Occurrence.column_adj _ hp

theorem lastColumn_right (xs : List (Packed k)) (P : Packed k) (i : Fin k) :
    (P.graph.right i).map (lastColumn xs P) = (Packed.eval (xs ++ [P])).graph.right i := by
  cases xs with
  | nil => simp [lastColumn]
  | cons Q qs => exact blockRight_right _ _ _ _ i

theorem firstColumn_left (P : Packed k) (xs : List (Packed k)) (i : Fin k) :
    (P.graph.left i).map (firstColumn P xs) = (Packed.eval (P :: xs)).graph.left i := by
  cases xs with
  | nil => simp [firstColumn, Occurrence.column]
  | cons Q qs => rfl

#print axioms mapSeam_injective
#print axioms lastColumn_right
#print axioms firstColumn_left
end StackSorting.BiInterface.RepeatedColumn
