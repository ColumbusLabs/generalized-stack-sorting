import SignedWordDeletion

namespace StackSorting.SignedWord
open StackSorting.FiniteGraph
attribute [local instance] Lean.Grind.Ring.intCast

/-- No produced word begins with T. The extra initial T matrix transition is
therefore immaterial, rather than an assumed physical transition. -/
def NoInitialT (p : Poly) : Prop := ∀ term ∈ p, term.2.head? ≠ some .t

theorem noInitialT_nil : NoInitialT [] := by simp [NoInitialT]
theorem noInitialT_one : NoInitialT one := by simp [NoInitialT, one]

theorem noInitialT_append {p q : Poly} (hp : NoInitialT p) (hq : NoInitialT q) :
    NoInitialT (p++q) := by
  intro term hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hp term hm
  · exact hq term hm

theorem noInitialT_prefix (a : Letter) (ha : a ≠ .t) (p : Poly) :
    NoInitialT (prefixLetter a p) := by
  intro term hm
  obtain ⟨term', _, rfl⟩ := List.mem_map.mp hm
  simpa only [List.head?_cons, ne_eq, Option.some.injEq] using ha

theorem noInitialT_negative {p : Poly} (h : NoInitialT p) : NoInitialT (negative p) := by
  intro term hm
  obtain ⟨term', hmem, rfl⟩ := List.mem_map.mp hm
  exact h term' hmem

theorem noInitialT_difference (p : Poly) : NoInitialT (difference p) :=
  noInitialT_append (noInitialT_prefix .b (by decide) p)
    (noInitialT_negative (noInitialT_prefix .z (by decide) p))

theorem F_noInitialT (w : Word) : NoInitialT (F w) := by
  cases w with
  | nil => exact noInitialT_one
  | cons a w =>
    cases a with
    | z => exact noInitialT_prefix .z (by decide) _
    | b => exact noInitialT_append (noInitialT_prefix .z (by decide) _) (noInitialT_prefix .z (by decide) _)
    | t => exact noInitialT_append (noInitialT_prefix .b (by decide) _) (noInitialT_prefix .z (by decide) _)

theorem J_noInitialT (w : Word) : NoInitialT (J w) := by
  cases w with
  | nil => exact noInitialT_one
  | cons a w =>
    cases a with
    | z => exact noInitialT_prefix .z (by decide) _
    | b => exact noInitialT_prefix .b (by decide) _
    | t => exact noInitialT_append (noInitialT_prefix .z (by decide) _) (noInitialT_difference _)

theorem K_noInitialT (w : Word) : NoInitialT (K w) := by
  cases w with
  | nil => exact noInitialT_nil
  | cons a w =>
    cases a with
    | z => exact noInitialT_nil
    | b => exact noInitialT_difference _
    | t => exact noInitialT_difference _

theorem U_noInitialT (w : Word) : NoInitialT (U w) :=
  noInitialT_append (F_noInitialT w) (K_noInitialT w)

def Homogeneous (n : Nat) (p : Poly) : Prop := ∀ term ∈ p, term.2.length = n

theorem homogeneous_nil (n : Nat) : Homogeneous n [] := by simp [Homogeneous]
theorem homogeneous_one : Homogeneous 0 one := by simp [Homogeneous, one]

theorem homogeneous_append {n : Nat} {p q : Poly}
    (hp : Homogeneous n p) (hq : Homogeneous n q) : Homogeneous n (p++q) := by
  intro term hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hp term hm
  · exact hq term hm

theorem homogeneous_prefix {n : Nat} {p : Poly} (a : Letter) (h : Homogeneous n p) :
    Homogeneous (n+1) (prefixLetter a p) := by
  intro term hm
  obtain ⟨term', hmem, rfl⟩ := List.mem_map.mp hm
  simpa only [List.length_cons] using congrArg Nat.succ (h term' hmem)

theorem homogeneous_negative {n : Nat} {p : Poly} (h : Homogeneous n p) :
    Homogeneous n (negative p) := by
  intro term hm
  obtain ⟨term', hmem, rfl⟩ := List.mem_map.mp hm
  exact h term' hmem

theorem homogeneous_difference {n : Nat} {p : Poly} (h : Homogeneous n p) :
    Homogeneous (n+1) (difference p) :=
  homogeneous_append (homogeneous_prefix .b h)
    (homogeneous_negative (homogeneous_prefix .z h))

theorem E_length (w : Word) : Homogeneous w.length (E w) := by
  cases w with
  | nil => exact homogeneous_one
  | cons a w => exact homogeneous_nil _

theorem J_length (w : Word) : Homogeneous w.length (J w) := by
  induction w with
  | nil => exact homogeneous_one
  | cons a w ih =>
    cases a with
    | z => exact homogeneous_prefix .z (E_length w)
    | b => exact homogeneous_prefix .b (E_length w)
    | t => exact homogeneous_append (homogeneous_prefix .z ih) (homogeneous_difference (E_length w))

theorem K_length (w : Word) : Homogeneous w.length (K w) := by
  induction w with
  | nil => exact homogeneous_nil _
  | cons a w ih =>
    cases a with
    | z => exact homogeneous_nil _
    | b => exact homogeneous_difference (E_length w)
    | t => exact homogeneous_difference ih

theorem F_length (w : Word) : Homogeneous w.length (F w) := by
  induction w with
  | nil => exact homogeneous_one
  | cons a w ih =>
    cases a with
    | z => exact homogeneous_prefix .z (J_length w)
    | b => exact homogeneous_append (homogeneous_prefix .z ih) (homogeneous_prefix .z (K_length w))
    | t => exact homogeneous_append (homogeneous_prefix .b ih) (homogeneous_prefix .z (K_length w))

theorem U_length (w : Word) : Homogeneous w.length (U w) :=
  homogeneous_append (F_length w) (K_length w)

theorem selected_length (a : Letter) (w : Word) : Homogeneous w.length (selected a w) := by
  cases a with
  | z => exact F_length w
  | b => exact U_length w
  | t => exact U_length w

/-- Every raw signed term, even a term that later cancels, decreases held height. -/
theorem heldDelete_length (w : Word) :
    ∀ term ∈ heldDelete w, term.2.length + 1 = w.length := by
  induction w with
  | nil => simp [heldDelete]
  | cons a w ih =>
    intro term hm
    rcases List.mem_append.mp hm with hm | hm
    · simpa only [List.length_cons] using congrArg Nat.succ (selected_length a w term hm)
    · obtain ⟨term', hmem, rfl⟩ := List.mem_map.mp hm
      simpa only [List.length_cons] using congrArg Nat.succ (ih term' hmem)

/-- The exact empty, height-one, and height-at-least-two unary boundary. -/
def AdmissibleWord (w : Word) : Prop :=
  w = [] ∨ w = [.z] ∨ ∃ a rest, (a = .z ∨ a = .b) ∧ w = .z::a::rest

def AdmissiblePoly (p : Poly) : Prop := ∀ term ∈ p, AdmissibleWord term.2

theorem admissible_append {p q : Poly} (hp : AdmissiblePoly p) (hq : AdmissiblePoly q) :
    AdmissiblePoly (p++q) := by
  intro term hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hp term hm
  · exact hq term hm

theorem admissible_prefix_z {p : Poly} (h : NoInitialT p) :
    AdmissiblePoly (prefixLetter .z p) := by
  intro term hm
  obtain ⟨term', hmem, rfl⟩ := List.mem_map.mp hm
  have ht := h term' hmem
  rcases term' with ⟨c, w⟩
  cases w with
  | nil => exact Or.inr (Or.inl rfl)
  | cons a w =>
    cases a with
    | z => exact Or.inr (Or.inr ⟨.z, w, Or.inl rfl, rfl⟩)
    | b => exact Or.inr (Or.inr ⟨.b, w, Or.inr rfl, rfl⟩)
    | t => exact False.elim (ht rfl)

theorem admissible_prefix_two (a : Letter) (ha : a=.z ∨ a=.b) (p : Poly) :
    AdmissiblePoly (prefixLetter .z (prefixLetter a p)) := by
  intro term hm
  obtain ⟨term', hmem, rfl⟩ := List.mem_map.mp hm
  obtain ⟨term'', _, rfl⟩ := List.mem_map.mp hmem
  exact Or.inr (Or.inr ⟨a, term''.2, ha, rfl⟩)

/-- Admissibility is preserved term by term, not merely after cancellation. -/
theorem heldDelete_admissible {w : Word} (h : AdmissibleWord w) :
    AdmissiblePoly (heldDelete w) := by
  rcases h with rfl | rfl | ⟨a, rest, ha, rfl⟩
  · simp [AdmissiblePoly, heldDelete]
  · intro term hm
    have he : heldDelete [.z] = one := rfl
    rw [he] at hm
    have ht : term = (1, []) := by simpa only [one, List.mem_singleton] using hm
    rw [ht]
    exact Or.inl rfl
  · rcases ha with rfl | rfl
    · change AdmissiblePoly (prefixLetter .z (J rest) ++
        prefixLetter .z (F rest ++ prefixLetter .z (heldDelete rest)))
      rw [prefix_append]
      exact admissible_append (admissible_prefix_z (J_noInitialT rest))
        (admissible_append (admissible_prefix_z (F_noInitialT rest))
          (admissible_prefix_two .z (Or.inl rfl) _))
    · change AdmissiblePoly ((prefixLetter .z (F rest) ++ prefixLetter .z (K rest)) ++
        prefixLetter .z (U rest ++ prefixLetter .b (heldDelete rest)))
      rw [prefix_append]
      exact admissible_append
        (admissible_append (admissible_prefix_z (F_noInitialT rest))
          (admissible_prefix_z (K_noInitialT rest)))
        (admissible_append (admissible_prefix_z (U_noInitialT rest))
          (admissible_prefix_two .b (Or.inr rfl) _))

variable {R : Type} [Lean.Grind.CommRing R]

theorem eval_congr_on_support (phi psi : Word → R) (p : Poly)
    (h : ∀ term ∈ p, phi term.2 = psi term.2) : eval phi p = eval psi p := by
  induction p with
  | nil => rfl
  | cons term p ih =>
    simp only [eval, h term (by simp), ih (fun term hm => h term (by simp [hm]))]

/-- Any two boundary extensions that agree off initial T have identical values
on each actual signed suffix channel. -/
theorem boundary_extension_independent (phi psi : Word → R)
    (h : ∀ w, w.head? ≠ some .t → phi w = psi w) (w : Word) :
    eval phi (F w) = eval psi (F w) ∧
    eval phi (J w) = eval psi (J w) ∧
    eval phi (K w) = eval psi (K w) := by
  exact ⟨eval_congr_on_support phi psi _ (fun term hm => h _ (F_noInitialT w term hm)),
    eval_congr_on_support phi psi _ (fun term hm => h _ (J_noInitialT w term hm)),
    eval_congr_on_support phi psi _ (fun term hm => h _ (K_noInitialT w term hm))⟩

#print axioms F_noInitialT
#print axioms J_noInitialT
#print axioms K_noInitialT
#print axioms boundary_extension_independent
#print axioms F_length
#print axioms U_length
#print axioms heldDelete_length
#print axioms heldDelete_admissible
end StackSorting.SignedWord
