import ContainerMachine
import EqualBasis

/-! Corollary 4: a genuinely finite forbidden set for the container class,
and basis elements of unbounded lengths for its generated output class.
The imported infinite-basis theorem concerns the literal original machine. -/
set_option linter.unusedSimpArgs false
namespace StackSorting.Generalized.Container
open BasisFamily (delete MinimalForbidden)

/-- A finite enumeration of all words of fixed length over a finite alphabet. -/
def words (alphabet : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => alphabet.flatMap (fun a => (words alphabet n).map (a :: ·))

theorem mem_words {alphabet q : List Nat} {n : Nat} :
    q ∈ words alphabet n ↔ q.length = n ∧ ∀ a ∈ q, a ∈ alphabet := by
  induction n generalizing q with
  | zero => simp [words]; intro h; simp [h]
  | succ n ih =>
    cases q with
    | nil => simp [words]
    | cons a q =>
      simp only [words, List.mem_flatMap, List.mem_map, List.cons.injEq]
      constructor
      · rintro ⟨b, hb, v, hv, hba, hvq⟩
        subst b; subst v
        obtain ⟨hl, hm⟩ := ih.mp hv
        exact ⟨by simp [hl], by intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact hb; exact hm x hx⟩
      · rintro ⟨hl, hm⟩
        refine ⟨a, hm a (by simp), q, ih.mpr ⟨by simpa using hl, ?_⟩, rfl, rfl⟩
        intro x hx
        exact hm x (by simp [hx])

/-- An explicit finite list for the canonical set `S_r ⊕ 1`. -/
def forbiddenList (r : Nat) : List (List Nat) :=
  ((words (List.range r) r).filter (fun q => q.isPerm (List.range r))).map (· ++ [r])

theorem mem_forbiddenList {r : Nat} {p : List Nat} :
    p ∈ forbiddenList r ↔ Forbidden r p := by
  simp only [forbiddenList, List.mem_map, List.mem_filter, List.isPerm_iff]
  constructor
  · rintro ⟨q, ⟨_, hp⟩, he⟩
    exact ⟨q, hp, he.symm⟩
  · rintro ⟨q, hp, rfl⟩
    refine ⟨q, ⟨mem_words.mpr ⟨?_, ?_⟩, hp⟩, rfl⟩
    · simpa using hp.length_eq
    · exact hp.subset

/-- Finite-basis certificate for the container's avoidance presentation. -/
theorem finitely_based_container (r : Nat) :
    ∃ F : List (List Nat), ∀ xs, Avoids r xs ↔
      ∀ p ∈ F, ¬ Occurs (r+1) p xs := by
  exact ⟨forbiddenList r, fun xs => by simp only [Avoids, mem_forbiddenList]⟩

/-- With zero-based labels these are the familiar patterns 123 and 213. -/
theorem forbiddenList_two : forbiddenList 2 = [[0, 1, 2], [1, 0, 2]] := by decide

theorem avoids_two_iff (xs : List Nat) :
    Avoids 2 xs ↔ ¬ Occurs 3 [0, 1, 2] xs ∧ ¬ Occurs 3 [1, 0, 2] xs := by
  have hf : Avoids 2 xs ↔ ∀ p ∈ forbiddenList 2, ¬ Occurs 3 p xs := by
    simp only [Avoids, mem_forbiddenList]
  simpa [forbiddenList_two] using hf

/-- Literal generated-side minimal forbidden permutations for the container
machine. Deletions retain their original labels, exactly as in the reviewed
original-machine theorem; strict increasing input therefore matters. -/
def ContainerMinimal (r s : Nat) (bypass : Bool) (n : Nat) (p : List Nat) : Prop :=
  p.Perm (List.range n) ∧ ¬ CRun r s bypass [] (List.range n) p [] ∧
    ∀ a, a < n → CRun r s bypass [] (delete a (List.range n)) (delete a p) []

theorem containerMinimal_iff {r s : Nat} (hr : 0 < r) (hs : 0 < s)
    (bypass : Bool) (n : Nat) (p : List Nat) :
    ContainerMinimal r s bypass n p ↔ MinimalForbidden r s n p := by
  have hg := generates_iff hr hs bypass (List.range n) p List.pairwise_lt_range
  have hd : ∀ a, CRun r s bypass [] (delete a (List.range n)) (delete a p) [] ↔
      Run r s [] (delete a (List.range n)) (delete a p) [] := by
    intro a
    apply generates_iff hr hs bypass
    exact List.pairwise_lt_range.sublist List.filter_sublist
  simp only [ContainerMinimal, MinimalForbidden, hg, hd]

/-- Pattern closure transferred through the literal simulation. A retained
subword is relabelled in increasing order, as in standardization. -/
theorem generated_filter_map {r s : Nat} (hr : 0 < r) (hs : 0 < s)
    (bypass : Bool) {input output : List Nat}
    (h : CRun r s bypass [] input output []) (hi : input.Pairwise (· < ·))
    (keep : Nat → Bool) (f : Nat → Nat)
    (hi' : ((input.filter keep).map f).Pairwise (· < ·)) :
    CRun r s bypass [] ((input.filter keep).map f) ((output.filter keep).map f) [] := by
  have ho := (generates_iff hr hs bypass input output hi).mp h
  have hp := (ho.filter keep).map f
  apply (generates_iff hr hs bypass _ _ hi').mpr
  simpa using hp

/-- Every proper retained-token pattern of a minimal forbidden permutation
is generated, including its usual standardization. -/
theorem ContainerMinimal.proper_patterns {r s n : Nat} (hr : 0 < r) (hs : 0 < s)
    {bypass : Bool} {p : List Nat} (h : ContainerMinimal r s bypass n p)
    (keep : Nat → Bool) (proper : ∃ a, a < n ∧ keep a = false) (f : Nat → Nat)
    (hi : (((List.range n).filter keep).map f).Pairwise (· < ·)) :
    CRun r s bypass [] (((List.range n).filter keep).map f) ((p.filter keep).map f) [] := by
  have hp := (containerMinimal_iff hr hs bypass n p).mp h
  exact (generates_iff hr hs bypass _ _ hi).mpr (hp.proper_filter_map keep proper f)

/-- **Corollary 4**, with or without bypass, for every `r,s ≥ 2` except `(2,2)`:
the generated class has minimal forbidden permutations beyond every bound.
No finite computation or additional mathematical axiom is used. -/
theorem infinite_basis (r s : Nat) (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hne : ¬ (r = 2 ∧ s = 2)) (bypass : Bool) :
    ∀ bound, ∃ p, bound < p.length ∧ ContainerMinimal r s bypass p.length p := by
  intro bound
  obtain ⟨p, hl, hp⟩ := (Equal.infinite_basis_classification r s hr hs hne).1 bound
  exact ⟨p, hl, (containerMinimal_iff (by omega) (by omega) bypass _ _).mpr hp⟩

/-- One statement combines finite container avoidance with infinite output
basis, exactly the counterexample requested in Vatter's question. -/
theorem corollary4 (r s : Nat) (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hne : ¬ (r = 2 ∧ s = 2)) :
    (∃ F : List (List Nat), ∀ xs, Avoids r xs ↔
      ∀ p ∈ F, ¬ Occurs (r+1) p xs) ∧
    (∀ bypass bound, ∃ p, bound < p.length ∧ ContainerMinimal r s bypass p.length p) :=
  ⟨finitely_based_container r, fun bypass => infinite_basis r s hr hs hne bypass⟩

/-- In particular the `Av(123,213)` container gives infinite output bases
for every selectable-pop width `s ≥ 3`. -/
theorem corollary4_two (s : Nat) (hs : 3 ≤ s) (bypass : Bool) :
    (∀ xs, Avoids 2 xs ↔ ¬ Occurs 3 [0,1,2] xs ∧ ¬ Occurs 3 [1,0,2] xs) ∧
    (∀ bound, ∃ p, bound < p.length ∧ ContainerMinimal 2 s bypass p.length p) :=
  ⟨avoids_two_iff, infinite_basis 2 s (by omega) (by omega) (by omega) bypass⟩

#print axioms finitely_based_container
#print axioms forbiddenList_two
#print axioms containerMinimal_iff
#print axioms generated_filter_map
#print axioms ContainerMinimal.proper_patterns
#print axioms infinite_basis
#print axioms corollary4
#print axioms corollary4_two
end StackSorting.Generalized.Container
