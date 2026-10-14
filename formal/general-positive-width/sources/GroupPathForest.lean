import FactorizationTree
import MarkedWordDecomposition

namespace StackSorting.Simon
open FactorizationTree

variable {V G : Type*} [Group G]

/-- The actual ordered edge word of a path with specified internal vertices. -/
def pathLetters (start : V) : List V → V → List (V × V)
  | [], finish => [(start, finish)]
  | v :: vs, finish => (start, v) :: pathLetters v vs finish

def pathValue (color : V → G) (edge : V × V) : G :=
  (color edge.1)⁻¹ * color edge.2

@[simp] theorem pathLetters_ne_nil (s : V) (vs : List V) (t : V) :
    pathLetters s vs t ≠ [] := by cases vs <;> simp [pathLetters]

theorem pathLetters_prod (color : V → G) (s : V) (vs : List V) (t : V) :
    ((pathLetters s vs t).map (pathValue color)).prod =
      (color s)⁻¹ * color t := by
  induction vs generalizing s with
  | nil => simp [pathLetters, pathValue]
  | cons v vs ih => simp [pathLetters, pathValue, ih, mul_assoc]

theorem pathLetters_append (s : V) (u : List V) (v : V) (rest : List V) (t : V) :
    pathLetters s (u ++ v :: rest) t =
      pathLetters s u v ++ pathLetters v rest t := by
  induction u generalizing s with
  | nil => simp [pathLetters]
  | cons a u ih => simp [pathLetters, ih]

/-- Edges of the successive completed segments. Endpoints are retained, so
these are genuinely consecutive pieces of one path. -/
def segmentPaths (s : V) : List (List V × V) → List (List (V × V))
  | [] => []
  | z :: zs => pathLetters s z.1 z.2 :: segmentPaths z.2 zs

def lastEndpoint (s : V) : List (List V × V) → V
  | [] => s
  | z :: zs => lastEndpoint z.2 zs

theorem pathLetters_decomposition (s : V) (blocks : List (List V × V))
    (rest : List V) (t : V) :
    pathLetters s ((blocks.flatMap fun z => z.1 ++ [z.2]) ++ rest) t =
      (segmentPaths s blocks).flatten ++ pathLetters (lastEndpoint s blocks) rest t := by
  induction blocks generalizing s with
  | nil => simp [segmentPaths, lastEndpoint]
  | cons z zs ih =>
    simp only [List.flatMap_cons, List.append_assoc, List.nil_append, List.cons_append,
      pathLetters_append, segmentPaths, lastEndpoint, List.flatten_cons]
    rw [ih]

omit [Group G] in
theorem lastEndpoint_color (color : V → G) (s : V) (blocks : List (List V × V))
    (e : G) (hs : color s = e) (hb : ∀ z ∈ blocks, color z.2 = e) :
    color (lastEndpoint s blocks) = e := by
  induction blocks generalizing s with
  | nil => exact hs
  | cons z zs ih =>
    exact ih z.2 (hb z (by simp)) (by intro r hr; exact hb r (by simp [hr]))

private theorem segmentPaths_properties (color : V → G) (e : G) (F : Finset G)
    (h : ℕ) (build : ∀ (s t : V) (vs : List V), (∀ v ∈ vs, color v ∈ F) →
      HasTree (pathValue color) (pathLetters s vs t) h) :
    ∀ (blocks : List (List V × V)) (start : V), color start = e →
      (∀ z ∈ blocks, color z.2 = e ∧ ∀ v ∈ z.1, color v ∈ F) →
      ∀ q ∈ segmentPaths start blocks,
        HasTree (pathValue color) q h ∧ (q.map (pathValue color)).prod = 1 := by
  intro blocks
  induction blocks with
  | nil => intro start hs hb q hq; simp [segmentPaths] at hq
  | cons z zs ih =>
    intro start hs hb q hq
    simp only [segmentPaths, List.mem_cons] at hq
    rcases hq with rfl | hq
    · refine ⟨build start z.2 z.1 (hb z (by simp)).2, ?_⟩
      rw [pathLetters_prod, hs, (hb z (by simp)).1, inv_mul_cancel]
    · exact ih z.2 (hb z (by simp)).1
        (by intro r hr; exact hb r (by simp [hr])) q hq

/-- A finite support of internal vertex colors, rather than inclusive prefix
values, is the strictly decreasing induction parameter. -/
theorem exists_group_path_tree_on_support (color : V → G) (F : Finset G) :
    ∀ (s t : V) (vs : List V), (∀ v ∈ vs, color v ∈ F) →
      HasTree (pathValue color) (pathLetters s vs t) (3 * F.card) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro s t vs hv
    have hvs : vs = [] := by
      by_contra hn
      obtain ⟨v, tail, rfl⟩ := List.exists_cons_of_ne_nil hn
      have := hv v (by simp)
      simp at this
    rw [hvs]
    exact hasTree_singleton (pathValue color) (s,t) 0
  | @insert e F he ih =>
    intro s t vs hv
    obtain ⟨blocks, rest, hvs, hb, hr⟩ :=
      exists_marked_decomposition (fun v => color v = e) vs
    have hin : ∀ z ∈ blocks, ∀ v ∈ z.1, color v ∈ F := by
      intro z hz v hvm
      have hm : color v ∈ insert e F := hv v (by
        rw [hvs]
        exact block_member_of_decomposition blocks rest hz hvm)
      exact (Finset.mem_insert.mp hm).resolve_left ((hb z hz).2 v hvm)
    have hrest : ∀ v ∈ rest, color v ∈ F := by
      intro v hvm
      have hm : color v ∈ insert e F := hv v (by
        rw [hvs]
        exact List.mem_append_right _ hvm)
      exact (Finset.mem_insert.mp hm).resolve_left (hr v hvm)
    have hcard : (insert e F).card = F.card + 1 := Finset.card_insert_of_notMem he
    cases blocks with
    | nil =>
      have heq : vs = rest := by simpa using hvs
      rw [heq]
      exact hasTree_mono (ih s t rest hrest) (by rw [hcard]; omega)
    | cons z zs =>
      have hfirst := ih s z.2 z.1 (hin z (by simp))
      have htail := ih (lastEndpoint z.2 zs) t rest hrest
      have hsegments : ∀ q ∈ segmentPaths z.2 zs,
          HasTree (pathValue color) q (3 * F.card) ∧
          (q.map (pathValue color)).prod = 1 :=
        segmentPaths_properties color e F (3 * F.card) ih zs z.2
          (hb z (by simp)).1 (by
            intro r hrm
            exact ⟨(hb r (by simp [hrm])).1, hin r (by simp [hrm])⟩)
      have hword : pathLetters s vs t = pathLetters s z.1 z.2 ++
          ((segmentPaths z.2 zs).flatten ++ pathLetters (lastEndpoint z.2 zs) rest t) := by
        rw [hvs, pathLetters_decomposition]
        simp [segmentPaths, lastEndpoint, List.append_assoc]
      cases hzs : zs with
      | nil =>
        have hword' : pathLetters s vs t =
            pathLetters s z.1 z.2 ++ pathLetters z.2 rest t := by
          simpa [hzs, segmentPaths, lastEndpoint] using hword
        rw [hword']
        have htail' : HasTree (pathValue color) (pathLetters z.2 rest t) (3 * F.card) := by
          simpa [hzs, lastEndpoint] using htail
        exact hasTree_mono (hasTree_binary hfirst htail') (by rw [hcard]; omega)
      | cons r rs =>
        have hnonempty : segmentPaths z.2 zs ≠ [] := by simp [hzs, segmentPaths]
        have hmiddle := hasTree_idempotent_blocks (pathValue color)
          (segmentPaths z.2 zs) (3 * F.card) hnonempty
          (by intro q hq; exact (hsegments q hq).1) 1 (one_mul 1)
          (by intro q hq; exact (hsegments q hq).2)
        have htail' := hasTree_mono htail (by omega : 3 * F.card ≤ 3 * F.card + 1)
        have hright := hasTree_binary hmiddle htail'
        have hfirst' := hasTree_mono hfirst (by omega : 3 * F.card ≤ (3 * F.card + 1) + 1)
        rw [hword]
        exact hasTree_mono (hasTree_binary hfirst' hright) (by rw [hcard]; omega)

theorem exists_group_path_tree [Fintype G] (color : V → G)
    (s t : V) (vs : List V) :
    HasTree (pathValue color) (pathLetters s vs t) (3 * Fintype.card G) := by
  classical
  simpa using exists_group_path_tree_on_support color Finset.univ s t vs
    (by intro v _; exact Finset.mem_univ (color v))

#print axioms exists_group_path_tree_on_support
#print axioms exists_group_path_tree
end StackSorting.Simon
