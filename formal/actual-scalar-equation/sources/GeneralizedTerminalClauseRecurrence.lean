import GeneralizedTerminalClauseValuation

/-! The recursive terminal-clause identity used by the exceptional-b channel.
It is derived from actual finite valuation, including the C_0 boundary. -/
namespace StackSorting.FiniteInclusionExclusion

theorem valuation_map (indices : List Nat) (f : Nat → Nat) (g : List Nat → Int) :
    valuation (indices.map f) g = valuation indices (fun J => g (J.map f)) := by
  induction indices generalizing g with
  | nil => rfl
  | cons i indices ih =>
    simp only [List.map_cons, valuation, ih]
    rfl

end StackSorting.FiniteInclusionExclusion
namespace StackSorting.Generalized.Decorated
open StackSorting.FiniteInclusionExclusion

theorem zeroFace_succ_map (m : Nat) (J : List Nat) :
    zeroFace (m+1) (J.map Nat.succ) = .B :: zeroFace m J := by
  simp only [zeroFace,List.range_succ_eq_map,List.map_cons,List.map_map]
  have hz : 0 ∉ J.map Nat.succ := by simp
  simp only [hz,ite_false,List.cons.injEq,true_and]
  apply List.map_congr_left
  intro j _
  simp

theorem zeroFace_succ_zero_map (m : Nat) (J : List Nat) :
    zeroFace (m+1) (0 :: J.map Nat.succ) = .Z :: zeroFace m J := by
  simp only [zeroFace,List.range_succ_eq_map,List.map_cons,List.map_map]
  simp only [List.mem_cons, true_or, ite_true, List.cons.injEq, true_and]
  apply List.map_congr_left
  intro j _
  simp

theorem zeroFace_empty (m : Nat) : zeroFace m [] = List.replicate m .B := by
  unfold zeroFace
  have hm : ∀ indices : List Nat, indices.map (fun _ => Factor.B) = List.replicate indices.length .B := by
    intro indices
    induction indices with
    | nil => rfl
    | cons i indices ih => simp [ih,List.replicate_succ]
  simpa using hm (List.range m)

theorem zeroFace_succ_first (m : Nat) :
    zeroFace (m+1) [0] = .Z :: List.replicate m .B := by
  simpa [zeroFace_empty] using zeroFace_succ_zero_map m []

theorem unary_append_factor {P : State} (hu : Unary P) {factor : Factor}
    (hf : factor = .Z ∨ factor = .B ∨ factor = .T) : Unary (P ++ [factor]) := by
  intro f hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hu f hm
  · have he : f = factor := by simpa using hm
    simpa [he] using hf

theorem completion_terminal_clause_valuation_eval {P : State} (hu : Unary P) (m n : Nat) :
    (completionCount (P ++ [.C m]) n : Int) =
      valuation (List.range m) (fun J => (completionCount (P ++ zeroFace m J) n : Int)) := by
  rw [completion_terminal_clause_valuation hu m n, valuation_eq_signed_sum]
  simp only [sign_eq_power]

/-- The three-term exceptional terminal-clause recursion is an actual distinct
output cardinality identity. In particular m=0 uses rejected C_0 exactly. -/
theorem completion_terminal_clause_step {P : State} (hu : Unary P) (m n : Nat) :
    (completionCount (P ++ [.C (m+1)]) n : Int) =
      (completionCount (P ++ [.B,.C m]) n : Int) +
      (completionCount (P ++ (.Z :: List.replicate m .B)) n : Int) -
      (completionCount (P ++ [.Z,.C m]) n : Int) := by
  have hB := completion_terminal_clause_valuation_eval
    (unary_append_factor hu (factor := .B) (by simp)) m n
  have hZ := completion_terminal_clause_valuation_eval
    (unary_append_factor hu (factor := .Z) (by simp)) m n
  rw [completion_terminal_clause_valuation_eval hu (m+1) n,
    List.range_succ_eq_map, valuation, valuation_map, valuation_map]
  simp only [zeroFace_succ_first,zeroFace_succ_map,zeroFace_succ_zero_map]
  simp only [List.append_assoc,List.singleton_append] at hB hZ
  rw [← hB,← hZ]
  omega

#check completion_terminal_clause_step
#print axioms completion_terminal_clause_step
end StackSorting.Generalized.Decorated
