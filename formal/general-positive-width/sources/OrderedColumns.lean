import PaddingReachability
import PathWordConstruction
import FiniteAbstractionSemigroup

/-!
Actual ordered columns of a heterogeneous nonempty graph word. All injections
below land in the existing right-associated quotient evaluation, not a new
axiomatic model of a word.
-/

universe u
namespace StackSorting.BiInterface.RepeatedColumn
open PathWord
variable {k : ℕ}

noncomputable def transIso {A B C : Type*} {G : Graph k A} {H : Graph k B} {K : Graph k C}
    (e : Iso G H) (f : Iso H K) : Iso G K where
  vertex := e.vertex.trans f.vertex
  adj := by intro x y; exact (f.adj _ _).trans (e.adj x y)
  left := by
    intro i
    change (G.left i).map (fun x => f.vertex (e.vertex x)) = K.left i
    simpa only [Option.map_map, Function.comp_def] using
      (congrArg (Option.map f.vertex) (e.left i)).trans (f.left i)
  right := by
    intro i
    change (G.right i).map (fun x => f.vertex (e.vertex x)) = K.right i
    simpa only [Option.map_map, Function.comp_def] using
      (congrArg (Option.map f.vertex) (e.right i)).trans (f.right i)

/-- A chosen occurrence, not mere membership: repeated equal letters remain
separate columns with separate indices. -/
inductive Occurrence (P : Packed.{u} k) : List (Packed.{u} k) → Type (u+1)
  | head (ps) : Occurrence P (P :: ps)
  | tail {Q ps} : Occurrence P ps → Occurrence P (Q :: ps)

namespace Occurrence
variable {P Q : Packed k} {ps : List (Packed k)}

def index : {ps : List (Packed k)} → Occurrence P ps → ℕ
  | _, .head _ => 0
  | _, .tail h => h.index + 1

theorem ne_nil (h : Occurrence P ps) : ps ≠ [] := by
  cases h <;> simp

theorem index_lt (h : Occurrence P ps) : h.index < ps.length := by
  induction h with
  | head ps => simp [index]
  | tail h ih => simpa [index] using Nat.succ_lt_succ ih

/-- The actual quotient inclusion of a specific ordered letter. -/
noncomputable def column : {ps : List (Packed k)} → (h : Occurrence P ps) → P.Vertex → (Packed.eval ps).Vertex
  | _, .head [] => id
  | _, .head (Q :: qs) => inLeft P.graph (Packed.eval (Q :: qs)).graph
  | _, .tail (ps := []) h => nomatch h
  | _, .tail (Q := Q) (ps := R :: rs) h =>
      fun v => inRight Q.graph (Packed.eval (R :: rs)).graph (column h v)

theorem column_injective (h : Occurrence P ps) : Function.Injective h.column := by
  induction h with
  | head ps =>
    cases ps with
    | nil => exact Function.injective_id
    | cons Q qs => exact inLeft_injective _ _
  | @tail Q ps h ih =>
    cases ps with
    | nil => exact (h.ne_nil rfl).elim
    | cons R rs => exact (inRight_injective _ _).comp ih

theorem column_adj (h : Occurrence P ps) {v w : P.Vertex} (hp : P.graph.Adj v w) :
    (Packed.eval ps).graph.Adj (h.column v) (h.column w) := by
  induction h with
  | head ps =>
    cases ps with
    | nil => exact hp
    | cons Q qs => exact Or.inl ⟨v,w,hp,rfl,rfl⟩
  | @tail Q ps h ih =>
    cases ps with
    | nil => exact (h.ne_nil rfl).elim
    | cons R rs => exact Or.inr ⟨h.column v,h.column w,ih,rfl,rfl⟩

/-- Global connectivity contains every finite walk of the chosen factor. -/
theorem column_reach (h : Occurrence P ps) {v w : P.Vertex}
    (hp : Reach P.graph.Adj v w) :
    Reach (Packed.eval ps).graph.Adj (h.column v) (h.column w) :=
  hp.map h.column (by intro a b hab; exact h.column_adj hab) (by intros; trivial)

/-- Prefixing preserves the selected occurrence, shifting its index exactly. -/
def prepend (xs : List (Packed k)) (h : Occurrence P ps) : Occurrence P (xs ++ ps) :=
  match xs with
  | [] => h
  | _ :: xs => .tail (prepend xs h)

@[simp] theorem prepend_index (xs : List (Packed k)) (h : Occurrence P ps) :
    (h.prepend xs).index = xs.length + h.index := by
  induction xs with
  | nil => simp [prepend]
  | cons Q xs ih => simp [prepend, index, ih, Nat.add_assoc, Nat.add_comm]

end Occurrence

/-- Reassociation of a nonempty ordered concatenation uses the already proved
quotient associator. No identity graph is assumed. -/
noncomputable def evalAppendIso (xs ys : List (Packed k)) (hx : xs ≠ []) (hy : ys ≠ []) :
    Iso (Packed.eval (xs ++ ys)).graph
      (glue (Packed.eval xs).graph (Packed.eval ys).graph) := by
  induction xs with
  | nil => exact (hx rfl).elim
  | cons P xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => exact (hy rfl).elim
      | cons Q qs => exact identIso _
    | cons Q qs =>
      have e := (identIso P.graph).glue (ih (by simp))
      exact transIso e (associatorIso P.graph (Packed.eval (Q :: qs)).graph
        (Packed.eval ys).graph).symm

/-- Include an initial nonempty consecutive block into the actual product. -/
noncomputable def blockLeft (xs ys : List (Packed k)) (hx : xs ≠ []) (hy : ys ≠ []) :
    (Packed.eval xs).Vertex → (Packed.eval (xs ++ ys)).Vertex :=
  fun v => (evalAppendIso xs ys hx hy).vertex.symm
    (inLeft (Packed.eval xs).graph (Packed.eval ys).graph v)

/-- Include a final nonempty consecutive block into the actual product. -/
noncomputable def blockRight (xs ys : List (Packed k)) (hx : xs ≠ []) (hy : ys ≠ []) :
    (Packed.eval ys).Vertex → (Packed.eval (xs ++ ys)).Vertex :=
  fun v => (evalAppendIso xs ys hx hy).vertex.symm
    (inRight (Packed.eval xs).graph (Packed.eval ys).graph v)

theorem blockLeft_injective (xs ys : List (Packed k)) (hx : xs ≠ []) (hy : ys ≠ []) :
    Function.Injective (blockLeft xs ys hx hy) :=
  (evalAppendIso xs ys hx hy).vertex.symm.injective.comp (inLeft_injective _ _)

theorem blockRight_injective (xs ys : List (Packed k)) (hx : xs ≠ []) (hy : ys ≠ []) :
    Function.Injective (blockRight xs ys hx hy) :=
  (evalAppendIso xs ys hx hy).vertex.symm.injective.comp (inRight_injective _ _)

theorem blockLeft_adj (xs ys : List (Packed k)) (hx : xs ≠ []) (hy : ys ≠ [])
    {v w} (hp : (Packed.eval xs).graph.Adj v w) :
    (Packed.eval (xs ++ ys)).graph.Adj (blockLeft xs ys hx hy v) (blockLeft xs ys hx hy w) := by
  apply ((evalAppendIso xs ys hx hy).adj _ _).mp
  simpa [blockLeft] using (show (glue (Packed.eval xs).graph (Packed.eval ys).graph).Adj
    (inLeft _ _ v) (inLeft _ _ w) from Or.inl ⟨v,w,hp,rfl,rfl⟩)

theorem blockRight_adj (xs ys : List (Packed k)) (hx : xs ≠ []) (hy : ys ≠ [])
    {v w} (hp : (Packed.eval ys).graph.Adj v w) :
    (Packed.eval (xs ++ ys)).graph.Adj (blockRight xs ys hx hy v) (blockRight xs ys hx hy w) := by
  apply ((evalAppendIso xs ys hx hy).adj _ _).mp
  simpa [blockRight] using (show (glue (Packed.eval xs).graph (Packed.eval ys).graph).Adj
    (inRight _ _ v) (inRight _ _ w) from Or.inr ⟨v,w,hp,rfl,rfl⟩)

/-- Any nonempty word of one idempotent abstract value evaluates to that value.
This is a conclusion about the abstraction of the actual quotient product. -/
theorem eval_homogeneous_idempotent (e : Abstract k) (he : e * e = e)
    (ps : List (Packed.{0} k)) (hne : ps ≠ [])
    (hp : ∀ P ∈ ps, abstractGraph P.graph = e) :
    abstractGraph (Packed.eval ps).graph = e := by
  induction ps with
  | nil => exact (hne rfl).elim
  | cons P ps ih =>
    cases ps with
    | nil => exact hp P (by simp)
    | cons Q qs =>
      change abstractGraph (glue P.graph (Packed.eval (Q :: qs)).graph) = e
      rw [abstractGraph_glue, hp P (by simp), ih (by simp)
        (by intro R hR; exact hp R (by simp [hR])), he]

#print axioms Occurrence.column_injective
#print axioms evalAppendIso
#print axioms eval_homogeneous_idempotent
end StackSorting.BiInterface.RepeatedColumn
