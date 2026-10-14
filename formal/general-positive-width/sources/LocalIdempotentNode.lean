import LocalDivisorWords
import PairAdjacent
import RightZeroForest
import TreeSubstitution

namespace StackSorting.Simon
open FactorizationTree

variable {B M : Type*} [Monoid M] [Fintype M]

/-- The nontrivial local-divisor lifting rule. An arbitrary number of children
with a common local idempotent can be assembled in the ambient monoid at a
cost depending only on its cardinality, not on the number of children. -/
theorem hasTree_of_common_local_idempotent (c : M) (interior : B → M)
    (ws : List (List B)) (H : ℕ) (harity : 2 ≤ ws.length)
    (hne : ∀ w ∈ ws, w ≠ [])
    (htrees : ∀ w ∈ ws, HasTree (ambientBlockValue c interior) w H)
    (e : LocalDivisor c) (he : e * e = e)
    (hvalues : ∀ w ∈ ws, (w.map (localBlockValue c interior)).prod = e) :
    HasTree (ambientBlockValue c interior) ws.flatten
      (H + 3 * Fintype.card M + 3) := by
  classical
  let Letter := {w : List B // w ∈ ws}
  let subst : Letter × Letter → List B := fun p => p.1.val ++ p.2.val
  let φ : Letter × Letter → M := fun p => ((subst p).map (ambientBlockValue c interior)).prod
  have hzero : ∀ p q, φ p * φ q = φ q := by
    intro p q
    exact paired_blockWords_rightZero c interior e he p.1.val p.2.val q.1.val q.2.val
      (hne _ p.1.property) (hne _ p.2.property) (hne _ q.1.property) (hne _ q.2.property)
      (hvalues _ p.1.property) (hvalues _ p.2.property) (hvalues _ q.1.property)
  have hbase : ∀ p, HasTree (ambientBlockValue c interior) (subst p) (H + 1) := by
    intro p
    exact hasTree_binary (htrees _ p.1.property) (htrees _ p.2.property)
  let pairs := adjacentPairs ws.attach
  let tail := oddLast ws.attach
  have hpne : pairs ≠ [] := adjacentPairs_ne_nil ws.attach (by simpa using harity)
  have hp := exists_rightZero_tree φ hzero pairs hpne
  have hps := hasTree_substitute φ (ambientBlockValue c interior) subst
    (H + 1) hbase (by intro p; rfl) pairs (3 * Fintype.card M + 1) hp
  have hps' : HasTree (ambientBlockValue c interior) (pairs.flatMap subst)
      (H + 3 * Fintype.card M + 2) := hasTree_mono hps (by omega)
  have hword : ws.flatten = pairs.flatMap subst ++ tail.toList.flatMap (fun w => w.val) := by
    calc
      ws.flatten = ws.attach.flatMap (fun w => w.val) := by simp [List.flatMap_def]
      _ = _ := by
        rw [← adjacentPairs_reconstruct ws.attach]
        simp [pairs, tail, subst, List.flatMap_assoc]
        rfl
  rw [hword]
  cases htail : tail with
  | none =>
    simpa [htail] using hasTree_mono hps'
      (by omega : H + 3 * Fintype.card M + 2 ≤ H + 3 * Fintype.card M + 3)
  | some last =>
    have hl := htrees last.val last.property
    have hl' := hasTree_mono hl
      (by omega : H ≤ H + 3 * Fintype.card M + 2)
    simpa [htail] using hasTree_binary hps' hl'

#print axioms hasTree_of_common_local_idempotent
end StackSorting.Simon
