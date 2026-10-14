import FiniteConfigurationWalk
import FinitePortEncoding

namespace StackSorting.FinitePort
open FiniteState

/-- No positive ports at the root. This excludes root self-cycles and makes
the finite-fuel decoder coincide with unbounded finite configuration walks. -/
def RootEmpty {n colors relations} (C : Code n colors relations) : Prop :=
  ∀ v, v.val = 0 → (C v).ports = []

theorem encode_rootEmpty {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) :
    RootEmpty (encode T O G) := by
  intro v hv
  simp [encode, inherited_root_empty T O G v hv]

abbrev Configuration (n W : Nat) := Vertex n × Fin (W+1)

/-- State zero terminates. A positive state follows the exact stored parent
port; relation bits play no part in this transition. -/
def PortStep {n colors relations W} (T : RootedTree n) (C : Code n colors relations)
    (a b : Configuration n W) : Prop :=
  a.1.val ≠ 0 ∧ a.2.val ≠ 0 ∧ b.1 = T.parent a.1 ∧
    ∃ e, (C a.1).ports[a.2.val-1]? = some e ∧ e.parentPort = b.2.val

theorem walk_readPort {n colors relations W} (T : RootedTree n)
    (C : Code n colors relations) {a b : Configuration n W}
    (h : Walk (PortStep T C) a b) (hb : b.2.val = 0)
    (fuel : Nat) (hf : a.1.val ≤ fuel) :
    readPort T C fuel a.1 a.2.val = some b.1 := by
  induction h generalizing fuel with
  | refl a => simp [hb, readPort]
  | @step a d b had hdb ih =>
    obtain ⟨ha, hi, hd, e, he, hp⟩ := had
    have hlt := T.parent_lt a.1 ha
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hh := ih hb fuel (by rw [hd]; omega)
      have hi' : a.2.val = (a.2.val-1)+1 := by omega
      rw [hi', readPort, he]
      simp only [Option.bind_some]
      rw [hp, ← hd]
      exact hh

theorem readPort_walk {n colors relations W} (T : RootedTree n)
    (C : Code n colors relations) (hB : BoundedCode C W) (hR : RootEmpty C)
    (fuel : Nat) (v u : Vertex n) (i : Fin (W+1))
    (h : readPort T C fuel v i.val = some u) :
    Walk (PortStep T C) (v,i) (u,0) := by
  induction fuel generalizing v i with
  | zero =>
    by_cases hi : i.val = 0
    · have hv : v = u := by simpa [hi, readPort] using h
      have his : i = 0 := Fin.ext hi
      subst u; subst i
      exact .refl _
    · have hi' : i.val = (i.val-1)+1 := by omega
      rw [hi', readPort] at h
      contradiction
  | succ fuel ih =>
    by_cases hi : i.val = 0
    · have hv : v = u := by simpa [hi, readPort] using h
      have his : i = 0 := Fin.ext hi
      subst u; subst i
      exact .refl _
    · have hi' : i.val = (i.val-1)+1 := by omega
      have hr : v.val ≠ 0 := by
        intro hz
        rw [hi', readPort, hR v hz] at h
        simp at h
      rw [hi', readPort] at h
      cases he : (C v).ports[i.val-1]? with
      | none => simp [he] at h
      | some e =>
        simp only [he, Option.bind_some] at h
        have hp := (hB v).2 e (List.mem_of_getElem? he)
        let j : Fin (W+1) := ⟨e.parentPort, by omega⟩
        exact .step ⟨hr, hi, rfl, e, he, rfl⟩ (ih (T.parent v) j h)

/-- The decoder uses exactly the same original vertices, with no port copies.
The state component belongs to syntax only. -/
theorem portWalk_iff_readPort {n colors relations W} (T : RootedTree n)
    (C : Code n colors relations) (hB : BoundedCode C W) (hR : RootEmpty C)
    (v u : Vertex n) (i : Fin (W+1)) :
    Walk (PortStep T C) (v,i) (u,0) ↔ readPort T C n v i.val = some u := by
  constructor
  · intro h; exact walk_readPort T C h rfl n (Nat.le_of_lt v.isLt)
  · exact readPort_walk T C hB hR n v u i

#print axioms encode_rootEmpty
#print axioms portWalk_iff_readPort
end StackSorting.FinitePort
