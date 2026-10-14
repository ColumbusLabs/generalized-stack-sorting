import DecompositionNumberedCodec
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.OfFn

namespace StackSorting.FinitePort

/-- A literal finite alphabet: colors, bounded port count, and exactly that
many bounded parent-port numbers with all directional relation bits. -/
abbrev Alphabet (colors relations W : Nat) :=
  (Fin colors → Bool) ×
    (Σ d : Fin (W+1), Fin d.val → (Fin (W+1) × (Fin relations → Bool → Bool)))

instance alphabetFintype (colors relations W : Nat) : Fintype (Alphabet colors relations W) :=
  inferInstance

def Alphabet.toLabel {colors relations W} (a : Alphabet colors relations W) :
    NodeLabel colors relations where
  color := a.1
  ports := List.ofFn (fun i => ⟨(a.2.2 i).1.val, (a.2.2 i).2⟩)

def Alphabet.ofLabel {colors relations W} (l : NodeLabel colors relations)
    (hlen : l.ports.length ≤ W) (hp : ∀ e ∈ l.ports, e.parentPort ≤ W) :
    Alphabet colors relations W :=
  ⟨l.color, ⟨⟨l.ports.length, by omega⟩, fun i =>
    ⟨⟨(l.ports.get i).parentPort, by
      have := hp (l.ports.get i) (List.get_mem ..)
      omega⟩, (l.ports.get i).bit⟩⟩⟩

theorem Alphabet.toLabel_ofLabel {colors relations W} (l : NodeLabel colors relations)
    (hlen : l.ports.length ≤ W) (hp : ∀ e ∈ l.ports, e.parentPort ≤ W) :
    (Alphabet.ofLabel l hlen hp).toLabel = l := by
  cases l with
  | mk color ports =>
    simp only [Alphabet.toLabel, Alphabet.ofLabel]
    have hf : (fun i : Fin ports.length =>
        (⟨(ports.get i).parentPort, (ports.get i).bit⟩ : PortEntry relations)) = ports.get := by
      funext i
      cases ports.get i
      rfl
    rw [hf, List.ofFn_get]

theorem Alphabet.toLabel_bounded {colors relations W} (a : Alphabet colors relations W) :
    a.toLabel.ports.length ≤ W ∧ ∀ e ∈ a.toLabel.ports, e.parentPort ≤ W := by
  constructor
  · simpa only [Alphabet.toLabel, List.length_ofFn] using Nat.le_of_lt_succ a.2.1.isLt
  · intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact Nat.le_of_lt_succ (a.2.2 i).1.isLt

/-- The finite alphabet introduces no padding multiplicity: its decoding is
injective, including zero-bit inherited entries. -/
theorem Alphabet.toLabel_injective {colors relations W} :
    Function.Injective (@Alphabet.toLabel colors relations W) := by
  rintro ⟨ca,⟨da,pa⟩⟩ ⟨cb,⟨db,pb⟩⟩ h
  have hc : ca = cb := congrArg NodeLabel.color h
  have hd : da = db := by
    apply Fin.ext
    have hh := congrArg (fun x : NodeLabel colors relations => x.ports.length) h
    simpa only [Alphabet.toLabel, List.length_ofFn] using hh
  subst cb
  subst db
  have hp : pa = pb := by
    have hh := congrArg NodeLabel.ports h
    change List.ofFn (fun i => (⟨(pa i).1.val,(pa i).2⟩ : PortEntry relations)) =
      List.ofFn (fun i => (⟨(pb i).1.val,(pb i).2⟩ : PortEntry relations)) at hh
    have hf := List.ofFn_injective hh
    funext i
    have he := congrFun hf i
    exact Prod.ext (Fin.ext (congrArg PortEntry.parentPort he)) (congrArg PortEntry.bit he)
  subst pb
  rfl

theorem Alphabet.ofLabel_toLabel {colors relations W} (a : Alphabet colors relations W) :
    Alphabet.ofLabel a.toLabel a.toLabel_bounded.1 a.toLabel_bounded.2 = a := by
  apply Alphabet.toLabel_injective
  exact Alphabet.toLabel_ofLabel ..

def alphabetCode {n colors relations W} (C : Code n colors relations) (h : BoundedCode C W) :
    Fin n → Alphabet colors relations W := fun v => Alphabet.ofLabel (C v) (h v).1 (h v).2

theorem alphabetCode_recovers {n colors relations W} (C : Code n colors relations)
    (h : BoundedCode C W) :
    (fun v => (alphabetCode C h v).toLabel) = C := by
  funext v
  exact Alphabet.toLabel_ofLabel (C v) (h v).1 (h v).2

/-- The accepted decomposition-to-code endpoint uses a genuinely finite
alphabet, rather than unbounded natural-number port records. -/
theorem exactCodec_finiteAlphabet {n colors relations W}
    {G : Diagram n colors relations} (E : GraphWidth.ExactNumberedCodec G W) :
    ∃ labels : Fin n → Alphabet colors relations W,
      (∀ q u v, DecodedRel E.tree (fun i => (labels i).toLabel) q
        (E.index u) (E.index v) ↔ G.rel q u v = true) ∧
      ∀ u c, (decode E.tree (fun i => (labels i).toLabel)).color (E.index u) c = G.color u c := by
  refine ⟨alphabetCode E.code E.bounded, ?_, ?_⟩
  · rw [alphabetCode_recovers]
    exact E.relation
  · rw [alphabetCode_recovers]
    exact E.color

#print axioms Alphabet.toLabel_ofLabel
#print axioms exactCodec_finiteAlphabet
end StackSorting.FinitePort
