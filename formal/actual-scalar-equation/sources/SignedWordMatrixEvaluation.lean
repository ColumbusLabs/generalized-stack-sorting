import SignedWordDeletion
import SignedSuffixEvaluation

/-! Matrix evaluation of the literal signed finite sums. No transition identity
is an input: the four-channel recurrence follows from F/J/K/E's definitions. -/
noncomputable section
namespace StackSorting.SignedWord
open StackSorting.FiniteGraph
attribute [local instance] Lean.Grind.Ring.intCast
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
variable {R : Type} [Lean.Grind.CommRing R]

def letterMatrix (y : Chart R) : Letter → Mat R 6 6
  | .z => litZ y
  | .b => litB y
  | .t => litT y

def wordColumn (y : Chart R) (beta : Vec R 6) : Word → Vec R 6
  | [] => beta
  | a::w => mv (letterMatrix y a) (wordColumn y beta w)

theorem wordColumn_eq_wordValue (y : Chart R) (beta : Vec R 6) (w : Word) :
    wordColumn y beta w = wordValue y beta w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [wordColumn, wordValue, ih]
    cases a <;> rfl

def polyColumn (y : Chart R) (beta : Vec R 6) (p : Poly) : Vec R 6 :=
  fun i => eval (fun w => wordColumn y beta w i) p

def emptyIndicator : Word → R
  | [] => 1
  | _::_ => 0

def evaluatedChannels (y : Chart R) (beta : Vec R 6) (w : Word) : SuffixChannels R :=
  ⟨polyColumn y beta (F w), polyColumn y beta (J w), polyColumn y beta (K w),
    emptyIndicator w⟩

theorem polyColumn_nil (y : Chart R) (beta : Vec R 6) :
    polyColumn y beta [] = fun _ => 0 := rfl

theorem polyColumn_one (y : Chart R) (beta : Vec R 6) :
    polyColumn y beta one = beta := by
  funext i
  exact eval_one (fun w => wordColumn y beta w i)

theorem polyColumn_append (y : Chart R) (beta : Vec R 6) (p q : Poly) :
    polyColumn y beta (p++q) = fun i => polyColumn y beta p i + polyColumn y beta q i := by
  funext i
  exact eval_append _ _ _

theorem polyColumn_prefix (y : Chart R) (beta : Vec R 6) (a : Letter) (p : Poly) :
    polyColumn y beta (prefixLetter a p) = mv (letterMatrix y a) (polyColumn y beta p) := by
  funext i
  simp only [polyColumn, eval_prefix, wordColumn, mv, eval_sumFin, eval_mul]

theorem polyColumn_difference (y : Chart R) (beta : Vec R 6) (p : Poly) :
    polyColumn y beta (difference p) = mv (FiniteGraph.difference y) (polyColumn y beta p) := by
  funext i
  simp only [polyColumn, eval_difference, wordColumn, letterMatrix, mv, eval_sumFin, eval_mul,
    FiniteGraph.difference]
  have he : (fun j => (litB y i j-litZ y i j)*eval (fun w => wordColumn y beta w j) p) =
      (fun j => litB y i j*eval (fun w => wordColumn y beta w j) p +
        -(litZ y i j*eval (fun w => wordColumn y beta w j) p)) := by
    funext j
    grind
  rw [he, sumFin_add, sumFin_neg]
  grind

theorem polyColumn_E (y : Chart R) (beta : Vec R 6) (w : Word) :
    polyColumn y beta (E w) = fun i => beta i * emptyIndicator w := by
  cases w with
  | nil => rw [E, polyColumn_one]; funext i; simp only [emptyIndicator]; grind
  | cons a w => rw [E, polyColumn_nil]; funext i; simp only [emptyIndicator]; grind

theorem mv_add_right (A : Mat R 6 6) (v w : Vec R 6) :
    mv A (fun i => v i+w i) = fun i => mv A v i+mv A w i := by
  funext i
  unfold mv
  have h : (fun j => A i j*(v j+w j)) = (fun j => A i j*v j+A i j*w j) := by
    funext j
    grind
  rw [h, sumFin_add]

theorem mv_scale_right (A : Mat R 6 6) (v : Vec R 6) (c : R) :
    mv A (fun i => v i*c) = fun i => mv A v i*c := by
  funext i
  unfold mv
  have h : (fun j => A i j*(v j*c)) = (fun j => (A i j*v j)*c) := by
    funext j
    grind
  rw [h, sumFin_mul]

omit [Lean.Grind.CommRing R] in
theorem channels_ext (s t : SuffixChannels R)
    (hf : s.f=t.f) (hj : s.j=t.j) (hk : s.k=t.k) (he : s.e=t.e) : s=t := by
  cases s
  cases t
  cases hf
  cases hj
  cases hk
  cases he
  rfl

theorem evaluatedChannels_nil (y : Chart R) (beta : Vec R 6) :
    evaluatedChannels y beta [] = channelBase beta := by
  simp only [evaluatedChannels, F, J, K, polyColumn_one, polyColumn_nil, emptyIndicator, channelBase]

theorem evaluatedChannels_cons (y : Chart R) (beta : Vec R 6) (a : Letter) (w : Word) :
    evaluatedChannels y beta (a::w) = channelStep y beta a (evaluatedChannels y beta w) := by
  cases a with
  | z =>
    apply channels_ext
    · simp only [evaluatedChannels, F, polyColumn_prefix, letterMatrix, channelStep]
    · simp only [evaluatedChannels, J, polyColumn_prefix, letterMatrix, polyColumn_E,
        mv_scale_right, channelStep]
    · rfl
    · rfl
  | b =>
    apply channels_ext
    · simp only [evaluatedChannels, F, polyColumn_append, polyColumn_prefix, letterMatrix,
        channelStep, mv_add_right]
    · simp only [evaluatedChannels, J, polyColumn_prefix, letterMatrix, polyColumn_E,
        mv_scale_right, channelStep]
    · simp only [evaluatedChannels, K, polyColumn_difference, polyColumn_E,
        mv_scale_right, channelStep]
    · rfl
  | t =>
    apply channels_ext
    · simp only [evaluatedChannels, F, polyColumn_append, polyColumn_prefix, letterMatrix, channelStep]
    · simp only [evaluatedChannels, J, polyColumn_append, polyColumn_prefix, letterMatrix,
        polyColumn_difference, polyColumn_E, mv_scale_right, channelStep]
    · simp only [evaluatedChannels, K, polyColumn_difference, channelStep]
    · rfl

/-- The graph's four channels evaluate the actual finite signed operators on
all words, including the empty terminal. -/
theorem concrete_four_channel_evaluation (y : Chart R) (beta : Vec R 6) (w : Word) :
    evaluatedChannels y beta w = evalChannels y beta w := by
  induction w with
  | nil => exact evaluatedChannels_nil y beta
  | cons a w ih => rw [evaluatedChannels_cons, evalChannels, ih]

/-- The literal coordinate selector has coefficients 1 for F and, only for
B/T, 1 for K. Its E and J coefficients vanish. -/
def selectedColumn (a : Letter) (s : SuffixChannels R) : Vec R 6 :=
  match a with
  | .z => s.f
  | .b => fun i => s.f i+s.k i
  | .t => fun i => s.f i+s.k i

theorem selectedColumn_concrete (y : Chart R) (beta : Vec R 6) (a : Letter) (w : Word) :
    polyColumn y beta (selected a w) = selectedColumn a (evalChannels y beta w) := by
  rw [←concrete_four_channel_evaluation]
  cases a <;> simp only [selected, selectedColumn, evaluatedChannels, U, polyColumn_append]

theorem heldDelete_matrix_step (y : Chart R) (beta : Vec R 6) (a : Letter) (w : Word) :
    polyColumn y beta (heldDelete (a::w)) = fun i =>
      selectedColumn a (evalChannels y beta w) i +
      mv (letterMatrix y a) (polyColumn y beta (heldDelete w)) i := by
  simp only [heldDelete, polyColumn_append, polyColumn_prefix, selectedColumn_concrete]

#print axioms polyColumn_difference
#print axioms evaluatedChannels_cons
#print axioms concrete_four_channel_evaluation
end StackSorting.SignedWord
