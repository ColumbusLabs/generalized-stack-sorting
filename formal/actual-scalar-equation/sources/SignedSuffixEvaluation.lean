import GraphLiterals
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
variable {R : Type} [Lean.Grind.CommRing R]

def wordTransition (y : Chart R) : Letter → Mat R 6 6
  | .z => litZ y
  | .b => litB y
  | .t => litT y

/-- Column valuation of an ordinary word, with no scalar equation premise. -/
def wordValue (y : Chart R) (beta : Vec R 6) : List Letter → Vec R 6
  | [] => beta
  | a::w => mv (wordTransition y a) (wordValue y beta w)

/-- Four exact suffix channels, before the 19-to-9 quotient. -/
structure SuffixChannels (R : Type) where
  f : Vec R 6
  j : Vec R 6
  k : Vec R 6
  e : R

def channelBase (beta : Vec R 6) : SuffixChannels R :=
  ⟨beta, beta, (fun _ => 0), 1⟩

def difference (y : Chart R) : Mat R 6 6 := fun i j => litB y i j-litZ y i j

def channelStep (y : Chart R) (beta : Vec R 6) (a : Letter)
    (s : SuffixChannels R) : SuffixChannels R :=
  match a with
  | .z => ⟨mv (litZ y) s.j, (fun i => mv (litZ y) beta i*s.e), (fun _ => 0), 0⟩
  | .b => ⟨mv (litZ y) (fun i => s.f i+s.k i),
      (fun i => mv (litB y) beta i*s.e), (fun i => mv (difference y) beta i*s.e), 0⟩
  | .t => ⟨(fun i => mv (litB y) s.f i+mv (litZ y) s.k i),
      (fun i => mv (litZ y) s.j i+mv (difference y) beta i*s.e), mv (difference y) s.k, 0⟩

def evalChannels (y : Chart R) (beta : Vec R 6) : List Letter → SuffixChannels R
  | [] => channelBase beta
  | a::w => channelStep y beta a (evalChannels y beta w)

def packChannels (s : SuffixChannels R) : Vec R 19 := fun i =>
  match i.val with
  | 0 => s.f 0 | 1 => s.f 1 | 2 => s.f 2 | 3 => s.f 3 | 4 => s.f 4 | 5 => s.f 5
  | 6 => s.j 0 | 7 => s.j 1 | 8 => s.j 2 | 9 => s.j 3 | 10 => s.j 4 | 11 => s.j 5
  | 12 => s.k 0 | 13 => s.k 1 | 14 => s.k 2 | 15 => s.k 3 | 16 => s.k 4 | 17 => s.k 5
  | 18 => s.e
  | _ => 0

end StackSorting.FiniteGraph
