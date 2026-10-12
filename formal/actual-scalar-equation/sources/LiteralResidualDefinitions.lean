import ChartScalars
import SignedSuffixEvaluation
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
variable {R : Type} [Lean.Grind.CommRing R]

def transitions (y : Chart R) : Letter → Mat R 6 6
  | .z => litZ y
  | .b => litB y
  | .t => litT y

def suffix9 (y : Chart R) (beta : Vec R 6) : Letter → Mat R 9 9
  | .z => litN9z y beta
  | .b => litN9b y beta
  | .t => litN9t y beta

def deleted9 (y : Chart R) (beta : Vec R 6) : Letter → Mat R 6 9
  | .z => litCSz y beta
  | .b => litCSb y beta
  | .t => litCSt y beta

inductive Family where | b | z deriving DecidableEq, Repr

def initialPrefix (y : Chart R) (f : Family) (a : Letter) : Vec R 6 :=
  match f with
  | .b => transitions y a 0
  | .z => vm (litalpha y 0) (transitions y a)

def initialSuffix9 (y : Chart R) (beta : Vec R 6) : Family → Letter → Vec R 9
  | .b, .z => litinitialBz y beta 0
  | .b, .b => litinitialBb y beta 0
  | .b, .t => litinitialBt y 0
  | .z, .z => litinitialZz y beta 0
  | .z, .b => litinitialZb y beta 0
  | .z, .t => litinitialZt y beta 0

def initial9 (y : Chart R) (beta : Vec R 6) (f : Family) (a : Letter) : Vec R 6 × Vec R 9 :=
  (initialPrefix y f a, initialSuffix9 y beta f a)

def suffix19 (y : Chart R) (beta : Vec R 6) : Letter → Mat R 19 19
  | .z => litN19z y beta
  | .b => litN19b y beta
  | .t => litN19t y beta

def deleted19 (y : Chart R) : Letter → Mat R 6 19
  | .z => litCz y
  | .b => litCb y
  | .t => litCt y

def boundaryF (y : Chart R) : Letter → Vec R 19
  | .z => litpFz y 0
  | .b => litpFb y 0
  | .t => litpFt y 0

def boundaryJ (y : Chart R) (beta : Vec R 6) : Letter → Vec R 19
  | .z => litpJz y beta 0
  | .b => litpJb y beta 0
  | .t => litpJt y beta 0

def boundaryK (y : Chart R) (beta : Vec R 6) : Letter → Vec R 19
  | .z => litpKz y 0
  | .b => litpKb y beta 0
  | .t => litpKt y 0

/-- The original six initial residual rows, with signs and boundary weights explicit. -/
def initial19 (y : Chart R) (beta : Vec R 6) (f : Family) (a : Letter) : Vec R 6 × Vec R 19 :=
  (initialPrefix y f a, match f with
    | .b => fun j => -deleted19 y a 0 j-2*boundaryF y a j-2*boundaryK y beta a j
    | .z => fun j => -vm (litalpha y 0) (deleted19 y a) j-boundaryF y a j-boundaryJ y beta a j)

end StackSorting.FiniteGraph
