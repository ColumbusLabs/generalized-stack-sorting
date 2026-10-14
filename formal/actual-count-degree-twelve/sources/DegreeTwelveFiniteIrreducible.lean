import DegreeTwelveRabinChain
import DegreeTwelveBezout
import DegreeTwelveCoefficientStep0
import DegreeTwelveCoefficientStep1
import DegreeTwelveCoefficientStep2
import DegreeTwelveCoefficientStep3
import DegreeTwelveCoefficientStep4
import DegreeTwelveCoefficientStep5
import DegreeTwelveCoefficientStep6
import DegreeTwelveCoefficientStep7
import DegreeTwelveCoefficientStep8
import DegreeTwelveCoefficientStep9
import DegreeTwelveCoefficientStep10
import DegreeTwelveCoefficientStep11

namespace StackSorting.DegreeTwelve
open Polynomial
set_option maxRecDepth 4096

theorem specialized_irreducible : Irreducible specialized := by
  have hc : Nat.card (ZMod 17) = 17 := by simp
  exact rabin_degree_twelve_from_chain 17 hc specialized specialized_degree
    rem1 rem2 rem3 rem4 rem5 rem6 rem7 rem8 rem9 rem10 rem11
    certified_frobenius_step_0
    certified_frobenius_step_1
    certified_frobenius_step_2
    certified_frobenius_step_3
    certified_frobenius_step_4
    certified_frobenius_step_5
    certified_frobenius_step_6
    certified_frobenius_step_7
    certified_frobenius_step_8
    certified_frobenius_step_9
    certified_frobenius_step_10
    certified_frobenius_step_11
    coprime_remainder_4 coprime_remainder_6

#print axioms specialized_irreducible
end StackSorting.DegreeTwelve
