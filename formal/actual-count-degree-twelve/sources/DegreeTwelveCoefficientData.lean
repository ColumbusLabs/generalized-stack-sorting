import DegreeTwelveCoefficientArithmetic
import DegreeTwelveData
namespace StackSorting.DegreeTwelve
open Polynomial
open Coefficients
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def fCoeffs : List Coefficients.F := [5, 14, 9, 10, 4, 3, 14, 7, 14, 3, 14, 7, 5]
def remCoeffs0 : List Coefficients.F := [0, 1]
def remCoeffs1 : List Coefficients.F := [10, 11, 15, 7, 2, 13, 10, 0, 1, 8, 9, 8]
def remCoeffs2 : List Coefficients.F := [5, 12, 9, 5, 8, 8, 10, 13, 14, 8, 11, 15]
def remCoeffs3 : List Coefficients.F := [9, 9, 6, 2, 5, 10, 1, 14, 4, 3, 9, 7]
def remCoeffs4 : List Coefficients.F := [6, 13, 0, 12, 12, 7, 0, 5, 4, 1, 2, 3]
def remCoeffs5 : List Coefficients.F := [13, 12, 3, 12, 15, 3, 11, 3, 15, 15, 2, 2]
def remCoeffs6 : List Coefficients.F := [0, 12, 6, 7, 4, 5, 9, 13, 5, 14, 10, 4]
def remCoeffs7 : List Coefficients.F := [9, 11, 11, 1, 7, 14, 9, 2, 16, 10, 6, 15]
def remCoeffs8 : List Coefficients.F := [15, 11, 11, 5, 3, 3, 2, 1, 0, 3, 7, 4]
def remCoeffs9 : List Coefficients.F := [9, 1, 5, 11, 8, 14, 12, 7, 4, 16, 8, 16]
def remCoeffs10 : List Coefficients.F := [5, 14, 5, 0, 15, 15, 13, 0, 4, 9, 4, 12]
def remCoeffs11 : List Coefficients.F := [6, 12, 14, 6, 6, 10, 8, 10, 1, 15, 0, 16]
def remCoeffs12 : List Coefficients.F := [0, 1]

theorem eval_fCoeffs : Coefficients.eval fCoeffs = specialized := by
  unfold fCoeffs specialized
  simp only [Coefficients.eval, C_ofNat]
  ring

theorem eval_remCoeffs0 : Coefficients.eval remCoeffs0 = rem0 := by
  unfold remCoeffs0 rem0
  simp only [Coefficients.eval, C_0, C_1]
  ring

theorem eval_remCoeffs1 : Coefficients.eval remCoeffs1 = rem1 := by
  unfold remCoeffs1 rem1
  simp only [Coefficients.eval, C_ofNat, C_0, C_1]
  ring

theorem eval_remCoeffs2 : Coefficients.eval remCoeffs2 = rem2 := by
  unfold remCoeffs2 rem2
  simp only [Coefficients.eval, C_ofNat]
  ring

theorem eval_remCoeffs3 : Coefficients.eval remCoeffs3 = rem3 := by
  unfold remCoeffs3 rem3
  simp only [Coefficients.eval, C_ofNat, C_1]
  ring

theorem eval_remCoeffs4 : Coefficients.eval remCoeffs4 = rem4 := by
  unfold remCoeffs4 rem4
  simp only [Coefficients.eval, C_ofNat, C_0, C_1]
  ring

theorem eval_remCoeffs5 : Coefficients.eval remCoeffs5 = rem5 := by
  unfold remCoeffs5 rem5
  simp only [Coefficients.eval, C_ofNat]
  ring

theorem eval_remCoeffs6 : Coefficients.eval remCoeffs6 = rem6 := by
  unfold remCoeffs6 rem6
  simp only [Coefficients.eval, C_ofNat, C_0]
  ring

theorem eval_remCoeffs7 : Coefficients.eval remCoeffs7 = rem7 := by
  unfold remCoeffs7 rem7
  simp only [Coefficients.eval, C_ofNat, C_1]
  ring

theorem eval_remCoeffs8 : Coefficients.eval remCoeffs8 = rem8 := by
  unfold remCoeffs8 rem8
  simp only [Coefficients.eval, C_ofNat, C_0, C_1]
  ring

theorem eval_remCoeffs9 : Coefficients.eval remCoeffs9 = rem9 := by
  unfold remCoeffs9 rem9
  simp only [Coefficients.eval, C_ofNat, C_1]
  ring

theorem eval_remCoeffs10 : Coefficients.eval remCoeffs10 = rem10 := by
  unfold remCoeffs10 rem10
  simp only [Coefficients.eval, C_ofNat, C_0]
  ring

theorem eval_remCoeffs11 : Coefficients.eval remCoeffs11 = rem11 := by
  unfold remCoeffs11 rem11
  simp only [Coefficients.eval, C_ofNat, C_0, C_1]
  ring

theorem eval_remCoeffs12 : Coefficients.eval remCoeffs12 = rem12 := by
  unfold remCoeffs12 rem12
  simp only [Coefficients.eval, C_0, C_1]
  ring

end
end StackSorting.DegreeTwelve
