import PLAStochastic.Swing.Gaussian.StripExit.Ballot

/-! Arithmetic that puts the bridge estimate into the paper's duration scale. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem inv_sqrt_half_le_four {N : ℕ} (hN : 2 ≤ N) :
    (Real.sqrt ((N/2 : ℕ) : ℝ))⁻¹ ≤ 4*(Real.sqrt ((N : ℝ)+1))⁻¹ := by
  have hM : 0 < N/2 := by omega
  have hMr : (0 : ℝ) < (N/2 : ℕ) := by exact_mod_cast hM
  have hNMr : (N : ℝ)+1 ≤ 16*((N/2 : ℕ) : ℝ) := by
    exact_mod_cast (show N+1 ≤ 16*(N/2) by omega)
  have hr : Real.sqrt ((N : ℝ)+1) ≤ 4*Real.sqrt ((N/2 : ℕ) : ℝ) := by
    calc
      _ ≤ Real.sqrt (16*((N/2 : ℕ) : ℝ)) := Real.sqrt_le_sqrt hNMr
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]; norm_num
  have hh : (1 : ℝ)/Real.sqrt ((N/2 : ℕ) : ℝ) ≤ 4/Real.sqrt ((N : ℝ)+1) :=
    (div_le_div_iff₀ (Real.sqrt_pos.mpr hMr)
    (Real.sqrt_pos.mpr (show (0 : ℝ) < (N : ℝ)+1 by positivity))).mpr (by simpa only [one_mul] using hr)
  simpa only [one_div, div_eq_mul_inv, one_mul] using hh

theorem frozenBridge_tail_arithmetic {N : ℕ} (hN : 2 ≤ N) (w : ℝ) {E : ℝ}
    (hE : 0 ≤ E) (hEN : 4*E ≤ N) :
    Real.sqrt 2*gaussianBallotConstant*(2*E/(N : ℝ)+(Real.sqrt ((N/2 : ℕ) : ℝ))⁻¹)*
        (max w 0+3/2+2*E/((N : ℝ)+1)) ≤
    16*gaussianBallotConstant*(1+max w 0)*
      (E/((N : ℝ)+1)+(Real.sqrt ((N : ℝ)+1))⁻¹) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn : (0 : ℝ) < (N : ℝ)+1 := by positivity
  have ha : 2*E/(N : ℝ) ≤ 4*(E/((N : ℝ)+1)) := by
    rw [show 4*(E/((N : ℝ)+1)) = (4*E)/((N : ℝ)+1) by ring]
    apply (div_le_div_iff₀ hNr hn).mpr
    nlinarith [mul_nonneg hE (sub_nonneg.mpr hNr1)]
  have hs := inv_sqrt_half_le_four hN
  have hh : max w 0+3/2+2*E/((N : ℝ)+1) ≤ 2*(1+max w 0) := by
    have hd : 2*E/((N : ℝ)+1) ≤ 1/2 := (div_le_iff₀ hn).mpr (by linarith)
    linarith [le_max_right w 0]
  have hc := gaussianBallotConstant_pos
  have hroot : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  calc
    _ ≤ 2*gaussianBallotConstant*(4*(E/((N : ℝ)+1))+
        4*(Real.sqrt ((N : ℝ)+1))⁻¹)*(2*(1+max w 0)) := by
      gcongr
    _ = _ := by ring

end SwingRepair
