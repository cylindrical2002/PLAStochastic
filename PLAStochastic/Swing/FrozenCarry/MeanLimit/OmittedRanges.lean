import PLAStochastic.Swing.FrozenCarry.MeanLimit.InteriorLowerBound

/-! Deterministic endpoints and logarithmic costs of the two omitted ranges. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem frozenMeanLimit_endpoint_order {δ E : ℝ}
    (hδ : 0 ≤ δ) (hδ4 : δ ≤ 1/4) (hE : 1 ≤ E) :
    1 ≤ ⌈E⌉₊ ∧ ⌈E⌉₊ ≤ frozenInteriorLow δ E ∧
      frozenInteriorLow δ E ≤ frozenInteriorHigh δ E ∧
      frozenInteriorHigh δ E ≤ ⌈E^2⌉₊+1 := by
  have hlo : E ≤ E^(1+δ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hE (show (1 : ℝ) ≤ 1+δ by linarith)
  have hmid : E^(1+δ) ≤ E^(2-δ) :=
    Real.rpow_le_rpow_of_exponent_le hE (by linarith)
  have hhi : E^(2-δ) ≤ E^2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hE (show 2-δ ≤ (2 : ℝ) by linarith)
  refine ⟨Nat.one_le_ceil_iff.mpr (by linarith), Nat.ceil_mono hlo, ?_, ?_⟩
  · exact (Nat.ceil_mono hmid).trans (Nat.ceil_le_floor_add_one _)
  · exact Nat.add_le_add_right ((Nat.floor_mono hhi).trans (Nat.floor_le_ceil _)) 1

theorem frozenMeanLimit_outer_log_width {δ E : ℝ}
    (hδ : 0 ≤ δ) (hδ4 : δ ≤ 1/4) (hE : 1 ≤ E) :
    |Real.log (frozenInteriorLow δ E : ℝ)-Real.log (⌈E⌉₊ : ℝ)| ≤
        δ*Real.log E+1 ∧
    |Real.log (⌈E^2⌉₊+1 : ℕ)-Real.log (frozenInteriorHigh δ E : ℝ)| ≤
        δ*Real.log E+2 := by
  obtain ⟨hc, hca, hab, hbd⟩ := frozenMeanLimit_endpoint_order hδ hδ4 hE
  have hEp : 0 < E := by linarith
  have hcp : (0 : ℝ) < ⌈E⌉₊ := by exact_mod_cast hc
  have hap : (0 : ℝ) < frozenInteriorLow δ E := by exact_mod_cast hc.trans hca
  have hbp : (0 : ℝ) < frozenInteriorHigh δ E := by exact_mod_cast (hc.trans hca).trans hab
  have hcaR : (⌈E⌉₊ : ℝ) ≤ frozenInteriorLow δ E := by exact_mod_cast hca
  have hbdR : (frozenInteriorHigh δ E : ℝ) ≤ (⌈E^2⌉₊+1 : ℕ) := by exact_mod_cast hbd
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hcp hcaR)),
    abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hbp hbdR))]
  have hlogc : Real.log E ≤ Real.log (⌈E⌉₊ : ℝ) := Real.log_le_log hEp (Nat.le_ceil _)
  have hp1 : 1 ≤ E^(1+δ) := Real.one_le_rpow hE (by linarith)
  have hloga : Real.log (frozenInteriorLow δ E : ℝ) ≤ Real.log 2+(1+δ)*Real.log E := by
    have hh := Real.log_le_log hap (show (frozenInteriorLow δ E : ℝ) ≤ 2*E^(1+δ) by
      linarith [frozenInteriorLow_lt (δ := δ) hEp.le])
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hEp] at hh
  have hlogb : (2-δ)*Real.log E ≤ Real.log (frozenInteriorHigh δ E : ℝ) := by
    rw [← Real.log_rpow hEp]
    exact Real.log_le_log (by positivity) (frozenInteriorHigh_gt δ E).le
  have hlogd : Real.log (⌈E^2⌉₊+1 : ℕ) ≤ Real.log 3+2*Real.log E := by
    have hd : ((⌈E^2⌉₊+1 : ℕ) : ℝ) ≤ 3*E^2 := by
      push_cast
      have := frozen_cutoff_le hE
      nlinarith
    have hh := Real.log_le_log (hbp.trans_le hbdR) hd
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hh
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  constructor <;> linarith

end SwingRepair
