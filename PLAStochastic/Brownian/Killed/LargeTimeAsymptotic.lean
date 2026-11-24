import PLAStochastic.Brownian.Killed.Semigroup

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

 def heatSpectralGap (r : ℝ) (n : ℕ) : ℝ := heatFrequency r n ^ 2 / 2 - heatScale r

 theorem heatSpectralGap_eq (r : ℝ) (n : ℕ) :
    heatSpectralGap r n = (((n : ℝ) + 1)^2-1)*heatScale r := by
  unfold heatSpectralGap heatFrequency heatScale
  ring

 theorem heatSpectralGap_zero (r : ℝ) : heatSpectralGap r 0 = 0 := by
  rw [heatSpectralGap_eq]
  norm_num

 theorem heatSpectralGap_nonneg {r : ℝ} (hr : 0 < r) (n : ℕ) : 0 ≤ heatSpectralGap r n := by
  rw [heatSpectralGap_eq]
  apply mul_nonneg _ (heatScale_pos hr).le
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

 theorem heatSpectralGap_pos {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : n ≠ 0) : 0 < heatSpectralGap r n := by
  rw [heatSpectralGap_eq]
  apply mul_pos _ (heatScale_pos hr)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  nlinarith

 def heatRescaledMode (r : ℝ) (n : ℕ) (t x z : ℝ) : ℝ :=
  (2/r * (Real.sin (heatFrequency r n*x) * Real.sin (heatFrequency r n*z))) *
    Real.exp (-heatSpectralGap r n*t)

 theorem heatRescaledMode_eq (r : ℝ) (n : ℕ) (t x z : ℝ) :
    heatRescaledMode r n t x z = Real.exp (heatScale r*t) * heatSpatialMode r 0 0 n t x z := by
  dsimp only [heatRescaledMode, heatSpatialMode, heatSpectralGap]
  simp only [Nat.cast_zero, pow_zero, mul_one, zero_mul, zero_div, add_zero]
  rw [show -(heatFrequency r n ^ 2 / 2 - heatScale r) * t =
    heatScale r*t + -(heatFrequency r n ^ 2)*t/2 by ring, Real.exp_add]
  ring

 theorem heatRescaledMode_bound {r t : ℝ} (hr : 0 < r) (ht : 1 ≤ t) (n : ℕ) (x z : ℝ) :
    ‖heatRescaledMode r n t x z‖ ≤ Real.exp (heatScale r) * heatSpatialBound r 1 0 0 n := by
  have hm : ‖heatRescaledMode r n t x z‖ ≤ ‖heatRescaledMode r n 1 x z‖ := by
    dsimp only [heatRescaledMode]
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left ht (heatSpectralGap_nonneg hr n)
    linarith
  apply hm.trans
  rw [heatRescaledMode_eq, norm_mul, mul_one, Real.norm_eq_abs (Real.exp _),
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (heatSpatialMode_bound hr (by norm_num) le_rfl 0 0 n x z)
    (Real.exp_nonneg _)

 theorem tendsto_heatRescaledMode {r : ℝ} (hr : 0 < r) (n : ℕ) (x z : ℝ) :
    Tendsto (fun t => heatRescaledMode r n t x z) atTop
      (𝓝 (if n = 0 then 2/r * (Real.sin (heatFrequency r 0*x) * Real.sin (heatFrequency r 0*z)) else 0)) := by
  by_cases hn : n = 0
  · subst n
    simp only [heatRescaledMode, heatSpectralGap_zero, neg_zero, zero_mul, Real.exp_zero, mul_one]
    exact tendsto_const_nhds
  · rw [if_neg hn]
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (heatSpectralGap_pos hr hn))
    simpa only [heatRescaledMode, neg_mul, Function.comp_def, id_eq, mul_zero] using hh.const_mul
      (2/r * (Real.sin (heatFrequency r n*x) * Real.sin (heatFrequency r n*z)))

/-- The genuine first-eigenfunction large-time asymptotic, with a summable bound on the full tail. -/
 theorem tendsto_rescaled_dirichletHeatKernel {r : ℝ} (hr : 0 < r) (x z : ℝ) :
    Tendsto (fun t => Real.exp (heatScale r*t) * dirichletHeatKernel r t x z) atTop
      (𝓝 (2/r * (Real.sin (heatFrequency r 0*x) * Real.sin (heatFrequency r 0*z)))) := by
  have hb : ∀ᶠ t : ℝ in atTop, ∀ n, ‖heatRescaledMode r n t x z‖ ≤
      Real.exp (heatScale r) * heatSpatialBound r 1 0 0 n := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht n
    exact heatRescaledMode_bound hr ht n x z
  have h := tendsto_tsum_of_dominated_convergence
    ((summable_heatSpatialBound hr (by norm_num : (0 : ℝ) < 1) 0 0).mul_left (Real.exp (heatScale r)))
    (fun n => tendsto_heatRescaledMode hr n x z) hb
  simpa only [heatRescaledMode_eq, tsum_mul_left, heatSpatialSeries, dirichletHeatKernel,
    tsum_ite_eq, if_pos rfl] using h

end BrownianAffine
