import PLAStochastic.Affine.Moments.Optimal.Survival.Image.JetBounds
import PLAStochastic.Affine.Moments.Optimal.Survival.Image.Convergence
import PLAStochastic.ForMathlib.Analysis.Calculus.ExponentialDerivative

/-! # All-order smoothness and flatness of the actual optimal image series -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace BrownianAffine

theorem optimalImageMode_local_jet_bounds (r : ℕ) {T : ℝ} (hT : 0 < T) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n t, t ≤ T → ‖iteratedDeriv r (optimalImageMode n) t‖ ≤ u n := by
  obtain ⟨C, _, hb⟩ := iteratedDeriv_optimalImageMode_gaussian_bound r hT
  refine ⟨fun n => C * ((n : ℝ) + 1) ^ 2 * Real.exp (-4 * ((n : ℝ) + 1) ^ 2 / T), ?_, hb⟩
  convert! (Real.summable_gaussian_succ_pow 2 (by positivity : 0 < 4 / T)).mul_left C using 1
  funext n
  rw [mul_assoc]
  congr 2
  ring_nf

/-- Smoothness of the sum includes all positive orders and the boundary at zero. -/
theorem contDiff_optimalImageSeries : ContDiff ℝ ∞ optimalImageSeries := by
  apply contDiff_const.add
  exact contDiff_tsum_of_local_iteratedDeriv_bounds contDiff_optimalImageMode
    (fun r T hT => optimalImageMode_local_jet_bounds r hT)

theorem iteratedDeriv_optimalImageSeries_succ (r : ℕ) (t : ℝ) :
    iteratedDeriv (r + 1) optimalImageSeries t =
      ∑' n, iteratedDeriv (r + 1) (optimalImageMode n) t := by
  change iteratedDeriv (r + 1) (fun x => 1 + ∑' n, optimalImageMode n x) t = _
  rw [iteratedDeriv_const_add (Nat.succ_pos r)]
  exact congrFun (iteratedDeriv_tsum_of_local_bounds contDiff_optimalImageMode
    (fun j T hT => optimalImageMode_local_jet_bounds j hT) (r + 1)) t

/-- Every positive-order derivative vanishes on the entire nonpositive half-line. -/
theorem iteratedDeriv_optimalImageSeries_succ_of_nonpos (r : ℕ) {t : ℝ} (ht : t ≤ 0) :
    iteratedDeriv (r + 1) optimalImageSeries t = 0 := by
  rw [iteratedDeriv_optimalImageSeries_succ]
  simp only [iteratedDeriv_optimalImageMode_of_nonpos _ _ ht, tsum_zero]

/-- A coarse polynomial bound suffices for the later finite-difference interpolation. -/
theorem iteratedDeriv_optimalImageSeries_succ_polynomial_bound (r : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, 1 ≤ t →
      ‖iteratedDeriv (r + 1) optimalImageSeries t‖ ≤ A * t ^ 3 := by
  obtain ⟨C, E, hC, hE, hb⟩ := iteratedDeriv_optimalImageMode_gaussian_coefficients (r + 1)
  obtain ⟨G, hG, hg⟩ := Real.tsum_gaussian_succ_pow_scaled_bound 2 (by norm_num : 0 < (4 : ℝ))
  refine ⟨(60 * C + 24 * E) * G, by positivity, fun t ht => ?_⟩
  have ht0 := zero_lt_one.trans_le ht
  let g : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ 2 * Real.exp (-4 * ((n : ℝ) + 1) ^ 2 / t)
  have hs : Summable g := by
    convert! Real.summable_gaussian_succ_pow 2 (by positivity : 0 < 4 / t) using 1
    funext n
    dsimp only [g]
    congr 2
    ring
  have hsum : ‖iteratedDeriv (r + 1) optimalImageSeries t‖ ≤
      (2 * (29 + t) * C + 12 * E * (t + 1)) * ∑' n, g n := by
    rw [iteratedDeriv_optimalImageSeries_succ]
    apply tsum_of_norm_bounded (hs.hasSum.mul_left _)
    intro n
    simpa only [g, mul_assoc] using hb t ht0 n t le_rfl
  have hfactor : 2 * (29 + t) * C + 12 * E * (t + 1) ≤ (60 * C + 24 * E) * t := by
    nlinarith
  have hsqrt : Real.sqrt t ^ 3 ≤ t ^ 2 := by
    have hs1 : 1 ≤ Real.sqrt t := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ht
    have hst : Real.sqrt t ≤ t := by nlinarith [Real.sq_sqrt ht0.le]
    rw [pow_succ, Real.sq_sqrt ht0.le]
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hst ht0.le
  calc
    _ ≤ (2 * (29 + t) * C + 12 * E * (t + 1)) * ∑' n, g n := hsum
    _ ≤ ((60 * C + 24 * E) * t) * (G * Real.sqrt t ^ 3) :=
      mul_le_mul hfactor (hg t ht) (tsum_nonneg (fun _ => by dsimp [g]; positivity)) (by positivity)
    _ ≤ ((60 * C + 24 * E) * t) * (G * t ^ 2) := by gcongr
    _ = ((60 * C + 24 * E) * G) * t ^ 3 := by ring

end BrownianAffine
