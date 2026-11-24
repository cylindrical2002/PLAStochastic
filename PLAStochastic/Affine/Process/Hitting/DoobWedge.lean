import PLAStochastic.Brownian.Hitting.WedgeSurvival
import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.WedgeSeries.Summability
import PLAStochastic.Affine.Process.Hitting.SupremumExponentialLaw

/-!
# Doob's expanding-wedge probability from actual Brownian stopping

Each series mode is a Gaussian exponential martingale. Summability permits
termwise integration at bounded exits; dominated convergence then removes the
cutoff and identifies the limit with the closed-wedge survival indicator.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

def stoppedWedgeCoordinates (B : ℝ≥0 → Ω → ℝ) (a b : ℝ) (H : ℕ) (ω : Ω) : ℝ × ℝ :=
  let t := boundedWedgeExit B a b H ω
  (a + (t : ℝ) - B t ω, b + (t : ℝ) + B t ω)

def stoppedWedgeSeries (B : ℝ≥0 → Ω → ℝ) (a b : ℝ) (H : ℕ) (ω : Ω) : ℝ :=
  wedgeSeries (stoppedWedgeCoordinates B a b H ω).1 (stoppedWedgeCoordinates B a b H ω).2

theorem integral_wedgeTerm_at_exit (hB : IsBrownianReal B μ) (a b : ℝ) (n H : ℕ) :
    Integrable (fun ω => wedgeTerm n (stoppedWedgeCoordinates B a b H ω).1
      (stoppedWedgeCoordinates B a b H ω).2) μ ∧
    (∫ ω, wedgeTerm n (stoppedWedgeCoordinates B a b H ω).1
      (stoppedWedgeCoordinates B a b H ω).2 ∂μ) = wedgeTerm n a b := by
  let m : ℝ := (n : ℝ) + 1
  let P : Ω → ℝ := fun ω =>
    let p := stoppedWedgeCoordinates B a b H ω
    Real.exp (-(m ^ 2) * (p.1 + p.2) + m * (p.1 - p.2))
  let N : Ω → ℝ := fun ω =>
    let p := stoppedWedgeCoordinates B a b H ω
    Real.exp (-((-m) ^ 2) * (p.1 + p.2) + (-m) * (p.1 - p.2))
  have hp : Integrable P μ ∧ (∫ ω, P ω ∂μ) = Real.exp (-(m ^ 2) * (a + b) + m * (a - b)) :=
    integral_wedgeExponential_boundedWedgeExit hB m a b H
  have hn : Integrable N μ ∧ (∫ ω, N ω ∂μ) = Real.exp (-((-m) ^ 2) * (a + b) + (-m) * (a - b)) :=
    integral_wedgeExponential_boundedWedgeExit hB (-m) a b H
  have heq : (fun ω => wedgeTerm n (stoppedWedgeCoordinates B a b H ω).1
      (stoppedWedgeCoordinates B a b H ω).2) =
      (fun ω => (-1 : ℝ) ^ (n + 1) * (P ω + N ω)) := by
    funext ω
    simp only [wedgeTerm, P, N, m, neg_sq, neg_mul, sub_eq_add_neg]
  constructor
  · rw [heq]
    exact (hp.1.add hn.1).const_mul _
  · rw [heq, integral_const_mul, integral_add hp.1 hn.1, hp.2, hn.2]
    simp only [wedgeTerm, m, neg_sq, neg_mul, sub_eq_add_neg]

theorem stoppedWedgeCoordinates_mem_ae (hB : IsBrownianReal B μ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (H : ℕ) :
    ∀ᵐ ω ∂μ, 0 ≤ (stoppedWedgeCoordinates B a b H ω).1 ∧
      0 ≤ (stoppedWedgeCoordinates B a b H ω).2 ∧
      a + b ≤ (stoppedWedgeCoordinates B a b H ω).1 + (stoppedWedgeCoordinates B a b H ω).2 := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hc h0
  have hn := boundedWedgeExit_nonneg_coordinates (T := (H : ℝ≥0)) hc h0 ha hb
  refine ⟨hn.1, hn.2, ?_⟩
  dsimp only [stoppedWedgeCoordinates]
  have ht := (boundedWedgeExit B a b H ω).property
  linarith

theorem integral_stoppedWedgeSeries (hB : IsBrownianReal B μ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (H : ℕ) :
    Integrable (stoppedWedgeSeries B a b H) μ ∧
      (∫ ω, stoppedWedgeSeries B a b H ω ∂μ) = wedgeSeries a b := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hab : 0 < a + b := add_pos ha hb
  let F : ℕ → Ω → ℝ := fun n ω => wedgeTerm n (stoppedWedgeCoordinates B a b H ω).1
    (stoppedWedgeCoordinates B a b H ω).2
  let C : ℕ → ℝ := fun n => 2 * Real.exp (-(n : ℝ) * (a + b))
  have hF (n : ℕ) : Integrable (F n) μ := (integral_wedgeTerm_at_exit hB a b n H).1
  have hC : Summable C := summable_wedgeBound hab
  have hbound : ∀ᵐ ω ∂μ, ∀ n, ‖F n ω‖ ≤ C n := by
    filter_upwards [stoppedWedgeCoordinates_mem_ae hB ha.le hb.le H] with ω hω n
    exact wedgeTerm_bound hab.le hω.1 hω.2.1 hω.2.2 n
  have hsum : ∀ᵐ ω ∂μ, Summable (fun n => F n ω) := by
    filter_upwards [hbound] with ω hω
    exact hC.of_norm_bounded hω
  have hmeas : AEStronglyMeasurable (fun ω => ∑' n, F n ω) μ := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun N : ℕ => (integrable_finsetSum (Finset.range N) (fun n _ => hF n)).aestronglyMeasurable)
    filter_upwards [hsum] with ω hω
    exact hω.tendsto_sum_tsum_nat
  have hi : Integrable (fun ω => ∑' n, F n ω) μ := by
    apply (integrable_const (∑' n, C n)).mono' hmeas
    filter_upwards [hbound] with ω hω
    exact tsum_of_norm_bounded hC.hasSum hω
  have hnorm : Summable (fun n => ∫ ω, ‖F n ω‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) ?_ hC
    intro n
    calc
      (∫ ω, ‖F n ω‖ ∂μ) ≤ ∫ _ : Ω, C n ∂μ :=
        integral_mono_ae (hF n).norm (integrable_const _) (hbound.mono (fun _ hω => hω n))
      _ = C n := by simp
  constructor
  · exact (integrable_const 1).add hi
  · change (∫ ω, 1 + ∑' n, F n ω ∂μ) = _
    rw [integral_add (integrable_const 1) hi,
      ← integral_tsum_of_summable_integral_norm hF hnorm]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    congr 1
    apply tsum_congr
    intro n
    exact (integral_wedgeTerm_at_exit hB a b n H).2

theorem stoppedWedgeSeries_tendsto_indicator (hB : IsBrownianReal B μ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᵐ ω ∂μ, Tendsto (fun H : ℕ => stoppedWedgeSeries B a b H ω) atTop
      (𝓝 ((wedgeSurvival B a b).indicator (fun _ => (1 : ℝ)) ω)) := by
  classical
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero,
    brownian_wedge_coordinates_tendsto_atTop_ae hB a b] with ω hc h0 hcoord
  by_cases hω : ω ∈ wedgeSurvival B a b
  · rw [indicator_of_mem hω]
    have ht := tendsto_wedgeSeries_of_atTop hcoord.1 hcoord.2
    convert! ht using 1
    funext H
    simp only [stoppedWedgeSeries, stoppedWedgeCoordinates, boundedWedgeExit_eq_cutoff_of_survival hω,
      NNReal.coe_natCast]
  · rw [indicator_of_notMem hω]
    apply tendsto_const_nhds.congr'
    filter_upwards [boundedWedgeExit_eventually_zero_coordinate hc h0 ha.le hb.le hω] with H hH
    let p := stoppedWedgeCoordinates B a b H ω
    have hs : 0 < p.1 + p.2 := by
      dsimp only [p, stoppedWedgeCoordinates]
      have ht := (boundedWedgeExit B a b H ω).property
      linarith
    symm
    change wedgeSeries p.1 p.2 = 0
    change p.1 = 0 ∨ p.2 = 0 at hH
    rcases hH with h | h
    · rw [h]
      exact wedgeSeries_zero_left (by simpa only [h, zero_add] using hs)
    · rw [h]
      exact wedgeSeries_zero_right (by simpa only [h, add_zero] using hs)

/-- Doob's wedge series is the actual probability of remaining between both
expanding boundaries for all nonnegative times. -/
theorem measureReal_wedgeSurvival_eq_wedgeSeries (hB : IsBrownianReal B μ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    μ.real (wedgeSurvival B a b) = wedgeSeries a b := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let C := 1 + ∑' n : ℕ, 2 * Real.exp (-(n : ℝ) * (a + b))
  have hbound (H : ℕ) : ∀ᵐ ω ∂μ, ‖stoppedWedgeSeries B a b H ω‖ ≤ C := by
    filter_upwards [stoppedWedgeCoordinates_mem_ae hB ha.le hb.le H] with ω hω
    exact wedgeSeries_bound (add_pos ha hb) hω.1 hω.2.1 hω.2.2
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Ω => C)
    (fun H => (integral_stoppedWedgeSeries hB ha hb H).1.aestronglyMeasurable)
    (integrable_const _) hbound (stoppedWedgeSeries_tendsto_indicator hB ha hb)
  have heq : (fun H : ℕ => ∫ ω, stoppedWedgeSeries B a b H ω ∂μ) = fun _ => wedgeSeries a b :=
    funext (fun H => (integral_stoppedWedgeSeries hB ha hb H).2)
  rw [heq] at ht
  have hind : (∫ ω, (wedgeSurvival B a b).indicator (fun _ => (1 : ℝ)) ω ∂μ) =
      μ.real (wedgeSurvival B a b) := by
    rw [integral_indicator₀ (nullMeasurableSet_wedgeSurvival hB ha.le hb.le)]
    simp
  rw [hind] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem measure_wedgeSurvival_eq_wedgeSeries (hB : IsBrownianReal B μ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    μ (wedgeSurvival B a b) = ENNReal.ofReal (wedgeSeries a b) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  rw [← measureReal_wedgeSurvival_eq_wedgeSeries hB ha hb, measureReal_def, ENNReal.ofReal_toReal]
  exact measure_ne_top _ _

theorem measure_driftedSup_joint_le (hB : IsBrownianReal B μ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    μ {ω | driftedSup (B · ω) 1 ≤ ENNReal.ofReal a ∧
      driftedSup (fun t => -B t ω) 1 ≤ ENNReal.ofReal b} = ENNReal.ofReal (wedgeSeries a b) := by
  have heq : {ω | driftedSup (B · ω) 1 ≤ ENNReal.ofReal a ∧
      driftedSup (fun t => -B t ω) 1 ≤ ENNReal.ofReal b} = wedgeSurvival B a b := by
    ext ω
    exact (wedgeSurvival_iff_driftedSup_bounds ha.le hb.le ω).symm
  rw [heq]
  exact measure_wedgeSurvival_eq_wedgeSeries hB ha hb

/-- The joint CDF for the manuscript's literal real-valued suprema. -/
theorem measure_realDriftedSup_joint_le (hB : IsBrownianReal B μ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    μ {ω | realDriftedSup (B · ω) 1 ≤ a ∧
      realDriftedSup (fun t => -B t ω) 1 ≤ b} = ENNReal.ofReal (wedgeSeries a b) := by
  rw [← measure_driftedSup_joint_le hB ha hb]
  apply measure_congr
  filter_upwards [driftedPair_ne_top_ae hB] with ω hω
  apply propext
  change (realDriftedSup (B · ω) 1 ≤ a ∧ realDriftedSup (fun t => -B t ω) 1 ≤ b) ↔
    (driftedSup (B · ω) 1 ≤ ENNReal.ofReal a ∧ driftedSup (fun t => -B t ω) 1 ≤ ENNReal.ofReal b)
  simp only [driftedSup_eq_ofReal_realDriftedSup hω.1,
    driftedSup_eq_ofReal_realDriftedSup hω.2, ENNReal.ofReal_le_ofReal_iff ha.le,
    ENNReal.ofReal_le_ofReal_iff hb.le]

end BrownianAffine
