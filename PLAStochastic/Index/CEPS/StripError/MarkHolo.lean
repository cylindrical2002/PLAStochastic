import PLAStochastic.Index.CEPS.StripError.NormalIdentity
import Mathlib.Probability.Moments.ComplexMGF

/-!
# WP9: the actual strip entrance as a holomorphic function of the mark

For the band walk `V = kWalk 0 β a`, the marked entrance `H_t = cepsStripSeries ν β a l 0 (-t) q`
is a series of Laplace transforms of the killed walk, which lives in `[0, l]`. Each term is a
complex moment generating function of a bounded variable, hence entire
(`differentiable_cepsStripMark`), and the series converges uniformly on every vertical strip:
`H` is holomorphic in `t` (`cepsStripSeries_differentiableOn`) with
`‖H_t‖ ≤ e^{|Re t| l} ∑ₙ |e^{-qn}| P(alive at n)` (`norm_cepsStripSeries_le`).

With the step transform written through the link `ν ∘ (a · - β)⁻¹ = driftStep ρ μ`
(`cepsStepMgf_neg_eq`), the WP8 telescope reads `d(t) H_t = 1 - u_t - ℓ_t` with the canonical
denominator `d = cepsD ρ μ q` (`strip_actual_telescope`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex Metric Filter
open WienerHopf

/-! ## The step transform through the link -/

theorem cepsStepMgf_neg_eq (ν : ProbabilityMeasure ℝ) (β a : ℝ) {ρ : Measure ℝ} {μ : ℝ}
    (hlink : (ν : Measure ℝ).map (fun x => a * x - β) = driftStep ρ μ) (t : ℂ) :
    cepsStepMgf ν β a (-t) = cexp (μ * t) * stepTransform ρ t := by
  rw [← stepTransform_driftStep, ← hlink]
  unfold cepsStepMgf stepTransform
  rw [integral_map (by fun_prop) (by fun_prop)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  congr 1
  push_cast
  ring

/-- The WP8 telescope with the canonical denominator. -/
theorem strip_actual_telescope {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ} {D₀ : ℝ}
    (hf : CepsGapDensity ν f D₀) (β : ℝ) {a : ℝ} (ha : a ≠ 0) {ρ : Measure ℝ} {μ : ℝ}
    (hlink : (ν : Measure ℝ).map (fun x => a * x - β) = driftStep ρ μ) {l : ℝ} (hl : 0 ≤ l)
    {t q : ℂ} (ht : t.re = 0) (hq : 0 ≤ q.re) :
    cepsD ρ μ q t * cepsStripSeries ν β a l 0 (-t) q =
      1 - cepsStripExit ν β a l 0 (Iio 0) (-t) q - cepsStripExit ν β a l 0 (Ioi l) (-t) q := by
  have h := hf.cepsStrip_telescope β ha (l := l) (y := 0) ⟨le_rfl, hl⟩
    (s := -t) (by rw [neg_re, ht, neg_zero]) hq
  rw [cepsStepMgf_neg_eq ν β a hlink t] at h
  rw [← h]
  unfold cepsD
  ring

/-! ## Holomorphy in the mark -/

/-- The alive set at time `n`. -/
def stripAliveSet (β a l : ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  {g | ∀ i ≤ n, kWalk 0 β a g i ∈ Icc 0 l}

theorem measurableSet_stripAliveSet (β a l : ℝ) (n : ℕ) :
    MeasurableSet (stripAliveSet β a l n) := by
  have h : stripAliveSet β a l n = ⋂ i ∈ Finset.range (n + 1),
      (fun g => kWalk 0 β a g i) ⁻¹' Icc 0 l := by
    ext g
    simp [stripAliveSet]
  rw [h]
  exact Finset.measurableSet_biInter _ fun i _ =>
    measurableSet_Icc.preimage (measurable_kWalk_right 0 β a i)

theorem cepsStripMark_eq_complexMGF (ν : ProbabilityMeasure ℝ) (β a l : ℝ) (n : ℕ) (t : ℂ) :
    cepsStripMark ν β a l 0 (-t) n =
      complexMGF (fun g => -kWalk 0 β a g n) ((iidLaw ν).restrict (stripAliveSet β a l n)) t := by
  classical
  unfold cepsStripMark complexMGF
  rw [← integral_indicator (measurableSet_stripAliveSet β a l n)]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  rw [krAlive_eq_ite]
  by_cases h : ∀ i ≤ n, kWalk 0 β a g i ∈ Icc 0 l
  · rw [if_pos h, indicator_of_mem (show g ∈ stripAliveSet β a l n from h)]
    simp only [Complex.ofReal_one, one_mul, sub_zero]
    congr 1
    push_cast
    ring
  · rw [if_neg h, indicator_of_notMem (show g ∉ stripAliveSet β a l n from h)]
    simp

theorem differentiable_cepsStripMark (ν : ProbabilityMeasure ℝ) (β a l : ℝ) (n : ℕ) :
    Differentiable ℂ (fun t => cepsStripMark ν β a l 0 (-t) n) := by
  intro t
  simp_rw [cepsStripMark_eq_complexMGF]
  have hX : AEMeasurable (fun g : ℕ → ℝ => -kWalk 0 β a g n)
      ((iidLaw ν).restrict (stripAliveSet β a l n)) :=
    (measurable_kWalk_right 0 β a n).neg.aemeasurable
  have hset : integrableExpSet (fun g : ℕ → ℝ => -kWalk 0 β a g n)
      ((iidLaw ν).restrict (stripAliveSet β a l n)) = univ := by
    ext s
    simp only [mem_univ, iff_true]
    refine Integrable.of_bound ((Real.continuous_exp.measurable.comp (measurable_const.mul
      (measurable_kWalk_right 0 β a n).neg)).aestronglyMeasurable) (Real.exp (|s| * |l|)) ?_
    filter_upwards [ae_restrict_mem (measurableSet_stripAliveSet β a l n)] with g hg
    have hv := hg n le_rfl
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    have h1 : |(-kWalk 0 β a g n)| ≤ |l| := by
      rw [abs_neg, abs_of_nonneg hv.1]
      exact hv.2.trans (le_abs_self l)
    calc s * -kWalk 0 β a g n ≤ |s * -kWalk 0 β a g n| := le_abs_self _
      _ = |s| * |(-kWalk 0 β a g n)| := abs_mul _ _
      _ ≤ |s| * |l| := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  exact (analyticAt_complexMGF (by simp [hset])).differentiableAt

theorem norm_cepsStripMark_le_exp (ν : ProbabilityMeasure ℝ) (β a : ℝ) {l : ℝ}
    (n : ℕ) (t : ℂ) :
    ‖cepsStripMark ν β a l 0 (-t) n‖ ≤
      Real.exp (|t.re| * l) * krSurv (Icc 0 l) (ν : Measure ℝ) β a n 0 := by
  unfold cepsStripMark
  rw [krSurv_eq_integral measurableSet_Icc, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((kr_integrable_of_bdd
    (measurable_krAlive_right measurableSet_Icc _ _ n 0) (abs_krAlive_le_one n 0)).const_mul _)
    (Eventually.of_forall fun g => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (krAlive_nonneg _ _ _)]
  rw [krAlive_eq_ite]
  split_ifs with h
  · have hv := h n le_rfl
    rw [one_mul, mul_one, Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    simp only [sub_zero, mul_re, neg_re, ofReal_re, neg_im, ofReal_im, mul_zero, sub_zero]
    have h1 : -t.re * kWalk 0 β a g n ≤ |t.re| * kWalk 0 β a g n :=
      mul_le_mul_of_nonneg_right (neg_le_abs t.re) hv.1
    have h2 : |t.re| * kWalk 0 β a g n ≤ |t.re| * l :=
      mul_le_mul_of_nonneg_left hv.2 (abs_nonneg _)
    linarith
  · simp

/-- **The marked entrance is holomorphic in the mark** on every vertical strip. -/
theorem cepsStripSeries_differentiableOn {ν : ProbabilityMeasure ℝ} (β a : ℝ) {l : ℝ}
    (hl : 0 ≤ l) {q : ℂ} (hsum : Summable fun n : ℕ =>
      ‖Complex.exp (-q * n)‖ * krSurv (Icc 0 l) (ν : Measure ℝ) β a n 0) {R : ℝ} :
    DifferentiableOn ℂ (fun t => cepsStripSeries ν β a l 0 (-t) q) {t : ℂ | |t.re| < R} := by
  have hU : IsOpen {t : ℂ | |t.re| < R} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  refine differentiableOn_tsum_of_summable_norm (hsum.mul_left (Real.exp (|R| * l)))
    (fun n => ((differentiable_cepsStripMark ν β a l n).const_mul _).differentiableOn) hU
    (fun n t ht => ?_)
  rw [norm_mul]
  have ht' : |t.re| ≤ |R| := (le_of_lt ht).trans (le_abs_self R)
  calc _ ≤ ‖Complex.exp (-q * n)‖ *
        (Real.exp (|t.re| * l) * krSurv (Icc 0 l) (ν : Measure ℝ) β a n 0) :=
      mul_le_mul_of_nonneg_left (norm_cepsStripMark_le_exp ν β a n t) (norm_nonneg _)
    _ ≤ ‖Complex.exp (-q * n)‖ *
        (Real.exp (|R| * l) * krSurv (Icc 0 l) (ν : Measure ℝ) β a n 0) := by
      gcongr
      exact krSurv_nonneg measurableSet_Icc ν β a n 0
    _ = _ := by ring

theorem norm_cepsStripSeries_le {ν : ProbabilityMeasure ℝ} (β a : ℝ) {l : ℝ}
    {q : ℂ} (hsum : Summable fun n : ℕ =>
      ‖Complex.exp (-q * n)‖ * krSurv (Icc 0 l) (ν : Measure ℝ) β a n 0) (t : ℂ) :
    ‖cepsStripSeries ν β a l 0 (-t) q‖ ≤ Real.exp (|t.re| * l) *
      ∑' n : ℕ, ‖Complex.exp (-q * n)‖ * krSurv (Icc 0 l) (ν : Measure ℝ) β a n 0 := by
  unfold cepsStripSeries
  have hb : ∀ n : ℕ, ‖Complex.exp (-q * n) * cepsStripMark ν β a l 0 (-t) n‖ ≤
      Real.exp (|t.re| * l) * (‖Complex.exp (-q * n)‖ * krSurv (Icc 0 l) (ν : Measure ℝ) β a n 0) := by
    intro n
    rw [norm_mul]
    calc _ ≤ ‖Complex.exp (-q * n)‖ *
          (Real.exp (|t.re| * l) * krSurv (Icc 0 l) (ν : Measure ℝ) β a n 0) :=
        mul_le_mul_of_nonneg_left (norm_cepsStripMark_le_exp ν β a n t) (norm_nonneg _)
      _ = _ := by ring
  have hs := hsum.mul_left (Real.exp (|t.re| * l))
  refine (norm_tsum_le_tsum_norm (hs.of_nonneg_of_le (fun n => norm_nonneg _) hb)).trans ?_
  rw [← tsum_mul_left]
  exact (hs.of_nonneg_of_le (fun n => norm_nonneg _) hb).tsum_le_tsum hb hs

/-- The marked entrance at mark zero is the survival series. -/
theorem cepsStripSeries_zero_eq_surv (ν : ProbabilityMeasure ℝ) (β a l : ℝ) (q : ℂ) :
    cepsStripSeries ν β a l 0 (-0) q =
      ∑' n : ℕ, Complex.exp (-q * n) * (krSurv (Icc 0 l) (ν : Measure ℝ) β a n 0 : ℂ) := by
  unfold cepsStripSeries
  refine tsum_congr fun n => ?_
  congr 1
  unfold cepsStripMark
  rw [krSurv_eq_integral measurableSet_Icc, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp

end

end PGM
