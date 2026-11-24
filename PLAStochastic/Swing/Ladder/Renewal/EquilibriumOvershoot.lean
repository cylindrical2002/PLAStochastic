import PLAStochastic.Swing.Ladder.Law.UniformMoments
import Mathlib.MeasureTheory.Integral.Layercake

/-! # Equilibrium overshoot and residual life

`eq:equilibriumovershoot` defines the limiting overshoot by the density
`P(H>o)/E H` on `[0,∞)`; `eq:overshootrenewalidentity` expresses the overshoot
above a level as the residual life of the ladder renewal process.  Both are
recorded here as explicit measure-theoretic objects, together with the parts of
the paper's argument that need no renewal theorem: the normalisation of the
equilibrium law, and the vanishing of the near part of the residual-life
integral.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The mean of a nonnegative inter-arrival law, in `ℝ≥0∞`. -/
noncomputable def ladderMeanENN (ν : Measure ℝ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal x ∂ν

theorem measurable_ladderTail (ν : Measure ℝ) : Measurable (fun o : ℝ => ν (Ioi o)) := by
  refine Antitone.measurable ?_
  intro s t hst
  exact measure_mono (Ioi_subset_Ioi hst)

/-- Layer cake: the mean is the integral of the tail. -/
theorem ladderMeanENN_eq_lintegral_tail (ν : Measure ℝ) [SFinite ν]
    (hnn : 0 ≤ᵐ[ν] fun x : ℝ => x) :
    ladderMeanENN ν = ∫⁻ o in Ioi (0 : ℝ), ν (Ioi o) := by
  have h := lintegral_eq_lintegral_meas_lt ν hnn aemeasurable_id
  rw [ladderMeanENN, h]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  congr 1

/-- The equilibrium overshoot law of `eq:equilibriumovershoot`. -/
noncomputable def equilibriumOvershootLaw (ν : Measure ℝ) : Measure ℝ :=
  (volume.restrict (Ici (0 : ℝ))).withDensity (fun o => ν (Ioi o) / ladderMeanENN ν)

/-- The equilibrium overshoot tail. -/
noncomputable def equilibriumOvershootTail (ν : Measure ℝ) (t : ℝ) : ℝ≥0∞ :=
  (∫⁻ o in Ioi t, ν (Ioi o)) / ladderMeanENN ν

theorem equilibriumOvershootLaw_apply (ν : Measure ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    equilibriumOvershootLaw ν A =
      ∫⁻ o in A ∩ Ici (0 : ℝ), ν (Ioi o) / ladderMeanENN ν := by
  rw [equilibriumOvershootLaw, withDensity_apply _ hA, Measure.restrict_restrict hA]

/-- The equilibrium overshoot law is a probability measure. -/
theorem equilibriumOvershootLaw_isProbabilityMeasure (ν : Measure ℝ) [SFinite ν]
    (hnn : 0 ≤ᵐ[ν] fun x : ℝ => x)
    (h0 : ladderMeanENN ν ≠ 0) (htop : ladderMeanENN ν ≠ ⊤) :
    IsProbabilityMeasure (equilibriumOvershootLaw ν) := by
  constructor
  rw [equilibriumOvershootLaw, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_restrict MeasurableSet.univ, univ_inter]
  have hpull : (∫⁻ o in Ici (0 : ℝ), ν (Ioi o) / ladderMeanENN ν) =
      (∫⁻ o in Ici (0 : ℝ), ν (Ioi o)) / ladderMeanENN ν := by
    simp_rw [ENNReal.div_eq_inv_mul]
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr h0)]
  have hIci : (∫⁻ o in Ici (0 : ℝ), ν (Ioi o)) = ∫⁻ o in Ioi (0 : ℝ), ν (Ioi o) := by
    rw [Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm]
  rw [hpull, hIci, ← ladderMeanENN_eq_lintegral_tail ν hnn,
    ENNReal.div_self h0 htop]

/-! ### The residual-life expression -/

/-- `eq:overshootrenewalidentity`: the renewal expression for the tail of the
overshoot above the level `b`. -/
noncomputable def renewalOvershootTail (ν : Measure ℝ) (b t : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Icc (0 : ℝ) b, ν (Ioi (b+t-s)) ∂(ladderRenewalMeasure ν)

/-- The near part of the residual-life integral is controlled by the distant
ladder tail times the renewal mass, with no renewal theorem. -/
theorem renewalOvershootTail_near_le (ν : Measure ℝ) {b t : ℝ} :
    (∫⁻ s in Icc (0 : ℝ) (b/2), ν (Ioi (b+t-s)) ∂(ladderRenewalMeasure ν)) ≤
      ν (Ioi (b/2+t)) * ladderRenewalMeasure ν (Icc 0 (b/2)) := by
  have hmono : ∀ s ∈ Icc (0 : ℝ) (b/2), ν (Ioi (b+t-s)) ≤ ν (Ioi (b/2+t)) := by
    intro s hs
    exact measure_mono (Ioi_subset_Ioi (by linarith [hs.2]))
  calc (∫⁻ s in Icc (0 : ℝ) (b/2), ν (Ioi (b+t-s)) ∂(ladderRenewalMeasure ν))
      ≤ ∫⁻ _s in Icc (0 : ℝ) (b/2), ν (Ioi (b/2+t)) ∂(ladderRenewalMeasure ν) :=
        setLIntegral_mono' measurableSet_Icc hmono
    _ = ν (Ioi (b/2+t)) * ladderRenewalMeasure ν (Icc 0 (b/2)) := by
        rw [setLIntegral_const]

/-! ### The actual Gaussian ladder family -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem gaussianAscendingLadderLaw_mean_ne_zero
    (hX : ∀ n, Measurable (X n))
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {M a : ℝ} (ha : 0 < a) (haM : a ≤ M) :
    ladderMeanENN (gaussianAscendingLadderLaw X μ a) ≠ 0 := by
  have hc := gaussianAscendingLadderCommonDensity_pos M
  have hlow := lintegral_ofReal_ge_of_minorization
    (gaussianAscendingLadderLaw_common_minorization hX (hG 0) ha.le haM)
  intro h
  rw [ladderMeanENN] at h
  rw [h, le_zero_iff, ENNReal.ofReal_eq_zero] at hlow
  linarith

theorem gaussianAscendingLadderLaw_mean_ne_top
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) :
    ladderMeanENN (gaussianAscendingLadderLaw X μ a) ≠ ⊤ := by
  have := hi.isProbabilityMeasure
  have hmeas : Measurable (gaussianAscendingLadderHeight X a) :=
    gaussianAscendingLadderHeight_measurable hX a
  have hHint : Integrable (gaussianAscendingLadderHeight X a) μ :=
    gaussianAscendingLadderHeight_integrable_compact hX hi hG hδ hδa haM
  have hint' : Integrable (fun x : ℝ => x) (gaussianAscendingLadderLaw X μ a) :=
    (integrable_map_measure aestronglyMeasurable_id hmeas.aemeasurable).mpr hHint
  have hnn : 0 ≤ᵐ[gaussianAscendingLadderLaw X μ a] fun x : ℝ => x := by
    rw [Filter.EventuallyLE, ae_iff]
    have hset : {x : ℝ | ¬ (0 : ℝ) ≤ x} = {x : ℝ | x < 0} := by
      ext x
      simp
    have hmsIio : MeasurableSet {x : ℝ | x < 0} := by
      have h : {x : ℝ | x < 0} = Iio (0 : ℝ) := by ext x; simp
      rw [h]
      exact measurableSet_Iio
    have hpre : (gaussianAscendingLadderHeight X a) ⁻¹' {x : ℝ | x < 0} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact gaussianAscendingLadderHeight_nonneg (X := X) a ω
    show gaussianAscendingLadderLaw X μ a {x : ℝ | ¬ (0 : ℝ) ≤ x} = 0
    rw [hset, show gaussianAscendingLadderLaw X μ a =
      μ.map (gaussianAscendingLadderHeight X a) from rfl,
      Measure.map_apply hmeas hmsIio, hpre, measure_empty]
  have hfin := hint'.2
  rw [hasFiniteIntegral_iff_ofReal hnn] at hfin
  exact hfin.ne

/-- The equilibrium overshoot law of the actual positive-drift ladder height is
a probability measure for every drift in a compact positive interval. -/
theorem gaussianAscendingLadderEquilibrium_isProbabilityMeasure
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) :
    IsProbabilityMeasure (equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a)) := by
  have := hi.isProbabilityMeasure
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hmeas : Measurable (gaussianAscendingLadderHeight X a) :=
    gaussianAscendingLadderHeight_measurable hX a
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have hnn : 0 ≤ᵐ[gaussianAscendingLadderLaw X μ a] fun x : ℝ => x := by
    rw [Filter.EventuallyLE, ae_iff]
    have hset : {x : ℝ | ¬ (0 : ℝ) ≤ x} = {x : ℝ | x < 0} := by
      ext x
      simp
    have hmsIio : MeasurableSet {x : ℝ | x < 0} := by
      have h : {x : ℝ | x < 0} = Iio (0 : ℝ) := by ext x; simp
      rw [h]
      exact measurableSet_Iio
    have hpre : (gaussianAscendingLadderHeight X a) ⁻¹' {x : ℝ | x < 0} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact gaussianAscendingLadderHeight_nonneg (X := X) a ω
    show gaussianAscendingLadderLaw X μ a {x : ℝ | ¬ (0 : ℝ) ≤ x} = 0
    rw [hset, show gaussianAscendingLadderLaw X μ a =
      μ.map (gaussianAscendingLadderHeight X a) from rfl,
      Measure.map_apply hmeas hmsIio, hpre, measure_empty]
  exact equilibriumOvershootLaw_isProbabilityMeasure _ hnn
    (gaussianAscendingLadderLaw_mean_ne_zero hX hG ha haM)
    (gaussianAscendingLadderLaw_mean_ne_top hX hi hG hδ hδa haM)

end SwingRepair
