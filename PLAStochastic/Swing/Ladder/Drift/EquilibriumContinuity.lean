import PLAStochastic.ForMathlib.Probability.TailComparison.L1Distance
import PLAStochastic.Swing.StationaryLimit.MarginKernel.Limiting
import PLAStochastic.Swing.Ladder.Drift.L1Continuity

/-! # Continuity of the equilibrium overshoot in the drift

The real-valued equilibrium density `P(H_a > t)/E H_a` is `L¹`-continuous in the
drift, because the ladder height is `L¹`-continuous and the ladder mean is
bounded below on every compact positive interval.  Consequently the reflected
equilibrium law `Law(a - O_a)` is weakly continuous in the drift against
bounded Lipschitz test functions.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- The real-valued ladder tail. -/
def ladderTailReal (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a t : ℝ) : ℝ :=
  μ.real {ω | t < gaussianAscendingLadderHeight X a ω}

/-- The real-valued ladder mean. -/
def ladderMeanReal (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a : ℝ) : ℝ :=
  ∫ ω, gaussianAscendingLadderHeight X a ω ∂μ

/-- The real-valued equilibrium overshoot density. -/
def equilibriumDensityReal (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a t : ℝ) : ℝ :=
  ladderTailReal X μ a t / ladderMeanReal X μ a

theorem ladderTailReal_eq (hX : ∀ n, Measurable (X n)) (a t : ℝ) :
    ladderTailReal X μ a t = (gaussianAscendingLadderLaw X μ a (Ioi t)).toReal := by
  rw [ladderTailReal, gaussianAscendingLadderLaw,
    Measure.map_apply (gaussianAscendingLadderHeight_measurable hX a) measurableSet_Ioi]
  rfl

theorem ladderMeanReal_eq (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) :
    ladderMeanReal X μ a = (ladderMeanENN (gaussianAscendingLadderLaw X μ a)).toReal := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hlprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have hnn := gaussianAscendingLadderLaw_nonneg_ae (X := X) (μ := μ) hX a
  have hint : Integrable (gaussianAscendingLadderHeight X a) μ :=
    gaussianAscendingLadderHeight_integrable_compact hX hi hG hδ hδa haM
  have hmapint : Integrable (fun x : ℝ => x) (gaussianAscendingLadderLaw X μ a) :=
    (integrable_map_measure aestronglyMeasurable_id
      (gaussianAscendingLadderHeight_measurable hX a).aemeasurable).mpr hint
  have hmapaux := integral_map (μ := μ)
      (φ := gaussianAscendingLadderHeight X a) (f := fun x : ℝ => x)
      (gaussianAscendingLadderHeight_measurable hX a).aemeasurable
      measurable_id.aestronglyMeasurable
  have hmap : ladderMeanReal X μ a = ∫ x, x ∂(gaussianAscendingLadderLaw X μ a) :=
    hmapaux.symm
  rw [hmap, integral_eq_lintegral_of_nonneg_ae hnn aestronglyMeasurable_id]
  rfl

theorem ladderMeanReal_pos (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) :
    gaussianAscendingLadderCommonDensity M ≤ ladderMeanReal X μ a :=
  gaussianAscendingLadderHeight_mean_ge hX hi hG hδ hδa haM

/-- The layer-cake identity for the ladder tail. -/
theorem integral_ladderTailReal (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) :
    (∫ t in Ioi (0 : ℝ), ladderTailReal X μ a t) = ladderMeanReal X μ a := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hint : Integrable (gaussianAscendingLadderHeight X a) μ :=
    gaussianAscendingLadderHeight_integrable_compact hX hi hG hδ hδa haM
  exact (hint.integral_eq_integral_meas_lt
    (ae_of_all _ (fun ω => gaussianAscendingLadderHeight_nonneg (X := X) a ω))).symm

theorem ladderTailReal_nonneg (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a t : ℝ) :
    0 ≤ ladderTailReal X μ a t := measureReal_nonneg

theorem measurable_ladderTailReal (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a : ℝ) :
    Measurable (ladderTailReal X μ a) := by
  refine Measurable.ennreal_toReal ?_
  exact Antitone.measurable (fun s t hst => measure_mono (fun ω h => lt_of_le_of_lt hst h))

theorem measurable_equilibriumDensityReal (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a : ℝ) :
    Measurable (equilibriumDensityReal X μ a) :=
  (measurable_ladderTailReal X μ a).div_const _

theorem integrableOn_ladderTailReal (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) :
    IntegrableOn (ladderTailReal X μ a) (Ioi 0) volume := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hint : Integrable (gaussianAscendingLadderHeight X a) μ :=
    gaussianAscendingLadderHeight_integrable_compact hX hi hG hδ hδa haM
  exact integrable_meas_gt hint
    (ae_of_all _ (fun ω => gaussianAscendingLadderHeight_nonneg (X := X) a ω))

/-- `L¹` continuity of the equilibrium density in the drift. -/
theorem equilibriumDensityReal_l1_tendsto
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun a' : ℝ => ∫ t in Ioi (0 : ℝ),
        |equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t|) (𝓝 a) (𝓝 0) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set δ : ℝ := a/2 with hδdef
  set M : ℝ := 2*a with hMdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have haδ : δ ≤ a := by rw [hδdef]; linarith
  have haM : a ≤ M := by rw [hMdef]; linarith
  set c : ℝ := gaussianAscendingLadderCommonDensity M with hcdef
  have hc : 0 < c := gaussianAscendingLadderCommonDensity_pos M
  have hma : 0 < ladderMeanReal X μ a := lt_of_lt_of_le hc (ladderMeanReal_pos hX hi hG hδ haδ haM)
  -- the two ingredients
  have hl1 := gaussianAscendingLadderHeight_l1_tendsto hX hi hG ha
  have hmean : Tendsto (fun a' : ℝ => ladderMeanReal X μ a') (𝓝 a) (𝓝 (ladderMeanReal X μ a)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Metric.tendsto_nhds] at hl1
    have hnbhd : ∀ᶠ a' : ℝ in 𝓝 a, a' ∈ Ioo δ M :=
      IsOpen.mem_nhds isOpen_Ioo ⟨by rw [hδdef]; linarith, by rw [hMdef]; linarith⟩
    filter_upwards [hnbhd, hl1 ε hε] with a' hmem hsmall
    have hint1 : Integrable (gaussianAscendingLadderHeight X a') μ :=
      gaussianAscendingLadderHeight_integrable_compact hX hi hG hδ hmem.1.le hmem.2.le
    have hint2 : Integrable (gaussianAscendingLadderHeight X a) μ :=
      gaussianAscendingLadderHeight_integrable_compact hX hi hG hδ haδ haM
    have hd : |ladderMeanReal X μ a' - ladderMeanReal X μ a| ≤
        ∫ ω, |gaussianAscendingLadderHeight X a' ω -
          gaussianAscendingLadderHeight X a ω| ∂μ := by
      rw [ladderMeanReal, ladderMeanReal, ← integral_sub hint1 hint2]
      exact abs_integral_le_integral_abs
    have hs : |(∫ ω, |gaussianAscendingLadderHeight X a' ω -
        gaussianAscendingLadderHeight X a ω| ∂μ) - 0| < ε := by
      simpa only [Real.dist_eq] using hsmall
    rw [sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at hs
    rw [Real.dist_eq]
    linarith
  have hinv : Tendsto (fun a' : ℝ => 1/ladderMeanReal X μ a') (𝓝 a)
      (𝓝 (1/ladderMeanReal X μ a)) := tendsto_const_nhds.div hmean hma.ne'
  -- the ε argument
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hbig : 0 < ladderMeanReal X μ a := hma
  have hnbhd : ∀ᶠ a' : ℝ in 𝓝 a, a' ∈ Ioo δ M :=
    IsOpen.mem_nhds isOpen_Ioo ⟨by rw [hδdef]; linarith, by rw [hMdef]; linarith⟩
  rw [Metric.tendsto_nhds] at hl1 hinv
  have hεc : 0 < c*ε/2 := by positivity
  have hεm : 0 < ε/(2*ladderMeanReal X μ a) := by positivity
  filter_upwards [hnbhd, hl1 (c*ε/2) hεc, hinv (ε/(2*ladderMeanReal X μ a)) hεm]
    with a' hmem hL1 hInv
  have hma' : 0 < ladderMeanReal X μ a' :=
    lt_of_lt_of_le hc (ladderMeanReal_pos hX hi hG hδ hmem.1.le hmem.2.le)
  have hmac : c ≤ ladderMeanReal X μ a' := ladderMeanReal_pos hX hi hG hδ hmem.1.le hmem.2.le
  have hint1 : Integrable (gaussianAscendingLadderHeight X a') μ :=
    gaussianAscendingLadderHeight_integrable_compact hX hi hG hδ hmem.1.le hmem.2.le
  have hint2 : Integrable (gaussianAscendingLadderHeight X a) μ :=
    gaussianAscendingLadderHeight_integrable_compact hX hi hG hδ haδ haM
  have hT1 : IntegrableOn (ladderTailReal X μ a') (Ioi 0) volume :=
    integrableOn_ladderTailReal hX hi hG hδ hmem.1.le hmem.2.le
  have hT2 : IntegrableOn (ladderTailReal X μ a) (Ioi 0) volume :=
    integrableOn_ladderTailReal hX hi hG hδ haδ haM
  have hd1 : IntegrableOn (equilibriumDensityReal X μ a') (Ioi 0) volume :=
    hT1.div_const _
  have hd2 : IntegrableOn (equilibriumDensityReal X μ a) (Ioi 0) volume :=
    hT2.div_const _
  have hlhs : IntegrableOn (fun t : ℝ =>
      |equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t|) (Ioi 0) volume :=
    (hd1.sub hd2).abs
  set K : ℝ := |1/ladderMeanReal X μ a' - 1/ladderMeanReal X μ a| with hKdef
  have hK0 : 0 ≤ K := abs_nonneg _
  have hrhs : IntegrableOn (fun t : ℝ =>
      |ladderTailReal X μ a' t - ladderTailReal X μ a t|/ladderMeanReal X μ a' +
        ladderTailReal X μ a t * K) (Ioi 0) volume :=
    ((hT1.sub hT2).abs.div_const _).add (hT2.mul_const _)
  have hpoint : ∀ t : ℝ,
      |equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t| ≤
        |ladderTailReal X μ a' t - ladderTailReal X μ a t|/ladderMeanReal X μ a' +
          ladderTailReal X μ a t * K := by
    intro t
    have hsplit : equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t =
        (ladderTailReal X μ a' t - ladderTailReal X μ a t)/ladderMeanReal X μ a' +
          ladderTailReal X μ a t *
            (1/ladderMeanReal X μ a' - 1/ladderMeanReal X μ a) := by
      rw [equilibriumDensityReal, equilibriumDensityReal]
      field_simp
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_of_pos hma', abs_mul,
      abs_of_nonneg (ladderTailReal_nonneg X μ a t), ← hKdef]
  have hmono := setIntegral_mono_on hlhs hrhs measurableSet_Ioi (fun t _ => hpoint t)
  have hpart1 : IntegrableOn (fun t : ℝ =>
      |ladderTailReal X μ a' t - ladderTailReal X μ a t|/ladderMeanReal X μ a')
      (Ioi 0) volume := (hT1.sub hT2).abs.div_const _
  have hpart2 : IntegrableOn (fun t : ℝ => ladderTailReal X μ a t * K)
      (Ioi 0) volume := hT2.mul_const _
  have hsplitint : (∫ t in Ioi (0 : ℝ),
      (|ladderTailReal X μ a' t - ladderTailReal X μ a t|/ladderMeanReal X μ a' +
        ladderTailReal X μ a t * K)) =
      (∫ t in Ioi (0 : ℝ), |ladderTailReal X μ a' t - ladderTailReal X μ a t|)/
          ladderMeanReal X μ a' + (ladderMeanReal X μ a) * K := by
    rw [integral_add hpart1 hpart2,
      integral_div, integral_mul_const, integral_ladderTailReal hX hi hG hδ haδ haM]
  rw [hsplitint] at hmono
  have htail := integral_abs_meas_gt_sub_le hint1 hint2
    (fun ω => gaussianAscendingLadderHeight_nonneg (X := X) a' ω)
    (fun ω => gaussianAscendingLadderHeight_nonneg (X := X) a ω)
  have hL1' : (∫ ω, |gaussianAscendingLadderHeight X a' ω -
      gaussianAscendingLadderHeight X a ω| ∂μ) < c*ε/2 := by
    have h := hL1
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at h
    exact h
  have hKsmall : K < ε/(2*ladderMeanReal X μ a) := by
    rw [hKdef, ← Real.dist_eq]
    exact hInv
  have htailnn : (0 : ℝ) ≤ ∫ t in Ioi (0 : ℝ),
      |ladderTailReal X μ a' t - ladderTailReal X μ a t| :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ => abs_nonneg _)
  have hstep1 : (∫ t in Ioi (0 : ℝ),
      |ladderTailReal X μ a' t - ladderTailReal X μ a t|)/ladderMeanReal X μ a' < ε/2 := by
    rw [div_lt_iff₀ hma']
    have h1 : (∫ t in Ioi (0 : ℝ),
        |ladderTailReal X μ a' t - ladderTailReal X μ a t|) < c*ε/2 :=
      lt_of_le_of_lt htail hL1'
    nlinarith
  have hstep2 : (ladderMeanReal X μ a) * K < ε/2 := by
    have := mul_lt_mul_of_pos_left hKsmall hbig
    have heq : ladderMeanReal X μ a * (ε/(2*ladderMeanReal X μ a)) = ε/2 := by
      field_simp
    linarith [heq ▸ this]
  have hnn : (0 : ℝ) ≤ ∫ t in Ioi (0 : ℝ),
      |equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t| :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ => abs_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

/-! ### The reflected equilibrium law against a test function -/

theorem swingEquilibriumDensity_toReal (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) (t : ℝ) :
    (swingEquilibriumDensity X μ a t).toReal = equilibriumDensityReal X μ a t := by
  rw [swingEquilibriumDensity, ENNReal.toReal_div, equilibriumDensityReal,
    ← ladderTailReal_eq hX a t, ← ladderMeanReal_eq hX hi hG hδ hδa haM]

theorem swingEquilibriumDensity_lt_top (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    swingEquilibriumDensity X μ a t < ⊤ := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hlprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  refine ENNReal.div_lt_top (measure_ne_top _ _) ?_
  exact gaussianAscendingLadderLaw_mean_ne_zero hX hG ha le_rfl

/-- The reflected equilibrium law integrates a test function against the real
equilibrium density. -/
theorem swingOvershootMeasure_integral_eq [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M)
    {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ y, f y ∂(swingOvershootMeasure X μ a)) =
      ∫ t in Ioi (0 : ℝ), equilibriumDensityReal X μ a t * f (a - t) := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hdm : Measurable (fun t : ℝ => swingEquilibriumDensity X μ a t) :=
    (swingEquilibriumDensity_joint_measurable hX).comp
      ((measurable_const (a := a)).prodMk measurable_id)
  have hmap : (∫ y, f y ∂(swingOvershootMeasure X μ a)) =
      ∫ o, f (a - o) ∂(equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a)) := by
    rw [swingOvershootMeasure, integral_map
      (measurable_const_sub_self a).aemeasurable hf.aestronglyMeasurable]
  have hdens : (fun o : ℝ => gaussianAscendingLadderLaw X μ a (Ioi o) /
      ladderMeanENN (gaussianAscendingLadderLaw X μ a)) =
      fun o : ℝ => swingEquilibriumDensity X μ a o := rfl
  rw [hmap, equilibriumOvershootLaw, hdens,
    integral_withDensity_eq_integral_toReal_smul hdm
      (Filter.Eventually.of_forall (fun t => swingEquilibriumDensity_lt_top hX hi hG ha t))]
  have hset : (volume.restrict (Ici (0 : ℝ))) = volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm
  rw [hset]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [smul_eq_mul, swingEquilibriumDensity_toReal hX hi hG hδ hδa haM t]

theorem integral_equilibriumDensityReal (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) :
    (∫ t in Ioi (0 : ℝ), equilibriumDensityReal X μ a t) = 1 := by
  have hc : 0 < gaussianAscendingLadderCommonDensity M :=
    gaussianAscendingLadderCommonDensity_pos M
  have hma : 0 < ladderMeanReal X μ a :=
    lt_of_lt_of_le hc (ladderMeanReal_pos hX hi hG hδ hδa haM)
  have hdiv : (∫ t in Ioi (0 : ℝ), equilibriumDensityReal X μ a t) =
      (∫ t in Ioi (0 : ℝ), ladderTailReal X μ a t)/ladderMeanReal X μ a := by
    rw [← integral_div]
    rfl
  rw [hdiv, integral_ladderTailReal hX hi hG hδ hδa haM, div_self hma.ne']

theorem integrableOn_equilibriumDensityReal (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) :
    IntegrableOn (equilibriumDensityReal X μ a) (Ioi 0) volume :=
  (integrableOn_ladderTailReal hX hi hG hδ hδa haM).div_const _

theorem equilibriumDensityReal_nonneg (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) (t : ℝ) :
    0 ≤ equilibriumDensityReal X μ a t := by
  have hc : 0 < gaussianAscendingLadderCommonDensity M :=
    gaussianAscendingLadderCommonDensity_pos M
  have hma : 0 < ladderMeanReal X μ a :=
    lt_of_lt_of_le hc (ladderMeanReal_pos hX hi hG hδ hδa haM)
  exact div_nonneg (ladderTailReal_nonneg X μ a t) hma.le

/-- Weak continuity of the reflected equilibrium law in the drift, against every
bounded Lipschitz test function. -/
theorem swingOvershootMeasure_integral_tendsto [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℝ} {L B : ℝ} (hfm : Measurable f)
    (hlip : ∀ x y : ℝ, |f x - f y| ≤ L*|x - y|) (hfB : ∀ x, |f x| ≤ B) :
    Tendsto (fun a' : ℝ => ∫ y, f y ∂(swingOvershootMeasure X μ a')) (𝓝 a)
      (𝓝 (∫ y, f y ∂(swingOvershootMeasure X μ a))) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set δ : ℝ := a/2 with hδdef
  set M : ℝ := 2*a with hMdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have haδ : δ ≤ a := by rw [hδdef]; linarith
  have haM : a ≤ M := by rw [hMdef]; linarith
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (f 0)) (hfB 0)
  have hL0 : 0 ≤ L := by
    have h := hlip 0 0
    simp only [sub_self, abs_zero, mul_zero] at h
    by_contra hc
    push Not at hc
    have h1 := hlip 0 1
    have h2 : |(0 : ℝ) - 1| = 1 := by norm_num
    rw [h2, mul_one] at h1
    linarith [abs_nonneg (f 0 - f 1)]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hdl1 := equilibriumDensityReal_l1_tendsto hX hi hG ha
  rw [Metric.tendsto_nhds] at hdl1
  have hnbhd : ∀ᶠ a' : ℝ in 𝓝 a, a' ∈ Ioo δ M :=
    IsOpen.mem_nhds isOpen_Ioo ⟨by rw [hδdef]; linarith, by rw [hMdef]; linarith⟩
  have hclose : ∀ᶠ a' : ℝ in 𝓝 a, |a' - a| < ε/(2*(L+1)) := by
    have hpos : 0 < ε/(2*(L+1)) := by positivity
    filter_upwards [Metric.ball_mem_nhds a hpos] with a' ha'
    simpa only [Metric.mem_ball, Real.dist_eq] using ha'
  have hεB : 0 < ε/(2*(B+1)) := by positivity
  filter_upwards [hnbhd, hclose, hdl1 (ε/(2*(B+1))) hεB] with a' hmem hnear hdsmall
  have hd1 := integrableOn_equilibriumDensityReal hX hi hG hδ hmem.1.le hmem.2.le
  have hd2 := integrableOn_equilibriumDensityReal hX hi hG hδ haδ haM
  have hrep1 := swingOvershootMeasure_integral_eq hX hi hG hδ hmem.1.le hmem.2.le hfm
  have hrep2 := swingOvershootMeasure_integral_eq hX hi hG hδ haδ haM hfm
  have hmeas1 : Measurable (fun t : ℝ => equilibriumDensityReal X μ a' t * f (a' - t)) :=
    (measurable_equilibriumDensityReal X μ a').mul
      (hfm.comp (measurable_const_sub_self a'))
  have hmeas2 : Measurable (fun t : ℝ => equilibriumDensityReal X μ a t * f (a - t)) :=
    (measurable_equilibriumDensityReal X μ a).mul
      (hfm.comp (measurable_const_sub_self a))
  have hnn1 := equilibriumDensityReal_nonneg hX hi hG hδ hmem.1.le hmem.2.le
  have hnn2 := equilibriumDensityReal_nonneg hX hi hG hδ haδ haM
  have hg1 : IntegrableOn (fun t : ℝ => equilibriumDensityReal X μ a' t * f (a' - t))
      (Ioi 0) volume := by
    refine Integrable.mono' (hd1.mul_const B) hmeas1.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn1 t)]
    exact mul_le_mul_of_nonneg_left (hfB _) (hnn1 t)
  have hg2 : IntegrableOn (fun t : ℝ => equilibriumDensityReal X μ a t * f (a - t))
      (Ioi 0) volume := by
    refine Integrable.mono' (hd2.mul_const B) hmeas2.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn2 t)]
    exact mul_le_mul_of_nonneg_left (hfB _) (hnn2 t)
  -- the pointwise split
  set A : ℝ := L*|a' - a| with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hbound1 : IntegrableOn (fun t : ℝ => equilibriumDensityReal X μ a' t * A)
      (Ioi 0) volume := hd1.mul_const _
  have hbound2 : IntegrableOn
      (fun t : ℝ => |equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t| * B)
      (Ioi 0) volume := ((hd1.sub hd2).abs).mul_const _
  have hboundsum : IntegrableOn (fun t : ℝ => equilibriumDensityReal X μ a' t * A +
      |equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t| * B)
      (Ioi 0) volume := hbound1.add hbound2
  have habsint : IntegrableOn (fun t : ℝ => |equilibriumDensityReal X μ a' t * f (a' - t) -
      equilibriumDensityReal X μ a t * f (a - t)|) (Ioi 0) volume := (hg1.sub hg2).abs
  have hpoint : ∀ t : ℝ,
      |equilibriumDensityReal X μ a' t * f (a' - t) -
        equilibriumDensityReal X μ a t * f (a - t)| ≤
        equilibriumDensityReal X μ a' t * A +
          |equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t| * B := by
    intro t
    have hsplit : equilibriumDensityReal X μ a' t * f (a' - t) -
        equilibriumDensityReal X μ a t * f (a - t) =
        equilibriumDensityReal X μ a' t * (f (a' - t) - f (a - t)) +
          (equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t) * f (a - t) := by
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have h1 : |equilibriumDensityReal X μ a' t * (f (a' - t) - f (a - t))| ≤
        equilibriumDensityReal X μ a' t * A := by
      rw [abs_mul, abs_of_nonneg (hnn1 t)]
      refine mul_le_mul_of_nonneg_left ?_ (hnn1 t)
      have := hlip (a' - t) (a - t)
      have heq : |a' - t - (a - t)| = |a' - a| := by
        congr 1
        ring
      rw [heq] at this
      rw [hAdef]
      exact this
    have h2 : |(equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t) * f (a - t)| ≤
        |equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t| * B := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hfB _) (abs_nonneg _)
    linarith
  have hmono := setIntegral_mono_on habsint hboundsum measurableSet_Ioi (fun t _ => hpoint t)
  have hsplitint : (∫ t in Ioi (0 : ℝ), (equilibriumDensityReal X μ a' t * A +
      |equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t| * B)) =
      A + (∫ t in Ioi (0 : ℝ),
        |equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t|) * B := by
    rw [integral_add hbound1 hbound2, integral_mul_const, integral_mul_const,
      integral_equilibriumDensityReal hX hi hG hδ hmem.1.le hmem.2.le, one_mul]
  rw [hsplitint] at hmono
  have habs : |(∫ y, f y ∂(swingOvershootMeasure X μ a')) -
      ∫ y, f y ∂(swingOvershootMeasure X μ a)| ≤
      A + (∫ t in Ioi (0 : ℝ),
        |equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t|) * B := by
    rw [hrep1, hrep2, ← integral_sub hg1 hg2]
    exact le_trans abs_integral_le_integral_abs hmono
  -- the two halves
  have hAsmall : A < ε/2 := by
    rw [hAdef]
    have hle : L*|a' - a| ≤ L*(ε/(2*(L+1))) :=
      mul_le_mul_of_nonneg_left hnear.le hL0
    have hkey : L*(ε/(2*(L+1))) < ε/2 := by
      have hL1 : (0:ℝ) < L + 1 := by linarith
      have h2 : L*(ε/(2*(L+1))) = (L*ε)/(2*(L+1)) := by ring
      rw [h2, div_lt_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
      nlinarith
    linarith
  have hDsmall : (∫ t in Ioi (0 : ℝ),
      |equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t|) * B < ε/2 := by
    have hD : (∫ t in Ioi (0 : ℝ),
        |equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t|) <
        ε/(2*(B+1)) := by
      have h := hdsmall
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (setIntegral_nonneg measurableSet_Ioi (fun t _ => abs_nonneg _))] at h
      exact h
    have hB1 : 0 < B + 1 := by linarith
    have hnnD : (0 : ℝ) ≤ ∫ t in Ioi (0 : ℝ),
        |equilibriumDensityReal X μ a' t - equilibriumDensityReal X μ a t| :=
      setIntegral_nonneg (μ := volume) measurableSet_Ioi (fun t _ => abs_nonneg _)
    have hstep := mul_lt_mul_of_pos_right hD hB1
    have hne : (B + 1) ≠ 0 := ne_of_gt hB1
    have heq : (ε/(2*(B+1))) * (B+1) = ε/2 := by
      field_simp
    rw [heq] at hstep
    nlinarith
  rw [Real.dist_eq]
  linarith

end SwingRepair
