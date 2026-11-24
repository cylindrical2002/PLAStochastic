import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.DirichletHeatKernel.SineSeries
import PLAStochastic.Brownian.Markov.FourierMartingale
import PLAStochastic.Brownian.Hitting.WedgeStopping

/-!
Actual interval stopping identities. The exit time is the infimum of strict crossings,
with a deterministic cutoff. Gaussian Fourier martingales supply the stopped sine moments.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- Truncation commutes with the actual first open exit, including paths without a crossing. -/
theorem boundedOpenExitTime_min {X : ℝ≥0 → Ω → ℝ} {S : Set ℝ} {T H : ℝ≥0}
    (hTH : T ≤ H) (ω : Ω) :
    boundedOpenExitTime X S T ω = min (boundedOpenExitTime X S H ω) T := by
  apply le_antisymm
  · apply le_min _ (boundedOpenExitTime_le X S T ω)
    apply le_csInf (insert_nonempty _ _)
    intro s hs
    rcases mem_insert_iff.mp hs with rfl | hs
    · exact (boundedOpenExitTime_le X S T ω).trans hTH
    · by_cases hsT : s ≤ T
      · exact csInf_le ⟨0, fun _ _ => bot_le⟩ (mem_insert_of_mem _ ⟨hsT, hs.2⟩)
      · exact (boundedOpenExitTime_le X S T ω).trans (le_of_not_ge hsT)
  · apply le_csInf (insert_nonempty _ _)
    intro s hs
    rcases mem_insert_iff.mp hs with rfl | hs
    · exact min_le_right _ _
    · apply (min_le_left _ _).trans
      exact csInf_le ⟨0, fun _ _ => bot_le⟩ (mem_insert_of_mem _ ⟨hs.1.trans hTH, hs.2⟩)

/-- The bounded first strict crossing of either endpoint, starting at x. -/
def boundedIntervalExit (B : ℝ≥0 → Ω → ℝ) (x r : ℝ) (T : ℝ≥0) : Ω → ℝ≥0 :=
  boundedOpenExitTime (fun t ω => x + B t ω) (driftBarrierSet r 0) T

theorem adapted_shiftedBrownian (hB : IsPreBrownianReal B μ) (x : ℝ) :
    Adapted (brownianNaturalFiltration hB) (fun t ω => x + measurableBrownian hB t ω) := by
  intro t
  exact (Filtration.stronglyAdapted_natural
    (fun t => (measurable_measurableBrownian hB t).stronglyMeasurable) t).measurable.const_add x

theorem gridHittingTime_shiftedBrownian_ae_eq (hB : IsPreBrownianReal B μ)
    (x r : ℝ) (δ : ℝ≥0) (N : ℕ) :
    gridHittingTime (fun t ω => x + measurableBrownian hB t ω) (driftBarrierSet r 0) δ N =ᵐ[μ]
      gridHittingTime (fun t ω => x + B t ω) (driftBarrierSet r 0) δ N := by
  filter_upwards [measurableBrownian_countable_ae_eq hB (fun k : ℕ => δ * k)] with ω hω
  have hp : (fun n : ℕ => x + measurableBrownian hB (δ * n) ω) =
      (fun n : ℕ => x + B (δ * n) ω) := by
    funext n
    rw [hω n]
  have hh := congrArg (fun f : ℕ → ℝ => hittingBtwn (fun n (_ : Unit) => f n)
    (driftBarrierSet r 0) 0 N ()) hp
  exact congrArg (fun k : ℕ => δ * (k : ℝ≥0)) hh

/-- The exact Fourier optional-stopping identity at a real, continuously observed interval exit. -/
theorem integral_actualBrownianFourier_boundedIntervalExit (hB : IsBrownianReal B μ)
    (c x r : ℝ) (T : ℝ≥0) :
    Integrable (fun ω => actualBrownianFourier B c (boundedIntervalExit B x r T ω) ω) μ ∧
      (∫ ω, actualBrownianFourier B c (boundedIntervalExit B x r T ω) ω ∂μ) = 1 := by
  obtain ⟨H, hH⟩ := exists_nat_ge T
  let G : ℕ → Ω → ℝ≥0 := fun n =>
    gridHittingTime (fun t ω => x + measurableBrownian hB.toIsPreBrownianReal t ω)
      (driftBarrierSet r 0) (reciprocalMesh n) (H * (n + 1))
  apply integral_actualBrownianFourier_stopping_limit hB c
    (τ := fun n ω => min (G n ω : WithTop ℝ≥0) (T : WithTop ℝ≥0)) (T := T)
  · intro n
    exact (isStoppingTime_gridHittingTime (adapted_shiftedBrownian hB.toIsPreBrownianReal x)
      (measurableSet_driftBarrierSet r 0) (reciprocalMesh_pos n) (H * (n + 1))).min_const T
  · exact fun _ _ => min_le_right _ _
  · intro n
    have hc := (gridHittingTime_countable_range
      (fun t ω => x + measurableBrownian hB.toIsPreBrownianReal t ω)
      (driftBarrierSet r 0) (reciprocalMesh n) (H * (n + 1))).image
      (fun z : WithTop ℝ≥0 => min z T)
    simpa only [← Set.range_comp, Function.comp_def, G] using hc
  · have heq : ∀ᵐ ω ∂μ, ∀ n, G n ω =
        gridHittingTime (fun t ω => x + B t ω) (driftBarrierSet r 0)
          (reciprocalMesh n) (H * (n + 1)) ω :=
      ae_all_iff.mpr (fun n => gridHittingTime_shiftedBrownian_ae_eq hB.toIsPreBrownianReal
        x r (reciprocalMesh n) (H * (n + 1)))
    filter_upwards [hB.cont, heq] with ω hω heqω
    have ht := gridHittingTime_tendsto_boundedOpenExitTime
      (X := fun t ω => x + B t ω) (ω := ω) (S := driftBarrierSet r 0) (isOpen_Iio.union isOpen_Ioi) (hω.const_add x) H
    have hm := (ht.congr (fun n => (heqω n).symm)).min (tendsto_const_nhds (x := T))
    rw [← boundedOpenExitTime_min hH] at hm
    simpa only [← WithTop.coe_min, WithTop.untopD_coe, boundedIntervalExit] using hm

theorem gaussianPhase_im (c x : ℝ) : (gaussianPhase c x).im = Real.sin (c * x) := by
  simp [gaussianPhase, Complex.exp_im]

omit [MeasurableSpace Ω] in
theorem actualBrownianFourier_shifted_im (c x : ℝ) (T : ℝ≥0) (ω : Ω) :
    (gaussianPhase c x * actualBrownianFourier B c T ω).im =
      Real.exp (c ^ 2 * (T : ℝ) / 2) * Real.sin (c * (x + B T ω)) := by
  unfold actualBrownianFourier
  rw [← mul_assoc, mul_comm (gaussianPhase c x), mul_assoc, ← gaussianPhase_add]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, gaussianPhase_im]

theorem integral_stopped_shifted_sine (hB : IsBrownianReal B μ) (c x r : ℝ) (T : ℝ≥0) :
    (∫ ω, Real.exp (c ^ 2 * (boundedIntervalExit B x r T ω : ℝ) / 2) *
      Real.sin (c * (x + B (boundedIntervalExit B x r T ω) ω)) ∂μ) = Real.sin (c * x) := by
  have hs := integral_actualBrownianFourier_boundedIntervalExit hB c x r T
  have hi := (hs.1.const_mul (gaussianPhase c x))
  have hval : (∫ ω, gaussianPhase c x * actualBrownianFourier B c (boundedIntervalExit B x r T ω) ω ∂μ) =
      gaussianPhase c x := by
    rw [integral_const_mul, hs.2, mul_one]
  have him := congrArg Complex.im hval
  have hii := integral_im hi
  change (∫ ω, (gaussianPhase c x * actualBrownianFourier B c (boundedIntervalExit B x r T ω) ω).im ∂μ) =
    (∫ ω, gaussianPhase c x * actualBrownianFourier B c (boundedIntervalExit B x r T ω) ω ∂μ).im at hii
  rw [← hii] at him
  simpa only [actualBrownianFourier_shifted_im, gaussianPhase_im] using him

/-- The sine of the actual endpoint, killed when a strict boundary crossing occurs before T. -/
def intervalKilledSine (B : ℝ≥0 → Ω → ℝ) (x r : ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  if boundedIntervalExit B x r T ω = T then Real.sin (heatFrequency r n * (x + B T ω)) else 0

omit [MeasurableSpace Ω] in
theorem stopped_sine_eq_killed {x r : ℝ} (hr : 0 < r) (hx : x ∈ Icc 0 r)
    {ω : Ω} (hω : Continuous (B · ω)) (h0 : B 0 ω = 0) (T : ℝ≥0) (n : ℕ) :
    Real.exp (heatFrequency r n ^ 2 * (boundedIntervalExit B x r T ω : ℝ) / 2) *
      Real.sin (heatFrequency r n * (x + B (boundedIntervalExit B x r T ω) ω)) =
    Real.exp (heatFrequency r n ^ 2 * (T : ℝ) / 2) * intervalKilledSine B x r T n ω := by
  by_cases heq : boundedIntervalExit B x r T ω = T
  · simp only [intervalKilledSine, heq, ↓reduceIte]
  · have hlt : boundedIntervalExit B x r T ω < T :=
      lt_of_le_of_ne (boundedOpenExitTime_le _ _ _ _) heq
    have hstart : x + B 0 ω ∈ Icc (- (0 : ℝ)) r := by simpa [h0] using hx
    have hbd := boundedOpenExitTime_boundary (X := fun t ω => x + B t ω)
      (a := r) (b := 0) (T := T) (hω.const_add x) hstart hlt
    have hs : Real.sin (heatFrequency r n *
        (x + B (boundedIntervalExit B x r T ω) ω)) = 0 := by
      rcases hbd with hb | hb
      · change x + B (boundedIntervalExit B x r T ω) ω = r at hb
        rw [hb]
        have hf : heatFrequency r n * r = ((n + 1 : ℕ) : ℝ) * Real.pi := by
          unfold heatFrequency
          push_cast
          field_simp
        rw [hf]
        exact Real.sin_nat_mul_pi (n + 1)
      · change x + B (boundedIntervalExit B x r T ω) ω = -0 at hb
        simp only [hb, neg_zero, mul_zero, Real.sin_zero]
    simp only [hs, intervalKilledSine, if_neg heq, mul_zero]

/-- Actual killed sine moments. This is a probability statement, not a hypothesis about the kernel. -/
theorem integral_intervalKilledSine (hB : IsBrownianReal B μ) {x r : ℝ}
    (hr : 0 < r) (hx : x ∈ Icc 0 r) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, intervalKilledSine B x r T n ω ∂μ) =
      Real.exp (-(heatFrequency r n ^ 2) * (T : ℝ) / 2) * Real.sin (heatFrequency r n * x) := by
  have heq : (fun ω => Real.exp (heatFrequency r n ^ 2 * (boundedIntervalExit B x r T ω : ℝ) / 2) *
        Real.sin (heatFrequency r n * (x + B (boundedIntervalExit B x r T ω) ω))) =ᵐ[μ]
      (fun ω => Real.exp (heatFrequency r n ^ 2 * (T : ℝ) / 2) * intervalKilledSine B x r T n ω) := by
    filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hω h0
    exact stopped_sine_eq_killed hr hx hω h0 T n
  have hi := integral_stopped_shifted_sine hB (heatFrequency r n) x r T
  rw [integral_congr_ae heq, integral_const_mul] at hi
  have hexp : Real.exp (-(heatFrequency r n ^ 2) * (T : ℝ) / 2) *
      Real.exp (heatFrequency r n ^ 2 * (T : ℝ) / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  calc
    _ = (Real.exp (-(heatFrequency r n ^ 2) * (T : ℝ) / 2) *
        Real.exp (heatFrequency r n ^ 2 * (T : ℝ) / 2)) *
        (∫ ω, intervalKilledSine B x r T n ω ∂μ) := by rw [hexp, one_mul]
    _ = _ := by rw [mul_assoc, hi]

/-- The actual continuous exit is measurable; a fixed Fourier norm recovers its value. -/
theorem boundedIntervalExit_aemeasurable (hB : IsBrownianReal B μ) (x r : ℝ) (T : ℝ≥0) :
    AEMeasurable (boundedIntervalExit B x r T) μ := by
  have hi := (integral_actualBrownianFourier_boundedIntervalExit hB 2 x r T).1
  have hm := (Real.measurable_log.comp_aemeasurable hi.aestronglyMeasurable.aemeasurable.norm).div_const 2
  have heq : (fun ω => Real.log ‖actualBrownianFourier B 2 (boundedIntervalExit B x r T ω) ω‖ / 2) =
      fun ω => (boundedIntervalExit B x r T ω : ℝ) := by
    funext ω
    simp only [actualBrownianFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), norm_gaussianPhase, mul_one, Real.log_exp]
    ring
  simp only [Function.comp_def] at hm
  rw [heq] at hm
  simpa only [Real.toNNReal_coe] using hm.real_toNNReal

theorem nullMeasurableSet_intervalSurvival (hB : IsBrownianReal B μ) (x r : ℝ) (T : ℝ≥0) :
    NullMeasurableSet {ω | boundedIntervalExit B x r T ω = T} μ :=
  (boundedIntervalExit_aemeasurable hB x r T).nullMeasurableSet_preimage (measurableSet_singleton T)

theorem intervalKilledSine_aestronglyMeasurable (hB : IsBrownianReal B μ)
    (x r : ℝ) (T : ℝ≥0) (n : ℕ) : AEStronglyMeasurable (intervalKilledSine B x r T n) μ := by
  have hsin : AEStronglyMeasurable (fun ω => Real.sin (heatFrequency r n * (x + B T ω))) μ :=
    (Real.measurable_sin.comp_aemeasurable ((hB.aemeasurable T).const_add x |>.const_mul _)).aestronglyMeasurable
  have heq : intervalKilledSine B x r T n =
      {ω | boundedIntervalExit B x r T ω = T}.indicator
        (fun ω => Real.sin (heatFrequency r n * (x + B T ω))) := by
    funext ω
    simp [intervalKilledSine, Set.indicator]
  rw [heq]
  exact hsin.indicator₀ (nullMeasurableSet_intervalSurvival hB x r T)

theorem intervalKilledSine_integrable (hB : IsBrownianReal B μ)
    (x r : ℝ) (T : ℝ≥0) (n : ℕ) : Integrable (intervalKilledSine B x r T n) μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  apply Integrable.of_bound (intervalKilledSine_aestronglyMeasurable hB x r T n) 1
  apply Eventually.of_forall
  intro ω
  unfold intervalKilledSine
  split_ifs
  · exact Real.abs_sin_le_one _
  · simp

end BrownianAffine
