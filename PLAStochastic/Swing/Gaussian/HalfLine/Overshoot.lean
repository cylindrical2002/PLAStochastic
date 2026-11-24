import PLAStochastic.Swing.Gaussian.HalfLine.FirstNegative

/-! Actual half-line selected overshoot integration. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem gaussianHalfLineExitSlice_lintegral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℝ} (ha : 0 ≤ a) (n : ℕ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : ∀ r : ℝ, -(1/2 : ℝ) ≤ r → (∫⁻ u, f u ∂gaussianExcessLaw r) ≤ C) :
    (∫⁻ ω in gaussianHalfLineExitSlice X x a n, f (gaussianHalfLineOvershoot X x a ω) ∂μ) ≤
      C * μ (gaussianHalfLineExitSlice X x a n) := by
  have := hi.isProbabilityMeasure
  let r := fun ω => gaussianDriftWalk X x a n ω + a
  have hr : Measurable[incrementIndexSpace X (Iio n)] r :=
    (gaussianDriftWalk_measurable_past X x a n).add_const a
  have hnegG : μ.map (fun ω => -X n ω) = gaussianReal 0 1 := by
    calc
      _ = (μ.map (X n)).map (fun z : ℝ => -z) :=
        (Measure.map_map measurable_neg (hX n)).symm
      _ = _ := by rw [hG, gaussianReal_map_neg, neg_zero]
  have hnegMeas : Measurable[MeasurableSpace.comap (X n) inferInstance] (fun ω => -X n ω) :=
    (show Measurable[MeasurableSpace.comap (X n) inferInstance] (X n) from
      measurable_iff_comap_le.mpr le_rfl).neg
  have hnegInd := indep_of_indep_of_le_left (currentIncrement_indep_past hX hi n) hnegMeas.comap_le
  have he : gaussianHalfLineExitSlice X x a n =
      gaussianHalfLineSurvives X x a n ∩ {ω | r ω < -X n ω} := by
    ext ω
    change (ω ∈ gaussianHalfLineSurvives X x a n ∧ gaussianDriftWalk X x a (n + 1) ω < 0) ↔ _
    rw [gaussianDriftWalk_succ]
    change (_ ∧ _ < 0) ↔ (_ ∧ r ω < -X n ω)
    dsimp only [r]
    constructor <;> rintro ⟨hs, ho⟩ <;> exact ⟨hs, by linarith⟩
  have ho : ∀ ω ∈ gaussianHalfLineExitSlice X x a n,
      gaussianHalfLineOvershoot X x a ω = -X n ω - r ω := by
    intro ω hω
    rw [gaussianHalfLineOvershoot_of_slice hω, gaussianDriftWalk_succ]
    dsimp only [r]
    ring
  calc
    _ = ∫⁻ ω in gaussianHalfLineExitSlice X x a n, f (-X n ω-r ω) ∂μ :=
      setLIntegral_congr_fun (gaussianHalfLineExitSlice_measurable hX x a n)
        (fun ω hω => congrArg f (ho ω hω))
    _ ≤ _ := by
      rw [he]
      apply past_freshGaussian_excess_lintegral_le (incrementIndexSpace_le hX _) (hX n).neg
        hnegG hnegInd hr (gaussianHalfLineSurvives_measurable_past X x a n) _ hf hC hb
      intro ω hω
      have hs := hω n le_rfl
      dsimp only [r]
      linarith

theorem gaussianHalfLineFinite_lintegral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : ∀ r : ℝ, -(1/2 : ℝ) ≤ r → (∫⁻ u, f u ∂gaussianExcessLaw r) ≤ C) :
    (∫⁻ ω in {ω | gaussianHalfLineExit X x a ω ≠ ⊤}, f (gaussianHalfLineOvershoot X x a ω) ∂μ) ≤
      C * μ {ω | gaussianHalfLineExit X x a ω ≠ ⊤} := by
  rw [gaussianHalfLineFinite_eq_iUnion hx,
    lintegral_iUnion (gaussianHalfLineExitSlice_measurable hX x a)
      (gaussianHalfLineExitSlice_disjoint X x a),
    measure_iUnion (gaussianHalfLineExitSlice_disjoint X x a)
      (gaussianHalfLineExitSlice_measurable hX x a), ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum (fun n =>
    gaussianHalfLineExitSlice_lintegral_le hX hi hG ha n hf hC hb)

/-- Every nonnegative exponential parameter is integrable for the true selected overshoot. -/
theorem gaussianHalfLineOvershoot_integrable_exp
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a θ : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp (θ*gaussianHalfLineOvershoot X x a ω)) μ := by
  have := hi.isProbabilityMeasure
  let A := {ω | gaussianHalfLineExit X x a ω ≠ ⊤}
  have hA : MeasurableSet A :=
    ((gaussianHalfLineExit_isStoppingTime hX x a).measurable' (measurableSet_singleton ⊤)).compl
  have hf : Measurable (fun ω => Real.exp (θ*gaussianHalfLineOvershoot X x a ω)) :=
    ((gaussianHalfLineOvershoot_measurable hX x a).const_mul θ).exp
  have hle : (∫⁻ ω in A, ENNReal.ofReal (Real.exp (θ*gaussianHalfLineOvershoot X x a ω)) ∂μ) ≤
      ENNReal.ofReal (gaussianExcessExpMomentBound θ) * μ A := by
    apply gaussianHalfLineFinite_lintegral_le hX hi hG hx ha
      (f := fun u => ENNReal.ofReal (Real.exp (θ*u))) (by fun_prop) ENNReal.ofReal_ne_top
    intro r hr
    rw [← ofReal_integral_eq_lintegral_ofReal (gaussianExcessLaw_integrable_exp r θ)
      (ae_of_all _ (fun _ => (Real.exp_pos _).le))]
    exact ENNReal.ofReal_le_ofReal (gaussianExcessLaw_exp_moment_le hr hθ)
  have hint : IntegrableOn (fun ω => Real.exp (θ*gaussianHalfLineOvershoot X x a ω)) A μ :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable
      (ae_of_all _ (fun _ => (Real.exp_pos _).le))).mp
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hle)
  have hc : IntegrableOn (fun ω => Real.exp (θ*gaussianHalfLineOvershoot X x a ω)) Aᶜ μ := by
    apply (integrable_const (1 : ℝ)).integrableOn.congr
    apply (ae_restrict_iff' hA.compl).mpr
    exact ae_of_all _ (fun ω hω => by
      have ht : gaussianHalfLineExit X x a ω = ⊤ := by simpa [A] using hω
      simp [gaussianHalfLineOvershoot, ht])
  exact (integrableOn_univ.mp (by simpa only [union_compl_self] using hint.union hc))

end SwingRepair
