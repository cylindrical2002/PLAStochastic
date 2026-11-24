import PLAStochastic.Swing.Gaussian.StripExit.Overshoot
import PLAStochastic.Swing.Gaussian.Tail.SelectedExcess

/-! # Uniform moments at the actual first Gaussian strip exit

Each fixed exit slice is integrated using independence of the next increment from the
strict past. Its random threshold is handled by the restricted product law in
`GaussianSelectedExcess`. Summing the disjoint slices transfers the uniform conditional
Gaussian excess bounds to the selected overshoot without any independence assumption
on the selected increment, and without assuming that the exit time is finite.
The overshoot is zero on paths that never exit.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem gaussianStripLowerSlice_lintegral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a R : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a) (n : ℕ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : ∀ r : ℝ, -(1/2 : ℝ) ≤ r → (∫⁻ u, f u ∂gaussianExcessLaw r) ≤ C) :
    (∫⁻ ω in gaussianStripLowerSlice X x a R n, f (gaussianStripOvershoot X x a R ω) ∂μ) ≤
      C * μ (gaussianStripLowerSlice X x a R n) := by
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
  have he : gaussianStripLowerSlice X x a R n =
      gaussianStripSurvives X x a R n ∩ {ω | r ω < -X n ω} := by
    ext ω
    change (ω ∈ gaussianStripSurvives X x a R n ∧ gaussianDriftWalk X x a (n + 1) ω < 0) ↔ _
    rw [gaussianDriftWalk_succ]
    change (_ ∧ _ < 0) ↔ (_ ∧ r ω < -X n ω)
    dsimp only [r]
    constructor <;> rintro ⟨hs, ho⟩ <;> exact ⟨hs, by linarith⟩
  have ho : ∀ ω ∈ gaussianStripLowerSlice X x a R n,
      gaussianStripOvershoot X x a R ω = -X n ω - r ω := by
    intro ω hω
    rw [gaussianStripOvershoot_of_lowerExit hR (gaussianStripLowerSlice_subset hω),
      gaussianStripExitPosition_of_eq (gaussianStripExit_eq_of_lowerSlice hω), gaussianDriftWalk_succ]
    dsimp only [r]
    ring
  calc
    _ = ∫⁻ ω in gaussianStripLowerSlice X x a R n, f (-X n ω-r ω) ∂μ :=
      setLIntegral_congr_fun (gaussianStripLowerSlice_measurable hX x a R n)
        (fun ω hω => congrArg f (ho ω hω))
    _ ≤ _ := by
      rw [he]
      apply past_freshGaussian_excess_lintegral_le (incrementIndexSpace_le hX _) (hX n).neg
        hnegG hnegInd hr (gaussianStripSurvives_measurable_past X x a R n) _ hf hC hb
      intro ω hω
      have hs := (hω n le_rfl).1
      dsimp only [r]
      linarith

theorem gaussianStripUpperSlice_lintegral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a R : ℝ} (hR : 0 ≤ R) (ha : a ≤ 1/2) (n : ℕ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : ∀ r : ℝ, -(1/2 : ℝ) ≤ r → (∫⁻ u, f u ∂gaussianExcessLaw r) ≤ C) :
    (∫⁻ ω in gaussianStripUpperSlice X x a R n, f (gaussianStripOvershoot X x a R ω) ∂μ) ≤
      C * μ (gaussianStripUpperSlice X x a R n) := by
  have := hi.isProbabilityMeasure
  let r := fun ω => R - gaussianDriftWalk X x a n ω - a
  have hr : Measurable[incrementIndexSpace X (Iio n)] r :=
    ((gaussianDriftWalk_measurable_past X x a n).const_sub R).sub_const a
  have he : gaussianStripUpperSlice X x a R n =
      gaussianStripSurvives X x a R n ∩ {ω | r ω < X n ω} := by
    ext ω
    change (ω ∈ gaussianStripSurvives X x a R n ∧ R < gaussianDriftWalk X x a (n + 1) ω) ↔ _
    rw [gaussianDriftWalk_succ]
    change (_ ∧ _ < _) ↔ (_ ∧ r ω < X n ω)
    dsimp only [r]
    constructor <;> rintro ⟨hs, ho⟩ <;> exact ⟨hs, by linarith⟩
  have ho : ∀ ω ∈ gaussianStripUpperSlice X x a R n,
      gaussianStripOvershoot X x a R ω = X n ω - r ω := by
    intro ω hω
    rw [gaussianStripOvershoot_of_upperExit hR (gaussianStripUpperSlice_subset hω),
      gaussianStripExitPosition_of_eq (gaussianStripExit_eq_of_upperSlice hω), gaussianDriftWalk_succ]
    dsimp only [r]
    ring
  calc
    _ = ∫⁻ ω in gaussianStripUpperSlice X x a R n, f (X n ω-r ω) ∂μ :=
      setLIntegral_congr_fun (gaussianStripUpperSlice_measurable hX x a R n)
        (fun ω hω => congrArg f (ho ω hω))
    _ ≤ _ := by
      rw [he]
      apply past_freshGaussian_excess_lintegral_le (incrementIndexSpace_le hX _) (hX n)
        (hG n) (currentIncrement_indep_past hX hi n) hr
        (gaussianStripSurvives_measurable_past X x a R n) _ hf hC hb
      intro ω hω
      have hs := (hω n le_rfl).2
      dsimp only [r]
      linarith


theorem gaussianStripLowerExit_lintegral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a R : ℝ} (hx : x ∈ Icc 0 R) (ha : 0 ≤ a)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : ∀ r : ℝ, -(1/2 : ℝ) ≤ r → (∫⁻ u, f u ∂gaussianExcessLaw r) ≤ C) :
    (∫⁻ ω in gaussianStripLowerExit X x a R, f (gaussianStripOvershoot X x a R ω) ∂μ) ≤
      C * μ (gaussianStripLowerExit X x a R) := by
  rw [gaussianStripLowerExit_eq_iUnion hx,
    lintegral_iUnion (gaussianStripLowerSlice_measurable hX x a R)
      (gaussianStripLowerSlice_disjoint X x a R),
    measure_iUnion (gaussianStripLowerSlice_disjoint X x a R)
      (gaussianStripLowerSlice_measurable hX x a R), ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum (fun n =>
    gaussianStripLowerSlice_lintegral_le hX hi hG (hx.1.trans hx.2) ha n hf hC hb)

theorem gaussianStripUpperExit_lintegral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a R : ℝ} (hx : x ∈ Icc 0 R) (ha : a ≤ 1/2)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : ∀ r : ℝ, -(1/2 : ℝ) ≤ r → (∫⁻ u, f u ∂gaussianExcessLaw r) ≤ C) :
    (∫⁻ ω in gaussianStripUpperExit X x a R, f (gaussianStripOvershoot X x a R ω) ∂μ) ≤
      C * μ (gaussianStripUpperExit X x a R) := by
  rw [gaussianStripUpperExit_eq_iUnion hx,
    lintegral_iUnion (gaussianStripUpperSlice_measurable hX x a R)
      (gaussianStripUpperSlice_disjoint X x a R),
    measure_iUnion (gaussianStripUpperSlice_disjoint X x a R)
      (gaussianStripUpperSlice_measurable hX x a R), ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum (fun n =>
    gaussianStripUpperSlice_lintegral_le hX hi hG (hx.1.trans hx.2) ha n hf hC hb)

theorem gaussianStripFinite_lintegral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a R : ℝ} (hx : x ∈ Icc 0 R) (ha : 0 ≤ a) (ha' : a ≤ 1/2)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : ∀ r : ℝ, -(1/2 : ℝ) ≤ r → (∫⁻ u, f u ∂gaussianExcessLaw r) ≤ C) :
    (∫⁻ ω in {ω | gaussianStripExit X x a R ω ≠ ⊤},
      f (gaussianStripOvershoot X x a R ω) ∂μ) ≤
      C * μ {ω | gaussianStripExit X x a R ω ≠ ⊤} := by
  rw [gaussianStripFinite_eq_lower_union_upper,
    lintegral_union (gaussianStripUpperExit_measurable hX x a R)
      (gaussianStripLowerUpper_disjoint (hx.1.trans hx.2)),
    measure_union (gaussianStripLowerUpper_disjoint (hx.1.trans hx.2))
      (gaussianStripUpperExit_measurable hX x a R), mul_add]
  exact add_le_add (gaussianStripLowerExit_lintegral_le hX hi hG hx ha hf hC hb)
    (gaussianStripUpperExit_lintegral_le hX hi hG hx ha' hf hC hb)

theorem gaussianStripOvershoot_lintegral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a R : ℝ} (hx : x ∈ Icc 0 R) (ha : 0 ≤ a) (ha' : a ≤ 1/2)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hf0 : f 0 = 0)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : ∀ r : ℝ, -(1/2 : ℝ) ≤ r → (∫⁻ u, f u ∂gaussianExcessLaw r) ≤ C) :
    (∫⁻ ω, f (gaussianStripOvershoot X x a R ω) ∂μ) ≤ C := by
  have := hi.isProbabilityMeasure
  have hm : MeasurableSet {ω | gaussianStripExit X x a R ω ≠ ⊤} :=
    ((gaussianStripExit_isStoppingTime hX x a R).measurable' (measurableSet_singleton ⊤)).compl
  have he : ∀ ω, f (gaussianStripOvershoot X x a R ω) =
      {ω | gaussianStripExit X x a R ω ≠ ⊤}.indicator
        (fun ω => f (gaussianStripOvershoot X x a R ω)) ω := by
    intro ω
    by_cases hω : gaussianStripExit X x a R ω = ⊤
    · simp [hω, gaussianStripOvershoot, hf0]
    · simp [hω]
  calc
    _ = ∫⁻ ω in {ω | gaussianStripExit X x a R ω ≠ ⊤},
        f (gaussianStripOvershoot X x a R ω) ∂μ := by
      calc
        _ = ∫⁻ ω, {ω | gaussianStripExit X x a R ω ≠ ⊤}.indicator
            (fun ω => f (gaussianStripOvershoot X x a R ω)) ω ∂μ := lintegral_congr he
        _ = _ := lintegral_indicator hm _
    _ ≤ C * μ {ω | gaussianStripExit X x a R ω ≠ ⊤} :=
      gaussianStripFinite_lintegral_le hX hi hG hx ha ha' hf hC hb
    _ ≤ C * 1 := by gcongr; exact prob_le_one
    _ = C := mul_one _


/-- Any uniform nonnegative excess moment transfers to the actual selected exit overshoot. -/
theorem gaussianStripOvershoot_integral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a R : ℝ} (hx : x ∈ Icc 0 R) (ha : 0 ≤ a) (ha' : a ≤ 1/2)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : f 0 = 0)
    (hfn : ∀ u, 0 ≤ u → 0 ≤ f u) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ r : ℝ, -(1/2 : ℝ) ≤ r →
      Integrable f (gaussianExcessLaw r) ∧ (∫ u, f u ∂gaussianExcessLaw r) ≤ C) :
    Integrable (fun ω => f (gaussianStripOvershoot X x a R ω)) μ ∧
      (∫ ω, f (gaussianStripOvershoot X x a R ω) ∂μ) ≤ C := by
  have hfm : Measurable (fun ω => f (gaussianStripOvershoot X x a R ω)) :=
    hf.comp (gaussianStripOvershoot_measurable hX x a R)
  have hfn' : 0 ≤ᵐ[μ] (fun ω => f (gaussianStripOvershoot X x a R ω)) :=
    ae_of_all _ (fun ω => hfn _ (gaussianStripOvershoot_nonneg X x a R ω))
  have hle : (∫⁻ ω, ENNReal.ofReal (f (gaussianStripOvershoot X x a R ω)) ∂μ) ≤
      ENNReal.ofReal C := by
    apply gaussianStripOvershoot_lintegral_le hX hi hG hx ha ha'
      hf.ennreal_ofReal (by simp [hf0]) ENNReal.ofReal_ne_top
    intro r hr
    rw [← ofReal_integral_eq_lintegral_ofReal (hb r hr).1
      ((gaussianExcessLaw_positive_ae r).mono (fun u hu => hfn u hu.le))]
    exact ENNReal.ofReal_le_ofReal (hb r hr).2
  have hint := (lintegral_ofReal_ne_top_iff_integrable
    hfm.aestronglyMeasurable hfn').mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint hfn'] at hle
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hle

/-- The first two moments of the actual selected overshoot are bounded independently of the strip. -/
theorem gaussianStripOvershoot_uniform_moments
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a R : ℝ} (hx : x ∈ Icc 0 R) (ha : 0 ≤ a) (ha' : a ≤ 1/2) :
    (Integrable (gaussianStripOvershoot X x a R) μ ∧
      (∫ ω, gaussianStripOvershoot X x a R ω ∂μ) ≤ gaussianExcessExpMomentBound 2) ∧
    (Integrable (fun ω => (gaussianStripOvershoot X x a R ω)^2) μ ∧
      (∫ ω, (gaussianStripOvershoot X x a R ω)^2 ∂μ) ≤ gaussianExcessExpMomentBound 2) := by
  refine ⟨gaussianStripOvershoot_integral_le hX hi hG hx ha ha' measurable_id rfl
    (fun _ hu => hu) (gaussianExcessExpMomentBound_pos 2).le
    (fun _ hr => (gaussianExcessLaw_uniform_moments hr).1), ?_⟩
  exact gaussianStripOvershoot_integral_le hX hi hG hx ha ha' (by fun_prop) (by norm_num)
    (fun u _ => sq_nonneg u) (gaussianExcessExpMomentBound_pos 2).le
    (fun _ hr => (gaussianExcessLaw_uniform_moments hr).2.1)

/-- The lower-exit exponential bound is weighted by the actual lower-exit probability. -/
theorem gaussianStripLowerExit_small_exp_moment_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a R : ℝ} (hx : x ∈ Icc 0 R) (ha : 0 ≤ a) (ha' : a ≤ 1/2) :
    IntegrableOn (fun ω => Real.exp (2*a*gaussianStripOvershoot X x a R ω))
      (gaussianStripLowerExit X x a R) μ ∧
    (∫ ω in gaussianStripLowerExit X x a R,
      Real.exp (2*a*gaussianStripOvershoot X x a R ω) ∂μ) ≤
      (1+2*gaussianExcessExpMomentBound 2*a) * μ.real (gaussianStripLowerExit X x a R) := by
  have := hi.isProbabilityMeasure
  let C := 1+2*gaussianExcessExpMomentBound 2*a
  have hM := (gaussianExcessExpMomentBound_pos 2).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hfm : Measurable (fun ω => Real.exp (2*a*gaussianStripOvershoot X x a R ω)) :=
    ((gaussianStripOvershoot_measurable hX x a R).const_mul (2*a)).exp
  have hfn : 0 ≤ᵐ[μ.restrict (gaussianStripLowerExit X x a R)]
      (fun ω => Real.exp (2*a*gaussianStripOvershoot X x a R ω)) :=
    ae_of_all _ (fun _ => (Real.exp_pos _).le)
  have hle : (∫⁻ ω in gaussianStripLowerExit X x a R,
      ENNReal.ofReal (Real.exp (2*a*gaussianStripOvershoot X x a R ω)) ∂μ) ≤
      ENNReal.ofReal C * μ (gaussianStripLowerExit X x a R) := by
    apply gaussianStripLowerExit_lintegral_le hX hi hG hx ha
      (f := fun u => ENNReal.ofReal (Real.exp (2*a*u)))
      (C := ENNReal.ofReal C) (by fun_prop) ENNReal.ofReal_ne_top
    intro r hr
    rw [← ofReal_integral_eq_lintegral_ofReal (gaussianExcessLaw_integrable_exp r (2*a))
      (ae_of_all _ (fun _ => (Real.exp_pos _).le))]
    exact ENNReal.ofReal_le_ofReal (gaussianExcessLaw_small_exp_moment_le hr ha ha')
  have hle' : (∫⁻ ω in gaussianStripLowerExit X x a R,
      ENNReal.ofReal (Real.exp (2*a*gaussianStripOvershoot X x a R ω)) ∂μ) ≤
      ENNReal.ofReal (C * μ.real (gaussianStripLowerExit X x a R)) := by
    simpa only [ENNReal.ofReal_mul hC, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)] using hle
  have hint := (lintegral_ofReal_ne_top_iff_integrable
    hfm.aestronglyMeasurable hfn).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle')
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint hfn] at hle'
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (measureReal_nonneg))).mp hle'

end SwingRepair
