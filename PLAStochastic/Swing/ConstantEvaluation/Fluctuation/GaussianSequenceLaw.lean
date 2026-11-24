import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.DriftMaximum

/-! # Law invariance for i.i.d. standard Gaussian sequences and the moments of `M_a`

Two i.i.d. standard Gaussian sequences on the same probability space give the same law
to every measurable functional of the whole sequence (both joint laws are the infinite
product `⨂ N(0,1)`).  Shifting or negating an i.i.d. standard Gaussian sequence gives
another one.  The negative-drift maximum `M_a = sup_n (W_n - a n)` is square integrable
for `a > 0`: `M_a² ≤ ∑_{n≥1} (W_n - a n)_+²` and `𝔼(W_n - a n)_+² ≤ (2/a²) e^{-n a²/2}`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair

variable {Ω : Type*} [MeasurableSpace Ω] {X Y : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### Joint law and its invariances -/

/-- The joint law of an i.i.d. standard Gaussian sequence is the infinite product. -/
theorem iidGaussian_map_seq (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    μ.map (fun ω (n : ℕ) => X n ω) = Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1) := by
  rw [hi.map_fun_eq_infinitePi_map hX]
  simp_rw [hG]

/-- Shifting the index keeps the sequence i.i.d. standard Gaussian. -/
theorem iidGaussian_shift (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (s : ℕ) :
    (∀ n, Measurable (fun ω => X (s + n) ω)) ∧ iIndepFun (fun n ω => X (s + n) ω) μ ∧
      ∀ n, μ.map (fun ω => X (s + n) ω) = gaussianReal 0 1 :=
  ⟨fun n => hX (s + n),
    hi.precomp (g := fun n : ℕ => s + n) (by intro i j h; dsimp at h; omega),
    fun n => hG (s + n)⟩

/-- Negating keeps the sequence i.i.d. standard Gaussian. -/
theorem iidGaussian_neg (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    (∀ n, Measurable (fun ω => -X n ω)) ∧ iIndepFun (fun n ω => -X n ω) μ ∧
      ∀ n, μ.map (fun ω => -X n ω) = gaussianReal 0 1 := by
  refine ⟨fun n => (hX n).neg, ?_, fun n => ?_⟩
  · exact hi.comp (fun _ (x : ℝ) => -x) (fun _ => measurable_neg)
  · have : (fun ω => -X n ω) = (fun x : ℝ => -x) ∘ X n := rfl
    rw [this, ← Measure.map_map measurable_neg (hX n), hG n, gaussianReal_map_neg, neg_zero]

/-- Two i.i.d. standard Gaussian sequences give the same law to every measurable
functional of the whole sequence. -/
theorem iidGaussian_map_functional_eq {E : Type*} [MeasurableSpace E]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hY : ∀ n, Measurable (Y n)) (hiY : iIndepFun Y μ) (hGY : ∀ n, μ.map (Y n) = gaussianReal 0 1)
    {Ψ : (ℕ → ℝ) → E} (hΨ : Measurable Ψ) :
    μ.map (fun ω => Ψ (fun n => X n ω)) = μ.map (fun ω => Ψ (fun n => Y n ω)) := by
  have h1 : (fun ω => Ψ (fun n => X n ω)) = Ψ ∘ (fun ω (n : ℕ) => X n ω) := rfl
  have h2 : (fun ω => Ψ (fun n => Y n ω)) = Ψ ∘ (fun ω (n : ℕ) => Y n ω) := rfl
  rw [h1, h2, ← Measure.map_map hΨ (measurable_pi_lambda _ hX),
    ← Measure.map_map hΨ (measurable_pi_lambda _ hY), iidGaussian_map_seq hX hi hG,
    iidGaussian_map_seq hY hiY hGY]

theorem iidGaussian_measure_functional_eq
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hY : ∀ n, Measurable (Y n)) (hiY : iIndepFun Y μ) (hGY : ∀ n, μ.map (Y n) = gaussianReal 0 1)
    {A : Set (ℕ → ℝ)} (hA : MeasurableSet A) :
    μ ((fun ω (n : ℕ) => X n ω) ⁻¹' A) = μ ((fun ω (n : ℕ) => Y n ω) ⁻¹' A) := by
  rw [← Measure.map_apply (measurable_pi_lambda _ hX) hA,
    ← Measure.map_apply (measurable_pi_lambda _ hY) hA, iidGaussian_map_seq hX hi hG,
    iidGaussian_map_seq hY hiY hGY]

theorem iidGaussian_integral_functional_eq
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hY : ∀ n, Measurable (Y n)) (hiY : iIndepFun Y μ) (hGY : ∀ n, μ.map (Y n) = gaussianReal 0 1)
    {Ψ : (ℕ → ℝ) → ℝ} (hΨ : Measurable Ψ) :
    ∫ ω, Ψ (fun n => X n ω) ∂μ = ∫ ω, Ψ (fun n => Y n ω) ∂μ := by
  rw [← integral_map (measurable_pi_lambda _ hX).aemeasurable hΨ.aestronglyMeasurable,
    ← integral_map (measurable_pi_lambda _ hY).aemeasurable hΨ.aestronglyMeasurable,
    iidGaussian_map_seq hX hi hG, iidGaussian_map_seq hY hiY hGY]

theorem iidGaussian_integrable_functional_iff
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hY : ∀ n, Measurable (Y n)) (hiY : iIndepFun Y μ) (hGY : ∀ n, μ.map (Y n) = gaussianReal 0 1)
    {Ψ : (ℕ → ℝ) → ℝ} (hΨ : Measurable Ψ) :
    Integrable (fun ω => Ψ (fun n => X n ω)) μ ↔ Integrable (fun ω => Ψ (fun n => Y n ω)) μ := by
  have h1 : (fun ω => Ψ (fun n => X n ω)) = Ψ ∘ (fun ω (n : ℕ) => X n ω) := rfl
  have h2 : (fun ω => Ψ (fun n => Y n ω)) = Ψ ∘ (fun ω (n : ℕ) => Y n ω) := rfl
  rw [h1, h2, ← integrable_map_measure hΨ.aestronglyMeasurable
      (measurable_pi_lambda _ hX).aemeasurable,
    ← integrable_map_measure hΨ.aestronglyMeasurable (measurable_pi_lambda _ hY).aemeasurable,
    iidGaussian_map_seq hX hi hG, iidGaussian_map_seq hY hiY hGY]

/-! ### The canonical maximum functional -/

/-- `M_a` as a functional of the whole sequence. -/
def canonicalDriftMaximum (a : ℝ) : (ℕ → ℝ) → ℝ :=
  driftMaximum (fun n (w : ℕ → ℝ) => w n) a

theorem canonicalDriftMaximum_measurable (a : ℝ) : Measurable (canonicalDriftMaximum a) :=
  driftMaximum_measurable (fun n => measurable_pi_apply n) a

omit [MeasurableSpace Ω] in
theorem driftMaximum_eq_canonical (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) :
    driftMaximum X a ω = canonicalDriftMaximum a (fun n => X n ω) := rfl

/-- The law of `M_a` is the same for all i.i.d. standard Gaussian sequences. -/
theorem integral_driftMaximum_eq
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hY : ∀ n, Measurable (Y n)) (hiY : iIndepFun Y μ) (hGY : ∀ n, μ.map (Y n) = gaussianReal 0 1)
    (a : ℝ) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    ∫ ω, φ (driftMaximum X a ω) ∂μ = ∫ ω, φ (driftMaximum Y a ω) ∂μ := by
  simp_rw [driftMaximum_eq_canonical]
  exact iidGaussian_integral_functional_eq hX hi hG hY hiY hGY
    (hφ.comp (canonicalDriftMaximum_measurable a))

theorem integrable_driftMaximum_iff
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hY : ∀ n, Measurable (Y n)) (hiY : iIndepFun Y μ) (hGY : ∀ n, μ.map (Y n) = gaussianReal 0 1)
    (a : ℝ) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Integrable (fun ω => φ (driftMaximum X a ω)) μ ↔
      Integrable (fun ω => φ (driftMaximum Y a ω)) μ := by
  simp_rw [driftMaximum_eq_canonical]
  exact iidGaussian_integrable_functional_iff hX hi hG hY hiY hGY
    (hφ.comp (canonicalDriftMaximum_measurable a))

/-! ### Square integrability of `M_a` -/

theorem posPart_sq_le_exp {a : ℝ} (ha : 0 < a) (u : ℝ) :
    (max u 0) ^ 2 ≤ 2 / a ^ 2 * Real.exp (a * u) := by
  rcases le_or_gt u 0 with hu | hu
  · rw [max_eq_right hu]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · rw [max_eq_left hu.le]
    have h := Real.quadratic_le_exp_of_nonneg (mul_nonneg ha.le hu.le)
    have hau : 0 < a * u := mul_pos ha hu
    have ha2 : (0 : ℝ) < a ^ 2 := by positivity
    have hkey : (a * u) ^ 2 / 2 ≤ Real.exp (a * u) := by linarith
    calc u ^ 2 = 2 / a ^ 2 * ((a * u) ^ 2 / 2) := by field_simp
      _ ≤ 2 / a ^ 2 * Real.exp (a * u) := by gcongr

/-- `𝔼 exp(a (W_n - a n)) = exp(-n a²/2)`. -/
theorem integral_exp_negDriftWalk (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) (n : ℕ) :
    ∫ ω, Real.exp (a * negDriftWalk X a n ω) ∂μ = Real.exp (-(n * a ^ 2 / 2)) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hl : HasLaw (cumulativeSamples X n) (gaussianReal 0 (n : ℝ≥0)) μ := by
    simpa [cumulativeSamples] using!
      gaussian_weighted_sum_hasLaw hX hi hG (Finset.range n) (fun _ => 1)
  have hm := mgf_gaussianReal hl.map_eq a
  simp only [mgf, NNReal.coe_natCast, zero_mul, zero_add] at hm
  have heq : (fun ω => Real.exp (a * negDriftWalk X a n ω)) =
      fun ω => Real.exp (-(a * (a * n))) * Real.exp (a * cumulativeSamples X n ω) := by
    funext ω
    rw [negDriftWalk_eq, ← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul, hm, ← Real.exp_add]
  congr 1
  ring

/-- `𝔼 (W_n - a n)_+² ≤ (2/a²) exp(-n a²/2)`. -/
theorem lintegral_negDriftWalk_posPart_sq_le (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((max (negDriftWalk X a n ω) 0) ^ 2) ∂μ ≤
      ENNReal.ofReal (2 / a ^ 2 * Real.exp (-(n * a ^ 2 / 2))) := by
  have hint : Integrable (fun ω => 2 / a ^ 2 * Real.exp (a * negDriftWalk X a n ω)) μ :=
    (gaussianDriftWalk_integrable_exp hX hi hG 0 (-a) a n).const_mul _
  calc ∫⁻ ω, ENNReal.ofReal ((max (negDriftWalk X a n ω) 0) ^ 2) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (2 / a ^ 2 * Real.exp (a * negDriftWalk X a n ω)) ∂μ :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (posPart_sq_le_exp ha _)
    _ = ENNReal.ofReal (∫ ω, 2 / a ^ 2 * Real.exp (a * negDriftWalk X a n ω) ∂μ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => by positivity)]
    _ = ENNReal.ofReal (2 / a ^ 2 * Real.exp (-(n * a ^ 2 / 2))) := by
        rw [integral_const_mul, integral_exp_negDriftWalk hX hi hG a n]

theorem summable_exp_neg_sq_mul {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ => 2 / a ^ 2 * Real.exp (-(((n + 1 : ℕ) : ℝ) * a ^ 2 / 2)) := by
  have hr0 : 0 ≤ Real.exp (-(a ^ 2 / 2)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(a ^ 2 / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : 0 < a ^ 2 / 2 := by positivity
    linarith
  have hgeom := (summable_geometric_of_lt_one hr0 hr1).mul_left (2 / a ^ 2 * Real.exp (-(a ^ 2 / 2)))
  refine hgeom.congr fun n => ?_
  rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  ring

/-- `∫ M_a² < ∞` for `a > 0`. -/
theorem lintegral_driftMaximum_sq_lt_top (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    ∫⁻ ω, ENNReal.ofReal (driftMaximum X a ω ^ 2) ∂μ < ⊤ := by
  have hbound : ∀ᵐ ω ∂μ, ENNReal.ofReal (driftMaximum X a ω ^ 2) ≤
      ∑' n : ℕ, ENNReal.ofReal ((max (negDriftWalk X a (n + 1) ω) 0) ^ 2) := by
    filter_upwards [driftMaxAttained_ae hX hi hG ha] with ω hω
    have hnn : 0 ≤ driftMaximum X a ω := driftMaximum_nonneg hω
    rw [driftMaximum_eq_argmax hω] at hnn ⊢
    rcases Nat.eq_zero_or_pos (driftArgmax X a ω) with h0 | hpos
    · rw [h0, negDriftWalk_zero]
      simp
    · obtain ⟨k, hk⟩ : ∃ k, driftArgmax X a ω = k + 1 :=
        ⟨driftArgmax X a ω - 1, by omega⟩
      rw [hk] at hnn ⊢
      calc ENNReal.ofReal (negDriftWalk X a (k + 1) ω ^ 2)
          = ENNReal.ofReal ((max (negDriftWalk X a (k + 1) ω) 0) ^ 2) := by
            rw [max_eq_left hnn]
        _ ≤ ∑' n : ℕ, ENNReal.ofReal ((max (negDriftWalk X a (n + 1) ω) 0) ^ 2) :=
            ENNReal.le_tsum k
  have hmeas : ∀ n : ℕ, Measurable fun ω =>
      ENNReal.ofReal ((max (negDriftWalk X a (n + 1) ω) 0) ^ 2) := fun n =>
    ENNReal.measurable_ofReal.comp
      (((negDriftWalk_measurable hX a (n + 1)).max measurable_const).pow_const 2)
  calc ∫⁻ ω, ENNReal.ofReal (driftMaximum X a ω ^ 2) ∂μ
      ≤ ∫⁻ ω, ∑' n : ℕ, ENNReal.ofReal ((max (negDriftWalk X a (n + 1) ω) 0) ^ 2) ∂μ :=
        lintegral_mono_ae hbound
    _ = ∑' n : ℕ, ∫⁻ ω, ENNReal.ofReal ((max (negDriftWalk X a (n + 1) ω) 0) ^ 2) ∂μ :=
        lintegral_tsum fun n => (hmeas n).aemeasurable
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (2 / a ^ 2 * Real.exp (-(((n + 1 : ℕ) : ℝ) * a ^ 2 / 2))) :=
        ENNReal.tsum_le_tsum fun n => lintegral_negDriftWalk_posPart_sq_le hX hi hG ha (n + 1)
    _ = ENNReal.ofReal (∑' n : ℕ, 2 / a ^ 2 * Real.exp (-(((n + 1 : ℕ) : ℝ) * a ^ 2 / 2))) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (summable_exp_neg_sq_mul ha)).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- `M_a ∈ L²` for `a > 0`. -/
theorem integrable_driftMaximum_sq (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    Integrable (fun ω => driftMaximum X a ω ^ 2) μ := by
  refine ⟨((driftMaximum_measurable hX a).pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => sq_nonneg _)]
  exact lintegral_driftMaximum_sq_lt_top hX hi hG ha

theorem memLp_two_driftMaximum (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    MemLp (driftMaximum X a) 2 μ :=
  (memLp_two_iff_integrable_sq (driftMaximum_measurable hX a).aestronglyMeasurable).mpr
    (integrable_driftMaximum_sq hX hi hG ha)

/-- `M_a ∈ L¹` for `a > 0`. -/
theorem integrable_driftMaximum (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    Integrable (driftMaximum X a) μ := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  exact (memLp_two_driftMaximum hX hi hG ha).integrable one_le_two

end SwingRepair
