import PLAStochastic.Swing.Gaussian.Survival.FiniteTilt
import PLAStochastic.Swing.Gaussian.Survival.SmallDrift

/-! Finite-coordinate likelihood identities for the actual Gaussian survival event. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def gaussianFiniteSamples (n k : ℕ) (z : Fin n → ℝ) : ℝ :=
  if hk : k < n then z ⟨k, hk⟩ else 0

theorem gaussianFiniteSamples_measurable (n k : ℕ) : Measurable (gaussianFiniteSamples n k) := by
  unfold gaussianFiniteSamples
  split_ifs <;> fun_prop

theorem cumulativeSamples_gaussianFiniteSamples (n : ℕ) (z : Fin n → ℝ) :
    cumulativeSamples (gaussianFiniteSamples n) n z = ∑ i, z i := by
  exact (Finset.sum_fin_eq_sum_range z).symm

theorem gaussianFiniteSamples_translate {n j : ℕ} (hj : j ≤ n)
    (z : Fin n → ℝ) (x a b : ℝ) :
    gaussianDriftWalk (gaussianFiniteSamples n) x a j (fun i => z i+b) =
    gaussianDriftWalk (gaussianFiniteSamples n) x (a+b) j z := by
  have he : cumulativeSamples (gaussianFiniteSamples n) j (fun i => z i+b) =
      cumulativeSamples (gaussianFiniteSamples n) j z+b*j := by
    unfold cumulativeSamples
    calc
      _ = ∑ k ∈ Finset.range j, (gaussianFiniteSamples n k z+b) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k < n := lt_of_lt_of_le (Finset.mem_range.mp hk) hj
        simp only [gaussianFiniteSamples, dif_pos hkn]
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]; ring
  dsimp only [gaussianDriftWalk]
  rw [he]
  ring

theorem gaussianFiniteSamples_survives_translate (n : ℕ) (z : Fin n → ℝ) (x a b : ℝ) :
    (fun i => z i+b) ∈ gaussianHalfLineSurvives (gaussianFiniteSamples n) x a n ↔
      z ∈ gaussianHalfLineSurvives (gaussianFiniteSamples n) x (a+b) n := by
  simp only [gaussianHalfLineSurvives, mem_ofPred_eq]
  constructor <;> intro h j hj
  · rw [← gaussianFiniteSamples_translate hj z x a b]
    exact h j hj
  · rw [gaussianFiniteSamples_translate hj z x a b]
    exact h j hj

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

omit mΩ in
theorem gaussianFiniteSamples_actual {n j : ℕ} (hj : j ≤ n) (x a : ℝ) (ω : Ω) :
    gaussianDriftWalk (gaussianFiniteSamples n) x a j (fun i => X i.val ω) =
      gaussianDriftWalk X x a j ω := by
  unfold gaussianDriftWalk cumulativeSamples
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k < n := lt_of_lt_of_le (Finset.mem_range.mp hk) hj
  simp only [gaussianFiniteSamples, dif_pos hkn]

omit mΩ in
theorem gaussianFiniteSamples_actual_survives (n : ℕ) (x a : ℝ) (ω : Ω) :
    (fun i : Fin n => X i.val ω) ∈ gaussianHalfLineSurvives (gaussianFiniteSamples n) x a n ↔
      ω ∈ gaussianHalfLineSurvives X x a n := by
  simp only [gaussianHalfLineSurvives, mem_ofPred_eq]
  constructor <;> intro h j hj
  · rw [← gaussianFiniteSamples_actual hj x a ω]
    exact h j hj
  · rw [gaussianFiniteSamples_actual hj x a ω]
    exact h j hj

theorem gaussianFiniteSamples_hasLaw
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    HasLaw (fun ω => fun i : Fin n => X i.val ω)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) μ :=
  (iIndepFun.precomp Fin.val_injective hi).hasLaw_pi
    (fun i => ⟨(hX i.val).aemeasurable, hG i.val⟩)


theorem gaussianFiniteSamples_survives_measurable (n : ℕ) (x a : ℝ) :
    MeasurableSet (gaussianHalfLineSurvives (gaussianFiniteSamples n) x a n) :=
  incrementIndexSpace_le (gaussianFiniteSamples_measurable n) _ _
    (gaussianHalfLineSurvives_measurable_past _ _ _ _)

theorem gaussianFiniteSurvival_integral
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) (x a : ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ ω in gaussianHalfLineSurvives X x a n, f (cumulativeSamples X n ω) ∂μ) =
    ∫ z in gaussianHalfLineSurvives (gaussianFiniteSamples n) x a n, f (∑ i, z i)
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  have hA : MeasurableSet (gaussianHalfLineSurvives X x a n) :=
    incrementIndexSpace_le hX _ _ (gaussianHalfLineSurvives_measurable_past _ _ _ _)
  have hB := gaussianFiniteSamples_survives_measurable n x a
  rw [← integral_indicator hA, ← integral_indicator hB]
  have he := (gaussianFiniteSamples_hasLaw hX hi hG n).integral_comp
    ((hf.comp (show Measurable (fun z : Fin n → ℝ => ∑ i, z i) by fun_prop)).indicator hB).aestronglyMeasurable
  dsimp only [Function.comp_def] at he
  rw [← he]
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  have hmem := gaussianFiniteSamples_actual_survives (X := X) n x a ω
  have hsum : ∑ i : Fin n, X i.val ω = cumulativeSamples X n ω :=
    Fin.sum_univ_eq_sum_range (fun i => X i ω) n
  by_cases h : ω ∈ gaussianHalfLineSurvives X x a n
  · simp only [indicator_of_mem h, indicator_of_mem (hmem.mpr h), hsum]
  · simp only [indicator_of_notMem h, indicator_of_notMem (mt hmem.mp h)]

/-- The density change is carried back to the original iid Gaussian sample space. -/
theorem gaussianHalfLineSurvives_change_drift
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) (x a b : ℝ) :
    μ.real (gaussianHalfLineSurvives X x (a+b) n) =
    ∫ ω in gaussianHalfLineSurvives X x a n,
      Real.exp (b*cumulativeSamples X n ω-(n : ℝ)*b^2/2) ∂μ := by
  have hB := gaussianFiniteSamples_survives_measurable n x a
  have hB' := gaussianFiniteSamples_survives_measurable n x (a+b)
  have hprob := gaussianFiniteSurvival_integral hX hi hG n x (a+b)
    (f := fun _ => (1 : ℝ)) measurable_const
  simp only [setIntegral_const, smul_eq_mul, mul_one] at hprob
  rw [hprob, gaussianFiniteSurvival_integral hX hi hG n x a
    (f := fun u => Real.exp (b*u-(n : ℝ)*b^2/2)) (by fun_prop)]
  have he := gaussianPi_integral_translate b (measurable_const.indicator hB :
    Measurable ((gaussianHalfLineSurvives (gaussianFiniteSamples n) x a n).indicator (fun _ => (1 : ℝ))))
  calc
    _ = ∫ z, (gaussianHalfLineSurvives (gaussianFiniteSamples n) x a n).indicator
        (fun _ => (1 : ℝ)) (fun i => z i+b)
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
      rw [← integral_indicator_one hB']
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        simp only [indicator_apply, Pi.one_apply, gaussianFiniteSamples_survives_translate])
    _ = _ := by
      rw [he, ← integral_indicator hB]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        by_cases h : z ∈ gaussianHalfLineSurvives (gaussianFiniteSamples n) x a n
        · simp only [indicator_of_mem h, mul_one]
        · simp only [indicator_of_notMem h, mul_zero])


omit mΩ in
/-- Adding the initial nonnegative state identifies the two prefix conventions. -/
theorem gaussianHalfLineSurvives_eq_survivalEvent {x a : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    gaussianHalfLineSurvives X x a n = gaussianSurvivalEvent X x a n := by
  ext ω
  constructor
  · intro h j hj
    exact h j hj.2
  · intro h j hj
    by_cases hj0 : j = 0
    · simpa only [hj0, gaussianDriftWalk_zero] using hx
    · exact h j ⟨Nat.one_le_iff_ne_zero.mpr hj0, hj⟩

/-- The weighted surviving endpoint is the opposite-drift survival probability. -/
theorem gaussianHalfLineSurvives_weighted_endpoint
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) (x a : ℝ) :
    (∫ ω in gaussianHalfLineSurvives X x a n,
      Real.exp (-2*a*gaussianDriftWalk X x a n ω) ∂μ) =
    Real.exp (-2*a*x)*μ.real (gaussianHalfLineSurvives X x (-a) n) := by
  rw [show -a = a+(-2*a) by ring, gaussianHalfLineSurvives_change_drift hX hi hG,
    ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => by
    dsimp only
    rw [← Real.exp_add]
    congr 1
    unfold gaussianDriftWalk
    ring)

theorem gaussianLikelihood_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) (b : ℝ) :
    Integrable (fun ω => Real.exp (b*cumulativeSamples X n ω-(n : ℝ)*b^2/2)) μ := by
  have he := (gaussianDriftWalk_integrable_exp hX hi hG 0 0 b n).const_mul
    (Real.exp (-(n : ℝ)*b^2/2))
  apply he.congr
  exact ae_of_all _ (fun ω => by
    dsimp only
    rw [← Real.exp_add]
    congr 1
    unfold gaussianDriftWalk
    ring)

/-- On zero-drift survival, the endpoint sign bounds the exact likelihood. -/
theorem gaussianHalfLineSurvives_negative_drift_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) (x : ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    μ.real (gaussianHalfLineSurvives X x (-a) n) ≤
      Real.exp (a*x-(n : ℝ)*a^2/2)*μ.real (gaussianHalfLineSurvives X x 0 n) := by
  have := hi.isProbabilityMeasure
  have hA : MeasurableSet (gaussianHalfLineSurvives X x 0 n) :=
    incrementIndexSpace_le hX _ _ (gaussianHalfLineSurvives_measurable_past _ _ _ _)
  rw [show -a = 0+(-a) by ring, gaussianHalfLineSurvives_change_drift hX hi hG]
  calc
    _ ≤ ∫ _ in gaussianHalfLineSurvives X x 0 n,
        Real.exp (a*x-(n : ℝ)*a^2/2) ∂μ := by
      apply setIntegral_mono_on (gaussianLikelihood_integrable hX hi hG n (-a)).integrableOn
        (integrable_const _) hA
      intro ω hω
      have hend := hω n le_rfl
      simp only [gaussianDriftWalk, zero_mul, add_zero] at hend
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg ha hend]
    _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_comm]

end SwingRepair
