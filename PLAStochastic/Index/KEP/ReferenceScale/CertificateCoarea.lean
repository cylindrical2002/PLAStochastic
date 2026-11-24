import PLAStochastic.Index.GEP.SurvivalBound.GoodSlope
import PLAStochastic.Index.GEP.Kernel.Facet.SlopeCoarea
import PLAStochastic.Index.KEP.ReferenceScale.ActualBridgeWard

/-!
# Exact coarea of the real minimal-slope certificate

The middle block uses its actual last gap as the coarea coordinate. Its total
gap is changed to the physical slope, retaining the exact coefficient `d/a`.
This is an identity for the original iid certificate, rather than an assumed
representation of a selected bridge.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kep_surv_wint_zero (ν σ : ProbabilityMeasure ℝ) (n : ℕ)
    (F : (ℕ → ℝ) → ℂ) : surv_wint ν σ 0 n F = ∫ g, F g ∂iidLaw ν := by
  classical
  unfold surv_wint surv_wcoef
  rw [Finset.sum_eq_single ∅]
  · simp [wordLaw_empty]
  · intro S _ hS
    have hcard : S.card ≠ 0 := by simpa using hS
    simp [zero_pow hcard]
  · simp

set_option backward.isDefEq.respectTransparency.types false in
theorem kep_integral_reciprocal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℝ} (hd : 0 < d) (G : ℝ → E) :
    (∫ t in Ioi (0 : ℝ), G t) =
      ∫ a in Ioi (0 : ℝ), (d / a ^ 2) • G (d / a) := by
  have hd' (a : ℝ) (ha : a ∈ Ioi (0 : ℝ)) :
      HasDerivWithinAt (fun a : ℝ => d / a) (-d / a ^ 2) (Ioi 0) a := by
    have hder : HasDerivAt (fun z : ℝ => d / z) ((0 * a - d * 1) / a ^ 2) a :=
      (hasDerivAt_const a d).div (hasDerivAt_id a) (ne_of_gt ha)
    simpa only [zero_mul, mul_one, zero_sub] using hder.hasDerivWithinAt (s := Ioi 0)
  have hinj : InjOn (fun a : ℝ => d / a) (Ioi 0) := by
    intro a ha b hb hab
    have hh := (div_eq_div_iff (ne_of_gt ha) (ne_of_gt hb)).mp hab
    exact (mul_left_cancel₀ hd.ne' hh).symm
  have himg : (fun a : ℝ => d / a) '' Ioi 0 = Ioi 0 := by
    simpa only [sub_zero, neg_zero] using kernel_reciprocal_image hd 0
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd' hinj G
  rw [himg] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro a _
  dsimp only
  rw [show -d / a ^ 2 = -(d / a ^ 2) by ring,
    abs_neg, abs_of_nonneg (div_nonneg hd.le (sq_nonneg a))]

theorem kep_integral_iid_last_shift (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {F : (ℕ → ℝ) → ℝ} (hF : Measurable F) {M : ℝ} (hM : ∀ g, |F g| ≤ M)
    (n : ℕ) :
    (∫ g, F g ∂iidLaw ν) =
      ∫ t, ∫ g, f (t - gapKeys g n) *
        F (Function.update g n (t - gapKeys g n)) ∂iidLaw ν := by
  have h := surv_integral_wordLaw_shift ν ν ∅ (m := n) (by simp)
    hf hf0 hν (rawAsm_measurable_gapKeys n)
    (F := fun g => (F g : ℂ)) (Complex.measurable_ofReal.comp hF)
    (M := M) (fun g => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hM g)
  rw [wordLaw_empty] at h
  have hr := congrArg Complex.re h
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal, Complex.ofReal_re] using hr

def kepCertificateMiddle (eps d : ℝ) (n : ℕ) (Ψ : ℝ → ℝ) (g : ℕ → ℝ) : ℝ :=
  Ψ (d / gapKeys g (n + 1)) *
    ∏ l ∈ Finset.range (n + 2), (Icc (0 : ℝ) (2 * eps)).indicator (fun _ => (1 : ℝ))
      (kWalk 0 1 (d / gapKeys g (n + 1)) g l)

theorem measurable_kepCertificateMiddle (eps d : ℝ) (n : ℕ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) : Measurable (kepCertificateMiddle eps d n Ψ) := by
  unfold kepCertificateMiddle kWalk
  refine (hΨ.comp (measurable_const.div (rawAsm_measurable_gapKeys (n + 1)))).mul
    (Finset.measurable_prod _ fun l _ => ?_)
  exact (measurable_const.indicator measurableSet_Icc).comp
    (measurable_const.sub ((measurable_const.div (rawAsm_measurable_gapKeys (n + 1))).mul
      (rawAsm_measurable_gapKeys l)))

theorem abs_kepCertificateMiddle_le (eps d : ℝ) (n : ℕ) {Ψ : ℝ → ℝ} {M : ℝ}
    (hΨ : ∀ a, |Ψ a| ≤ M) (g : ℕ → ℝ) : |kepCertificateMiddle eps d n Ψ g| ≤ M := by
  unfold kepCertificateMiddle
  rw [abs_mul, Finset.abs_prod]
  have hp : ∏ l ∈ Finset.range (n + 2),
      |(Icc (0 : ℝ) (2 * eps)).indicator (fun _ => (1 : ℝ))
        (kWalk 0 1 (d / gapKeys g (n + 1)) g l)| ≤ 1 :=
    Finset.prod_le_one (fun _ _ => abs_nonneg _) fun l _ => by
      by_cases h : kWalk 0 1 (d / gapKeys g (n + 1)) g l ∈ Icc (0 : ℝ) (2 * eps) <;> simp [h]
  have hM : 0 ≤ M := (abs_nonneg (Ψ 0)).trans (hΨ 0)
  calc
    _ ≤ M * 1 := mul_le_mul (hΨ _) hp (Finset.prod_nonneg fun _ _ => abs_nonneg _) hM
    _ = M := mul_one _

/-- The last gap parametrizes the total middle span. The original path
indicators become exactly the killed density, including both endpoints. -/
theorem kepCertificateMiddle_last_gap (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {eps d t : ℝ} (heps : 0 ≤ eps) (hd : 0 < d) (n : ℕ)
    (hddef : d = (n + 1 : ℕ) - 2 * eps) {Ψ : ℝ → ℝ}
    (hΨ0 : ∀ a, a ∉ Icc (1 / 2 : ℝ) 2 → Ψ a = 0) :
    (∫ g, f (t - gapKeys g n) *
      kepCertificateMiddle eps d n Ψ (Function.update g n (t - gapKeys g n)) ∂iidLaw ν) =
    Ψ (d / t) * (d / t) * krDens (Icc 0 (2 * eps)) ν f 1 (d / t) (n + 1) 0 (2 * eps) := by
  have hkeys (g : ℕ → ℝ) :
      gapKeys (Function.update g n (t - gapKeys g n)) (n + 1) = t := by
    rw [gapKeys_update_succ]
    ring
  by_cases ha : d / t ∈ Icc (1 / 2 : ℝ) 2
  · have ha0 : 0 < d / t := by linarith [ha.1]
    have ht : t ≠ 0 := by intro h; simp [h] at ha0
    have hat : d / t * t = d := div_mul_cancel₀ d ht
    have hendpoint (g : ℕ → ℝ) :
        kWalk 0 1 (d / t) (Function.update g n (t - gapKeys g n)) (n + 1) = 2 * eps := by
      simp only [kWalk, hkeys, zero_add, mul_one, hat]
      rw [hddef]
      ring
    have hpre (g : ℕ → ℝ) (l : ℕ) (hl : l ≤ n) :
        kWalk 0 1 (d / t) (Function.update g n (t - gapKeys g n)) l =
          kWalk 0 1 (d / t) g l :=
      surv_kWalk_congr fun s hs => Function.update_of_ne (by omega) _ _
    rw [krDens_succ, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun g => by
      dsimp only
      unfold kepCertificateMiddle
      rw [hkeys, Finset.prod_range_succ, hendpoint,
        indicator_of_mem (show 2 * eps ∈ Icc (0 : ℝ) (2 * eps) from ⟨by linarith, le_rfl⟩),
        mul_one]
      have hp : (∏ l ∈ Finset.range (n + 1),
          (Icc (0 : ℝ) (2 * eps)).indicator (fun _ => (1 : ℝ))
            (kWalk 0 1 (d / t) (Function.update g n (t - gapKeys g n)) l)) =
          krAlive (Icc 0 (2 * eps)) 1 (d / t) n 0 g := by
        unfold krAlive
        apply Finset.prod_congr rfl
        intro l hl
        rw [hpre g l (by have := Finset.mem_range.mp hl; omega)]
      rw [hp]
      unfold krKer
      rw [indicator_of_mem
        (show 2 * eps ∈ Icc (0 : ℝ) (2 * eps) from ⟨by linarith, le_rfl⟩)]
      by_cases hu : kWalk 0 1 (d / t) g n ∈ Icc (0 : ℝ) (2 * eps)
      · rw [indicator_of_mem hu, abs_of_pos ha0]
        have harg : (kWalk 0 1 (d / t) g n + 1 - 2 * eps) / (d / t) =
            t - gapKeys g n := by
          simp only [kWalk, zero_add, mul_one]
          have hn : (n : ℝ) + 1 - 2 * eps = d := by simpa using hddef.symm
          rw [show (n : ℝ) - d / t * gapKeys g n + 1 - 2 * eps =
            d - d / t * gapKeys g n by linarith]
          field_simp
        rw [harg]
        field_simp
      · rw [indicator_of_notMem hu]
        have hzero : krAlive (Icc 0 (2 * eps)) 1 (d / t) n 0 g = 0 := by
          unfold krAlive
          rw [Finset.prod_range_succ, indicator_of_notMem hu, mul_zero]
        rw [hzero]
        ring
  · have hz := hΨ0 (d / t) ha
    rw [hz, zero_mul, zero_mul]
    apply integral_eq_zero_of_ae
    exact ae_of_all _ fun g => by simp [kepCertificateMiddle, hkeys, hz]

/-- Exact physical-slope coarea for the original iid middle certificate.
No smoothness or derivative estimate is a premise of this identification. -/
theorem integral_kepCertificateMiddle_eq_killed_bridge (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {eps d : ℝ} (heps : 0 ≤ eps) (hd : 0 < d) (n : ℕ)
    (hddef : d = (n + 1 : ℕ) - 2 * eps) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    {M : ℝ} (hΨb : ∀ a, |Ψ a| ≤ M)
    (hΨ0 : ∀ a, a ∉ Icc (1 / 2 : ℝ) 2 → Ψ a = 0) :
    (∫ g, kepCertificateMiddle eps d n Ψ g ∂iidLaw ν) =
      ∫ a in Ioi (0 : ℝ), d / a * Ψ a *
        krDens (Icc 0 (2 * eps)) ν f 1 a (n + 1) 0 (2 * eps) := by
  rw [kep_integral_iid_last_shift ν hf hf0 hν
    (measurable_kepCertificateMiddle eps d n hΨ)
    (abs_kepCertificateMiddle_le eps d n hΨb) n]
  simp_rw [kepCertificateMiddle_last_gap ν heps hd n hddef hΨ0]
  have hpos : (∫ t, Ψ (d / t) * (d / t) *
      krDens (Icc 0 (2 * eps)) ν f 1 (d / t) (n + 1) 0 (2 * eps)) =
      ∫ t in Ioi (0 : ℝ), Ψ (d / t) * (d / t) *
        krDens (Icc 0 (2 * eps)) ν f 1 (d / t) (n + 1) 0 (2 * eps) := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    exact ae_of_all _ fun t => by
      dsimp only
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem ht]
      · rw [indicator_of_notMem ht]
        have ha : d / t ∉ Icc (1 / 2 : ℝ) 2 := by
          intro h
          have hdt : d / t ≤ 0 := div_nonpos_of_nonneg_of_nonpos hd.le (not_lt.mp ht)
          linarith [h.1]
        rw [hΨ0 _ ha]
        ring
  rw [hpos, kep_integral_reciprocal hd]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro a ha
  dsimp only
  have haa : d / (d / a) = a := by field_simp
  rw [haa, smul_eq_mul]
  field_simp

theorem kep_integral_positive_eq_logSlope {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (G : ℝ → E) :
    (∫ a in Ioi (0 : ℝ), G a) = ∫ s, Real.exp s • G (Real.exp s) := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := univ)
    MeasurableSet.univ (fun s _ => (Real.hasDerivAt_exp s).hasDerivWithinAt)
    Real.exp_injective.injOn G
  simpa only [image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _),
    Measure.restrict_univ] using h

theorem integral_kepCertificateMiddle_eq_logBridge (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {eps d : ℝ} (heps : 0 ≤ eps) (hd : 0 < d) (n : ℕ)
    (hddef : d = (n + 1 : ℕ) - 2 * eps) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    {M : ℝ} (hΨb : ∀ a, |Ψ a| ≤ M)
    (hΨ0 : ∀ a, a ∉ Icc (1 / 2 : ℝ) 2 → Ψ a = 0) :
    (∫ g, kepCertificateMiddle eps d n Ψ g ∂iidLaw ν) =
      ∫ s, d * Ψ (Real.exp s) * kepFixedBridge (kepLogStep f 1) (2 * eps) s n 0 (2 * eps) := by
  rw [integral_kepCertificateMiddle_eq_killed_bridge ν hf hf0 hν heps hd n hddef hΨ hΨb hΨ0,
    kep_integral_positive_eq_logSlope]
  apply integral_congr_ae
  exact ae_of_all _ fun s => by
    dsimp only
    rw [kepLogBridge_eq_krDens ν hf hf0 hfD hν (Or.inl rfl) s n
      ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩, one_mul, smul_eq_mul]
    field_simp

end

end PGM
