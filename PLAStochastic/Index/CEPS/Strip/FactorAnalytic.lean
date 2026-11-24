import PLAStochastic.Index.CEPS.Strip.FactorEnvelope
import PLAStochastic.Index.CEPS.Strip.StripRegion
import PLAStochastic.Index.CEPS.Scaled.ComplexJetPair
import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound

/-! # Joint analyticity at padded finite vectors, Cauchy time-operator bounds, disc geometry

The factor and pair germs of `ComplexJetFactors`, `ComplexJetHalfFactors` and
`ComplexJetPair` are specialized to the padded parameter `(q, z, b)`. The time operator
is bounded by a Cauchy estimate on a frequency disc, and small discs around outer strip
points stay in a slightly larger outer strip.
-/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsComplexJetPad_fst_analyticOnNhd (d i : ℕ) :
    AnalyticOnNhd ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ => cepsComplexJetPad d v.1 i) univ :=
  fun v _ => (cepsComplexJetPad_analyticAt d i v.1).comp analyticAt_fst

theorem cepsStrip_analyticOnNhd_freq (d : ℕ) :
    AnalyticOnNhd ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ => v.2.1) univ :=
  fun _ _ => analyticAt_fst.comp analyticAt_snd

theorem cepsStrip_analyticOnNhd_scale (d : ℕ) :
    AnalyticOnNhd ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ => v.2.2) univ :=
  fun _ _ => analyticAt_snd.comp analyticAt_snd

theorem cepsStrip_analyticAt_slice {d : ℕ} (q : Fin d → ℂ) (b z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => ((q, w, b) : (Fin d → ℂ) × ℂ × ℂ)) z :=
  analyticAt_const.prod (analyticAt_id.prod analyticAt_const)

variable {d N : ℕ} {lam : ℝ} {q : Fin d → ℂ} {z b : ℂ}

theorem cepsComplexKernelFiniteFactors_joint_analyticAt
    (hc : CepsComplexJetRootChart (cepsComplexJetPad d q) lam z)
    (hden : cepsComplexKernelDenominatorJetModel (cepsComplexJetPad d q) N lam z b ≠ 0)
    (hquot : cepsComplexCumulantJetQuotient (cepsComplexJetPad d q) N lam z b (b * z) ≠ 0) :
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
        cepsComplexKernelBridgeJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2) (q, z, b) ∧
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
        cepsComplexKernelEntranceJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2) (q, z, b) :=
  cepsComplexKernelFiniteFactors_germ (U := univ) isOpen_univ (mem_univ _) N lam
    (p := fun v : (Fin d → ℂ) × ℂ × ℂ => cepsComplexJetPad d v.1)
    (b := fun v => v.2.2) (z := fun v => v.2.1)
    (cepsComplexJetPad_fst_analyticOnNhd d) (cepsStrip_analyticOnNhd_scale d)
    (cepsStrip_analyticOnNhd_freq d) hc hden hquot

theorem cepsComplexKernelHalfFactors_joint_analyticAt
    (hc : CepsComplexJetRootChart (cepsComplexJetPad d q) lam z)
    (hquot : cepsComplexCumulantJetQuotient (cepsComplexJetPad d q) N lam z b (b * z) ≠ 0)
    (hmark : b * z - cepsComplexCumulantRootModel (cepsComplexJetPad d q) N lam z (-1) N b ≠ 0) :
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
        cepsComplexKernelHalfEntranceJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2)
        (q, z, b) ∧
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
        cepsComplexKernelHalfBridgeJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2)
        (q, z, b) :=
  cepsComplexKernelHalfFactors_analyticAt (U := univ) isOpen_univ (mem_univ _) N lam
    (p := fun v : (Fin d → ℂ) × ℂ × ℂ => cepsComplexJetPad d v.1)
    (b := fun v => v.2.2) (z := fun v => v.2.1)
    (cepsComplexJetPad_fst_analyticOnNhd d) (cepsStrip_analyticOnNhd_scale d)
    (cepsStrip_analyticOnNhd_freq d) hc hquot hmark

theorem cepsComplexKernelPairJetModel_joint_analyticAt
    (hc : CepsComplexJetRootChart (cepsComplexJetPad d q) lam z)
    (hden : cepsComplexKernelDenominatorJetModel (cepsComplexJetPad d q) N lam z b ≠ 0)
    (hquot : cepsComplexCumulantJetQuotient (cepsComplexJetPad d q) N lam z b (b * z) ≠ 0)
    (hw : 1 + b * lam ≠ 0) :
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
        cepsComplexKernelPairJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2) (q, z, b) :=
  cepsComplexKernelPairJetModel_analyticAt (U := univ) isOpen_univ (mem_univ _) N lam
    (p := fun v : (Fin d → ℂ) × ℂ × ℂ => cepsComplexJetPad d v.1)
    (b := fun v => v.2.2) (z := fun v => v.2.1)
    (cepsComplexJetPad_fst_analyticOnNhd d) (cepsStrip_analyticOnNhd_scale d)
    (cepsStrip_analyticOnNhd_freq d _ (mem_univ _)) hc hden hquot hw

theorem cepsComplexKernelHalfPairJetModel_joint_analyticAt
    (hc : CepsComplexJetRootChart (cepsComplexJetPad d q) lam z)
    (hquot : cepsComplexCumulantJetQuotient (cepsComplexJetPad d q) N lam z b (b * z) ≠ 0)
    (hmark : b * z - cepsComplexCumulantRootModel (cepsComplexJetPad d q) N lam z (-1) N b ≠ 0)
    (hw : 1 + b * lam ≠ 0) :
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
        cepsComplexKernelHalfPairJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2) (q, z, b) :=
  cepsComplexKernelHalfPairJetModel_analyticAt (U := univ) isOpen_univ (mem_univ _) N lam
    (p := fun v : (Fin d → ℂ) × ℂ × ℂ => cepsComplexJetPad d v.1)
    (b := fun v => v.2.2) (z := fun v => v.2.1)
    (cepsComplexJetPad_fst_analyticOnNhd d) (cepsStrip_analyticOnNhd_scale d)
    (cepsStrip_analyticOnNhd_freq d _ (mem_univ _)) hc hquot hmark hw

/-- The subtracted pair is a genuine joint germ once the factor premises hold; the half-line
premises are needed only on the positive tail. -/
theorem cepsComplexKernelSubtractedPairJetModel_joint_analyticAt
    (hc : CepsComplexJetRootChart (cepsComplexJetPad d q) lam z)
    (hden : cepsComplexKernelDenominatorJetModel (cepsComplexJetPad d q) N lam z b ≠ 0)
    (hquot : cepsComplexCumulantJetQuotient (cepsComplexJetPad d q) N lam z b (b * z) ≠ 0)
    (hw : 1 + b * lam ≠ 0)
    (hmark : 1 ≤ lam →
      b * z - cepsComplexCumulantRootModel (cepsComplexJetPad d q) N lam z (-1) N b ≠ 0) :
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
        cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2)
        (q, z, b) := by
  have hP := cepsComplexKernelPairJetModel_joint_analyticAt hc hden hquot hw
  unfold cepsComplexKernelSubtractedPairJetModel
  by_cases hl : 1 ≤ lam
  · simp only [if_pos hl]
    exact hP.sub (cepsComplexKernelHalfPairJetModel_joint_analyticAt hc hquot (hmark hl) hw)
  · simpa only [if_neg hl, sub_zero] using hP

/-- Frequency slices of joint germs. -/
theorem cepsStrip_frequency_analyticAt {f : (Fin d → ℂ) × ℂ × ℂ → ℂ}
    (hf : AnalyticAt ℂ f (q, z, b)) : AnalyticAt ℂ (fun w : ℂ => f (q, w, b)) z :=
  hf.comp (f := fun w : ℂ => ((q, w, b) : (Fin d → ℂ) × ℂ × ℂ)) (cepsStrip_analyticAt_slice q b z)

/-- Cauchy bound for the complete time operator from a bound on a frequency disc. -/
theorem cepsStrip_timeOperator_norm_le {f : ℂ → ℂ} {z b w : ℂ} {ρ K : ℝ} (hρ : 0 < ρ)
    (hd : ∀ z' ∈ ball z ρ, DifferentiableAt ℂ f z') (hK : ∀ z' ∈ ball z ρ, ‖f z'‖ ≤ K)
    (hw : ‖w⁻¹‖ ≤ 2) (hb : ‖b‖ ≤ 1 / 2) :
    ‖-(1 / w) * deriv f z - b * f z‖ ≤ (4 / ρ + 1) * K := by
  have hzb : z ∈ ball z ρ := mem_ball_self hρ
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK z hzb)
  have hD := norm_iteratedDeriv_le_of_ball 1 hρ
    (fun z' hz' => (hd z' hz').differentiableWithinAt) hK
  rw [iteratedDeriv_one] at hD
  have hD' : ‖deriv f z‖ ≤ 2 * K / ρ := by
    convert hD using 1
    simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one]
    field_simp
  calc
    ‖-(1 / w) * deriv f z - b * f z‖ ≤ ‖-(1 / w) * deriv f z‖ + ‖b * f z‖ := norm_sub_le _ _
    _ = ‖w⁻¹‖ * ‖deriv f z‖ + ‖b‖ * ‖f z‖ := by
      rw [norm_mul, norm_mul, norm_neg, one_div]
    _ ≤ 2 * (2 * K / ρ) + 1 / 2 * K :=
      add_le_add (mul_le_mul hw hD' (norm_nonneg _) (by norm_num))
        (mul_le_mul hb (hK z hzb) (norm_nonneg _) (by norm_num))
    _ ≤ (4 / ρ + 1) * K := by
      have : 2 * (2 * K / ρ) = 4 / ρ * K := by ring
      nlinarith

theorem cepsStrip_sqrt_norm_sub_le {z z' : ℂ} {ρ : ℝ} (hρ1 : ρ ≤ 1) (hzz : ‖z' - z‖ < ρ) :
    Real.sqrt ‖z'‖ ≤ Real.sqrt ‖z‖ + 1 := by
  have h1 : ‖z'‖ ≤ ‖z‖ + 1 := by
    have := norm_sub_norm_le z' z
    linarith
  calc
    Real.sqrt ‖z'‖ ≤ Real.sqrt (‖z‖ + 1) := Real.sqrt_le_sqrt h1
    _ ≤ Real.sqrt ‖z‖ + 1 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [Real.sq_sqrt (norm_nonneg z), Real.sqrt_nonneg ‖z‖]

/-- Small discs around outer strip points stay in a slightly larger outer strip. -/
theorem cepsStrip_disc_geometry {F₀ ρ : ℝ} (hF₀ : 0 < F₀) (hρ1 : ρ ≤ 1)
    (hρF : ρ ≤ F₀ ^ 2 / 8) {lam : ℝ} {z z' : ℂ}
    (hF : F₀ ≤ |lam| + Real.sqrt ‖z‖) (hzz : ‖z' - z‖ < ρ) :
    z.re - ρ ≤ z'.re ∧ F₀ / 4 ≤ |lam| + Real.sqrt ‖z'‖ ∧
      |lam| + Real.sqrt ‖z‖ ≤ |lam| + Real.sqrt ‖z'‖ + 1 ∧
      |lam| + Real.sqrt ‖z'‖ ≤ |lam| + Real.sqrt ‖z‖ + 1 := by
  have hre : z.re - ρ ≤ z'.re := by
    have h := abs_re_le_norm (z' - z)
    rw [sub_re] at h
    have := neg_abs_le (z'.re - z.re)
    linarith
  have hup := cepsStrip_sqrt_norm_sub_le hρ1 hzz
  have hdown := cepsStrip_sqrt_norm_sub_le (z := z') (z' := z) hρ1 (by rwa [norm_sub_rev])
  refine ⟨hre, ?_, by linarith, by linarith⟩
  by_cases hl : F₀ / 4 ≤ |lam|
  · linarith [Real.sqrt_nonneg ‖z'‖]
  · have hs : 3 * F₀ / 4 ≤ Real.sqrt ‖z‖ := by linarith
    have hz2 : (3 * F₀ / 4) ^ 2 ≤ ‖z‖ := by
      have := pow_le_pow_left₀ (by positivity) hs 2
      rwa [Real.sq_sqrt (norm_nonneg _)] at this
    have hz' : (F₀ / 4) ^ 2 ≤ ‖z'‖ := by
      have := norm_sub_norm_le z z'
      rw [norm_sub_rev] at this
      nlinarith
    have : F₀ / 4 ≤ Real.sqrt ‖z'‖ := (Real.le_sqrt (by positivity) (norm_nonneg _)).mpr hz'
    linarith [abs_nonneg lam]

end PGM
