import PLAStochastic.Index.CEPS.Scaled.KernelDiscountJets
import PLAStochastic.Index.CEPS.Scaled.ComplexJetQuotientBudget

/-! # The complex finite-jet marked discount

The marked discount is minus the finite cumulant spatial unit at zero drift and marker
`b z`. It is entire in the finite coordinates, the frequency and the scale, restricts to the
real-vector model `cepsKernelMarkedDiscountJetModel`, and grows at most linearly in `‖z‖` on
the scale window `‖b‖ (1 + √‖z‖) ≤ 1`.
-/

noncomputable section
open Complex Set Metric
namespace PGM

def cepsComplexKernelMarkedDiscountJetModel (p : ℕ → ℂ) (N : ℕ) (z b : ℂ) : ℂ :=
  -cepsComplexCumulantQuotientSpatialUnit p N 0 z b (b * z)

theorem cepsComplexKernelMarkedDiscountJetModel_real (p : ℕ → ℝ) (N : ℕ) (z b : ℂ) :
    cepsComplexKernelMarkedDiscountJetModel (fun i => (p i : ℂ)) N z b =
      cepsKernelMarkedDiscountJetModel p N z b := rfl

/-- The quadratic exponential unit grows like its argument up to `exp (‖b‖² ‖T‖)`. -/
theorem quadraticExpUnit_norm_le (b T : ℂ) :
    ‖quadraticExpUnit b T‖ ≤ Real.exp (‖b‖ ^ 2 * ‖T‖) * ‖T‖ := by
  have h0 : quadraticExpUnit b 0 = 0 := by simp [quadraticExpUnit]
  have h := (convex_closedBall (0 : ℂ) ‖T‖).norm_image_sub_le_of_norm_deriv_le
    (f := quadraticExpUnit b) (C := Real.exp (‖b‖ ^ 2 * ‖T‖))
    (fun w _ => (quadraticExpUnit_hasDerivAt b w).differentiableAt) ?_
    (mem_closedBall_self (norm_nonneg T)) (mem_closedBall_zero_iff.mpr le_rfl)
  · rw [h0, sub_zero, sub_zero] at h
    exact h
  · intro w hw
    rw [(quadraticExpUnit_hasDerivAt b w).deriv, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    calc
      (b ^ 2 * w).re ≤ ‖b ^ 2 * w‖ := re_le_norm _
      _ = ‖b‖ ^ 2 * ‖w‖ := by rw [norm_mul, norm_pow]
      _ ≤ ‖b‖ ^ 2 * ‖T‖ :=
        mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hw) (by positivity)

theorem cepsComplexKernelMarkedDiscountJetModel_eq (p : ℕ → ℂ) (N : ℕ) (z b : ℂ) :
    cepsComplexKernelMarkedDiscountJetModel p N z b =
      -quadraticExpUnit b ((b * z) ^ 2 * cepsCgfComplexJetPolynomial p N (b * (b * z)) - z) := by
  unfold cepsComplexKernelMarkedDiscountJetModel cepsComplexCumulantQuotientSpatialUnit
    cepsComplexCumulantQuadraticEquation
  simp only [ofReal_zero, zero_mul, mul_zero, add_zero, mul_one]

/-- **(S3)** Joint analyticity and polynomial frequency growth of the marked discount. -/
theorem cepsComplexKernelMarkedDiscount_budget (d N : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ δb K : ℝ, ∃ e : ℕ, 0 < δb ∧ ∀ q : Fin d → ℂ, ‖q‖ ≤ M → ∀ z b : ℂ,
      ‖b‖ * (1 + Real.sqrt ‖z‖) ≤ δb →
        AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
            cepsComplexKernelMarkedDiscountJetModel (cepsComplexJetPad d v.1) N v.2.1 v.2.2)
            (q, z, b) ∧
        ‖cepsComplexKernelMarkedDiscountJetModel (cepsComplexJetPad d q) N z b‖ ≤
          K * (1 + ‖z‖) ^ e := by
  let L := ((N : ℝ) + 1) * M + 1
  have hL : 0 ≤ L := by positivity
  refine ⟨1, Real.exp L * L, 1, one_pos, ?_⟩
  intro q hq z b hb
  constructor
  · -- genuine joint analyticity
    let x : (Fin d → ℂ) × ℂ × ℂ := (q, z, b)
    have hp : ∀ i, AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ => cepsComplexJetPad d v.1 i) x :=
      fun i => (cepsComplexJetPad_analyticAt d i q).comp (f := Prod.fst) (x := x) analyticAt_fst
    have hbA : AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ => v.2.2) x :=
      analyticAt_snd.comp analyticAt_snd
    have hzA : AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ => v.2.1) x :=
      analyticAt_fst.comp analyticAt_snd
    have hT : AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
        (v.2.2 * v.2.1) ^ 2 * cepsCgfComplexJetPolynomial (cepsComplexJetPad d v.1) N
          (v.2.2 * (v.2.2 * v.2.1)) - v.2.1) x :=
      (((hbA.mul hzA).pow 2).mul
        (cepsCgfComplexJetPolynomial_analyticAt hp (hbA.mul (hbA.mul hzA)) N)).sub hzA
    have hU := ((quadraticExpUnit_joint_analyticAt _).comp (hbA.prod hT)).neg
    simp only [cepsComplexKernelMarkedDiscountJetModel_eq]
    exact hU
  · -- polynomial growth
    let P := cepsComplexJetPad d q
    have hpκ : ∀ j ≤ N, ‖P (cepsJetCode (.inl j))‖ ≤ M :=
      fun j _ => cepsComplexJetPad_norm_le hM hq _
    have hbs : ‖b‖ * Real.sqrt ‖z‖ ≤ 1 := by
      have : ‖b‖ * Real.sqrt ‖z‖ ≤ ‖b‖ * (1 + Real.sqrt ‖z‖) :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      linarith
    have hb2z : ‖b‖ ^ 2 * ‖z‖ ≤ 1 := by
      have h := pow_le_pow_left₀ (by positivity) hbs 2
      rw [mul_pow, Real.sq_sqrt (norm_nonneg z)] at h
      linarith
    have hs : ‖b * (b * z)‖ ≤ 1 := by
      rw [norm_mul, norm_mul]
      nlinarith [norm_nonneg b, norm_nonneg z]
    have hP := cepsCgfComplexJetPolynomial_norm_le N hM hpκ hs
    have hbz2 : ‖(b * z) ^ 2‖ ≤ ‖z‖ := by
      rw [norm_pow, norm_mul, mul_pow]
      have hz0 := norm_nonneg z
      nlinarith
    let T := (b * z) ^ 2 * cepsCgfComplexJetPolynomial P N (b * (b * z)) - z
    have hT : ‖T‖ ≤ L * ‖z‖ := by
      calc
        ‖T‖ ≤ ‖(b * z) ^ 2 * cepsCgfComplexJetPolynomial P N (b * (b * z))‖ + ‖z‖ :=
          norm_sub_le _ _
        _ ≤ ‖z‖ * (((N : ℝ) + 1) * M) + ‖z‖ := by
          rw [norm_mul]
          gcongr
        _ = L * ‖z‖ := by dsimp only [L]; ring
    have hbT : ‖b‖ ^ 2 * ‖T‖ ≤ L := by
      calc
        ‖b‖ ^ 2 * ‖T‖ ≤ ‖b‖ ^ 2 * (L * ‖z‖) := mul_le_mul_of_nonneg_left hT (by positivity)
        _ = L * (‖b‖ ^ 2 * ‖z‖) := by ring
        _ ≤ L * 1 := mul_le_mul_of_nonneg_left hb2z hL
        _ = L := mul_one L
    rw [cepsComplexKernelMarkedDiscountJetModel_eq, norm_neg]
    calc
      _ ≤ Real.exp (‖b‖ ^ 2 * ‖T‖) * ‖T‖ := quadraticExpUnit_norm_le b T
      _ ≤ Real.exp L * (L * ‖z‖) :=
        mul_le_mul (Real.exp_le_exp.mpr hbT) hT (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp L * L * (1 + ‖z‖) ^ 1 := by
        rw [pow_one, mul_assoc]
        gcongr
        linarith

end PGM
