import PLAStochastic.Index.Model.GapLaw
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.HasLaw

/-!
# Exponential gaps

Moments of the standard exponential law `expMeasure 1` (density `exp (-x)` on `[0, ∞)`),
and the resulting `GapLaw` for an iid sequence of standard exponential gaps.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Real

namespace PGM

/-! ## Integrals against the standard exponential law -/

theorem toReal_exponentialPDF_one (x : ℝ) :
    (exponentialPDF 1 x).toReal = (Ici (0 : ℝ)).indicator (fun y => exp (-y)) x := by
  rw [exponentialPDF_eq]
  by_cases hx : 0 ≤ x
  · simp [hx, (exp_pos _).le]
  · simp [hx]

theorem expMeasure_one_eq_withDensity :
    expMeasure 1 = volume.withDensity (exponentialPDF 1) := rfl

theorem measurable_exponentialPDF_one : Measurable (exponentialPDF 1) :=
  (measurable_exponentialPDFReal 1).ennreal_ofReal

instance isProbabilityMeasure_expMeasure_one : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-- Integrals against `expMeasure 1` are integrals of `exp (-x) * f x` over `(0, ∞)`. -/
theorem integral_expMeasure_one (f : ℝ → ℝ) :
    ∫ x, f x ∂(expMeasure 1) = ∫ x in Ioi 0, exp (-x) * f x := by
  rw [expMeasure_one_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
    measurable_exponentialPDF_one (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [toReal_exponentialPDF_one, smul_eq_mul]
  have : (fun x => (Ici (0 : ℝ)).indicator (fun y => exp (-y)) x * f x) =
      (Ici (0 : ℝ)).indicator (fun y => exp (-y) * f y) := by
    ext x
    by_cases hx : x ∈ Ici (0 : ℝ) <;> simp [hx]
  rw [this, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

/-- Integrability against `expMeasure 1` is integrability of `exp (-x) * f x` on `(0, ∞)`. -/
theorem integrable_expMeasure_one_iff {f : ℝ → ℝ} :
    Integrable f (expMeasure 1) ↔ IntegrableOn (fun x => exp (-x) * f x) (Ioi 0) := by
  rw [expMeasure_one_eq_withDensity, integrable_withDensity_iff_integrable_smul'
    measurable_exponentialPDF_one (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [toReal_exponentialPDF_one, smul_eq_mul]
  have : (fun x => (Ici (0 : ℝ)).indicator (fun y => exp (-y)) x * f x) =
      (Ici (0 : ℝ)).indicator (fun y => exp (-y) * f y) := by
    ext x
    by_cases hx : x ∈ Ici (0 : ℝ) <;> simp [hx]
  rw [this, integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]

/-! ## Moments of the standard exponential law -/

theorem integral_exp_neg_mul_pow (n : ℕ) :
    ∫ x in Ioi 0, exp (-x) * x ^ n = n.factorial := by
  rw [← Gamma_nat_eq_factorial, Gamma_eq_integral (by positivity)]
  simp [← rpow_natCast]

theorem integrableOn_exp_neg_mul_pow (n : ℕ) :
    IntegrableOn (fun x : ℝ => exp (-x) * x ^ n) (Ioi 0) := by
  have h := GammaIntegral_convergent (s := n + 1) (by positivity)
  simpa [← rpow_natCast] using h

theorem integrable_pow_expMeasure_one (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (expMeasure 1) :=
  integrable_expMeasure_one_iff.mpr (integrableOn_exp_neg_mul_pow n)

theorem integral_pow_expMeasure_one (n : ℕ) :
    ∫ x, x ^ n ∂(expMeasure 1) = n.factorial := by
  rw [integral_expMeasure_one, integral_exp_neg_mul_pow]

theorem integral_id_expMeasure_one : ∫ x, x ∂(expMeasure 1) = 1 := by
  simpa using integral_pow_expMeasure_one 1

theorem integral_sub_one_sq_expMeasure_one : ∫ x, (x - 1) ^ 2 ∂(expMeasure 1) = 1 := by
  have h : (fun x : ℝ => (x - 1) ^ 2) = fun x => x ^ 2 - 2 * x ^ 1 + 1 := by
    ext x; ring
  have i2 := integrable_pow_expMeasure_one 2
  have i1 : Integrable (fun x : ℝ => 2 * x ^ 1) (expMeasure 1) :=
    (integrable_pow_expMeasure_one 1).const_mul 2
  have i21 : Integrable (fun x : ℝ => x ^ 2 - 2 * x ^ 1) (expMeasure 1) := i2.sub i1
  rw [h, integral_add i21 (integrable_const _), integral_sub i2 i1, integral_const_mul,
    integral_pow_expMeasure_one, integral_pow_expMeasure_one]
  simp

/-- The standard exponential law is concentrated on `(0, ∞)`. -/
theorem ae_pos_expMeasure_one : ∀ᵐ x ∂(expMeasure 1), 0 < x := by
  rw [expMeasure_one_eq_withDensity, ae_withDensity_iff measurable_exponentialPDF_one]
  have h0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [h0] with x hx hpdf
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · exact absurd (exponentialPDF_of_neg hneg) hpdf
  · exact hpos

theorem integral_abs_sub_one_pow_three_expMeasure_one_le :
    ∫ x, |x - 1| ^ 3 ∂(expMeasure 1) ≤ 16 := by
  have i3 := integrable_pow_expMeasure_one 3
  have i2 : Integrable (fun x : ℝ => 3 * x ^ 2) (expMeasure 1) :=
    (integrable_pow_expMeasure_one 2).const_mul 3
  have i1 : Integrable (fun x : ℝ => 3 * x ^ 1) (expMeasure 1) :=
    (integrable_pow_expMeasure_one 1).const_mul 3
  have i32 : Integrable (fun x : ℝ => x ^ 3 + 3 * x ^ 2) (expMeasure 1) := i3.add i2
  have i321 : Integrable (fun x : ℝ => x ^ 3 + 3 * x ^ 2 + 3 * x ^ 1) (expMeasure 1) :=
    i32.add i1
  have hint : Integrable (fun x : ℝ => x ^ 3 + 3 * x ^ 2 + 3 * x ^ 1 + 1) (expMeasure 1) :=
    i321.add (integrable_const _)
  have hle : ∫ x, |x - 1| ^ 3 ∂(expMeasure 1) ≤
      ∫ x, (x ^ 3 + 3 * x ^ 2 + 3 * x ^ 1 + 1) ∂(expMeasure 1) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hint ?_
    filter_upwards [ae_pos_expMeasure_one] with x hx
    have habs : |x - 1| ≤ x + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc |x - 1| ^ 3 ≤ (x + 1) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) habs 3
      _ = x ^ 3 + 3 * x ^ 2 + 3 * x ^ 1 + 1 := by ring
  have hval : ∫ x, (x ^ 3 + 3 * x ^ 2 + 3 * x ^ 1 + 1) ∂(expMeasure 1) = 16 := by
    rw [integral_add i321 (integrable_const _), integral_add i32 i1, integral_add i3 i2,
      integral_const_mul, integral_const_mul, integral_pow_expMeasure_one,
      integral_pow_expMeasure_one, integral_pow_expMeasure_one]
    simp [Nat.factorial]
    norm_num
  linarith

theorem memLp_id_three_expMeasure_one : MemLp id 3 (expMeasure 1) := by
  rw [← integrable_norm_rpow_iff aestronglyMeasurable_id (by norm_num) (by norm_num)]
  have h := (integrable_pow_expMeasure_one 3).norm
  simp only [norm_pow] at h
  convert h using 2 with x
  simp

/-! ## iid standard exponential gaps -/

section GapLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℕ → Ω → ℝ}

/-- Every gap of an iid sequence with standard exponential first gap is standard exponential. -/
theorem IIDSeq.hasLaw_expMeasure_one (hE : IIDSeq P E) (hlaw : HasLaw (E 0) (expMeasure 1) P)
    (t : ℕ) : HasLaw (E t) (expMeasure 1) P where
  aemeasurable := (hE.measurable t).aemeasurable
  map_eq := by rw [(hE.ident t).map_eq, hlaw.map_eq]

/-- iid standard exponential gaps satisfy `GapLaw` with `μ = σ = 1` and `κ = 16`. -/
theorem gapLaw_exp (hE : IIDSeq P E) (hlaw : HasLaw (E 0) (expMeasure 1) P) :
    GapLaw P E 1 1 16 where
  iid := hE
  memLp3 := (hlaw.map_eq ▸ memLp_id_three_expMeasure_one).comp_of_map hlaw.aemeasurable
  mean := hlaw.integral_eq.trans integral_id_expMeasure_one
  var := (hlaw.integral_comp (f := fun x => (x - 1) ^ 2) (by fun_prop)).trans
    (integral_sub_one_sq_expMeasure_one.trans (one_pow 2).symm)
  third := by
    have h := integral_abs_sub_one_pow_three_expMeasure_one_le
    rw [← hlaw.integral_comp (f := fun x => |x - 1| ^ 3) (by fun_prop)] at h
    exact h
  mu_pos := one_pos
  sigma_pos := one_pos

/-- iid standard exponential gaps are almost surely positive. -/
theorem IIDSeq.ae_pos_of_expMeasure_one (hE : IIDSeq P E)
    (hlaw : HasLaw (E 0) (expMeasure 1) P) (t : ℕ) : ∀ᵐ ω ∂P, 0 < E t ω :=
  ((hE.hasLaw_expMeasure_one hlaw t).ae_iff (p := fun x => 0 < x)
    (measurableSet_setOfPred.mp measurableSet_Ioi)).mpr ae_pos_expMeasure_one

end GapLaw

end PGM
