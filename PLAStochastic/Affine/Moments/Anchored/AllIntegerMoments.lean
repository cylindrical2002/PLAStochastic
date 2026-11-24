import PLAStochastic.Affine.Moments.Anchored.KingmanIdentification
import PLAStochastic.Affine.Moments.Anchored.OddZetaPolynomial
import PLAStochastic.Affine.Moments.Anchored.ContourIntegrand
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # Real substitutions connecting the actual gamma moment to the contour edges -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

private theorem image_upper_square :
    (fun x : ℝ => (x ^ 2 + 1) / 4) '' Ioi 0 = Ioi (1 / 4 : ℝ) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change 0 < x at hx
    have := sq_pos_of_pos hx
    change (1 / 4 : ℝ) < (x ^ 2 + 1) / 4
    nlinarith
  · intro hz
    have hp : 0 < 4 * z - 1 := by change 1 / 4 < z at hz; linarith
    refine ⟨Real.sqrt (4 * z - 1), Real.sqrt_pos.mpr hp, ?_⟩
    dsimp only
    rw [Real.sq_sqrt hp.le]
    ring

private theorem image_lower_square :
    (fun x : ℝ => (1 - x ^ 2) / 4) '' Ioo 0 1 = Ioo (0 : ℝ) (1 / 4) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change 0 < x ∧ x < 1 at hx
    change 0 < (1 - x ^ 2) / 4 ∧ (1 - x ^ 2) / 4 < 1 / 4
    have := sq_pos_of_pos hx.1
    constructor <;> nlinarith [sq_nonneg (x - 1)]
  · intro hz
    have hp : 0 < 1 - 4 * z := by have := hz.2; linarith
    have hsq := Real.sq_sqrt hp.le
    refine ⟨Real.sqrt (1 - 4 * z), ⟨Real.sqrt_pos.mpr hp, ?_⟩, ?_⟩
    · have h0 := Real.sqrt_nonneg (1 - 4 * z)
      have := hz.1
      nlinarith
    · dsimp only
      rw [hsq]
      ring

/-- The upper branch uses the actual hyperbolic form of the infinite-sum transform. -/
theorem kingmanLaplace_moment_upper {q : ℕ} (hq : 0 < q) :
    (∫ z in Ioi (1 / 4 : ℝ), z ^ (q - 1) * kingmanLaplace z) =
      Real.pi / (2 * (4 : ℝ) ^ q) *
        ∫ x in Ioi (0 : ℝ), x * (x ^ 2 + 1) ^ q / Real.cosh (Real.pi * x / 2) := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => (x ^ 2 + 1) / 4) (x / 2) x := by
    convert! (((hasDerivAt_id x).pow 2).add_const 1).div_const 4 using 1
    simp only [id_eq]
    ring
  have hinj : InjOn (fun x : ℝ => (x ^ 2 + 1) / 4) (Ioi 0) := by
    intro x hx y hy hxy
    dsimp only at hxy
    change 0 < x at hx
    change 0 < y at hy
    nlinarith
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x _ => (hd x).hasDerivWithinAt) hinj
    (fun z : ℝ => z ^ (q - 1) * kingmanLaplace z)
  rw [image_upper_square] at he
  rw [he, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change 0 < x at hx
  dsimp only
  simp only [smul_eq_mul, abs_of_pos (half_pos hx)]
  rw [kingmanLaplace_eq_cosh (by nlinarith [sq_nonneg x] : 1 / 4 ≤ (x ^ 2 + 1) / 4)]
  rw [show 4 * ((x ^ 2 + 1) / 4) - 1 = x ^ 2 by ring, Real.sqrt_sq hx.le]
  have hpow (a : ℝ) : a ^ (q - 1) * a = a ^ q := by rw [← pow_succ, Nat.sub_add_cancel hq]
  have hd' : Real.pi / 2 * x = Real.pi * x / 2 := by ring
  rw [hd']
  calc
    _ = Real.pi / 2 * x * ((x ^ 2 + 1) / 4) ^ q /
        Real.cosh (Real.pi * x / 2) := by rw [← hpow]; ring
    _ = _ := by rw [div_pow]; ring

/-- The lower branch avoids the removable endpoint by changing variables on open intervals. -/
theorem kingmanLaplace_moment_lower {q : ℕ} (hq : 0 < q) :
    (∫ z in Ioo (0 : ℝ) (1 / 4), z ^ (q - 1) * kingmanLaplace z) =
      Real.pi / (2 * (4 : ℝ) ^ q) *
        ∫ x in (0 : ℝ)..1, x * (1 - x ^ 2) ^ q / Real.cos (Real.pi * x / 2) := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => (1 - x ^ 2) / 4) (-x / 2) x := by
    convert! ((hasDerivAt_const x 1).sub ((hasDerivAt_id x).pow 2)).div_const 4 using 1
    simp only [id_eq]
    ring
  have hinj : InjOn (fun x : ℝ => (1 - x ^ 2) / 4) (Ioo 0 1) := by
    intro x hx y hy hxy
    dsimp only at hxy
    have hx0 := hx.1
    have hy0 := hy.1
    nlinarith
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun x _ => (hd x).hasDerivWithinAt) hinj
    (fun z : ℝ => z ^ (q - 1) * kingmanLaplace z)
  rw [image_lower_square] at he
  rw [he, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  change 0 < x ∧ x < 1 at hx
  dsimp only
  have ha : |-x / 2| = x / 2 := by rw [abs_div, abs_neg, abs_of_pos hx.1]; norm_num
  simp only [smul_eq_mul, ha]
  have hz : 0 < (1 - x ^ 2) / 4 := by nlinarith [sq_nonneg (x - 1)]
  rw [kingmanLaplace_eq_cos hz (by nlinarith [sq_nonneg x] : (1 - x ^ 2) / 4 ≤ 1 / 4)]
  rw [show 1 - 4 * ((1 - x ^ 2) / 4) = x ^ 2 by ring, Real.sqrt_sq hx.1.le]
  have hpow (a : ℝ) : a ^ (q - 1) * a = a ^ q := by rw [← pow_succ, Nat.sub_add_cancel hq]
  rw [show Real.pi / 2 * x = Real.pi * x / 2 by ring]
  calc
    _ = Real.pi / 2 * x * ((1 - x ^ 2) / 4) ^ q /
        Real.cos (Real.pi * x / 2) := by rw [← hpow]; ring
    _ = _ := by rw [div_pow]; ring

/-- Splitting and changing variables in the true transform gives the two contour edges. -/
theorem kingmanLaplace_moment_substitution {q : ℕ} (hq : 0 < q)
    (hi : IntegrableOn (fun z : ℝ => z ^ (q - 1) * kingmanLaplace z) (Ioi 0)) :
    (∫ z in Ioi (0 : ℝ), z ^ (q - 1) * kingmanLaplace z) =
      Real.pi / (2 * (4 : ℝ) ^ q) *
        ((∫ x in Ioi (0 : ℝ), x * (x ^ 2 + 1) ^ q / Real.cosh (Real.pi * x / 2)) +
          ∫ x in (0 : ℝ)..1, x * (1 - x ^ 2) ^ q / Real.cos (Real.pi * x / 2)) := by
  have hu : Ioc (0 : ℝ) (1 / 4) ∪ Ioi (1 / 4) = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro h
      by_cases hx : x ≤ 1 / 4
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (lt_of_not_ge hx)
  have hd : Disjoint (Ioc (0 : ℝ) (1 / 4)) (Ioi (1 / 4)) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact not_lt_of_ge hx.2 hy
  have hl : IntegrableOn (fun z : ℝ => z ^ (q - 1) * kingmanLaplace z) (Ioc 0 (1 / 4)) :=
    hi.mono_set (fun _ hx => hx.1)
  have hh : IntegrableOn (fun z : ℝ => z ^ (q - 1) * kingmanLaplace z) (Ioi (1 / 4)) :=
    hi.mono_set (Ioi_subset_Ioi (by norm_num))
  conv_lhs => rw [← hu]
  rw [setIntegral_union hd measurableSet_Ioi hl hh, integral_Ioc_eq_integral_Ioo,
    kingmanLaplace_moment_lower hq, kingmanLaplace_moment_upper hq]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The actual lifetime moment equals the fully evaluated polynomial integral. -/
theorem anchoredUnitLifetime_moment_eq_anchoredMomentIntegral (hB : IsBrownianReal B μ)
    {q : ℕ} (hq : 0 < q) :
    (∫ ω, anchoredUnitLifetime B ω ^ q ∂μ) = anchoredMomentIntegral q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hn : (q : ℝ) - 1 = ((q - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  have hm := anchoredUnitLifetime_moment_kingmanLaplace hB hqR
  simp only [hn, Real.rpow_natCast] at hm
  rw [hm.2, kingmanLaplace_moment_substitution hq hm.1,
    anchoredMomentContour_real_identity hq]
  unfold anchoredMomentIntegral anchoredMomentPolynomial
  have hp : (4 : ℝ) ^ q = (2 : ℝ) ^ q * (2 : ℝ) ^ q := by rw [← mul_pow]; norm_num
  rw [hp, pow_succ (2 : ℝ)]
  field_simp

/-- The first exact Brownian anchored moment in the main theorem. -/
theorem anchoredUnitLifetime_mean_zeta (hB : IsBrownianReal B μ) :
    (∫ ω, anchoredUnitLifetime B ω ∂μ) = 21 * (riemannZeta 3).re / Real.pi ^ 2 := by
  have h := anchoredUnitLifetime_moment_eq_anchoredMomentIntegral hB (by norm_num : 0 < 1)
  simpa only [pow_one, anchoredMomentIntegral_one] using h

theorem anchoredUnitLifetime_second_moment_zeta (hB : IsBrownianReal B μ) :
    (∫ ω, anchoredUnitLifetime B ω ^ 2 ∂μ) =
      930 * (riemannZeta 5).re / Real.pi ^ 4 - 14 * (riemannZeta 3).re / Real.pi ^ 2 := by
  rw [anchoredUnitLifetime_moment_eq_anchoredMomentIntegral hB (by norm_num : 0 < 2),
    anchoredMomentIntegral_two]

theorem anchoredUnitLifetime_third_moment_zeta (hB : IsBrownianReal B μ) :
    (∫ ω, anchoredUnitLifetime B ω ^ 3 ∂μ) =
      40005 * (riemannZeta 7).re / Real.pi ^ 6 - 930 * (riemannZeta 5).re / Real.pi ^ 4 := by
  rw [anchoredUnitLifetime_moment_eq_anchoredMomentIntegral hB (by norm_num : 0 < 3),
    anchoredMomentIntegral_three]

theorem anchoredUnitLifetime_fourth_moment_zeta (hB : IsBrownianReal B μ) :
    (∫ ω, anchoredUnitLifetime B ω ^ 4 ∂μ) =
      1931580 * (riemannZeta 9).re / Real.pi ^ 8 - 53340 * (riemannZeta 7).re / Real.pi ^ 6 +
        124 * (riemannZeta 5).re / Real.pi ^ 4 := by
  rw [anchoredUnitLifetime_moment_eq_anchoredMomentIntegral hB (by norm_num : 0 < 4),
    anchoredMomentIntegral_four]

end BrownianAffine
