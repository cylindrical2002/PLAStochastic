import PLAStochastic.ForMathlib.MeasureTheory.Constructions.PiFactor
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Negative moments of sums of iid positive variables

For iid positive coordinates with a bounded density, `E (X₁ + ⋯ + X_N)^{-a} ≤ N^{-a} e^{8Da}`
once `N ≥ 4a` (`research/2026-09-29-ceps-full-expansion/smoothing.md` (S8)). Instead of the
Laplace three-range estimate of the source, the proof uses AM–GM,
`(∑ xᵢ)^{-a} ≤ N^{-a} ∏ xᵢ^{-a/N}`, independence, and the one-variable bound
`E X^{-q} ≤ 1 + 8 D q` for `0 ≤ q ≤ 1/4`.

* `rpow_neg_le_one_add`: `x^{-q} ≤ 1 + 2 q x^{-3/4}` on `(0, 1)`.
* `lintegral_rpow_neg_le_of_density`: `∫⁻ x^{-q} dν ≤ 1 + 8 D q` for a density `f ≤ D`.
* `lintegral_sum_rpow_neg_le`: the product bound over any index set `S` of the coordinates.
-/

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal

namespace PGM

/-- `x^{-q} ≤ 1 + 2 q x^{-3/4}` for `0 < x < 1` and `0 ≤ q ≤ 1/4`. -/
theorem rpow_neg_le_one_add {x q : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hq0 : 0 ≤ q)
    (hq : q ≤ 1 / 4) : x ^ (-q) ≤ 1 + 2 * q * x ^ (-(3 / 4 : ℝ)) := by
  set y := -Real.log x with hy
  have hy0 : 0 < y := by rw [hy]; linarith [Real.log_neg hx0 hx1]
  have hxq : x ^ (-q) = Real.exp (q * y) := by
    rw [Real.rpow_def_of_pos hx0, hy]; ring_nf
  have h1 : Real.exp (q * y) ≤ 1 + q * y * Real.exp (q * y) := by
    have := Real.add_one_le_exp (-(q * y))
    have he : Real.exp (-(q * y)) * Real.exp (q * y) = 1 := by
      rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos (q * y)
    nlinarith
  have h2 : Real.exp (q * y) ≤ x ^ (-(1 / 4 : ℝ)) := by
    rw [← hxq]
    exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1.le (by linarith)
  have h3 : y ≤ 2 * x ^ (-(1 / 2 : ℝ)) := by
    have hpos : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
    have := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_rpow hx0] at this
    rw [hy]; linarith
  have h4 : x ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 4 : ℝ)) = x ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_add hx0]; norm_num
  have hqy : q * y * Real.exp (q * y) ≤ q * (2 * x ^ (-(1 / 2 : ℝ))) * x ^ (-(1 / 4 : ℝ)) := by
    have hy' : q * y ≤ q * (2 * x ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left h3 hq0
    have hpos : 0 ≤ q * y := mul_nonneg hq0 hy0.le
    calc q * y * Real.exp (q * y) ≤ q * (2 * x ^ (-(1 / 2 : ℝ))) * Real.exp (q * y) :=
          mul_le_mul_of_nonneg_right hy' (Real.exp_pos _).le
      _ ≤ q * (2 * x ^ (-(1 / 2 : ℝ))) * x ^ (-(1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [hxq]
  calc Real.exp (q * y) ≤ 1 + q * y * Real.exp (q * y) := h1
    _ ≤ 1 + q * (2 * x ^ (-(1 / 2 : ℝ))) * x ^ (-(1 / 4 : ℝ)) := by linarith
    _ = 1 + 2 * q * x ^ (-(3 / 4 : ℝ)) := by rw [← h4]; ring

/-- `∫_0^1 x^{-3/4} dx = 4`. -/
theorem lintegral_Ioo_rpow_neg_three_quarters :
    ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x ^ (-(3 / 4 : ℝ))) = 4 := by
  have hint : IntervalIntegrable (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hI : IntegrableOn (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hint
  have hval : ∫ x in Ioc (0 : ℝ) 1, x ^ (-(3 / 4 : ℝ)) = 4 := by
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by norm_num))]
    norm_num
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm, ← ofReal_integral_eq_lintegral_ofReal hI]
  · rw [hval]; simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact Real.rpow_nonneg hx.1.le _

/-- `∫⁻ x^{-q} dν ≤ 1 + 8 D q` for a law on `(0, ∞)` with density at most `D`. -/
theorem lintegral_rpow_neg_le_of_density {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} (hfm : Measurable f) {D : ℝ} (hD : 0 ≤ D)
    (hν : ν = volume.withDensity fun x => ENNReal.ofReal (f x)) (hf : ∀ x, f x ≤ D)
    (hν0 : ν (Iic 0) = 0) {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4) :
    ∫⁻ x, ENNReal.ofReal (x ^ (-q)) ∂ν ≤ ENNReal.ofReal (1 + 8 * D * q) := by
  have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal (x ^ (-q)) ≤
      1 + ENNReal.ofReal (2 * q) *
        (Ioo (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (x ^ (-(3 / 4 : ℝ)))) x := by
    have hae : ∀ᵐ x ∂ν, 0 < x := by
      rw [ae_iff]
      have : {a : ℝ | ¬ 0 < a} = Set.Iic 0 := by ext; simp
      rw [this]; exact hν0
    filter_upwards [hae] with x hx
    by_cases hx1 : x < 1
    · rw [indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from ⟨hx, hx1⟩),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add zero_le_one (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by
        have := rpow_neg_le_one_add hx hx1 hq0 hq; linarith)
    · rw [indicator_of_notMem (show x ∉ Ioo (0 : ℝ) 1 from fun h => hx1 h.2), mul_zero,
        add_zero]
      refine ENNReal.ofReal_le_one.mpr ?_
      exact Real.rpow_le_one_of_one_le_of_nonpos (not_lt.mp hx1) (by linarith)
  have hmeas : Measurable fun x : ℝ =>
      (Ioo (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (x ^ (-(3 / 4 : ℝ)))) x :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).indicator measurableSet_Ioo
  calc ∫⁻ x, ENNReal.ofReal (x ^ (-q)) ∂ν
      ≤ ∫⁻ x, 1 + ENNReal.ofReal (2 * q) *
          (Ioo (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (x ^ (-(3 / 4 : ℝ)))) x ∂ν :=
        lintegral_mono_ae hpt
    _ = 1 + ENNReal.ofReal (2 * q) * ∫⁻ x,
          (Ioo (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (x ^ (-(3 / 4 : ℝ)))) x ∂ν := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ hmeas]
    _ ≤ 1 + ENNReal.ofReal (2 * q) * (ENNReal.ofReal D * 4) := by
        gcongr
        rw [hν, lintegral_withDensity_eq_lintegral_mul _ hfm.ennreal_ofReal hmeas,
          ← lintegral_Ioo_rpow_neg_three_quarters, ← lintegral_indicator measurableSet_Ioo,
          ← lintegral_const_mul _ hmeas]
        refine lintegral_mono fun x => ?_
        simp only [Pi.mul_apply]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hf x)) _
    _ = ENNReal.ofReal (1 + 8 * D * q) := by
        rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul hD, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
        congr 1
        ring

/-- **Negative moments of a sum of iid positive coordinates.** If `∫⁻ x^{-q} dν ≤ 1 + Bq`
for `0 ≤ q ≤ 1/4`, then `E (∑_{i ∈ S} Xᵢ)^{-a} ≤ |S|^{-a} e^{Ba}` once `|S| ≥ 4a`. -/
theorem lintegral_sum_rpow_neg_le {n : ℕ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν0 : ν (Iic 0) = 0) {B : ℝ} (hB : 0 ≤ B)
    (hνq : ∀ q : ℝ, 0 ≤ q → q ≤ 1 / 4 →
      ∫⁻ x, ENNReal.ofReal (x ^ (-q)) ∂ν ≤ ENNReal.ofReal (1 + B * q))
    (S : Finset (Fin n)) (hS : S.Nonempty) {a : ℝ} (ha : 0 ≤ a) (hN : 4 * a ≤ S.card) :
    ∫⁻ x, ENNReal.ofReal ((∑ i ∈ S, x i) ^ (-a)) ∂(Measure.pi fun _ => ν) ≤
      ENNReal.ofReal ((S.card : ℝ) ^ (-a) * Real.exp (B * a)) := by
  classical
  set N : ℝ := (S.card : ℝ) with hNdef
  have hN0 : 0 < N := by rw [hNdef]; exact_mod_cast hS.card_pos
  set q : ℝ := a / N with hqdef
  have hq0 : 0 ≤ q := div_nonneg ha hN0.le
  have hq : q ≤ 1 / 4 := by rw [hqdef, div_le_iff₀ hN0]; linarith
  have hpos : ∀ᵐ x ∂(Measure.pi fun _ : Fin n => ν), ∀ i, 0 < x i := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    have : {x : Fin n → ℝ | ¬ 0 < x i} = Function.eval i ⁻¹' Iic 0 := by
      ext x; simp [not_lt]
    rw [this]
    exact Measure.pi_eval_preimage_null _ hν0
  set g : Fin n → ℝ → ℝ≥0∞ := fun i x => if i ∈ S then ENNReal.ofReal (x ^ (-q)) else 1 with hg
  have hgm : ∀ i, Measurable (g i) := by
    intro i
    simp only [hg]
    split_ifs
    · exact ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
    · exact measurable_const
  have hpt : ∀ᵐ x ∂(Measure.pi fun _ : Fin n => ν),
      ENNReal.ofReal ((∑ i ∈ S, x i) ^ (-a)) ≤
        ENNReal.ofReal (N ^ (-a)) * ∏ i, g i (x i) := by
    filter_upwards [hpos] with x hx
    have hamgm := Real.geom_mean_le_arith_mean_weighted S (fun _ => 1 / N) x
      (fun _ _ => by positivity) (by rw [Finset.sum_const, nsmul_eq_mul, hNdef]; field_simp)
      (fun i _ => (hx i).le)
    have hprod_pos : 0 < ∏ i ∈ S, x i ^ (1 / N) :=
      Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _
    have hsum : ∑ i ∈ S, 1 / N * x i = (∑ i ∈ S, x i) / N := by
      rw [← Finset.mul_sum]; ring
    rw [hsum] at hamgm
    have hle : N * ∏ i ∈ S, x i ^ (1 / N) ≤ ∑ i ∈ S, x i := by
      rw [le_div_iff₀ hN0] at hamgm; linarith
    have h1 : (∑ i ∈ S, x i) ^ (-a) ≤ (N * ∏ i ∈ S, x i ^ (1 / N)) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
    have h2 : (N * ∏ i ∈ S, x i ^ (1 / N)) ^ (-a) = N ^ (-a) * ∏ i ∈ S, x i ^ (-q) := by
      rw [Real.mul_rpow hN0.le hprod_pos.le, ← Real.finsetProd_rpow S _
        (fun i _ => (Real.rpow_pos_of_pos (hx i) _).le)]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Real.rpow_mul (hx i).le, hqdef]
      congr 1
      field_simp
    have h3 : ∏ i, g i (x i) = ENNReal.ofReal (∏ i ∈ S, x i ^ (-q)) := by
      rw [ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.rpow_pos_of_pos (hx i) _).le]
      simp only [hg]
      rw [Finset.prod_ite_mem, Finset.univ_inter]
    rw [h3, ← ENNReal.ofReal_mul (Real.rpow_nonneg hN0.le _)]
    exact ENNReal.ofReal_le_ofReal (h1.trans h2.le)
  calc ∫⁻ x, ENNReal.ofReal ((∑ i ∈ S, x i) ^ (-a)) ∂(Measure.pi fun _ => ν)
      ≤ ∫⁻ x, ENNReal.ofReal (N ^ (-a)) * ∏ i, g i (x i) ∂(Measure.pi fun _ => ν) :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (N ^ (-a)) * ∏ i, ∫⁻ y, g i y ∂ν := by
        rw [lintegral_const_mul _ (Finset.measurable_fun_prod
          (f := fun i (x : Fin n → ℝ) => g i (x i)) _ fun i _ =>
          (hgm i).comp (measurable_pi_apply i)), lintegral_fin_pi_prod _ g hgm]
    _ ≤ ENNReal.ofReal (N ^ (-a)) * ∏ i, (if i ∈ S then ENNReal.ofReal (1 + B * q) else 1) := by
        gcongr with i
        simp only [hg]
        split_ifs
        · exact hνq q hq0 hq
        · simp
    _ = ENNReal.ofReal (N ^ (-a)) * ENNReal.ofReal ((1 + B * q) ^ S.card) := by
        rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const,
          ENNReal.ofReal_pow (by positivity)]
    _ ≤ ENNReal.ofReal (N ^ (-a) * Real.exp (B * a)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hN0.le _)]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hN0.le _))
        have h1 : 1 + B * q ≤ Real.exp (B * q) := by linarith [Real.add_one_le_exp (B * q)]
        calc (1 + B * q) ^ S.card ≤ Real.exp (B * q) ^ S.card :=
              pow_le_pow_left₀ (by positivity) h1 _
          _ = Real.exp (B * a) := by
              rw [← Real.exp_nat_mul, hqdef, ← hNdef]
              congr 1
              field_simp

end PGM
