import PLAStochastic.ForMathlib.Probability.Hellinger.ExponentialTransport
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# An inverse-scale Hellinger budget for the actual exponential transport

Linear Jacobian error and quadratic displacement, both of inverse scale order,
give an inverse scale Hellinger bound. The proof integrates the actual root
densities with a polynomial times exponential envelope.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set

def exponentialTransportIntegral (a : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), (t ^ 2 / 2 + t) ^ 2 * Real.exp (-a * t)

theorem exponential_transport_polynomial_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => (t ^ 2 / 2 + t) ^ 2 * Real.exp (-a * t))
      (Ioi 0) volume := by
  have hi (k : ℕ) : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-a * t)) (Ioi 0) volume := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (k : ℝ)) (p := 1) (b := a) (by linarith [Nat.cast_nonneg (α := ℝ) k]) one_pos ha
    simpa only [Real.rpow_one, Real.rpow_natCast] using h
  apply Integrable.congr ((((hi 4).div_const 4).add (hi 3)).add (hi 2))
  exact ae_of_all _ fun t => by dsimp; ring

theorem exponentialTransportIntegral_nonneg (a : ℝ) : 0 ≤ exponentialTransportIntegral a :=
  integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem hellinger_positiveExp_pullback_le (e : ℝ ≃o ℝ) (d : ℝ → ℝ)
    (hd : ∀ t, HasDerivAt e (d t) t) (hdm : Measurable d) (hdpos : ∀ t, 0 < d t)
    (he0 : e 0 = 0) {a B n : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 ≤ B) (hn : 0 < n)
    (helow : ∀ t, 0 ≤ t → a * t ≤ e t)
    (hediff : ∀ t, 0 ≤ t → |e t - t| ≤ B * t ^ 2 / n)
    (hddiff : ∀ t, 0 ≤ t → |d t - 1| ≤ B * t / n) :
    positiveExpDensity.hellinger (positiveExpDensity.pullbackOrderIso e d hd hdm hdpos) ≤
      B * Real.sqrt (exponentialTransportIntegral a) / n := by
  let p := positiveExpDensity
  let q := p.pullbackOrderIso e d hd hdm hdpos
  let F : ℝ → ℝ := (Ioi (0 : ℝ)).indicator
    (fun t => (t ^ 2 / 2 + t) ^ 2 * Real.exp (-a * t))
  have hiF : Integrable F volume :=
    (exponential_transport_polynomial_integrable ha).integrable_indicator measurableSet_Ioi
  have hb (t : ℝ) : (Real.sqrt (p.density t) - Real.sqrt (q.density t)) ^ 2 ≤
      (B / n) ^ 2 * F t := by
    by_cases ht : 0 < t
    · have het : 0 < e t := by simpa only [he0] using e.strictMono ht
      have hsqexp : Real.exp (-(a * t) / 2) ^ 2 = Real.exp (-a * t) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      have hdiff := exponential_jacobian_root_difference_le (hdpos t).le
        (show a * t ≤ t from by nlinarith only [ha1, ht])
        (helow t ht.le)
      have hcoef : |t - e t| / 2 + |d t - 1| ≤ (B / n) * (t ^ 2 / 2 + t) := by
        rw [abs_sub_comm t (e t)]
        calc
          _ ≤ (B * t ^ 2 / n) / 2 + B * t / n :=
            add_le_add (div_le_div_of_nonneg_right (hediff t ht.le) (by norm_num))
              (hddiff t ht.le)
          _ = _ := by ring
      have hroot := hdiff.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)
      change (Real.sqrt ((Ioi (0 : ℝ)).indicator (fun t => Real.exp (-t)) t) -
        Real.sqrt (d t * (Ioi (0 : ℝ)).indicator (fun t => Real.exp (-t)) (e t))) ^ 2 ≤ _
      dsimp only [F]
      rw [indicator_of_mem (s := Ioi (0 : ℝ)) ht,
        indicator_of_mem (s := Ioi (0 : ℝ)) het, Real.sqrt_mul (hdpos t).le,
        ← Real.exp_half, ← Real.exp_half, indicator_of_mem (s := Ioi (0 : ℝ)) ht]
      have hs := pow_le_pow_left₀ (abs_nonneg _) hroot 2
      rw [sq_abs, mul_pow, mul_pow, hsqexp] at hs
      simpa only [mul_assoc] using hs
    · have het : e t ≤ 0 := by
        simpa only [he0] using e.monotone (not_lt.mp ht)
      have hpzero : p.density t = 0 := positiveExpDensity_nonpos (not_lt.mp ht)
      have hqzero : q.density t = 0 := by
        change d t * p.density (e t) = 0
        rw [positiveExpDensity_nonpos het, mul_zero]
      rw [hpzero, hqzero, Real.sqrt_zero, sub_self, zero_pow two_ne_zero]
      simp only [F, indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht), mul_zero]
      exact le_rfl
  have hsq : p.hellinger q ^ 2 ≤ (B / n) ^ 2 * exponentialTransportIntegral a := by
    rw [p.hellinger_sq q]
    apply (integral_mono (p.sqrt_memLp.sub q.sqrt_memLp).integrable_sq
      (hiF.const_mul ((B / n) ^ 2)) hb).trans_eq
    dsimp only [F]
    rw [integral_const_mul, integral_indicator measurableSet_Ioi]
    rfl
  have hI := exponentialTransportIntegral_nonneg a
  have hs := Real.sq_sqrt hI
  have he : (B * Real.sqrt (exponentialTransportIntegral a) / n) ^ 2 =
      (B / n) ^ 2 * exponentialTransportIntegral a := by
    rw [div_pow, mul_pow, hs]
    ring
  have hC : 0 ≤ B * Real.sqrt (exponentialTransportIntegral a) / n := by positivity
  nlinarith only [hsq, he, hC, p.hellinger_nonneg q]

end

end ProbabilityTheory
