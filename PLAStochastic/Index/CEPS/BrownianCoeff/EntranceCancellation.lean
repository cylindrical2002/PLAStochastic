import PLAStochastic.Index.CEPS.BrownianCoeff.EntranceBounds
import PLAStochastic.Index.CEPS.BrownianCoeff.PositiveRoot

/-!
# A removable entrance cancellation formula

An exponential average replaces the displayed division by the frequency. The
formula therefore remains exact at zero frequency on the positive-drift tail.
-/

noncomputable section

open Complex Set Filter Topology MeasureTheory

namespace PGM

def cepsBrownianExpAverage (x : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, Complex.exp (-x * t)

theorem cepsBrownianExpAverage_continuous : Continuous cepsBrownianExpAverage := by
  have hfun : Continuous (fun p : ℂ × ℝ => Complex.exp (-p.1 * p.2)) := by fun_prop
  have h := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun x : ℂ => fun t : ℝ => Complex.exp (-x * t)) hfun
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  change Continuous (fun x : ℂ => ∫ t in (0 : ℝ)..1, Complex.exp (-x * t))
  simpa only [intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc] using h

theorem cepsBrownianExpAverage_mul (x : ℂ) :
    x * cepsBrownianExpAverage x = 1 - Complex.exp (-x) := by
  have hd (t : ℝ) : HasDerivAt (fun r : ℝ => Complex.exp (-x * r))
      (-x * Complex.exp (-x * t)) t := by
    simpa [mul_comm] using hasDerivAt_comp_affine (b := 0) (u := -x)
      (Complex.hasDerivAt_exp (0 + t * -x))
  have hi : IntervalIntegrable (fun t : ℝ => -x * Complex.exp (-x * t)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [intervalIntegral.integral_const_mul] at h
  simpa [cepsBrownianExpAverage, neg_mul, eq_sub_iff_add_eq, add_comm] using
    (show x * (∫ t in (0 : ℝ)..1, Complex.exp (-x * t)) = 1 - Complex.exp (-x) by
      simpa only [ofReal_one, mul_one, ofReal_zero, mul_zero, Complex.exp_zero] using
        (show x * (∫ t in (0 : ℝ)..1, Complex.exp (-x * t)) =
          Complex.exp (-x * (0 : ℂ)) - Complex.exp (-x * (1 : ℂ)) by linear_combination -h))

theorem cepsBrownianExpAverage_norm {x : ℂ} (hx : 0 ≤ x.re) :
    ‖cepsBrownianExpAverage x‖ ≤ 1 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => Complex.exp (-x * t)) (C := 1) ?_
  · simpa [cepsBrownianExpAverage] using h
  · intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    rw [Complex.norm_exp]
    have hre : (-x * (t : ℂ)).re = -x.re * t := by simp
    rw [hre]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht.1.le)

theorem cepsBrownianEntranceIntegral_cancellation (a s : ℂ) :
    (s + a) * cepsBrownianEntranceIntegral a (s ^ 2) =
      cepsBrownianSinhc (s ^ 2) - Complex.exp (-a) * cepsBrownianExpAverage (s - a) := by
  have hoff (s : ℂ) (hs : s ≠ a) :
      (s + a) * cepsBrownianEntranceIntegral a (s ^ 2) =
        cepsBrownianSinhc (s ^ 2) - Complex.exp (-a) * cepsBrownianExpAverage (s - a) := by
    have hI := cepsBrownianEntranceIntegral_mul a (s ^ 2)
    have hJ := cepsBrownianExpAverage_mul (s - a)
    have hC := cepsBrownianCosh_sub_mul_sinhc s
    have he : Complex.exp (-a) * Complex.exp (-(s - a)) = Complex.exp (-s) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    apply mul_left_cancel₀ (sub_ne_zero.mpr hs)
    linear_combination hI + hC + Complex.exp (-a) * hJ - he
  by_cases hs : s ≠ a
  · exact hoff s hs
  · have hs' : s = a := not_ne_iff.mp hs
    subst s
    have hI : Continuous (fun s : ℂ => (s + a) * cepsBrownianEntranceIntegral a (s ^ 2)) := by
      exact (continuous_id.add continuous_const).mul
        (cepsBrownianEntranceIntegral_continuous.comp (continuous_const.prodMk (continuous_id.pow 2)))
    have hJ : Continuous (fun s : ℂ => cepsBrownianSinhc (s ^ 2) -
        Complex.exp (-a) * cepsBrownianExpAverage (s - a)) := by
      exact (cepsBrownianSinhc_differentiable.continuous.comp (continuous_id.pow 2)).sub
        (continuous_const.mul (cepsBrownianExpAverage_continuous.comp
          (continuous_id.sub continuous_const)))
    have heq : (fun s : ℂ => (s + a) * cepsBrownianEntranceIntegral a (s ^ 2)) =ᶠ[𝓝[≠] a]
        fun s => cepsBrownianSinhc (s ^ 2) - Complex.exp (-a) * cepsBrownianExpAverage (s - a) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hoff s hs
    exact tendsto_nhds_unique ((hI.tendsto a).mono_left nhdsWithin_le_nhds |>.congr' heq)
      ((hJ.tendsto a).mono_left nhdsWithin_le_nhds)

theorem cepsBrownianH_sub_HInf {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀)
    (hz : z.re = 0) (hlam : 0 < lam) :
    cepsBrownianH v lam z - cepsBrownianHInf v lam z =
      -(Complex.exp (-(lam : ℂ) / v) / cepsBrownianSinhc (cepsBrownianSquare v lam z)) *
        cepsBrownianHInf v lam z * cepsBrownianExpAverage (cepsBrownianXiPlus v lam z) := by
  have hvne := (cepsBrownian_variance_bounds hv₀ hv).2.2.2
  have hS := cepsBrownianSinhc_ne (lam := lam) hv₀ hv hz
  set a := (lam : ℂ) / v
  set s := cepsBrownianR v lam z / v
  have hsum : s + a ≠ 0 := by
    have ha := (cepsBrownian_positive_drift_re hv₀ hv hz hlam).1
    have hs := cepsBrownian_quotient_re_pos hv₀ hv hz (Or.inl hlam.ne')
    intro h
    have h' := congrArg Complex.re h
    simp only [add_re, zero_re] at h'
    change 0 ≤ a.re at ha
    change 0 < s.re at hs
    linarith
  have hI := cepsBrownianEntranceIntegral_cancellation a s
  have hInf : cepsBrownianHInf v lam z = 2 / v / (s + a) := by
    unfold cepsBrownianHInf
    dsimp [s, a]
    field_simp
    rw [add_comm]
  have hxi : cepsBrownianXiPlus v lam z = s - a := by
    dsimp [cepsBrownianXiPlus, s, a]
    ring
  rw [cepsBrownianH_integral, ← cepsBrownian_normalized_sq hvne, hInf, hxi, neg_div]
  change 2 / v * cepsBrownianEntranceIntegral a (s ^ 2) / cepsBrownianSinhc (s ^ 2) -
    2 / v / (s + a) = -(Complex.exp (-a) / cepsBrownianSinhc (s ^ 2)) *
      (2 / v / (s + a)) * cepsBrownianExpAverage (s - a)
  rw [← cepsBrownian_normalized_sq hvne] at hS
  change cepsBrownianSinhc (s ^ 2) ≠ 0 at hS
  have hI' : cepsBrownianEntranceIntegral a (s ^ 2) =
      (cepsBrownianSinhc (s ^ 2) - Complex.exp (-a) * cepsBrownianExpAverage (s - a)) /
        (s + a) := (eq_div_iff hsum).mpr (by simpa [mul_comm] using hI)
  rw [hI']
  field_simp [hvne, hsum, hS]
  ring

end PGM
