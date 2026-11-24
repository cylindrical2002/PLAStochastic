import PLAStochastic.Index.CEPS.BrownianCoeff.Defs
import PLAStochastic.ForMathlib.Analysis.Complex.Hadamard
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# An integral representation of the Brownian entrance

This representation removes the zero-frequency division and retains the real-part
exponents needed to bound the product of an entrance squared and a bridge.
-/

noncomputable section

open Complex Set Filter Topology MeasureTheory

namespace PGM

@[irreducible] def cepsBrownianEntranceIntegral (a u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, Complex.exp (-a * t) * ((1 - t : ℝ) : ℂ) *
    cepsBrownianSinhc (((1 - t : ℝ) : ℂ) ^ 2 * u)

theorem cepsBrownianEntranceIntegral_continuous :
    Continuous (fun p : ℂ × ℂ => cepsBrownianEntranceIntegral p.1 p.2) := by
  have hfun : Continuous (fun p : (ℂ × ℂ) × ℝ =>
      Complex.exp (-p.1.1 * p.2) * ((1 - p.2 : ℝ) : ℂ) *
        cepsBrownianSinhc (((1 - p.2 : ℝ) : ℂ) ^ 2 * p.1.2)) := by
    have := cepsBrownianSinhc_differentiable.continuous
    fun_prop
  have h := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun p : ℂ × ℂ => fun t : ℝ => Complex.exp (-p.1 * t) * ((1 - t : ℝ) : ℂ) *
      cepsBrownianSinhc (((1 - t : ℝ) : ℂ) ^ 2 * p.2)) hfun
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  simpa only [cepsBrownianEntranceIntegral, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc] using h

private theorem brownian_B_hasDerivAt (u : ℂ) (t : ℝ) :
    HasDerivAt (fun r : ℝ => ((1 - r : ℝ) : ℂ) * cepsBrownianSinhc (((1 - r : ℝ) : ℂ) ^ 2 * u))
      (-cepsBrownianCosh (((1 - t : ℝ) : ℂ) ^ 2 * u)) t := by
  by_cases hu : u = 0
  · subst u
    simp only [mul_zero, cepsBrownianSinhc_zero, mul_one, cepsBrownianCosh_zero]
    simpa using ((hasDerivAt_id t).const_sub 1).ofReal_comp
  · set s := Complex.sqrt u
    have hs : s ^ 2 = u := sqrt_sq_eq u
    have hsne : s ≠ 0 := by intro h; simp [h] at hs; exact hu hs.symm
    have heq (q : ℂ) : q * cepsBrownianSinhc (q ^ 2 * u) = Complex.sinh (q * s) / s := by
      rw [← hs, ← mul_pow]
      apply (eq_div_iff hsne).mpr
      calc
        q * cepsBrownianSinhc ((q * s) ^ 2) * s =
            (q * s) * cepsBrownianSinhc ((q * s) ^ 2) := by ring
        _ = Complex.sinh (q * s) := cepsBrownianSinhc_mul _
    have hfun : (fun r : ℝ => ((1 - r : ℝ) : ℂ) * cepsBrownianSinhc (((1 - r : ℝ) : ℂ) ^ 2 * u)) =
        fun r => Complex.sinh (((1 - r : ℝ) : ℂ) * s) / s := funext fun r => heq _
    rw [hfun, ← hs, ← mul_pow, cepsBrownianCosh_sq]
    have h := hasDerivAt_comp_affine (b := s) (u := -s) (t := t)
      (Complex.hasDerivAt_sinh (s + t * -s))
    have hfun' : (fun r : ℝ => Complex.sinh (s + r * -s)) =
        fun r => Complex.sinh (((1 - r : ℝ) : ℂ) * s) := by
      funext r
      congr 1
      push_cast
      ring
    rw [hfun'] at h
    apply (h.div_const s).congr_deriv
    have harg : s + (t : ℂ) * -s = ((1 - t : ℝ) : ℂ) * s := by push_cast; ring
    rw [harg]
    field_simp

private theorem brownian_C_hasDerivAt (u : ℂ) (t : ℝ) :
    HasDerivAt (fun r : ℝ => cepsBrownianCosh (((1 - r : ℝ) : ℂ) ^ 2 * u))
      (-u * (((1 - t : ℝ) : ℂ) * cepsBrownianSinhc (((1 - t : ℝ) : ℂ) ^ 2 * u))) t := by
  set s := Complex.sqrt u
  have hs : s ^ 2 = u := sqrt_sq_eq u
  have hfun : (fun r : ℝ => cepsBrownianCosh (((1 - r : ℝ) : ℂ) ^ 2 * u)) =
      fun r => Complex.cosh (((1 - r : ℝ) : ℂ) * s) := by
    funext r
    rw [← hs, ← mul_pow, cepsBrownianCosh_sq]
  rw [hfun]
  have h := hasDerivAt_comp_affine (b := s) (u := -s) (t := t)
    (Complex.hasDerivAt_cosh (s + t * -s))
  have hfun' : (fun r : ℝ => Complex.cosh (s + r * -s)) =
      fun r => Complex.cosh (((1 - r : ℝ) : ℂ) * s) := by
    funext r
    congr 1
    push_cast
    ring
  rw [hfun'] at h
  apply h.congr_deriv
  have harg : s + (t : ℂ) * -s = ((1 - t : ℝ) : ℂ) * s := by push_cast; ring
  rw [harg, ← cepsBrownianSinhc_mul, mul_pow, hs]
  ring_nf
  rw [hs]

theorem cepsBrownianEntranceIntegral_mul (a u : ℂ) :
    (u - a ^ 2) * cepsBrownianEntranceIntegral a u =
      cepsBrownianCosh u - a * cepsBrownianSinhc u - Complex.exp (-a) := by
  let B : ℝ → ℂ := fun t => ((1 - t : ℝ) : ℂ) * cepsBrownianSinhc (((1 - t : ℝ) : ℂ) ^ 2 * u)
  let C : ℝ → ℂ := fun t => cepsBrownianCosh (((1 - t : ℝ) : ℂ) ^ 2 * u)
  let F : ℝ → ℂ := fun t => Complex.exp (-a * t) * (a * B t - C t)
  have hderiv (t : ℝ) : HasDerivAt F ((u - a ^ 2) * (Complex.exp (-a * t) * B t)) t := by
    have hB := brownian_B_hasDerivAt u t
    have hC := brownian_C_hasDerivAt u t
    change HasDerivAt B (-C t) t at hB
    change HasDerivAt C (-u * B t) t at hC
    have he : HasDerivAt (fun r : ℝ => Complex.exp (-a * r)) (Complex.exp (-a * t) * -a) t := by
      simpa [mul_comm] using hasDerivAt_comp_affine (b := 0) (u := -a)
        (Complex.hasDerivAt_exp (0 + t * -a))
    have h := he.mul ((hB.const_mul a).sub hC)
    apply h.congr_deriv
    simp only [Pi.sub_apply]
    ring
  have hint : IntervalIntegrable (fun t : ℝ => (u - a ^ 2) * (Complex.exp (-a * t) * B t)) volume 0 1 := by
    have hS := cepsBrownianSinhc_differentiable.continuous
    apply Continuous.intervalIntegrable
    dsimp [B]
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint
  rw [intervalIntegral.integral_const_mul] at h
  dsimp [F, B, C] at h
  norm_num at h
  change (u - a ^ 2) * cepsBrownianEntranceIntegral a u = _
  have heq : (∫ t in (0 : ℝ)..1, Complex.exp (-a * t) *
        (((1 - t : ℝ) : ℂ) * cepsBrownianSinhc (((1 - t : ℝ) : ℂ) ^ 2 * u))) =
      cepsBrownianEntranceIntegral a u := by
    unfold cepsBrownianEntranceIntegral
    apply intervalIntegral.integral_congr
    intro t _
    ring
  push_cast at heq
  simp only [neg_mul] at heq
  rw [heq] at h
  linear_combination h

theorem cepsBrownianEntranceIntegral_eq (a u : ℂ) :
    cepsBrownianEntranceIntegral a u = dslope cepsBrownianCosh (a ^ 2) u -
      a * dslope cepsBrownianSinhc (a ^ 2) u := by
  have hoff (w : ℂ) (hw : w ≠ a ^ 2) : cepsBrownianEntranceIntegral a w =
      dslope cepsBrownianCosh (a ^ 2) w - a * dslope cepsBrownianSinhc (a ^ 2) w := by
    have h := cepsBrownianEntranceIntegral_mul a w
    rw [← cepsBrownianCosh_sub_mul_sinhc a] at h
    rw [dslope_of_ne _ hw, dslope_of_ne _ hw, slope_def_field, slope_def_field]
    field_simp
    linear_combination h
  by_cases hu : u ≠ a ^ 2
  · exact hoff u hu
  · have hu' : u = a ^ 2 := not_ne_iff.mp hu
    subst u
    have hp : Continuous (fun w : ℂ => (a, w)) := continuous_const.prodMk continuous_id
    have hI : Continuous (fun w : ℂ => cepsBrownianEntranceIntegral a w) :=
      cepsBrownianEntranceIntegral_continuous.comp hp
    have hC : Continuous (dslope cepsBrownianCosh (a ^ 2)) := by
      have h := (differentiableOn_dslope (Filter.univ_mem : (univ : Set ℂ) ∈ 𝓝 (a ^ 2))).mpr
        cepsBrownianCosh_differentiable.differentiableOn
      exact (differentiableOn_univ.mp h).continuous
    have hS : Continuous (dslope cepsBrownianSinhc (a ^ 2)) := by
      have h := (differentiableOn_dslope (Filter.univ_mem : (univ : Set ℂ) ∈ 𝓝 (a ^ 2))).mpr
        cepsBrownianSinhc_differentiable.differentiableOn
      exact (differentiableOn_univ.mp h).continuous
    have hD : Continuous (fun w : ℂ => dslope cepsBrownianCosh (a ^ 2) w -
        a * dslope cepsBrownianSinhc (a ^ 2) w) := hC.sub (continuous_const.mul hS)
    have he : (fun w => cepsBrownianEntranceIntegral a w) =ᶠ[𝓝[≠] (a ^ 2)]
        fun w => dslope cepsBrownianCosh (a ^ 2) w - a * dslope cepsBrownianSinhc (a ^ 2) w := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact hoff w hw
    exact tendsto_nhds_unique ((hI.tendsto (a ^ 2)).mono_left nhdsWithin_le_nhds |>.congr' he)
      ((hD.tendsto (a ^ 2)).mono_left nhdsWithin_le_nhds)

theorem cepsBrownianH_integral (v : ℂ) (lam : ℝ) (z : ℂ) :
    cepsBrownianH v lam z = 2 / v *
      cepsBrownianEntranceIntegral ((lam : ℂ) / v) (cepsBrownianSquare v lam z) /
        cepsBrownianSinhc (cepsBrownianSquare v lam z) := by
  rw [cepsBrownianEntranceIntegral_eq]
  rfl

end PGM
