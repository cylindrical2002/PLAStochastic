import PLAStochastic.Index.CEPS.BrownianCoeff.Defs

/-!
# Holomorphy of the Brownian coefficients in the variance

The zero-frequency case is evaluated by actual derivatives of entire functions.
The nonzero-frequency case uses the divided-difference formula locally away from `v = 0`.
-/

noncomputable section

open Complex Filter Topology

namespace PGM

theorem cepsBrownianSquare_differentiableAt {v : ℂ} (hv : v ≠ 0) (lam : ℝ) (z : ℂ) :
    DifferentiableAt ℂ (fun u => cepsBrownianSquare u lam z) v := by
  have ha : DifferentiableAt ℂ (fun u : ℂ => (lam : ℂ) / u) v :=
    differentiableAt_const _ |>.div differentiableAt_id hv
  exact ha.pow 2 |>.add (differentiableAt_const _ |>.div differentiableAt_id hv)

theorem cepsBrownianH_differentiableAt {v : ℂ} (lam : ℝ) (z : ℂ) (hv : v ≠ 0)
    (hs : cepsBrownianSinhc (cepsBrownianSquare v lam z) ≠ 0) :
    DifferentiableAt ℂ (fun u => cepsBrownianH u lam z) v := by
  have ha : DifferentiableAt ℂ (fun u : ℂ => (lam : ℂ) / u) v :=
    differentiableAt_const _ |>.div differentiableAt_id hv
  have hu := cepsBrownianSquare_differentiableAt hv lam z
  have hC := (cepsBrownianCosh_differentiable _).comp v hu
  have hS := (cepsBrownianSinhc_differentiable _).comp v hu
  by_cases hz : z = 0
  · subst z
    simp only [cepsBrownianH, cepsBrownianSquare, mul_zero, zero_div, add_zero, dslope_same]
    simp only [cepsBrownianSquare, mul_zero, zero_div, add_zero] at hs
    have hC' := (cepsBrownianCosh_differentiable.deriv _).comp v (ha.pow 2)
    have hS' := (cepsBrownianSinhc_differentiable.deriv _).comp v (ha.pow 2)
    exact ((differentiableAt_const _ |>.div differentiableAt_id hv).mul
      (hC'.sub (ha.mul hS'))).div ((cepsBrownianSinhc_differentiable _).comp v (ha.pow 2)) hs
  · have he : (fun u => cepsBrownianH u lam z) =ᶠ[𝓝 v] fun u =>
        (cepsBrownianCosh (cepsBrownianSquare u lam z) - (lam : ℂ) / u *
            cepsBrownianSinhc (cepsBrownianSquare u lam z) - Complex.exp (-(lam : ℂ) / u)) /
          z / cepsBrownianSinhc (cepsBrownianSquare u lam z) := by
      filter_upwards [eventually_ne_nhds hv] with u hune
      exact cepsBrownianH_eq hune lam hz
    have hdiff := ((hC.sub (ha.mul hS)).sub ha.neg.cexp).div_const z |>.div hS hs
    apply hdiff.congr_of_eventuallyEq
    filter_upwards [he] with u heu
    simpa only [neg_div, Function.comp_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply,
      Pi.neg_apply] using heu

theorem cepsBrownianU_differentiableAt {v : ℂ} (lam : ℝ) (z : ℂ) (hv : v ≠ 0)
    (hs : cepsBrownianSinhc (cepsBrownianSquare v lam z) ≠ 0) :
    DifferentiableAt ℂ (fun u => cepsBrownianU u lam z) v := by
  have ha : DifferentiableAt ℂ (fun u : ℂ => (lam : ℂ) / u) v :=
    differentiableAt_const _ |>.div differentiableAt_id hv
  have hu := cepsBrownianSquare_differentiableAt hv lam z
  exact (differentiableAt_id.div_const 2 |>.mul ha.cexp).div
    ((cepsBrownianSinhc_differentiable _).comp v hu) hs

theorem cepsBrownianKernel_differentiableAt {v₀ : ℝ} {v : ℂ} (lam : ℝ) (z : ℂ)
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0) :
    DifferentiableAt ℂ (fun u => cepsBrownianKernel u lam z) v := by
  obtain ⟨hvre, -, -, hvne⟩ := cepsBrownian_variance_bounds hv₀ hv
  have hvpos : 0 < v.re := by linarith
  have hs := cepsBrownianSinhc_ne (lam := lam) hv₀ hv hz
  have ha : DifferentiableAt ℂ (fun u : ℂ => (lam : ℂ) / u) v :=
    differentiableAt_const _ |>.div differentiableAt_id hvne
  have hu := cepsBrownianSquare_differentiableAt hvne lam z
  have hH := cepsBrownianH_differentiableAt lam z hvne hs
  have hS := (cepsBrownianSinhc_differentiable _).comp v hu
  have hS' := (cepsBrownianSinhc_differentiable.deriv _).comp v hu
  have hfirst := (((hH.pow 2).mul ha.cexp).mul hS').div (hS.pow 2) (pow_ne_zero 2 hs)
  unfold cepsBrownianKernel
  by_cases hlam : 1 ≤ lam
  · simp only [hlam, ite_true]
    have hlampos : 0 < lam := by linarith
    have hRne : cepsBrownianR v lam z ≠ 0 := by
      intro heq
      have hp := cepsBrownian_quotient_re_pos hv₀ hv hz (Or.inl hlampos.ne')
      simp [heq] at hp
    have hden : (lam : ℂ) + cepsBrownianR v lam z ≠ 0 := by
      intro heq
      have := congrArg Complex.re heq
      simp only [add_re, ofReal_re, zero_re] at this
      linarith [cepsBrownianR_re_nonneg v lam z]
    have hR := cepsBrownianR_differentiableAt (lam := lam) hvpos hz
    have hxi : DifferentiableAt ℂ (fun u => cepsBrownianXiPlus u lam z) v :=
      (differentiableAt_const _ |>.add hR).div differentiableAt_id hvne
    have hInf : DifferentiableAt ℂ (fun u => cepsBrownianHInf u lam z) v :=
      differentiableAt_const _ |>.div (differentiableAt_const _ |>.add hR) hden
    exact hfirst.add (((hInf.pow 2).mul hxi.neg.cexp).mul
      ((differentiableAt_id.div hR hRne).sub_const 1))
  · simp only [hlam, ite_false, add_zero]
    exact hfirst

end PGM
