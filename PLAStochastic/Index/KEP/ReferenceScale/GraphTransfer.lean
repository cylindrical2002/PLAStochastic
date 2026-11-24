import PLAStochastic.Index.KEP.ReferenceScale.GraphTransport

/-!
# First derivative transfer on the actual two-tail graph

The logarithmic-slope output is `exp(-s) * (D + i + r + u - xA + xB - v)`.
The exact material velocity is `-D * exp(-s)`. Integration by parts retains
both exterior fluxes, and the theorem explicitly requires the scalar cutoff
to vanish at both integration endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

def kepGraphOutput (D : ℝ) (i r : ℕ) (xA xB s u v : ℝ) : ℝ :=
  Real.exp (-s) * (D + (i : ℝ) + (r : ℝ) + u - xA + xB - v)

theorem continuous_kepGraphOutput (D : ℝ) (i r : ℕ) (xA xB : ℝ) :
    Continuous (fun t : ℝ × ℝ × ℝ => kepGraphOutput D i r xA xB t.1 t.2.1 t.2.2) := by
  unfold kepGraphOutput
  fun_prop

theorem hasDerivAt_kepGraphOutput_slope (D : ℝ) (i r : ℕ) (xA xB s u v : ℝ) :
    HasDerivAt (fun t => kepGraphOutput D i r xA xB t u v)
      (-kepGraphOutput D i r xA xB s u v) s := by
  convert ((Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)).mul_const
    (D + (i : ℝ) + (r : ℝ) + u - xA + xB - v) using 1 <;>
    first | rfl | (dsimp [kepGraphOutput]; ring)

theorem hasDerivAt_kepGraphOutput_left (D : ℝ) (i r : ℕ) (xA xB s u v : ℝ) :
    HasDerivAt (fun t => kepGraphOutput D i r xA xB s t v) (Real.exp (-s)) u := by
  convert (((((hasDerivAt_const u (D + (i : ℝ) + (r : ℝ))).add (hasDerivAt_id u)).sub_const
    xA).add_const xB).sub_const v).const_mul (Real.exp (-s)) using 1 <;>
    first | rfl | norm_num

theorem hasDerivAt_kepGraphOutput_right (D : ℝ) (i r : ℕ) (xA xB s u v : ℝ) :
    HasDerivAt (fun t => kepGraphOutput D i r xA xB s u t) (-Real.exp (-s)) v := by
  convert ((hasDerivAt_const v (D + (i : ℝ) + (r : ℝ) + u - xA + xB)).sub
    (hasDerivAt_id v)).const_mul (Real.exp (-s)) using 1 <;>
    first | rfl | ring

theorem kepGraphOutput_material_velocity (D : ℝ) (i r : ℕ) (xA xB s u v : ℝ) :
    -kepGraphOutput D i r xA xB s u v + (u - xA + (i : ℝ)) * Real.exp (-s) +
      (v - xB - (r : ℝ)) * (-Real.exp (-s)) = -D * Real.exp (-s) := by
  unfold kepGraphOutput
  ring

theorem kepTailPairTest_const_mul (pA pB : ℝ → ℝ → ℝ) (w s : ℝ) (i r : ℕ)
    (xA xB c : ℝ) (Φ : ℝ → ℝ → ℝ) :
    kepTailPairTest pA pB w s i r xA xB (fun u v => c * Φ u v) =
      c * kepTailPairTest pA pB w s i r xA xB Φ := by
  unfold kepTailPairTest
  simp_rw [kepTailTest_const_mul]

theorem kepTailPairTest_congr (pA pB : ℝ → ℝ → ℝ) (w s : ℝ) (i r : ℕ)
    (xA xB : ℝ) {Φ Ψ : ℝ → ℝ → ℝ} (h : ∀ u v, Φ u v = Ψ u v) :
    kepTailPairTest pA pB w s i r xA xB Φ = kepTailPairTest pA pB w s i r xA xB Ψ := by
  apply kepTailTest_congr
  intro u
  exact kepTailTest_congr pB w s r xB (h u)

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_kepGraphTest (A : KepTailDynamics (-1)) (B : KepTailDynamics 1)
    {φ φ' : ℝ → ℝ} (hφ : Continuous φ) (hφ' : Continuous φ')
    (hdφ : ∀ y, HasDerivAt φ (φ' y) y) {w : ℝ} (hw : 0 ≤ w)
    (D s : ℝ) (i r : ℕ) (xA xB : ℝ) :
    HasDerivAt (fun t => kepTailPairTest A.step B.step w t i r xA xB
      (fun u v => φ (kepGraphOutput D i r xA xB t u v)))
      (-D * Real.exp (-s) * kepTailPairTest A.step B.step w s i r xA xB
        (fun u v => φ' (kepGraphOutput D i r xA xB s u v)) +
        kepTailPairFlux A.step B.step w (-1) 1 s i r xA xB
          (fun u v => φ (kepGraphOutput D i r xA xB s u v))) s := by
  let S := kepGraphOutput D i r xA xB
  have hS := continuous_kepGraphOutput D i r xA xB
  have hΨ := hφ'.comp hS
  have hh := hasDerivAt_kepTailPairTest_transport A B
    (Φ := fun t u v => φ (S t u v))
    (Φs := fun t u v => φ' (S t u v) * (-S t u v))
    (Φu := fun t u v => φ' (S t u v) * Real.exp (-t))
    (Φv := fun t u v => φ' (S t u v) * (-Real.exp (-t)))
    (hφ.comp hS) (hΨ.mul hS.neg) (hΨ.mul (Real.continuous_exp.comp continuous_fst.neg))
    (hΨ.mul (Real.continuous_exp.comp continuous_fst.neg).neg)
    (fun t u v => (hdφ _).comp t (hasDerivAt_kepGraphOutput_slope D i r xA xB t u v))
    (fun t u v => (hdφ _).comp u (hasDerivAt_kepGraphOutput_left D i r xA xB t u v))
    (fun t u v => (hdφ _).comp v (hasDerivAt_kepGraphOutput_right D i r xA xB t u v))
    hw s i r xA xB
  have he : kepTailPairTest A.step B.step w s i r xA xB
      (fun u v => φ' (S s u v) * (-S s u v) +
        (u - xA - (i : ℝ) * (-1)) * (φ' (S s u v) * Real.exp (-s)) +
        (v - xB - (r : ℝ) * 1) * (φ' (S s u v) * (-Real.exp (-s)))) =
      -D * Real.exp (-s) * kepTailPairTest A.step B.step w s i r xA xB
        (fun u v => φ' (S s u v)) := by
    rw [← kepTailPairTest_const_mul]
    apply kepTailPairTest_congr
    intro u v
    dsimp [S, kepGraphOutput]
    ring
  rw [he] at hh
  exact hh

def kepLogGraphIntegral (pA pB : ℝ → ℝ → ℝ) (w lo hi D : ℝ) (i r : ℕ)
    (xA xB : ℝ) (R φ : ℝ → ℝ) : ℝ :=
  ∫ s in Ioc lo hi, R s * kepTailPairTest pA pB w s i r xA xB
    (fun u v => φ (kepGraphOutput D i r xA xB s u v))

def kepLogGraphFluxIntegral (pA pB : ℝ → ℝ → ℝ) (w lo hi D : ℝ) (i r : ℕ)
    (xA xB : ℝ) (R φ : ℝ → ℝ) : ℝ :=
  ∫ s in Ioc lo hi, (Real.exp s * R s / D) *
    kepTailPairFlux pA pB w (-1) 1 s i r xA xB
      (fun u v => φ (kepGraphOutput D i r xA xB s u v))

/-- First transfer, in logarithmic physical slope. The original scalar weight
is differentiated once and both terminal Dirac fluxes are kept. -/
theorem kepLogGraphIntegral_derivative_transfer
    (A : KepTailDynamics (-1)) (B : KepTailDynamics 1)
    {φ φ' R R' : ℝ → ℝ} (hφ : Continuous φ) (hφ' : Continuous φ')
    (hdφ : ∀ y, HasDerivAt φ (φ' y) y) (hR : Continuous R) (hR' : Continuous R')
    (hdR : ∀ s, HasDerivAt R (R' s) s)
    {w lo hi D : ℝ} (hw : 0 ≤ w) (hlh : lo ≤ hi) (hD : D ≠ 0)
    (hlo : R lo = 0) (hhi : R hi = 0) (i r : ℕ) (xA xB : ℝ) :
    kepLogGraphIntegral A.step B.step w lo hi D i r xA xB R φ' =
      kepLogGraphIntegral A.step B.step w lo hi D i r xA xB
        (fun s => Real.exp s * (R s + R' s) / D) φ +
      kepLogGraphFluxIntegral A.step B.step w lo hi D i r xA xB R φ := by
  let H : ℝ → ℝ := fun s => kepTailPairTest A.step B.step w s i r xA xB
    (fun u v => φ (kepGraphOutput D i r xA xB s u v))
  let J : ℝ → ℝ := fun s => kepTailPairTest A.step B.step w s i r xA xB
    (fun u v => φ' (kepGraphOutput D i r xA xB s u v))
  let F : ℝ → ℝ := fun s => kepTailPairFlux A.step B.step w (-1) 1 s i r xA xB
    (fun u v => φ (kepGraphOutput D i r xA xB s u v))
  let Q : ℝ → ℝ := fun s => Real.exp s * R s / D
  let Q' : ℝ → ℝ := fun s => Real.exp s * (R s + R' s) / D
  have hS := continuous_kepGraphOutput D i r xA xB
  have hH : Continuous H :=
    continuous_kepTailPairTest A.continuous_step B.continuous_step (hφ.comp hS) w i r xA xB
  have hJ : Continuous J :=
    continuous_kepTailPairTest A.continuous_step B.continuous_step (hφ'.comp hS) w i r xA xB
  have hF : Continuous F :=
    continuous_kepTailPairFlux A.continuous_step B.continuous_step (hφ.comp hS) w (-1) 1 i r xA xB
  have hQ : Continuous Q := (Real.continuous_exp.mul hR).div_const D
  have hQ' : Continuous Q' := (Real.continuous_exp.mul (hR.add hR')).div_const D
  have hdQ (s : ℝ) : HasDerivAt Q (Q' s) s := by
    convert ((Real.hasDerivAt_exp s).mul (hdR s)).div_const D using 1 <;>
      first | rfl | (dsimp [Q']; ring)
  have hdH (s : ℝ) : HasDerivAt H (-D * Real.exp (-s) * J s + F s) s :=
    hasDerivAt_kepGraphTest A B hφ hφ' hdφ hw D s i r xA xB
  have hi' (g : ℝ → ℝ) (hg : Continuous g) :
      Integrable g (volume.restrict (Ioc lo hi)) :=
    hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := lo) (b := hi) (u := Q) (u' := Q') (v := H)
    (v' := fun s => -D * Real.exp (-s) * J s + F s)
    (fun s _ => hdQ s) (fun s _ => hdH s) (hQ'.intervalIntegrable lo hi)
    ((by fun_prop : Continuous (fun s => -D * Real.exp (-s) * J s + F s)).intervalIntegrable lo hi)
  rw [intervalIntegral.integral_of_le hlh, intervalIntegral.integral_of_le hlh] at hIBP
  have hzero : Q hi * H hi - Q lo * H lo = 0 := by simp [Q, hlo, hhi]
  rw [hzero] at hIBP
  have he : (∫ s in Ioc lo hi, Q s * (-D * Real.exp (-s) * J s + F s)) =
      -(∫ s in Ioc lo hi, R s * J s) + ∫ s in Ioc lo hi, Q s * F s := by
    calc
      _ = ∫ s in Ioc lo hi, -(R s * J s) + Q s * F s := by
        apply integral_congr_ae
        exact ae_of_all _ fun s => by
          have hexp : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
          have hcancel : Q s * (-D * Real.exp (-s)) = -R s := by
            calc
              _ = -(R s * (Real.exp s * Real.exp (-s))) := by
                dsimp [Q]
                field_simp [hD]
              _ = _ := by rw [hexp, mul_one]
          dsimp only
          rw [mul_add, ← mul_assoc, hcancel, neg_mul]
      _ = _ := by
        rw [integral_add (f := fun s => -(R s * J s)) (g := fun s => Q s * F s)
          (hi' _ (by fun_prop)) (hi' _ (by fun_prop)), integral_neg]
  rw [he] at hIBP
  change (∫ s in Ioc lo hi, R s * J s) =
    (∫ s in Ioc lo hi, Q' s * H s) + ∫ s in Ioc lo hi, Q s * F s
  linarith

end

end PGM
