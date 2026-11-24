import PLAStochastic.Index.KEP.ReferenceScale.FixedBridge
import PLAStochastic.Index.KEP.ReferenceScale.LogSlopeStep

/-!
# The internal boundary fluxes in the finite killed-path Ward identities

Each recursive boundary term inserts a pin at the last internal position. The
convolution propagates all earlier pins. Both band endpoints are retained.
The number of steps is `n + 1`; there is no internal flux at `n = 0`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepBridgeTranslationFlux (p : ℝ → ℝ → ℝ) (w s : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 0
  | n + 1, x, y =>
      (∫ z in Ioc 0 w, kepBridgeTranslationFlux p w s n x z * p s (y - z)) +
        kepFixedBridge p w s n x w * p s (y - w) -
        kepFixedBridge p w s n x 0 * p s y

def kepBridgeTransportFlux (p : ℝ → ℝ → ℝ) (w σ s : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 0
  | n + 1, x, y =>
      (∫ z in Ioc 0 w, kepBridgeTransportFlux p w σ s n x z * p s (y - z)) +
        (w - x - (n + 1 : ℕ) * σ) * kepFixedBridge p w s n x w * p s (y - w) -
        (-x - (n + 1 : ℕ) * σ) * kepFixedBridge p w s n x 0 * p s y

theorem continuous_kepBridgeTranslationFlux {p : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (w : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ × ℝ × ℝ => kepBridgeTranslationFlux p w t.1 n t.2.1 t.2.2) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hk := continuous_kepFixedBridge hp w n
    exact ((continuous_integral_Ioc_of_continuous
      ((ih.comp (continuous_fst.fst.prodMk
        (continuous_fst.snd.fst.prodMk continuous_snd))).mul
        (hp.comp (continuous_fst.fst.prodMk (continuous_fst.snd.snd.sub continuous_snd))))
      0 w).add
      ((hk.comp (continuous_fst.prodMk (continuous_snd.fst.prodMk continuous_const))).mul
        (hp.comp (continuous_fst.prodMk (continuous_snd.snd.sub continuous_const))))).sub
      ((hk.comp (continuous_fst.prodMk (continuous_snd.fst.prodMk continuous_const))).mul
        (hp.comp (continuous_fst.prodMk continuous_snd.snd)))

theorem continuous_kepBridgeTransportFlux {p : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (w σ : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ × ℝ × ℝ => kepBridgeTransportFlux p w σ t.1 n t.2.1 t.2.2) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hk := continuous_kepFixedBridge hp w n
    exact ((continuous_integral_Ioc_of_continuous
      ((ih.comp (continuous_fst.fst.prodMk
        (continuous_fst.snd.fst.prodMk continuous_snd))).mul
        (hp.comp (continuous_fst.fst.prodMk (continuous_fst.snd.snd.sub continuous_snd))))
      0 w).add
      ((((continuous_const.sub continuous_snd.fst).sub continuous_const).mul
        (hk.comp (continuous_fst.prodMk (continuous_snd.fst.prodMk continuous_const)))).mul
        (hp.comp (continuous_fst.prodMk (continuous_snd.snd.sub continuous_const))))).sub
      (((continuous_snd.fst.neg.sub continuous_const).mul
        (hk.comp (continuous_fst.prodMk (continuous_snd.fst.prodMk continuous_const)))).mul
        (hp.comp (continuous_fst.prodMk continuous_snd.snd)))

/-- Simultaneous endpoint translation, with all internal pins. -/
theorem kepFixedBridge_translation {p p' : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hd : ∀ s t, HasDerivAt (p s) (p' s t) t) {w : ℝ} (hw : 0 ≤ w)
    (s : ℝ) (n : ℕ) (x y : ℝ) :
    kepFixedBridgeLeft p p' w s n x y + kepFixedBridgeRight p p' w s n x y =
      -kepBridgeTranslationFlux p w s n x y := by
  induction n generalizing x y with
  | zero => simp [kepFixedBridgeLeft, kepFixedBridgeRight, kepBridgeTranslationFlux]
  | succ n ih =>
    have hk : Continuous (kepFixedBridge p w s n x) :=
      (continuous_kepFixedBridge hp w n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    have hky : Continuous (kepFixedBridgeRight p p' w s n x) :=
      (continuous_kepFixedBridgeRight hp hp' w n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    have hb : Continuous (kepBridgeTranslationFlux p w s n x) :=
      (continuous_kepBridgeTranslationFlux hp w n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    have hpt : Continuous (fun z => p s (y - z)) :=
      hp.comp (continuous_const.prodMk (continuous_const.sub continuous_id))
    have hpt' : Continuous (fun z => p' s (y - z)) :=
      hp'.comp (continuous_const.prodMk (continuous_const.sub continuous_id))
    have hi : ∀ g : ℝ → ℝ, Continuous g → Integrable g (volume.restrict (Ioc 0 w)) :=
      fun g hg => hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := 0) (b := w) (u := kepFixedBridge p w s n x)
      (u' := kepFixedBridgeRight p p' w s n x)
      (v := fun z => p s (y - z)) (v' := fun z => -p' s (y - z))
      (fun z _ => hasDerivAt_kepFixedBridge_right hp hp' hd w s n x z)
      (fun z _ => by
        simpa only [Function.comp_def, zero_sub, mul_neg_one] using
          (hd s (y - z)).comp z ((hasDerivAt_const z y).sub (hasDerivAt_id z)))
      (hky.intervalIntegrable 0 w) (hpt'.neg.intervalIntegrable 0 w)
    rw [intervalIntegral.integral_of_le hw, intervalIntegral.integral_of_le hw] at hIBP
    simp only [mul_neg, integral_neg, sub_zero] at hIBP
    simp only [kepFixedBridgeLeft, kepFixedBridgeRight, kepBridgeTranslationFlux]
    have he : (∫ z in Ioc 0 w, kepFixedBridgeLeft p p' w s n x z * p s (y - z)) =
        -(∫ z in Ioc 0 w, kepFixedBridgeRight p p' w s n x z * p s (y - z)) -
          (∫ z in Ioc 0 w, kepBridgeTranslationFlux p w s n x z * p s (y - z)) := by
      calc
        _ = ∫ z in Ioc 0 w, -kepFixedBridgeRight p p' w s n x z * p s (y - z) -
            kepBridgeTranslationFlux p w s n x z * p s (y - z) := by
          apply integral_congr_ae
          exact ae_of_all _ fun z => by
            dsimp only
            linear_combination (p s (y - z)) * (ih x z)
        _ = _ := by
          rw [integral_sub (f := fun z => -kepFixedBridgeRight p p' w s n x z * p s (y - z))
            (g := fun z => kepBridgeTranslationFlux p w s n x z * p s (y - z))
            (hi _ (hky.neg.mul hpt)) (hi _ (hb.mul hpt))]
          simp only [neg_mul, integral_neg]
    rw [he]
    linarith

/-- The logarithmic-slope Ward identity on an arbitrary finite killed path. -/
theorem kepFixedBridge_transport {p p' q : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hd : ∀ s t, HasDerivAt (p s) (p' s t) t)
    {σ : ℝ} (hward : ∀ s t, q s t = -p s t + (σ - t) * p' s t)
    {w : ℝ} (hw : 0 ≤ w) (s : ℝ) (n : ℕ) (x y : ℝ) :
    kepFixedBridgeSlope p q w s n x y = -kepFixedBridge p w s n x y +
      ((n + 1 : ℕ) * σ + x - y) * kepFixedBridgeRight p p' w s n x y -
        kepBridgeTransportFlux p w σ s n x y := by
  induction n generalizing x y with
  | zero =>
    simp only [kepFixedBridgeSlope, kepFixedBridge, kepFixedBridgeRight,
      kepBridgeTransportFlux, sub_zero, hward]
    ring
  | succ n ih =>
    have hk : Continuous (kepFixedBridge p w s n x) :=
      (continuous_kepFixedBridge hp w n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    have hky : Continuous (kepFixedBridgeRight p p' w s n x) :=
      (continuous_kepFixedBridgeRight hp hp' w n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    have hb : Continuous (kepBridgeTransportFlux p w σ s n x) :=
      (continuous_kepBridgeTransportFlux hp w σ n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    have hpt : Continuous (fun z => p s (y - z)) :=
      hp.comp (continuous_const.prodMk (continuous_const.sub continuous_id))
    have hpt' : Continuous (fun z => p' s (y - z)) :=
      hp'.comp (continuous_const.prodMk (continuous_const.sub continuous_id))
    have hi : ∀ g : ℝ → ℝ, Continuous g → Integrable g (volume.restrict (Ioc 0 w)) :=
      fun g hg => hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    let A : ℝ → ℝ := fun z => ((n + 1 : ℕ) * σ + x - z) * kepFixedBridge p w s n x z
    let A' : ℝ → ℝ := fun z => -kepFixedBridge p w s n x z +
      ((n + 1 : ℕ) * σ + x - z) * kepFixedBridgeRight p p' w s n x z
    have hA : Continuous A := by dsimp [A]; fun_prop
    have hA' : Continuous A' := by dsimp [A']; fun_prop
    have hAd (z : ℝ) : HasDerivAt A (A' z) z := by
      convert (((hasDerivAt_const z ((n + 1 : ℕ) * σ + x)).sub (hasDerivAt_id z)).mul
        (hasDerivAt_kepFixedBridge_right hp hp' hd w s n x z)) using 1 <;>
        first | rfl | (dsimp [A']; ring)
    have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := 0) (b := w) (u := A) (u' := A')
      (v := fun z => p s (y - z)) (v' := fun z => -p' s (y - z))
      (fun z _ => hAd z)
      (fun z _ => by
        simpa only [Function.comp_def, zero_sub, mul_neg_one] using
          (hd s (y - z)).comp z ((hasDerivAt_const z y).sub (hasDerivAt_id z)))
      (hA'.intervalIntegrable 0 w) (hpt'.neg.intervalIntegrable 0 w)
    rw [intervalIntegral.integral_of_le hw, intervalIntegral.integral_of_le hw] at hIBP
    simp only [mul_neg, integral_neg, sub_zero] at hIBP
    have he : kepFixedBridgeSlope p q w s (n + 1) x y =
        -(∫ z in Ioc 0 w, kepFixedBridge p w s n x z * p s (y - z)) +
          ((n + 2 : ℕ) * σ + x - y) *
            (∫ z in Ioc 0 w, kepFixedBridge p w s n x z * p' s (y - z)) -
          (∫ z in Ioc 0 w, kepBridgeTransportFlux p w σ s n x z * p s (y - z)) +
          (∫ z in Ioc 0 w, A' z * p s (y - z)) -
          (∫ z in Ioc 0 w, A z * p' s (y - z)) := by
      rw [kepFixedBridgeSlope]
      calc
        _ = ∫ z in Ioc 0 w,
            -(kepFixedBridge p w s n x z * p s (y - z)) +
              ((n + 2 : ℕ) * σ + x - y) *
                (kepFixedBridge p w s n x z * p' s (y - z)) -
              kepBridgeTransportFlux p w σ s n x z * p s (y - z) +
              A' z * p s (y - z) - A z * p' s (y - z) := by
          apply integral_congr_ae
          exact ae_of_all _ fun z => by
            dsimp only
            rw [ih x z, hward]
            dsimp [A, A']
            push_cast
            ring
        _ = _ := by
          rw [integral_sub, integral_add, integral_sub, integral_add,
            integral_neg, integral_const_mul] <;> apply hi <;> fun_prop
    rw [he]
    simp only [kepFixedBridge, kepFixedBridgeRight, kepBridgeTransportFlux]
    change -(∫ z in Ioc 0 w, A z * p' s (y - z)) =
      A w * p s (y - w) - A 0 * p s y -
        (∫ z in Ioc 0 w, A' z * p s (y - z)) at hIBP
    have hbound : A w * p s (y - w) - A 0 * p s y =
        -(w - x - (n + 1 : ℕ) * σ) * kepFixedBridge p w s n x w * p s (y - w) +
          (-x - (n + 1 : ℕ) * σ) * kepFixedBridge p w s n x 0 * p s y := by
      dsimp [A]
      ring
    rw [hbound] at hIBP
    push_cast
    push_cast at hIBP
    linear_combination hIBP

end

end PGM
