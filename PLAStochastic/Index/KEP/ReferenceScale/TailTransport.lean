import PLAStochastic.Index.KEP.ReferenceScale.BridgePins

/-!
# Weak transport of exterior killed tails, including the terminal pins

Unlike a bridge, a tail includes its terminal position in the band integral.
The zero-step tail is evaluation at its starting point, hence a Dirac measure.
The boundary flux includes the last pin with precisely this zero-step suffix.
All derivatives below are derivatives of the actual compact integrals.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

def kepTailTest (p : ℝ → ℝ → ℝ) (w s : ℝ) (n : ℕ) (x : ℝ)
    (φ : ℝ → ℝ) : ℝ :=
  match n with
  | 0 => φ x
  | n + 1 => ∫ y in Ioc 0 w, kepFixedBridge p w s n x y * φ y

def kepTailSlopeTest (p q : ℝ → ℝ → ℝ) (w s : ℝ) (n : ℕ) (x : ℝ)
    (φ : ℝ → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n + 1 => ∫ y in Ioc 0 w, kepFixedBridgeSlope p q w s n x y * φ y

def kepTailFluxTest (p : ℝ → ℝ → ℝ) (w σ s : ℝ) (n : ℕ) (x : ℝ)
    (φ : ℝ → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n + 1 =>
      -(∫ y in Ioc 0 w, kepBridgeTransportFlux p w σ s n x y * φ y) -
        (w - x - (n + 1 : ℕ) * σ) * kepFixedBridge p w s n x w * φ w +
        (-x - (n + 1 : ℕ) * σ) * kepFixedBridge p w s n x 0 * φ 0

theorem kepTailTest_zero (p : ℝ → ℝ → ℝ) (w s x : ℝ) (φ : ℝ → ℝ) :
    kepTailTest p w s 0 x φ = φ x := rfl

theorem kepTailTest_dirac (p : ℝ → ℝ → ℝ) (w s x : ℝ) (φ : ℝ → ℝ) :
    kepTailTest p w s 0 x φ = ∫ y, φ y ∂Measure.dirac x := by
  simp [kepTailTest]

theorem kepTailTest_add {p : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (w s : ℝ) (n : ℕ) (x : ℝ)
    {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) :
    kepTailTest p w s n x (φ + ψ) =
      kepTailTest p w s n x φ + kepTailTest p w s n x ψ := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [kepTailTest, Pi.add_apply, mul_add]
    have hk : Continuous (kepFixedBridge p w s n x) :=
      (continuous_kepFixedBridge hp w n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    exact integral_add ((hk.mul hφ).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      ((hk.mul hψ).integrableOn_Icc.mono_set Ioc_subset_Icc_self)

theorem kepTailTest_const_mul (p : ℝ → ℝ → ℝ) (w s : ℝ) (n : ℕ) (x c : ℝ)
    (φ : ℝ → ℝ) :
    kepTailTest p w s n x (fun y => c * φ y) = c * kepTailTest p w s n x φ := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [kepTailTest, mul_left_comm _ c, integral_const_mul]

/-- Weak continuity equation in logarithmic slope. The terminal boundary
contribution is retained, with a Dirac suffix rather than a density suffix. -/
theorem kepTailSlopeTest_transport {p p' q : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hd : ∀ s t, HasDerivAt (p s) (p' s t) t)
    {σ : ℝ} (hward : ∀ s t, q s t = -p s t + (σ - t) * p' s t)
    {w : ℝ} (hw : 0 ≤ w) (s : ℝ) (n : ℕ) (x : ℝ)
    {φ φ' : ℝ → ℝ} (hφ : Continuous φ) (hφ' : Continuous φ')
    (hφd : ∀ y, HasDerivAt φ (φ' y) y) :
    kepTailSlopeTest p q w s n x φ =
      kepTailTest p w s n x (fun y => (y - x - (n : ℝ) * σ) * φ' y) +
        kepTailFluxTest p w σ s n x φ := by
  cases n with
  | zero => simp [kepTailSlopeTest, kepTailTest, kepTailFluxTest]
  | succ n =>
    let K := kepFixedBridge p w s n x
    let K' := kepFixedBridgeRight p p' w s n x
    let B := kepBridgeTransportFlux p w σ s n x
    let c : ℝ → ℝ := fun y => (n + 1 : ℕ) * σ + x - y
    have hK : Continuous K :=
      (continuous_kepFixedBridge hp w n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    have hK' : Continuous K' :=
      (continuous_kepFixedBridgeRight hp hp' w n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    have hB : Continuous B :=
      (continuous_kepBridgeTransportFlux hp w σ n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    have hc : Continuous c := by dsimp [c]; fun_prop
    have hi (g : ℝ → ℝ) (hg : Continuous g) :
        Integrable g (volume.restrict (Ioc 0 w)) :=
      hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := 0) (b := w) (u := K) (u' := K')
      (v := fun y => c y * φ y) (v' := fun y => -φ y + c y * φ' y)
      (fun y _ => hasDerivAt_kepFixedBridge_right hp hp' hd w s n x y)
      (fun y _ => by
        convert (((hasDerivAt_const y ((n + 1 : ℕ) * σ + x)).sub
          (hasDerivAt_id y)).mul (hφd y)) using 1 <;>
          first | rfl | (dsimp [c]; ring))
      (hK'.intervalIntegrable 0 w)
      ((hφ.neg.add (hc.mul hφ')).intervalIntegrable 0 w)
    rw [intervalIntegral.integral_of_le hw, intervalIntegral.integral_of_le hw] at hIBP
    have hsplit : (∫ y in Ioc 0 w, K y * (-φ y + c y * φ' y)) =
        -(∫ y in Ioc 0 w, K y * φ y) +
          (∫ y in Ioc 0 w, K y * (c y * φ' y)) := by
      simp_rw [mul_add, mul_neg]
      rw [integral_add (f := fun y => -(K y * φ y))
        (g := fun y => K y * (c y * φ' y)) (hi _ (by fun_prop))
        (hi _ (by fun_prop)), integral_neg]
    rw [hsplit] at hIBP
    have hsplit' : kepTailSlopeTest p q w s (n + 1) x φ =
        -(∫ y in Ioc 0 w, K y * φ y) +
          (∫ y in Ioc 0 w, K' y * (c y * φ y)) -
          (∫ y in Ioc 0 w, B y * φ y) := by
      unfold kepTailSlopeTest
      simp_rw [kepFixedBridge_transport hp hp' hd hward hw]
      change (∫ y in Ioc 0 w, (-K y + c y * K' y - B y) * φ y) = _
      simp_rw [sub_mul, add_mul, neg_mul]
      rw [integral_sub (f := fun y => -(K y * φ y) + c y * K' y * φ y)
        (g := fun y => B y * φ y) (hi _ (by fun_prop)) (hi _ (by fun_prop)),
        integral_add (f := fun y => -(K y * φ y))
        (g := fun y => c y * K' y * φ y) (hi _ (by fun_prop))
        (hi _ (by fun_prop)), integral_neg]
      congr 2
      apply integral_congr_ae
      exact ae_of_all _ fun y => by dsimp only; ring
    rw [hsplit']
    have hneg : kepTailTest p w s (n + 1) x
        (fun y => (y - x - (n + 1 : ℕ) * σ) * φ' y) =
        -(∫ y in Ioc 0 w, K y * (c y * φ' y)) := by
      unfold kepTailTest
      rw [← integral_neg]
      apply integral_congr_ae
      exact ae_of_all _ fun y => by dsimp [K, c]; ring
    rw [hneg]
    dsimp [kepTailFluxTest, K, c] at *
    linarith

set_option backward.isDefEq.respectTransparency.types false in
/-- Moving tests: both the test derivative and the weak transport are actual
derivatives. The zero-step case includes the slope derivative of the test. -/
theorem hasDerivAt_kepTailTest {p q Φ Φs : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hq : Continuous (Function.uncurry q))
    (hpd : ∀ s t, HasDerivAt (fun r => p r t) (q s t) s)
    (hΦ : Continuous (Function.uncurry Φ)) (hΦs : Continuous (Function.uncurry Φs))
    (hΦd : ∀ s y, HasDerivAt (fun r => Φ r y) (Φs s y) s)
    (w s : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun r => kepTailTest p w r n x (Φ r))
      (kepTailTest p w s n x (Φs s) + kepTailSlopeTest p q w s n x (Φ s)) s := by
  cases n with
  | zero => simpa only [kepTailTest, kepTailSlopeTest, add_zero] using hΦd s x
  | succ n =>
    have hK : Continuous (fun t : ℝ × ℝ => kepFixedBridge p w t.1 n x t.2) :=
      (continuous_kepFixedBridge hp w n).comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
    have hKs : Continuous (fun t : ℝ × ℝ => kepFixedBridgeSlope p q w t.1 n x t.2) :=
      (continuous_kepFixedBridgeSlope hp hq w n).comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
    have hh := hasDerivAt_integral_Ioc_of_continuous
      (F := fun r y => kepFixedBridge p w r n x y * Φ r y)
      (F' := fun r y => kepFixedBridgeSlope p q w r n x y * Φ r y +
        kepFixedBridge p w r n x y * Φs r y)
      (hK.mul hΦ) ((hKs.mul hΦ).add (hK.mul hΦs))
      (fun r y => (hasDerivAt_kepFixedBridge_slope hp hq hpd w r n x y).mul (hΦd r y))
      0 w s
    have hk : Continuous (kepFixedBridge p w s n x) :=
      hK.comp (continuous_const.prodMk continuous_id)
    have hks : Continuous (kepFixedBridgeSlope p q w s n x) :=
      hKs.comp (continuous_const.prodMk continuous_id)
    have hφ : Continuous (Φ s) := hΦ.comp (continuous_const.prodMk continuous_id)
    have hφs : Continuous (Φs s) := hΦs.comp (continuous_const.prodMk continuous_id)
    rw [integral_add
      (f := fun y => kepFixedBridgeSlope p q w s n x y * Φ s y)
      (g := fun y => kepFixedBridge p w s n x y * Φs s y)
      ((hks.mul hφ).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      ((hk.mul hφs).integrableOn_Icc.mono_set Ioc_subset_Icc_self), add_comm] at hh
    exact hh

end

end PGM
