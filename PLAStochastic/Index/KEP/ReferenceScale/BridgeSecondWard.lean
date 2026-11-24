import PLAStochastic.Index.KEP.ReferenceScale.BridgePins

/-!
# Mixed and second logarithmic-slope Ward identities

Every differentiated pin term has a single first-derivative factor. The second
spatial derivative occurs only on the original bridge. All formulas are genuine
derivatives of the finite compact integrals, rather than assumed Ward interfaces.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

def kepFixedBridgeMixed (p p' q r : ℝ → ℝ → ℝ) (w s : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, x, y => r s (y - x)
  | n + 1, x, y => ∫ z in Ioc 0 w,
      kepFixedBridgeSlope p q w s n x z * p' s (y - z) +
        kepFixedBridge p w s n x z * r s (y - z)

def kepBridgeFluxRight (p p' : ℝ → ℝ → ℝ) (w σ s : ℝ) (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ l ∈ Finset.range n,
    ((w - x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x w *
        kepFixedBridgeRight p p' w s (n - 1 - l) w y -
      (-x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x 0 *
        kepFixedBridgeRight p p' w s (n - 1 - l) 0 y)

def kepBridgeFluxSlope (p q : ℝ → ℝ → ℝ) (w σ s : ℝ) (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ l ∈ Finset.range n,
    ((w - x - (l + 1 : ℕ) * σ) *
        (kepFixedBridgeSlope p q w s l x w * kepFixedBridge p w s (n - 1 - l) w y +
          kepFixedBridge p w s l x w * kepFixedBridgeSlope p q w s (n - 1 - l) w y) -
      (-x - (l + 1 : ℕ) * σ) *
        (kepFixedBridgeSlope p q w s l x 0 * kepFixedBridge p w s (n - 1 - l) 0 y +
          kepFixedBridge p w s l x 0 * kepFixedBridgeSlope p q w s (n - 1 - l) 0 y))

theorem continuous_kepFixedBridgeMixed {p p' q r : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hq : Continuous (Function.uncurry q)) (hr : Continuous (Function.uncurry r))
    (w : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ × ℝ × ℝ => kepFixedBridgeMixed p p' q r w t.1 n t.2.1 t.2.2) := by
  cases n with
  | zero => exact hr.comp (continuous_fst.prodMk (continuous_snd.snd.sub continuous_snd.fst))
  | succ n =>
    apply continuous_integral_Ioc_of_continuous (a := 0) (b := w)
    exact (((continuous_kepFixedBridgeSlope hp hq w n).comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.fst.prodMk continuous_snd))).mul
      (hp'.comp (continuous_fst.fst.prodMk (continuous_fst.snd.snd.sub continuous_snd)))).add
      (((continuous_kepFixedBridge hp w n).comp
        (continuous_fst.fst.prodMk (continuous_fst.snd.fst.prodMk continuous_snd))).mul
        (hr.comp (continuous_fst.fst.prodMk (continuous_fst.snd.snd.sub continuous_snd))))

theorem hasDerivAt_kepFixedBridgeRight_right {p p' p'' : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hp'' : Continuous (Function.uncurry p''))
    (hdd : ∀ s t, HasDerivAt (p' s) (p'' s t) t)
    (w s : ℝ) (n : ℕ) (x y : ℝ) :
    HasDerivAt (kepFixedBridgeRight p p' w s n x)
      (kepFixedBridgeRight p p'' w s n x y) y := by
  cases n with
  | zero =>
    change HasDerivAt (fun t => p' s (t - x)) (p'' s (y - x)) y
    simpa only [kepFixedBridgeRight, Function.comp_def, id_eq, sub_zero, mul_one] using
      (hdd s (y - x)).comp y ((hasDerivAt_id y).sub_const x)
  | succ n =>
    simp only [kepFixedBridgeRight]
    refine hasDerivAt_integral_Ioc_of_continuous
      (F := fun t z => kepFixedBridge p w s n x z * p' s (t - z))
      (F' := fun t z => kepFixedBridge p w s n x z * p'' s (t - z)) ?_ ?_ ?_ 0 w y
    · exact ((continuous_kepFixedBridge hp w n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_snd))).mul
        (hp'.comp (continuous_const.prodMk (continuous_fst.sub continuous_snd)))
    · exact ((continuous_kepFixedBridge hp w n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_snd))).mul
        (hp''.comp (continuous_const.prodMk (continuous_fst.sub continuous_snd)))
    · intro t z
      simpa only [Function.comp_def, id_eq, sub_zero, mul_one, Pi.add_def] using
        (((hdd s (t - z)).comp t ((hasDerivAt_id t).sub_const z)).const_mul
          (kepFixedBridge p w s n x z))

theorem hasDerivAt_kepFixedBridgeRight_slope {p p' q r : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hq : Continuous (Function.uncurry q)) (hr : Continuous (Function.uncurry r))
    (hds : ∀ s t, HasDerivAt (fun v => p v t) (q s t) s)
    (hdt : ∀ s t, HasDerivAt (fun v => p' v t) (r s t) s)
    (w s : ℝ) (n : ℕ) (x y : ℝ) :
    HasDerivAt (fun v => kepFixedBridgeRight p p' w v n x y)
      (kepFixedBridgeMixed p p' q r w s n x y) s := by
  cases n with
  | zero => exact hdt s (y - x)
  | succ n =>
    simp only [kepFixedBridgeRight, kepFixedBridgeMixed]
    refine hasDerivAt_integral_Ioc_of_continuous
      (F := fun t z => kepFixedBridge p w t n x z * p' t (y - z))
      (F' := fun t z => kepFixedBridgeSlope p q w t n x z * p' t (y - z) +
        kepFixedBridge p w t n x z * r t (y - z)) ?_ ?_ ?_ 0 w s
    · exact ((continuous_kepFixedBridge hp w n).comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))).mul
        (hp'.comp (continuous_fst.prodMk (continuous_const.sub continuous_snd)))
    · exact (((continuous_kepFixedBridgeSlope hp hq w n).comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))).mul
        (hp'.comp (continuous_fst.prodMk (continuous_const.sub continuous_snd)))).add
        (((continuous_kepFixedBridge hp w n).comp
          (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))).mul
          (hr.comp (continuous_fst.prodMk (continuous_const.sub continuous_snd))))
    · intro t z
      exact (hasDerivAt_kepFixedBridge_slope hp hq hds w t n x z).mul (hdt t (y - z))

theorem hasDerivAt_kepFixedBridgeSlope_right {p p' q r : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hq : Continuous (Function.uncurry q)) (hr : Continuous (Function.uncurry r))
    (hdy : ∀ s t, HasDerivAt (p s) (p' s t) t)
    (hqt : ∀ s t, HasDerivAt (q s) (r s t) t)
    (w s : ℝ) (n : ℕ) (x y : ℝ) :
    HasDerivAt (kepFixedBridgeSlope p q w s n x)
      (kepFixedBridgeMixed p p' q r w s n x y) y := by
  cases n with
  | zero =>
    simpa only [kepFixedBridgeSlope, kepFixedBridgeMixed, Function.comp_def,
      id_eq, sub_zero, mul_one] using
      (hqt s (y - x)).comp y ((hasDerivAt_id y).sub_const x)
  | succ n =>
    simp only [kepFixedBridgeSlope, kepFixedBridgeMixed]
    refine hasDerivAt_integral_Ioc_of_continuous
      (F := fun t z => kepFixedBridgeSlope p q w s n x z * p s (t - z) +
        kepFixedBridge p w s n x z * q s (t - z))
      (F' := fun t z => kepFixedBridgeSlope p q w s n x z * p' s (t - z) +
        kepFixedBridge p w s n x z * r s (t - z)) ?_ ?_ ?_ 0 w y
    · exact (((continuous_kepFixedBridgeSlope hp hq w n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_snd))).mul
        (hp.comp (continuous_const.prodMk (continuous_fst.sub continuous_snd)))).add
        (((continuous_kepFixedBridge hp w n).comp
          (continuous_const.prodMk (continuous_const.prodMk continuous_snd))).mul
          (hq.comp (continuous_const.prodMk (continuous_fst.sub continuous_snd))))
    · exact (((continuous_kepFixedBridgeSlope hp hq w n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_snd))).mul
        (hp'.comp (continuous_const.prodMk (continuous_fst.sub continuous_snd)))).add
        (((continuous_kepFixedBridge hp w n).comp
          (continuous_const.prodMk (continuous_const.prodMk continuous_snd))).mul
          (hr.comp (continuous_const.prodMk (continuous_fst.sub continuous_snd))))
    · intro t z
      simpa only [Function.comp_def, id_eq, sub_zero, mul_one, Pi.add_def] using
        ((((hdy s (t - z)).comp t ((hasDerivAt_id t).sub_const z)).const_mul
          (kepFixedBridgeSlope p q w s n x z)).add
          (((hqt s (t - z)).comp t ((hasDerivAt_id t).sub_const z)).const_mul
            (kepFixedBridge p w s n x z)))

theorem hasDerivAt_kepBridgeTransportFlux_right {p p' : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hdy : ∀ s t, HasDerivAt (p s) (p' s t) t)
    (w σ s : ℝ) (n : ℕ) (x y : ℝ) :
    HasDerivAt (kepBridgeTransportFlux p w σ s n x)
      (kepBridgeFluxRight p p' w σ s n x y) y := by
  have hh := HasDerivAt.fun_sum (u := Finset.range n) fun l _ =>
    ((hasDerivAt_kepFixedBridge_right hp hp' hdy w s (n - 1 - l) w y).const_mul
      ((w - x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x w)).sub
      ((hasDerivAt_kepFixedBridge_right hp hp' hdy w s (n - 1 - l) 0 y).const_mul
        ((-x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x 0))
  apply hh.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun z => kepBridgeTransportFlux_eq_sum hp w σ s n x z

theorem hasDerivAt_kepBridgeTransportFlux_slope {p q : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hq : Continuous (Function.uncurry q))
    (hds : ∀ s t, HasDerivAt (fun v => p v t) (q s t) s)
    (w σ s : ℝ) (n : ℕ) (x y : ℝ) :
    HasDerivAt (fun v => kepBridgeTransportFlux p w σ v n x y)
      (kepBridgeFluxSlope p q w σ s n x y) s := by
  have hh := HasDerivAt.fun_sum (u := Finset.range n) fun l _ =>
    (((hasDerivAt_kepFixedBridge_slope hp hq hds w s l x w).mul
      (hasDerivAt_kepFixedBridge_slope hp hq hds w s (n - 1 - l) w y)).const_mul
      (w - x - (l + 1 : ℕ) * σ)).sub
      (((hasDerivAt_kepFixedBridge_slope hp hq hds w s l x 0).mul
        (hasDerivAt_kepFixedBridge_slope hp hq hds w s (n - 1 - l) 0 y)).const_mul
        (-x - (l + 1 : ℕ) * σ))
  apply hh.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun z => by
    dsimp only
    rw [kepBridgeTransportFlux_eq_sum hp w σ z n x y]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring

theorem kepFixedBridge_mixed_ward {p p' p'' q r : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hp'' : Continuous (Function.uncurry p''))
    (hq : Continuous (Function.uncurry q)) (hr : Continuous (Function.uncurry r))
    (hdy : ∀ s t, HasDerivAt (p s) (p' s t) t)
    (hdd : ∀ s t, HasDerivAt (p' s) (p'' s t) t)
    (hqt : ∀ s t, HasDerivAt (q s) (r s t) t)
    {σ : ℝ} (hward : ∀ s t, q s t = -p s t + (σ - t) * p' s t)
    {w : ℝ} (hw : 0 ≤ w) (s : ℝ) (n : ℕ) (x y : ℝ) :
    kepFixedBridgeMixed p p' q r w s n x y =
      -2 * kepFixedBridgeRight p p' w s n x y +
        ((n + 1 : ℕ) * σ + x - y) * kepFixedBridgeRight p p'' w s n x y -
        kepBridgeFluxRight p p' w σ s n x y := by
  have hh := (((hasDerivAt_kepFixedBridge_right hp hp' hdy w s n x y).neg).add
    (((hasDerivAt_const y ((n + 1 : ℕ) * σ + x)).sub (hasDerivAt_id y)).mul
      (hasDerivAt_kepFixedBridgeRight_right hp hp' hp'' hdd w s n x y))).sub
      (hasDerivAt_kepBridgeTransportFlux_right hp hp' hdy w σ s n x y)
  have hfun : (-kepFixedBridge p w s n x +
      ((fun _ => (n + 1 : ℕ) * σ + x) - id) * kepFixedBridgeRight p p' w s n x -
      kepBridgeTransportFlux p w σ s n x) = kepFixedBridgeSlope p q w s n x := by
    funext z
    exact (kepFixedBridge_transport hp hp' hdy hward hw s n x z).symm
  rw [hfun] at hh
  have he := (hasDerivAt_kepFixedBridgeSlope_right hp hp' hq hr hdy hqt w s n x y).unique hh
  convert he using 1; first | rfl | (dsimp only [Pi.sub_apply, id_eq]; ring)

theorem hasDerivAt_kepFixedBridgeSlope_second_ward {p p' p'' q r : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hp'' : Continuous (Function.uncurry p''))
    (hq : Continuous (Function.uncurry q)) (hr : Continuous (Function.uncurry r))
    (hdy : ∀ s t, HasDerivAt (p s) (p' s t) t)
    (hdd : ∀ s t, HasDerivAt (p' s) (p'' s t) t)
    (hds : ∀ s t, HasDerivAt (fun v => p v t) (q s t) s)
    (hdt : ∀ s t, HasDerivAt (fun v => p' v t) (r s t) s)
    (hqt : ∀ s t, HasDerivAt (q s) (r s t) t)
    {σ : ℝ} (hward : ∀ s t, q s t = -p s t + (σ - t) * p' s t)
    {w : ℝ} (hw : 0 ≤ w) (s : ℝ) (n : ℕ) (x y : ℝ) :
    HasDerivAt (fun v => kepFixedBridgeSlope p q w v n x y)
      (kepFixedBridge p w s n x y -
        3 * ((n + 1 : ℕ) * σ + x - y) * kepFixedBridgeRight p p' w s n x y +
        ((n + 1 : ℕ) * σ + x - y) ^ 2 * kepFixedBridgeRight p p'' w s n x y +
        kepBridgeTransportFlux p w σ s n x y -
        ((n + 1 : ℕ) * σ + x - y) * kepBridgeFluxRight p p' w σ s n x y -
        kepBridgeFluxSlope p q w σ s n x y) s := by
  have hh := (((hasDerivAt_kepFixedBridge_slope hp hq hds w s n x y).neg).add
    ((hasDerivAt_kepFixedBridgeRight_slope hp hp' hq hr hds hdt w s n x y).const_mul
      ((n + 1 : ℕ) * σ + x - y))).sub
      (hasDerivAt_kepBridgeTransportFlux_slope hp hq hds w σ s n x y)
  have hfun : (fun v => -kepFixedBridge p w v n x y +
      ((n + 1 : ℕ) * σ + x - y) * kepFixedBridgeRight p p' w v n x y -
      kepBridgeTransportFlux p w σ v n x y) =
      (fun v => kepFixedBridgeSlope p q w v n x y) := by
    funext v
    exact (kepFixedBridge_transport hp hp' hdy hward hw v n x y).symm
  change HasDerivAt (fun v => -kepFixedBridge p w v n x y +
    ((n + 1 : ℕ) * σ + x - y) * kepFixedBridgeRight p p' w v n x y -
    kepBridgeTransportFlux p w σ v n x y) _ s at hh
  rw [hfun] at hh
  convert hh using 1; first | rfl |
    (rw [kepFixedBridge_transport hp hp' hdy hward hw s n x y,
      kepFixedBridge_mixed_ward hp hp' hp'' hq hr hdy hdd hqt hward hw s n x y]; ring)

end

end PGM
