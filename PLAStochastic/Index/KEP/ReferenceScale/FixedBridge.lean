import PLAStochastic.ForMathlib.Analysis.Calculus.CompactIntervalDerivative
import PLAStochastic.Index.KEP.ReferenceScale.KernelWard

/-!
# Smooth fixed-endpoint representatives of the actual killed bridges

`kepFixedBridge p w s n` has `n + 1` steps. Only the intermediate positions
are integrated over the band. The endpoint indicators are restored by the
identification with `krDens` on the band. Thus endpoint derivatives belong to
this smooth representative, without differentiating an interval indicator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepFixedBridge (p : ℝ → ℝ → ℝ) (w s : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, x, y => p s (y - x)
  | n + 1, x, y => ∫ z in Ioc 0 w, kepFixedBridge p w s n x z * p s (y - z)

def kepFixedBridgeRight (p p' : ℝ → ℝ → ℝ) (w s : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, x, y => p' s (y - x)
  | n + 1, x, y => ∫ z in Ioc 0 w, kepFixedBridge p w s n x z * p' s (y - z)

def kepFixedBridgeLeft (p p' : ℝ → ℝ → ℝ) (w s : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, x, y => -p' s (y - x)
  | n + 1, x, y => ∫ z in Ioc 0 w,
      kepFixedBridgeLeft p p' w s n x z * p s (y - z)

def kepFixedBridgeSlope (p q : ℝ → ℝ → ℝ) (w s : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, x, y => q s (y - x)
  | n + 1, x, y => ∫ z in Ioc 0 w,
      kepFixedBridgeSlope p q w s n x z * p s (y - z) +
        kepFixedBridge p w s n x z * q s (y - z)

theorem kepFixedBridge_congr_at {p q : ℝ → ℝ → ℝ} {s t : ℝ}
    (hpq : ∀ z, p s z = q t z) (w : ℝ) (n : ℕ) (x y : ℝ) :
    kepFixedBridge p w s n x y = kepFixedBridge q w t n x y := by
  induction n generalizing x y with
  | zero => exact hpq (y - x)
  | succ n ih =>
    simp only [kepFixedBridge]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by dsimp only; rw [ih x z, hpq]

theorem continuous_kepFixedBridge {p : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (w : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ × ℝ × ℝ => kepFixedBridge p w t.1 n t.2.1 t.2.2) := by
  induction n with
  | zero =>
    exact hp.comp (continuous_fst.prodMk (continuous_snd.snd.sub continuous_snd.fst))
  | succ n ih =>
    apply continuous_integral_Ioc_of_continuous (a := 0) (b := w)
    exact (ih.comp (continuous_fst.fst.prodMk
      (continuous_fst.snd.fst.prodMk continuous_snd))).mul
      (hp.comp (continuous_fst.fst.prodMk (continuous_fst.snd.snd.sub continuous_snd)))

theorem continuous_kepFixedBridgeRight {p p' : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (w : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ × ℝ × ℝ => kepFixedBridgeRight p p' w t.1 n t.2.1 t.2.2) := by
  cases n with
  | zero =>
    exact hp'.comp (continuous_fst.prodMk (continuous_snd.snd.sub continuous_snd.fst))
  | succ n =>
    apply continuous_integral_Ioc_of_continuous (a := 0) (b := w)
    exact ((continuous_kepFixedBridge hp w n).comp (continuous_fst.fst.prodMk
      (continuous_fst.snd.fst.prodMk continuous_snd))).mul
      (hp'.comp (continuous_fst.fst.prodMk (continuous_fst.snd.snd.sub continuous_snd)))

theorem continuous_kepFixedBridgeLeft {p p' : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (w : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ × ℝ × ℝ => kepFixedBridgeLeft p p' w t.1 n t.2.1 t.2.2) := by
  induction n with
  | zero =>
    exact (hp'.comp
      (continuous_fst.prodMk (continuous_snd.snd.sub continuous_snd.fst))).neg
  | succ n ih =>
    apply continuous_integral_Ioc_of_continuous (a := 0) (b := w)
    exact (ih.comp (continuous_fst.fst.prodMk
      (continuous_fst.snd.fst.prodMk continuous_snd))).mul
      (hp.comp (continuous_fst.fst.prodMk (continuous_fst.snd.snd.sub continuous_snd)))

theorem continuous_kepFixedBridgeSlope {p q : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hq : Continuous (Function.uncurry q))
    (w : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ × ℝ × ℝ => kepFixedBridgeSlope p q w t.1 n t.2.1 t.2.2) := by
  induction n with
  | zero =>
    exact hq.comp (continuous_fst.prodMk (continuous_snd.snd.sub continuous_snd.fst))
  | succ n ih =>
    apply continuous_integral_Ioc_of_continuous (a := 0) (b := w)
    exact ((ih.comp (continuous_fst.fst.prodMk
      (continuous_fst.snd.fst.prodMk continuous_snd))).mul
      (hp.comp (continuous_fst.fst.prodMk (continuous_fst.snd.snd.sub continuous_snd)))).add
      (((continuous_kepFixedBridge hp w n).comp (continuous_fst.fst.prodMk
        (continuous_fst.snd.fst.prodMk continuous_snd))).mul
        (hq.comp (continuous_fst.fst.prodMk (continuous_fst.snd.snd.sub continuous_snd))))

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_kepFixedBridge_right {p p' : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hd : ∀ s t, HasDerivAt (p s) (p' s t) t) (w s : ℝ) (n : ℕ) (x y : ℝ) :
    HasDerivAt (kepFixedBridge p w s n x) (kepFixedBridgeRight p p' w s n x y) y := by
  cases n with
  | zero =>
    simpa only [kepFixedBridge, kepFixedBridgeRight, sub_zero, mul_one,
      Function.comp_def, id_eq] using
      (hd s (y - x)).comp y ((hasDerivAt_id y).sub_const x)
  | succ n =>
    simp only [kepFixedBridge, kepFixedBridgeRight]
    refine hasDerivAt_integral_Ioc_of_continuous
      (F := fun t z => kepFixedBridge p w s n x z * p s (t - z))
      (F' := fun t z => kepFixedBridge p w s n x z * p' s (t - z)) ?_ ?_ ?_ 0 w y
    · exact ((continuous_kepFixedBridge hp w n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_snd))).mul
        (hp.comp (continuous_const.prodMk (continuous_fst.sub continuous_snd)))
    · exact ((continuous_kepFixedBridge hp w n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_snd))).mul
        (hp'.comp (continuous_const.prodMk (continuous_fst.sub continuous_snd)))
    · intro t z
      simpa only [sub_zero, mul_one, Function.comp_def, id_eq] using
        (((hd s (t - z)).comp t ((hasDerivAt_id t).sub_const z)).const_mul
          (kepFixedBridge p w s n x z))

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_kepFixedBridge_left {p p' : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hd : ∀ s t, HasDerivAt (p s) (p' s t) t) (w s : ℝ) (n : ℕ) (x y : ℝ) :
    HasDerivAt (fun t => kepFixedBridge p w s n t y)
      (kepFixedBridgeLeft p p' w s n x y) x := by
  induction n generalizing x y with
  | zero =>
    simpa only [kepFixedBridge, kepFixedBridgeLeft, zero_sub, mul_neg_one,
      Function.comp_def, id_eq] using
      (hd s (y - x)).comp x ((hasDerivAt_const x y).sub (hasDerivAt_id x))
  | succ n ih =>
    simp only [kepFixedBridge, kepFixedBridgeLeft]
    refine hasDerivAt_integral_Ioc_of_continuous
      (F := fun t z => kepFixedBridge p w s n t z * p s (y - z))
      (F' := fun t z => kepFixedBridgeLeft p p' w s n t z * p s (y - z)) ?_ ?_ ?_ 0 w x
    · exact ((continuous_kepFixedBridge hp w n).comp
        (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))).mul
        (hp.comp (continuous_const.prodMk (continuous_const.sub continuous_snd)))
    · exact ((continuous_kepFixedBridgeLeft hp hp' w n).comp
        (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))).mul
        (hp.comp (continuous_const.prodMk (continuous_const.sub continuous_snd)))
    · intro t z
      exact (ih t z).mul_const (p s (y - z))

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_kepFixedBridge_slope {p q : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hq : Continuous (Function.uncurry q))
    (hd : ∀ s t, HasDerivAt (fun r => p r t) (q s t) s)
    (w s : ℝ) (n : ℕ) (x y : ℝ) :
    HasDerivAt (fun r => kepFixedBridge p w r n x y)
      (kepFixedBridgeSlope p q w s n x y) s := by
  induction n generalizing s x y with
  | zero => exact hd s (y - x)
  | succ n ih =>
    simp only [kepFixedBridge, kepFixedBridgeSlope]
    refine hasDerivAt_integral_Ioc_of_continuous
      (F := fun t z => kepFixedBridge p w t n x z * p t (y - z))
      (F' := fun t z => kepFixedBridgeSlope p q w t n x z * p t (y - z) +
        kepFixedBridge p w t n x z * q t (y - z)) ?_ ?_ ?_ 0 w s
    · exact ((continuous_kepFixedBridge hp w n).comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))).mul
        (hp.comp (continuous_fst.prodMk (continuous_const.sub continuous_snd)))
    · exact (((continuous_kepFixedBridgeSlope hp hq w n).comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))).mul
        (hp.comp (continuous_fst.prodMk (continuous_const.sub continuous_snd)))).add
        (((continuous_kepFixedBridge hp w n).comp
          (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))).mul
          (hq.comp (continuous_fst.prodMk (continuous_const.sub continuous_snd))))
    · intro t z
      exact (ih t x z).mul (hd t (y - z))

/-- Exact identification on the band, including its two endpoints. -/
theorem kepFixedBridge_eq_krDens (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {D w β a : ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (ha : a ≠ 0) (n : ℕ) {x y : ℝ} (hx : x ∈ Icc 0 w) (hy : y ∈ Icc 0 w) :
    kepFixedBridge (fun _ => kepStepSpatial f β a) w 0 n x y =
      krDens (Icc 0 w) ν f β a (n + 1) x y := by
  induction n generalizing y with
  | zero =>
    change kepStepSpatial f β a (y - x) = krDens (Icc 0 w) ν f β a 1 x y
    rw [krDens_one]
    simp only [krKer, indicator_of_mem hx,
      indicator_of_mem hy, one_mul, kepStepSpatial]
    rw [show β - (y - x) = x + β - y by ring]
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega,
      krDens_eq_kepFinalConvolution ν hf hf0 hfD hν ha n x hy]
    unfold kepFinalConvolution truncatedConvolution
    rw [kepFixedBridge]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    dsimp only
    rw [ih ⟨hz.1.le, hz.2⟩, mul_comm]

end

end PGM
