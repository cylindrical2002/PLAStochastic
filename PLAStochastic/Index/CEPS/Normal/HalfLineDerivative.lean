import PLAStochastic.Index.CEPS.Normal.Algebra
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Half-line total derivative

All drift derivatives here are real derivatives of complex-valued functions.
The algebraic differential identity uses root-equation derivatives and the
transport identity; it does not assume holomorphy in complex drift. Nonzero
root derivative and discount denominator are explicit. Zero-denominator
extensions are not supplied by this file.
-/

noncomputable section
set_option maxHeartbeats 800000
open Complex Filter Topology
namespace PGM

/-- Differentiating the marked root equation gives (P9). -/
theorem cepsNormal_marked_root_derivative {B : ℝ → ℂ} {ψ : ℂ → ℂ}
    {μ : ℝ} {t b' p : ℂ} (hB : HasDerivAt B b' μ)
    (hψ : HasDerivAt ψ (p - μ) (B μ))
    (hroot : ∀ᶠ x in 𝓝 μ, ψ (B x) + (x : ℂ) * B x = t * (1 + x))
    (hp : p ≠ 0) : b' = -(B μ - t) / p := by
  have hm : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 μ := (hasDerivAt_id μ).ofReal_comp
  have hleft := (hψ.comp μ hB).add (hm.mul hB)
  have hright : HasDerivAt (fun x : ℝ => t * (1 + (x : ℂ))) t μ := by
    simpa using (hm.const_add 1).const_mul t
  have he := (hleft.congr_of_eventuallyEq (EventuallyEq.symm hroot)).unique hright
  apply (eq_div_iff hp).2
  linear_combination he

/-- The fixed-discount root equation gives the drift derivative in (F7). -/
theorem cepsNormal_fixed_root_derivative {B : ℝ → ℂ} {ψ : ℂ → ℂ}
    {μ : ℝ} {q b' p : ℂ} (hB : HasDerivAt B b' μ)
    (hψ : HasDerivAt ψ (p - μ) (B μ))
    (hroot : ∀ᶠ x in 𝓝 μ, ψ (B x) + (x : ℂ) * B x = q)
    (hp : p ≠ 0) : b' = -B μ / p := by
  have hm : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 μ := (hasDerivAt_id μ).ofReal_comp
  have hleft := (hψ.comp μ hB).add (hm.mul hB)
  have he := (hleft.congr_of_eventuallyEq (EventuallyEq.symm hroot)).unique (hasDerivAt_const μ q)
  apply (eq_div_iff hp).2
  linear_combination he

/-- Algebraic consequence of the transport equation at `t` and `β`. -/
theorem cepsNormal_marked_transport {β t p e Lμt Lqt Lμb Lqb Lzb : ℂ}
    (hp : p ≠ 0) (ht : Lμt + t * Lqt = e) (hb : Lμb + β * Lqb = e) :
    Lμt + t * Lqt = e ∧
      Lμb + t * Lqb + Lzb * (-(β - t) / p) =
        e - (β - t) * (Lqb + Lzb / p) := by
  refine ⟨ht, ?_⟩
  field_simp
  linear_combination p * hb

/-- The analytic product/quotient calculation behind (P12) and (F10). -/
theorem cepsNormal_halfline_primitive_hasDerivAt
    {B P T C d : ℝ → ℂ} {μ : ℝ} {t w p₂ s e : ℂ}
    (hB : HasDerivAt B (-(B μ - t) / P μ) μ)
    (hP : HasDerivAt P (1 - (B μ - t) * p₂ / P μ) μ)
    (hT : HasDerivAt T e μ)
    (hC : HasDerivAt C (e - (B μ - t) * s) μ)
    (hd : HasDerivAt d 0 μ) (hP0 : P μ ≠ 0) (hd0 : d μ ≠ 0) :
    HasDerivAt
      (fun x : ℝ => (B x - t) * P x / d x ^ 2 *
        exp (2 * T x - 2 * C x - (B x - t) * (w * (1 + x))))
      ((B μ - t) ^ 2 * P μ / d μ ^ 2 *
        exp (2 * T μ - 2 * C μ - (B μ - t) * (w * (1 + μ))) *
        (-p₂ / P μ ^ 2 + 2 * s + (w * (1 + μ)) / P μ - w)) μ := by
  have hm : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 μ := (hasDerivAt_id μ).ofReal_comp
  have hl : HasDerivAt (fun x : ℝ => w * (1 + (x : ℂ))) w μ := by
    simpa using (hm.const_add 1).const_mul w
  have hE := ((hT.const_mul 2).sub (hC.const_mul 2)).sub ((hB.sub_const t).mul hl)
  have hF := (((hB.sub_const t).mul hP).div (hd.pow 2) (pow_ne_zero 2 hd0)).mul hE.cexp
  refine hF.congr_deriv ?_
  dsimp
  field_simp [hP0, hd0]
  ring

/-- The fixed-`(μ,l,t)` discount derivative of the half-line bridge. -/
theorem cepsNormal_halfBridge_hasDerivAt {B P C : ℂ → ℂ} {q l p₂ s : ℂ}
    (hB : HasDerivAt B (1 / P q) q)
    (hP : HasDerivAt P (p₂ / P q) q)
    (hC : HasDerivAt C s q) (hP0 : P q ≠ 0) :
    HasDerivAt (fun q' => P q' * exp (-B q' * l - 2 * C q'))
      (P q * exp (-B q * l - 2 * C q) * (p₂ / P q ^ 2 - l / P q - 2 * s)) q := by
  have h := hP.mul (((hB.neg.mul_const l).sub (hC.const_mul 2)).cexp)
  refine h.congr_deriv ?_
  dsimp
  field_simp [hP0]
  ring

/-- Half-line occupation pair at arbitrary fixed parameter coordinates. -/
def cepsNormalHalfPairAt (A : ℂ → ℂ → CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ)
    (μ q t w : ℂ) : ℂ :=
  let l := w * (1 + μ)
  exp (t * l) * ((A μ q).halfEntrance L μ q t) ^ 2 *
    (-deriv (fun q' => (A μ q').halfBridge L μ q' l) q -
      w * (A μ q).halfBridge L μ q l)

/-- (P12)/(F10), with the removable factor `β-t` cancelled in the primitive.

The discount derivative is at fixed `(μ,l,t)`. The drift derivative is along
`Qcurve`, with `l = w(1+μ)`. Root and transport path jets are explicit.
-/
theorem cepsNormal_halfPair_totalDerivative
    (B P : ℝ → ℂ → ℂ) (d : ℝ → ℂ → ℂ → ℂ)
    (L : ℂ → ℂ → ℂ → ℂ) (Qcurve : ℝ → ℂ)
    (μ : ℝ) (t w p₂ s e : ℂ)
    (hB : HasDerivAt (fun x : ℝ => B x (Qcurve x))
      (-(B μ (Qcurve μ) - t) / P μ (Qcurve μ)) μ)
    (hP : HasDerivAt (fun x : ℝ => P x (Qcurve x))
      (1 - (B μ (Qcurve μ) - t) * p₂ / P μ (Qcurve μ)) μ)
    (hT : HasDerivAt (fun x : ℝ => L (x : ℂ) (Qcurve x) t) e μ)
    (hC : HasDerivAt (fun x : ℝ => L (x : ℂ) (Qcurve x) (B x (Qcurve x)))
      (e - (B μ (Qcurve μ) - t) * s) μ)
    (hd : HasDerivAt (fun x : ℝ => d x (Qcurve x) t) 0 μ)
    (hBq : HasDerivAt (B μ) (1 / P μ (Qcurve μ)) (Qcurve μ))
    (hPq : HasDerivAt (P μ) (p₂ / P μ (Qcurve μ)) (Qcurve μ))
    (hCq : HasDerivAt (fun q' => L (μ : ℂ) q' (B μ q')) s (Qcurve μ))
    (hP0 : P μ (Qcurve μ) ≠ 0) (hd0 : d μ (Qcurve μ) t ≠ 0) :
    HasDerivAt
      (fun x : ℝ => (B x (Qcurve x) - t) * P x (Qcurve x) / d x (Qcurve x) t ^ 2 *
        exp (2 * L (x : ℂ) (Qcurve x) t - 2 * L (x : ℂ) (Qcurve x) (B x (Qcurve x)) -
          (B x (Qcurve x) - t) * (w * (1 + (x : ℂ)))))
      (exp (t * (w * (1 + (μ : ℂ)))) *
        (exp (L (μ : ℂ) (Qcurve μ) t) * (B μ (Qcurve μ) - t) / d μ (Qcurve μ) t) ^ 2 *
        (-deriv (fun q' => P μ q' * exp (-B μ q' * (w * (1 + (μ : ℂ))) -
          2 * L (μ : ℂ) q' (B μ q'))) (Qcurve μ) -
          w * (P μ (Qcurve μ) * exp (-B μ (Qcurve μ) * (w * (1 + (μ : ℂ))) -
            2 * L (μ : ℂ) (Qcurve μ) (B μ (Qcurve μ)))))) μ := by
  have hF := cepsNormal_halfline_primitive_hasDerivAt
    (B := fun x => B x (Qcurve x)) (P := fun x => P x (Qcurve x))
    (T := fun x => L (x : ℂ) (Qcurve x) t)
    (C := fun x => L (x : ℂ) (Qcurve x) (B x (Qcurve x)))
    (d := fun x => d x (Qcurve x) t) (μ := μ) (t := t) (w := w)
    (p₂ := p₂) (s := s) (e := e)
    hB hP hT hC hd hP0 hd0
  have hU := cepsNormal_halfBridge_hasDerivAt (B := B μ) (P := P μ)
    (C := fun q' => L (μ : ℂ) q' (B μ q')) (q := Qcurve μ)
    (p₂ := p₂) (s := s) (l := w * (1 + (μ : ℂ)))
    hBq hPq hCq hP0
  refine hF.congr_deriv ?_
  rw [hU.deriv]
  rw [div_pow, mul_pow]
  have hE :
      exp (2 * L (μ : ℂ) (Qcurve μ) t - 2 * L (μ : ℂ) (Qcurve μ) (B μ (Qcurve μ)) -
        (B μ (Qcurve μ) - t) * (w * (1 + (μ : ℂ)))) =
      exp (t * (w * (1 + (μ : ℂ)))) * exp (L (μ : ℂ) (Qcurve μ) t) ^ 2 *
        exp (-B μ (Qcurve μ) * (w * (1 + (μ : ℂ))) -
          2 * L (μ : ℂ) (Qcurve μ) (B μ (Qcurve μ))) := by
    have h2 := exp_nat_mul (L (μ : ℂ) (Qcurve μ) t) 2
    norm_num at h2
    rw [← h2, ← exp_add, ← exp_add]
    congr 1
    ring
  rw [hE]
  ring

end PGM
