import PLAStochastic.Index.KEP.ReferenceScale.GraphPins

/-!
# Two transfers on the original graph, and one transfer on a pinned graph

The twice-transferred original scalar has a genuine second derivative. A
first-flux pin scalar has only one derivative of its fixed bridge. The
original identity below retains the derivative test in the first flux; the
pin theorem transfers each such term when its updated numerator is positive.
No weighted norm or infinite-path estimate is claimed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

def kepGraphTransferredScalar (D : ℝ) (R R' : ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.exp s * (R s + R' s) / D

def kepGraphTransferredScalarFirst (D : ℝ) (R R' R'' : ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.exp s * (R s + 2 * R' s + R'' s) / D

theorem hasDerivAt_kepGraphTransferredScalar {R R' R'' : ℝ → ℝ}
    (hd : ∀ s, HasDerivAt R (R' s) s) (hdd : ∀ s, HasDerivAt R' (R'' s) s)
    (D s : ℝ) :
    HasDerivAt (kepGraphTransferredScalar D R R')
      (kepGraphTransferredScalarFirst D R R' R'' s) s := by
  convert ((Real.hasDerivAt_exp s).mul ((hd s).add (hdd s))).div_const D using 1 <;>
    first | rfl | (dsimp [kepGraphTransferredScalarFirst]; ring)

/-- Exact second original-graph identity. The last term is subsequently
expanded by `kepTailPairFlux_eq_pin_sums` and transferred pin by pin. -/
theorem kepLogGraphIntegral_second_transfer_with_flux
    (A : KepTailDynamics (-1)) (B : KepTailDynamics 1)
    {φ φ' φ'' R R' R'' : ℝ → ℝ}
    (hφ : Continuous φ) (hφ' : Continuous φ') (hφ'' : Continuous φ'')
    (hdφ : ∀ y, HasDerivAt φ (φ' y) y) (hddφ : ∀ y, HasDerivAt φ' (φ'' y) y)
    (hR : Continuous R) (hR' : Continuous R') (hR'' : Continuous R'')
    (hdR : ∀ s, HasDerivAt R (R' s) s) (hddR : ∀ s, HasDerivAt R' (R'' s) s)
    {w lo hi D : ℝ} (hw : 0 ≤ w) (hlh : lo ≤ hi) (hD : D ≠ 0)
    (hlo : R lo = 0) (hhi : R hi = 0) (hlo' : R' lo = 0) (hhi' : R' hi = 0)
    (i r : ℕ) (xA xB : ℝ) :
    kepLogGraphIntegral A.step B.step w lo hi D i r xA xB R φ'' =
      kepLogGraphIntegral A.step B.step w lo hi D i r xA xB
        (fun s => Real.exp (2 * s) * (2 * R s + 3 * R' s + R'' s) / D ^ 2) φ +
      kepLogGraphFluxIntegral A.step B.step w lo hi D i r xA xB
        (kepGraphTransferredScalar D R R') φ +
      kepLogGraphFluxIntegral A.step B.step w lo hi D i r xA xB R φ' := by
  have hQ : Continuous (kepGraphTransferredScalar D R R') :=
    (Real.continuous_exp.mul (hR.add hR')).div_const D
  have hQ' : Continuous (kepGraphTransferredScalarFirst D R R' R'') := by
    unfold kepGraphTransferredScalarFirst
    fun_prop
  have hzlo : kepGraphTransferredScalar D R R' lo = 0 := by
    simp [kepGraphTransferredScalar, hlo, hlo']
  have hzhi : kepGraphTransferredScalar D R R' hi = 0 := by
    simp [kepGraphTransferredScalar, hhi, hhi']
  have h1 := kepLogGraphIntegral_derivative_transfer A B hφ' hφ'' hddφ hR hR' hdR
    hw hlh hD hlo hhi i r xA xB
  have h2 := kepLogGraphIntegral_derivative_transfer A B hφ hφ' hdφ hQ hQ'
    (hasDerivAt_kepGraphTransferredScalar hdR hddR D) hw hlh hD hzlo hzhi i r xA xB
  change kepLogGraphIntegral A.step B.step w lo hi D i r xA xB R φ'' =
    kepLogGraphIntegral A.step B.step w lo hi D i r xA xB
      (kepGraphTransferredScalar D R R') φ' + _ at h1
  rw [h2] at h1
  have hscalar (s : ℝ) : Real.exp s * (kepGraphTransferredScalar D R R' s +
      kepGraphTransferredScalarFirst D R R' R'' s) / D =
      Real.exp (2 * s) * (2 * R s + 3 * R' s + R'' s) / D ^ 2 := by
    rw [show (2 : ℝ) * s = s + s by ring, Real.exp_add]
    dsimp [kepGraphTransferredScalar, kepGraphTransferredScalarFirst]
    field_simp [hD]
    ring
  simpa only [hscalar] using h1

def kepGraphPinScalar (p : ℝ → ℝ → ℝ) (w D d : ℝ) (l : ℕ) (x b : ℝ)
    (R : ℝ → ℝ) (s : ℝ) : ℝ :=
  (d / D) * Real.exp s * R s * kepFixedBridge p w s l x b

def kepGraphPinScalarFirst (p q : ℝ → ℝ → ℝ) (w D d : ℝ) (l : ℕ) (x b : ℝ)
    (R R' : ℝ → ℝ) (s : ℝ) : ℝ :=
  (d / D) * Real.exp s * ((R s + R' s) * kepFixedBridge p w s l x b +
    R s * kepFixedBridgeSlope p q w s l x b)

/-- A first-flux scalar needs only one actual bridge derivative. In particular
this expression does not contain a product of two short-row derivatives. -/
theorem hasDerivAt_kepGraphPinScalar {σ : ℝ} (A : KepTailDynamics σ)
    {R R' : ℝ → ℝ} (hdR : ∀ s, HasDerivAt R (R' s) s)
    (w D d : ℝ) (l : ℕ) (x b s : ℝ) :
    HasDerivAt (kepGraphPinScalar A.step w D d l x b R)
      (kepGraphPinScalarFirst A.step A.slope w D d l x b R R' s) s := by
  have hh := ((((Real.hasDerivAt_exp s).mul (hdR s)).const_mul (d / D)).mul
    (hasDerivAt_kepFixedBridge_slope A.continuous_step A.continuous_slope
      A.slope_derivative w s l x b))
  convert hh using 1 <;> first
  | rfl
  | (funext t; dsimp [kepGraphPinScalar]; ring)
  | (dsimp [kepGraphPinScalarFirst]; ring)

/-- Transfer an individual pinned graph, including a zero-step remaining tail.
Positive support has already proved `d > 0` for every nonzero reference pin. -/
theorem kepLogPinnedGraphIntegral_derivative_transfer
    (A : KepTailDynamics (-1)) (B : KepTailDynamics 1) {σ : ℝ} (C : KepTailDynamics σ)
    {φ φ' R R' : ℝ → ℝ} (hφ : Continuous φ) (hφ' : Continuous φ')
    (hdφ : ∀ y, HasDerivAt φ (φ' y) y) (hR : Continuous R) (hR' : Continuous R')
    (hdR : ∀ s, HasDerivAt R (R' s) s)
    {w lo hi D d : ℝ} (hw : 0 ≤ w) (hlh : lo ≤ hi) (hD : 0 < D) (hd : 0 ≤ d)
    (hlo : R lo = 0) (hhi : R hi = 0) (i r l : ℕ) (xA xB x b : ℝ) :
    kepLogGraphIntegral A.step B.step w lo hi (D + d) i r xA xB
      (kepGraphPinScalar C.step w D d l x b R) φ' =
    kepLogGraphIntegral A.step B.step w lo hi (D + d) i r xA xB
      (fun s => Real.exp s * (kepGraphPinScalar C.step w D d l x b R s +
        kepGraphPinScalarFirst C.step C.slope w D d l x b R R' s) / (D + d)) φ +
    kepLogGraphFluxIntegral A.step B.step w lo hi (D + d) i r xA xB
      (kepGraphPinScalar C.step w D d l x b R) φ := by
  have hK : Continuous (fun s => kepFixedBridge C.step w s l x b) :=
    (continuous_kepFixedBridge C.continuous_step w l).comp
      (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hKs : Continuous (fun s => kepFixedBridgeSlope C.step C.slope w s l x b) :=
    (continuous_kepFixedBridgeSlope C.continuous_step C.continuous_slope w l).comp
      (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hU : Continuous (kepGraphPinScalar C.step w D d l x b R) := by
    unfold kepGraphPinScalar
    fun_prop
  have hU' : Continuous (kepGraphPinScalarFirst C.step C.slope w D d l x b R R') := by
    unfold kepGraphPinScalarFirst
    fun_prop
  apply kepLogGraphIntegral_derivative_transfer A B hφ hφ' hdφ hU hU'
    (hasDerivAt_kepGraphPinScalar C hdR w D d l x b) hw hlh (by linarith : 0 < D + d).ne'
  · simp [kepGraphPinScalar, hlo]
  · simp [kepGraphPinScalar, hhi]

end

end PGM
