import PLAStochastic.Index.CEPS.Normal.Algebra

/-! # Exchange of the two Morse roots (C-7(iv)) -/

noncomputable section
open Complex
namespace PGM.CepsNormalData

def swapRoots (a : CepsNormalData) : CepsNormalData where
  βp := a.βm
  βm := a.βp
  d := a.d
  Q := a.Q
  ψp := a.ψm
  ψm := a.ψp

variable (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q : ℂ)

theorem eta_swap : a.swapRoots.eta = -a.eta := by
  simp only [eta, swapRoots]
  ring

theorem decay_swap (l : ℂ) : a.swapRoots.decay l = (a.decay l)⁻¹ := by
  rw [decay, eta_swap]
  have he : -(-a.eta) * l = -(-a.eta * l) := by ring
  rw [he, exp_neg]
  rfl

theorem pi_ne_zero (hQp : a.Q a.βp ≠ 0) (hQm : a.Q a.βm ≠ 0) :
    a.pi L μ q ≠ 0 := by
  exact mul_ne_zero (div_ne_zero hQp hQm) (exp_ne_zero _)

theorem pi_swap (hQp : a.Q a.βp ≠ 0) (hQm : a.Q a.βm ≠ 0) :
    a.swapRoots.pi L μ q = (a.pi L μ q)⁻¹ := by
  unfold pi swapRoots
  have he : 2 * L μ q a.βp - 2 * L μ q a.βm =
      -(2 * L μ q a.βm - 2 * L μ q a.βp) := by ring
  rw [he, exp_neg]
  field_simp

theorem markedN_swap (t : ℂ) (hQp : a.Q a.βp ≠ 0) (hQm : a.Q a.βm ≠ 0) :
    a.swapRoots.markedN L μ q t = a.markedN L μ q t / a.pi L μ q := by
  unfold markedN pi swapRoots
  have hE : exp (2 * L μ q a.βp - 2 * L μ q t) *
      exp (2 * L μ q a.βm - 2 * L μ q a.βp) =
      exp (2 * L μ q a.βm - 2 * L μ q t) := by
    rw [← exp_add]
    congr 1
    ring
  field_simp
  ring_nf at hE ⊢
  linear_combination a.Q t * hE

/-- `Δ` transforms covariantly; its zero set is unchanged. -/
theorem delta_swap (l : ℂ) (hQp : a.Q a.βp ≠ 0) (hQm : a.Q a.βm ≠ 0) :
    a.swapRoots.delta L μ q l = -a.delta L μ q l / (a.decay l * a.pi L μ q) := by
  rw [delta, decay_swap, pi_swap a L μ q hQp hQm, delta]
  have hE : a.decay l ≠ 0 := exp_ne_zero _
  have hP := pi_ne_zero a L μ q hQp hQm
  field_simp
  ring

theorem delta_swap_ne (l : ℂ) (hQp : a.Q a.βp ≠ 0) (hQm : a.Q a.βm ≠ 0)
    (hΔ : a.delta L μ q l ≠ 0) : a.swapRoots.delta L μ q l ≠ 0 := by
  rw [delta_swap a L μ q l hQp hQm]
  exact div_ne_zero (neg_ne_zero.mpr hΔ)
    (mul_ne_zero (exp_ne_zero _) (pi_ne_zero a L μ q hQp hQm))

theorem entranceNumerator_swap (t l : ℂ) (hQp : a.Q a.βp ≠ 0)
    (hQm : a.Q a.βm ≠ 0) :
    a.swapRoots.entranceNumerator L μ q t l =
      -a.entranceNumerator L μ q t l / (a.decay l * a.pi L μ q) := by
  unfold entranceNumerator
  rw [eta_swap, decay_swap, pi_swap a L μ q hQp hQm,
    markedN_swap a L μ q t hQp hQm]
  change (a.βm - t) - (a.βp - t) * (a.decay l)⁻¹ * (a.pi L μ q)⁻¹ -
      (-a.eta) * exp ((a.βp - t) * l) * (a.markedN L μ q t / a.pi L μ q) = _
  have hE : a.decay l ≠ 0 := exp_ne_zero _
  have hP := pi_ne_zero a L μ q hQp hQm
  have hphase : a.decay l * exp ((a.βp - t) * l) = exp ((a.βm - t) * l) := by
    rw [decay, ← exp_add]
    congr 1
    rw [eta]
    ring
  field_simp
  linear_combination (a.eta * a.markedN L μ q t) * hphase

/-- The normal entrance is independent of the sign of the Morse coordinate. -/
theorem entrance_swap (t l : ℂ) (hQp : a.Q a.βp ≠ 0)
    (hQm : a.Q a.βm ≠ 0) (hΔ : a.delta L μ q l ≠ 0) :
    a.swapRoots.entrance L μ q t l = a.entrance L μ q t l := by
  unfold entrance
  rw [entranceNumerator_swap a L μ q t l hQp hQm, delta_swap a L μ q l hQp hQm]
  change exp (L μ q t) / a.d t * _ / _ = _
  have hE : a.decay l ≠ 0 := exp_ne_zero _
  have hP := pi_ne_zero a L μ q hQp hQm
  field_simp

theorem halfBridge_swap (l : ℂ) (hQp : a.Q a.βp ≠ 0) (hQm : a.Q a.βm ≠ 0)
    (hp : a.ψp = a.eta * a.Q a.βp) (hm : a.ψm = -a.eta * a.Q a.βm) :
    a.swapRoots.halfBridge L μ q l = -a.halfBridge L μ q l / (a.decay l * a.pi L μ q) := by
  unfold halfBridge
  change a.ψm * exp (-a.βm * l - 2 * L μ q a.βm) = _
  rw [hp, hm, decay, pi]
  have hE : exp (-a.βm * l - 2 * L μ q a.βm) * exp (-a.eta * l) *
      exp (2 * L μ q a.βm - 2 * L μ q a.βp) =
      exp (-a.βp * l - 2 * L μ q a.βp) := by
    rw [← exp_add, ← exp_add]
    congr 1
    rw [eta]
    ring
  field_simp
  ring_nf at hE ⊢
  linear_combination -a.eta * hE

theorem bridge_swap (l : ℂ) (hQp : a.Q a.βp ≠ 0) (hQm : a.Q a.βm ≠ 0)
    (hp : a.ψp = a.eta * a.Q a.βp) (hm : a.ψm = -a.eta * a.Q a.βm)
    (hΔ : a.delta L μ q l ≠ 0) :
    a.swapRoots.bridge L μ q l = a.bridge L μ q l := by
  unfold bridge
  rw [halfBridge_swap a L μ q l hQp hQm hp hm, delta_swap a L μ q l hQp hQm]
  have hE : a.decay l ≠ 0 := exp_ne_zero _
  have hP := pi_ne_zero a L μ q hQp hQm
  field_simp

end PGM.CepsNormalData
