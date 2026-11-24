import PLAStochastic.Index.CEPS.Normal.Algebra

/-! # Width Hadamard identity for the normal entrance (C-7(ii)) -/

noncomputable section
open Complex
namespace PGM.CepsNormalData

variable (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q : ℂ)

theorem reflectedN_mul_markedN_zero (hQ0 : a.Q 0 ≠ 0) (hQm : a.Q a.βm ≠ 0) :
    a.reflectedN L μ q * a.markedN L μ q 0 = a.pi L μ q := by
  unfold reflectedN markedN pi
  have hE : exp (2 * L μ q 0 - 2 * L μ q a.βp) *
      exp (2 * L μ q a.βm - 2 * L μ q 0) =
      exp (2 * L μ q a.βm - 2 * L μ q a.βp) := by
    rw [← exp_add]
    congr 1
    ring
  field_simp
  ring_nf at hE ⊢
  linear_combination a.Q a.βp * hE

theorem reflectedN_prefactor (hQ0 : a.Q 0 ≠ 0)
    (hp : a.ψp = a.eta * a.Q a.βp) :
    exp (a.factorMinus L μ q 0) * a.eta * a.reflectedN L μ q =
      exp (L μ q 0) * a.ψp * exp (-2 * L μ q a.βp) := by
  rw [exp_factorMinus a L μ q hQ0, reflectedN, hp]
  have hE : exp (2 * L μ q 0 - 2 * L μ q a.βp) =
      exp (L μ q 0) ^ 2 * exp (-2 * L μ q a.βp) := by
    have he : -2 * L μ q a.βp = -(2 * L μ q a.βp) := by ring
    rw [he, exp_sub, exp_neg]
    have h2 := exp_nat_mul (L μ q 0) 2
    norm_num at h2
    rw [h2]
    ring
  rw [hE]
  field_simp

theorem hasDerivAt_decay (l : ℂ) :
    HasDerivAt a.decay (a.decay l * (-a.eta)) l := by
  change HasDerivAt (fun x => exp (-a.eta * x)) (exp (-a.eta * l) * (-a.eta)) l
  simpa using ((hasDerivAt_id l).const_mul (-a.eta)).cexp

theorem hasDerivAt_delta (l : ℂ) :
    HasDerivAt (a.delta L μ q) (a.eta * a.decay l * a.pi L μ q) l := by
  refine (((hasDerivAt_decay a l).mul_const (a.pi L μ q)).const_sub 1).congr_deriv ?_
  ring

theorem hasDerivAt_bottomNumerator (l : ℂ) :
    HasDerivAt (a.bottomNumerator L μ q)
      (-a.βp * a.eta * a.decay l * a.pi L μ q +
        a.eta * a.βp * exp (-a.βp * l) * a.reflectedN L μ q) l := by
  have hp := (((hasDerivAt_id l).const_mul (-a.βp)).cexp.const_mul a.eta).mul_const
    (a.reflectedN L μ q)
  have hE := (((hasDerivAt_decay a l).const_mul a.βp).mul_const
    (a.pi L μ q)).const_add (-a.βm)
  refine (hE.sub hp).congr_deriv ?_
  simp only [id_eq]
  ring

/-- The identity is multiplicative, so it is meaningful even when `ĥ₊ = 0`. -/
theorem hasDerivAt_bottomEntrance (l : ℂ) (hQ0 : a.Q 0 ≠ 0)
    (hQm : a.Q a.βm ≠ 0) (hd : a.d 0 ≠ 0) (hΔ : a.delta L μ q l ≠ 0)
    (hp : a.ψp = a.eta * a.Q a.βp) :
    HasDerivAt (a.bottomEntrance L μ q)
      (a.entrance L μ q 0 l * a.bridge L μ q l) l := by
  have h := ((hasDerivAt_bottomNumerator a L μ q l).const_mul
    (exp (a.factorMinus L μ q 0) / a.d 0)).div (hasDerivAt_delta a L μ q l) hΔ
  refine h.congr_deriv ?_
  have hN := reflectedN_mul_markedN_zero a L μ q hQ0 hQm
  have hP := reflectedN_prefactor a L μ q hQ0 hp
  have hE : a.decay l = exp (-a.βp * l) * exp (a.βm * l) := by
    rw [decay, ← exp_add]
    congr 1
    rw [eta]
    ring
  have hNum :
      (-a.βp * a.eta * a.decay l * a.pi L μ q +
        a.eta * a.βp * exp (-a.βp * l) * a.reflectedN L μ q) * a.delta L μ q l -
      a.bottomNumerator L μ q l * (a.eta * a.decay l * a.pi L μ q) =
      a.eta * exp (-a.βp * l) * a.reflectedN L μ q * a.entranceNumerator L μ q 0 l := by
    unfold delta bottomNumerator entranceNumerator
    simp only [sub_zero]
    rw [← hN, hE]
    rw [eta]
    ring
  unfold entrance bridge halfBridge
  have hBridge : exp (-a.βp * l - 2 * L μ q a.βp) =
      exp (-a.βp * l) * exp (-2 * L μ q a.βp) := by
    rw [← exp_add]
    congr 1
    ring
  rw [hBridge]
  calc
    _ = (exp (a.factorMinus L μ q 0) / a.d 0) *
        (a.eta * exp (-a.βp * l) * a.reflectedN L μ q *
          a.entranceNumerator L μ q 0 l) / a.delta L μ q l ^ 2 := by
      rw [← hNum]
      ring
    _ = _ := by
      field_simp [hd, hΔ]
      ring_nf at hP ⊢
      linear_combination a.entranceNumerator L μ q 0 l * hP

/-- The quotient form requested in (C12), with its necessary nonzero entrance. -/
theorem deriv_bottomEntrance_div (l : ℂ) (hQ0 : a.Q 0 ≠ 0)
    (hQm : a.Q a.βm ≠ 0) (hd : a.d 0 ≠ 0) (hΔ : a.delta L μ q l ≠ 0)
    (hp : a.ψp = a.eta * a.Q a.βp) (hh : a.entrance L μ q 0 l ≠ 0) :
    deriv (a.bottomEntrance L μ q) l / a.entrance L μ q 0 l =
      a.halfBridge L μ q l / a.delta L μ q l := by
  rw [(hasDerivAt_bottomEntrance a L μ q l hQ0 hQm hd hΔ hp).deriv]
  unfold bridge
  field_simp

end PGM.CepsNormalData
