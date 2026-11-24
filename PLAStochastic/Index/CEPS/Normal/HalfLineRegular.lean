import PLAStochastic.Index.CEPS.Normal.HalfLineDerivative

/-! # The genuine half-line entrance at a marker/root collision -/

noncomputable section
open Complex
namespace PGM
namespace CepsNormalData

/-- Cancels the upper-root zero while retaining the lower-root pole. -/
def regularHalfEntrance (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q t : ℂ) : ℂ :=
  exp (L μ q t) / ((t - a.βm) * a.Q t)

theorem halfEntrance_eq_regularHalfEntrance (a : CepsNormalData)
    (L : ℂ → ℂ → ℂ → ℂ) (μ q t : ℂ)
    (hd : a.d t = -(t - a.βp) * (t - a.βm) * a.Q t)
    (hp : t - a.βp ≠ 0) :
    a.halfEntrance L μ q t = a.regularHalfEntrance L μ q t := by
  unfold halfEntrance regularHalfEntrance
  rw [hd, show a.βp - t = -(t - a.βp) by ring, mul_neg,
    neg_mul, neg_mul, neg_div_neg_eq, mul_assoc,
    mul_comm (t - a.βp) ((t - a.βm) * a.Q t), mul_div_mul_right _ _ hp]

theorem regularHalfEntrance_at_upperRoot (a : CepsNormalData)
    (L : ℂ → ℂ → ℂ → ℂ) (μ q : ℂ) (hp : a.ψp = a.eta * a.Q a.βp) :
    a.regularHalfEntrance L μ q a.βp = exp (L μ q a.βp) / a.ψp := by
  unfold regularHalfEntrance eta at *
  rw [← hp]

end CepsNormalData

/-- Half-line pair using the actual cancelled entrance rather than totalized `0/0`. -/
def cepsNormalRegularHalfPairAt (A : ℂ → ℂ → CepsNormalData)
    (L : ℂ → ℂ → ℂ → ℂ) (μ q t w : ℂ) : ℂ :=
  let l := w * (1 + μ)
  exp (t * l) * ((A μ q).regularHalfEntrance L μ q t) ^ 2 *
    (-deriv (fun q' => (A μ q').halfBridge L μ q' l) q -
      w * (A μ q).halfBridge L μ q l)

theorem cepsNormalHalfPairAt_eq_regular (A : ℂ → ℂ → CepsNormalData)
    (L : ℂ → ℂ → ℂ → ℂ) (μ q t w : ℂ)
    (hd : (A μ q).d t = -(t - (A μ q).βp) * (t - (A μ q).βm) * (A μ q).Q t)
    (hp : t - (A μ q).βp ≠ 0) :
    cepsNormalHalfPairAt A L μ q t w = cepsNormalRegularHalfPairAt A L μ q t w := by
  unfold cepsNormalHalfPairAt cepsNormalRegularHalfPairAt
  rw [CepsNormalData.halfEntrance_eq_regularHalfEntrance _ L μ q t hd hp]

end PGM
