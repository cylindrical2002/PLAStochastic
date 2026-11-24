import PLAStochastic.Index.CEPS.Normal.Symmetry

/-!
# Uniform divided-difference normal forms

With `g(ζ) = exp(-ζ l) Q(ζ) exp(-2 L(ζ))`, both the entrance and bridge
have formulas without the displayed factors `d(t)`, `β₊-β₋`, or `Δ`.
The first divided difference of `g` is the sole remaining denominator.
This also handles `t = β±` and coinciding roots as an extension, rather than
using the totalized value of the raw formula at its zero denominators.
-/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsNormal_divided_difference_determinant (g : ℂ → ℂ) (a b t : ℂ) :
    (a - t) * g b + (t - b) * g a - (a - b) * g t =
      (a - b) * (a - t) * (t - b) * dslope (dslope g b) a t := by
  have h1 := sub_smul_dslope g b a
  have h2 := sub_smul_dslope g b t
  have h3 := sub_smul_dslope (dslope g b) a t
  simp only [smul_eq_mul] at h1 h2 h3
  linear_combination -(t - b) * h1 + (a - b) * h2 + ((a - b) * (t - b)) * h3

namespace CepsNormalData

variable (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q l : ℂ)

def normalG (ζ : ℂ) : ℂ := exp (-ζ * l) * a.Q ζ * exp (-2 * L μ q ζ)

def regularEntrance (t : ℂ) : ℂ :=
  -exp (L μ q t) * dslope (dslope (a.normalG L μ q l) a.βm) a.βp t /
    (a.Q t * dslope (a.normalG L μ q l) a.βm a.βp)

def regularBridge : ℂ :=
  -a.normalG L μ q l a.βp * a.normalG L μ q l a.βm /
    dslope (a.normalG L μ q l) a.βm a.βp

theorem normalG_ne {ζ : ℂ} (hQ : a.Q ζ ≠ 0) : a.normalG L μ q l ζ ≠ 0 :=
  mul_ne_zero (mul_ne_zero (exp_ne_zero _) hQ) (exp_ne_zero _)

theorem normalG_ratio (t : ℂ) (hQm : a.Q a.βm ≠ 0) :
    a.normalG L μ q l t / a.normalG L μ q l a.βm =
      exp ((a.βm - t) * l) * a.markedN L μ q t := by
  unfold normalG markedN
  have hE : exp (-t * l) * exp (-2 * L μ q t) =
      exp ((a.βm - t) * l) * exp (2 * L μ q a.βm - 2 * L μ q t) *
        exp (-a.βm * l) * exp (-2 * L μ q a.βm) := by
    rw [← exp_add, ← exp_add, ← exp_add, ← exp_add]
    congr 1
    ring
  field_simp
  ring_nf at hE ⊢
  linear_combination a.Q t * hE

theorem normalG_root_ratio (hQm : a.Q a.βm ≠ 0) :
    a.normalG L μ q l a.βp / a.normalG L μ q l a.βm = a.decay l * a.pi L μ q := by
  rw [normalG_ratio a L μ q l a.βp hQm]
  have hNt : a.markedN L μ q a.βp = a.pi L μ q := rfl
  rw [hNt]
  have he : (a.βm - a.βp) * l = -a.eta * l := by rw [eta]; ring
  rw [he]
  rfl

theorem delta_mul_normalG (hQm : a.Q a.βm ≠ 0) :
    a.delta L μ q l * a.normalG L μ q l a.βm =
      -a.eta * dslope (a.normalG L μ q l) a.βm a.βp := by
  have hgm := normalG_ne a L μ q l hQm
  rw [delta, ← normalG_root_ratio a L μ q l hQm]
  have h := sub_smul_dslope (a.normalG L μ q l) a.βm a.βp
  rw [smul_eq_mul, ← eta] at h
  field_simp
  linear_combination h

theorem entranceNumerator_mul_normalG (t : ℂ) (hQm : a.Q a.βm ≠ 0) :
    a.entranceNumerator L μ q t l * a.normalG L μ q l a.βm =
      a.eta * (a.βp - t) * (t - a.βm) *
        dslope (dslope (a.normalG L μ q l) a.βm) a.βp t := by
  have hgm := normalG_ne a L μ q l hQm
  have h := cepsNormal_divided_difference_determinant (a.normalG L μ q l) a.βp a.βm t
  rw [← eta] at h
  unfold entranceNumerator
  rw [mul_assoc (a.βm - t) (a.decay l) (a.pi L μ q),
    ← normalG_root_ratio a L μ q l hQm]
  have hNt := normalG_ratio a L μ q l t hQm
  rw [mul_assoc a.eta _ _, ← hNt]
  field_simp
  linear_combination h

/-- All the displayed singular factors cancel simultaneously in (C16). -/
theorem entrance_eq_regular (t : ℂ) (hQm : a.Q a.βm ≠ 0) (hQt : a.Q t ≠ 0)
    (hη : a.eta ≠ 0) (hpt : a.βp - t ≠ 0) (htm : t - a.βm ≠ 0)
    (hS : dslope (a.normalG L μ q l) a.βm a.βp ≠ 0)
    (hd : a.d t = a.Q t * (a.βp - t) * (t - a.βm)) :
    a.entrance L μ q t l = a.regularEntrance L μ q l t := by
  have hgm := normalG_ne a L μ q l hQm
  have hD := delta_mul_normalG a L μ q l hQm
  have hN := entranceNumerator_mul_normalG a L μ q l t hQm
  have hΔ : a.delta L μ q l ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hD
    exact (mul_ne_zero (neg_ne_zero.mpr hη) hS) hD.symm
  have hd0 : a.d t ≠ 0 := by rw [hd]; exact mul_ne_zero (mul_ne_zero hQt hpt) htm
  unfold entrance regularEntrance
  field_simp [hd0, hΔ, hQt, hS]
  rw [hd]
  apply mul_right_cancel₀ hgm
  linear_combination (a.Q t *
    dslope (a.normalG L μ q l) a.βm a.βp) * hN +
    (a.Q t * (a.βp - t) * (t - a.βm) *
      dslope (dslope (a.normalG L μ q l) a.βm) a.βp t) * hD

theorem bridge_eq_regular (hQm : a.Q a.βm ≠ 0) (hη : a.eta ≠ 0)
    (hS : dslope (a.normalG L μ q l) a.βm a.βp ≠ 0)
    (hp : a.ψp = a.eta * a.Q a.βp) :
    a.bridge L μ q l = a.regularBridge L μ q l := by
  have hD := delta_mul_normalG a L μ q l hQm
  have hgm := normalG_ne a L μ q l hQm
  have hΔ : a.delta L μ q l ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hD
    exact (mul_ne_zero (neg_ne_zero.mpr hη) hS) hD.symm
  have hU : a.halfBridge L μ q l = a.eta * a.normalG L μ q l a.βp := by
    unfold halfBridge normalG
    rw [hp]
    have he : exp (-a.βp * l - 2 * L μ q a.βp) =
        exp (-a.βp * l) * exp (-2 * L μ q a.βp) := by
      rw [← exp_add]
      congr 1
      ring
    rw [he]
    ring
  unfold bridge regularBridge
  rw [hU]
  field_simp
  linear_combination a.normalG L μ q l a.βp * hD

/-- Holomorphy in the marker, including markers equal to either root. Both
roots may already coincide; the first divided difference must remain nonzero.
-/
theorem differentiableOn_regularEntrance {R : ℝ}
    (hQ : DifferentiableOn ℂ a.Q (ball 0 R))
    (hL : DifferentiableOn ℂ (L μ q) (ball 0 R))
    (hbp : a.βp ∈ ball 0 R) (hbm : a.βm ∈ ball 0 R)
    (hQ0 : ∀ t ∈ ball (0 : ℂ) R, a.Q t ≠ 0)
    (hS : dslope (a.normalG L μ q l) a.βm a.βp ≠ 0) :
    DifferentiableOn ℂ (a.regularEntrance L μ q l) (ball 0 R) := by
  have hG : DifferentiableOn ℂ (a.normalG L μ q l) (ball 0 R) :=
    (((differentiableOn_id.neg.mul_const l).cexp).mul hQ).mul ((hL.const_mul (-2)).cexp)
  have h1 := (differentiableOn_dslope (isOpen_ball.mem_nhds hbm)).mpr hG
  have h2 := (differentiableOn_dslope (isOpen_ball.mem_nhds hbp)).mpr h1
  exact (hL.cexp.neg.mul h2).div (hQ.mul_const _) (fun t ht => mul_ne_zero (hQ0 t ht) hS)

theorem regularBridge_merged (hroots : a.βp = a.βm) :
    a.regularBridge L μ q l = -(a.normalG L μ q l a.βm) ^ 2 /
      deriv (a.normalG L μ q l) a.βm := by
  rw [regularBridge, hroots, dslope_same]
  ring

end CepsNormalData
end PGM
