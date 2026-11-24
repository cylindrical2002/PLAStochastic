import PLAStochastic.Index.CEPS.Normal.Defs

/-! # Algebraic strip identities (C-7(i), (iii), and (P8)) -/

noncomputable section
open Complex
namespace PGM.CepsNormalData

variable (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q : ℂ)

theorem exp_factorMinus {ζ : ℂ} (hQ : a.Q ζ ≠ 0) :
    exp (a.factorMinus L μ q ζ) = a.Q ζ / exp (L μ q ζ) := by
  rw [factorMinus, exp_sub, exp_log hQ]

theorem overshootMinus_eq {s : ℂ} (hQ1 : a.Q (a.βm + s) ≠ 0)
    (hQ0 : a.Q a.βm ≠ 0) :
    a.overshootMinus L μ q s = a.Q (a.βm + s) / a.Q a.βm *
      exp (L μ q a.βm - L μ q (a.βm + s)) := by
  rw [overshootMinus, exp_sub, exp_factorMinus a L μ q hQ1,
    exp_factorMinus a L μ q hQ0, exp_sub]
  field_simp

theorem pi_eq_overshoots (hQp : a.Q a.βp ≠ 0) (hQm : a.Q a.βm ≠ 0) :
    a.pi L μ q = a.overshootPlus L μ q a.eta * a.overshootMinus L μ q a.eta := by
  have hp : a.βm + a.eta = a.βp := by rw [eta]; ring
  have hm : a.βp - a.eta = a.βm := by rw [eta]; ring
  rw [overshootMinus_eq a L μ q (by rwa [hp]) hQm, hp, overshootPlus, hm, pi]
  rw [← mul_assoc, mul_comm (exp _) (a.Q a.βp / a.Q a.βm), mul_assoc, ← exp_add]
  congr 2
  ring

theorem markedN_eq_overshoot {t : ℂ} (hQt : a.Q t ≠ 0) (hQm : a.Q a.βm ≠ 0) :
    a.markedN L μ q t = exp (L μ q a.βm - L μ q t) *
      a.overshootMinus L μ q (t - a.βm) := by
  have ht : a.βm + (t - a.βm) = t := by ring
  rw [overshootMinus_eq a L μ q (by rwa [ht]) hQm, ht, markedN]
  rw [← mul_assoc, mul_comm (exp _) (a.Q t / a.Q a.βm), mul_assoc, ← exp_add]
  congr 2
  ring

theorem pi_eq_root_derivatives (hη : a.eta ≠ 0) (hQm : a.Q a.βm ≠ 0)
    (hp : a.ψp = a.eta * a.Q a.βp) (hm : a.ψm = -a.eta * a.Q a.βm) :
    a.pi L μ q = a.ψp / (-a.ψm) * exp (2 * L μ q a.βm - 2 * L μ q a.βp) := by
  rw [pi, hp, hm]
  congr 1
  field_simp

/-- The reduced two-passage system has exactly one solution when `Δ ≠ 0`. -/
theorem passage_system_unique (l : ℂ) (hQp : a.Q a.βp ≠ 0) (hQm : a.Q a.βm ≠ 0)
    (hΔ : a.delta L μ q l ≠ 0) :
    ∃! p : ℂ × ℂ,
      p.1 = a.eta * exp (L μ q a.βm) +
        a.overshootPlus L μ q a.eta * p.2 ∧
      p.2 = a.decay l * a.overshootMinus L μ q a.eta * p.1 := by
  let c := a.overshootPlus L μ q a.eta
  let g := a.decay l * a.overshootMinus L μ q a.eta
  let v := a.eta * exp (L μ q a.βm)
  have hcg : 1 - c * g = a.delta L μ q l := by
    rw [delta, pi_eq_overshoots a L μ q hQp hQm]
    dsimp [c, g]
    ring
  refine ⟨(v / a.delta L μ q l, g * (v / a.delta L μ q l)), ?_, ?_⟩
  · change v / a.delta L μ q l = v + c * (g * (v / a.delta L μ q l)) ∧ _
    constructor
    · rw [← hcg] at hΔ ⊢
      field_simp
      ring
    · rfl
  · intro p hp
    have hx : p.1 = v / a.delta L μ q l := by
      apply (eq_div_iff hΔ).2
      rw [← hcg]
      change p.1 = v + c * p.2 ∧ p.2 = g * p.1 at hp
      rw [hp.2] at hp
      linear_combination hp.1
    apply Prod.ext hx
    simpa only [hx] using hp.2

/-- The first reduced unknown is `1 - û(β₋)`. -/
def passageX (l : ℂ) : ℂ := a.eta * exp (L μ q a.βm) / a.delta L μ q l

def passageY (l : ℂ) : ℂ :=
  a.decay l * a.overshootMinus L μ q a.eta * a.passageX L μ q l

def upperExit (t l : ℂ) : ℂ :=
  1 - (a.βp - t) * exp (L μ q t) -
    a.overshootPlus L μ q (a.βp - t) * a.passageY L μ q l

def lowerExit (t l : ℂ) : ℂ :=
  exp ((a.βm - t) * l) * a.overshootMinus L μ q (t - a.βm) *
    a.passageX L μ q l

/-- (C16) is the entrance read out from the normal two-passage solution. -/
theorem entrance_eq_passage (t l : ℂ) (hQp : a.Q a.βp ≠ 0)
    (hQm : a.Q a.βm ≠ 0) (hQt : a.Q t ≠ 0) (hd : a.d t ≠ 0)
    (hΔ : a.delta L μ q l ≠ 0) :
    a.entrance L μ q t l = (1 - a.upperExit L μ q t l - a.lowerExit L μ q t l) / a.d t := by
  have hb : a.overshootPlus L μ q (a.βp - t) = exp (L μ q t - L μ q a.βp) := by
    rw [overshootPlus]
    simp only [sub_sub_cancel]
  have hbm : a.overshootMinus L μ q a.eta =
      a.Q a.βp / a.Q a.βm * exp (L μ q a.βm - L μ q a.βp) := by
    have hp : a.βm + a.eta = a.βp := by rw [eta]; ring
    rw [overshootMinus_eq a L μ q (by rwa [hp]) hQm, hp]
  have hbt : a.overshootMinus L μ q (t - a.βm) =
      a.Q t / a.Q a.βm * exp (L μ q a.βm - L μ q t) := by
    have ht : a.βm + (t - a.βm) = t := by ring
    rw [overshootMinus_eq a L μ q (by rwa [ht]) hQm, ht]
  have hexp : exp (L μ q t - L μ q a.βp) * exp (L μ q a.βm - L μ q a.βp) *
      exp (L μ q a.βm) = exp (L μ q t) * exp (2 * L μ q a.βm - 2 * L μ q a.βp) := by
    rw [← exp_add, ← exp_add, ← exp_add]
    congr 1
    ring
  have hexp' : exp (L μ q a.βm - L μ q t) * exp (L μ q a.βm) =
      exp (L μ q t) * exp (2 * L μ q a.βm - 2 * L μ q t) := by
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  unfold entrance entranceNumerator upperExit lowerExit passageY passageX
  rw [hb, hbm, hbt]
  field_simp [hd, hΔ, hQm]
  unfold delta pi markedN
  field_simp [hQm]
  rw [eta]
  ring_nf at hexp hexp' ⊢
  linear_combination -(a.βp - a.βm) * a.decay l * a.Q a.βp * hexp +
    ((a.βp - a.βm) * exp (-(t * l) + a.βm * l) * a.Q t) * hexp'

/-- The half-line difference formula (P5). -/
theorem entrance_sub_half (t l : ℂ) (hd : a.d t ≠ 0)
    (hΔ : a.delta L μ q l ≠ 0) :
    a.entrance L μ q t l - a.halfEntrance L μ q t =
      exp (L μ q t) * a.eta / (a.d t * a.delta L μ q l) *
        (a.decay l * a.pi L μ q - exp ((a.βm - t) * l) * a.markedN L μ q t) := by
  unfold entrance entranceNumerator halfEntrance
  field_simp
  rw [delta, eta]
  ring

/-- Explicit half-line primitive numerator (P8). -/
theorem primitiveNumerator_eq (t l : ℂ) :
    a.primitiveNumerator L μ q t l =
      (a.βp - t) ^ 2 * a.ψp / a.d t ^ 2 *
        exp (2 * L μ q t - 2 * L μ q a.βp) * exp (-(a.βp - t) * l) := by
  unfold primitiveNumerator halfEntrance halfBridge
  rw [div_pow, mul_pow]
  have hE : exp (t * l) * exp (L μ q t) ^ 2 *
      exp (-a.βp * l - 2 * L μ q a.βp) =
      exp (2 * L μ q t - 2 * L μ q a.βp) * exp (-(a.βp - t) * l) := by
    rw [← exp_nat_mul, ← exp_add, ← exp_add, ← exp_add]
    congr 1
    ring
  linear_combination ((a.βp - t) ^ 2 * a.ψp / a.d t ^ 2) * hE

theorem primitive_div_eq_amplitude (t l : ℂ) (hβt : a.βp - t ≠ 0) :
    a.primitiveNumerator L μ q t l / (a.βp - t) =
      a.amplitude L μ q t * exp (-(a.βp - t) * l) / a.d t := by
  rw [primitiveNumerator_eq]
  unfold amplitude
  field_simp

end PGM.CepsNormalData
