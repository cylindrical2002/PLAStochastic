import PLAStochastic.Index.CEPS.Normal.Algebra

/-!
# WP10: normal-side algebra of the fixed-drift drawup (blueprint (3.9))

The drawup transform is `u^bot/(1 - ℓ^bot)` (cycle identity (3.8)), where `u^bot`, `ℓ^bot` are
the upper and lower exit transforms of the bottom-started `Y_μ` strip `[0, l]` with mark
`e^{t Z_τ}`. Its normal two-passage system is
`û_t = e^{-(β₊-t)l} B₊(β₊-t) (1 - ℓ̂_{β₊})`, `ℓ̂_t = A₋(t) - B₋(t-β₋) û_{β₋}`,
with the exact descending ladder `1 - A₋(ζ) = (ζ - β₋) e^{L₋(ζ)}` (`ladderGap`). Its solution is
`botUpperExit`, `botLowerExit`. The exact form of (3.9) is

  `û_t (1 - E κ_t) = 𝒜(t) e^{-(β₊-t) l} (1 - ℓ̂_t)`,  `E = e^{-η l}`,

with the bounded correction `κ_t = Π - B₋(t-β₋) B₊(η) (1-A₋(β₊))/(1-A₋(t))` (`drawupKappa`) and the
amplitude in the form regular at `t = 0` (`regularAmplitude`). Finally `d_t 𝒦_t/(β₊-t) = 𝒜 e^{-ϑl}`
(`d_mul_primitive_div`), the same main term.
-/

noncomputable section
open Complex

namespace PGM.CepsNormalData

variable (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q : ℂ)

/-- `1 - A₋(ζ) = (ζ - β₋) e^{L₋(ζ)}`. -/
def ladderGap (ζ : ℂ) : ℂ := (ζ - a.βm) * exp (a.factorMinus L μ q ζ)

/-- Upper exit (above `l`) of the bottom-started normal strip, mark `t`. -/
def botUpperExit (t l : ℂ) : ℂ :=
  exp (-(a.βp - t) * l) * a.overshootPlus L μ q (a.βp - t) * a.ladderGap L μ q a.βp /
    a.delta L μ q l

/-- Lower exit (below `0`, a new minimum) of the bottom-started normal strip, mark `t`. -/
def botLowerExit (t l : ℂ) : ℂ :=
  1 - a.ladderGap L μ q t - a.overshootMinus L μ q (t - a.βm) * a.decay l *
    a.overshootPlus L μ q a.eta * a.ladderGap L μ q a.βp / a.delta L μ q l

/-- The correction `κ_t` of (3.9). -/
def drawupKappa (t : ℂ) : ℂ :=
  a.pi L μ q - a.overshootMinus L μ q (t - a.βm) * a.overshootPlus L μ q a.eta *
    a.ladderGap L μ q a.βp / a.ladderGap L μ q t

/-- The marked drawup amplitude (C19) in the form regular at `t = 0`. -/
def regularAmplitude (t : ℂ) : ℂ :=
  a.ψp * exp (2 * L μ q t - 2 * L μ q a.βp) / ((t - a.βm) * a.Q t)

theorem ladderGap_eq {ζ : ℂ} (hQ : a.Q ζ ≠ 0) :
    a.ladderGap L μ q ζ = (ζ - a.βm) * a.Q ζ / exp (L μ q ζ) := by
  rw [ladderGap, exp_factorMinus a L μ q hQ, mul_div_assoc]

/-- First equation of the normal bottom-started system. -/
theorem botUpperExit_passage (t l : ℂ) (hQp : a.Q a.βp ≠ 0) (hQm : a.Q a.βm ≠ 0)
    (hΔ : a.delta L μ q l ≠ 0) :
    a.botUpperExit L μ q t l = exp (-(a.βp - t) * l) * a.overshootPlus L μ q (a.βp - t) *
      (1 - a.botLowerExit L μ q a.βp l) := by
  have hpi := pi_eq_overshoots a L μ q hQp hQm
  have hd : a.delta L μ q l = 1 - a.decay l * a.overshootPlus L μ q a.eta *
      a.overshootMinus L μ q a.eta := by
    rw [delta, hpi]; ring
  have he : a.βp - a.βm = a.eta := rfl
  unfold botUpperExit botLowerExit
  rw [he]
  rw [hd] at hΔ ⊢
  field_simp
  ring

/-- Second equation of the normal bottom-started system. -/
theorem botLowerExit_passage (t l : ℂ) :
    a.botLowerExit L μ q t l = (1 - a.ladderGap L μ q t) -
      a.overshootMinus L μ q (t - a.βm) * a.botUpperExit L μ q a.βm l := by
  have he : a.βp - a.βm = a.eta := rfl
  unfold botLowerExit botUpperExit decay
  rw [he]
  ring

theorem amplitude_eq_regularAmplitude {t : ℂ}
    (hd : a.d t = -(t - a.βp) * (t - a.βm) * a.Q t) (hβ : a.βp - t ≠ 0) :
    a.amplitude L μ q t = a.regularAmplitude L μ q t := by
  unfold amplitude regularAmplitude
  rw [hd, show -(t - a.βp) = a.βp - t by ring]
  by_cases h : (t - a.βm) * a.Q t = 0
  · have h0 : (a.βp - t) * (t - a.βm) * a.Q t = 0 := by rw [mul_assoc, h, mul_zero]
    rw [h0, h]; simp
  · field_simp

/-- (3.9), exact form: `û_t (1 - E κ_t) = 𝒜(t) e^{-(β₊-t)l} (1 - ℓ̂_t)`. -/
theorem botExit_drawup_identity (t l : ℂ) (hψ : a.ψp = a.eta * a.Q a.βp)
    (hQp : a.Q a.βp ≠ 0) (hQt : a.Q t ≠ 0) (ht : t - a.βm ≠ 0)
    (hΔ : a.delta L μ q l ≠ 0) :
    a.botUpperExit L μ q t l * (1 - a.decay l * a.drawupKappa L μ q t) =
      a.regularAmplitude L μ q t * exp (-(a.βp - t) * l) * (1 - a.botLowerExit L μ q t l) := by
  have hgt : a.ladderGap L μ q t ≠ 0 := mul_ne_zero ht (exp_ne_zero _)
  have hgp : a.ladderGap L μ q a.βp = a.ψp / exp (L μ q a.βp) := by
    rw [ladderGap_eq a L μ q hQp, hψ]; rfl
  have hgt' := ladderGap_eq a L μ q hQt (ζ := t)
  have hop : a.overshootPlus L μ q (a.βp - t) = exp (L μ q t) / exp (L μ q a.βp) := by
    rw [overshootPlus, sub_sub_cancel, exp_sub]
  have hamp : a.regularAmplitude L μ q t * a.ladderGap L μ q t =
      a.overshootPlus L μ q (a.βp - t) * a.ladderGap L μ q a.βp := by
    rw [hgt', hgp, hop, regularAmplitude]
    have h2 : exp (2 * L μ q t - 2 * L μ q a.βp) =
        exp (L μ q t) ^ 2 / exp (L μ q a.βp) ^ 2 := by
      rw [exp_sub, ← exp_nat_mul, ← exp_nat_mul]; norm_num
    rw [h2]
    field_simp
  -- `(1 - ℓ̂_t) Δ = g(t) (1 - E κ_t)`.
  unfold botUpperExit botLowerExit drawupKappa
  field_simp
  unfold delta
  linear_combination (a.ladderGap L μ q t * a.decay l * a.pi L μ q - a.ladderGap L μ q t -
    a.ladderGap L μ q a.βp * a.decay l *
      a.overshootMinus L μ q (t - a.βm) * a.overshootPlus L μ q a.eta) * hamp

theorem one_sub_botLowerExit_mul_delta (t l : ℂ) (ht : a.ladderGap L μ q t ≠ 0)
    (hΔ : a.delta L μ q l ≠ 0) :
    (1 - a.botLowerExit L μ q t l) * a.delta L μ q l =
      a.ladderGap L μ q t * (1 - a.decay l * a.drawupKappa L μ q t) := by
  unfold botLowerExit drawupKappa
  field_simp
  unfold delta
  ring

/-- The upper endpoint of the half-line primitive is the drawup main term (P8). -/
theorem d_mul_primitive_div (t l : ℂ) (hd0 : a.d t ≠ 0) (hβ : a.βp - t ≠ 0) :
    a.d t * (a.primitiveNumerator L μ q t l / (a.βp - t)) =
      a.amplitude L μ q t * exp (-(a.βp - t) * l) := by
  rw [primitive_div_eq_amplitude a L μ q t l hβ]
  field_simp

end PGM.CepsNormalData

namespace PGM

/-- Perturbation of the cycle quotient: from `G (1 - ℓ) = u`, `‖G‖ ≤ 1` and the normal identity
`û (1 - ε) = Â (1 - ℓ̂)` with `‖ε‖ ≤ 1/2`, `‖1 - ℓ̂‖ ≥ c > 0`. -/
theorem norm_cycle_sub_le {G u ℓ û ℓ' A ε : ℂ} {c : ℝ} (hc : 0 < c)
    (hcyc : G * (1 - ℓ) = u) (hG : ‖G‖ ≤ 1) (hnorm : û * (1 - ε) = A * (1 - ℓ'))
    (hε : ‖ε‖ ≤ 1 / 2) (hℓ' : c ≤ ‖1 - ℓ'‖) :
    ‖G - A‖ ≤ (‖u - û‖ + ‖ℓ - ℓ'‖) / c + 2 * ‖A‖ * ‖ε‖ := by
  have hℓ0 : 0 < ‖1 - ℓ'‖ := lt_of_lt_of_le hc hℓ'
  have h1ε : (1 : ℝ) / 2 ≤ ‖1 - ε‖ := by
    have := norm_sub_norm_le (1 : ℂ) ε
    rw [norm_one] at this
    linarith
  have hkey : (G - A) * (1 - ℓ') = (u - û) + G * (ℓ - ℓ') + û * ε := by
    linear_combination hcyc + hnorm
  have hû : ‖û‖ ≤ 2 * ‖A‖ * ‖1 - ℓ'‖ := by
    have h := congrArg norm hnorm
    rw [norm_mul, norm_mul] at h
    have : ‖û‖ * (1 / 2) ≤ ‖A‖ * ‖1 - ℓ'‖ := by
      rw [← h]; exact mul_le_mul_of_nonneg_left h1ε (norm_nonneg _)
    linarith
  have hb : ‖G - A‖ * ‖1 - ℓ'‖ ≤ ‖u - û‖ + ‖ℓ - ℓ'‖ + 2 * ‖A‖ * ‖ε‖ * ‖1 - ℓ'‖ := by
    rw [← norm_mul, hkey]
    have h1 : ‖G * (ℓ - ℓ')‖ ≤ ‖ℓ - ℓ'‖ := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hG (norm_nonneg _)).trans (by rw [one_mul])
    have h2 : ‖û * ε‖ ≤ 2 * ‖A‖ * ‖ε‖ * ‖1 - ℓ'‖ := by
      rw [norm_mul]
      calc ‖û‖ * ‖ε‖ ≤ 2 * ‖A‖ * ‖1 - ℓ'‖ * ‖ε‖ :=
            mul_le_mul_of_nonneg_right hû (norm_nonneg _)
        _ = 2 * ‖A‖ * ‖ε‖ * ‖1 - ℓ'‖ := by ring
    calc ‖(u - û) + G * (ℓ - ℓ') + û * ε‖
        ≤ ‖u - û‖ + ‖G * (ℓ - ℓ')‖ + ‖û * ε‖ := norm_add₃_le
      _ ≤ ‖u - û‖ + ‖ℓ - ℓ'‖ + 2 * ‖A‖ * ‖ε‖ * ‖1 - ℓ'‖ := by linarith
  have hdiv : ‖G - A‖ ≤ (‖u - û‖ + ‖ℓ - ℓ'‖) / ‖1 - ℓ'‖ + 2 * ‖A‖ * ‖ε‖ := by
    rw [div_add' _ _ _ hℓ0.ne', le_div_iff₀ hℓ0]
    linarith
  refine hdiv.trans ?_
  gcongr
