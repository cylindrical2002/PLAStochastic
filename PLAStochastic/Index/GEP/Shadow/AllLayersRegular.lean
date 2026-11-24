import PLAStochastic.Index.GEP.Shadow.PairedHypotheses

/-!
# WP3: every shadow layer is a regular law (`regLaw_shLawPM_all`)

`memory-route.md` §4–5 (closure along the shadow and the shadow exponential density tail):
there are `D, θ, v₋, v₊, e₀`, independent of `eps` and `ℓ`, with
`η_ℓ = shLawPM … eps ℓ ∈ RegLaw D θ v₋ v₊` for all `eps ≥ e₀` and `ℓ ≥ 1`.

The constants of the passive class are fixed first and do not involve a density bound
(`GEPShadowPairedActual`): `MomClass KcIn shBeta shVlo` with `E e^{(θK/2) Y} ≤ CK`, the active tail
`(72/71) e^{-shAT R/eps²}`, the active mean bracket `[eps²/(128 bIn), cPlus eps²/vIn]` and
`E (X - Y)² ≤ shKd/eps²`.  `pairedLaw_envelope` for these constants gives envelope constants
`K, c` that do not depend on the passive density bound.  With `Ds = max(envK1, K)` and
`θ' = min(envC1, c)`, induction on `ℓ ≥ 1` keeps `EnvBd Ds θ' η_ℓ`:

* `ℓ = 1`: `envBd_shLaw_one` (the Gamma mixture over the local stopping bound);
* `ℓ → ℓ + 1`: `EnvBd.locBd` gives `LocBd Ds η_ℓ`; `pairedHyp_shPair` and `shLaw_momClass` give the
  hypotheses of `pairedLaw_envelope` at the fixed density bound `Ds`, and `shLaw_active_sum`
  identifies the law of `A^X/C_X` with `η_{ℓ+1}`.

`regLaw_of_envBd_of_moments` with `lawMean_shLawPM` and `shLaw_variance_bracket` then gives
`RegLaw Ds θ' (vIn/4) KcIn η_ℓ`.  The threshold `e₀` is the maximum of `epsK`, the two scale
conditions of `shLaw_variance_bracket` (`shScaleEps`) and the threshold of `pairedLaw_envelope`
at `Ds`.  Besides `GapLaw`, the proof uses the raw positivity `hpos` of the gaps (active cyclic
counting and the first-layer local bound).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}

/-- The scale threshold: `epsK` and the two conditions of `shLaw_variance_bracket`. -/
def shScaleEps (P : Measure Ω) (g : ℕ → Ω → ℝ) (μ₀ σ₀ : ℝ) : ℝ :=
  max (epsK (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))))
    (max (Real.sqrt (cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀)))
      (Real.sqrt (4 * cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) * (σ₀ ^ 2 / μ₀ ^ 2 + 1) / vIn μ₀ σ₀)))

omit [IsProbabilityMeasure P] in
theorem shScale_of_le (hμ : 0 < μ₀) (hσ : 0 < σ₀) {eps : ℝ}
    (h : shScaleEps P g μ₀ σ₀ ≤ eps) : ShScale P g μ₀ σ₀ eps := by
  have h1 : epsK (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps :=
    le_trans (le_max_left _ _) h
  have h2 : Real.sqrt (cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀)) ≤ eps :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h
  have h3 : Real.sqrt (4 * cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) * (σ₀ ^ 2 / μ₀ ^ 2 + 1) / vIn μ₀ σ₀) ≤
      eps := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h
  have hcb : 0 < cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) :=
    lt_of_lt_of_le (by have := bAbs_pos.trans_le (bAbs_le_bIn μ₀ σ₀); positivity)
      (le_max_left _ _)
  have hv := vIn_pos hμ hσ
  have hsq : ∀ x : ℝ, 0 ≤ x → Real.sqrt x ≤ eps → x ≤ eps ^ 2 := by
    intro x hx hle
    have := pow_le_pow_left₀ (Real.sqrt_nonneg x) hle 2
    rwa [Real.sq_sqrt hx] at this
  refine ⟨h1, hsq _ hcb.le h2, ?_⟩
  have h4 := hsq _ (by positivity) h3
  rw [div_le_iff₀ hv] at h4
  linarith

/-- **All shadow layers are regular laws**, with constants independent of `eps` and `ℓ`. -/
theorem regLaw_shLawPM_all (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) :
    ∃ D θ vlo vhi e0 : ℝ, 0 < D ∧ 0 < θ ∧ 0 < vlo ∧ vlo ≤ vhi ∧
      ∀ eps, e0 ≤ eps → ∀ ℓ, 1 ≤ ℓ → RegLaw D θ vlo vhi (shLawPM P hg.iid.measurable eps ℓ) := by
  have hμ := hg.mu_pos
  have hσ := hg.sigma_pos
  have hb0 : 0 < bIn μ₀ σ₀ := bAbs_pos.trans_le (bAbs_le_bIn μ₀ σ₀)
  have hv0 := vIn_pos hμ hσ
  have hcmcp : 1 / (128 * bIn μ₀ σ₀) ≤ cPlus / vIn μ₀ σ₀ := by
    have h1 : 1 / (128 * bIn μ₀ σ₀) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have hbb : bAbs ≤ bIn μ₀ σ₀ := bAbs_le_bIn _ _
      have hb1 : (1 : ℝ) ≤ bAbs := by unfold bAbs K2; norm_num
      linarith
    have h2 : 1 ≤ cPlus / vIn μ₀ σ₀ := by
      rw [le_div_iff₀ hv0]
      have := vIn_le_half μ₀ σ₀
      unfold cPlus
      linarith
    linarith
  obtain ⟨K, c, hK, hc, henv⟩ := pairedLaw_envelope (Ω := Ω × (ℕ → ℝ))
    (b := KcIn) (β := shBeta μ₀ σ₀) (vmin := shVlo μ₀ σ₀) (θ₁ := θK / 2) (B₁ := CK)
    (At := 72 / 71) (aT := shAT μ₀ σ₀) (Kd := shKd μ₀ σ₀)
    (cm := 1 / (128 * bIn μ₀ σ₀)) (cp := cPlus / vIn μ₀ σ₀)
    (shVlo_pos hμ hσ) (shVlo_le_KcIn μ₀ σ₀) (one_le_shBeta μ₀ σ₀)
    (by have := θK_pos; positivity) CK_pos (by norm_num) (shAT_pos hμ hσ)
    (shKd_nonneg μ₀ σ₀) (by positivity) hcmcp
  set Ds := max (envK1 μ₀ σ₀) K with hDs
  set θ' := min (envC1 μ₀ σ₀) c with hθ'
  have hDs0 : 0 < Ds := lt_of_lt_of_le (envK1_pos hμ hσ) (le_max_left _ _)
  have hθ'0 : 0 < θ' := lt_min (envC1_pos hμ hσ) hc
  obtain ⟨e₁, he₁⟩ := henv Ds hDs0
  refine ⟨Ds, θ', shVlo μ₀ σ₀, KcIn, max (shScaleEps P g μ₀ σ₀) e₁, hDs0, hθ'0,
    shVlo_pos hμ hσ, shVlo_le_KcIn μ₀ σ₀, ?_⟩
  intro eps heps
  have hs : ShScale P g μ₀ σ₀ eps := shScale_of_le hμ hσ (le_trans (le_max_left _ _) heps)
  have he₁' : e₁ ≤ eps := le_trans (le_max_right _ _) heps
  have heps0 := hs.epsZero_le
  have key : ∀ ℓ, 1 ≤ ℓ → EnvBd Ds θ' (shLaw P eps g ℓ) := by
    intro ℓ hℓ
    induction ℓ, hℓ using Nat.le_induction with
    | base =>
      exact (envBd_shLaw_one hg hpos heps0).mono (envK1_pos hμ hσ).le (le_max_left _ _)
        (min_le_left _ _)
    | succ ℓ hℓ ih =>
      have hloc : LocBd Ds
          ((shLawPM P hg.iid.measurable eps ℓ : ProbabilityMeasure ℝ) : Measure ℝ) :=
        ih.locBd hDs0.le hθ'0.le
      have hbr := actMean_shPair_bracket hg heps0 ℓ
      have h := he₁ eps he₁' (shP P) (shPair P eps g ℓ) (shLawPM P hg.iid.measurable eps ℓ)
        (pairedHyp_shPair hg hpos hs hℓ) (shLaw_momClass hg hs hℓ)
        (expMom_shLawPM hg hs.epsK_le ℓ) hloc hbr.1 hbr.2
      rw [shLaw_active_sum hg heps0 ℓ] at h
      exact h.mono hK.le (le_max_right _ _) (min_le_right _ _)
  intro ℓ hℓ
  have hbr := shLaw_variance_bracket hg heps0 hs.scale hs.small hℓ
  exact regLaw_of_envBd_of_moments (lawMean_shLawPM hg heps0 ℓ) hbr.1 hbr.2 (key ℓ hℓ) hDs0.le

end

end PGM
