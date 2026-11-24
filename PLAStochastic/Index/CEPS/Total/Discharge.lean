import PLAStochastic.Index.CEPS.Total.Close
import PLAStochastic.Index.CEPS.Total.PairForm
import PLAStochastic.Index.CEPS.Total.SobolevSup
import PLAStochastic.Index.CEPS.StripError.Pair

/-!
# WP10: S-9 unconditionally

WP9's S-6 (`ceps_pair_error`) on the level domain, with the level density (which is
`2^n`-Lipschitz, `CepsLevelDensity.lipschitz`) and the identification of the physical normal pair
with `cepsNormalRegularPair` (`cepsPhysicalPair_eq_normalData`), gives the level premise
`CepsPairCloseLevel n` for every `n` (`cepsPairCloseLevel`). Hence

  `cepsNormalClose : CepsNormalClose cepsNormalGn`,

the S-9 estimate `|E e^{-tS_T} - Ĝ_w(t)| ≤ K εᵖ e^{-cε}` in the form of `Glue/Defs.lean`.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf

namespace PGM

theorem cepsLevelCutoff_le_stripPairMu (n : ℕ) :
    cepsLevelCutoff n ≤ (cepsLevelDomain n).stripPairMu (cepsLevelScale n) := by
  obtain ⟨hR, hμ8, -, h12⟩ := cepsLevelCutoff_le n
  set dom := cepsLevelDomain n
  have hμ₀ := dom.μ₀_pos
  have h1 := dom.μ₀_c₀
  have h2 := dom.c₀_le
  have h3 := dom.ρA_one
  have hc0 := dom.c₀_pos
  have hS1 : 1 ≤ cepsLevelScale n := one_le_pow₀ (by norm_num)
  have hstep : cepsLevelScale n ≤ cepsLevelStepD n :=
    le_mul_of_one_le_right (cepsLevelScale_pos n).le (Real.one_le_exp (cepsLevelRate_pos n).le)
  have hD1 : 1 ≤ cepsLevelStepD n := hS1.trans hstep
  have hVD : cepsVarLo (cepsLevelStepD n) * cepsLevelStepD n ≤ 1 / 256 := by
    unfold cepsVarLo
    have hD0 : 0 < cepsLevelStepD n := by linarith
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hV0 : 0 < cepsVarLo (cepsLevelStepD n) := cepsVarLo_pos (by linarith)
  have hμ : dom.μ₀ ≤ 1 / (64 * cepsLevelScale n) := by
    have hc : dom.c₀ ≤ 1 / 1000 := by linarith
    rw [le_div_iff₀ (by have := cepsLevelScale_pos n; positivity)]
    -- `μ₀ · 64 · 2^n ≤ μ₀ · 64 · D ≤ 4 D V c₀ ≤ 1`
    have e1 : dom.μ₀ * (64 * cepsLevelScale n) ≤ dom.μ₀ * (64 * cepsLevelStepD n) := by
      gcongr
    have e2 : dom.μ₀ * (64 * cepsLevelStepD n) ≤
        4 * (cepsVarLo (cepsLevelStepD n) * cepsLevelStepD n) * dom.c₀ := by
      nlinarith
    have e3 : 4 * (cepsVarLo (cepsLevelStepD n) * cepsLevelStepD n) * dom.c₀ ≤
        4 * (1 / 256) * (1 / 1000) := by
      gcongr
    linarith
  unfold CepsCanonDomain.stripPairMu
  refine le_min (le_min hR ?_) h12
  linarith

/-- **S-6 on every level**, from WP9's `ceps_pair_error`. -/
theorem cepsPairCloseLevel (n : ℕ) : CepsPairCloseLevel n := by
  set dom := cepsLevelDomain n
  have hθ := cepsLevelRate_pos n
  have hD := cepsLevelStepD_pos n
  have hM := cepsLevelScale_pos n
  have hvhi : cepsLevelRate n ≤ cepsLevelScale n := by
    unfold cepsLevelRate cepsLevelScale
    exact (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))).trans (one_le_pow₀ (by norm_num))
  obtain ⟨K, hK⟩ := ceps_pair_error dom hθ hD (Dg := cepsLevelScale n) (θg := cepsLevelRate n)
    (vlo := cepsLevelRate n) (vhi := cepsLevelScale n) hM hθ hθ hvhi
    (Real.toNNReal (cepsLevelScale n))
  have hmark := dom.stripPairMark_pos hD hM.le
  have hρA := dom.ρA_pos
  have hq₀ := dom.q₀_pos
  set t₀ := min dom.stripPairMark (min (dom.ρA / 2) (dom.q₀ / 4))
  have ht₀ : 0 < t₀ := lt_min hmark (lt_min (by positivity) (by positivity))
  refine ⟨K, dom.c₀ / 32, t₀, dom.stripPairWidth, 33, by have := dom.c₀_pos; positivity, ht₀, ?_⟩
  intro eps heps ν f hdens y hy0 hy μ hμ
  obtain ⟨hreg, hgap, hW, -, -⟩ := hdens.stepLaw
  obtain ⟨-, -, hLip⟩ := hdens.lipschitz
  have hδ := cepsLevelCutoff_le_stripPairMu n
  have hμa : |μ| ≤ cepsLevelCutoff n := abs_le.mpr hμ
  have heps1 : 1 ≤ eps := (le_max_right _ _).trans heps
  have heps0 : 0 < eps := by linarith
  have hyn : ‖Complex.I * (y : ℂ)‖ = |y| := by
    rw [norm_mul, Complex.norm_I, one_mul, norm_real, Real.norm_eq_abs]
  have hmain := hK ν f (fun x => f (1 - x)) hreg hgap hLip hW μ (hμa.trans hδ) (Complex.I * y)
    (by simp) (by rw [hyn]; exact hy.trans (min_le_left _ _)) eps heps
  -- the physical pair is the regular normal pair
  set b := (2 * eps)⁻¹ with hb_def
  have hb : 0 < b := by positivity
  have htz : (b : ℂ) ^ 2 * (Complex.I * ((4 * eps ^ 2 * y : ℝ) : ℂ)) = Complex.I * y := by
    rw [hb_def]; exact scaled_mark_eq heps0 y
  obtain ⟨-, hμ8, -, h12⟩ := cepsLevelCutoff_le n
  have hμ₀ : |μ| ≤ dom.μ₀ := by have := dom.μ₀_pos; linarith
  have hy4 : |y| ≤ dom.q₀ / 4 := hy.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hq : ‖(b : ℂ) ^ 2 * (Complex.I * ((4 * eps ^ 2 * y : ℝ) : ℂ)) * (1 + (μ : ℂ))‖ < dom.q₀ := by
    rw [htz, norm_mul, hyn]
    have h1 : ‖1 + (μ : ℂ)‖ ≤ 3 / 2 := by
      calc ‖1 + (μ : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖(μ : ℂ)‖ := norm_add_le _ _
        _ ≤ 3 / 2 := by rw [norm_one, norm_real, Real.norm_eq_abs]; linarith
    calc |y| * ‖1 + (μ : ℂ)‖ ≤ dom.q₀ / 4 * (3 / 2) :=
          mul_le_mul hy4 h1 (norm_nonneg _) (by positivity)
      _ < dom.q₀ := by linarith
  have ht : (b : ℂ) ^ 2 * (Complex.I * ((4 * eps ^ 2 * y : ℝ) : ℂ)) ∈ ball (0 : ℂ) dom.ρA := by
    rw [htz, mem_ball_zero_iff, hyn]
    have := hy.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hpair := cepsPhysicalPair_eq_normalData dom hW hθ hD hb hμ₀ hq ht
  have hw : (b : ℂ)⁻¹ = ((2 * eps : ℝ) : ℂ) := by rw [hb_def]; push_cast; rw [inv_inv]
  rw [htz, hw] at hpair
  rw [hpair]
  exact hmain

/-- **S-9 (C20)**: the actual transform is exponentially close to the normal transform
`cepsNormalGn`, in the form required by `Glue/Main.lean`. -/
theorem cepsNormalClose : CepsNormalClose cepsNormalGn :=
  cepsNormalClose_of_pairClose cepsPairCloseLevel

end PGM
