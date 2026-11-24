import PLAStochastic.Index.CEPS.Total.Reflection
import PLAStochastic.Index.CEPS.Actual.Drawup

/-!
# WP10: S-8, the fixed-drift drawup

For the `Y_δ`-walk (`kWalk 0 (1+δ) 1`), the actual drawup transform `G = cepsDrawup` satisfies the
exact cycle identity `G (1 - ℓ^bot) = u^bot` (WP8 `cepsDrawup_cycle`), and `‖G‖ ≤ 1`. The
bottom-started actual exits `u^bot`, `ℓ^bot` are compared (S-3, WP9) with the top-started normal
exits of the reflected data, which are the bottom-started normal exits `botUpperExit`,
`botLowerExit` of the original data (`reflected_exits_actual`). The normal identity (3.9) and the
class-uniform bounds (`drawup_normal_bounds`) then give (`drawup_close_of_exit_error`)

  `‖G - 𝒜_δ(t) e^{-(β₊-t) l}‖ ≤ e/G₀ + C e^{-c l}`

whenever the bottom exit error is at most `e`.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf

namespace PGM

theorem norm_cepsDrawup_le_one (ν : ProbabilityMeasure ℝ) (β a l : ℝ) {s q : ℂ}
    (hs : s.re = 0) (hq : 0 ≤ q.re) : ‖cepsDrawup ν β a l s q‖ ≤ 1 := by
  have hsum := summable_cepsDrawup ν β a l hs hq
  have hP : ∀ K : ℕ, ∑ N ∈ Finset.range K, cepsDrawupProb ν β a l N ≤ 1 := by
    intro K
    have hint : ∀ N, Integrable ({g : ℕ → ℝ | cepsDrawupCross β a l g N}.indicator
        (fun _ => (1 : ℝ))) (iidLaw ν) := fun N =>
      (integrable_const (1 : ℝ)).indicator (measurableSet_cepsDrawupCross β a l N)
    have e : ∀ N, cepsDrawupProb ν β a l N = ∫ g, {g : ℕ → ℝ | cepsDrawupCross β a l g N}.indicator
        (fun _ => (1 : ℝ)) g ∂(iidLaw ν) := fun N => by
      rw [integral_indicator (measurableSet_cepsDrawupCross β a l N), setIntegral_const,
        smul_eq_mul, mul_one]
      rfl
    simp_rw [e]
    rw [← integral_finsetSum _ fun N _ => hint N]
    exact (integral_mono (integrable_finsetSum _ fun N _ => hint N) (integrable_const 1)
      fun g => cepsDrawupCross_disjoint β a l g K).trans (by simp)
  have hle : ∀ N : ℕ, ‖Complex.exp (-q * ((N : ℂ) + 1)) * cepsDrawupTerm ν β a l s N‖ ≤
      cepsDrawupProb ν β a l N := fun N => by
    rw [norm_mul]
    calc _ ≤ 1 * cepsDrawupProb ν β a l N :=
          mul_le_mul (norm_cexp_neg_mul_succ_le_one hq N) (norm_cepsDrawupTerm_le ν β a l hs N)
            (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  calc ‖cepsDrawup ν β a l s q‖
      ≤ ∑' N : ℕ, ‖Complex.exp (-q * ((N : ℂ) + 1)) * cepsDrawupTerm ν β a l s N‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' N : ℕ, cepsDrawupProb ν β a l N :=
        hsum.tsum_le_tsum hle (summable_cepsDrawupProb ν β a l)
    _ ≤ 1 := Real.tsum_le_of_sum_range_le (fun N => measureReal_nonneg) hP

namespace CepsNormalData

/-- The drawup objects only see `Q` at `t`, `β₊`, `β₋`. -/
theorem drawup_objects_congr (a b : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q t l : ℂ)
    (hp : a.βp = b.βp) (hm : a.βm = b.βm) (hψ : a.ψp = b.ψp)
    (hQt : a.Q t = b.Q t) (hQp : a.Q a.βp = b.Q b.βp) (hQm : a.Q a.βm = b.Q b.βm) :
    a.botUpperExit L μ q t l = b.botUpperExit L μ q t l ∧
      a.botLowerExit L μ q t l = b.botLowerExit L μ q t l ∧
      a.drawupKappa L μ q t = b.drawupKappa L μ q t ∧
      a.regularAmplitude L μ q t = b.regularAmplitude L μ q t ∧
      a.decay l = b.decay l := by
  have heta : a.eta = b.eta := by rw [eta, eta, hp, hm]
  have hfm : ∀ ζ, a.Q ζ = b.Q ζ → a.factorMinus L μ q ζ = b.factorMinus L μ q ζ := by
    intro ζ h; rw [factorMinus, factorMinus, h]
  have hgap : ∀ ζ, a.Q ζ = b.Q ζ → a.ladderGap L μ q ζ = b.ladderGap L μ q ζ := by
    intro ζ h; rw [ladderGap, ladderGap, hfm ζ h, hm]
  have hQp' : a.Q b.βp = b.Q b.βp := by rw [← hp]; exact hQp.trans (by rw [hp])
  have hQm' : a.Q b.βm = b.Q b.βm := by rw [← hm]; exact hQm.trans (by rw [hm])
  have hgp : a.ladderGap L μ q a.βp = b.ladderGap L μ q b.βp := by rw [hp]; exact hgap _ hQp'
  have hgt : a.ladderGap L μ q t = b.ladderGap L μ q t := hgap _ hQt
  have hBmt : a.overshootMinus L μ q (t - a.βm) = b.overshootMinus L μ q (t - b.βm) := by
    rw [overshootMinus, overshootMinus, hm, add_sub_cancel, hfm _ hQt, hfm _ hQm']
  have hBp : ∀ s, a.overshootPlus L μ q s = b.overshootPlus L μ q s := by
    intro s; rw [overshootPlus, overshootPlus, hp]
  have hpi : a.pi L μ q = b.pi L μ q := by rw [pi, pi, hQp, hQm, hp, hm]
  have hdecay : a.decay l = b.decay l := by rw [decay, decay, heta]
  have hdelta : a.delta L μ q l = b.delta L μ q l := by rw [delta, delta, hdecay, hpi]
  refine ⟨?_, ?_, ?_, ?_, hdecay⟩
  · rw [botUpperExit, botUpperExit, hBp, hgp, hdelta, hp]
  · rw [botLowerExit, botLowerExit, hgt, hBmt, hdecay, heta, hBp, hgp, hdelta]
  · rw [drawupKappa, drawupKappa, hpi, hBmt, heta, hBp, hgp, hgt]
  · rw [regularAmplitude, regularAmplitude, hψ, hm, hp, hQt]

end CepsNormalData

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
/-- **S-8 (local form).** For the `Y_δ` drawup at fixed drift `0 < δ ≤ μ₀`, an exit error `e` of
the bottom-started strip (in the WP9 form: actual `cepsStripExit` against the reflected
top-started normal exits) gives `‖G - 𝒜_δ(t) e^{-(β₊-t) l}‖ ≤ e/G₀ + C e^{-c l}`. -/
theorem drawup_close_of_exit_error (hv : 0 < v) {δ : ℝ} (hδ : 0 < δ) (hδμ : δ ≤ dom.μ₀) :
    ∃ G₀ C l₀ : ℝ, 0 < G₀ ∧ 0 ≤ l₀ ∧
      ∀ (ν : ProbabilityMeasure ℝ) (fW : ℝ → ℝ),
        IsStepLaw ((ν : Measure ℝ).map fun x => 1 - x) fW D θ v →
      ∀ t : ℂ, t.re = 0 → ‖t‖ ≤ dom.c₀ / 4 → ‖t * (1 + (δ : ℂ))‖ ≤ dom.q₀ →
      ∀ l : ℝ, l₀ ≤ l → ∀ e : ℝ,
        let ρW := (ν : Measure ℝ).map fun x => 1 - x
        let q := t * (1 + (δ : ℂ))
        let a' := cepsNormalData D θ (ρW.map Neg.neg) ((-δ : ℝ) : ℂ) q
        let L' := dom.canonL (ρW.map Neg.neg)
        ‖cepsStripExit ν (1 + δ) 1 l 0 (Iio 0) t q - a'.upperExit L' ((-δ : ℝ) : ℂ) q (-t) l‖ +
            ‖cepsStripExit ν (1 + δ) 1 l 0 (Ioi l) t q -
              a'.lowerExit L' ((-δ : ℝ) : ℂ) q (-t) l‖ ≤ e →
        ‖cepsDrawup ν (1 + δ) 1 l t q -
            (cepsWHNormalData D θ ρW δ q).regularAmplitude (dom.canonL ρW) δ q t *
              exp (-((cepsWHNormalData D θ ρW δ q).βp - t) * l)‖ ≤
          e / G₀ + C * Real.exp (-dom.drawupRate δ * l) := by
  obtain ⟨Cκ, G₀, Ca, l₀, hG₀, hl₀, hCκ, hCa, hb⟩ := drawup_normal_bounds dom hθ hD hv hδ hδμ
  refine ⟨G₀, 2 * Ca * Cκ, l₀, hG₀, hl₀, ?_⟩
  intro ν fW hW t ht0 ht hq l hl e ρW q a' L' hexit
  have hμ : |δ| ≤ dom.μ₀ := by rwa [abs_of_pos hδ]
  have hμc : ‖(δ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hq0 : 0 ≤ q.re := by
    show 0 ≤ (t * (1 + (δ : ℂ))).re
    simp [mul_re, ht0]
  have hl0 : 0 ≤ l := hl₀.trans hl
  obtain ⟨hid, hκ, hκ2, hgap, hamp⟩ := hb ρW fW hW t ht0 ht hq l hl
  -- the reflected exits are the bottom exits of the original data
  obtain ⟨hU, hLo⟩ := reflected_exits_actual dom hW hθ hD hμ hq0 hq ht (l : ℂ)
  -- `cepsNormalData` and `cepsWHNormalData` agree on the drawup objects
  have hc0 := dom.c₀_pos
  have hρA : dom.c₀ / 4 < dom.ρA := by have := dom.c₀_le; have := dom.ρA_pos; linarith
  have hball : ∀ ζ : ℂ, ‖ζ‖ ≤ dom.c₀ / 4 →
      cepsQ D θ ρW δ q ζ = cepsQuotA D θ ρW δ q ζ := fun ζ hζ =>
    CepsC6.cepsQ_eq_cepsQuotA dom hW hθ hD hμc hq (mem_ball_zero_iff.mpr (by linarith))
  obtain ⟨cU, cL, -, -, -⟩ := CepsNormalData.drawup_objects_congr
    (cepsWHNormalData D θ ρW δ q) (cepsNormalData D θ ρW δ q) (dom.canonL ρW) δ q t l
    rfl rfl rfl (hball t ht) (hball _ (dom.norm_rootPlus_le hW hθ hD hμc hq))
    (hball _ (dom.norm_rootMinus_le hW hθ hD hμc hq))
  rw [hU, ← cL] at hexit
  rw [hLo, ← cU] at hexit
  -- cycle identity and the perturbation bound
  have hcyc := cepsDrawup_cycle ν (1 + δ) 1 hl0 (s := t) (q := q) ht0 hq0
  have hG := norm_cepsDrawup_le_one ν (1 + δ) 1 l (s := t) (q := q) ht0 hq0
  have key := norm_cycle_sub_le hG₀ hcyc hG hid hκ2 hgap
  set A := (cepsWHNormalData D θ ρW δ q).regularAmplitude (dom.canonL ρW) δ q t *
    exp (-((cepsWHNormalData D θ ρW δ q).βp - t) * l)
  have h1 : (‖cepsStripExit ν (1 + δ) 1 l 0 (Ioi l) t q -
      (cepsWHNormalData D θ ρW δ q).botUpperExit (dom.canonL ρW) δ q t l‖ +
      ‖cepsStripExit ν (1 + δ) 1 l 0 (Iio 0) t q -
        (cepsWHNormalData D θ ρW δ q).botLowerExit (dom.canonL ρW) δ q t l‖) / G₀ ≤ e / G₀ := by
    gcongr; linarith
  have h2 : 2 * ‖A‖ * ‖(cepsWHNormalData D θ ρW δ q).decay l *
      (cepsWHNormalData D θ ρW δ q).drawupKappa (dom.canonL ρW) δ q t‖ ≤
      2 * Ca * Cκ * Real.exp (-dom.drawupRate δ * l) := by
    have := mul_le_mul hamp hκ (norm_nonneg _) hCa
    nlinarith [norm_nonneg A]
  linarith

end PGM
