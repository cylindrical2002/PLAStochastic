import PLAStochastic.Index.CEPS.Total.DrawupAlgebra
import PLAStochastic.Index.CEPS.Normal.ActualPiBounds
import PLAStochastic.Index.CEPS.Normal.ActualBudget
import PLAStochastic.Index.CEPS.Normal.ActualRootSector
import PLAStochastic.Index.CEPS.Scaled.RootDirections
import PLAStochastic.Index.CEPS.Scaled.LadderSigns

/-!
# WP10: class-uniform bounds for the fixed-drift normal drawup (blueprint (3.9))

At a fixed positive drift `δ ≤ μ₀`, marked discount `q = t(1+δ)` with `t ∈ iℝ` small, the actual
Morse data (`cepsWHNormalData`, `Q = cepsQ`) and canonical factor `dom.canonL` give

* `‖E κ_t‖ ≤ C e^{-c l}` and `≤ 1/2` for `l ≥ l₀` (`E = e^{-η l}`, `Re η ≥ c δ`);
* `‖1 - ℓ̂_t‖ ≥ c` (the descending ladder gap `1 - A₋(t)` is bounded below since `Re β₋ ≤ -c δ`);
* `‖𝒜(t) e^{-(β₊-t) l}‖ ≤ C` (`Re β₊ ≥ 0`);

with constants depending only on the class `(D, θ, v)`, the domain `dom` and `δ`, together with
the exact identity `botExit_drawup_identity`.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf

namespace PGM

theorem norm_exp_le_exp_norm' (z : ℂ) : ‖exp z‖ ≤ Real.exp ‖z‖ := by
  rw [norm_exp]; exact Real.exp_le_exp.mpr (re_le_norm z)

theorem exp_neg_norm_le_norm_exp' (z : ℂ) : Real.exp (-‖z‖) ≤ ‖exp z‖ := by
  rw [norm_exp]; exact Real.exp_le_exp.mpr (by linarith [neg_abs_le z.re, abs_re_le_norm z])

end PGM

namespace PGM.CepsNormalData

variable (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q : ℂ)

/-- Abstract form of the (3.9) bounds: from numeric bounds on `L`, `Q`, `η`, `Π`, the lower
root gap and the decay, the correction `E κ`, the gap `1 - ℓ̂` and the amplitude are bounded. -/
theorem drawup_abstract_bounds {t l : ℂ} {B V vq H Pm m₀ e : ℝ}
    (hQp : a.Q a.βp ≠ 0) (hQm : a.Q a.βm ≠ 0) (hQt : a.Q t ≠ 0) (hψ : a.ψp = a.eta * a.Q a.βp)
    (hLt : ‖L μ q t‖ ≤ B) (hLp : ‖L μ q a.βp‖ ≤ B) (hLm : ‖L μ q a.βm‖ ≤ B)
    (hvq : 0 < vq) (hQtl : vq ≤ ‖a.Q t‖) (hQth : ‖a.Q t‖ ≤ V) (hQph : ‖a.Q a.βp‖ ≤ V)
    (hQml : vq ≤ ‖a.Q a.βm‖) (hη : ‖a.eta‖ ≤ H) (hpi : ‖a.pi L μ q‖ ≤ Pm)
    (hm₀ : 0 < m₀) (hm : m₀ ≤ ‖t - a.βm‖) (he0 : 0 ≤ e) (hE : ‖a.decay l‖ ≤ e)
    (hEp : ‖exp (-(a.βp - t) * l)‖ ≤ 1)
    (hsmall : e * (Pm + (V * Real.exp B / (vq * Real.exp (-B))) * Real.exp (2 * B) *
      (H * V * Real.exp B) / (m₀ * vq * Real.exp (-B))) ≤ 1 / 2)
    (hsmall' : e * Pm ≤ 1 / 2) :
    a.botUpperExit L μ q t l * (1 - a.decay l * a.drawupKappa L μ q t) =
        a.regularAmplitude L μ q t * exp (-(a.βp - t) * l) * (1 - a.botLowerExit L μ q t l) ∧
      ‖a.decay l * a.drawupKappa L μ q t‖ ≤ e * (Pm + (V * Real.exp B / (vq * Real.exp (-B))) *
        Real.exp (2 * B) * (H * V * Real.exp B) / (m₀ * vq * Real.exp (-B))) ∧
      ‖a.decay l * a.drawupKappa L μ q t‖ ≤ 1 / 2 ∧
      m₀ * vq * Real.exp (-B) / 3 ≤ ‖1 - a.botLowerExit L μ q t l‖ ∧
      ‖a.regularAmplitude L μ q t * exp (-(a.βp - t) * l)‖ ≤
        H * V * Real.exp (4 * B) / (m₀ * vq) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hLt
  have hexpB := Real.exp_pos B
  have hexpnB := Real.exp_pos (-B)
  have hnexp_le : ∀ z : ℂ, ‖z‖ ≤ B → ‖exp z‖ ≤ Real.exp B := fun z hz =>
    (norm_exp_le_exp_norm' z).trans (Real.exp_le_exp.mpr hz)
  have hnexp_ge : ∀ z : ℂ, ‖z‖ ≤ B → Real.exp (-B) ≤ ‖exp z‖ := fun z hz =>
    (Real.exp_le_exp.mpr (neg_le_neg hz)).trans (exp_neg_norm_le_norm_exp' z)
  have htm : t - a.βm ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hm₀ hm)
  -- the four building blocks
  have hgt : a.ladderGap L μ q t = (t - a.βm) * a.Q t / exp (L μ q t) :=
    ladderGap_eq a L μ q hQt
  have hgp : a.ladderGap L μ q a.βp = a.eta * a.Q a.βp / exp (L μ q a.βp) := by
    rw [ladderGap_eq a L μ q hQp]; rfl
  have hBm : a.overshootMinus L μ q (t - a.βm) =
      (a.Q t / exp (L μ q t)) / (a.Q a.βm / exp (L μ q a.βm)) := by
    rw [overshootMinus, add_sub_cancel, exp_sub, exp_factorMinus a L μ q hQt,
      exp_factorMinus a L μ q hQm]
  have hBp : a.overshootPlus L μ q a.eta = exp (L μ q a.βm) / exp (L μ q a.βp) := by
    rw [overshootPlus, show a.βp - a.eta = a.βm by rw [eta]; ring, exp_sub]
  have ngt : m₀ * vq * Real.exp (-B) ≤ ‖a.ladderGap L μ q t‖ := by
    rw [hgt, norm_div, norm_mul, le_div_iff₀ (norm_pos_iff.mpr (exp_ne_zero _))]
    calc m₀ * vq * Real.exp (-B) * ‖exp (L μ q t)‖ ≤ m₀ * vq * Real.exp (-B) * Real.exp B := by
          gcongr; exact hnexp_le _ hLt
      _ = m₀ * vq := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      _ ≤ ‖t - a.βm‖ * ‖a.Q t‖ := by gcongr
  have ngp : ‖a.ladderGap L μ q a.βp‖ ≤ H * V * Real.exp B := by
    rw [hgp, norm_div, norm_mul, div_le_iff₀ (norm_pos_iff.mpr (exp_ne_zero _))]
    calc ‖a.eta‖ * ‖a.Q a.βp‖ ≤ H * V := by gcongr; exact (norm_nonneg _).trans hη
      _ = H * V * Real.exp B * Real.exp (-B) := by
          rw [mul_assoc (H * V), ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ H * V * Real.exp B * ‖exp (L μ q a.βp)‖ := by
          have : 0 ≤ H * V := mul_nonneg ((norm_nonneg _).trans hη) ((norm_nonneg _).trans hQth)
          gcongr; exact hnexp_ge _ hLp
  have nBm : ‖a.overshootMinus L μ q (t - a.βm)‖ ≤ V * Real.exp B / (vq * Real.exp (-B)) := by
    have hV0 : 0 ≤ V := (norm_nonneg _).trans hQth
    have hpos : ∀ z : ℂ, 0 < ‖exp z‖ := fun z => norm_pos_iff.mpr (exp_ne_zero _)
    have num : ‖a.Q t‖ / ‖exp (L μ q t)‖ ≤ V * Real.exp B := by
      rw [div_le_iff₀ (hpos _)]
      calc ‖a.Q t‖ ≤ V := hQth
        _ = V * Real.exp B * Real.exp (-B) := by
            rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        _ ≤ V * Real.exp B * ‖exp (L μ q t)‖ := by gcongr; exact hnexp_ge _ hLt
    have den : vq * Real.exp (-B) ≤ ‖a.Q a.βm‖ / ‖exp (L μ q a.βm)‖ := by
      rw [le_div_iff₀ (hpos _)]
      calc vq * Real.exp (-B) * ‖exp (L μ q a.βm)‖ ≤ vq * Real.exp (-B) * Real.exp B := by
            gcongr; exact hnexp_le _ hLm
        _ = vq := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
        _ ≤ ‖a.Q a.βm‖ := hQml
    rw [hBm, norm_div, norm_div, norm_div]
    exact div_le_div₀ (by positivity) num (by positivity) den
  have nBp : ‖a.overshootPlus L μ q a.eta‖ ≤ Real.exp (2 * B) := by
    rw [hBp, norm_div, div_le_iff₀ (norm_pos_iff.mpr (exp_ne_zero _))]
    calc ‖exp (L μ q a.βm)‖ ≤ Real.exp B := hnexp_le _ hLm
      _ = Real.exp (2 * B) * Real.exp (-B) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (2 * B) * ‖exp (L μ q a.βp)‖ := by gcongr; exact hnexp_ge _ hLp
  have hgt0 : 0 < ‖a.ladderGap L μ q t‖ :=
    lt_of_lt_of_le (by positivity) ngt
  have nκ : ‖a.drawupKappa L μ q t‖ ≤ Pm + (V * Real.exp B / (vq * Real.exp (-B))) *
      Real.exp (2 * B) * (H * V * Real.exp B) / (m₀ * vq * Real.exp (-B)) := by
    unfold drawupKappa
    refine (norm_sub_le _ _).trans (add_le_add hpi ?_)
    rw [norm_div, norm_mul, norm_mul]
    have h1 : 0 ≤ V * Real.exp B / (vq * Real.exp (-B)) := (norm_nonneg _).trans nBm
    have h2 : 0 ≤ H * V * Real.exp B := (norm_nonneg _).trans ngp
    refine div_le_div₀ (by positivity) ?_ (by positivity) ngt
    exact mul_le_mul (mul_le_mul nBm nBp (norm_nonneg _) h1) ngp (norm_nonneg _) (by positivity)
  set Cκ := Pm + (V * Real.exp B / (vq * Real.exp (-B))) * Real.exp (2 * B) *
      (H * V * Real.exp B) / (m₀ * vq * Real.exp (-B)) with hCκ
  have hEκ : ‖a.decay l * a.drawupKappa L μ q t‖ ≤ e * Cκ := by
    rw [norm_mul]; exact mul_le_mul hE nκ (norm_nonneg _) he0
  have hEκ2 : ‖a.decay l * a.drawupKappa L μ q t‖ ≤ 1 / 2 := hEκ.trans hsmall
  have hEpi : ‖a.decay l * a.pi L μ q‖ ≤ 1 / 2 := by
    rw [norm_mul]; exact (mul_le_mul hE hpi (norm_nonneg _) he0).trans hsmall'
  have hΔ : a.delta L μ q l ≠ 0 := by
    intro h0
    have : a.decay l * a.pi L μ q = 1 := by rw [delta] at h0; linear_combination -h0
    rw [this, norm_one] at hEpi; norm_num at hEpi
  have hPm0 : 0 ≤ Pm := (norm_nonneg _).trans hpi
  have nΔ : ‖a.delta L μ q l‖ ≤ 3 / 2 := by
    unfold delta
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]; linarith
  have hid := botExit_drawup_identity a L μ q t l hψ hQp hQt htm hΔ
  have hlow := one_sub_botLowerExit_mul_delta a L μ q t l (norm_pos_iff.mp hgt0) hΔ
  refine ⟨hid, hEκ, hEκ2, ?_, ?_⟩
  · -- `‖1 - ℓ̂‖ ‖Δ‖ = ‖g(t)‖ ‖1 - E κ‖ ≥ ‖g(t)‖ / 2`
    have h1 : (1 : ℝ) / 2 ≤ ‖1 - a.decay l * a.drawupKappa L μ q t‖ := by
      have := norm_sub_norm_le (1 : ℂ) (a.decay l * a.drawupKappa L μ q t)
      rw [norm_one] at this; linarith
    have hn := congrArg norm hlow
    rw [norm_mul, norm_mul] at hn
    have hX0 := norm_nonneg (1 - a.botLowerExit L μ q t l)
    have hstep : m₀ * vq * Real.exp (-B) / 2 ≤ ‖a.ladderGap L μ q t‖ *
        ‖1 - a.decay l * a.drawupKappa L μ q t‖ := by nlinarith
    rw [← hn] at hstep
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  · unfold regularAmplitude
    rw [norm_mul, norm_div, norm_mul, norm_mul, hψ, norm_mul]
    have hE4 : ‖exp (2 * L μ q t - 2 * L μ q a.βp)‖ ≤ Real.exp (4 * B) := by
      refine (norm_exp_le_exp_norm' _).trans (Real.exp_le_exp.mpr ?_)
      calc ‖2 * L μ q t - 2 * L μ q a.βp‖ ≤ ‖2 * L μ q t‖ + ‖2 * L μ q a.βp‖ := norm_sub_le _ _
        _ ≤ 2 * B + 2 * B := by
            rw [norm_mul, norm_mul, Complex.norm_ofNat]; gcongr
        _ = 4 * B := by ring
    have hden : m₀ * vq ≤ ‖t - a.βm‖ * ‖a.Q t‖ := by gcongr
    have hH0 : 0 ≤ H := (norm_nonneg _).trans hη
    have hV0 : 0 ≤ V := (norm_nonneg _).trans hQth
    calc ‖a.eta‖ * ‖a.Q a.βp‖ * ‖exp (2 * L μ q t - 2 * L μ q a.βp)‖ /
          (‖t - a.βm‖ * ‖a.Q t‖) * ‖exp (-(a.βp - t) * l)‖
        ≤ H * V * Real.exp (4 * B) / (m₀ * vq) * 1 := by
          gcongr
      _ = _ := mul_one _

end PGM.CepsNormalData

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem canonL_norm_le_logBound {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    (hζ : ‖ζ‖ ≤ dom.c₀ / 2) : ‖dom.canonL ρW μ q ζ‖ ≤ dom.normalLogBound := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hL := dom.norm_cepsCanonL_le hW hθ hD (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμ' (ofReal_im μ) hq hζ
  exact hL

include hθ in
theorem normalLogBound_nonneg' : 0 ≤ dom.normalLogBound := by
  have hρ := dom.ρA_pos
  have hc := dom.c₀_pos
  unfold CepsCanonDomain.normalLogBound CepsCanonDomain.CL CepsCanonDomain.Linf
  positivity

include hW hθ hD in
/-- Pointwise estimates at one marked parameter point. -/
theorem drawup_pointwise {δ : ℝ} (hδ : 0 < δ) (hδμ : δ ≤ dom.μ₀) {t : ℂ} (ht0 : t.re = 0)
    (ht : ‖t‖ ≤ dom.c₀ / 4) (hq : ‖t * (1 + (δ : ℂ))‖ ≤ dom.q₀) :
    let q := t * (1 + (δ : ℂ))
    let a := cepsWHNormalData D θ ρW δ q
    let L := dom.canonL ρW
    let s := Real.sqrt (cepsVarLo D) / (3 * v) * δ
    a.ψp = a.eta * a.Q a.βp ∧ a.Q a.βp ≠ 0 ∧ a.Q a.βm ≠ 0 ∧ a.Q t ≠ 0 ∧
      s / (2 * Real.sqrt v) ≤ a.eta.re ∧ 0 ≤ a.βp.re ∧
      s / (4 * Real.sqrt v) ≤ ‖t - a.βm‖ ∧
      ‖a.eta‖ ≤ 2 * cepsChartK D * dom.rmax ∧
      ‖a.pi L δ q‖ ≤ 1 + dom.normalPiBound * (2 * cepsChartK D * dom.rmax) ∧
      (∀ ζ ∈ ({t, a.βp, a.βm} : Set ℂ), ‖L δ q ζ‖ ≤ dom.normalLogBound ∧
        cepsVarLo D / 4 ≤ ‖a.Q ζ‖ ∧ ‖a.Q ζ‖ ≤ v) := by
  intro q a L s
  have hμ : |δ| ≤ dom.μ₀ := by rwa [abs_of_pos hδ]
  have hμ' : ‖(δ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hre : 0 ≤ q.re := by
    show 0 ≤ (t * (1 + (δ : ℂ))).re
    simp [mul_re, ht0]
  have hc0 := dom.c₀_pos
  have hρA : dom.c₀ / 4 < dom.ρA := by have := dom.c₀_le; have := dom.ρA_pos; linarith
  have hbp := dom.norm_rootPlus_le hW hθ hD hμ' hq
  have hbm := dom.norm_rootMinus_le hW hθ hD hμ' hq
  have hr := cepsRootR_norm_ge_drift dom hW hθ hD hμ hre
  rw [abs_of_pos hδ] at hr
  have hsqv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hQball : ∀ ζ : ℂ, ‖ζ‖ ≤ dom.c₀ / 4 → a.Q ζ ≠ 0 ∧ cepsVarLo D / 4 ≤ ‖a.Q ζ‖ ∧ ‖a.Q ζ‖ ≤ v :=
    fun ζ hζ => ⟨CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq
        (mem_ball_zero_iff.mpr (by linarith)),
      cepsQ_norm_ge_on_rootZone dom hW hθ hD hμ' hq (by linarith),
      cepsQ_norm_le_on_rootZone dom hW hθ hD hμ' hq (by linarith)⟩
  have hLb : ∀ ζ : ℂ, ‖ζ‖ ≤ dom.c₀ / 4 → ‖L δ q ζ‖ ≤ dom.normalLogBound :=
    fun ζ hζ => canonL_norm_le_logBound dom hW hθ hD hμ hq (by linarith)
  have hψ : a.ψp = a.eta * a.Q a.βp := by
    have := CepsC6.cepsQ_rootPlus_mul dom hW hθ hD hμ' hq
    show deriv (cepsCgfShift ρW δ) (cepsRootPlus D θ ρW δ q) =
      (cepsRootPlus D θ ρW δ q - cepsRootMinus D θ ρW δ q) * cepsQ D θ ρW δ q
        (cepsRootPlus D θ ρW δ q)
    rw [← this]; ring
  have heta_re := cepsRoots_difference_re_ge hW hθ hD dom hμ hq hre
  have hsigns := cepsRoots_re_signs dom hW hθ hD hμ hre hq
  have hminus := cepsRootMinus_re_ge_scale dom hW hθ hD hμ hδ.le hq hre
  have heta := cepsRoots_difference_norm_le hW hθ hD dom hμ' hq
  have hrmax := dom.norm_cepsRootR_le hW hθ hD hμ' hq
  have hK := cepsChartK_pos hD
  have hpi := cepsNormal_actual_pi_sub_one_le dom hW hθ hD hμ hq
  have hetaB : ‖a.eta‖ ≤ 2 * cepsChartK D * dom.rmax :=
    heta.trans (by gcongr)
  refine ⟨hψ, (hQball _ hbp).1, (hQball _ hbm).1, (hQball _ ht).1, ?_, hsigns.1, ?_, hetaB, ?_, ?_⟩
  · refine le_trans ?_ heta_re
    gcongr
  · have h1 : ‖cepsRootR D θ ρW δ q‖ / (4 * Real.sqrt v) ≤ (t - a.βm).re := by
      show _ ≤ (t - cepsRootMinus D θ ρW δ q).re
      rw [sub_re, ht0]; linarith
    refine le_trans ?_ (h1.trans (re_le_norm _))
    gcongr
  · have := norm_sub_norm_le (a.pi L δ q) 1
    rw [norm_one] at this
    have h2 : dom.normalPiBound * ‖a.eta‖ ≤ dom.normalPiBound * (2 * cepsChartK D * dom.rmax) := by
      have : 0 ≤ dom.normalPiBound := by
        unfold CepsCanonDomain.normalPiBound
        have := cepsNormal_budget_nonneg dom hθ hD
        have := cepsVarLo_pos hD
        have := CepsCanonDomain.v_pos hW hθ hD
        positivity
      gcongr
    linarith [hpi]
  · intro ζ hζ
    have hζ' : ‖ζ‖ ≤ dom.c₀ / 4 := by
      rcases hζ with h | h | h
      · rw [h]; exact ht
      · rw [Set.mem_singleton_iff.mp h] at *; exact hbp
      · rw [Set.mem_singleton_iff.mp h]; exact hbm
    exact ⟨hLb ζ hζ', (hQball ζ hζ').2⟩

/-- The decay rate of `E = e^{-η l}` at drift `δ`. -/
def CepsCanonDomain.drawupRate (_dom : CepsCanonDomain D θ v) (δ : ℝ) : ℝ :=
  Real.sqrt (cepsVarLo D) / (3 * v) * δ / (2 * Real.sqrt v)

include hθ hD in
/-- **(3.9), class-uniform.** At a fixed drift `0 < δ ≤ μ₀` and marked discount `q = t(1+δ)`,
`t ∈ iℝ`, `‖t‖ ≤ c₀/4`, the bottom-started normal exits satisfy the exact identity
`û (1 - E κ) = 𝒜 e^{-(β₊-t)l} (1 - ℓ̂)` with `‖E κ‖ ≤ C e^{-c l} ≤ 1/2`, `‖1 - ℓ̂‖ ≥ G` and
`‖𝒜 e^{-(β₊-t)l}‖ ≤ C'` for `l ≥ l₀`; the constants depend only on the class and `δ`. -/
theorem drawup_normal_bounds (hv : 0 < v) {δ : ℝ} (hδ : 0 < δ) (hδμ : δ ≤ dom.μ₀) :
    ∃ Cκ G Ca l₀ : ℝ, 0 < G ∧ 0 ≤ l₀ ∧ 0 ≤ Cκ ∧ 0 ≤ Ca ∧
      ∀ (ρ : Measure ℝ) (g : ℝ → ℝ), IsStepLaw ρ g D θ v →
      ∀ t : ℂ, t.re = 0 → ‖t‖ ≤ dom.c₀ / 4 → ‖t * (1 + (δ : ℂ))‖ ≤ dom.q₀ →
      ∀ l : ℝ, l₀ ≤ l →
        let q := t * (1 + (δ : ℂ))
        let a := cepsWHNormalData D θ ρ δ q
        let L := dom.canonL ρ
        a.botUpperExit L δ q t l * (1 - a.decay l * a.drawupKappa L δ q t) =
            a.regularAmplitude L δ q t * exp (-(a.βp - t) * l) *
              (1 - a.botLowerExit L δ q t l) ∧
          ‖a.decay l * a.drawupKappa L δ q t‖ ≤ Cκ * Real.exp (-dom.drawupRate δ * l) ∧
          ‖a.decay l * a.drawupKappa L δ q t‖ ≤ 1 / 2 ∧
          G ≤ ‖1 - a.botLowerExit L δ q t l‖ ∧
          ‖a.regularAmplitude L δ q t * exp (-(a.βp - t) * l)‖ ≤ Ca := by
  set B := dom.normalLogBound
  set vq := cepsVarLo D / 4
  set H := 2 * cepsChartK D * dom.rmax
  set Pm := 1 + dom.normalPiBound * (2 * cepsChartK D * dom.rmax)
  set s := Real.sqrt (cepsVarLo D) / (3 * v) * δ
  set m₀ := s / (4 * Real.sqrt v)
  set cE := dom.drawupRate δ
  set Cκ := Pm + (v * Real.exp B / (vq * Real.exp (-B))) * Real.exp (2 * B) *
      (H * v * Real.exp B) / (m₀ * vq * Real.exp (-B))
  have hvl := cepsVarLo_pos hD
  have hvq : 0 < vq := by positivity
  have hK := cepsChartK_pos hD
  have hR := dom.rmax_pos
  have hB0 : 0 ≤ B := normalLogBound_nonneg' dom hθ
  have hPB : 0 ≤ dom.normalPiBound := by
    unfold CepsCanonDomain.normalPiBound
    have := cepsNormal_budget_nonneg dom hθ hD
    positivity
  have hPm : 0 ≤ Pm := by positivity
  have hs : 0 < s := by positivity
  have hm₀ : 0 < m₀ := by positivity
  have hcE : 0 < cE := by
    show 0 < Real.sqrt (cepsVarLo D) / (3 * v) * δ / (2 * Real.sqrt v); positivity
  have hCκ : 0 ≤ Cκ := by positivity
  set l₀ := Real.log (2 * (Cκ + Pm) + 1) / cE
  have hl₀ : 0 ≤ l₀ := div_nonneg (Real.log_nonneg (by linarith)) hcE.le
  refine ⟨Cκ, m₀ * vq * Real.exp (-B) / 3, H * v * Real.exp (4 * B) / (m₀ * vq), l₀,
    by positivity, hl₀, hCκ, by positivity, ?_⟩
  intro ρ g hρ t ht0 ht hq l hl q a L
  obtain ⟨hψ, hQp, hQm, hQt, heta, hβp, hm, hη, hpi, hpts⟩ :=
    drawup_pointwise dom hρ hθ hD hδ hδμ ht0 ht hq
  have hl0 : 0 ≤ l := hl₀.trans hl
  have he : Real.exp (-cE * l) * (2 * (Cκ + Pm) + 1) ≤ 1 := by
    have h1 : Real.log (2 * (Cκ + Pm) + 1) ≤ cE * l := by
      have := mul_le_mul_of_nonneg_left hl hcE.le
      rwa [mul_div_cancel₀ _ hcE.ne'] at this
    calc Real.exp (-cE * l) * (2 * (Cκ + Pm) + 1)
        = Real.exp (-cE * l) * Real.exp (Real.log (2 * (Cκ + Pm) + 1)) := by
          rw [Real.exp_log (by linarith)]
      _ ≤ Real.exp (-cE * l) * Real.exp (cE * l) := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  have hepos := Real.exp_pos (-cE * l)
  have hsmall : Real.exp (-cE * l) * Cκ ≤ 1 / 2 := by nlinarith
  have hsmall' : Real.exp (-cE * l) * Pm ≤ 1 / 2 := by nlinarith
  have hE : ‖a.decay (l : ℂ)‖ ≤ Real.exp (-cE * l) := by
    unfold CepsNormalData.decay
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    have : (-a.eta * (l : ℂ)).re = -a.eta.re * l := by simp [mul_re]
    rw [this]
    have h2 : cE ≤ a.eta.re := by
      show s / (2 * Real.sqrt v) ≤ _; exact heta
    nlinarith
  have hEp : ‖exp (-(a.βp - t) * (l : ℂ))‖ ≤ 1 := by
    rw [norm_exp]
    have : (-(a.βp - t) * (l : ℂ)).re = -a.βp.re * l := by simp [mul_re, ht0]
    rw [this, Real.exp_le_one_iff]
    nlinarith
  have ht' : t ∈ ({t, a.βp, a.βm} : Set ℂ) := by simp
  have hp' : a.βp ∈ ({t, a.βp, a.βm} : Set ℂ) := by simp
  have hm' : a.βm ∈ ({t, a.βp, a.βm} : Set ℂ) := by simp
  obtain ⟨hLt, hQtl, hQth⟩ := hpts t ht'
  obtain ⟨hLp, -, hQph⟩ := hpts a.βp hp'
  obtain ⟨hLm, hQml, -⟩ := hpts a.βm hm'
  have hres := a.drawup_abstract_bounds L δ q (t := t) (l := (l : ℂ)) hQp hQm hQt hψ hLt hLp hLm
    hvq hQtl hQth hQph hQml hη hpi hm₀ hm hepos.le hE hEp hsmall hsmall'
  obtain ⟨h1, h2, h3, h4, h5⟩ := hres
  exact ⟨h1, by rw [mul_comm Cκ]; exact h2, h3, h4, h5⟩

end PGM
