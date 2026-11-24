import PLAStochastic.Index.CEPS.Ident.Reality
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Esscher.Main

/-!
# CEPS WP4: the ladder transforms of the drifted step in the canonical domain

Bridge between the W library and the canonical-factor conventions. For a class step law `ρW`,
`dom : CepsCanonDomain D θ v` and real `|μ| ≤ μ₀`, the step `Y = W + μ` (`driftStep ρW μ`):

* `IsStepLaw.theta_le_two_mul` (`θ ≤ 2D`) and `CepsCanonDomain.μ₀_le_drift` (`μ₀ ≤ 1/(64D)`);
* `driftStep_strip`: `∫ e^{±(θ/2) y} dY < ∞` and `Y` charges both half-lines;
* `wienerHopf_cepsD`: `(1 - A₊)(1 - A₋) = d` on `|Re ζ| ≤ θ/2`, `Re q ≥ 0` (W-3);
* `differentiableOn_asc` (`Re ζ < θ/2`), `differentiableOn_desc` (`Re ζ > -θ/2`);
* `norm_asc_le`: `‖A₊(ζ)‖ ≤ E[e^{(θ/2) H₊}; σ₊ < ∞]` for `Re ζ ≤ θ/2`;
* `tendsto_asc_atBot`: `A₊(t) → 0` as real `t → -∞`;
* `continuousOn_asc_q`: `q ↦ A₊(ζ)` is continuous on `Re q ≥ 0` for `Re ζ ≤ θ/2`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf
open scoped ENNReal

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

/-- `θ ≤ 2D`: the envelope `D e^{-θ|x|}` has mass `2D/θ ≥ 1`. -/
theorem WienerHopf.IsStepLaw.theta_le_two_mul (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 ≤ D) :
    θ ≤ 2 * D := by
  have := hW.isProbabilityMeasure
  have h1 : ∫⁻ x, ENNReal.ofReal (fW x) = 1 := by
    have h := measure_univ (μ := ρW)
    rw [hW.eq_withDensity, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h
  have h2 : ∫⁻ x, ENNReal.ofReal (fW x) ≤
      ∫⁻ x, ENNReal.ofReal D * ENNReal.ofReal (Real.exp (-θ * |x|)) :=
    lintegral_mono fun x => by
      rw [← ENNReal.ofReal_mul hD]; exact ENNReal.ofReal_le_ofReal (hW.le_exp x)
  rw [lintegral_const_mul _ (by fun_prop), IsStepLaw.lintegral_exp_neg_abs θ hθ,
    ← ENNReal.ofReal_mul hD, h1, ENNReal.one_le_ofReal] at h2
  rw [mul_div_assoc', le_div_iff₀ hθ] at h2
  linarith

/-- The ascending-ladder integrability on `{τ = n}` for `Re ζ ≤ a`. -/
theorem integrableOn_cexp_asc {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {a : ℝ}
    (hpos : Integrable (fun y : ℝ => Real.exp (a * y)) ρ) {ζ : ℂ} (hζ : ζ.re ≤ a) (n : ℕ) :
    IntegrableOn (fun ω => cexp (ζ * WienerHopf.partialSum n ω)) {ω | firstEntry (Ioi 0) ω = n}
      (pathLaw ρ) := by
  refine ((integrable_exp_partialSum hpos n).1.integrableOn).mono'
    (by fun_prop : Measurable fun ω => cexp (ζ * WienerHopf.partialSum n ω)).aestronglyMeasurable
    ((ae_restrict_iff' (measurableSet_firstEntry_eq measurableSet_Ioi n)).mpr
      (Eventually.of_forall fun ω hω => ?_))
  simp only [mem_ofPred_eq] at hω
  rw [norm_cexp_mul_ofReal, Real.exp_le_exp]
  exact mul_le_mul_of_nonneg_right hζ (le_of_lt (firstEntry_eq_coe_iff.mp hω).2.1)

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

theorem μ₀_le_drift : dom.μ₀ ≤ 1 / (64 * D) := by
  have h1 := dom.μ₀_c₀
  have h2 := dom.c₀_le
  have h3 := dom.ρA_R
  have h4 := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have h5 := cepsCgfRadius_le (D := D) (θ := θ)
  have h6 := hW.theta_le_two_mul hθ hD.le
  have hc0 := dom.c₀_pos
  have hc : dom.c₀ ≤ D / 64000 := by linarith
  have h7 : cepsVarLo D * dom.c₀ ≤ 1 / (256 * 64000 * D) := by
    unfold cepsVarLo
    calc 1 / (256 * D ^ 2) * dom.c₀ ≤ 1 / (256 * D ^ 2) * (D / 64000) := by gcongr
      _ = 1 / (256 * 64000 * D) := by field_simp
  have h8 : 16 * dom.μ₀ * D ≤ 1 / (256 * 64000) := by
    calc 16 * dom.μ₀ * D ≤ 1 / (256 * 64000 * D) * D := by gcongr; linarith
      _ = 1 / (256 * 64000) := by field_simp
  rw [le_div_iff₀ (by positivity)]
  nlinarith [dom.μ₀_pos]

/-- The strip hypotheses of the W library for `Y = W + μ`. -/
theorem driftStep_strip {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) :
    Integrable (fun y : ℝ => Real.exp (θ / 2 * y)) (driftStep ρW μ) ∧
      Integrable (fun y : ℝ => Real.exp (-(θ / 2) * y)) (driftStep ρW μ) ∧
      0 < driftStep ρW μ (Iio 0) ∧ 0 < driftStep ρW μ (Ioi 0) := by
  have := hW.isProbabilityMeasure
  have hv := v_pos hW hθ hD
  have hm := driftStep_masses hW hθ.le hD hv hμ (dom.μ₀_le_drift hW hθ hD)
  have hmass : 0 < 1 / (1024 * D ^ 2 * v) := by positivity
  refine ⟨integrable_exp_driftStep ρW μ _ (hW.integrable_exp_of_abs_lt hD.le
      (by rw [abs_of_pos (by positivity)]; linarith)),
    integrable_exp_driftStep ρW μ _ (hW.integrable_exp_of_abs_lt hD.le
      (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)), ?_, ?_⟩
  · by_contra hn
    have hz : driftStep ρW μ (Iio 0) = 0 := le_antisymm (not_lt.mp hn) bot_le
    have hz' : (driftStep ρW μ).real (Iio 0) = 0 := by simp [measureReal_def, hz]
    have hs : Iic (-(1 / (64 * D))) ⊆ Iio (0 : ℝ) := fun x hx => by
      simp only [mem_Iic, mem_Iio] at hx ⊢
      have : 0 < 1 / (64 * D) := by positivity
      linarith
    have he := measureReal_mono (μ := driftStep ρW μ) hs
    linarith [hm.1]
  · by_contra hn
    have hz : driftStep ρW μ (Ioi 0) = 0 := le_antisymm (not_lt.mp hn) bot_le
    have hz' : (driftStep ρW μ).real (Ioi 0) = 0 := by simp [measureReal_def, hz]
    have hs : Ici (1 / (64 * D)) ⊆ Ioi (0 : ℝ) := fun x hx => by
      simp only [mem_Ici, mem_Ioi] at hx ⊢
      have : 0 < 1 / (64 * D) := by positivity
      linarith
    have he := measureReal_mono (μ := driftStep ρW μ) hs
    linarith [hm.2]

/-- **W-3 in the canonical conventions.** `(1 - A₊(ζ))(1 - A₋(ζ)) = d(ζ; μ, q)`. -/
theorem wienerHopf_cepsD {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q ζ : ℂ} (hq : 0 ≤ q.re)
    (hζ : |ζ.re| ≤ θ / 2) :
    (1 - ascTransform (driftStep ρW μ) (cexp (-q)) ζ) *
      (1 - descTransform (driftStep ρW μ) (cexp (-q)) ζ) = cepsD ρW μ q ζ := by
  have := hW.isProbabilityMeasure
  obtain ⟨h1, h2, hl, hr⟩ := dom.driftStep_strip hW hθ hD hμ
  exact wienerHopf_drift_strip ρW μ (by positivity) h1 h2 hl hr hq hζ

theorem differentiableOn_asc {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {s : ℂ} (hs : ‖s‖ ≤ 1) :
    DifferentiableOn ℂ (fun ζ => ascTransform (driftStep ρW μ) s ζ) {ζ : ℂ | ζ.re < θ / 2} := by
  have := hW.isProbabilityMeasure
  obtain ⟨h1, -, hl, -⟩ := dom.driftStep_strip hW hθ hD hμ
  exact differentiableOn_ascTransform (a := θ / 2) (by positivity) h1
    (expEntryMass_Iic_lt_one (by positivity) hl) hs

theorem differentiableOn_desc {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {s : ℂ} (hs : ‖s‖ ≤ 1) :
    DifferentiableOn ℂ (fun ζ => descTransform (driftStep ρW μ) s ζ)
      {ζ : ℂ | -(θ / 2) < ζ.re} := by
  have := hW.isProbabilityMeasure
  obtain ⟨-, h2, -, hr⟩ := dom.driftStep_strip hW hθ hD hμ
  exact differentiableOn_descTransform (a := θ / 2) (by positivity) h2
    (expEntryMass_Ioi_lt_one (by positivity) hr) hs

/-- `‖A₊(ζ)‖ ≤ E[e^{(θ/2) H₊}; σ₊ < ∞]` for `Re ζ ≤ θ/2`, `‖s‖ ≤ 1`. -/
theorem norm_asc_le {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {s : ℂ} (hs : ‖s‖ ≤ 1) {ζ : ℂ}
    (hζ : ζ.re ≤ θ / 2) :
    ‖ascTransform (driftStep ρW μ) s ζ‖ ≤ expEntryMass (driftStep ρW μ) (Ioi 0) (θ / 2) := by
  have := hW.isProbabilityMeasure
  obtain ⟨h1, -, hl, -⟩ := dom.driftStep_strip hW hθ hD hμ
  have hθ2 : (0 : ℝ) < θ / 2 := by positivity
  obtain ⟨-, hint, -⟩ := expEntryMass_compl_le (ρ := driftStep ρW μ) measurableSet_Iic
    isLadderSet_Iic (fun x hx => mul_nonpos_of_nonneg_of_nonpos hθ2.le hx)
    (expEntryMass_Iic_lt_one hθ2 hl) h1
  rw [compl_Iic] at hint
  unfold ascTransform entryTransform expEntryMass
  refine norm_integral_le_of_norm_le hint ((ae_restrict_iff'
    (measurableSet_firstEntry_lt_top measurableSet_Ioi)).mpr
      (Eventually.of_forall fun ω hω => ?_))
  have hpos : (0 : ℝ) < entryValue (Ioi 0) ω := entryValue_mem hω
  rw [norm_mul, norm_pow, norm_cexp_mul_ofReal]
  calc ‖s‖ ^ (firstEntry (Ioi 0) ω).toNat * Real.exp (ζ.re * entryValue (Ioi 0) ω)
      ≤ 1 * Real.exp (θ / 2 * entryValue (Ioi 0) ω) :=
        mul_le_mul (pow_le_one₀ (norm_nonneg _) hs)
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hζ hpos.le)) (Real.exp_pos _).le
          zero_le_one
    _ = _ := one_mul _

/-- `q ↦ A₊(ζ)` is continuous on `Re q ≥ 0` for `Re ζ ≤ θ/2`. -/
theorem continuousOn_asc_q {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {ζ : ℂ} (hζ : ζ.re ≤ θ / 2) :
    ContinuousOn (fun q => ascTransform (driftStep ρW μ) (cexp (-q)) ζ) {q : ℂ | 0 ≤ q.re} := by
  have := hW.isProbabilityMeasure
  obtain ⟨h1, -, hl, -⟩ := dom.driftStep_strip hW hθ hD hμ
  have hθ2 : (0 : ℝ) < θ / 2 := by positivity
  obtain ⟨he, -, -⟩ := expEntryMass_compl_le (ρ := driftStep ρW μ) measurableSet_Iic
    isLadderSet_Iic (fun x hx => mul_nonpos_of_nonneg_of_nonpos hθ2.le hx)
    (expEntryMass_Iic_lt_one hθ2 hl) h1
  rw [compl_Iic] at he
  have hsum := summable_entry_of_le (ρ := driftStep ρW μ) measurableSet_Ioi (s := 1) (z := ζ)
    (by simp) (fun x hx => mul_le_mul_of_nonneg_right hζ (le_of_lt (show (0 : ℝ) < x from hx)))
    h1 he
  simp only [norm_one, one_pow, one_mul] at hsum
  exact continuousOn_entryTransform_exp measurableSet_Ioi
    (integrableOn_cexp_asc h1 hζ) hsum

end

/-- `A₊(t) → 0` as real `t → -∞` (the ascending ladder height is positive). -/
theorem tendsto_asc_atBot (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {s : ℂ} (hs : ‖s‖ ≤ 1) :
    Tendsto (fun t : ℝ => ascTransform ρ s t) atBot (𝓝 0) := by
  have hA := measurableSet_firstEntry_lt_top (A := Ioi (0 : ℝ)) measurableSet_Ioi
  have hm : ∀ t : ℝ, Measurable fun ω : ℕ → ℝ =>
      s ^ (firstEntry (Ioi 0) ω).toNat * cexp ((t : ℂ) * (entryValue (Ioi 0) ω : ℂ)) := by
    intro t
    have h1 : Measurable fun ω : ℕ → ℝ => (firstEntry (Ioi 0) ω).toNat :=
      (Measurable.of_discrete (f := ENat.toNat)).comp (measurable_firstEntry measurableSet_Ioi)
    have h2 : Measurable fun n : ℕ => s ^ n := Measurable.of_discrete
    have h3 := (measurable_entryValue (A := Ioi (0 : ℝ)) measurableSet_Ioi)
    exact (h2.comp h1).mul (by fun_prop)
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := (pathLaw ρ).restrict {ω | firstEntry (Ioi 0) ω < ⊤}) (l := atBot)
    (F := fun (t : ℝ) ω => s ^ (firstEntry (Ioi 0) ω).toNat *
      cexp ((t : ℂ) * (entryValue (Ioi 0) ω : ℂ)))
    (f := fun _ => (0 : ℂ)) (fun _ => (1 : ℝ))
    (Eventually.of_forall fun t => (hm t).aestronglyMeasurable)
    ((eventually_le_atBot 0).mono fun t ht => (ae_restrict_iff' hA).mpr
      (Eventually.of_forall fun ω hω => ?_))
    (integrable_const _) ((ae_restrict_iff' hA).mpr (Eventually.of_forall fun ω hω => ?_))
  · simpa [ascTransform, entryTransform] using hlim
  · have hpos : (0 : ℝ) < entryValue (Ioi 0) ω := entryValue_mem hω
    rw [norm_mul, norm_pow, norm_cexp_mul_ofReal, ofReal_re]
    calc ‖s‖ ^ (firstEntry (Ioi 0) ω).toNat * Real.exp (t * entryValue (Ioi 0) ω)
        ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (norm_nonneg _) hs)
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg ht hpos.le))
          (Real.exp_pos _).le zero_le_one
      _ = 1 := one_mul 1
  · have hpos : (0 : ℝ) < entryValue (Ioi 0) ω := entryValue_mem hω
    have hexp : Tendsto (fun t : ℝ => Real.exp (t * entryValue (Ioi 0) ω)) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.atBot_mul_const hpos)
    refine squeeze_zero_norm (fun t => ?_) hexp
    rw [norm_mul, norm_pow, norm_cexp_mul_ofReal, ofReal_re]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (pow_le_one₀ (norm_nonneg _) hs)

end CepsCanonDomain

end PGM
