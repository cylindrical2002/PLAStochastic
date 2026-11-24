import PLAStochastic.Index.GEP.Universality.Defs
import PLAStochastic.Index.GEP.Response.Defs
import PLAStochastic.Index.GEP.OrbitClosure.RegularClass
import Mathlib.Probability.Moments.Variance

/-!
# WP5 classes and smooth components

The bounded density component is preserved along positive mixture paths, including when the
second component is singular. The constants in these statements depend on the class and the
maximum mixing parameter, not on the singular component.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

variable {D D' c₀ c₀' θ vlo vhi : ℝ} {ν ρ : ProbabilityMeasure ℝ}

/-- The lower-integral third-moment bound includes integrability. -/
theorem UnivClass.integrable_third {κ₃ B : ℝ} (h : UnivClass vlo vhi κ₃ B θ ν) :
    Integrable (fun x : ℝ => |x - 1| ^ 3) (ν : Measure ℝ) := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => by positivity)]
  exact h.third.trans_lt ENNReal.ofReal_lt_top

theorem UnivClass.memLp3 {κ₃ B : ℝ} (h : UnivClass vlo vhi κ₃ B θ ν) :
    MemLp id 3 (ν : Measure ℝ) := by
  have hm : MemLp (fun x : ℝ => x - 1) 3 (ν : Measure ℝ) := by
    rw [← integrable_norm_rpow_iff (by fun_prop) (by norm_num) (by norm_num)]
    simpa [Real.norm_eq_abs, Real.rpow_natCast] using h.integrable_third
  convert hm.add (memLp_const (1 : ℝ)) using 1
  ext x
  simp

theorem UnivClass.ae_pos {κ₃ B : ℝ} (h : UnivClass vlo vhi κ₃ B θ ν) :
    ∀ᵐ x ∂(ν : Measure ℝ), 0 < x := by
  filter_upwards [compl_mem_ae_iff.mpr h.pos] with x hx
  simpa using hx

/-- The second raw moment is uniformly bounded by the variance upper bound plus one. -/
theorem UnivClass.integral_sq_le {κ₃ B : ℝ} (h : UnivClass vlo vhi κ₃ B θ ν) :
    ∫ x, x ^ 2 ∂(ν : Measure ℝ) ≤ vhi + 1 := by
  have h2 : MemLp id 2 (ν : Measure ℝ) := h.memLp3.mono_exponent (by norm_num)
  have hv : variance id (ν : Measure ℝ) = lawVar ν := by
    rw [variance_eq_integral h2.aemeasurable]
    rfl
  have heq := variance_eq_sub h2
  change variance id (ν : Measure ℝ) =
    (∫ x, x ^ 2 ∂(ν : Measure ℝ)) - lawMean ν ^ 2 at heq
  rw [hv, h.mean] at heq
  linarith [h.var_le]

/-- Centering positive mean-one gaps preserves a class-uniform two-sided exponential moment. -/
theorem UnivClass.lintegral_exp_abs_sub_one_le {κ₃ B a : ℝ}
    (h : UnivClass vlo vhi κ₃ B θ ν) (ha : 0 ≤ a) (haθ : a ≤ θ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (a * |x - 1|)) ∂(ν : Measure ℝ) ≤
      ENNReal.ofReal (Real.exp a * B) := by
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (a * |x - 1|)) ∂(ν : Measure ℝ)
      ≤ ∫⁻ x, ENNReal.ofReal (Real.exp a) *
          ENNReal.ofReal (Real.exp (θ * x)) ∂(ν : Measure ℝ) := by
        refine lintegral_mono_ae (h.ae_pos.mono fun x hx => ?_)
        rw [← ENNReal.ofReal_mul (Real.exp_pos a).le, ← Real.exp_add]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have habs : |x - 1| ≤ x + 1 := by rw [abs_le]; constructor <;> linarith
        have hmul := mul_le_mul_of_nonneg_left habs ha
        have hθmul := mul_le_mul_of_nonneg_right haθ hx.le
        nlinarith
    _ ≤ ENNReal.ofReal (Real.exp a) * ENNReal.ofReal B := by
        rw [lintegral_const_mul _ (by fun_prop)]
        gcongr
        exact h.expMom
    _ = ENNReal.ofReal (Real.exp a * B) := (ENNReal.ofReal_mul (Real.exp_pos a).le).symm

/-- Convex mixtures preserve the universality moment class, without density assumptions. -/
theorem UnivClass.mix {κ₃ B : ℝ} (hν : UnivClass vlo vhi κ₃ B θ ν)
    (hρ : UnivClass vlo vhi κ₃ B θ ρ) (s : ℝ) :
    UnivClass vlo vhi κ₃ B θ (mixPM ν ρ s) := by
  set a := mixParam s with ha_def
  have ha0 : 0 ≤ a := mixParam_nonneg s
  have ha1 : a ≤ 1 := mixParam_le_one s
  have h1a : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have hiν : Integrable (fun x : ℝ => x) (ν : Measure ℝ) :=
    hν.memLp3.integrable (by norm_num)
  have hiρ : Integrable (fun x : ℝ => x) (ρ : Measure ℝ) :=
    hρ.memLp3.integrable (by norm_num)
  have h2ν : MemLp id 2 (ν : Measure ℝ) := hν.memLp3.mono_exponent (by norm_num)
  have h2ρ : MemLp id 2 (ρ : Measure ℝ) := hρ.memLp3.mono_exponent (by norm_num)
  have hsν : Integrable (fun x : ℝ => (x - 1) ^ 2) (ν : Measure ℝ) :=
    (h2ν.sub (memLp_const 1)).integrable_sq
  have hsρ : Integrable (fun x : ℝ => (x - 1) ^ 2) (ρ : Measure ℝ) :=
    (h2ρ.sub (memLp_const 1)).integrable_sq
  have hint : ∀ {g : ℝ → ℝ}, Integrable g (ν : Measure ℝ) →
      Integrable g (ρ : Measure ℝ) →
      ∫ x, g x ∂(mixPM ν ρ s : Measure ℝ) =
        (1 - a) * ∫ x, g x ∂(ν : Measure ℝ) + a * ∫ x, g x ∂(ρ : Measure ℝ) := by
    intro g hgν hgρ
    rw [coe_mixPM, integral_add_measure
      (hgν.smul_measure ENNReal.ofReal_ne_top) (hgρ.smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal h1a, ENNReal.toReal_ofReal ha0, smul_eq_mul, smul_eq_mul]
  have hm : lawMean (mixPM ν ρ s) = 1 := by
    rw [lawMean, hint hiν hiρ]
    change (1 - a) * lawMean ν + a * lawMean ρ = 1
    rw [hν.mean, hρ.mean]
    ring
  have hv : lawVar (mixPM ν ρ s) = (1 - a) * lawVar ν + a * lawVar ρ := by
    rw [lawVar, hm, hint hsν hsρ, lawVar, lawVar, hν.mean, hρ.mean]
  have hlin : ∀ {g : ℝ → ℝ≥0∞} {C : ℝ},
      (∫⁻ x, g x ∂(ν : Measure ℝ)) ≤ ENNReal.ofReal C →
      (∫⁻ x, g x ∂(ρ : Measure ℝ)) ≤ ENNReal.ofReal C →
      (∫⁻ x, g x ∂(mixPM ν ρ s : Measure ℝ)) ≤ ENNReal.ofReal C := by
    intro g C hgν hgρ
    rw [coe_mixPM, lintegral_add_measure, lintegral_smul_measure,
      lintegral_smul_measure, smul_eq_mul, smul_eq_mul]
    calc ENNReal.ofReal (1 - mixParam s) * (∫⁻ x, g x ∂(ν : Measure ℝ)) +
          ENNReal.ofReal (mixParam s) * (∫⁻ x, g x ∂(ρ : Measure ℝ))
        ≤ ENNReal.ofReal (1 - a) * ENNReal.ofReal C +
          ENNReal.ofReal a * ENNReal.ofReal C := by gcongr
      _ = ENNReal.ofReal C := by
        rw [← add_mul, ← ENNReal.ofReal_add h1a ha0]
        simp
  refine ⟨?_, hm, ?_, ?_, hlin hν.third hρ.third, hlin hν.expMom hρ.expMom⟩
  · rw [coe_mixPM, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      hν.pos, hρ.pos]
    simp
  · rw [hv]
    have h0 := mul_le_mul_of_nonneg_left hν.var_ge h1a
    have h1 := mul_le_mul_of_nonneg_left hρ.var_ge ha0
    nlinarith
  · rw [hv]
    have h0 := mul_le_mul_of_nonneg_left hν.var_le h1a
    have h1 := mul_le_mul_of_nonneg_left hρ.var_le ha0
    nlinarith

theorem SmoothPart.mono (h : SmoothPart D c₀ ν) (hD : D ≤ D') (hc : c₀' ≤ c₀) :
    SmoothPart D' c₀' ν := by
  obtain ⟨f, hfm, hf0, hfD, hmass, hν⟩ := h.part
  exact ⟨f, hfm, hf0, fun x => (hfD x).trans hD,
    (ENNReal.ofReal_le_ofReal hc).trans hmass, hν⟩

theorem SmoothPart.D_nonneg (h : SmoothPart D c₀ ν) : 0 ≤ D := by
  obtain ⟨f, _, hf0, hfD, _, _⟩ := h.part
  exact (hf0 0).trans (hfD 0)

theorem SmoothPart.D_pos (h : SmoothPart D c₀ ν) (hc : 0 < c₀) : 0 < D := by
  by_contra hD
  obtain ⟨f, _, hf0, hfD, hmass, _⟩ := h.part
  have hz : ∀ x, f x = 0 := fun x => le_antisymm ((hfD x).trans (le_of_not_gt hD)) (hf0 x)
  have hp : 0 < ENNReal.ofReal c₀ := ENNReal.ofReal_pos.mpr hc
  exact (not_le_of_gt hp) (by simpa [hz] using hmass)

theorem SmoothPart.mass_le_one (h : SmoothPart D c₀ ν) : c₀ ≤ 1 := by
  obtain ⟨f, _, _, _, hmass, hν⟩ := h.part
  have hi : (∫⁻ x, ENNReal.ofReal (f x)) ≤ 1 := by
    simpa [withDensity_apply] using hν univ
  apply (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp
  simpa using hmass.trans hi

/-- A regular law has a bounded density component of total mass one. -/
theorem RegLaw.smoothPart (h : RegLaw D θ vlo vhi ν) (hθ : 0 ≤ θ) :
    SmoothPart D 1 ν := by
  obtain ⟨f, hfm, hf0, hfz, hfD, hν⟩ := h.density
  have hbound : ∀ x, f x ≤ D := by
    intro x
    rcases le_or_gt x 0 with hx | hx
    · rw [hfz x hx]
      exact h.D_nonneg
    · calc f x ≤ D * Real.exp (-θ * x) := hfD x
        _ ≤ D * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by nlinarith)) h.D_nonneg
        _ = D := mul_one _
  refine ⟨f, hfm, hf0, hbound, ?_, le_of_eq hν.symm⟩
  have hm := congrArg (fun μ : Measure ℝ => μ univ) hν
  simpa [withDensity_apply] using hm.le

/-- The left density component survives mixing with any probability law. -/
theorem SmoothPart.mix_left (h : SmoothPart D c₀ ν) (ρ : ProbabilityMeasure ℝ) (s : ℝ) :
    SmoothPart D ((1 - mixParam s) * c₀) (mixPM ν ρ s) := by
  obtain ⟨f, hfm, hf0, hfD, hmass, hν⟩ := h.part
  have ha : 0 ≤ 1 - mixParam s := sub_nonneg.mpr (mixParam_le_one s)
  have ha1 : 1 - mixParam s ≤ 1 := by linarith [mixParam_nonneg s]
  refine ⟨fun x => (1 - mixParam s) * f x, hfm.const_mul _,
    fun x => mul_nonneg ha (hf0 x), fun x => ?_, ?_, ?_⟩
  · calc (1 - mixParam s) * f x ≤ 1 * f x :=
          mul_le_mul_of_nonneg_right ha1 (hf0 x)
      _ ≤ D := by simpa using hfD x
  · simp_rw [ENNReal.ofReal_mul ha]
    rw [lintegral_const_mul _ hfm.ennreal_ofReal]
    gcongr
  · have heq : volume.withDensity (fun x => ENNReal.ofReal ((1 - mixParam s) * f x)) =
        ENNReal.ofReal (1 - mixParam s) •
          volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
      simp_rw [ENNReal.ofReal_mul ha]
      exact withDensity_smul _ hfm.ennreal_ofReal
    rw [heq, coe_mixPM]
    exact Measure.le_add_right (_root_.smul_le_smul_left _ hν)

/-- A whole mixture interval has one lower bound on its smooth mass. -/
theorem SmoothPart.mix_left_uniform (h : SmoothPart D c₀ ν) (hc : 0 ≤ c₀)
    (ρ : ProbabilityMeasure ℝ) {r s : ℝ} (hr : r ≤ 1) (hs : s ∈ Icc (0 : ℝ) r) :
    SmoothPart D ((1 - r) * c₀) (mixPM ν ρ s) := by
  have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans hr⟩
  apply (h.mix_left ρ s).mono le_rfl
  rw [mixParam_of_mem hs1]
  exact mul_le_mul_of_nonneg_right (by linarith [hs.2]) hc

/-- Regular starting laws give the positive smooth mass required by WP5 on `s ≤ r < 1`. -/
theorem RegLaw.smoothPart_mix (h : RegLaw D θ vlo vhi ν) (hθ : 0 ≤ θ)
    (ρ : ProbabilityMeasure ℝ) {r s : ℝ} (hr : r < 1) (hs : s ∈ Icc (0 : ℝ) r) :
    SmoothPart D (1 - r) (mixPM ν ρ s) := by
  simpa using (h.smoothPart hθ).mix_left_uniform zero_le_one ρ hr.le hs

/-- Real moment bounds give the lower-integral formulation of the universality class. -/
theorem UnivClass.of_moments {κ₃ B : ℝ}
    (hpos : (ν : Measure ℝ) (Iic 0) = 0) (hmean : lawMean ν = 1)
    (hvlo : vlo ≤ lawVar ν) (hvhi : lawVar ν ≤ vhi)
    (hthird : Integrable (fun x : ℝ => |x - 1| ^ 3) (ν : Measure ℝ))
    (hκ : ∫ x, |x - 1| ^ 3 ∂(ν : Measure ℝ) ≤ κ₃) (he : ExpMom θ B ν) :
    UnivClass vlo vhi κ₃ B θ ν := by
  refine ⟨hpos, hmean, hvlo, hvhi, ?_, ?_⟩
  · rw [← ofReal_integral_eq_lintegral_ofReal hthird
      (ae_of_all _ fun x => by positivity)]
    exact ENNReal.ofReal_le_ofReal hκ
  · rw [← ofReal_integral_eq_lintegral_ofReal he.integrable
      (ae_of_all _ fun x => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal he.le

/-- A regular class supplies uniform third and exponential moments for WP5. -/
theorem RegLaw.univClass (h : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo) :
    UnivClass vlo vhi (regBeta D θ vlo * Real.sqrt vhi ^ 3) (2 * D / θ) (θ / 2) ν := by
  have hm := h.momClass hθ hvlo
  have hmem : MemLp (fun x : ℝ => x - 1) ((3 : ℕ) : ℝ≥0∞) (ν : Measure ℝ) := by
    exact hm.memLp3.sub (memLp_const 1)
  have hi : Integrable (fun x : ℝ => |x - 1| ^ 3) (ν : Measure ℝ) := by
    simpa [Real.norm_eq_abs] using hmem.integrable_norm_pow (by norm_num)
  apply UnivClass.of_moments hm.pos h.mean h.var_ge h.var_le hi _ (h.expMom hθ)
  calc ∫ x, |x - 1| ^ 3 ∂(ν : Measure ℝ)
      ≤ regBeta D θ vlo * Real.sqrt (lawVar ν) ^ 3 := hm.third_le
    _ ≤ regBeta D θ vlo * Real.sqrt vhi ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ ((zero_le_one.trans (one_le_regBeta D θ vlo)))
      gcongr
      exact h.var_le

end

end PGM
