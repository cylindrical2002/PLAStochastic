import PLAStochastic.Index.CEPS.Total.HalfLine
import PLAStochastic.Index.CEPS.Scaled.TrueTransformBudget
import PLAStochastic.Index.CEPS.Scaled.TrueCutoffIntegrability
import PLAStochastic.Index.CEPS.Scaled.TrueHalfPairScaling
import PLAStochastic.Index.CEPS.Scaled.TruePositivePair

/-!
# WP10: the scaled normal expression is the physical normal transform (3.11)

For `b > 0`, a nonzero imaginary scaled mark `z` (physical mark `t = b² z`, width `w = 1/b`)
and a fixed physical cutoff `δ`, the scaled normal expression of `Scaled/`
(`cepsScaledTrueNormalExpression dom ρW b δ z = 𝓔_b(z) - (d_t/b²) ∫ I^mark dλ`) equals

  `d_t P(b) - d_t ∫_{[-δ,δ]} (Ĵ_t(μ) - 1_{μ ≥ b} J^∞_t(μ)) dμ`,

with `P` the marked half-line primitive (`cepsHalfPrimitiveMarked`), the physical normal pair
`Ĵ_t(μ) = cepsScaledTruePhysicalPair dom ρW (μ/b) z b` and the half-line pair
`J^∞_t(μ) = cepsNormalHalfPair (cepsNormalData …) …` (`scaledNormalExpression_eq_physical`). Both
`Ĵ` on `[-δ, δ]` and `J^∞` on `[b, δ]` are integrable. The substitution is `μ = b λ`.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

theorem ofReal_mul_div_cancel {b : ℝ} (hb : b ≠ 0) (μ : ℝ) :
    (b : ℂ) * ((μ / b : ℝ) : ℂ) = (μ : ℂ) := by
  have hb' : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb
  push_cast; field_simp

theorem scaledDiscount_div {b : ℝ} (hb : b ≠ 0) (μ : ℝ) (z : ℂ) :
    cepsComplexScaledDiscount (μ / b) z b = (b : ℂ) ^ 2 * z * (1 + (μ : ℂ)) := by
  rw [cepsComplexScaledDiscount, ofReal_mul_div_cancel hb]

include hW hθ hD in
/-- The physical half-line pair of `Scaled/` is the WP5 half-line pair. -/
theorem halfPhysicalPair_eq_halfPair {b : ℝ} (hb : 0 < b) {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {z : ℂ} (ht : (b : ℂ) ^ 2 * z ≠ 0)
    (hq : ‖(b : ℂ) ^ 2 * z * (1 + (μ : ℂ))‖ ≤ dom.q₀)
    (hu : (b : ℂ) ^ 2 * z ∈ ball (0 : ℂ) (cepsMarkedUnitRadius D θ)) :
    cepsScaledTrueHalfPhysicalPair dom ρW (μ / b) z b =
      cepsNormalHalfPair (cepsNormalData D θ ρW) (dom.canonL ρW) μ ((b : ℂ) ^ 2 * z) (b : ℂ)⁻¹ := by
  set t := (b : ℂ) ^ 2 * z with ht_def
  have hb0 : b ≠ 0 := hb.ne'
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  rw [cepsScaledTrueHalfPhysicalPair_eq_regularHalfPair, ofReal_mul_div_cancel hb0,
    scaledDiscount_div hb0]
  have hd := CepsC6.cepsD_eq_mul_cepsQ dom hW hθ hD hμ' hq t
  have hd0 : cepsD ρW μ (t * (1 + (μ : ℂ))) t ≠ 0 := by
    rw [cepsD_marked_eq]; exact cepsMarkedDiscount_ne_zero_on_unit hW hθ hD ht hu
  have hp : t - cepsRootPlus D θ ρW μ (t * (1 + (μ : ℂ))) ≠ 0 := by
    intro h0
    apply hd0
    rw [hd, show cepsRootPlus D θ ρW μ (t * (1 + (μ : ℂ))) - t = 0 by
      rw [← neg_sub, h0, neg_zero], zero_mul, zero_mul]
  rw [← cepsNormalHalfPairAt_eq_regular (cepsWHNormalData D θ ρW) (dom.canonL ρW) μ
    (t * (1 + (μ : ℂ))) t (b : ℂ)⁻¹ (by
      show cepsD ρW μ (t * (1 + (μ : ℂ))) t = _
      rw [hd]; simp only [cepsWHNormalData]; ring) hp]
  rfl

/-- The physical normal pair of `Scaled/` as a function of the physical drift. -/
def cepsPhysicalPair (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ) (b : ℝ) (z : ℂ) (μ : ℝ) : ℂ :=
  cepsScaledTruePhysicalPair dom ρW (μ / b) z b

/-- The half-line pair at physical mark `t = b² z`, width `w = 1/b`. -/
def cepsPhysicalHalfPair (D θ : ℝ) (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ) (b : ℝ)
    (z : ℂ) (μ : ℝ) : ℂ :=
  cepsNormalHalfPair (cepsNormalData D θ ρW) (dom.canonL ρW) μ ((b : ℂ) ^ 2 * z) (b : ℂ)⁻¹

theorem norm_mul_one_add_le {t : ℂ} {μ δ : ℝ} (hμ : |μ| ≤ δ) :
    ‖t * (1 + (μ : ℂ))‖ ≤ ‖t‖ * (1 + δ) := by
  rw [norm_mul]
  gcongr
  calc ‖1 + (μ : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖(μ : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 + δ := by rw [norm_one, norm_real, Real.norm_eq_abs]; linarith

/-- Hypotheses shared by the identification lemmas. -/
structure CepsIdentData (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ) (fW : ℝ → ℝ) (m : ℕ)
    (η M b δ : ℝ) (z : ℂ) : Prop where
  sobolev : CepsSobolevClass m η fW
  order : 2 ≤ m
  weight : 2 * dom.c₀ ≤ η
  bound : cepsSobolev m η fW ≤ M
  pos : 0 < b
  le : b ≤ δ
  cut : δ ≤ dom.trueDecayScaleBase M / 4
  drift : δ ≤ dom.μ₀
  imag : z.re = 0
  ne : z ≠ 0
  freq : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4
  disc : ‖(b : ℂ) ^ 2 * z‖ * (1 + δ) ≤ dom.q₀
  unit : (b : ℂ) ^ 2 * z ∈ ball (0 : ℂ) (cepsMarkedUnitRadius D θ)

namespace CepsIdentData

variable {dom} {m : ℕ} {η M b δ : ℝ} {z : ℂ}

include hW hθ hD in
theorem mem_freq (h : CepsIdentData dom ρW fW m η M b δ z) {μ : ℝ} (hμ : |μ| ≤ δ) :
    (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M (μ / b) z) := by
  have hM : 0 ≤ M := (cepsSobolev_nonneg m η fW).trans h.bound
  refine cepsScaledTrueDecay_mem_of_cutoff dom hW hθ hD hM h.pos h.cut h.freq ?_
  rw [abs_div, abs_of_pos h.pos]
  exact div_le_div_of_nonneg_right hμ h.pos.le

theorem t_ne (h : CepsIdentData dom ρW fW m η M b δ z) : (b : ℂ) ^ 2 * z ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (ofReal_ne_zero.mpr h.pos.ne')) h.ne

end CepsIdentData

include hW hθ hD in
/-- `b³ J^∞_t(μ) = I^∞(μ/b)` on `[b, δ]`. -/
theorem halfPair_scaled_eq {m : ℕ} {η M b δ : ℝ} {z : ℂ}
    (h : CepsIdentData dom ρW fW m η M b δ z) {μ : ℝ} (hμ : μ ∈ Icc b δ) :
    (b : ℂ) ^ 3 * cepsPhysicalHalfPair D θ dom ρW b z μ =
      cepsScaledTrueHalfPair dom ρW (μ / b) z b := by
  have hμa : |μ| ≤ δ := by rw [abs_of_pos (h.pos.trans_le hμ.1)]; exact hμ.2
  have hlam : 1 ≤ μ / b := (one_le_div h.pos).mpr hμ.1
  have hbs := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M (μ / b) z)
    (h.mem_freq hW hθ hD hμa)
  rw [← cepsScaledTrueHalfPair_eq_physical dom hW hθ hD M (μ / b) hlam h.imag.symm.le h.pos hbs,
    halfPhysicalPair_eq_halfPair dom hW hθ hD h.pos (hμa.trans h.drift) h.t_ne
      ((norm_mul_one_add_le hμa).trans h.disc) h.unit]
  rfl

include hW hθ hD in
/-- `b³ (Ĵ_t(μ) - 1_{μ ≥ b} J^∞_t(μ)) = I^mark(μ/b)` on `[-δ, δ]`. -/
theorem cutoffPair_scaled_eq {m : ℕ} {η M b δ : ℝ} {z : ℂ}
    (h : CepsIdentData dom ρW fW m η M b δ z) {μ : ℝ} (hμ : μ ∈ Icc (-δ) δ) :
    (b : ℂ) ^ 3 * (cepsPhysicalPair dom ρW b z μ -
        (Ici b).indicator (cepsPhysicalHalfPair D θ dom ρW b z) μ) =
      cepsScaledTrueCutoffPair dom ρW b δ z (μ / b) := by
  have hμa : |μ| ≤ δ := abs_le.mpr hμ
  have hbs := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M (μ / b) z)
    (h.mem_freq hW hθ hD hμa)
  have hcut : |μ / b| ≤ δ / b := by
    rw [abs_div, abs_of_pos h.pos]; exact div_le_div_of_nonneg_right hμa h.pos.le
  rw [cepsScaledTrueCutoffPair, if_pos hcut,
    ← cepsScaledTrueSubtractedPair_eq_physical dom hW hθ hD M (μ / b) h.imag.symm.le h.pos hbs,
    cepsScaledTrueSubtractedPhysicalPair]
  by_cases hbμ : b ≤ μ
  · have hlam : 1 ≤ μ / b := (one_le_div h.pos).mpr hbμ
    rw [if_pos hlam, indicator_of_mem (show μ ∈ Ici b from hbμ), cepsPhysicalHalfPair,
      ← halfPhysicalPair_eq_halfPair dom hW hθ hD h.pos (hμa.trans h.drift) h.t_ne
        ((norm_mul_one_add_le hμa).trans h.disc) h.unit]
    rfl
  · have hlam : ¬ 1 ≤ μ / b := fun h1 => hbμ ((one_le_div h.pos).mp h1)
    rw [if_neg hlam, indicator_of_notMem (show μ ∉ Ici b from hbμ), sub_zero]
    rfl

include hW hθ hD in
/-- The scaled half-line pair is bounded on `[1, δ/b]`. -/
theorem halfPair_scaled_bound {m : ℕ} {η M b δ : ℝ} {z : ℂ}
    (h : CepsIdentData dom ρW fW m η M b δ z) {lam : ℝ} (hlam : lam ∈ Icc 1 (δ / b)) :
    ‖cepsScaledTrueHalfPair dom ρW lam z b‖ ≤
      dom.trueHalfEntranceConstant ^ 2 *
        (dom.trueHalfOperatorConstant * (1 + δ / b + Real.sqrt ‖z‖)) := by
  have hb := h.pos
  have hla : |lam| ≤ δ / b := by rw [abs_of_pos (by linarith [hlam.1])]; exact hlam.2
  have hμa : |b * lam| ≤ δ := by
    rw [abs_mul, abs_of_pos hb]
    calc b * |lam| ≤ b * (δ / b) := by gcongr
      _ = δ := mul_div_cancel₀ δ hb.ne'
  have hbd := h.mem_freq hW hθ hD hμa
  rw [show b * lam / b = lam by field_simp [h.pos.ne']] at hbd
  have hbf := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M lam z) hbd
  have hbden := ball_subset_ball ((trueFrequencyScaleRadius_le dom M lam z).trans
    (truePairScaleRadius_le dom M lam z)) hbf
  have hE : ‖exp (((b : ℂ) * z) * (1 + (b : ℂ) * lam))‖ = 1 := by
    rw [norm_exp]
    have : (((b : ℂ) * z) * (1 + (b : ℂ) * lam)).re = 0 := by simp [mul_re, h.imag]
    rw [this, Real.exp_zero]
  have hH := cepsScaledTrueHalfEntrance_positive_budget dom hW hθ hD M lam hlam.1
    h.imag.symm.le hbden
  have hO := cepsScaledTrueHalfBridge_timeOperator_budget dom hW hθ hD M lam hlam.1
    h.imag.symm.le h.pos hbf
  have hX : 1 + |lam| + Real.sqrt ‖z‖ ≤ 1 + δ / b + Real.sqrt ‖z‖ := by linarith
  have hC0 : 0 ≤ dom.trueHalfOperatorConstant := by
    have := (norm_nonneg _).trans hO
    have hp : 0 < 1 + |lam| + Real.sqrt ‖z‖ := by positivity
    exact nonneg_of_mul_nonneg_left this hp
  unfold cepsScaledTrueHalfPair
  rw [norm_mul, norm_mul, hE, one_mul, norm_pow]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hH 2) (hO.trans (by gcongr))
    (norm_nonneg _) (by positivity)

include hW hθ hD in
/-- Integrability of the half-line pair on `[b, δ]`. -/
theorem physicalHalfPair_integrableOn {m : ℕ} {η M b δ : ℝ} {z : ℂ}
    (h : CepsIdentData dom ρW fW m η M b δ z) :
    IntegrableOn (cepsPhysicalHalfPair D θ dom ρW b z) (Icc b δ) := by
  set S : Set ℝ := Icc 1 (δ / b)
  set C := dom.trueHalfEntranceConstant ^ 2 *
    (dom.trueHalfOperatorConstant * (1 + δ / b + Real.sqrt ‖z‖))
  have hb := h.pos
  have hM : 0 ≤ M := (cepsSobolev_nonneg m η fW).trans h.bound
  have hmeas := cepsScaledTrueHalfPair_aestronglyMeasurable_cutoff dom hW hθ hD h.sobolev h.order
    h.weight h.bound (S := S) measurableSet_Icc h.imag.symm.le hb
    (fun a ha => by
      have hla : |a| ≤ δ / b := by rw [abs_of_pos (by linarith [ha.1])]; exact ha.2
      have hμa : |b * a| ≤ δ := by
        rw [abs_mul, abs_of_pos hb]
        calc b * |a| ≤ b * (δ / b) := by gcongr
          _ = δ := mul_div_cancel₀ δ hb.ne'
      have := h.mem_freq hW hθ hD hμa
      rwa [show b * a / b = a by field_simp [hb.ne']] at this)
    (fun a ha => ha.1)
  have hg : Integrable (S.indicator fun a => cepsScaledTrueHalfPair dom ρW a z b) := by
    have hdom : Integrable (S.indicator fun _ : ℝ => C) :=
      (integrableOn_const (C := C) (by simp [S, Real.volume_Icc])).integrable_indicator
        measurableSet_Icc
    refine Integrable.mono' hdom hmeas ?_
    · refine Filter.Eventually.of_forall fun a => ?_
      by_cases ha : a ∈ S
      · rw [indicator_of_mem ha, indicator_of_mem ha]
        exact halfPair_scaled_bound dom hW hθ hD h ha
      · rw [indicator_of_notMem ha, indicator_of_notMem ha, norm_zero]
  have hgc := (hg.comp_div hb.ne').const_mul (((b : ℂ) ^ 3)⁻¹)
  refine (hgc.integrableOn (s := Icc b δ)).congr_fun (fun μ hμ => ?_) measurableSet_Icc
  have hS : μ / b ∈ S := ⟨(one_le_div hb).mpr hμ.1, div_le_div_of_nonneg_right hμ.2 hb.le⟩
  simp only
  rw [indicator_of_mem hS, ← halfPair_scaled_eq dom hW hθ hD h hμ]
  have : (b : ℂ) ^ 3 ≠ 0 := pow_ne_zero _ (ofReal_ne_zero.mpr hb.ne')
  rw [← mul_assoc, inv_mul_cancel₀ this, one_mul]

include hW hθ hD in
/-- On `[-δ, δ]`, `Ĵ = b⁻³ I^mark(·/b) + 1_{μ ≥ b} J^∞`. -/
theorem physicalPair_eq_on {m : ℕ} {η M b δ : ℝ} {z : ℂ}
    (h : CepsIdentData dom ρW fW m η M b δ z) {μ : ℝ} (hμ : μ ∈ Icc (-δ) δ) :
    cepsPhysicalPair dom ρW b z μ = ((b : ℂ) ^ 3)⁻¹ * cepsScaledTrueCutoffPair dom ρW b δ z (μ / b) +
      (Ici b).indicator (cepsPhysicalHalfPair D θ dom ρW b z) μ := by
  rw [← cutoffPair_scaled_eq dom hW hθ hD h hμ]
  have : (b : ℂ) ^ 3 ≠ 0 := pow_ne_zero _ (ofReal_ne_zero.mpr h.pos.ne')
  rw [← mul_assoc, inv_mul_cancel₀ this, one_mul, sub_add_cancel]

theorem indicator_Ici_integrableOn {f : ℝ → ℂ} {b δ : ℝ} (hb : 0 < b)
    (hf : IntegrableOn f (Icc b δ)) : IntegrableOn ((Ici b).indicator f) (Icc (-δ) δ) := by
  have he : Ici b ∩ Icc (-δ) δ = Icc b δ := by
    ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
  refine (integrable_indicator_iff measurableSet_Ici).mpr ?_
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ici, he]
  exact hf

include hW hθ hD in
/-- Integrability of the physical normal pair on `[-δ, δ]`. -/
theorem physicalPair_integrableOn {m : ℕ} {η M b δ : ℝ} {z : ℂ}
    (h : CepsIdentData dom ρW fW m η M b δ z) :
    IntegrableOn (cepsPhysicalPair dom ρW b z) (Icc (-δ) δ) := by
  have hb := h.pos
  have hcut := cepsScaledTrueCutoffPair_integrable dom hW hθ hD h.sobolev h.weight h.bound h.order
    hb h.cut h.imag h.freq
  have h1 := ((hcut.comp_div hb.ne').const_mul (((b : ℂ) ^ 3)⁻¹)).integrableOn (s := Icc (-δ) δ)
  have h2 := indicator_Ici_integrableOn hb
    (physicalHalfPair_integrableOn dom hW hθ hD h)
  exact (h1.add h2).congr_fun (fun μ hμ => (physicalPair_eq_on dom hW hθ hD h hμ).symm)
    measurableSet_Icc

include hW hθ hD in
/-- **The scaled normal expression is the physical normal transform (3.11).** -/
theorem scaledNormalExpression_eq_physical {m : ℕ} {η M b δ : ℝ} {z : ℂ}
    (h : CepsIdentData dom ρW fW m η M b δ z) :
    cepsScaledTrueNormalExpression dom ρW b δ z =
      cepsMarkedDiscount ρW ((b : ℂ) ^ 2 * z) *
          cepsHalfPrimitiveMarked D θ dom ρW ((b : ℂ) ^ 2 * z) (b : ℂ)⁻¹ b -
        cepsMarkedDiscount ρW ((b : ℂ) ^ 2 * z) *
          ∫ μ in Icc (-δ) δ, (cepsPhysicalPair dom ρW b z μ -
            (Ici b).indicator (cepsPhysicalHalfPair D θ dom ρW b z) μ) := by
  have hb := h.pos
  have hb0 : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  set F : ℝ → ℂ := (Icc (-δ) δ).indicator (fun μ => (b : ℂ) ^ 3 *
    (cepsPhysicalPair dom ρW b z μ - (Ici b).indicator (cepsPhysicalHalfPair D θ dom ρW b z) μ))
  have hCF : ∀ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam = F (b * lam) := by
    intro lam
    by_cases hl : |lam| ≤ δ / b
    · have hmem : b * lam ∈ Icc (-δ) δ := by
        have : |b * lam| ≤ δ := by
          rw [abs_mul, abs_of_pos hb]
          calc b * |lam| ≤ b * (δ / b) := by gcongr
            _ = δ := mul_div_cancel₀ δ hb.ne'
        exact abs_le.mp this
      simp only [F]
      rw [indicator_of_mem hmem, cutoffPair_scaled_eq dom hW hθ hD h hmem,
        show b * lam / b = lam by field_simp [hb.ne']]
    · have hmem : b * lam ∉ Icc (-δ) δ := by
        intro hm
        apply hl
        have := abs_le.mpr hm
        rw [abs_mul, abs_of_pos hb] at this
        rw [le_div_iff₀ hb]; linarith
      simp only [F]
      rw [indicator_of_notMem hmem, cepsScaledTrueCutoffPair, if_neg hl]
  have hint : ∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam =
      (b : ℂ) ^ 2 * ∫ μ in Icc (-δ) δ, (cepsPhysicalPair dom ρW b z μ -
        (Ici b).indicator (cepsPhysicalHalfPair D θ dom ρW b z) μ) := by
    simp_rw [hCF]
    rw [Measure.integral_comp_mul_left F b, integral_indicator measurableSet_Icc,
      integral_const_mul, abs_inv, abs_of_pos hb, Complex.real_smul]
    push_cast
    field_simp
  unfold cepsScaledTrueNormalExpression
  rw [cepsScaledMarkedEndpoint_eq_physical dom hW hθ hD hb h.ne h.unit,
    cepsScaledMarkedDiscount_eq_div hW hθ hD z hb0, hint]
  unfold cepsHalfPrimitiveMarked
  field_simp

end PGM
