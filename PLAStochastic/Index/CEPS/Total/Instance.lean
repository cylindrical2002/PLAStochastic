import PLAStochastic.Index.CEPS.Total.Identify
import PLAStochastic.Index.CEPS.Total.Assembly
import PLAStochastic.Index.CEPS.Total.Drawup
import PLAStochastic.Index.CEPS.Tails.Main
import PLAStochastic.Index.CEPS.Glue.Defs

/-!
# WP10: S-9 at one parameter point

For one gap law `ν` (with density `f`, step law `ρW = ν ∘ (1 - ·)⁻¹`), one half-width `ε`
(`w = 2ε`, `b = 1/w`) and one nonzero imaginary mark `t = i y` (scaled mark `z = t/b²`), the exact
representation (E), the drawup occupation identity, the half-line primitive (P12) on `[b, δ]`,
the identification of the scaled normal expression of `Scaled/` with (3.11), and the assembly
algebra give (`ceps_close_at_point`)

  `‖E e^{-t S_T} - cepsScaledTrueNormalExpression dom ρW b δ z‖ ≤ ‖d_t‖ (e₁ + e₂ + 2 δ e₄) + e₃`

whenever the outer tails are at most `e₁`, `e₂` (S-7), the drawup is within `e₃` of its normal
main term (S-8) and the pair is within `e₄` of the physical normal pair on `[-δ, δ]` (S-6).
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf

namespace PGM

/-- `d_t = 1 - φ(t)` in the step-law form. -/
theorem cepsMarkedDiscount_map_one_sub (ν : ProbabilityMeasure ℝ) (t : ℂ) :
    cepsMarkedDiscount ((ν : Measure ℝ).map fun x => 1 - x) t = 1 - cepsLaplace ν t := by
  unfold cepsMarkedDiscount stepTransform cepsLaplace
  congr 1
  rw [integral_map (by fun_prop) (by fun_prop), ← integral_const_mul]
  congr 1
  funext x
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The actual transform at `t = 0` is `1`. -/
theorem cepsActualTransform_zero (eps : ℝ) (ν : ProbabilityMeasure ℝ) :
    cepsActualTransform eps ν 0 = 1 := by
  unfold cepsActualTransform
  simp

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
/-- The upper endpoint of the half-line primitive is the S-8 main term. -/
theorem d_mul_halfPrimitive_eq_drawupMain (hW : IsStepLaw ρW fW D θ v) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ dom.μ₀) {t : ℂ} (hq : ‖t * (1 + (δ : ℂ))‖ ≤ dom.q₀)
    (hd : cepsMarkedDiscount ρW t ≠ 0) (w : ℂ) :
    cepsMarkedDiscount ρW t * cepsHalfPrimitiveMarked D θ dom ρW t w δ =
      (cepsWHNormalData D θ ρW δ (t * (1 + (δ : ℂ)))).regularAmplitude (dom.canonL ρW) δ
          (t * (1 + (δ : ℂ))) t *
        exp (-((cepsWHNormalData D θ ρW δ (t * (1 + (δ : ℂ)))).βp - t) * (w * (1 + (δ : ℂ)))) := by
  have hμ : |δ| ≤ dom.μ₀ := by rwa [abs_of_nonneg hδ0]
  have hμ' : ‖(δ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  rw [d_mul_halfPrimitive dom hW hθ hD hμ hq hd w]
  set q := t * (1 + (δ : ℂ))
  have hdq := CepsC6.cepsD_eq_mul_cepsQ dom hW hθ hD hμ' hq t
  have hd0 : cepsD ρW δ q t ≠ 0 := by rw [cepsD_marked_eq]; exact hd
  have hβ : cepsRootPlus D θ ρW δ q - t ≠ 0 := by
    intro h0; apply hd0; rw [hdq, h0, zero_mul, zero_mul]
  have he := CepsNormalData.amplitude_eq_regularAmplitude (cepsWHNormalData D θ ρW δ q)
    (dom.canonL ρW) δ q (t := t) (by
      show cepsD ρW δ q t = _
      rw [hdq]; simp only [cepsWHNormalData]; ring) hβ
  rw [← he]
  rfl

include hθ hD in
/-- **S-9 at one parameter point.** -/
theorem ceps_close_at_point {ν : ProbabilityMeasure ℝ}
    (hW : IsStepLaw ((ν : Measure ℝ).map fun x => 1 - x) fW D θ v)
    {D₀ θ₀ vlo vhi : ℝ} (hν : RegLaw D₀ θ₀ vlo vhi ν) (hvlo : 0 < vlo) (hθ₀ : 0 < θ₀)
    (hD₀ : 0 < D₀) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D₀)
    {m : ℕ} {η M δ w : ℝ} {z : ℂ}
    (hI : CepsIdentData dom ((ν : Measure ℝ).map fun x => 1 - x) fW m η M w⁻¹ δ z)
    (hw : 0 < w) (hδ1 : δ < 1) (hδμ : δ < dom.μ₀ / 4)
    (htq : ‖((w⁻¹ : ℝ) : ℂ) ^ 2 * z‖ * (1 + δ) < dom.q₀ / 4)
    {e₁ e₂ e₃ e₄ : ℝ}
    (hpos : ‖(∑ k ∈ Finset.range (⌊w⌋₊ + 1), cepsLaplace ν (((w⁻¹ : ℝ) : ℂ) ^ 2 * z) ^ k) +
        (∫ μ in Ici δ, cepsActualPair ν f (w / 2) (((w⁻¹ : ℝ) : ℂ) ^ 2 * z) μ) -
        cepsDrawupOccupation ν δ (w * (1 + δ)) (((w⁻¹ : ℝ) : ℂ) ^ 2 * z)‖ ≤ e₁)
    (hneg : ‖∫ μ in Ioo (-1) (-δ), cepsActualPair ν f (w / 2) (((w⁻¹ : ℝ) : ℂ) ^ 2 * z) μ‖ ≤ e₂)
    (hdraw : ‖cepsDrawup ν (1 + δ) 1 (w * (1 + δ)) (((w⁻¹ : ℝ) : ℂ) ^ 2 * z)
        ((((w⁻¹ : ℝ) : ℂ) ^ 2 * z) * (1 + (δ : ℂ))) -
      (cepsWHNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x) δ
          ((((w⁻¹ : ℝ) : ℂ) ^ 2 * z) * (1 + (δ : ℂ)))).regularAmplitude
          (dom.canonL ((ν : Measure ℝ).map fun x => 1 - x)) δ
          ((((w⁻¹ : ℝ) : ℂ) ^ 2 * z) * (1 + (δ : ℂ))) (((w⁻¹ : ℝ) : ℂ) ^ 2 * z) *
        exp (-((cepsWHNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x) δ
          ((((w⁻¹ : ℝ) : ℂ) ^ 2 * z) * (1 + (δ : ℂ)))).βp - ((w⁻¹ : ℝ) : ℂ) ^ 2 * z) *
            ((w * (1 + δ) : ℝ) : ℂ))‖ ≤ e₃)
    (hpair : ∀ μ ∈ Icc (-δ) δ, ‖cepsActualPair ν f (w / 2) (((w⁻¹ : ℝ) : ℂ) ^ 2 * z) μ -
      cepsPhysicalPair dom ((ν : Measure ℝ).map fun x => 1 - x) w⁻¹ z μ‖ ≤ e₄) :
    ‖cepsActualTransform (w / 2) ν (((w⁻¹ : ℝ) : ℂ) ^ 2 * z) -
        cepsScaledTrueNormalExpression dom ((ν : Measure ℝ).map fun x => 1 - x) w⁻¹ δ z‖ ≤
      ‖1 - cepsLaplace ν (((w⁻¹ : ℝ) : ℂ) ^ 2 * z)‖ * (e₁ + e₂ + 2 * δ * e₄) + e₃ := by
  set ρ := (ν : Measure ℝ).map fun x => 1 - x
  set b := w⁻¹
  set t := ((b : ℝ) : ℂ) ^ 2 * z with ht_def
  have hb : 0 < b := inv_pos.mpr hw
  have hδ : 0 < δ := hb.trans_le hI.le
  have ht0 : t.re = 0 := by
    rw [ht_def, show ((b : ℝ) : ℂ) ^ 2 = ((b ^ 2 : ℝ) : ℂ) by push_cast; ring, re_ofReal_mul,
      hI.imag, mul_zero]
  have htne : t ≠ 0 := hI.t_ne
  have htre : 0 ≤ t.re := ht0.symm.le
  have hd : cepsMarkedDiscount ρ t ≠ 0 :=
    cepsMarkedDiscount_ne_zero_on_unit hW hθ hD htne hI.unit
  have hdφ : cepsMarkedDiscount ρ t = 1 - cepsLaplace ν t := cepsMarkedDiscount_map_one_sub ν t
  -- (E)
  obtain ⟨hrep, hJint, -, -⟩ := ceps_exact_marked_rep_of_regLaw_pos hν hvlo (half_pos hw) hf htre
  rw [show 2 * (w / 2) = w by ring] at hrep
  -- the drawup occupation identity
  have hocc := cepsDrawupOccupation_mul_of_regLaw hν hθ₀ hD₀ hvlo hδ (l := w * (1 + δ))
    (by positivity) hf htre
  have hq1 : t * ((1 + δ : ℝ) : ℂ) = t * (1 + (δ : ℂ)) := by push_cast; ring
  rw [hq1] at hocc
  -- the half-line primitive on `[b, δ]`
  have hJinf := physicalHalfPair_integrableOn dom hW hθ hD hI
  have hftc := halfLine_integral_eq dom hW hθ hD hI.sobolev hI.order hI.weight hb hI.le hδμ
    ht0 htne (by simpa only [ht_def] using htq) hI.unit ((b : ℂ)⁻¹) hJinf
  have hq : ‖t * (1 + (δ : ℂ))‖ ≤ dom.q₀ :=
    (norm_mul_one_add_le (by rw [abs_of_pos hδ])).trans hI.disc
  have hupper := d_mul_halfPrimitive_eq_drawupMain dom hθ hD hW hδ.le hI.drift hq hd ((b : ℂ)⁻¹)
  have hwb : (b : ℂ)⁻¹ * (1 + (δ : ℂ)) = ((w * (1 + δ) : ℝ) : ℂ) := by
    simp only [b]; push_cast; rw [inv_inv]
  rw [hwb] at hupper
  -- the identification
  rw [scaledNormalExpression_eq_physical dom hW hθ hD hI, hdφ]
  have hJn := physicalPair_integrableOn dom hW hθ hD hI
  refine norm_assembly_sub_le (m := ⌊w⌋₊)
    (Aδ := (1 - cepsLaplace ν t) * cepsHalfPrimitiveMarked D θ dom ρ t (b : ℂ)⁻¹ δ)
    hδ hδ1 hb ?_ hJint hpos hneg hocc ?_ hpair hJn hJinf ?_
  · unfold cepsActualTransform
    rw [hrep]
  · rw [← hdφ, hupper]; exact hdraw
  · simp only [cepsPhysicalHalfPair] at hftc ⊢
    rw [hftc, mul_sub]

end PGM
