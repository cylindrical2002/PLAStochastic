import PLAStochastic.Index.GEP.StrongApprox.LocalCLT.CharFunDeficit

/-!
# WP5 normalization of bounded density components

A positive bounded density submeasure can be normalized to a probability measure.
Its density and moment bounds depend only on the given lower bound on the component
mass. The rest of the original law may be singular.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Normalize the smooth submeasure without introducing its actual mass as a class parameter. -/
theorem SmoothPart.exists_probability_component {D c₀ : ℝ} {ν : ProbabilityMeasure ℝ}
    (h : SmoothPart D c₀ ν) (hc : 0 < c₀) :
    ∃ ρ : ProbabilityMeasure ℝ,
      ENNReal.ofReal c₀ • (ρ : Measure ℝ) ≤ (ν : Measure ℝ) ∧
      LocBd (D / c₀) (ρ : Measure ℝ) ∧
      (ρ : Measure ℝ) ≤ ENNReal.ofReal c₀⁻¹ • (ν : Measure ℝ) := by
  obtain ⟨f, _, _, hfD, hmass, hν⟩ := h.part
  let η : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have hην : η ≤ (ν : Measure ℝ) := hν
  let : IsFiniteMeasure η := isFiniteMeasure_of_le (ν : Measure ℝ) hην
  have hmass' : ENNReal.ofReal c₀ ≤ η univ := by
    simpa [η, withDensity_apply] using hmass
  have hm0 : η univ ≠ 0 :=
    ne_of_gt ((ENNReal.ofReal_pos.mpr hc).trans_le hmass')
  let : NeZero η := ⟨fun hz => hm0 (by simp [hz])⟩
  let ρ : ProbabilityMeasure ℝ := ⟨(η univ)⁻¹ • η, inferInstance⟩
  have hρ : (ρ : Measure ℝ) = (η univ)⁻¹ • η := rfl
  have hnorm : η univ • (ρ : Measure ℝ) = η := by
    rw [hρ, smul_smul, ENNReal.mul_inv_cancel hm0 (measure_ne_top η univ), one_smul]
  have hinv : (η univ)⁻¹ ≤ ENNReal.ofReal c₀⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hc]
    exact ENNReal.inv_le_inv.mpr hmass'
  have hρη : (ρ : Measure ℝ) ≤ ENNReal.ofReal c₀⁻¹ • η := by
    rw [hρ]
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
  have hηloc : LocBd D η := by
    intro A hA
    change volume.withDensity (fun x => ENNReal.ofReal (f x)) A ≤ _
    rw [withDensity_apply _ hA]
    calc ∫⁻ x in A, ENNReal.ofReal (f x) ≤ ∫⁻ _ in A, ENNReal.ofReal D :=
          lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hfD x))
      _ = ENNReal.ofReal D * volume A := by simp
  refine ⟨ρ, ?_, ?_, hρη.trans (_root_.smul_le_smul_left _ hην)⟩
  · calc ENNReal.ofReal c₀ • (ρ : Measure ℝ) ≤ η univ • (ρ : Measure ℝ) := by
          intro A
          simp only [Measure.smul_apply, smul_eq_mul]
          gcongr
      _ = η := hnorm
      _ ≤ (ν : Measure ℝ) := hην
  · intro A hA
    calc (ρ : Measure ℝ) A ≤ (ENNReal.ofReal c₀⁻¹ • η) A := hρη A
      _ = ENNReal.ofReal c₀⁻¹ * η A := by rw [Measure.smul_apply, smul_eq_mul]
      _ ≤ ENNReal.ofReal c₀⁻¹ * (ENNReal.ofReal D * volume A) := by
          gcongr
          exact hηloc A hA
      _ = ENNReal.ofReal (D / c₀) * volume A := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
          congr 2
          ring

/-- The normalized component inherits `L²` and a uniform second moment about the origin. -/
theorem SmoothPart.exists_probability_component_of_second_moment
    {D c₀ C : ℝ} {ν : ProbabilityMeasure ℝ}
    (h : SmoothPart D c₀ ν) (hc : 0 < c₀)
    (h2 : MemLp id 2 (ν : Measure ℝ))
    (hC : ∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ) ≤ C) :
    ∃ ρ : ProbabilityMeasure ℝ,
      ENNReal.ofReal c₀ • (ρ : Measure ℝ) ≤ (ν : Measure ℝ) ∧
      LocBd (D / c₀) (ρ : Measure ℝ) ∧
      MemLp id 2 (ρ : Measure ℝ) ∧
      ∫ x : ℝ, x ^ 2 ∂(ρ : Measure ℝ) ≤ C / c₀ := by
  obtain ⟨ρ, hpart, hloc, hdom⟩ := h.exists_probability_component hc
  refine ⟨ρ, hpart, hloc,
    h2.of_measure_le_smul ENNReal.ofReal_ne_top hdom, ?_⟩
  calc ∫ x : ℝ, x ^ 2 ∂(ρ : Measure ℝ)
      ≤ ∫ x : ℝ, x ^ 2 ∂(ENNReal.ofReal c₀⁻¹ • (ν : Measure ℝ)) :=
        integral_mono_measure hdom (ae_of_all _ fun x => sq_nonneg x)
          (h2.integrable_sq.smul_measure ENNReal.ofReal_ne_top)
    _ = c₀⁻¹ * ∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ) := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hc.le),
          smul_eq_mul]
    _ ≤ c₀⁻¹ * C := mul_le_mul_of_nonneg_left hC (inv_nonneg.mpr hc.le)
    _ = C / c₀ := by ring

/-- The explicit class-uniform gap for a density part of mass at least `c₀`. -/
def smoothPartCramerGap (D c₀ C t₀ : ℝ) : ℝ :=
  c₀ * (c0CharFn * min (t₀ ^ 2) (1 / (C / c₀)) / (D / c₀) ^ 2 / 2)

theorem smoothPartCramerGap_pos {D c₀ C t₀ : ℝ}
    (hD : 0 < D) (hc : 0 < c₀) (hC : 0 < C) (ht₀ : 0 < t₀) :
    0 < smoothPartCramerGap D c₀ C t₀ := by
  have hchar := c0CharFn_pos
  unfold smoothPartCramerGap
  positivity

/-- A bounded density part gives a uniform Cramér gap even with a singular remainder. -/
theorem SmoothPart.norm_charFun_le_uniform {D c₀ C t₀ : ℝ} {ν : ProbabilityMeasure ℝ}
    (h : SmoothPart D c₀ ν) (hc : 0 < c₀) (h2 : MemLp id 2 (ν : Measure ℝ))
    (hC : ∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ) ≤ C) (ht₀ : 0 < t₀)
    {t : ℝ} (ht : t₀ ≤ |t|) :
    ‖charFun (ν : Measure ℝ) t‖ ≤ 1 - smoothPartCramerGap D c₀ C t₀ := by
  obtain ⟨ρ, hpart, hloc, hρ2, hρC⟩ :=
    h.exists_probability_component_of_second_moment hc h2 hC
  exact norm_charFun_le_of_component_gap hc.le hpart
    (norm_charFun_le_uniform_of_locBd hloc hρ2 hρC ht₀ ht)

/-- WP5's untilted Cramér bound has constants depending only on the stated class parameters. -/
theorem UnivClass.norm_charFun_le_uniform {vlo vhi κ₃ B θ D c₀ t₀ : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : UnivClass vlo vhi κ₃ B θ ν)
    (hs : SmoothPart D c₀ ν) (hc : 0 < c₀) (ht₀ : 0 < t₀) {t : ℝ} (ht : t₀ ≤ |t|) :
    ‖charFun (ν : Measure ℝ) t‖ ≤ 1 - smoothPartCramerGap D c₀ (vhi + 1) t₀ := by
  exact hs.norm_charFun_le_uniform hc (hν.memLp3.mono_exponent (by norm_num))
    hν.integral_sq_le ht₀ ht

theorem UnivClass.smoothPartCramerGap_pos {vlo vhi κ₃ B θ D c₀ t₀ : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : UnivClass vlo vhi κ₃ B θ ν)
    (hs : SmoothPart D c₀ ν) (hc : 0 < c₀) (ht₀ : 0 < t₀) :
    0 < smoothPartCramerGap D c₀ (vhi + 1) t₀ := by
  have hv : 0 ≤ vhi := (integral_nonneg (fun x => sq_nonneg (x - lawMean ν))).trans hν.var_le
  exact PGM.smoothPartCramerGap_pos (hs.D_pos hc) hc (by linarith) ht₀

end

end PGM
