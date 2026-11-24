import PLAStochastic.Index.GEP.StrongApprox.Tilt.UniformComponent

/-! # Affine normalization and Fourier components for the tilted class -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Translation leaves the modulus of a real characteristic function unchanged. -/
theorem norm_charFun_map_sub_const (μ : Measure ℝ) (m t : ℝ) :
    ‖charFun (μ.map (fun x => x - m)) t‖ = ‖charFun μ t‖ := by
  simp only [sub_eq_add_neg, charFun_map_add_const, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Affine normalization changes only the frequency in the characteristic-function modulus. -/
theorem norm_charFun_map_sub_div (μ : Measure ℝ) (m s t : ℝ) :
    ‖charFun (μ.map (fun x => (x - m) / s)) t‖ = ‖charFun μ (t / s)‖ := by
  have he : μ.map (fun x => (x - m) / s) =
      (μ.map (fun x => x - m)).map (fun x => s⁻¹ * x) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    simp only [Function.comp_apply, div_eq_mul_inv, mul_comm]
  rw [he, charFun_map_mul, norm_charFun_map_sub_const]
  congr 2
  ring

/-- A positive density part yields an integrable squared Fourier transform of a probability component. -/
theorem SmoothPart.exists_fourier_component {D c : ℝ} {ν : ProbabilityMeasure ℝ}
    (hs : SmoothPart D c ν) (hc : 0 < c) :
    ∃ σ : ProbabilityMeasure ℝ, ENNReal.ofReal c • (σ : Measure ℝ) ≤ (ν : Measure ℝ) ∧
      LocBd (D / c) (σ : Measure ℝ) ∧
      Integrable (fun t : ℝ => ‖charFun (σ : Measure ℝ) t‖ ^ 2) ∧
      (∫ t : ℝ, ‖charFun (σ : Measure ℝ) t‖ ^ 2) ≤ 2 * Real.pi * (D / c) := by
  obtain ⟨σ, hpart, hloc, -⟩ := hs.exists_probability_component hc
  obtain ⟨hi, hb⟩ := integral_norm_charFun_sq_le hloc
  exact ⟨σ, hpart, hloc, hi, hb⟩

/-- A smooth probability component and a finite remainder give an exact Fourier decomposition. -/
theorem SmoothPart.exists_fourier_decomposition {D c : ℝ} {ν : ProbabilityMeasure ℝ}
    (hs : SmoothPart D c ν) (hc : 0 < c) :
    ∃ σ : ProbabilityMeasure ℝ, ∃ η : Measure ℝ,
      (ν : Measure ℝ) = ENNReal.ofReal c • (σ : Measure ℝ) + η ∧
      IsFiniteMeasure η ∧ η.real univ = 1 - c ∧
      LocBd (D / c) (σ : Measure ℝ) ∧
      Integrable (fun t : ℝ => ‖charFun (σ : Measure ℝ) t‖ ^ 2) ∧
      (∫ t : ℝ, ‖charFun (σ : Measure ℝ) t‖ ^ 2) ≤ 2 * Real.pi * (D / c) ∧
      ∀ t : ℝ, charFun (ν : Measure ℝ) t = c * charFun (σ : Measure ℝ) t + charFun η t ∧
        ‖charFun η t‖ ≤ 1 - c := by
  obtain ⟨σ, hpart, hloc, hi, hb⟩ := hs.exists_fourier_component hc
  let : IsFiniteMeasure (ENNReal.ofReal c • (σ : Measure ℝ)) :=
    isFiniteMeasure_of_le (ν : Measure ℝ) hpart
  let η := (ν : Measure ℝ) - ENNReal.ofReal c • (σ : Measure ℝ)
  have hsum : ENNReal.ofReal c • (σ : Measure ℝ) + η = (ν : Measure ℝ) := by
    rw [add_comm]
    exact Measure.sub_add_cancel_of_le hpart
  have hη : IsFiniteMeasure η := inferInstance
  have hmass : η.real univ = 1 - c := by
    have he := congrArg (fun μ : Measure ℝ => μ.real univ) hsum
    rw [measureReal_add_apply, measureReal_ennreal_smul_apply,
      probReal_univ (μ := (σ : Measure ℝ)), ENNReal.toReal_ofReal hc.le,
      probReal_univ (μ := (ν : Measure ℝ)), mul_one] at he
    linarith
  refine ⟨σ, η, hsum.symm, hη, hmass, hloc, hi, hb, ?_⟩
  intro t
  constructor
  · rw [← hsum, charFun_add_measure_real, charFun_smul_measure_real,
      ENNReal.toReal_ofReal hc.le, RCLike.real_smul_eq_coe_mul]
    rfl
  · exact (norm_charFun_le t).trans_eq hmass

/-- Recentring and scaling preserve a class-uniform Cramer gap away from the origin. -/
theorem UnivClass.standardized_centeredTilt_cramer
    {vlo vhi κ₃ B θ D c t₀ : ℝ} {ν : ProbabilityMeasure ℝ}
    (h : UnivClass vlo vhi κ₃ B θ ν) (hs : SmoothPart D c ν)
    (hθ : 0 < θ) (hc : 0 < c) (ht₀ : 0 < t₀) {lam : ℝ} (hlam : |lam| ≤ θ / 2)
    {ρ : ProbabilityMeasure ℝ} (hρ : (ρ : Measure ℝ) = centeredTilt ν lam)
    (m : ℝ) {s S : ℝ} (hs0 : 0 < s) (hsS : s ≤ S) :
    let q := tiltComponentFactor θ B c
    0 < smoothPartCramerGap (q * D) (q * (c / 2)) (tiltRawSecondBound θ B) (t₀ / S) ∧
      ∀ t : ℝ, t₀ ≤ |t| →
        ‖charFun ((ρ : Measure ℝ).map (fun x => (x - m) / s)) t‖ ≤
          1 - smoothPartCramerGap (q * D) (q * (c / 2)) (tiltRawSecondBound θ B) (t₀ / S) := by
  have hS : 0 < S := hs0.trans_le hsS
  obtain ⟨hpos, hgap⟩ := h.centeredTilt_cramer hs hθ hc (div_pos ht₀ hS) hlam hρ
  refine ⟨hpos, ?_⟩
  intro t ht
  rw [norm_charFun_map_sub_div]
  apply hgap
  rw [abs_div, abs_of_pos hs0]
  calc
    t₀ / S ≤ t₀ / s := div_le_div_of_nonneg_left ht₀.le hs0 hsS
    _ ≤ |t| / s := div_le_div_of_nonneg_right ht hs0.le

end

end PGM
