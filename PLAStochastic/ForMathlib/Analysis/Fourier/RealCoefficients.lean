import PLAStochastic.ForMathlib.Analysis.Fourier.InverseAsymptotics
import PLAStochastic.ForMathlib.Analysis.Fourier.CoefficientMeasurable

/-! # Reality of the asymptotic inverse Fourier coefficients -/

noncomputable section

open Filter Topology MeasureTheory Finset

namespace PGM

theorem FourierBandEstimates.rotate_I {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    (h : FourierBandEstimates φ a) :
    FourierBandEstimates (fun eps u => Complex.I * φ eps u) (fun k u => Complex.I * a k u) := by
  have hnorm (z : ℂ) : ‖Complex.I * z‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hrem (eps u : ℝ) (P : ℕ) :
      Complex.I * φ eps u - ∑ k ∈ range (P + 1), ((eps⁻¹) ^ k : ℝ) • (Complex.I * a k u) =
        Complex.I * (φ eps u - ∑ k ∈ range (P + 1), ((eps⁻¹) ^ k : ℝ) • a k u) := by
    rw [mul_sub, mul_sum]
    congr 1
    exact sum_congr rfl fun k _ => by
      change (((eps⁻¹) ^ k : ℝ) : ℂ) * (Complex.I * a k u) =
        Complex.I * ((((eps⁻¹) ^ k : ℝ) : ℂ) * a k u)
      ring
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨δ, hδ, hδ1, c, U, K, hc, hU, hK, d, hm, ha⟩ := h.delta
    refine ⟨δ, hδ, hδ1, c, U, K, hc, hU, hK, d, ?_, ?_⟩
    · filter_upwards [hm] with eps he u hu hl
      simpa only [hnorm] using he u hu hl
    · intro k
      obtain ⟨B, hB, d, hb⟩ := ha k
      exact ⟨B, hB, d, fun u => by simpa only [hnorm] using hb u⟩
  · intro r
    obtain ⟨K, hK, he⟩ := h.high r
    refine ⟨K, hK, ?_⟩
    filter_upwards [he] with eps he u
    simpa only [hnorm] using he u
  · intro P A hA
    obtain ⟨K, hK, d, he⟩ := h.low P A hA
    refine ⟨K, hK, d, ?_⟩
    filter_upwards [he] with eps he u hu
    rw [hrem, hnorm]
    exact he u hu

/-- If the actual inverse transforms are eventually real, every inverse coefficient
is real. This is proved by applying uniqueness to the rotated imaginary expansion. -/
theorem FourierBandEstimates.inverse_coefficients_real {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    (h : FourierBandEstimates φ a)
    (hφ : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps))
    (hreal : ∀ᶠ eps in atTop, ∀ x, (angularInverse (φ eps) x).im = 0) (k : ℕ) (x : ℝ) :
    angularInverse (a k) x = (angularRealInverse (a k) x : ℂ) := by
  have hrot := h.rotate_I
  have hm : ∀ᶠ eps in atTop, AEStronglyMeasurable (fun u => Complex.I * φ eps u) :=
    hφ.mono fun _ he => he.const_mul _
  have hu := hrot.uniform_inverse_expansion hm (hrot.coefficient_aestronglyMeasurable hm) 0
  simp only [iteratedDeriv_zero] at hu
  have hz : ∀ᶠ eps in atTop, angularRealInverse (fun u => Complex.I * φ eps u) x = 0 := by
    filter_upwards [hreal] with eps he
    simp only [angularRealInverse, angularInverse_const_mul, Complex.I_mul_re, he x, neg_zero]
  have hc := hu.coefficient_zero hz k
  simp only [angularRealInverse, angularInverse_const_mul, Complex.I_mul_re] at hc
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using neg_eq_zero.mp hc

end PGM
