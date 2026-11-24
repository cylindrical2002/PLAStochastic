import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.Joint
import PLAStochastic.Index.GEP.Kernel.Output.Identification.UniformWindow
import PLAStochastic.Index.GEP.Kernel.Output.Identification.InterfaceTransfer

/-! # Converting the physical-weight budgets to the original scale C and width 2ε -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
set_option maxHeartbeats 1000000

/-- The output exponent is fixed from the diffusive-scale budget first. A
later input-tail exponent may enlarge only the epsilon threshold through its
small physical-rate requirement `σ`. -/
theorem kernel_regLaw_tail_physical_scale (D θ vlo vhi ρ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (hρ : 0 < ρ) :
    ∃ ηB : ℝ, 0 < ηB ∧ ∀ σ : ℝ, 0 < σ → ∃ e0 : ℝ, 1 ≤ e0 ∧
      ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ η : ℝ, 0 ≤ η → η ≤ ηB →
        0 < lawC eps ν ∧ 1 / lawC eps ν ≤ 128 * regB vhi ∧
        η / lawC eps ν ≤ ρ / (2 * eps) ^ 2 ∧ η / lawC eps ν ≤ σ := by
  obtain ⟨e0, he01, hfacts⟩ := regLaw_facts hD hθ hvlo hv
  let b := regB vhi
  have hb : 0 < b := (regV_pos hvlo).trans_le (regV_le_regB hv)
  let ηB := ρ / (512 * b)
  have hηB : 0 < ηB := by positivity
  refine ⟨ηB, hηB, ?_⟩
  intro σ hσ
  refine ⟨max e0 (1 + (128 * b * ηB) / σ), he01.trans (le_max_left _ _), ?_⟩
  intro eps heps ν hν η hη hηle
  have he0 := (le_max_left e0 (1 + (128 * b * ηB) / σ)).trans heps
  have he1 : 1 ≤ eps := he01.trans he0
  have hep : 0 < eps := by linarith
  obtain ⟨_, hCm, _⟩ := hfacts eps he0 ν hν
  have hC : 0 < lawC eps ν := lt_of_lt_of_le (by positivity) hCm
  have hCE : eps ^ 2 ≤ (128 * b) * lawC eps ν := by
    have hh := (div_le_iff₀ (show 0 < 128 * b by positivity)).mp hCm
    simpa only [mul_comm] using hh
  have hInv : 1 / lawC eps ν ≤ 128 * b := by
    apply (div_le_iff₀ hC).mpr
    nlinarith [show 1 ≤ eps ^ 2 by nlinarith]
  have hscale : η / lawC eps ν ≤ ρ / (2 * eps) ^ 2 := by
    apply (div_le_div_iff₀ hC (sq_pos_of_pos (show 0 < 2 * eps by positivity))).mpr
    have he := mul_le_mul_of_nonneg_left hηle (show 0 ≤ 512 * b by positivity)
    have hbη : 512 * b * ηB = ρ := by dsimp [ηB]; field_simp
    rw [hbη] at he
    have hh := mul_le_mul_of_nonneg_left hCE (show 0 ≤ 4 * η by positivity)
    nlinarith [mul_le_mul_of_nonneg_right he hC.le]
  have hcap : η / lawC eps ν ≤ σ := by
    apply (div_le_iff₀ hC).mpr
    have he := (le_max_right e0 (1 + (128 * b * ηB) / σ)).trans heps
    have he' : 128 * b * ηB ≤ σ * eps ^ 2 := by
      have hh : 128 * b * ηB / σ ≤ eps ^ 2 := by nlinarith
      exact (div_le_iff₀ hσ).mp hh |>.trans_eq (by ring)
    have hh := mul_le_mul_of_nonneg_left hCE hσ.le
    have hh' := mul_le_mul_of_nonneg_left hηle (show 0 ≤ 128 * b by positivity)
    nlinarith
  exact ⟨hC, hInv, hscale, hcap⟩

/-- Keeping the coarse exponent 16 avoids any dependence of the tail power on
input or output weights. The original normalization only changes a class
constant. -/
theorem kernel_tail_div_width {j : ℝ → ℝ} {eps C K ζ B : ℝ}
    (hC : 0 < C) (hK : 0 ≤ K) (_heps : 0 ≤ eps) (_hB : 0 ≤ B)
    (hInv : 1 / C ≤ B) (htail : KernelTail (K * (2 * eps) ^ 16) ζ j) :
    KernelTail ((B * K * 2 ^ 16) * eps ^ 16) ζ (fun x => j x / C) := by
  filter_upwards [htail] with x hx
  rw [abs_div, abs_of_pos hC]
  apply (div_le_div_of_nonneg_right hx hC.le).trans
  have hh := mul_le_mul_of_nonneg_left hInv
    (show 0 ≤ K * (2 * eps) ^ 16 * Real.exp (ζ * x) by positivity)
  calc
    _ = (K * (2 * eps) ^ 16 * Real.exp (ζ * x)) * (1 / C) := by ring
    _ ≤ _ := hh
    _ = _ := by ring

end
end PGM
