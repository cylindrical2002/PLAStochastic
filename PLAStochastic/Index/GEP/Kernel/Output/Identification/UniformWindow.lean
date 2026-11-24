import PLAStochastic.Index.GEP.Kernel.Output.Identification.BoundaryKernel

/-! # Uniform window facts for the concrete output kernel -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

theorem output_window_facts_regLaw (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ η0 e0 : ℝ, 0 < η0 ∧ 1 ≤ e0 ∧
      ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ η : ℝ, 0 < η → η ≤ η0 →
        0 < lawC eps ν ∧ η/lawC eps ν ≤ θ/4 ∧
        Summable (fluxWindowMoment eps ν (2*η/lawC eps ν)) ∧
        (∀ᵐ g ∂iidLaw ν, gapSegLen eps g ≠ ⊤) := by
  obtain ⟨e0, he01, hfacts⟩ := regLaw_facts hD hθ hvlo hv
  let b := regB vhi
  have hb : 0 < b := (regV_pos hvlo).trans_le (regV_le_regB hv)
  let c := tailRate * regV vlo
  have hc : 0 < c := mul_pos tailRate_pos (regV_pos hvlo)
  let κ0 := min (θ / 8) (c * θ ^ 2 / (64 * D))
  have hκ0 : 0 < κ0 := lt_min (by positivity) (by positivity)
  let η0 := κ0 / (256 * b)
  have hη0 : 0 < η0 := by positivity
  refine ⟨η0, e0, hη0, he01, fun eps heps ν hν η hη hηle => ?_⟩
  obtain ⟨hfin, hCm, htail, _⟩ := hfacts eps heps ν hν
  have heps1 : 1 ≤ eps := he01.trans heps
  have heps0 : 0 < eps := by linarith
  have he2 : 1 ≤ eps ^ 2 := one_le_pow₀ heps1
  have he2p : 0 < eps ^ 2 := by positivity
  have hC : 0 < lawC eps ν := lt_of_lt_of_le (by positivity) hCm
  let δ := 2 * η / lawC eps ν
  have hδ0 : 0 ≤ δ := by positivity
  have hCE : eps ^ 2 ≤ (128 * b) * lawC eps ν := by
    have hh := (div_le_iff₀ (by positivity : 0 < 128 * b)).mp hCm
    nlinarith
  have hηcap : 256 * b * η ≤ κ0 := by
    have hh := mul_le_mul_of_nonneg_left hηle (by positivity : 0 ≤ 256 * b)
    have he : 256 * b * η0 = κ0 := by dsimp [η0]; field_simp
    rwa [he] at hh
  have hδcap : δ * eps ^ 2 ≤ κ0 := by
    calc
      _ ≤ δ * ((128 * b) * lawC eps ν) := mul_le_mul_of_nonneg_left hCE hδ0
      _ = 256 * b * η := by dsimp [δ]; field_simp; ring
      _ ≤ _ := hηcap
  have hκθ : 2 * δ ≤ θ / 4 := by
    have hh := hδcap.trans (min_le_left (θ / 8) (c * θ ^ 2 / (64 * D)))
    nlinarith [mul_le_mul_of_nonneg_left he2 hδ0]
  have hηθ : η / lawC eps ν ≤ θ / 4 := by
    have he : δ = 2 * (η / lawC eps ν) := by dsimp [δ]; ring
    rw [he] at hκθ
    linarith
  let q := Real.exp (-c / (4 * eps ^ 2))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr (by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith : -c ≤ 0) (by positivity))
  have hq4 : q ^ 4 = tailA vlo eps := by
    rw [show q = Real.exp (-c / (4 * eps ^ 2)) from rfl, ← Real.exp_nat_mul, tailA]
    congr 1
    dsimp [c]
    field_simp
  have htail' : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * (q ^ 4) ^ m) := by
    rw [hq4]
    exact htail
  have hdecay : q * Real.exp (8 * D / θ ^ 2 * δ) < 1 := by
    rw [show q = Real.exp (-c / (4 * eps ^ 2)) from rfl, ← Real.exp_add, Real.exp_lt_one_iff]
    have hh := hδcap.trans (min_le_right (θ / 8) (c * θ ^ 2 / (64 * D)))
    have h1 : 64 * D * (δ * eps ^ 2) ≤ c * θ ^ 2 := by
      rw [le_div_iff₀ (by positivity)] at hh
      linarith
    have h2 : 8 * D / θ ^ 2 * δ ≤ c / (8 * eps ^ 2) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h3 : -c / (4 * eps ^ 2) = -(c / (8 * eps ^ 2)) - c / (8 * eps ^ 2) := by
      field_simp
      ring
    have hcp : 0 < c / (8 * eps ^ 2) := by positivity
    linarith
  have hWin := flux_window_moment_summable hν hθ hq0 hq1 htail' hδ0 hκθ hdecay
  exact ⟨hC, hηθ, hWin, hfin⟩

/-- The concrete weighted IF series supplies the original output primitive
uniformly over the regular class. The weight cap precedes every test. -/
theorem output_isBdryKernel_regLaw (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ η0 e0 : ℝ, 0 < η0 ∧ 1 ≤ e0 ∧
      ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ≥0∞, Measurable f → (ν : Measure ℝ) = volume.withDensity f →
      ∀ η M : ℝ, 0 < η → η ≤ η0 → ∀ ψ : ℝ → ℝ, OutTest η M ψ →
        IsBdryKernel eps ν ψ (outputBoundaryKernel eps ν f ψ) := by
  obtain ⟨η0,e0,hη0,he0,hfacts⟩ := output_window_facts_regLaw D θ vlo vhi hD hθ hvlo hv
  refine ⟨η0,e0,hη0,he0,fun eps heps ν hν f hf hνf η M hη hηle ψ hψ => ?_⟩
  obtain ⟨hC,hηθ,hWin,hfin⟩ := hfacts eps heps ν hν η hη hηle
  exact output_isBdryKernel_of_window hν hθ hf hνf (he0.trans heps) hψ hη hC hηθ hWin hfin

end
end PGM
