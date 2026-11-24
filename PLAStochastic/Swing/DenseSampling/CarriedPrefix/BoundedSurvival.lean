import PLAStochastic.Swing.Algorithm.Measurability
import PLAStochastic.Affine.Process.DriftedSurvival.GridUpper

/-! # The actual carried-prefix event in the longest-interval upper estimate -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The carried observation is index zero of the fresh Brownian clock, while
its anchor-relative age is h. Later accepted samples have ages (j+1)h. -/
def nativeBoundedCarriedFit (D : ℕ → ℝ) (w ε M h : ℝ) (N : ℕ) : Prop :=
  ∃ m : ℝ, |m| ≤ M ∧ ∀ j : ℕ, j ≤ N →
    w + D j - m * ((j : ℝ) + 1) * h ∈ Icc 0 (2 * ε)

def nativeCarriedBoundedFitEvent {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (w ε M : ℝ) (h : ℝ≥0) (N : ℕ) : Set Ω :=
  {ω | nativeBoundedCarriedFit (fun j => B ((j : ℝ≥0) * h) ω) w ε M h N}

/-- A bounded feasible candidate implies grid nonnegativity for the fixed
comparison drift M, with a deterministic upper strip bound. -/
theorem nativeBoundedCarriedFit_implies_grid_strip {D : ℕ → ℝ} {w ε M h : ℝ} {N : ℕ}
    (hM : 0 ≤ M) (hh : 0 ≤ h) (hf : nativeBoundedCarriedFit D w ε M h N) :
    ∀ j : ℕ, j ≤ N → w + M * h + D j + M * ((j : ℝ) * h) ∈
      Icc 0 (2 * ε + 2 * M * ((N : ℝ) + 1) * h) := by
  obtain ⟨m, hm, hfit⟩ := hf
  intro j hj
  have hm0 : 0 ≤ m + M := by linarith [(abs_le.mp hm).1]
  have hm2 : m + M ≤ 2 * M := by linarith [(abs_le.mp hm).2]
  have htime : 0 ≤ ((j : ℝ) + 1) * h := mul_nonneg (by positivity) hh
  have hjN : ((j : ℝ) + 1) * h ≤ ((N : ℝ) + 1) * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hj 1) hh
  have hlo := mul_nonneg hm0 htime
  have hup : (m + M) * (((j : ℝ) + 1) * h) ≤ 2 * M * (((N : ℝ) + 1) * h) :=
    mul_le_mul hm2 hjN htime (by positivity)
  have hc := hfit j hj
  constructor <;> nlinarith [hc.1, hc.2]

/-- The carried state upper estimate, before selecting a logarithmic mesh radius.
The maximal-prefix event itself supplies the feasible bounded slope. -/
theorem exists_native_carried_survival_upper {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {M : ℝ} (hM : 0 ≤ M) {q : ℝ≥0} (hq : 0 < q) : ∃ C : ℝ, 0 < C ∧
      ∀ w ε : ℝ, ∀ h : ℝ≥0, 0 < h → -M * (h : ℝ) ≤ w →
      ∀ N : ℕ, q ≤ (N : ℝ≥0) * h → ∀ ρ : ℝ, 0 ≤ ρ →
      μ.real (nativeCarriedBoundedFitEvent B w ε M h N) ≤
        C * (w + 2 * M * (h : ℝ) + ρ) +
          (N : ℝ) * (2 * Real.exp (-(ρ ^ 2 / (2 * (h : ℝ))))) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C, hC, hb⟩ := exists_linear_brownian_grid_survival_bound hB M hq
  refine ⟨C, hC, ?_⟩
  intro w ε h hh hw N hN ρ hρ
  let x := w + M * (h : ℝ)
  let R := max (2 * ε + 2 * M * ((N : ℝ) + 1) * h) x
  have hx : x ∈ Icc 0 R := ⟨by dsimp only [x]; linarith, le_max_right _ _⟩
  have hsub : nativeCarriedBoundedFitEvent B w ε M h N ⊆ brownianDriftedGridStripEvent B x M R h N := by
    intro ω hω j hj
    have hs := nativeBoundedCarriedFit_implies_grid_strip hM h.coe_nonneg hω j hj
    refine ⟨?_, ?_⟩
    · simpa only [x, NNReal.coe_mul, NNReal.coe_natCast] using hs.1
    · have hu : x + B ((j : ℝ≥0) * h) ω + M * (((j : ℝ≥0) * h) : ℝ) ≤
          2 * ε + 2 * M * ((N : ℝ) + 1) * h := by
        simpa only [x, NNReal.coe_mul, NNReal.coe_natCast] using hs.2
      exact hu.trans (le_max_left _ _)
  have he := (measureReal_mono (μ := μ) hsub).trans (hb x R hx h hh N hN ρ hρ)
  simp only [abs_of_nonneg hM] at he
  have heq : w + M * (h : ℝ) + ρ + M * (h : ℝ) = w + 2 * M * (h : ℝ) + ρ := by ring
  simpa only [x, heq] using he

/-- This is the quantitative upper branch of Appendix B.1, with an explicitly
proved O(h^3) mesh exception and the d=w_++sqrt(h) boundary scale. -/
theorem exists_native_carried_survival_upper_logRadius {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {M : ℝ} (hM : 0 ≤ M) {q : ℝ≥0} (hq : 0 < q) : ∃ C : ℝ, 0 < C ∧
      ∀ w ε : ℝ, ∀ h : ℝ≥0, 0 < h → (h : ℝ) ≤ 1 → -M * (h : ℝ) ≤ w →
      ∀ N : ℕ, q ≤ (N : ℝ≥0) * h → ∀ T : ℝ, (N : ℝ) * h ≤ T →
      μ.real (nativeCarriedBoundedFitEvent B w ε M h N) ≤
        C * (max w 0 + Real.sqrt h + brownianGridLogRadius h) + 2 * T * (h : ℝ) ^ 3 := by
  obtain ⟨C, hC, hb⟩ := exists_native_carried_survival_upper hB hM hq
  refine ⟨C * (1 + 2 * M), mul_pos hC (by positivity), ?_⟩
  intro w ε h hh hh1 hw N hN T hNT
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hρ : 0 ≤ brownianGridLogRadius h := Real.sqrt_nonneg _
  have he := hb w ε h hh hw N hN (brownianGridLogRadius h) hρ
  rw [brownianGridLogRadius_chernoff hh' hh1] at he
  have hsq := Real.sq_sqrt (h.coe_nonneg)
  have hhroot : (h : ℝ) ≤ Real.sqrt h := by nlinarith [Real.sqrt_nonneg (h : ℝ)]
  have hmain : w + 2 * M * (h : ℝ) + brownianGridLogRadius h ≤
      (1 + 2 * M) * (max w 0 + Real.sqrt h + brownianGridLogRadius h) := by
    nlinarith [le_max_left w 0, le_max_right w 0, Real.sqrt_nonneg (h : ℝ),
      mul_nonneg hM hρ, mul_nonneg hM (le_max_right w 0)]
  have herr : (N : ℝ) * (2 * (h : ℝ) ^ 4) ≤ 2 * T * (h : ℝ) ^ 3 := by
    calc
      _ = 2 * ((N : ℝ) * (h : ℝ)) * (h : ℝ) ^ 3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNT (by norm_num)) (by positivity)
  exact he.trans (by nlinarith [mul_le_mul_of_nonneg_left hmain hC.le])

end SwingRepair
