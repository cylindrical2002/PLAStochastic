import PLAStochastic.Affine.Process.DriftedSurvival.LinearUpper
import PLAStochastic.Affine.Process.DriftedSurvival.GridChernoff

/-! # Linear boundary bounds for drifted Brownian grid survival -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Grid strip constraints and within-cell oscillation control imply a padded
continuous strip constraint. Only the fixed comparison drift enters the padding. -/
theorem grid_strip_extension (f : ℝ≥0 → ℝ) {x d R ρ : ℝ} {h : ℝ≥0}
    (hh : 0 < h) (hρ : 0 ≤ ρ) (N : ℕ)
    (hgrid : ∀ k : ℕ, k ≤ N → x + f ((k : ℝ≥0) * h) + d * (((k : ℝ≥0) * h) : ℝ) ∈ Icc 0 R)
    (hmod : ∀ k : ℕ, k < N → ∀ u : ℝ≥0, u ≤ h →
      |f ((k : ℝ≥0) * h + u) - f ((k : ℝ≥0) * h)| ≤ ρ) :
    ∀ t : ℝ≥0, t ≤ (N : ℝ≥0) * h →
      x + (ρ + |d| * (h : ℝ)) + f t + d * (t : ℝ) ∈
        Icc 0 (R + 2 * (ρ + |d| * (h : ℝ))) := by
  intro t ht
  have hpad : 0 ≤ ρ + |d| * (h : ℝ) := add_nonneg hρ (mul_nonneg (abs_nonneg _) h.coe_nonneg)
  rcases ht.lt_or_eq with hlt | heq
  · let k : ℕ := ⌊t / h⌋₊
    have hkh : (k : ℝ≥0) * h ≤ t := (le_div_iff₀ hh).mp (Nat.floor_le (by positivity))
    have hk : k < N := (Nat.floor_lt (show (0 : ℝ≥0) ≤ t / h from bot_le)).mpr
      ((div_lt_iff₀ hh).mpr hlt)
    let u := t - (k : ℝ≥0) * h
    have hu : u ≤ h := by
      apply tsub_le_iff_right.mpr
      have hs := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (t / h))
      simpa only [add_mul, one_mul, add_comm] using hs.le
    have hf := hmod k hk u hu
    rw [add_tsub_cancel_of_le hkh] at hf
    have hg := hgrid k hk.le
    have hu0 : (0 : ℝ) ≤ (t : ℝ) - (((k : ℝ≥0) * h) : ℝ) := by
      exact sub_nonneg.mpr (by exact_mod_cast hkh)
    have hur : (t : ℝ) - (((k : ℝ≥0) * h) : ℝ) ≤ (h : ℝ) := by
      have hs : (u : ℝ) ≤ (h : ℝ) := by exact_mod_cast hu
      simpa only [u, NNReal.coe_sub hkh, NNReal.coe_mul] using hs
    have hd : |d * ((t : ℝ) - (((k : ℝ≥0) * h) : ℝ))| ≤ |d| * (h : ℝ) := by
      rw [abs_mul, abs_of_nonneg hu0]
      exact mul_le_mul_of_nonneg_left hur (abs_nonneg _)
    have hfl := (abs_le.mp hf).1
    have hfu := (abs_le.mp hf).2
    have hdl := (abs_le.mp hd).1
    have hdu := (abs_le.mp hd).2
    constructor <;> nlinarith [hg.1, hg.2]
  · rw [heq]
    simp only [NNReal.coe_mul]
    have hg := hgrid N le_rfl
    constructor <;> linarith [hg.1, hg.2]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Actual finite drifted-grid survival event, including the carried initial
point. It does not contain any slope-selection or independence hypothesis. -/
def brownianDriftedGridStripEvent (B : ℝ≥0 → Ω → ℝ) (x d R : ℝ) (h : ℝ≥0) (N : ℕ) : Set Ω :=
  {ω | ∀ k : ℕ, k ≤ N → x + B ((k : ℝ≥0) * h) ω + d * (((k : ℝ≥0) * h) : ℝ) ∈ Icc 0 R}

omit [MeasurableSpace Ω] in
/-- A deterministic event inclusion supplies the continuous comparison and
quantifies the only exceptional grid fluctuation event. -/
theorem brownianDriftedGridStripEvent_subset_padded (x d R : ℝ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) {h : ℝ≥0} (hh : 0 < h) (N : ℕ) {q : ℝ≥0} (hq : q ≤ (N : ℝ≥0) * h) :
    brownianDriftedGridStripEvent B x d R h N ⊆
      {ω | ∀ t : ℝ≥0, t ≤ q → x + (ρ + |d| * (h : ℝ)) + B t ω + d * (t : ℝ) ∈
        Icc 0 (R + 2 * (ρ + |d| * (h : ℝ)))} ∪ brownianGridOscillationEvent B h N ρ := by
  intro ω hω
  by_cases hg : ω ∈ brownianGridOscillationEvent B h N ρ
  · exact Or.inr hg
  · apply Or.inl
    have hm : ∀ k : ℕ, k < N → ∀ u : ℝ≥0, u ≤ h →
        |B ((k : ℝ≥0) * h + u) ω - B ((k : ℝ≥0) * h) ω| ≤ ρ := by
      intro k hk u hu
      by_contra he
      apply hg
      simp only [brownianGridOscillationEvent, mem_iUnion, Finset.mem_range, mem_ofPred_eq]
      exact ⟨k, hk, u, hu, lt_of_not_ge he⟩
    intro t ht
    exact grid_strip_extension (fun t => B t ω) hh hρ N hω hm t (ht.trans hq)

/-- B.1's discrete upper-bound mechanism. The constant is uniform over mesh,
number of samples, strip height, and admissible carried boundary distance. -/
theorem exists_linear_brownian_grid_survival_bound (hB : IsBrownianReal B μ)
    (d : ℝ) {q : ℝ≥0} (hq : 0 < q) : ∃ C : ℝ, 0 < C ∧
      ∀ x R : ℝ, x ∈ Icc 0 R → ∀ h : ℝ≥0, 0 < h → ∀ N : ℕ, q ≤ (N : ℝ≥0) * h →
      ∀ ρ : ℝ, 0 ≤ ρ → μ.real (brownianDriftedGridStripEvent B x d R h N) ≤
        C * (x + ρ + |d| * (h : ℝ)) +
          (N : ℝ) * (2 * Real.exp (-(ρ ^ 2 / (2 * (h : ℝ))))) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C, hC, hb⟩ := exists_linear_drifted_strip_survival_bound hB d hq
  refine ⟨C, hC, ?_⟩
  intro x R hx h hh N hN ρ hρ
  have hpad : 0 ≤ ρ + |d| * (h : ℝ) := add_nonneg hρ (mul_nonneg (abs_nonneg _) h.coe_nonneg)
  have hx' : x + (ρ + |d| * (h : ℝ)) ∈ Icc 0 (R + 2 * (ρ + |d| * (h : ℝ))) := by
    constructor <;> linarith [hx.1, hx.2]
  have hle := measureReal_mono (μ := μ) (brownianDriftedGridStripEvent_subset_padded (B := B) x d R hρ hh N hN)
  apply hle.trans
  apply (measureReal_union_le _ _).trans
  have hu := hb (x + (ρ + |d| * (h : ℝ))) (R + 2 * (ρ + |d| * (h : ℝ))) hx'
  have he := measureReal_brownianGridOscillationEvent_le hB hh N hρ
  simpa only [add_assoc] using add_le_add hu he

end BrownianAffine
