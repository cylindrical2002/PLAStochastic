import PLAStochastic.Swing.DenseSampling.Rejection.LongOutputCover

/-! # Deterministic mesh choices for the maximum probability estimate -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem native_maximum_comparison_cutoff {M : ℝ} (hM : 0 ≤ M) :
    ∃ H : ℝ≥0, 0 < H ∧ (H : ℝ) ≤ 1/32 ∧ M*(H : ℝ) ≤ 1 := by
  have hp : 0 < min (1/32 : ℝ) (1/(M+1)) := lt_min (by norm_num) (by positivity)
  let H : ℝ≥0 := ⟨min (1/32) (1/(M+1)), hp.le⟩
  have hH : (H : ℝ) = min (1/32) (1/(M+1)) := rfl
  refine ⟨H, by exact_mod_cast hH ▸ hp, hH.le.trans (min_le_left _ _), ?_⟩
  have hb : (H : ℝ) ≤ 1/(M+1) := hH.le.trans (min_le_right _ _)
  have hm := (le_div_iff₀ (show 0 < M+1 by positivity)).mp hb
  nlinarith [H.coe_nonneg]

/-- One ceiling chooses enough future samples for the survival estimate while
remaining inside every segment of duration at least a. -/
theorem native_maximum_future_grid {a : ℝ} (ha : 0 < a) {h : ℝ≥0} (hh : 0 < h)
    (hha : (h : ℝ) ≤ a/4) :
    let N := ⌈(a/2)/(h : ℝ)⌉₊
    a/2 ≤ (N : ℝ)*(h : ℝ) ∧ ((N : ℝ)+1)*(h : ℝ) ≤ a ∧ (N : ℝ)*(h : ℝ) ≤ a := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hl := Nat.le_ceil ((a/2)/(h : ℝ))
  have hu := Nat.ceil_lt_add_one (show 0 ≤ (a/2)/(h : ℝ) by positivity)
  have hlow := (div_le_iff₀ hhR).mp hl
  have hup := mul_lt_mul_of_pos_right hu hhR
  rw [add_mul, div_mul_cancel₀ _ hhR.ne', one_mul] at hup
  exact ⟨hlow, by nlinarith, by nlinarith⟩

/-- The extended output pays all local duration charges and still lies in a
fixed deterministic horizon when the mesh is small. -/
theorem native_maximum_extended_grid {h H : ℝ≥0} (hh : 0 < h) {n : ℕ} {T : ℝ}
    (hnT : (n : ℝ)*(h : ℝ) ≤ T) (hH : (H : ℝ) ≤ 1/32) (hh1 : (h : ℝ) ≤ 1/2) :
    let last := n+⌈(H : ℝ)/(h : ℝ)⌉₊+1
    n+1 ≤ last ∧ (n : ℝ)*(h : ℝ)+(H : ℝ) ≤ (last : ℝ)*(h : ℝ) ∧
      (last : ℝ)*(h : ℝ) ≤ T+2 := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hl := Nat.le_ceil ((H : ℝ)/(h : ℝ))
  have hu := Nat.ceil_lt_add_one (div_nonneg H.coe_nonneg h.coe_nonneg)
  have hlow := (div_le_iff₀ hhR).mp hl
  have hup := mul_lt_mul_of_pos_right hu hhR
  rw [add_mul, div_mul_cancel₀ _ hhR.ne', one_mul] at hup
  refine ⟨by omega, ?_, ?_⟩ <;> push_cast <;> nlinarith

/-- The union over all possible grid rejection times leaves a vanishing
quadratic mesh exception. -/
theorem native_maximum_mesh_exception {a T : ℝ} (ha : 0 ≤ a) {h : ℝ≥0} {n : ℕ}
    (hnT : (n : ℝ)*(h : ℝ) ≤ T) (hh1 : (h : ℝ) ≤ 1) :
    (2*a*(h : ℝ)^3)*((n : ℝ)+1) ≤ (2*a*(T+1))*(h : ℝ)^2 := by
  have hc : 0 ≤ 2*a*(h : ℝ)^2 := by positivity
  have hb := mul_le_mul_of_nonneg_left (show ((n : ℝ)+1)*(h : ℝ) ≤ T+1 by nlinarith) hc
  nlinarith [hb]

end SwingRepair
