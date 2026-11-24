import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith

namespace SwingRepair

noncomputable section

/-- The lower slope bound contributed by one sample. -/
def slopeLower (sampleTime sampleValue anchorTime anchorValue tolerance : ℝ) : ℝ :=
  (sampleValue - anchorValue - tolerance) / (sampleTime - anchorTime)

/-- The upper slope bound contributed by one sample. -/
def slopeUpper (sampleTime sampleValue anchorTime anchorValue tolerance : ℝ) : ℝ :=
  (sampleValue - anchorValue + tolerance) / (sampleTime - anchorTime)

/-- A slope is feasible when its anchored line meets every finite sample constraint. -/
def feasibleSlope {ι : Type*} (samples : Finset ι) (t y : ι → ℝ)
    (t₀ y₀ ε m : ℝ) : Prop :=
  ∀ i ∈ samples, |y i - (y₀ + m * (t i - t₀))| ≤ ε

/-- Positive elapsed time converts a sample error constraint to an interval of slopes. -/
theorem sample_error_iff_bounds {sampleTime sampleValue anchorTime anchorValue ε m : ℝ}
    (ht : anchorTime < sampleTime) :
    |sampleValue - (anchorValue + m * (sampleTime - anchorTime))| ≤ ε ↔
      slopeLower sampleTime sampleValue anchorTime anchorValue ε ≤ m ∧
        m ≤ slopeUpper sampleTime sampleValue anchorTime anchorValue ε := by
  dsimp [slopeLower, slopeUpper]
  rw [abs_le, div_le_iff₀ (sub_pos.mpr ht), le_div_iff₀ (sub_pos.mpr ht)]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The finite cone is exactly the set of slopes meeting all sample error constraints. -/
theorem feasibleSlope_iff_bounds {ι : Type*} (samples : Finset ι) (t y : ι → ℝ)
    (t₀ y₀ ε m : ℝ) (ht : ∀ i ∈ samples, t₀ < t i) :
    feasibleSlope samples t y t₀ y₀ ε m ↔
      ∀ i ∈ samples,
        slopeLower (t i) (y i) t₀ y₀ ε ≤ m ∧
          m ≤ slopeUpper (t i) (y i) t₀ y₀ ε := by
  constructor
  · intro h i hi
    exact (sample_error_iff_bounds (ht i hi)).mp (h i hi)
  · intro h i hi
    exact (sample_error_iff_bounds (ht i hi)).mpr (h i hi)

/-- Removing constraints preserves the feasibility of a slope. -/
theorem feasibleSlope_of_subset {ι : Type*} {samples larger : Finset ι}
    {t y : ι → ℝ} {t₀ y₀ ε m : ℝ} (hsub : samples ⊆ larger)
    (h : feasibleSlope larger t y t₀ y₀ ε m) :
    feasibleSlope samples t y t₀ y₀ ε m := by
  intro i hi
  exact h i (hsub hi)

/-- Inserting a sample adds exactly its own error constraint. -/
theorem feasibleSlope_insert {ι : Type*} [DecidableEq ι]
    (samples : Finset ι) (i : ι) (t y : ι → ℝ) (t₀ y₀ ε m : ℝ) :
    feasibleSlope (insert i samples) t y t₀ y₀ ε m ↔
      feasibleSlope samples t y t₀ y₀ ε m ∧
        |y i - (y₀ + m * (t i - t₀))| ≤ ε := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (Finset.mem_insert_of_mem hj),
      h i (Finset.mem_insert_self i samples)⟩
  · rintro ⟨h, hi⟩ j hj
    rcases Finset.mem_insert.mp hj with hji | hj
    · subst j
      exact hi
    · exact h j hj

/-- The new feasible set is the intersection of the old set and one slope interval. -/
theorem feasibleSlope_insert_iff_bounds {ι : Type*} [DecidableEq ι]
    (samples : Finset ι) (i : ι) (t y : ι → ℝ) (t₀ y₀ ε m : ℝ)
    (ht : t₀ < t i) :
    feasibleSlope (insert i samples) t y t₀ y₀ ε m ↔
      feasibleSlope samples t y t₀ y₀ ε m ∧
        m ∈ Set.Icc (slopeLower (t i) (y i) t₀ y₀ ε)
          (slopeUpper (t i) (y i) t₀ y₀ ε) := by
  rw [feasibleSlope_insert, sample_error_iff_bounds ht]
  rfl

/-- The set-valued version also handles the initially unbounded cone. -/
theorem feasibleSlopes_insert_eq_inter {ι : Type*} [DecidableEq ι]
    (samples : Finset ι) (i : ι) (t y : ι → ℝ) (t₀ y₀ ε : ℝ)
    (ht : t₀ < t i) :
    {m | feasibleSlope (insert i samples) t y t₀ y₀ ε m} =
      {m | feasibleSlope samples t y t₀ y₀ ε m} ∩
        Set.Icc (slopeLower (t i) (y i) t₀ y₀ ε)
          (slopeUpper (t i) (y i) t₀ y₀ ε) := by
  ext m
  exact feasibleSlope_insert_iff_bounds samples i t y t₀ y₀ ε m ht

/-- The empty prefix imposes no constraint on a slope. -/
theorem feasibleSlopes_empty {ι : Type*} (t y : ι → ℝ) (t₀ y₀ ε : ℝ) :
    {m | feasibleSlope ∅ t y t₀ y₀ ε m} = Set.univ := by
  ext m
  simp [feasibleSlope]

/-- Intersecting two closed intervals updates only their two endpoints. -/
theorem interval_update_iff {lower upper newLower newUpper m : ℝ} :
    m ∈ Set.Icc (max lower newLower) (min upper newUpper) ↔
      m ∈ Set.Icc lower upper ∧ m ∈ Set.Icc newLower newUpper := by
  simp only [Set.mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨hl, hnl⟩, hu, hnu⟩
    exact ⟨⟨hl, hu⟩, hnl, hnu⟩
  · rintro ⟨⟨hl, hu⟩, hnl, hnu⟩
    exact ⟨⟨hl, hnl⟩, hu, hnu⟩

/-- If two endpoints represent the previous cone, max/min represent its exact update. -/
theorem updated_bounds_iff_feasibleSlope {ι : Type*} [DecidableEq ι]
    (samples : Finset ι) (i : ι) (t y : ι → ℝ) (t₀ y₀ ε lower upper m : ℝ)
    (ht : t₀ < t i)
    (hcone : ∀ a, a ∈ Set.Icc lower upper ↔ feasibleSlope samples t y t₀ y₀ ε a) :
    m ∈ Set.Icc (max lower (slopeLower (t i) (y i) t₀ y₀ ε))
        (min upper (slopeUpper (t i) (y i) t₀ y₀ ε)) ↔
      feasibleSlope (insert i samples) t y t₀ y₀ ε m := by
  rw [interval_update_iff, hcone m]
  exact (feasibleSlope_insert_iff_bounds samples i t y t₀ y₀ ε m ht).symm

/-- A nonempty updated interval provides a slope feasible for every updated sample. -/
theorem exists_feasibleSlope_of_updated_bounds {ι : Type*} [DecidableEq ι]
    (samples : Finset ι) (i : ι) (t y : ι → ℝ) (t₀ y₀ ε lower upper : ℝ)
    (ht : t₀ < t i)
    (hcone : ∀ a, a ∈ Set.Icc lower upper ↔ feasibleSlope samples t y t₀ y₀ ε a)
    (hne : max lower (slopeLower (t i) (y i) t₀ y₀ ε) ≤
      min upper (slopeUpper (t i) (y i) t₀ y₀ ε)) :
    ∃ m, feasibleSlope (insert i samples) t y t₀ y₀ ε m := by
  refine ⟨max lower (slopeLower (t i) (y i) t₀ y₀ ε), ?_⟩
  apply (updated_bounds_iff_feasibleSlope samples i t y t₀ y₀ ε lower upper _ ht hcone).mp
  exact ⟨le_rfl, hne⟩

/-- The endpoint comparison is an exact feasibility test, including a singleton cone. -/
theorem exists_feasibleSlope_iff_updated_bounds {ι : Type*} [DecidableEq ι]
    (samples : Finset ι) (i : ι) (t y : ι → ℝ) (t₀ y₀ ε lower upper : ℝ)
    (ht : t₀ < t i)
    (hcone : ∀ a, a ∈ Set.Icc lower upper ↔ feasibleSlope samples t y t₀ y₀ ε a) :
    (∃ m, feasibleSlope (insert i samples) t y t₀ y₀ ε m) ↔
      max lower (slopeLower (t i) (y i) t₀ y₀ ε) ≤
        min upper (slopeUpper (t i) (y i) t₀ y₀ ε) := by
  constructor
  · rintro ⟨m, hm⟩
    have hb :=
      (updated_bounds_iff_feasibleSlope samples i t y t₀ y₀ ε lower upper m ht hcone).mpr hm
    exact hb.1.trans hb.2
  · exact exists_feasibleSlope_of_updated_bounds samples i t y t₀ y₀ ε lower upper ht hcone

/-- Strict reversal of the updated endpoints is exactly the rejection condition. -/
theorem no_feasibleSlope_iff_updated_bounds {ι : Type*} [DecidableEq ι]
    (samples : Finset ι) (i : ι) (t y : ι → ℝ) (t₀ y₀ ε lower upper : ℝ)
    (ht : t₀ < t i)
    (hcone : ∀ a, a ∈ Set.Icc lower upper ↔ feasibleSlope samples t y t₀ y₀ ε a) :
    (¬ ∃ m, feasibleSlope (insert i samples) t y t₀ y₀ ε m) ↔
      min upper (slopeUpper (t i) (y i) t₀ y₀ ε) <
        max lower (slopeLower (t i) (y i) t₀ y₀ ε) := by
  rw [exists_feasibleSlope_iff_updated_bounds samples i t y t₀ y₀ ε lower upper ht hcone]
  exact not_le

/-- A first sample cannot reject when the tolerance is nonnegative. -/
theorem feasibleSlope_singleton {ι : Type*} (i : ι) (t y : ι → ℝ) (t₀ y₀ ε : ℝ)
    (ht : t₀ < t i) (hε : 0 ≤ ε) :
    feasibleSlope {i} t y t₀ y₀ ε ((y i - y₀) / (t i - t₀)) := by
  intro j hj
  have hji : j = i := Finset.mem_singleton.mp hj
  subst j
  have hdt : t i - t₀ ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  rw [div_mul_cancel₀ _ hdt]
  have hz : y i - (y₀ + (y i - y₀)) = 0 := by linarith
  rw [hz, abs_zero]
  exact hε

end

end SwingRepair
