import PLAStochastic.Swing.DenseSampling.CarriedPrefix.BoundedSurvival

/-! # Joint measurability of the carried bounded-prefix event -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- Adding a deterministic slope cap still leaves a finite closed interval
intersection, so no existential measurability assumption is needed. -/
theorem bounded_nativeCone_nonempty_iff {ι : Type*} (samples : Finset ι)
    (hne : samples.Nonempty) (t y : ι → ℝ) (a q ε M : ℝ)
    (ht : ∀ i ∈ samples, a < t i) :
    (∃ m : ℝ, |m| ≤ M ∧ feasibleSlope samples t y a q ε m) ↔
      max (-M) (nativeConeLower samples hne t y a q ε) ≤
        min M (nativeConeUpper samples hne t y a q ε) := by
  constructor
  · rintro ⟨m, hm, hf⟩
    have hc := (nativeCone_mem_iff samples hne t y a q ε m ht).mpr hf
    exact (max_le (abs_le.mp hm).1 hc.1).trans (le_min (abs_le.mp hm).2 hc.2)
  · intro hc
    refine ⟨max (-M) (nativeConeLower samples hne t y a q ε), ?_, ?_⟩
    · exact abs_le.mpr ⟨le_max_left _ _, hc.trans (min_le_left _ _)⟩
    · exact (nativeCone_mem_iff samples hne t y a q ε _ ht).mp
        ⟨le_max_right _ _, hc.trans (min_le_right _ _)⟩

theorem nativeBoundedCarriedFit_iff_feasible (D : ℕ → ℝ) (w ε M h : ℝ) (N : ℕ) :
    nativeBoundedCarriedFit D w ε M h N ↔ ∃ m : ℝ, |m| ≤ M ∧
      feasibleSlope (Finset.range (N + 1)) (fun j => ((j : ℝ) + 1) * h)
        (fun j => w + D j - ε) 0 0 ε m := by
  constructor
  · rintro ⟨m, hm, hf⟩
    refine ⟨m, hm, fun j hj => ?_⟩
    have hc := hf j (by have h := Finset.mem_range.mp hj; omega)
    dsimp only
    rw [abs_le]
    constructor <;> nlinarith [hc.1, hc.2]
  · rintro ⟨m, hm, hf⟩
    refine ⟨m, hm, fun j hj => ?_⟩
    have hc := abs_le.mp (hf j (Finset.mem_range.mpr (by omega)))
    constructor <;> nlinarith [hc.1, hc.2]

/-- Joint measurability allows the carry to be selected from the observed
history. Future Brownian data remain separate coordinates. -/
theorem measurableSet_nativeBoundedCarriedFit {Ω : Type*} [MeasurableSpace Ω]
    (D : ℕ → Ω → ℝ) {W : Ω → ℝ} (hW : Measurable W) (hD : ∀ j, Measurable (D j))
    (ε M : ℝ) {h : ℝ} (hh : 0 < h) (N : ℕ) :
    MeasurableSet {ω | nativeBoundedCarriedFit (fun j => D j ω) (W ω) ε M h N} := by
  let t (j : ℕ) := ((j : ℝ) + 1) * h
  let Y (j : ℕ) (ω : Ω) := W ω + D j ω - ε
  have hY (j : ℕ) : Measurable (Y j) := (hW.add (hD j)).sub_const ε
  have hne : (Finset.range (N + 1)).Nonempty := by simp
  have ht (j : ℕ) (_ : j ∈ Finset.range (N + 1)) : 0 < t j := mul_pos (by positivity) hh
  have hL := measurable_nativeConeLower (Finset.range (N + 1)) hne t Y 0 ε
    (measurable_const (a := (0 : ℝ))) (fun j _ => hY j)
  have hU := measurable_nativeConeUpper (Finset.range (N + 1)) hne t Y 0 ε
    (measurable_const (a := (0 : ℝ))) (fun j _ => hY j)
  have heq : {ω | nativeBoundedCarriedFit (fun j => D j ω) (W ω) ε M h N} =
      {ω | max (-M) (nativeConeLower (Finset.range (N + 1)) hne t (fun j => Y j ω) 0 0 ε) ≤
        min M (nativeConeUpper (Finset.range (N + 1)) hne t (fun j => Y j ω) 0 0 ε)} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [nativeBoundedCarriedFit_iff_feasible]
    exact bounded_nativeCone_nonempty_iff (Finset.range (N + 1)) hne t (fun j => Y j ω) 0 0 ε M ht
  rw [heq]
  exact measurableSet_le ((measurable_const (a := -M)).max hL) ((measurable_const (a := M)).min hU)

/-- The actual Brownian event is null measurable even when both the process
and the past-chosen carried value are only almost surely measurable. -/
theorem nullMeasurableSet_nativeBoundedCarriedFit_brownian {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {W : Ω → ℝ} (hW : AEMeasurable W μ) (ε M : ℝ) {h : ℝ≥0} (hh : 0 < h) (N : ℕ) :
    NullMeasurableSet {ω | nativeBoundedCarriedFit (fun j => B ((j : ℝ≥0) * h) ω)
      (W ω) ε M h N} μ := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hE := measurableSet_nativeBoundedCarriedFit
    (fun j (z : ℝ × (ℕ → ℝ)) => z.2 j) measurable_fst
    (fun j => (measurable_pi_apply j).comp measurable_snd) ε M hh' N
  have hm := hW.prodMk (aemeasurable_pi_lambda _ (fun j : ℕ => hB.aemeasurable ((j : ℝ≥0) * h)))
  exact hm.nullMeasurable hE

end SwingRepair
