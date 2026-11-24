import PLAStochastic.Swing.Entrance.Grid.Cut
import PLAStochastic.Swing.DenseSampling.Segments.ShrinkingConeSlope
import PLAStochastic.Swing.Repair.SpanLifetimeLaw

/-!
# The rescaled grid path of the exact Brownian coupling

Under the exact grid coupling `X_E = normalizedMeshIncrement B h_E` with `h_E = E^{-2}`
(`gaussianBudgetMesh`), the anchored sample path is `y_n = E f(n h_E)` for the continuous path
`f = processPath B ω`. This file records the deterministic dictionary between the entrance cone of
`y` at tolerance `E` and the sampled cone of `f` on the mesh `h_E` at tolerance `1`:

* `E · slopeLower n y_n 0 y_0 E = slopeLower (n h) (f (n h)) 0 0 1`, and likewise for the upper
  bound, so `E a_n` and `E b_n` are the sampled lower and upper slopes of `f`;
* the cone of `y` is nonempty at `n` iff some slope fits `f` within `1` at `h, 2h, …, nh`;
* the native prefix feasibility of `f` on the mesh and of `y` on the unit grid are the same cone
  condition.
-/

open MeasureTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology

namespace SwingRepair

noncomputable section

/-- The rescaled grid path `y_n = E f(n h_E)` with `h_E = E^{-2}`. -/
def entranceGridPath (f : ℝ → ℝ) (E : ℝ≥0) (n : ℕ) : ℝ :=
  (E : ℝ) * f ((n : ℝ) * (gaussianBudgetMesh E : ℝ))

theorem coe_gaussianBudgetMesh (E : ℝ≥0) :
    (gaussianBudgetMesh E : ℝ) = ((E : ℝ) ^ 2)⁻¹ := by
  simp [gaussianBudgetMesh, inv_pow]

theorem gaussianBudgetMesh_pos {E : ℝ≥0} (hE : E ≠ 0) : 0 < (gaussianBudgetMesh E : ℝ) := by
  rw [coe_gaussianBudgetMesh]
  have : (0 : ℝ) < E := by exact_mod_cast pos_iff_ne_zero.mpr hE
  positivity

theorem sq_mul_gaussianBudgetMesh {E : ℝ≥0} (hE : E ≠ 0) :
    (E : ℝ) ^ 2 * (gaussianBudgetMesh E : ℝ) = 1 := by
  rw [coe_gaussianBudgetMesh]
  have : (E : ℝ) ≠ 0 := by exact_mod_cast hE
  field_simp

theorem entranceGridPath_zero (f : ℝ → ℝ) (hf : f 0 = 0) (E : ℝ≥0) :
    entranceGridPath f E 0 = 0 := by
  simp [entranceGridPath, hf]

/-- The exact coupling: the normalized Brownian mesh increments sum to the rescaled grid path. -/
theorem cumulativeSamples_normalizedMesh_eq_gridPath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (E : ℝ≥0) (ω : Ω) (hc : Continuous (B · ω)) (hz : B 0 ω = 0) (n : ℕ) :
    cumulativeSamples (normalizedMeshIncrement B (gaussianBudgetMesh E)) n ω =
      entranceGridPath (processPath B ω) E n := by
  rw [cumulativeSamples_normalizedMesh B _ ω hc hz n, sqrt_gaussianBudgetMesh, entranceGridPath,
    div_inv_eq_mul, mul_comm]

theorem entrancePath_normalizedMesh {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (E : ℝ≥0) (ω : Ω)
    (hc : Continuous (B · ω)) (hz : B 0 ω = 0) :
    entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω =
      entranceGridPath (processPath B ω) E :=
  funext (cumulativeSamples_normalizedMesh_eq_gridPath B E ω hc hz)

variable {f : ℝ → ℝ} {E : ℝ≥0}

/-! ## Scaling of the sample bounds -/

theorem mul_slopeLower_gridPath (hf : f 0 = 0) (hE : E ≠ 0) {i : ℕ} (hi : 1 ≤ i) :
    (E : ℝ) * slopeLower (i : ℝ) (entranceGridPath f E i) 0 (entranceGridPath f E 0) E =
      slopeLower ((i : ℝ) * gaussianBudgetMesh E) (f ((i : ℝ) * gaussianBudgetMesh E)) 0 0 1 := by
  have hE' : (E : ℝ) ≠ 0 := by exact_mod_cast hE
  have hi' : (i : ℝ) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
  rw [entranceGridPath_zero f hf]
  unfold slopeLower entranceGridPath
  rw [coe_gaussianBudgetMesh]
  generalize f ((i : ℝ) * ((E : ℝ) ^ 2)⁻¹) = u
  simp only [sub_zero]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
  ring

theorem mul_slopeUpper_gridPath (hf : f 0 = 0) (hE : E ≠ 0) {i : ℕ} (hi : 1 ≤ i) :
    (E : ℝ) * slopeUpper (i : ℝ) (entranceGridPath f E i) 0 (entranceGridPath f E 0) E =
      slopeUpper ((i : ℝ) * gaussianBudgetMesh E) (f ((i : ℝ) * gaussianBudgetMesh E)) 0 0 1 := by
  have hE' : (E : ℝ) ≠ 0 := by exact_mod_cast hE
  have hi' : (i : ℝ) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
  rw [entranceGridPath_zero f hf]
  unfold slopeUpper entranceGridPath
  rw [coe_gaussianBudgetMesh]
  generalize f ((i : ℝ) * ((E : ℝ) ^ 2)⁻¹) = u
  simp only [sub_zero]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
  ring

theorem mul_entranceLower_le_iff (hf : f 0 = 0) (hE : E ≠ 0) {n : ℕ} (hn : 1 ≤ n) {c : ℝ} :
    (E : ℝ) * entranceLower (entranceGridPath f E) E n ≤ c ↔
      ∀ k, 1 ≤ k → k ≤ n →
        slopeLower ((k : ℝ) * gaussianBudgetMesh E) (f ((k : ℝ) * gaussianBudgetMesh E)) 0 0 1 ≤
          c := by
  have hE' : (0 : ℝ) < E := by exact_mod_cast pos_iff_ne_zero.mpr hE
  rw [← le_div_iff₀' hE', entranceLower_le_iff _ _ hn]
  refine forall_congr' fun k => imp_congr_right fun hk1 => imp_congr_right fun _ => ?_
  rw [le_div_iff₀' hE', mul_slopeLower_gridPath hf hE hk1]

theorem le_mul_entranceUpper_iff (hf : f 0 = 0) (hE : E ≠ 0) {n : ℕ} (hn : 1 ≤ n) {c : ℝ} :
    c ≤ (E : ℝ) * entranceUpper (entranceGridPath f E) E n ↔
      ∀ k, 1 ≤ k → k ≤ n →
        c ≤ slopeUpper ((k : ℝ) * gaussianBudgetMesh E)
          (f ((k : ℝ) * gaussianBudgetMesh E)) 0 0 1 := by
  have hE' : (0 : ℝ) < E := by exact_mod_cast pos_iff_ne_zero.mpr hE
  rw [← div_le_iff₀' hE', le_entranceUpper_iff _ _ hn]
  refine forall_congr' fun k => imp_congr_right fun hk1 => imp_congr_right fun _ => ?_
  rw [div_le_iff₀' hE', mul_slopeUpper_gridPath hf hE hk1]

theorem exists_mul_entranceLower_eq (hf : f 0 = 0) (hE : E ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    ∃ k, 1 ≤ k ∧ k ≤ n ∧ (E : ℝ) * entranceLower (entranceGridPath f E) E n =
      slopeLower ((k : ℝ) * gaussianBudgetMesh E) (f ((k : ℝ) * gaussianBudgetMesh E)) 0 0 1 := by
  obtain ⟨k, hk1, hkn, he⟩ := exists_entranceLower_eq (entranceGridPath f E) E hn
  exact ⟨k, hk1, hkn, by rw [he, mul_slopeLower_gridPath hf hE hk1]⟩

theorem exists_mul_entranceUpper_eq (hf : f 0 = 0) (hE : E ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    ∃ k, 1 ≤ k ∧ k ≤ n ∧ (E : ℝ) * entranceUpper (entranceGridPath f E) E n =
      slopeUpper ((k : ℝ) * gaussianBudgetMesh E) (f ((k : ℝ) * gaussianBudgetMesh E)) 0 0 1 := by
  obtain ⟨k, hk1, hkn, he⟩ := exists_entranceUpper_eq (entranceGridPath f E) E hn
  exact ⟨k, hk1, hkn, by rw [he, mul_slopeUpper_gridPath hf hE hk1]⟩

/-! ## Cone feasibility on the two scales -/

/-- A sampled residual bound in terms of the two sample slope bounds. -/
theorem abs_sub_mul_le_one_iff {t v m : ℝ} (ht : 0 < t) :
    |v - m * t| ≤ 1 ↔ slopeLower t v 0 0 1 ≤ m ∧ m ≤ slopeUpper t v 0 0 1 := by
  have h := sample_error_iff_bounds (sampleTime := t) (sampleValue := v) (anchorTime := 0)
    (anchorValue := 0) (ε := 1) (m := m) ht
  simpa only [sub_zero, zero_add] using h

/-- Every slope in the entrance cone of `y` at index `n`, multiplied by `E`, fits `f` within one at
the first `n` mesh points. -/
theorem gridFit_of_mem_cone (hf : f 0 = 0) (hE : E ≠ 0) {n : ℕ} (hn : 1 ≤ n) {m : ℝ}
    (hl : entranceLower (entranceGridPath f E) E n ≤ m)
    (hu : m ≤ entranceUpper (entranceGridPath f E) E n) :
    ∀ k, 1 ≤ k → k ≤ n →
      |f ((k : ℝ) * gaussianBudgetMesh E) - (E * m) * ((k : ℝ) * gaussianBudgetMesh E)| ≤ 1 := by
  have hE' : (0 : ℝ) < E := by exact_mod_cast pos_iff_ne_zero.mpr hE
  intro k hk1 hkn
  have hk : 0 < (k : ℝ) * gaussianBudgetMesh E :=
    mul_pos (by exact_mod_cast hk1) (gaussianBudgetMesh_pos hE)
  apply (abs_sub_mul_le_one_iff hk).mpr
  constructor
  · exact (mul_entranceLower_le_iff hf hE hn).mp (mul_le_mul_of_nonneg_left hl hE'.le) k hk1 hkn
  · exact (le_mul_entranceUpper_iff hf hE hn).mp (mul_le_mul_of_nonneg_left hu hE'.le) k hk1 hkn

/-- The entrance cone of `y = E f(· h_E)` is nonempty at `n` iff a line through the origin fits
`f` within one at the first `n` mesh points. -/
theorem entranceGridPath_cone_iff (hf : f 0 = 0) (hE : E ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    entranceLower (entranceGridPath f E) E n ≤ entranceUpper (entranceGridPath f E) E n ↔
      ∃ m : ℝ, ∀ k, 1 ≤ k → k ≤ n →
        |f ((k : ℝ) * gaussianBudgetMesh E) - m * ((k : ℝ) * gaussianBudgetMesh E)| ≤ 1 := by
  have hE' : (0 : ℝ) < E := by exact_mod_cast pos_iff_ne_zero.mpr hE
  constructor
  · intro hc
    exact ⟨_, gridFit_of_mem_cone hf hE hn le_rfl hc⟩
  · rintro ⟨m, hm⟩
    have hb : ∀ k, 1 ≤ k → k ≤ n →
        slopeLower ((k : ℝ) * gaussianBudgetMesh E) (f ((k : ℝ) * gaussianBudgetMesh E)) 0 0 1 ≤ m ∧
        m ≤ slopeUpper ((k : ℝ) * gaussianBudgetMesh E)
          (f ((k : ℝ) * gaussianBudgetMesh E)) 0 0 1 := fun k hk1 hkn =>
      (abs_sub_mul_le_one_iff (mul_pos (by exact_mod_cast hk1) (gaussianBudgetMesh_pos hE))).mp
        (hm k hk1 hkn)
    have h1 := (mul_entranceLower_le_iff hf hE hn).mpr (fun k hk1 hkn => (hb k hk1 hkn).1)
    have h2 := (le_mul_entranceUpper_iff hf hE hn).mpr (fun k hk1 hkn => (hb k hk1 hkn).2)
    exact le_of_mul_le_mul_left (h1.trans h2) hE'

/-- The native prefix of `f` on the mesh `h`, written as a sampled fit through the origin. -/
theorem nativePrefixFeasible_mesh_iff (hf : f 0 = 0) (h : ℝ) (j : ℕ) :
    nativePrefixFeasible (fun n => (n : ℝ) * h) (fun n => f ((n : ℝ) * h)) 1 0 j (f 0) ↔
      ∃ m : ℝ, ∀ k, 1 ≤ k → k ≤ j → |f ((k : ℝ) * h) - m * ((k : ℝ) * h)| ≤ 1 := by
  unfold nativePrefixFeasible feasibleSlope
  simp only [Nat.cast_zero, zero_mul, hf, sub_zero, zero_add, Finset.mem_Icc]
  exact exists_congr fun m => ⟨fun h k hk1 hkj => h k ⟨hk1, hkj⟩, fun h k hk => h k hk.1 hk.2⟩

/-- The native prefix of `y` on the unit grid is the entrance cone condition. -/
theorem nativePrefixFeasible_unit_iff (y : ℕ → ℝ) (E : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    nativePrefixFeasible (fun n => (n : ℝ)) y E 0 j (y 0) ↔
      entranceLower y E j ≤ entranceUpper y E j := by
  have hne : (Finset.Icc 1 j).Nonempty := Finset.nonempty_Icc.mpr hj
  have ht : ∀ i ∈ Finset.Icc 1 j, (0 : ℝ) < (i : ℝ) := fun i hi => by
    exact_mod_cast (Finset.mem_Icc.mp hi).1
  have h := nativeCone_nonempty_iff (Finset.Icc 1 j) hne (fun n => (n : ℝ)) y 0 (y 0) E ht
  rw [entranceLower, entranceUpper, dif_pos hne, dif_pos hne, ← h]
  unfold nativePrefixFeasible
  simp only [Nat.cast_zero, zero_add]

theorem nativePrefixFeasible_unit_zero (y : ℕ → ℝ) (E : ℝ) :
    nativePrefixFeasible (fun n => (n : ℝ)) y E 0 0 (y 0) := by
  refine ⟨0, fun i hi => ?_⟩
  simp at hi

end

end SwingRepair
