import PLAStochastic.Swing.Repair.CycleCount
import PLAStochastic.Affine.Sampled.Lifetime

/-!
# Exact deterministic connection between repair spans and sampled anchored lifetimes

The repair parameter is the final error budget; its prefix cone already uses
half that budget. The existing firstRepairSpan adds one to the zero-based
rejected increment index, giving the rejected sample index.
-/

noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter
open scoped NNReal ENNReal Topology

namespace SwingRepair

theorem unitPrefix_nonempty_iff_anchoredResiduals (y : ℕ → ℝ) (hy : y 0 = 0)
    {E : ℝ} (hE : 0 ≤ E) (N : ℕ) :
    (prefixCone (fun n => (n : ℝ)) y 0 N E).Nonempty ↔
      ∃ a : ℝ, ∀ k ≤ N, |y k - a * (k : ℝ)| ≤ E / 2 := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun k hk => ?_⟩
    by_cases hk₀ : k = 0
    · subst k
      simp only [hy, Nat.cast_zero, mul_zero, sub_self, abs_zero]
      positivity
    · have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero hk₀)
      have hb := ha k (Finset.mem_Icc.mpr ⟨by omega, hk⟩)
      simp only [Set.mem_Icc, Nat.cast_zero] at hb
      have h := (sample_error_iff_bounds hkpos).mpr hb
      simpa only [hy, Nat.cast_zero, sub_zero, zero_add] using h
  · rintro ⟨a, ha⟩
    refine ⟨a, fun k hk => ?_⟩
    have hk' := Finset.mem_Icc.mp hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    simp only [Set.mem_Icc, Nat.cast_zero]
    apply (sample_error_iff_bounds hkpos).mp
    simpa only [hy, Nat.cast_zero, sub_zero, zero_add] using ha k hk'.2

theorem finiteMesh_error_at_grid_iff (f : C(ℝ, ℝ)) {h : ℝ} (hh : 0 < h) (N : ℕ) (ε : ℝ) :
    finiteMeshAnchoredError f ((N : ℝ) * h) h ≤ ε ↔
      ∃ a : ℝ, ∀ k ≤ N, |f ((k : ℝ) * h) - a * ((k : ℝ) * h)| ≤ ε := by
  have hfloor : ⌊((N : ℝ) * h) / h⌋₊ = N := by
    rw [mul_div_cancel_right₀ _ hh.ne', Nat.floor_natCast]
  rw [finiteMeshAnchoredError_le_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun k hk => ?_⟩
    exact ha ⟨k, by simpa only [hfloor] using Nat.lt_succ_of_le hk⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, fun i => ?_⟩
    exact ha i ((Nat.le_of_lt_succ i.isLt).trans hfloor.le)

/-- Time and amplitude rescaling preserve the actual half-budget cone exactly. -/
theorem prefixCone_rescaledMesh_nonempty_iff (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    {h c ε : ℝ} (hh : 0 < h) (hc : 0 < c) (hε : 0 ≤ ε) (N : ℕ) :
    (prefixCone (fun n => (n : ℝ)) (fun n => f ((n : ℝ) * h) / c)
      0 N (2 * ε / c)).Nonempty ↔ finiteMeshAnchoredError f ((N : ℝ) * h) h ≤ ε := by
  rw [unitPrefix_nonempty_iff_anchoredResiduals _ (by simp [hf]) (by positivity),
    finiteMesh_error_at_grid_iff f hh N ε]
  have hbudget : (2 * ε / c) / 2 = ε / c := by ring
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a * c / h, fun k hk => ?_⟩
    have hs := ha k hk
    rw [hbudget] at hs
    have heq : f ((k : ℝ) * h) / c - a * k =
        (f ((k : ℝ) * h) - (a * c / h) * ((k : ℝ) * h)) / c := by
      field_simp [hh.ne', hc.ne']
    rw [heq, abs_div, abs_of_pos hc] at hs
    exact (div_le_div_iff_of_pos_right hc).mp hs
  · rintro ⟨a, ha⟩
    refine ⟨a * h / c, fun k hk => ?_⟩
    rw [hbudget]
    have heq : f ((k : ℝ) * h) / c - (a * h / c) * k =
        (f ((k : ℝ) * h) - a * ((k : ℝ) * h)) / c := by ring
    rw [heq, abs_div, abs_of_pos hc]
    exact (div_le_div_iff_of_pos_right hc).mpr (ha k hk)

/-- Finite sampled infeasibility forces the original extended rejection index to be finite. -/
theorem firstRepairReject_ne_top_of_meshLifetime_ne_top {Ω : Type*}
    (X : ℕ → Ω → ℝ) (ω : Ω) (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    (h : ℝ≥0) (hh : h ≠ 0) {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε)
    (hsamples : ∀ n, cumulativeSamples X n ω = f ((n : ℝ) * h) / c)
    (hfinite : finiteMeshAnchoredLifetime f h ε ≠ ∞) :
    firstRepairReject X (2 * ε / c) ω ≠ ⊤ := by
  have hp : 0 < (h : ℝ) := by exact_mod_cast (pos_of_ne_zero hh)
  have hy : (fun n => cumulativeSamples X n ω) = (fun n : ℕ => f ((n : ℝ) * h) / c) :=
    funext hsamples
  intro ht
  have hnever := (firstRepairReject_eq_top_iff X (2 * ε / c) ω).mp ht
  have hcone (n : ℕ) :
      (prefixCone (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω) 0 n (2 * ε / c)).Nonempty := by
    cases n with
    | zero => exact prefixCone_self_nonempty _ _ _ _
    | succ n => simpa only [repairRejected, not_not] using hnever n
  apply hfinite
  rw [finiteMeshAnchoredLifetime_eq_iInf f h hh ε]
  apply le_antisymm le_top
  apply le_iInf
  intro n
  have hn := hcone n
  rw [hy, prefixCone_rescaledMesh_nonempty_iff f hf hp hc hε n] at hn
  simp only [NNReal.coe_natCast, if_neg (not_lt_of_ge hn), le_refl]

/-- The sampled lifetime is exactly mesh width times the actual rejected sample index.
The original WithTop rejection must be finite; no stopping-time claim is made after defaulting. -/
theorem finiteMeshLifetime_eq_mul_firstRepairSpan {Ω : Type*}
    (X : ℕ → Ω → ℝ) (ω : Ω) (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    (h : ℝ≥0) (hh : h ≠ 0) {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε)
    (hsamples : ∀ n, cumulativeSamples X n ω = f ((n : ℝ) * h) / c)
    (hfinite : firstRepairReject X (2 * ε / c) ω ≠ ⊤) :
    finiteMeshAnchoredLifetime f h ε =
      (h : ℝ≥0∞) * (firstRepairSpan X (2 * ε / c) ω : ℝ≥0∞) := by
  have hp : 0 < (h : ℝ) := by exact_mod_cast (pos_of_ne_zero hh)
  have hy : (fun n => cumulativeSamples X n ω) = (fun n : ℕ => f ((n : ℝ) * h) / c) :=
    funext hsamples
  let J := firstRepairSpan X (2 * ε / c) ω
  have hfit (n : ℕ) : finiteMeshAnchoredError f ((n : ℝ) * h) h ≤ ε ↔ n < J := by
    have hn := prefixCone_iff_lt_firstRepairSpan X (2 * ε / c) ω hfinite n
    rw [hy, prefixCone_rescaledMesh_nonempty_iff f hf hp hc hε n] at hn
    exact hn
  have hfail (n : ℕ) : ε < finiteMeshAnchoredError f ((n : ℝ≥0) * h) h ↔ J ≤ n := by
    simpa only [NNReal.coe_natCast, not_le, not_lt] using not_congr (hfit n)
  rw [finiteMeshAnchoredLifetime_eq_iInf f h hh ε]
  apply le_antisymm
  · apply (iInf_le _ J).trans
    rw [if_pos ((hfail J).mpr le_rfl)]
    simp only [ENNReal.coe_mul, ENNReal.coe_natCast, mul_comm, le_refl, J]
  · apply le_iInf
    intro n
    split_ifs with hn
    · have hJn := (hfail n).mp hn
      simp only [ENNReal.coe_mul, ENNReal.coe_natCast]
      rw [mul_comm (n : ℝ≥0∞) (h : ℝ≥0∞)]
      gcongr
    · exact le_top

end SwingRepair
