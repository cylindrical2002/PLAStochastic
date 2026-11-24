import PLAStochastic.Swing.FirstSegment.Recording
import PLAStochastic.Swing.Repair.SpanLifetimeGeometry
import PLAStochastic.Affine.Pinch.CompletedStoppingTime

/-!
# Dense-mesh convergence of the actual first native recording

The first duration is read from the actual nativeStream output. The exact
rejected-grid lifetime differs from this last accepted recording by one mesh
width. The deterministic sampled-error approximation then gives pathwise
convergence, retaining the distinction between rejection and recording.
-/

noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology

namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem strictMono_mesh_times {h : ℝ} (hh : 0 < h) :
    StrictMono (fun n : ℕ => (n : ℝ) * h) := by
  intro i j hij
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) hh

/-- The native full-budget prefix is exactly the actual finite-grid fitting
problem. The initial sample is included through the proved origin condition. -/
theorem nativeGridPrefix_iff_finiteMeshError (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    {h ε : ℝ} (hh : 0 < h) (hε : 0 ≤ ε) (N : ℕ) :
    nativePrefixFeasible (fun n => (n : ℝ) * h) (fun n => f ((n : ℝ) * h))
      ε 0 N (f 0) ↔ finiteMeshAnchoredError f ((N : ℝ) * h) h ≤ ε := by
  rw [finiteMesh_error_at_grid_iff f hh N ε]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun k hk => ?_⟩
    by_cases hk0 : k = 0
    · subst k
      simpa only [Nat.cast_zero, zero_mul, hf, mul_zero, sub_zero, abs_zero] using hε
    · have hb := ha k (Finset.mem_Icc.mpr ⟨by omega, hk⟩)
      simpa only [Nat.cast_zero, zero_mul, hf, sub_zero, zero_add] using hb
  · rintro ⟨a, ha⟩
    refine ⟨a, fun k hk => ?_⟩
    simpa only [Nat.cast_zero, zero_mul, hf, sub_zero, zero_add] using ha k (Finset.mem_Icc.mp hk).2

/-- A finite actual grid lifetime supplies the genuine first rejected index. -/
theorem exists_nativeGrid_threshold (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    (h : ℝ≥0) (hh : h ≠ 0) {ε : ℝ} (hε : 0 ≤ ε)
    (hfinite : finiteMeshAnchoredLifetime f h ε ≠ ∞) :
    ∃ K : ℕ, 1 < K ∧ ∀ j,
      nativePrefixFeasible (fun n => (n : ℝ) * h) (fun n => f ((n : ℝ) * h))
        ε 0 j (f 0) ↔ j < K := by
  have hp : 0 < (h : ℝ) := by exact_mod_cast (pos_of_ne_zero hh)
  have hex : ∃ n : ℕ, ε < finiteMeshAnchoredError f ((n : ℝ) * h) h := by
    by_contra hn
    push Not at hn
    apply hfinite
    rw [finiteMeshAnchoredLifetime_eq_iInf f h hh ε]
    apply le_antisymm le_top
    apply le_iInf
    intro n
    simp only [NNReal.coe_natCast, if_neg (not_lt_of_ge (hn n)), le_refl]
  let K := Nat.find hex
  have hK : ε < finiteMeshAnchoredError f ((K : ℝ) * h) h := Nat.find_spec hex
  have hmono := finiteMeshAnchoredError_monotone_time f hp
  have hcone (j : ℕ) : nativePrefixFeasible (fun n => (n : ℝ) * h)
      (fun n => f ((n : ℝ) * h)) ε 0 j (f 0) ↔ j < K := by
    rw [nativeGridPrefix_iff_finiteMeshError f hf hp hε j]
    constructor
    · intro hj
      by_contra hjK
      have hKj : K ≤ j := le_of_not_gt hjK
      have he : finiteMeshAnchoredError f ((K : ℝ) * h) h ≤
          finiteMeshAnchoredError f ((j : ℝ) * h) h := by
        apply hmono
        gcongr
      exact hK.not_ge (he.trans hj)
    · intro hjK
      exact le_of_not_gt (Nat.find_min hex hjK)
  refine ⟨K, ?_, hcone⟩
  apply (hcone 1).mp
  exact nativePrefix_singleton _ _ (strictMono_mesh_times hp) hε 0 (f 0)

/-- Exact geometric identity: the first recorded endpoint precedes the first
rejected grid sample by exactly one mesh width. -/
theorem nativeFirstRecording_mesh_add_one (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    (h : ℝ≥0) (hh : h ≠ 0) {ε : ℝ} (hε : 0 ≤ ε)
    (hfinite : finiteMeshAnchoredLifetime f h ε ≠ ∞) :
    (h : ℝ) * ((nativeFirstRecording (fun n => (n : ℝ) * h)
      (fun n => f ((n : ℝ) * h)) ε : ℕ) + 1 : ℝ) =
      (finiteMeshAnchoredLifetime f h ε).toReal := by
  obtain ⟨K, hK, hcone⟩ := exists_nativeGrid_threshold f hf h hh hε hfinite
  have hp : 0 < (h : ℝ) := by exact_mod_cast (pos_of_ne_zero hh)
  have hrecord := nativeFirstRecording_eq_threshold (fun n => (n : ℝ) * h)
    (fun n => f ((n : ℝ) * h)) ε hK (by simpa only [Nat.cast_zero, zero_mul] using hcone)
  have hfail (j : ℕ) : ε < finiteMeshAnchoredError f ((j : ℝ≥0) * h) h ↔ K ≤ j := by
    simpa only [NNReal.coe_mul, NNReal.coe_natCast, not_le, not_lt] using
      not_congr ((nativeGridPrefix_iff_finiteMeshError f hf hp hε j).symm.trans (hcone j))
  have hlife : finiteMeshAnchoredLifetime f h ε = (h : ℝ≥0∞) * K := by
    rw [finiteMeshAnchoredLifetime_eq_iInf f h hh ε]
    apply le_antisymm
    · exact (iInf_le _ K).trans (by
        rw [if_pos ((hfail K).mpr le_rfl)]
        simp only [ENNReal.coe_mul, ENNReal.coe_natCast, mul_comm, le_refl])
    · apply le_iInf
      intro j
      split_ifs with hj
      · have hKj := (hfail j).mp hj
        simp only [ENNReal.coe_mul, ENNReal.coe_natCast]
        rw [mul_comm (j : ℝ≥0∞) (h : ℝ≥0∞)]
        gcongr
      · exact le_top
  rw [hrecord, hlife, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_natCast]
  rw [Nat.cast_sub (show 1 ≤ K by omega), Nat.cast_one]
  ring

/-- Along any positive vanishing meshes, the actual native first recording
converges pathwise to the original continuous anchored lifetime. -/
theorem tendsto_nativeFirstRecording_mesh (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    {ε : ℝ} (hε : 0 ≤ ε) (hfinite : anchoredLifetime f ε ≠ ∞)
    {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0} (hh : ∀ i, h i ≠ 0)
    (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    Tendsto (fun i => (h i : ℝ) * (nativeFirstRecording (fun n => (n : ℝ) * h i)
      (fun n => f ((n : ℝ) * h i)) ε : ℝ)) l (𝓝 (anchoredLifetime f ε).toReal) := by
  have hp (i : ι) : 0 < (h i : ℝ) := by exact_mod_cast (pos_of_ne_zero (hh i))
  have hlife := tendsto_finiteMeshAnchoredLifetime f ε hp hconv
  have hfin : ∀ᶠ i in l, finiteMeshAnchoredLifetime f (h i) ε ≠ ∞ :=
    (hlife.eventually_lt_const (lt_top_iff_ne_top.mpr hfinite)).mono (fun _ hi => hi.ne)
  have hreal : Tendsto (fun i => (finiteMeshAnchoredLifetime f (h i) ε).toReal)
      l (𝓝 (anchoredLifetime f ε).toReal) :=
    (ENNReal.continuousAt_toReal hfinite).tendsto.comp hlife
  have hdiff := hreal.sub hconv
  simp only [sub_zero] at hdiff
  apply hdiff.congr'
  filter_upwards [hfin] with i hi
  have heq := nativeFirstRecording_mesh_add_one f hf (h i) (hh i) hε hi
  linarith

/-- The convergence concerns each fixed Brownian path on a single full-measure
set, rather than only a weak or mean limit. -/
theorem nativeFirstRecording_mesh_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0}
    (hh : ∀ i, h i ≠ 0) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun i => (h i : ℝ) *
      (nativeFirstRecording (fun n => (n : ℝ) * h i)
        (fun n => B ((n : ℝ≥0) * h i) ω) ε : ℝ)) l
      (𝓝 (anchoredProcessLifetime B ε ω).toReal) := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero,
    anchoredProcessLifetime_tolerance_ae_ne_top hB hε] with ω hc hz hf
  have hzero : processPath B ω 0 = 0 := (processPath_apply_of_continuous hc 0).trans hz
  have ht := tendsto_nativeFirstRecording_mesh (processPath B ω) hzero hε.le hf hh hconv
  change Tendsto _ l (𝓝 (anchoredLifetime (processPath B ω) ε).toReal)
  convert ht using 1
  funext i
  congr 2
  congr 1
  funext n
  simpa only [NNReal.coe_mul, NNReal.coe_natCast] using
    (processPath_apply_of_continuous hc ((n : ℝ≥0) * h i)).symm

end SwingRepair
