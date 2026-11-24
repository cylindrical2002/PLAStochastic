import PLAStochastic.Swing.Algorithm.OutputChain
import PLAStochastic.Swing.DenseSampling.Segments.UniformLocalBounds
import PLAStochastic.Swing.Algorithm.Measurability

/-! # Vanishing mesh times the actual number of completed native recordings -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The terminal EOF segment is excluded, exactly as in the paper's recording count. -/
def nativeCompletedCount (t y : ℕ → ℝ) (ε : ℝ) (last : ℕ) : ℕ :=
  (nativeStream t y ε last).length - 1

theorem NativeChain.completed_count_mul_le {t y : ℕ → ℝ} {ε : ℝ}
    {s last : ℕ} {q : ℝ} {segs : List NativeSegment}
    (hc : NativeChain t y ε s q last segs) (n : ℕ)
    (hspan : ∀ seg ∈ segs,
      (¬ nativePrefixFeasible t y ε seg.start (seg.finish + 1) seg.anchorValue) →
      n ≤ seg.finish - seg.start) :
    (segs.length - 1) * n ≤ last - s := by
  induction hc with
  | empty => simp
  | terminal hv => simp
  | @cons head last tail hv hr hn ih =>
      have hh := hspan head List.mem_cons_self hr
      have ht := ih (fun seg hs => hspan seg (List.mem_cons_of_mem head hs))
      have hb := hn.start_le_finish
      have hp := hv.positive
      simp only [List.length_cons, Nat.add_sub_cancel]
      by_cases hz : tail.length = 0
      · simp [hz]
      · have he : tail.length = (tail.length - 1) + 1 := by omega
        rw [he, Nat.add_mul, one_mul]
        omega

theorem eventually_nativeCompletedCount_mul_le (f : C(ℝ, ℝ)) {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) {ι : Type*} {l : Filter ι} {h : ι → ℝ} {last : ι → ℕ}
    (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0))
    (hlast : ∀ i, (last i : ℝ) * h i ≤ T) (n : ℕ) :
    ∀ᶠ i in l, (nativeCompletedCount (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i)) ε (last i)) * n ≤ last i := by
  filter_upwards [eventually_native_completed_spans_ge f hT hε hh hconv n] with i hi
  have hmono : StrictMono (fun j : ℕ => (j : ℝ) * h i) :=
    fun a b hab => mul_lt_mul_of_pos_right (by exact_mod_cast hab) (hh i)
  have hc := nativeStream_spec (fun j => (j : ℝ) * h i)
    (fun j => f ((j : ℝ) * h i)) hmono hε.le (last i)
  have hb := hc.completed_count_mul_le n ?_
  · simpa only [nativeCompletedCount, Nat.sub_zero] using hb
  intro seg hseg hr
  have hbounds := hc.segment_bounds seg hseg
  have hq := hc.anchor_errors (by simp only [sub_self, abs_zero]; exact hε.le) seg hseg
  apply hi seg.start seg.finish hbounds.2.2
    ((mul_le_mul_of_nonneg_right (by exact_mod_cast hbounds.2.1.trans' hbounds.2.2.le) (hh i).le).trans (hlast i))
    seg.anchorValue hq hr

/-- For every continuous input on a compact horizon, the mesh multiplied by the
actual number of non-EOF recordings tends to zero. No Brownian input is needed. -/
theorem tendsto_mesh_mul_nativeCompletedCount (f : C(ℝ, ℝ)) {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) {ι : Type*} {l : Filter ι} {h : ι → ℝ} {last : ι → ℕ}
    (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0))
    (hlast : ∀ i, (last i : ℝ) * h i ≤ T) :
    Tendsto (fun i => h i * (nativeCompletedCount (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i)) ε (last i) : ℝ)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨n, hn⟩ := exists_nat_gt (T / δ + 1)
  have hnR : 0 < (n : ℝ) := by have ht := div_nonneg hT hδ.le; linarith
  have hbound : T / (n : ℝ) < δ := by
    apply (div_lt_iff₀ hnR).mpr
    have ht : T / δ < (n : ℝ) := by linarith
    have hh := (div_lt_iff₀ hδ).mp ht
    linarith
  filter_upwards [eventually_nativeCompletedCount_mul_le f hT hε hh hconv hlast n] with i hi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (hh i).le (Nat.cast_nonneg _))]
  apply lt_of_le_of_lt ?_ hbound
  apply (le_div_iff₀ hnR).mpr
  have hir : ((nativeCompletedCount (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i)) ε (last i) : ℝ)) * n ≤ last i := by exact_mod_cast hi
  have hp := mul_le_mul_of_nonneg_left hir (hh i).le
  nlinarith [hlast i]

theorem tendsto_mesh_mul_nativeCompletedCount_floor (f : C(ℝ, ℝ)) {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) {ι : Type*} {l : Filter ι} {h : ι → ℝ}
    (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0)) :
    Tendsto (fun i => h i * (nativeCompletedCount (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i)) ε ⌊T / h i⌋₊ : ℝ)) l (𝓝 0) :=
  tendsto_mesh_mul_nativeCompletedCount f hT hε hh hconv (fun i => meshFloor_mul_le hT (hh i))

/-- The finite count agrees with the actual repeated-recording stopping times.
The stopping-time clock records increments, so sample horizon n+1 corresponds to n. -/
theorem nativeCompletedCount_eq_recording_card {Ω : Type*} [MeasurableSpace Ω]
    (t : ℕ → ℝ) (Y : ℕ → Ω → ℝ) (ε : ℝ) (n : ℕ) (ω : Ω) :
    nativeCompletedCount t (fun j => Y j ω) ε (n + 1) =
      ((Finset.Icc 1 n).filter (fun k => nativeRecordingTime t Y ε k ω ≤ n)).card := by
  classical
  have hb := nativeStream_length_le_last t (fun j => Y j ω) ε (n + 1)
  have he : (Finset.Icc 1 n).filter (fun k => nativeRecordingTime t Y ε k ω ≤ n) =
      Finset.Ico 1 (nativeStream t (fun j => Y j ω) ε (n + 1)).length := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, nativeRecordingTime_le_iff]
    omega
  rw [he, Nat.card_Ico]
  rfl

/-- Brownian specialization retains the actual sample path and the actual stream. -/
theorem mesh_mul_nativeCompletedCount_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0}
    (hh : ∀ i, h i ≠ 0) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun i => (h i : ℝ) *
      (nativeCompletedCount (fun j => (j : ℝ) * h i)
        (fun j => B ((j : ℝ≥0) * h i) ω) ε ⌊T / (h i : ℝ)⌋₊ : ℝ)) l (𝓝 0) := by
  filter_upwards [hB.cont] with ω hc
  have hf := tendsto_mesh_mul_nativeCompletedCount_floor (processPath B ω) hT hε
    (fun i => (show (0 : ℝ≥0) < h i from pos_iff_ne_zero.mpr (hh i))) hconv
  convert hf using 1
  funext i
  congr 2
  congr 1
  funext j
  simpa only [NNReal.coe_mul, NNReal.coe_natCast] using!
    (processPath_apply_of_continuous hc ((j : ℝ≥0) * h i)).symm

end SwingRepair
