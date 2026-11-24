import PLAStochastic.Brownian.Construction.DyadicPolygon
import Mathlib.Topology.ContinuousMap.Compact

/-! Actual compact uniform limits of dyadic interpolants and their continuous global assembly. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators Classical
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Every polygonal approximation is an actual element of the complete uniform path space. -/
def dyadicCompactPath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (K n : ℕ) (ω : Ω) :
    C(Icc (0 : ℝ≥0) K, ℝ) :=
  ⟨fun t => dyadicPolygon B n t ω,
    (continuous_dyadicPolygon B n ω).comp continuous_subtype_val⟩

theorem dyadicCompactPath_step_dist_le {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (K n : ℕ) (ω : Ω) {a : ℝ} (ha : 0 ≤ a)
    (hinc : ∀ j < (K + 1) * 2 ^ (n + 1),
      |B (dyadicTime (n + 1) (j + 1)) ω - B (dyadicTime (n + 1) j) ω| ≤ a) :
    dist (dyadicCompactPath B K n ω) (dyadicCompactPath B K (n + 1) ω) ≤ 4 * a := by
  rw [dist_comm, dist_eq_norm]
  apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ 4 * a)).mpr
  intro t
  change ‖dyadicPolygon B (n + 1) t ω - dyadicPolygon B n t ω‖ ≤ 4 * a
  rw [Real.norm_eq_abs]
  apply dyadicPolygon_step_bound B n (K + 1) ω ha hinc t
  exact t.property.2.trans_lt (by exact_mod_cast Nat.lt_succ_self K)

/-- Summably small refinement steps make the actual interpolants uniformly Cauchy. -/
theorem dyadicCompactPath_cauchy {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (K : ℕ) (ω : Ω)
    (hinc : ∀ᶠ n in atTop, ∀ j < (K + 1) * 2 ^ n,
      |B (dyadicTime n (j + 1)) ω - B (dyadicTime n j) ω| < (7 / 8 : ℝ) ^ n) :
    CauchySeq (fun n => dyadicCompactPath B K n ω) := by
  apply cauchySeq_of_summable_dist
  have hs : Summable (fun n : ℕ => 4 * (7 / 8 : ℝ) ^ (n + 1)) := by
    apply (summable_nat_add_iff (f := fun n : ℕ => 4 * (7 / 8 : ℝ) ^ n) 1).mpr
    exact (summable_geometric_of_abs_lt_one (by norm_num : |(7 / 8 : ℝ)| < 1)).mul_left (4 : ℝ)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hinc] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
  exact dyadicCompactPath_step_dist_le B K n ω (by positivity) (fun j hj => (hn j hj).le)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem preBrownian_compactPaths_cauchy_ae (hB : IsPreBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ K : ℕ, CauchySeq (fun n => dyadicCompactPath B K n ω) := by
  filter_upwards [preBrownian_dyadic_edges_all_horizons_ae hB] with ω hω K
  exact dyadicCompactPath_cauchy B K ω (hω (K + 1))

/-- The continuous uniform limit on a compact horizon, with zero as the exceptional-path version. -/
def compactPolygonLimit {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (K : ℕ) (ω : Ω) :
    C(Icc (0 : ℝ≥0) K, ℝ) :=
  if h : CauchySeq (fun n => dyadicCompactPath B K n ω) then
    Classical.choose (cauchySeq_tendsto_of_complete h) else 0

theorem compactPolygonLimit_tendsto {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (K : ℕ) (ω : Ω)
    (h : CauchySeq (fun n => dyadicCompactPath B K n ω)) :
    Tendsto (fun n => dyadicCompactPath B K n ω) atTop (𝓝 (compactPolygonLimit B K ω)) := by
  rw [compactPolygonLimit, dif_pos h]
  exact Classical.choose_spec (cauchySeq_tendsto_of_complete h)

theorem compactPolygonLimit_pointwise_tendsto {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (K : ℕ) (ω : Ω)
    (h : CauchySeq (fun n => dyadicCompactPath B K n ω)) (t : Icc (0 : ℝ≥0) K) :
    Tendsto (fun n => dyadicPolygon B n t ω) atTop (𝓝 (compactPolygonLimit B K ω t)) :=
  (continuous_eval_const t).continuousAt.tendsto.comp (compactPolygonLimit_tendsto B K ω h)

theorem compactPolygonLimit_compatible {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (h : ∀ K : ℕ, CauchySeq (fun n => dyadicCompactPath B K n ω))
    (K L : ℕ) (t : ℝ≥0) (htK : t ≤ K) (htL : t ≤ L) :
    compactPolygonLimit B K ω ⟨t, bot_le, htK⟩ = compactPolygonLimit B L ω ⟨t, bot_le, htL⟩ :=
  tendsto_nhds_unique
    (compactPolygonLimit_pointwise_tendsto B K ω (h K) ⟨t, bot_le, htK⟩)
    (compactPolygonLimit_pointwise_tendsto B L ω (h L) ⟨t, bot_le, htL⟩)

/-- A single process obtained by joining the compatible compact uniform limits. -/
def continuousPolygonModification {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  compactPolygonLimit B (Nat.ceil t) ω ⟨t, bot_le, Nat.le_ceil t⟩

theorem continuousPolygonModification_eq_compact {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (h : ∀ K : ℕ, CauchySeq (fun n => dyadicCompactPath B K n ω))
    (K : ℕ) (t : ℝ≥0) (ht : t ≤ K) :
    continuousPolygonModification B t ω = compactPolygonLimit B K ω ⟨t, bot_le, ht⟩ :=
  compactPolygonLimit_compatible B ω h (Nat.ceil t) K t (Nat.le_ceil t) ht

theorem continuous_continuousPolygonModification {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (h : ∀ K : ℕ, CauchySeq (fun n => dyadicCompactPath B K n ω)) :
    Continuous (fun t => continuousPolygonModification B t ω) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨K, hKt⟩ := exists_nat_gt t
  let f : ℝ≥0 → ℝ := fun s => compactPolygonLimit B K ω ⟨min s K, bot_le, min_le_right _ _⟩
  have hf : Continuous f := by
    apply (compactPolygonLimit B K ω).continuous.comp
    exact (continuous_id.min continuous_const).subtype_mk _
  apply hf.continuousAt.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hKt] with s hs
  have hle : s ≤ (K : ℝ≥0) := hs.le
  simp only [f, min_eq_left hle]
  exact continuousPolygonModification_eq_compact B ω h K s hle

theorem preBrownian_continuousPolygonModification_continuous_ae (hB : IsPreBrownianReal B μ) :
    ∀ᵐ ω ∂μ, Continuous (fun t => continuousPolygonModification B t ω) := by
  filter_upwards [preBrownian_compactPaths_cauchy_ae hB] with ω hω
  exact continuous_continuousPolygonModification B ω hω

theorem preBrownian_polygon_tendsto_modification_ae (hB : IsPreBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, Tendsto (fun n => dyadicPolygon B n t ω) atTop
      (𝓝 (continuousPolygonModification B t ω)) := by
  filter_upwards [preBrownian_compactPaths_cauchy_ae hB] with ω hω t
  exact compactPolygonLimit_pointwise_tendsto B (Nat.ceil t) ω (hω _) ⟨t, bot_le, Nat.le_ceil t⟩

end BrownianAffine
