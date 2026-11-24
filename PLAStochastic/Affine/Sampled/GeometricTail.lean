import PLAStochastic.Affine.Sampled.Lifetime
import PLAStochastic.Affine.Error.BrownianScaling
import PLAStochastic.Affine.Lifetime.GaussianBlocks
import PLAStochastic.ForMathlib.MeasureTheory.Integral.GeometricTailIntegrability

/-!
# Uniform geometric tails of actual sampled Brownian lifetimes

For meshes at most one, floor(4 / h) grid increments span a time in (3,4].
Three-point obstructions on disjoint such pairs of intervals reduce, by actual
Brownian scaling, to independent standard Gaussian block variables. The bound
is uniform in the mesh and is proved before any integrability conclusion.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace BrownianAffine

def gaussianBlockPassRadius (R : ℝ) : ℝ≥0∞ := gaussianReal 0 1 (Set.Icc (-R) R)

theorem gaussianBlockPassRadius_lt_one (R : ℝ) : gaussianBlockPassRadius R < 1 := by
  by_contra h
  have hq : gaussianReal 0 1 (Set.Icc (-R) R) = 1 :=
    le_antisymm prob_le_one (le_of_not_gt h)
  have hz : gaussianReal 0 1 (Set.Icc (-R) R)ᶜ = 0 := by
    rw [measure_compl measurableSet_Icc (measure_ne_top _ _), measure_univ, hq, tsub_self]
  have hv := (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)) hz
  have hsub : Set.Ioi R ⊆ (Set.Icc (-R) R)ᶜ := by
    intro x hx hmem
    exact (not_le_of_gt hx) hmem.2
  have hmono := measure_mono (μ := (volume : Measure ℝ)) hsub
  rw [hv, Real.volume_Ioi] at hmono
  exact (by simp : ¬ (∞ : ℝ≥0∞) ≤ 0) hmono

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem gaussianBlocks_probability_radius (hB : IsPreBrownianReal B μ) (R : ℝ) (n : ℕ) :
    μ {ω | ∀ j < n, |gaussianBlock B j ω| ≤ R} = gaussianBlockPassRadius R ^ n := by
  classical
  have h := (gaussianBlock_iIndepFun hB).measure_inter_preimage_eq_mul (Finset.range n)
    (sets := fun _ => Set.Icc (-R) R) (fun _ _ => measurableSet_Icc)
  have hset : {ω | ∀ j < n, |gaussianBlock B j ω| ≤ R} =
      ⋂ j ∈ Finset.range n, (gaussianBlock B j) ⁻¹' Set.Icc (-R) R := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range, Set.mem_preimage,
      Set.mem_Icc, abs_le]
  rw [hset, h]
  have heach (j : ℕ) : μ ((gaussianBlock B j) ⁻¹' Set.Icc (-R) R) = gaussianBlockPassRadius R :=
    (gaussianBlock_hasLaw hB j).measure_eq measurableSet_Icc
  simp only [heach, Finset.prod_const, Finset.card_range]

/-- A fixed positive Brownian time dilation whose block points are actual mesh observations. -/
def meshBlockScale (h : ℝ≥0) : ℝ≥0 := ((⌊(4 : ℝ) / h⌋₊ : ℝ≥0) * h) / 8

theorem meshBlockScale_bounds {h : ℝ≥0} (hh : h ≠ 0) (hh₁ : h ≤ 1) :
    (1 / 4 : ℝ≥0) ≤ meshBlockScale h ∧ meshBlockScale h ≤ 1 / 2 := by
  have hp : 0 < (h : ℝ) := by exact_mod_cast (pos_of_ne_zero hh)
  have hle := meshFloor_mul_le (by norm_num : (0 : ℝ) ≤ 4) hp
  have hgap := meshFloor_gap_lt (T := 4) hp
  have hhr : (h : ℝ) ≤ 1 := by exact_mod_cast hh₁
  constructor
  · change (1 : ℝ) / 4 ≤ (⌊(4 : ℝ) / h⌋₊ : ℝ) * (h : ℝ) / 8
    linarith
  · change (⌊(4 : ℝ) / h⌋₊ : ℝ) * (h : ℝ) / 8 ≤ (1 : ℝ) / 2
    linarith

theorem meshBlockScale_ne_zero {h : ℝ≥0} (hh : h ≠ 0) (hh₁ : h ≤ 1) :
    meshBlockScale h ≠ 0 := by
  have h := (meshBlockScale_bounds hh hh₁).1
  exact ne_of_gt (lt_of_lt_of_le (by norm_num) h)

omit [MeasurableSpace Ω] in
theorem gaussianBlock_normalized (B : ℝ≥0 → Ω → ℝ) (c : ℝ≥0) (j : ℕ) (ω : Ω) :
    gaussianBlock (normalizedBrownian B c) j ω =
      (Real.sqrt (c : ℝ))⁻¹ *
        ((B (c * (16 * j + 8)) ω - (B (c * (16 * j)) ω +
          B (c * (16 * j + 16)) ω) / 2) / 2) := by
  unfold gaussianBlock normalizedBrownian
  ring

omit [MeasurableSpace Ω] in
theorem meshBlockScale_times (h : ℝ≥0) (j : ℕ) :
    meshBlockScale h * (16 * j) = ((2 * ⌊(4 : ℝ) / h⌋₊ * j : ℕ) : ℝ≥0) * h ∧
    meshBlockScale h * (16 * j + 8) = ((⌊(4 : ℝ) / h⌋₊ * (2 * j + 1) : ℕ) : ℝ≥0) * h ∧
    meshBlockScale h * (16 * j + 16) = ((2 * ⌊(4 : ℝ) / h⌋₊ * (j + 1) : ℕ) : ℝ≥0) * h := by
  unfold meshBlockScale
  push_cast
  constructor
  · ring
  constructor <;> ring

theorem finiteMesh_error_implies_sample_fit (f : C(ℝ, ℝ)) {T h ε : ℝ}
    (hh : 0 < h) (herr : finiteMeshAnchoredError f T h ≤ ε) :
    ∃ a : ℝ, ∀ k : ℕ, (k : ℝ) * h ≤ T → |f ((k : ℝ) * h) - a * ((k : ℝ) * h)| ≤ ε := by
  obtain ⟨a, ha⟩ := (finiteMeshAnchoredError_le_iff f T h ε).mp herr
  refine ⟨a, fun k hk => ?_⟩
  have hi : k ≤ ⌊T / h⌋₊ := Nat.le_floor ((le_div_iff₀ hh).mpr hk)
  exact ha ⟨k, Nat.lt_succ_of_le hi⟩

theorem three_point_anchored_obstruction (s r a y₀ yₘ y₁ ε : ℝ)
    (h₀ : |y₀ - a * s| ≤ ε) (hₘ : |yₘ - a * (s + r)| ≤ ε)
    (h₁ : |y₁ - a * (s + 2 * r)| ≤ ε) :
    |(yₘ - (y₀ + y₁) / 2) / 2| ≤ ε := by
  rw [abs_le] at h₀ hₘ h₁ ⊢
  constructor <;> nlinarith

/-- Actual grid feasibility forces every normalized, disjoint three-point block to pass. -/
theorem finiteMesh_error_implies_scaled_blocks (f : C(ℝ, ℝ))
    {h : ℝ≥0} (hh : h ≠ 0) (hh₁ : h ≤ 1) (ε : ℝ) (n : ℕ)
    (herr : finiteMeshAnchoredError f (8 * n) h ≤ ε) :
    ∀ j < n, |(Real.sqrt (meshBlockScale h : ℝ))⁻¹ *
      ((f ((meshBlockScale h : ℝ) * (16 * j + 8)) -
        (f ((meshBlockScale h : ℝ) * (16 * j)) +
          f ((meshBlockScale h : ℝ) * (16 * j + 16))) / 2) / 2)| ≤ 2 * ε := by
  have hp : 0 < (h : ℝ) := by exact_mod_cast (pos_of_ne_zero hh)
  obtain ⟨a, ha⟩ := finiteMesh_error_implies_sample_fit f hp herr
  have hb := meshBlockScale_bounds hh hh₁
  have hc₀ : 0 ≤ (meshBlockScale h : ℝ) := (meshBlockScale h).coe_nonneg
  have hc₁ : (meshBlockScale h : ℝ) ≤ 1 / 2 := by exact_mod_cast hb.2
  have hsqrt : (1 : ℝ) / 2 ≤ Real.sqrt (meshBlockScale h : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    have hl : (1 : ℝ) / 4 ≤ (meshBlockScale h : ℝ) := by exact_mod_cast hb.1
    nlinarith
  have hinv : (Real.sqrt (meshBlockScale h : ℝ))⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ (show 0 < Real.sqrt (meshBlockScale h : ℝ) by linarith)]
    linarith
  intro j hj
  have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast (show j + 1 ≤ n by omega)
  have hlast : (meshBlockScale h : ℝ) * (16 * j + 16) ≤ 8 * n := by
    calc
      _ ≤ (1 / 2 : ℝ) * (16 * j + 16) :=
        mul_le_mul_of_nonneg_right hc₁ (by positivity)
      _ ≤ 8 * n := by linarith
  have ht := meshBlockScale_times h j
  have ht₀ := congrArg (fun t : ℝ≥0 => (t : ℝ)) ht.1
  have htₘ := congrArg (fun t : ℝ≥0 => (t : ℝ)) ht.2.1
  have ht₁ := congrArg (fun t : ℝ≥0 => (t : ℝ)) ht.2.2
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_ofNat] at ht₀ htₘ ht₁
  have h₀ := ha (2 * ⌊(4 : ℝ) / h⌋₊ * j) (by
    rw [← ht₀]
    exact (mul_le_mul_of_nonneg_left (by linarith : (16 : ℝ) * j ≤ 16 * j + 16) hc₀).trans hlast)
  have hₘ := ha (⌊(4 : ℝ) / h⌋₊ * (2 * j + 1)) (by
    rw [← htₘ]
    exact (mul_le_mul_of_nonneg_left (by linarith : (16 : ℝ) * j + 8 ≤ 16 * j + 16) hc₀).trans hlast)
  have h₁ := ha (2 * ⌊(4 : ℝ) / h⌋₊ * (j + 1)) (by rw [← ht₁]; exact hlast)
  rw [← ht₀] at h₀
  rw [← htₘ] at hₘ
  rw [← ht₁] at h₁
  have hraw := three_point_anchored_obstruction
    ((meshBlockScale h : ℝ) * (16 * j)) ((meshBlockScale h : ℝ) * 8) a _ _ _ ε h₀
    (by
      rw [← show (meshBlockScale h : ℝ) * (16 * j + 8) =
        (meshBlockScale h : ℝ) * (16 * j) + (meshBlockScale h : ℝ) * 8 by ring]
      exact hₘ)
    (by
      rw [← show (meshBlockScale h : ℝ) * (16 * j + 16) =
        (meshBlockScale h : ℝ) * (16 * j) + 2 * ((meshBlockScale h : ℝ) * 8) by ring]
      exact h₁)
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact mul_le_mul hinv hraw (abs_nonneg _) (by norm_num)

/-- A survival event at 16n contains n independent actual grid obstructions;
the resulting ratio depends on tolerance but not on the mesh. -/
theorem finiteMeshProcessLifetime_tail_le (hB : IsBrownianReal B μ)
    {h : ℝ≥0} (hh : h ≠ 0) (hh₁ : h ≤ 1) (ε : ℝ) (n : ℕ) :
    μ {ω | (16 : ℝ≥0∞) * n ≤ finiteMeshProcessLifetime B h ε ω} ≤
      gaussianBlockPassRadius (2 * ε) ^ n := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  let c := meshBlockScale h
  have hC := isBrownianReal_normalized hB (meshBlockScale_ne_zero hh hh₁)
  rw [← gaussianBlocks_probability_radius hC.toIsPreBrownianReal (2 * ε) n]
  apply measure_mono_ae
  filter_upwards [hB.cont] with ω hcω
  intro hsurv
  have herr : finiteMeshAnchoredError (processPath B ω) (8 * n) h ≤ ε := by
    by_contra he
    have he' : ε < finiteMeshAnchoredError (processPath B ω) ((8 * n : ℝ≥0) : ℝ) h := by
      simpa using lt_of_not_ge he
    have hle : finiteMeshProcessLifetime B h ε ω ≤ (8 * n : ℝ≥0) :=
      firstExceedance_le_of_exceeds he'
    have hbad : (16 : ℝ≥0∞) * n ≤ (8 * n : ℝ≥0) := hsurv.trans hle
    have hbad' : (16 : ℝ) * n ≤ 8 * n := by exact_mod_cast hbad
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith
  intro j hj
  have hb := finiteMesh_error_implies_scaled_blocks (processPath B ω) hh hh₁ ε n herr j hj
  rw [gaussianBlock_normalized]
  have h₀ := processPath_apply_of_continuous hcω (c * (16 * j))
  have hₘ := processPath_apply_of_continuous hcω (c * (16 * j + 8))
  have h₁ := processPath_apply_of_continuous hcω (c * (16 * j + 16))
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_ofNat] at h₀ hₘ h₁
  change |(Real.sqrt (c : ℝ))⁻¹ *
    ((processPath B ω ((c : ℝ) * (16 * j + 8)) -
      (processPath B ω ((c : ℝ) * (16 * j)) +
        processPath B ω ((c : ℝ) * (16 * j + 16))) / 2) / 2)| ≤ 2 * ε at hb
  rw [h₀, hₘ, h₁] at hb
  exact hb

theorem finiteMeshProcessLifetime_geometricTail (hB : IsBrownianReal B μ)
    {h : ℝ≥0} (hh : h ≠ 0) (hh₁ : h ≤ 1) (ε : ℝ) :
    GeometricTail16 μ (finiteMeshProcessLifetime B h ε)
      (gaussianBlockPassRadius (2 * ε)).toReal :=
  geometricTail16_of_ennreal (gaussianBlockPassRadius_lt_one (2 * ε))
    (finiteMeshProcessLifetime_tail_le hB hh hh₁ ε)

end BrownianAffine
