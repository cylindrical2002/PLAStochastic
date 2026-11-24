import PLAStochastic.Swing.DenseSampling.Segments.UniformLocalBounds

/-!
# Quantitative native slope and boundary bounds

The selected old line is feasible on its accepted prefix. A genuine rejection
therefore violates that very line at the next sample. The resulting bounds
apply directly to native segment data, irrespective of its SSE optimality.
-/

noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology

namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- A rejected prefix violates any line feasible on its old prefix at the
new sample; rejection is not assumed to violate a chosen line. -/
theorem native_rejected_line_error_gt {t y : ℕ → ℝ} {ε q m : ℝ} {s e : ℕ}
    (hold : feasibleSlope (Finset.Icc (s + 1) e) t y (t s) q ε m)
    (hreject : ¬ nativePrefixFeasible t y ε s (e + 1) q) :
    ε < |y (e + 1) - (q + m * (t (e + 1) - t s))| := by
  by_contra h
  apply hreject
  refine ⟨m, fun i hi => ?_⟩
  have hi' := Finset.mem_Icc.mp hi
  by_cases hie : i ≤ e
  · exact hold i (Finset.mem_Icc.mpr ⟨hi'.1, hie⟩)
  · have heq : i = e + 1 := by omega
    subst i
    exact le_of_not_gt h

/-- Endpoint feasibility gives the paper's inverse-accepted-count slope bound. -/
theorem native_slope_step_bound (y : ℕ → ℝ) {h ε q m : ℝ} (hh : 0 < h)
    {s e : ℕ} (hse : s < e) (hq : |q - y s| ≤ ε)
    (hfit : feasibleSlope (Finset.Icc (s + 1) e) (fun j => (j : ℝ) * h) y
      ((s : ℝ) * h) q ε m) :
    |m| * h ≤ (2 * ε + |y e - y s|) / ((e - s : ℕ) : ℝ) := by
  have hlen : 0 < ((e - s : ℕ) : ℝ) := by exact_mod_cast (Nat.sub_pos_of_lt hse)
  have hcast : ((e - s : ℕ) : ℝ) = (e : ℝ) - (s : ℝ) := Nat.cast_sub hse.le
  have he := hfit e (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hq' : |y s - q| ≤ ε := by simpa only [abs_sub_comm] using hq
  have hbound : |m * ((e : ℝ) * h - (s : ℝ) * h)| ≤ 2 * ε + |y e - y s| := by
    calc
      _ = |((y e - y s) + (y s - q)) - (y e - (q + m * ((e : ℝ) * h - (s : ℝ) * h)))| := by
        congr 1; ring
      _ ≤ |(y e - y s) + (y s - q)| + |y e - (q + m * ((e : ℝ) * h - (s : ℝ) * h))| := abs_sub _ _
      _ ≤ |y e - y s| + |y s - q| + |y e - (q + m * ((e : ℝ) * h - (s : ℝ) * h))| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by linarith
  apply (le_div_iff₀ hlen).mpr
  have hgap : 0 ≤ (e : ℝ) * h - (s : ℝ) * h := by
    have hes : (s : ℝ) < e := by exact_mod_cast hse
    nlinarith
  rw [abs_mul, abs_of_nonneg hgap] at hbound
  rw [hcast]
  nlinarith

/-- A completed native endpoint lies within one path increment and one line
increment of the error boundary, with no rounding or hidden mesh convention. -/
theorem native_boundary_deficit_bound (y : ℕ → ℝ) {h ε q m : ℝ} (hh : 0 < h)
    {s e : ℕ} (hse : s < e)
    (hfit : feasibleSlope (Finset.Icc (s + 1) e) (fun j => (j : ℝ) * h) y
      ((s : ℝ) * h) q ε m)
    (hreject : ¬ nativePrefixFeasible (fun j => (j : ℝ) * h) y ε s (e + 1) q) :
    0 ≤ ε - |q + m * ((e : ℝ) * h - (s : ℝ) * h) - y e| ∧
      ε - |q + m * ((e : ℝ) * h - (s : ℝ) * h) - y e| < |y (e + 1) - y e| + |m| * h := by
  have he := hfit e (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hn := native_rejected_line_error_gt hfit hreject
  have hb : |y (e + 1) - (q + m * (((e + 1 : ℕ) : ℝ) * h - (s : ℝ) * h))| ≤
      |y e - (q + m * ((e : ℝ) * h - (s : ℝ) * h))| + |y (e + 1) - y e| + |m| * h := by
    calc
      _ = |(y e - (q + m * ((e : ℝ) * h - (s : ℝ) * h))) + (y (e + 1) - y e) - m * h| := by
        congr 1
        rw [Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ |(y e - (q + m * ((e : ℝ) * h - (s : ℝ) * h))) + (y (e + 1) - y e)| + |m * h| := abs_sub _ _
      _ ≤ |y e - (q + m * ((e : ℝ) * h - (s : ℝ) * h))| + |y (e + 1) - y e| + |m| * h := by
        rw [abs_mul, abs_of_pos hh]
        exact add_le_add (abs_add_le _ _) le_rfl
  rw [abs_sub_comm (q + m * ((e : ℝ) * h - (s : ℝ) * h)) (y e)]
  constructor <;> linarith

/-- Uniformly over all completed native intervals ending in a compact
horizon, one-step changes of the fitted line tend to zero. -/
theorem exists_uniform_native_slope_step (f : C(ℝ, ℝ)) {T ε r : ℝ} (hT : 0 ≤ T)
    (hε : 0 < ε) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → ∀ s e : ℕ,
      s < e → (e : ℝ) * h ≤ T → ∀ q m : ℝ, |q - f ((s : ℝ) * h)| ≤ ε →
      feasibleSlope (Finset.Icc (s + 1) e) (fun j => (j : ℝ) * h)
        (fun j => f ((j : ℝ) * h)) ((s : ℝ) * h) q ε m →
      (¬ nativePrefixFeasible (fun j => (j : ℝ) * h) (fun j => f ((j : ℝ) * h)) ε s (e + 1) q) →
      |m| * h < r := by
  let M := ‖intervalPath f T‖
  let C := 2 * ε + 2 * M
  have hM : 0 ≤ M := norm_nonneg _
  have hC : 0 < C := by dsimp only [C]; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (C / r)
  have hnR : 0 < (n : ℝ) := (div_pos hC hr).trans hn
  have hnN : 0 < n := by exact_mod_cast hnR
  have hnr : C < (n : ℝ) * r := (div_lt_iff₀ hr).mp hn
  obtain ⟨δ, hδ, hpref⟩ := exists_uniform_nativePrefix_mesh f hT hε n hnN
  refine ⟨δ, hδ, fun h hh hhδ s e hse heT q m hq hfit hrej => ?_⟩
  have hseR : (s : ℝ) < e := by exact_mod_cast hse
  have hsT : (s : ℝ) * h ≤ T := (mul_le_mul_of_nonneg_right hseR.le hh.le).trans heT
  have hlen : n ≤ e - s := by
    by_contra h
    have he : e + 1 ≤ s + n := by omega
    exact hrej (nativePrefixFeasible_mono_end (hpref _ hh hhδ s hsT q hq) he)
  have hlenR : (n : ℝ) ≤ ((e - s : ℕ) : ℝ) := by exact_mod_cast hlen
  have hlenpos : 0 < ((e - s : ℕ) : ℝ) := hnR.trans_le hlenR
  have hsVal := path_value_le_interval_norm f
    (show (s : ℝ) * h ∈ Icc (0 : ℝ) T from ⟨by positivity, hsT⟩)
  have heVal := path_value_le_interval_norm f
    (show (e : ℝ) * h ∈ Icc (0 : ℝ) T from ⟨by positivity, heT⟩)
  have hosc : |f ((e : ℝ) * h) - f ((s : ℝ) * h)| ≤ 2 * M := by
    have hb := abs_sub (f ((e : ℝ) * h)) (f ((s : ℝ) * h))
    dsimp only [M]
    linarith
  have hb := native_slope_step_bound (fun j => f ((j : ℝ) * h)) hh hse hq hfit
  have hmul := (le_div_iff₀ hlenpos).mp hb
  dsimp only [C] at hnr
  nlinarith

/-- Both parts of the uniform boundary-control estimate hold over every
completed native interval; no selected subsequence of recordings is assumed. -/
theorem exists_uniform_native_boundary_control (f : C(ℝ, ℝ)) {T ε r : ℝ} (hT : 0 ≤ T)
    (hε : 0 < ε) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → ∀ s e : ℕ,
      s < e → (e : ℝ) * h ≤ T → ∀ q m : ℝ, |q - f ((s : ℝ) * h)| ≤ ε →
      feasibleSlope (Finset.Icc (s + 1) e) (fun j => (j : ℝ) * h)
        (fun j => f ((j : ℝ) * h)) ((s : ℝ) * h) q ε m →
      (¬ nativePrefixFeasible (fun j => (j : ℝ) * h) (fun j => f ((j : ℝ) * h)) ε s (e + 1) q) →
      |m| * h < r ∧
      0 ≤ ε - |q + m * ((e : ℝ) * h - (s : ℝ) * h) - f ((e : ℝ) * h)| ∧
      ε - |q + m * ((e : ℝ) * h - (s : ℝ) * h) - f ((e : ℝ) * h)| < r := by
  have hr2 : 0 < r / 2 := half_pos hr
  obtain ⟨δs, hδs, hslope⟩ := exists_uniform_native_slope_step f hT hε hr2
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous (f := f) f.continuous.continuousOn
    (s := Icc (0 : ℝ) (T + 1))
  obtain ⟨d, hd, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu (r / 2) hr2
  refine ⟨min δs (min 1 d), lt_min hδs (lt_min zero_lt_one hd),
    fun h hh hhδ s e hse heT q m hq hfit hrej => ?_⟩
  have hhδs : h < δs := hhδ.trans_le (min_le_left _ _)
  have hh1 : h < 1 := hhδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhd : h < d := hhδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hmh := hslope h hh hhδs s e hse heT q m hq hfit hrej
  have heMem : (e : ℝ) * h ∈ Icc (0 : ℝ) (T + 1) := ⟨by positivity, by linarith⟩
  have hnMem : ((e + 1 : ℕ) : ℝ) * h ∈ Icc (0 : ℝ) (T + 1) := by
    rw [Nat.cast_add, Nat.cast_one]
    constructor
    · positivity
    · nlinarith
  have hdist : dist (((e + 1 : ℕ) : ℝ) * h) ((e : ℝ) * h) < d := by
    rw [Real.dist_eq, Nat.cast_add, Nat.cast_one]
    have heq : ((e : ℝ) + 1) * h - (e : ℝ) * h = h := by ring
    rw [heq, abs_of_pos hh]
    exact hhd
  have hm := hmod _ hnMem _ heMem hdist
  have hm' : |f (((e + 1 : ℕ) : ℝ) * h) - f ((e : ℝ) * h)| < r / 2 := by
    simpa only [Real.dist_eq] using hm
  have hb := native_boundary_deficit_bound (fun j => f ((j : ℝ) * h)) hh hse hfit hrej
  exact ⟨by linarith, hb.1, by linarith [hb.2]⟩

end SwingRepair

