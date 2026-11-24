import PLAStochastic.Swing.DenseSampling.Segments.SlopeBoundaryBounds

/-! # Signed native rejection and boundary flipping -/

noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology

namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- For a nonnegative inherited error and small relative displacements, a
true rejection puts the rejected sample above every previously feasible line. -/
theorem native_rejected_error_positive (y : ℕ → ℝ) {h ε q m : ℝ} (hh : 0 < h)
    {s e : ℕ} (hse : s < e) (hq : 0 ≤ q - y s)
    (hfit : feasibleSlope (Finset.Icc (s + 1) e) (fun j => (j : ℝ) * h) y
      ((s : ℝ) * h) q ε m)
    (hreject : ¬ nativePrefixFeasible (fun j => (j : ℝ) * h) y ε s (e + 1) q)
    (hsmall : ∀ j ∈ Finset.Icc (s + 1) (e + 1), |y j - y s| < ε) :
    ε < y (e + 1) - (q + m * (((e + 1 : ℕ) : ℝ) * h - (s : ℝ) * h)) := by
  have hsj (j : ℕ) (hj : s + 1 ≤ j) : (s : ℝ) * h < (j : ℝ) * h := by
    apply mul_lt_mul_of_pos_right _ hh
    exact_mod_cast (show s < j by omega)
  have hnpos := hsj (e + 1) (by omega)
  have hnsmall := hsmall (e + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hε : 0 ≤ ε := (abs_nonneg _).trans hnsmall.le
  let U := slopeUpper (((e + 1 : ℕ) : ℝ) * h) (y (e + 1)) ((s : ℝ) * h) q ε
  have hcross (j : ℕ) (hj : j ∈ Finset.Icc (s + 1) e) :
      slopeLower ((j : ℝ) * h) (y j) ((s : ℝ) * h) q ε < U := by
    have hj' := Finset.mem_Icc.mp hj
    have hjpos := sub_pos.mpr (hsj j hj'.1)
    have hjle : (j : ℝ) * h - (s : ℝ) * h ≤
        ((e + 1 : ℕ) : ℝ) * h - (s : ℝ) * h := by
      apply sub_le_sub_right
      apply mul_le_mul_of_nonneg_right _ hh.le
      exact_mod_cast (show j ≤ e + 1 by omega)
    have hjsmall := hsmall j (Finset.mem_Icc.mpr ⟨hj'.1, by omega⟩)
    have hb := native_lower_lt_new_upper hjpos hjle hq
      (le_max_left |y j - y s| |y (e + 1) - y s|)
      (le_max_right |y j - y s| |y (e + 1) - y s|)
      (max_lt_iff.mpr ⟨hjsmall, hnsmall⟩)
    dsimp only [slopeLower, slopeUpper, U] at *
    simp only [sub_zero] at hb
    convert hb using 1 <;> congr 1 <;> ring
  by_contra hbad
  have hlow : slopeLower (((e + 1 : ℕ) : ℝ) * h) (y (e + 1)) ((s : ℝ) * h) q ε ≤ m := by
    apply (div_le_iff₀ (sub_pos.mpr hnpos)).mpr
    linarith [le_of_not_gt hbad]
  have hLU : slopeLower (((e + 1 : ℕ) : ℝ) * h) (y (e + 1)) ((s : ℝ) * h) q ε ≤ U := by
    apply (div_le_div_iff_of_pos_right (sub_pos.mpr hnpos)).mpr
    linarith
  apply hreject
  refine ⟨min m U, fun j hj => ?_⟩
  have hj' := Finset.mem_Icc.mp hj
  apply (sample_error_iff_bounds (hsj j hj'.1)).mpr
  by_cases hje : j ≤ e
  · have hjold := Finset.mem_Icc.mpr ⟨hj'.1, hje⟩
    have hm := (sample_error_iff_bounds (hsj j hj'.1)).mp (hfit j hjold)
    exact ⟨le_min hm.1 (hcross j hjold).le, (min_le_left _ _).trans hm.2⟩
  · have heq : j = e + 1 := by omega
    subst j
    exact ⟨le_min hlow hLU, min_le_right _ _⟩

/-- Reflection gives the opposite sign for a nonpositive inherited error. -/
theorem native_rejected_error_negative (y : ℕ → ℝ) {h ε q m : ℝ} (hh : 0 < h)
    {s e : ℕ} (hse : s < e) (hq : q - y s ≤ 0)
    (hfit : feasibleSlope (Finset.Icc (s + 1) e) (fun j => (j : ℝ) * h) y
      ((s : ℝ) * h) q ε m)
    (hreject : ¬ nativePrefixFeasible (fun j => (j : ℝ) * h) y ε s (e + 1) q)
    (hsmall : ∀ j ∈ Finset.Icc (s + 1) (e + 1), |y j - y s| < ε) :
    y (e + 1) - (q + m * (((e + 1 : ℕ) : ℝ) * h - (s : ℝ) * h)) < -ε := by
  have hrfit : feasibleSlope (Finset.Icc (s + 1) e) (fun j => (j : ℝ) * h)
      (fun j => -y j) ((s : ℝ) * h) (-q) ε (-m) := by
    intro j hj
    convert hfit j hj using 1
    rw [show -y j - (-q + -m * ((j : ℝ) * h - (s : ℝ) * h)) =
      -(y j - (q + m * ((j : ℝ) * h - (s : ℝ) * h))) by ring, abs_neg]
  have hrreject : ¬ nativePrefixFeasible (fun j => (j : ℝ) * h)
      (fun j => -y j) ε s (e + 1) (-q) := by
    rintro ⟨a, ha⟩
    apply hreject
    refine ⟨-a, fun j hj => ?_⟩
    convert ha j hj using 1
    rw [show y j - (q + -a * ((j : ℝ) * h - (s : ℝ) * h)) =
      -(-y j - (-q + a * ((j : ℝ) * h - (s : ℝ) * h))) by ring, abs_neg]
  have h := native_rejected_error_positive (fun j => -y j) hh hse
    (show 0 ≤ -q - -y s by linarith) hrfit hrreject (fun j hj => by
      simpa only [neg_sub_neg, abs_sub_comm] using hsmall j hj)
  linarith

/-- The selected line's one-step increment vanishes uniformly along every
completed interval in a compact horizon. -/
theorem tendsto_native_slope_step (f : C(ℝ, ℝ)) {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) {ι : Type*} {l : Filter ι}
    {h q m : ι → ℝ} {s e : ι → ℕ} (hh : ∀ i, 0 < h i)
    (hconv : Tendsto h l (𝓝 0))
    (hdata : ∀ᶠ i in l, s i < e i ∧ (e i : ℝ) * h i ≤ T ∧
      |q i - f ((s i : ℝ) * h i)| ≤ ε ∧
      feasibleSlope (Finset.Icc (s i + 1) (e i)) (fun j => (j : ℝ) * h i)
        (fun j => f ((j : ℝ) * h i)) ((s i : ℝ) * h i) (q i) ε (m i) ∧
      ¬ nativePrefixFeasible (fun j => (j : ℝ) * h i)
        (fun j => f ((j : ℝ) * h i)) ε (s i) (e i + 1) (q i)) :
    Tendsto (fun i => |m i| * h i) l (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall (fun i => hb.trans_le (mul_nonneg (abs_nonneg _) (hh i).le))
  · intro b hb
    obtain ⟨δ, hδ, hbound⟩ := exists_uniform_native_slope_step f hT hε hb
    filter_upwards [hdata, hconv.eventually_lt_const hδ] with i hi hhδ
    exact hbound (h i) (hh i) hhδ (s i) (e i) hi.1 hi.2.1 (q i) (m i)
      hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2

/-- Continuity controls all intervening samples, including the rejected one,
when both recording times approach the same limit. -/
theorem eventually_native_small_displacements (f : C(ℝ, ℝ)) {σ ε : ℝ}
    (hε : 0 < ε) {ι : Type*} {l : Filter ι} {h : ι → ℝ} {s e : ι → ℕ}
    (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0))
    (hstart : Tendsto (fun i => (s i : ℝ) * h i) l (𝓝 σ))
    (hfinish : Tendsto (fun i => (e i : ℝ) * h i) l (𝓝 σ)) :
    ∀ᶠ i in l, ∀ j ∈ Finset.Icc (s i + 1) (e i + 1),
      |f ((j : ℝ) * h i) - f ((s i : ℝ) * h i)| < ε := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.continuousAt_iff.mp f.continuous.continuousAt (ε / 2) (half_pos hε)
  have hn : Tendsto (fun i => ((e i + 1 : ℕ) : ℝ) * h i) l (𝓝 σ) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_zero] using hfinish.add hconv
  filter_upwards [hstart.eventually_const_lt (show σ - δ < σ by linarith),
    hstart.eventually_lt_const (show σ < σ + δ by linarith),
    hn.eventually_lt_const (show σ < σ + δ by linarith)] with i hslo hshi hni
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  have hlo : (s i : ℝ) * h i ≤ (j : ℝ) * h i :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast (show s i ≤ j by omega)) (hh i).le
  have hup : (j : ℝ) * h i ≤ ((e i + 1 : ℕ) : ℝ) * h i :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hj'.2) (hh i).le
  have hjdist : dist ((j : ℝ) * h i) σ < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hsdist : dist ((s i : ℝ) * h i) σ < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hjf := hmod hjdist
  have hsf := hmod hsdist
  rw [Real.dist_eq] at hjf hsf
  have hb := abs_sub_le (f ((j : ℝ) * h i)) (f σ) (f ((s i : ℝ) * h i))
  rw [abs_sub_comm (f σ)] at hb
  linarith

/-- A completed segment starting near either boundary ends near the opposite
boundary once its duration vanishes. The line is the actual feasible selected
line, and the first rejection is used with its proved direction. -/
theorem tendsto_native_endpoint_opposite_boundary (f : C(ℝ, ℝ))
    {σ ε η : ℝ} (hσ : 0 ≤ σ) (hε : 0 < ε) (hη : η = ε ∨ η = -ε)
    {ι : Type*} {l : Filter ι} {h q m : ι → ℝ} {s e : ι → ℕ}
    (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0))
    (hstart : Tendsto (fun i => (s i : ℝ) * h i) l (𝓝 σ))
    (hfinish : Tendsto (fun i => (e i : ℝ) * h i) l (𝓝 σ))
    (hanchor : Tendsto (fun i => q i - f ((s i : ℝ) * h i)) l (𝓝 η))
    (hdata : ∀ᶠ i in l, s i < e i ∧ |q i - f ((s i : ℝ) * h i)| ≤ ε ∧
      feasibleSlope (Finset.Icc (s i + 1) (e i)) (fun j => (j : ℝ) * h i)
        (fun j => f ((j : ℝ) * h i)) ((s i : ℝ) * h i) (q i) ε (m i) ∧
      ¬ nativePrefixFeasible (fun j => (j : ℝ) * h i)
        (fun j => f ((j : ℝ) * h i)) ε (s i) (e i + 1) (q i)) :
    Tendsto (fun i => q i + m i * ((e i : ℝ) * h i - (s i : ℝ) * h i) -
      f ((e i : ℝ) * h i)) l (𝓝 (-η)) := by
  have hstep := tendsto_native_slope_step f (show 0 ≤ σ + 1 by linarith) hε hh hconv
    (hdata.and (hfinish.eventually_lt_const (show σ < σ + 1 by linarith)) |>.mono
      (fun i hi => ⟨hi.1.1, hi.2.le, hi.1.2⟩))
  have hn : Tendsto (fun i => ((e i + 1 : ℕ) : ℝ) * h i) l (𝓝 σ) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_zero] using hfinish.add hconv
  have hinc : Tendsto (fun i => |f (((e i + 1 : ℕ) : ℝ) * h i) - f ((e i : ℝ) * h i)|)
      l (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, abs_zero] using
      (((f.continuous.tendsto σ).comp hn).sub ((f.continuous.tendsto σ).comp hfinish)).abs
  have hsmall := eventually_native_small_displacements f hε hh hconv hstart hfinish
  have hbound : ∀ᶠ i in l,
      -ε ≤ q i + m i * ((e i : ℝ) * h i - (s i : ℝ) * h i) - f ((e i : ℝ) * h i) ∧
      q i + m i * ((e i : ℝ) * h i - (s i : ℝ) * h i) - f ((e i : ℝ) * h i) ≤ ε := by
    filter_upwards [hdata] with i hi
    have he := hi.2.2.1 (e i) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
    rw [abs_sub_comm] at he
    exact abs_le.mp he
  have hline (i : ι) :
      q i + m i * (((e i + 1 : ℕ) : ℝ) * h i - (s i : ℝ) * h i) -
        f (((e i + 1 : ℕ) : ℝ) * h i) =
      (q i + m i * ((e i : ℝ) * h i - (s i : ℝ) * h i) - f ((e i : ℝ) * h i)) +
        m i * h i - (f (((e i + 1 : ℕ) : ℝ) * h i) - f ((e i : ℝ) * h i)) := by
    rw [Nat.cast_add, Nat.cast_one]
    ring
  rcases hη with hη | hη
  · rw [hη] at hanchor ⊢
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun i => -ε + (|f (((e i + 1 : ℕ) : ℝ) * h i) - f ((e i : ℝ) * h i)| +
        |m i| * h i)) l (𝓝 (-ε)) by simpa only [add_zero] using (hinc.add hstep).const_add (-ε))
      (hbound.mono (fun _ hi => hi.1))
    filter_upwards [hdata, hsmall, hanchor.eventually_const_lt hε] with i hi hs hpos
    have hrej := native_rejected_error_positive (fun j => f ((j : ℝ) * h i)) (hh i) hi.1
      hpos.le hi.2.2.1 hi.2.2.2 hs
    have h1 := hline i
    have h2 := neg_le_abs (m i * h i)
    have h3 := le_abs_self (f (((e i + 1 : ℕ) : ℝ) * h i) - f ((e i : ℝ) * h i))
    rw [abs_mul, abs_of_pos (hh i)] at h2
    linarith
  · rw [hη] at hanchor ⊢
    simp only [neg_neg]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (show Tendsto (fun i => ε - (|f (((e i + 1 : ℕ) : ℝ) * h i) - f ((e i : ℝ) * h i)| +
        |m i| * h i)) l (𝓝 ε) by simpa only [add_zero, sub_zero] using (hinc.add hstep).const_sub ε)
      tendsto_const_nhds _ (hbound.mono (fun _ hi => hi.2))
    filter_upwards [hdata, hsmall, hanchor.eventually_lt_const (show -ε < 0 by linarith)] with i hi hs hneg
    have hrej := native_rejected_error_negative (fun j => f ((j : ℝ) * h i)) (hh i) hi.1
      hneg.le hi.2.2.1 hi.2.2.2 hs
    have h1 := hline i
    have h2 := le_abs_self (m i * h i)
    have h3 := neg_le_abs (f (((e i + 1 : ℕ) : ℝ) * h i) - f ((e i : ℝ) * h i))
    rw [abs_mul, abs_of_pos (hh i)] at h2
    linarith

end SwingRepair
