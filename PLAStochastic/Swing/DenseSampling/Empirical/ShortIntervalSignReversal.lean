import PLAStochastic.Swing.DenseSampling.Empirical.LimitingBoundarySign

/-! # Uniform sign reversal on all short native intervals -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def nativePolarity (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

theorem nativePolarity_values (x : ℝ) : nativePolarity x = 1 ∨ nativePolarity x = -1 := by
  unfold nativePolarity
  split_ifs <;> simp

theorem nativePolarity_abs (x : ℝ) : |nativePolarity x| = 1 := by
  rcases nativePolarity_values x with h | h <;> rw [h] <;> norm_num

theorem nativePolarity_distance {x : ℝ} (hx : |x| ≤ 1) :
    |x - nativePolarity x| = 1 - |x| := by
  unfold nativePolarity
  by_cases h : 0 ≤ x
  · rw [if_pos h, abs_of_nonneg h, abs_of_nonpos (by linarith [(abs_le.mp hx).2] : x - 1 ≤ 0)]
    ring
  · rw [if_neg h, abs_of_nonpos (le_of_not_ge h),
      abs_of_nonneg (by linarith [(abs_le.mp hx).1] : 0 ≤ x - -1)]
    ring

/-- A single path modulus and mesh cutoff work simultaneously over every
completed segment. Short segments reverse the inherited error's sign. -/
theorem exists_uniform_native_short_sign_flip (f : C(ℝ, ℝ)) {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → ∀ s e : ℕ,
      s < e → (e : ℝ) * h ≤ T → ((e : ℝ) * h - (s : ℝ) * h) < ρ →
      ∀ q m : ℝ, |q - f ((s : ℝ) * h)| ≤ ε →
      feasibleSlope (Finset.Icc (s + 1) e) (fun j => (j : ℝ) * h)
        (fun j => f ((j : ℝ) * h)) ((s : ℝ) * h) q ε m →
      (¬ nativePrefixFeasible (fun j => (j : ℝ) * h)
        (fun j => f ((j : ℝ) * h)) ε s (e + 1) q) →
      nativePolarity (q + m * ((e : ℝ) * h - (s : ℝ) * h) - f ((e : ℝ) * h)) =
        -nativePolarity (q - f ((s : ℝ) * h)) := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous (f := f) f.continuous.continuousOn
    (s := Icc (0 : ℝ) (T + 1))
  obtain ⟨d, hd, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  obtain ⟨d₁, hd₁, hmod₁⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 4) (by positivity)
  obtain ⟨d₂, hd₂, hslope⟩ := exists_uniform_native_slope_step f hT hε (show 0 < ε / 4 by positivity)
  refine ⟨d / 2, min d₂ (min 1 (min (d / 2) d₁)), half_pos hd,
    lt_min hd₂ (lt_min zero_lt_one (lt_min (half_pos hd) hd₁)), ?_⟩
  intro h hh hhδ s e hse heT hshort q m hq hfit hrej
  have hh₂ : h < d₂ := hhδ.trans_le (min_le_left _ _)
  have hh1 : h < 1 := hhδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhd : h < d / 2 := hhδ.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhd₁ : h < d₁ := hhδ.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hnmem : ((e + 1 : ℕ) : ℝ) * h ∈ Icc (0 : ℝ) (T + 1) := by
    rw [Nat.cast_add, Nat.cast_one]
    constructor
    · positivity
    · nlinarith
  have hsmem : (s : ℝ) * h ∈ Icc (0 : ℝ) (T + 1) := by
    constructor
    · positivity
    · have hes : (s : ℝ) ≤ e := by exact_mod_cast hse.le
      nlinarith
  have hemem : (e : ℝ) * h ∈ Icc (0 : ℝ) (T + 1) := ⟨by positivity, by linarith⟩
  have hsmall : ∀ j ∈ Finset.Icc (s + 1) (e + 1), |f ((j : ℝ) * h) - f ((s : ℝ) * h)| < ε := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have hsj : (s : ℝ) ≤ j := by exact_mod_cast (show s ≤ j by omega)
    have hje : (j : ℝ) ≤ (e : ℝ) + 1 := by exact_mod_cast hj'.2
    have hjmem : (j : ℝ) * h ∈ Icc (0 : ℝ) (T + 1) := by
      constructor
      · positivity
      · rw [Nat.cast_add, Nat.cast_one] at hnmem
        nlinarith [hnmem.2]
    have hjdist : dist ((j : ℝ) * h) ((s : ℝ) * h) < d := by
      rw [Real.dist_eq, abs_of_nonneg (by nlinarith : 0 ≤ (j : ℝ) * h - (s : ℝ) * h)]
      nlinarith
    simpa only [Real.dist_eq] using hmod _ hjmem _ hsmem hjdist
  have hindist : dist (((e + 1 : ℕ) : ℝ) * h) ((e : ℝ) * h) < d₁ := by
    rw [Real.dist_eq, Nat.cast_add, Nat.cast_one]
    have heq : ((e : ℝ) + 1) * h - (e : ℝ) * h = h := by ring
    rw [heq, abs_of_pos hh]
    exact hhd₁
  have hinc : |f (((e + 1 : ℕ) : ℝ) * h) - f ((e : ℝ) * h)| < ε / 4 := by
    simpa only [Real.dist_eq] using hmod₁ _ hnmem _ hemem hindist
  have hstep := hslope h hh hh₂ s e hse heT q m hq hfit hrej
  have hline : q + m * (((e + 1 : ℕ) : ℝ) * h - (s : ℝ) * h) - f (((e + 1 : ℕ) : ℝ) * h) =
      q + m * ((e : ℝ) * h - (s : ℝ) * h) - f ((e : ℝ) * h) +
        m * h - (f (((e + 1 : ℕ) : ℝ) * h) - f ((e : ℝ) * h)) := by
    rw [Nat.cast_add, Nat.cast_one]
    ring
  by_cases hsign : 0 ≤ q - f ((s : ℝ) * h)
  · have hr := native_rejected_error_positive _ hh hse hsign hfit hrej hsmall
    have hmp := neg_le_abs (m * h)
    rw [abs_mul, abs_of_pos hh] at hmp
    have hip := le_abs_self (f (((e + 1 : ℕ) : ℝ) * h) - f ((e : ℝ) * h))
    have hout : q + m * ((e : ℝ) * h - (s : ℝ) * h) - f ((e : ℝ) * h) < 0 := by linarith
    simp only [nativePolarity, if_pos hsign, if_neg hout.not_ge]
  · have hr := native_rejected_error_negative _ hh hse (le_of_not_ge hsign) hfit hrej hsmall
    have hmp := le_abs_self (m * h)
    rw [abs_mul, abs_of_pos hh] at hmp
    have hip := neg_le_abs (f (((e + 1 : ℕ) : ℝ) * h) - f ((e : ℝ) * h))
    have hout : 0 < q + m * ((e : ℝ) * h - (s : ℝ) * h) - f ((e : ℝ) * h) := by linarith
    simp only [nativePolarity, if_neg hsign, if_pos hout.le, neg_neg]

end SwingRepair
