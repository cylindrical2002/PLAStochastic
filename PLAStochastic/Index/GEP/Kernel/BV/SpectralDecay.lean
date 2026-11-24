import PLAStochastic.Index.GEP.Kernel.BV.Energy

/-!
# Spectral decay at a small-energy time of the killed chain

The energy bound is derived for actual iterates of `kStepZ` and then specialized
to the real regular-law kernel. The decay originates in the existing killed
spectral gap; it is not a Fourier multiplier formula for powers of that kernel.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- The scalar gap factor is nonnegative in the parameter range used by the chain. -/
theorem kBV_gap_factor_nonneg {c a₀ w : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hw : 1 ≤ w) :
    0 ≤ 1 - killGapConst c a₀ / w ^ 2 := by
  have hk : killGapConst c a₀ ≤ 1 := by
    have hm : c * min (Real.pi ^ 2 * a₀ ^ 2 / 4) 1 ≤ 1 :=
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le).trans (by simpa using hc1)
    unfold killGapConst
    linarith
  have hq : killGapConst c a₀ / w ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  linarith

/-- Squared `L²` norm decay through the actual killed iterates. -/
theorem kBV_iterate_normSq_le_gap {ν σ : Measure ℝ}
    [IsFiniteMeasure ν] [IsFiniteMeasure σ] {z : ℂ} {β a α w c a₀ : ℝ}
    (hw : 1 ≤ w) (hc : 0 < c) (hc1 : c ≤ 1) (ha₀ : 0 < a₀) (ha : a₀ ≤ |a|)
    (hgap : ∀ t : ℝ, ‖(1 - z) * charFun ν t + z * charFun σ t‖ ^ 2 ≤ 1 - c * min (t ^ 2) 1)
    {u : ℝ → ℂ} (hu : Measurable u)
    (hsupp : ∀ y, y ∉ Icc α (α + w) → u y = 0) (h2 : MemLp u 2) (n : ℕ) :
    kBVNormSq ((kStepZ (Icc α (α + w)) ν σ z β a)^[n] u) ≤
      (1 - killGapConst c a₀ / w ^ 2) ^ n * kBVNormSq u := by
  have h1 := kill_integrable_of_support (by simp : volume (Icc α (α + w)) ≠ ⊤) hsupp h2
  have hsup : ∀ j y, y ∉ Icc α (α + w) →
      ((kStepZ (Icc α (α + w)) ν σ z β a)^[j] u) y = 0 := by
    intro j
    cases j with
    | zero => exact hsupp
    | succ j =>
      intro y hy
      rw [Function.iterate_succ_apply']
      exact kStepZ_eq_zero_of_notMem hy
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hn, _, hn2⟩ := kBV_iterate_regular (ν := ν) (σ := σ) measurableSet_Icc z β a hu h1 h2 n
    have hsq := (memLp_two_iff_integrable_sq_norm hn.aestronglyMeasurable).1 hn2
    have hstep := integral_norm_kStepZ_sq_le_gap (β := β) hw hc ha₀ ha hgap hn (hsup n) hsq
    rw [Function.iterate_succ_apply']
    change kBVNormSq (kStepZ _ _ _ _ _ _ _) ≤ _
    calc kBVNormSq (kStepZ _ _ _ _ _ _ _) ≤
        (1 - killGapConst c a₀ / w ^ 2) *
          kBVNormSq ((kStepZ (Icc α (α + w)) ν σ z β a)^[n] u) := hstep
      _ ≤ (1 - killGapConst c a₀ / w ^ 2) *
          ((1 - killGapConst c a₀ / w ^ 2) ^ n * kBVNormSq u) :=
        mul_le_mul_of_nonneg_left ih (kBV_gap_factor_nonneg hc hc1 hw)
      _ = (1 - killGapConst c a₀ / w ^ 2) ^ (n + 1) * kBVNormSq u := by ring

/-- Explicit exponential `L²` decay, including singular direction laws. -/
theorem kBV_iterate_normSq_le_exp {ν σ : Measure ℝ}
    [IsFiniteMeasure ν] [IsFiniteMeasure σ] {z : ℂ} {β a α w c a₀ : ℝ}
    (hw : 1 ≤ w) (hc : 0 < c) (hc1 : c ≤ 1) (ha₀ : 0 < a₀) (ha : a₀ ≤ |a|)
    (hgap : ∀ t : ℝ, ‖(1 - z) * charFun ν t + z * charFun σ t‖ ^ 2 ≤ 1 - c * min (t ^ 2) 1)
    {u : ℝ → ℂ} (hu : Measurable u)
    (hsupp : ∀ y, y ∉ Icc α (α + w) → u y = 0) (h2 : MemLp u 2) (n : ℕ) :
    kBVNormSq ((kStepZ (Icc α (α + w)) ν σ z β a)^[n] u) ≤
      Real.exp (-(killGapConst c a₀ * n / w ^ 2)) * kBVNormSq u := by
  refine (kBV_iterate_normSq_le_gap hw hc hc1 ha₀ ha hgap hu hsupp h2 n).trans ?_
  apply mul_le_mul_of_nonneg_right _ (kBVNormSq_nonneg u)
  have hx : 1 - killGapConst c a₀ / w ^ 2 ≤ Real.exp (-(killGapConst c a₀ / w ^ 2)) := by
    linarith [Real.add_one_le_exp (-(killGapConst c a₀ / w ^ 2))]
  have hpow := pow_le_pow_left₀ (kBV_gap_factor_nonneg hc hc1 hw) hx n
  convert hpow using 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- A regular law produces a small-energy state in any window, with the full
preceding spectral decay. This supplies the `N⁻¹ exp(-c m/w²)` factor in the
low-frequency BV decomposition without any extra hypothesis on the killed kernel. -/
theorem kBV_regLaw_exists_small_energy_exp {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {α w : ℝ} (hw : 1 ≤ w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {u : ℝ → ℂ}
    (hu : Measurable u) (hsupp : ∀ y, y ∉ Icc α (α + w) → u y = 0)
    (h2 : MemLp u 2) (m N : ℕ) (hN : 0 < N) :
    ∃ j < N, kBVEnergy ((kStep (Icc α (α + w)) (ν : Measure ℝ) β a)^[m + j] u) ≤
      Real.exp (-(killGapConst (killCnu D vlo vhi) (1 / 2) * m / w ^ 2)) *
        kBVNormSq u / (killCnu D vlo vhi * N) := by
  have hc := killCnu_pos hD hvlo (hν.var_ge.trans hν.var_le)
  have hphysical (t : ℝ) : ‖charFun (ν : Measure ℝ) t‖ ^ 2 ≤
      1 - killCnu D vlo vhi * min (t ^ 2) 1 := by
    have h := kill_regLaw_charFun_gap hD hθ hvlo hν (a := 1) (by norm_num) t
    simp only [one_mul] at h
    linarith
  have hc1 : killCnu D vlo vhi ≤ 1 := by
    have h := hphysical 1
    norm_num only [one_pow, min_self] at h
    nlinarith [sq_nonneg ‖charFun (ν : Measure ℝ) 1‖]
  have hgap (t : ℝ) : ‖(1 - (0 : ℂ)) * charFun (ν : Measure ℝ) t +
      0 * charFun (ν : Measure ℝ) t‖ ^ 2 ≤ 1 - killCnu D vlo vhi * min (t ^ 2) 1 := by
    simpa using hphysical t
  have h1 := kill_integrable_of_support (by simp : volume (Icc α (α + w)) ≠ ⊤) hsupp h2
  obtain ⟨j, hj, hE⟩ := kBV_regLaw_exists_small_energy hD hθ hvlo hν measurableSet_Icc
    β ha hu h1 h2 m N hN
  refine ⟨j, hj, hE.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hnorm := kBV_iterate_normSq_le_exp (β := β) hw hc hc1 (a₀ := 1 / 2) (by norm_num)
    ha hgap hu hsupp h2 m
  have heq : kStepZ (Icc α (α + w)) (ν : Measure ℝ) (ν : Measure ℝ) 0 β a =
      kStep (Icc α (α + w)) (ν : Measure ℝ) β a := by funext v y; simp [kStepZ]
  simpa only [heq] using hnorm

end
end PGM
