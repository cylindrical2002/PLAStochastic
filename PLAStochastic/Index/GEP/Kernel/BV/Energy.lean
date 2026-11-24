import PLAStochastic.Index.GEP.SurvivalBound.KilledRow.RegularClass

/-!
# Fourier dissipation for the actual killed operator

The energy below is the low-frequency quadratic energy used in
`research/2026-09-28-gep-closure/kernel-bv.md`, in mathlib's Fourier convention.
The interval projections remain inside every iterate. In particular, no Fourier
multiplier formula for powers of a killed operator is assumed.

This file proves the dissipation and small-energy-time parts of the BV strategy.
It does not assert that an arbitrary killed row itself has bounded variation.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory FourierTransform Set
open scoped BigOperators

/-- The bounded Fourier energy that measures low-frequency spatial regularity. -/
def kBVEnergy (u : ℝ → ℂ) : ℝ :=
  ∫ ξ, min (ξ ^ 2) 1 * ‖𝓕 u ξ‖ ^ 2

/-- The squared Lebesgue `L²` norm, written as an ordinary integral. -/
def kBVNormSq (u : ℝ → ℂ) : ℝ := ∫ y, ‖u y‖ ^ 2

theorem kBVEnergy_nonneg (u : ℝ → ℂ) : 0 ≤ kBVEnergy u :=
  integral_nonneg fun _ => mul_nonneg (le_min (sq_nonneg _) zero_le_one) (sq_nonneg _)

theorem kBVNormSq_nonneg (u : ℝ → ℂ) : 0 ≤ kBVNormSq u :=
  integral_nonneg fun _ => sq_nonneg _

theorem kBV_integrable_energy {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    Integrable (fun ξ => min (ξ ^ 2) 1 * ‖𝓕 u ξ‖ ^ 2) := by
  have hF := kill_memLp_two_fourier h1 h2
  have hc := kill_continuous_fourier h1
  have hFsq := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).1 hF
  refine hFsq.mono' (by fun_prop) (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left (sq_nonneg _) (min_le_right _ _)

/-- The energy is finite and is at most the squared `L²` norm. -/
theorem kBVEnergy_le_normSq {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    kBVEnergy u ≤ kBVNormSq u := by
  rw [kBVEnergy, kBVNormSq, ← plancherel_integrable_memLp h1 h2]
  have hFsq := (memLp_two_iff_integrable_sq_norm
    (kill_continuous_fourier h1).aestronglyMeasurable).1 (kill_memLp_two_fourier h1 h2)
  exact integral_mono (kBV_integrable_energy h1 h2) hFsq fun ξ =>
    mul_le_of_le_one_left (sq_nonneg _) (min_le_right _ _)

/-- Fourier dissipation for one actual killed step, including its projection.
The hypothesis is only the scalar Fourier gap of the input step law. -/
theorem kBV_dissipation {J : Set ℝ} {ν σ : Measure ℝ}
    [IsFiniteMeasure ν] [IsFiniteMeasure σ] {z : ℂ} {β a c : ℝ}
    (hgap : ∀ ξ, ‖kMult ν σ z a ξ‖ ^ 2 ≤ 1 - c * min (ξ ^ 2) 1)
    {u : ℝ → ℂ} (hu : Measurable u) (h1 : Integrable u) (h2 : MemLp u 2) :
    c * kBVEnergy u ≤ kBVNormSq u - kBVNormSq (kStepZ J ν σ z β a u) := by
  have hFsq := (memLp_two_iff_integrable_sq_norm
    (kill_continuous_fourier h1).aestronglyMeasurable).1 (kill_memLp_two_fourier h1 h2)
  have hE := kBV_integrable_energy h1 h2
  have hmajor : Integrable (fun ξ => ‖𝓕 u ξ‖ ^ 2 - c * (min (ξ ^ 2) 1 * ‖𝓕 u ξ‖ ^ 2)) :=
    hFsq.sub (hE.const_mul c)
  have hle := integral_norm_kStepZ_sq_le_mult (J := J) (ν := ν) (σ := σ)
    (z := z) (β := β) (a := a) hu h1 h2
  have hbound : (∫ ξ, ‖kMult ν σ z a ξ‖ ^ 2 * ‖𝓕 u ξ‖ ^ 2) ≤
      kBVNormSq u - c * kBVEnergy u := by
    calc (∫ ξ, ‖kMult ν σ z a ξ‖ ^ 2 * ‖𝓕 u ξ‖ ^ 2)
        ≤ ∫ ξ, ‖𝓕 u ξ‖ ^ 2 - c * (min (ξ ^ 2) 1 * ‖𝓕 u ξ‖ ^ 2) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => by positivity)
            hmajor (Filter.Eventually.of_forall fun ξ => ?_)
          have h := mul_le_mul_of_nonneg_right (hgap ξ) (sq_nonneg ‖𝓕 u ξ‖)
          nlinarith
      _ = kBVNormSq u - c * kBVEnergy u := by
        rw [integral_sub hFsq (hE.const_mul c), integral_const_mul,
          plancherel_integrable_memLp h1 h2]
        rfl
  change _ ≤ _ - (∫ y, ‖kStepZ J ν σ z β a u y‖ ^ 2)
  linarith

/-- A finite energy budget follows by telescoping actual one-step dissipation. -/
theorem kBV_sum_energy_le {E H : ℕ → ℝ} {c : ℝ}
    (hstep : ∀ j, c * E j ≤ H j - H (j + 1)) (m N : ℕ) :
    c * (∑ j ∈ Finset.range N, E (m + j)) ≤ H m - H (m + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add]
    have h := hstep (m + N)
    simpa only [Nat.add_succ] using add_le_add ih h |>.trans_eq (by ring)

/-- Some state in every nonempty time window has small energy. This is the
pigeonhole step yielding the factor `N⁻¹` in the BV proof. -/
theorem kBV_exists_small_energy {E H : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hH : ∀ j, 0 ≤ H j) (hstep : ∀ j, c * E j ≤ H j - H (j + 1))
    (m N : ℕ) (hN : 0 < N) :
    ∃ j < N, E (m + j) ≤ H m / (c * N) := by
  have hsum := kBV_sum_energy_le hstep m N
  have hsum' : c * (∑ j ∈ Finset.range N, E (m + j)) ≤ H m := by
    linarith [hH (m + N)]
  by_contra h
  push Not at h
  have hlt : ∑ j ∈ Finset.range N, H m / (c * N) < ∑ j ∈ Finset.range N, E (m + j) := by
    exact Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN))
      fun j hj => h j (Finset.mem_range.mp hj)
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have heq : (∑ j ∈ Finset.range N, H m / (c * N)) = H m / c := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [heq] at hlt
  have := (div_lt_iff₀ hc).mp hlt
  nlinarith

/-- Every iterate of a killed finite-measure convolution preserves `L¹ ∩ L²`.
This fact supplies the domain conditions in each dissipation step. -/
theorem kBV_iterate_regular {J : Set ℝ} (hJ : MeasurableSet J)
    {ν σ : Measure ℝ} [IsFiniteMeasure ν] [IsFiniteMeasure σ]
    (z : ℂ) (β a : ℝ) {u : ℝ → ℂ}
    (hu : Measurable u) (h1 : Integrable u) (h2 : MemLp u 2) (n : ℕ) :
    Measurable ((kStepZ J ν σ z β a)^[n] u) ∧
      Integrable ((kStepZ J ν σ z β a)^[n] u) ∧
      MemLp ((kStepZ J ν σ z β a)^[n] u) 2 := by
  induction n with
  | zero => exact ⟨hu, h1, h2⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨measurable_kStepZ hJ ih.1, ?_, ?_⟩
    · rw [kStepZ_eq_indicator]
      exact (((integrable_kConv ν ih.1 ih.2.1 β a).const_mul (1 - z)).add
        ((integrable_kConv σ ih.1 ih.2.1 β a).const_mul z)).indicator hJ
    · rw [kStepZ_eq_indicator]
      exact ((((memLp_two_kConv ν ih.1 ih.2.1 ih.2.2 β a).1.const_mul (1 - z)).add
        ((memLp_two_kConv σ ih.1 ih.2.1 ih.2.2 β a).1.const_mul z))).indicator hJ

/-- The dissipative energy budget for actual killed iterates on every time window. -/
theorem kBV_iterate_energy_budget {J : Set ℝ} (hJ : MeasurableSet J)
    {ν σ : Measure ℝ} [IsFiniteMeasure ν] [IsFiniteMeasure σ]
    {z : ℂ} {β a c : ℝ}
    (hgap : ∀ ξ, ‖kMult ν σ z a ξ‖ ^ 2 ≤ 1 - c * min (ξ ^ 2) 1)
    {u : ℝ → ℂ} (hu : Measurable u) (h1 : Integrable u) (h2 : MemLp u 2)
    (m N : ℕ) :
    c * (∑ j ∈ Finset.range N, kBVEnergy ((kStepZ J ν σ z β a)^[m + j] u)) ≤
      kBVNormSq ((kStepZ J ν σ z β a)^[m] u) -
        kBVNormSq ((kStepZ J ν σ z β a)^[m + N] u) := by
  apply kBV_sum_energy_le (E := fun j => kBVEnergy ((kStepZ J ν σ z β a)^[j] u))
    (H := fun j => kBVNormSq ((kStepZ J ν σ z β a)^[j] u))
  intro j
  obtain ⟨hj, hj1, hj2⟩ := kBV_iterate_regular (ν := ν) (σ := σ) hJ z β a hu h1 h2 j
  simpa only [Function.iterate_succ_apply'] using
    kBV_dissipation (J := J) (β := β) hgap hj hj1 hj2

/-- A genuine small-energy state of the killed chain occurs in every nonempty
window. The initial norm is taken at the beginning of the window, so an earlier
spectral-gap estimate can supply the extra exponential decay. -/
theorem kBV_iterate_exists_small_energy {J : Set ℝ} (hJ : MeasurableSet J)
    {ν σ : Measure ℝ} [IsFiniteMeasure ν] [IsFiniteMeasure σ]
    {z : ℂ} {β a c : ℝ} (hc : 0 < c)
    (hgap : ∀ ξ, ‖kMult ν σ z a ξ‖ ^ 2 ≤ 1 - c * min (ξ ^ 2) 1)
    {u : ℝ → ℂ} (hu : Measurable u) (h1 : Integrable u) (h2 : MemLp u 2)
    (m N : ℕ) (hN : 0 < N) :
    ∃ j < N, kBVEnergy ((kStepZ J ν σ z β a)^[m + j] u) ≤
      kBVNormSq ((kStepZ J ν σ z β a)^[m] u) / (c * N) := by
  apply kBV_exists_small_energy
    (E := fun j => kBVEnergy ((kStepZ J ν σ z β a)^[j] u))
    (H := fun j => kBVNormSq ((kStepZ J ν σ z β a)^[j] u))
    hc (fun _ => kBVNormSq_nonneg _) _ m N hN
  intro j
  obtain ⟨hj, hj1, hj2⟩ := kBV_iterate_regular (ν := ν) (σ := σ) hJ z β a hu h1 h2 j
  simpa only [Function.iterate_succ_apply'] using
    kBV_dissipation (J := J) (β := β) hgap hj hj1 hj2

/-- The regular input class supplies the Fourier gap needed by the energy lemma,
with a constant independent of the interval and of every slope `|a| ≥ 1/2`. -/
theorem kBV_regLaw_mult_gap {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {a : ℝ} (ha : 1 / 2 ≤ |a|) (ξ : ℝ) :
    ‖kMult (ν : Measure ℝ) (ν : Measure ℝ) 0 a ξ‖ ^ 2 ≤
      1 - killCnu D vlo vhi * min (ξ ^ 2) 1 := by
  have h := kill_regLaw_charFun_gap hD hθ hvlo hν (a := 1) (by norm_num)
    (-(2 * Real.pi * a * ξ))
  simp only [one_mul] at h
  have hc : 0 ≤ killCnu D vlo vhi :=
    (killCnu_pos hD hvlo (hν.var_ge.trans hν.var_le)).le
  have ha2 : (1 / 2 : ℝ) ^ 2 ≤ a ^ 2 := by
    have hh := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (abs_nonneg a)).2 ha
    simpa only [sq_abs] using hh
  have hscale : 1 ≤ 4 * Real.pi ^ 2 * a ^ 2 := by
    calc 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      _ = 4 * Real.pi ^ 2 * (1 / 2 : ℝ) ^ 2 := by ring
      _ ≤ 4 * Real.pi ^ 2 * a ^ 2 := by gcongr
  have hs : ξ ^ 2 ≤ (-(2 * Real.pi * a * ξ)) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hscale (sq_nonneg ξ)
    nlinarith only [hh]
  have hmin : min (ξ ^ 2) 1 ≤ min ((-(2 * Real.pi * a * ξ)) ^ 2) 1 := min_le_min_right _ hs
  have hp := mul_le_mul_of_nonneg_left hmin hc
  simp only [kMult, sub_zero, one_mul, zero_mul, add_zero]
  linarith

/-- Small-energy states for the real killed kernel are proved directly from
`RegLaw`; no regularity or dissipation hypothesis on the kernel is added. -/
theorem kBV_regLaw_exists_small_energy {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {J : Set ℝ} (hJ : MeasurableSet J)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {u : ℝ → ℂ}
    (hu : Measurable u) (h1 : Integrable u) (h2 : MemLp u 2)
    (m N : ℕ) (hN : 0 < N) :
    ∃ j < N, kBVEnergy ((kStep J (ν : Measure ℝ) β a)^[m + j] u) ≤
      kBVNormSq ((kStep J (ν : Measure ℝ) β a)^[m] u) /
        (killCnu D vlo vhi * N) := by
  have h := kBV_iterate_exists_small_energy hJ
    (killCnu_pos hD hvlo (hν.var_ge.trans hν.var_le))
    (kBV_regLaw_mult_gap hD hθ hvlo hν ha) hu h1 h2 m N hN (β := β)
  have heq : kStepZ J (ν : Measure ℝ) (ν : Measure ℝ) 0 β a =
      kStep J (ν : Measure ℝ) β a := by funext v y; simp [kStepZ]
  simpa only [heq] using h

end
end PGM
