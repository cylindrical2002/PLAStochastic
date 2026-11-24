import PLAStochastic.Swing.Algorithm.FeasibleSlope
import Mathlib.Tactic

/-!
# The constrained least-squares choice in native Swing

The anchor is the previous fitted recording, which may differ from the true
sample. The loss sums only over the supplied accepted observations. Its unique
minimizer in a nonempty feasible slope interval is exactly the manuscript's
clipped least-squares coefficient.
-/

namespace SwingRepair

noncomputable section

def nativeSSE {ι : Type*} (samples : Finset ι) (t y : ι → ℝ)
    (anchorTime anchorValue slope : ℝ) : ℝ :=
  ∑ i ∈ samples, (y i - anchorValue - slope * (t i - anchorTime)) ^ 2

def nativeSSECross {ι : Type*} (samples : Finset ι) (t y : ι → ℝ)
    (anchorTime anchorValue : ℝ) : ℝ :=
  ∑ i ∈ samples, (t i - anchorTime) * (y i - anchorValue)

def nativeSSETimeSquare {ι : Type*} (samples : Finset ι) (t : ι → ℝ)
    (anchorTime : ℝ) : ℝ := ∑ i ∈ samples, (t i - anchorTime) ^ 2

def nativeLeastSquares {ι : Type*} (samples : Finset ι) (t y : ι → ℝ)
    (anchorTime anchorValue : ℝ) : ℝ :=
  nativeSSECross samples t y anchorTime anchorValue / nativeSSETimeSquare samples t anchorTime

def nativeClippedSlope (lower upper coefficient : ℝ) : ℝ :=
  max lower (min coefficient upper)

theorem nativeSSETimeSquare_positive {ι : Type*} {samples : Finset ι}
    {t : ι → ℝ} {anchorTime : ℝ} (hne : samples.Nonempty)
    (ht : ∀ i ∈ samples, anchorTime < t i) :
    0 < nativeSSETimeSquare samples t anchorTime := by
  obtain ⟨i, hi⟩ := hne
  apply Finset.sum_pos'
  · intro j _
    exact sq_nonneg _
  · exact ⟨i, hi, sq_pos_of_pos (sub_pos.mpr (ht i hi))⟩

theorem nativeSSE_quadratic {ι : Type*} (samples : Finset ι) (t y : ι → ℝ)
    (a q m : ℝ) :
    nativeSSE samples t y a q m = nativeSSE samples t y a q 0 -
      2 * m * nativeSSECross samples t y a q + m ^ 2 * nativeSSETimeSquare samples t a := by
  unfold nativeSSE nativeSSECross nativeSSETimeSquare
  simp only [zero_mul, sub_zero]
  calc
    _ = ∑ i ∈ samples, ((y i - q) ^ 2 - 2 * m * ((t i - a) * (y i - q)) +
        m ^ 2 * (t i - a) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.mul_sum]

theorem nativeSSE_completed_square {ι : Type*} (samples : Finset ι) (t y : ι → ℝ)
    (a q m : ℝ) (hD : nativeSSETimeSquare samples t a ≠ 0) :
    nativeSSE samples t y a q m =
      nativeSSE samples t y a q (nativeLeastSquares samples t y a q) +
        nativeSSETimeSquare samples t a * (m - nativeLeastSquares samples t y a q) ^ 2 := by
  rw [nativeSSE_quadratic samples t y a q m,
    nativeSSE_quadratic samples t y a q (nativeLeastSquares samples t y a q)]
  unfold nativeLeastSquares
  field_simp
  ring

theorem nativeClippedSlope_mem {L U A : ℝ} (hLU : L ≤ U) :
    nativeClippedSlope L U A ∈ Set.Icc L U := by
  exact ⟨le_max_left _ _, max_le hLU (min_le_right _ _)⟩

theorem nativeClippedSlope_distance_minimal {L U A m : ℝ}
    (hm : m ∈ Set.Icc L U) :
    (nativeClippedSlope L U A - A) ^ 2 ≤ (m - A) ^ 2 := by
  have hLU := hm.1.trans hm.2
  unfold nativeClippedSlope
  by_cases hAL : A ≤ L
  · rw [min_eq_left (hAL.trans hLU), max_eq_left hAL]
    nlinarith [sq_nonneg (m - L), mul_nonneg (sub_nonneg.mpr hm.1) (sub_nonneg.mpr hAL)]
  · by_cases hUA : U ≤ A
    · rw [min_eq_right hUA, max_eq_right hLU]
      nlinarith [sq_nonneg (U - m), mul_nonneg (sub_nonneg.mpr hm.2) (sub_nonneg.mpr hUA)]
    · rw [min_eq_left (le_of_not_ge hUA), max_eq_right (le_of_not_ge hAL), sub_self, zero_pow (by decide)]
      exact sq_nonneg _

theorem nativeClippedSlope_distance_eq_iff {L U A m : ℝ}
    (hm : m ∈ Set.Icc L U) :
    (m - A) ^ 2 = (nativeClippedSlope L U A - A) ^ 2 ↔ m = nativeClippedSlope L U A := by
  constructor
  · intro heq
    have hLU := hm.1.trans hm.2
    unfold nativeClippedSlope at *
    by_cases hAL : A ≤ L
    · rw [min_eq_left (hAL.trans hLU), max_eq_left hAL] at *
      nlinarith [mul_nonneg (sub_nonneg.mpr hm.1) (sub_nonneg.mpr hAL)]
    · by_cases hUA : U ≤ A
      · rw [min_eq_right hUA, max_eq_right hLU] at *
        nlinarith [mul_nonneg (sub_nonneg.mpr hm.2) (sub_nonneg.mpr hUA)]
      · rw [min_eq_left (le_of_not_ge hUA), max_eq_right (le_of_not_ge hAL)] at heq ⊢
        simp only [sub_self, zero_pow (by decide : 2 ≠ 0)] at heq
        nlinarith [sq_nonneg (m - A)]
  · intro h
    rw [h]

/-- The literal clipped formula minimizes the actual finite accepted-prefix SSE. -/
theorem nativeSSE_clipped_minimal {ι : Type*} {samples : Finset ι} {t y : ι → ℝ}
    {a q L U m : ℝ} (hne : samples.Nonempty) (ht : ∀ i ∈ samples, a < t i)
    (hm : m ∈ Set.Icc L U) :
    nativeSSE samples t y a q (nativeClippedSlope L U (nativeLeastSquares samples t y a q)) ≤
      nativeSSE samples t y a q m := by
  have hD := nativeSSETimeSquare_positive hne ht
  have h₁ := nativeSSE_completed_square samples t y a q
    (nativeClippedSlope L U (nativeLeastSquares samples t y a q)) hD.ne'
  have h₂ := nativeSSE_completed_square samples t y a q m hD.ne'
  have hd := mul_le_mul_of_nonneg_left
    (nativeClippedSlope_distance_minimal (A := nativeLeastSquares samples t y a q) hm) hD.le
  linarith

/-- There is exactly one constrained SSE minimizing slope whenever a nonempty prefix has positive times. -/
theorem nativeSSE_clipped_unique {ι : Type*} {samples : Finset ι} {t y : ι → ℝ}
    {a q L U m : ℝ} (hne : samples.Nonempty) (ht : ∀ i ∈ samples, a < t i)
    (hm : m ∈ Set.Icc L U)
    (heq : nativeSSE samples t y a q m =
      nativeSSE samples t y a q (nativeClippedSlope L U (nativeLeastSquares samples t y a q))) :
    m = nativeClippedSlope L U (nativeLeastSquares samples t y a q) := by
  have hD := nativeSSETimeSquare_positive hne ht
  have h₁ := nativeSSE_completed_square samples t y a q
    (nativeClippedSlope L U (nativeLeastSquares samples t y a q)) hD.ne'
  have h₂ := nativeSSE_completed_square samples t y a q m hD.ne'
  apply (nativeClippedSlope_distance_eq_iff hm).mp
  nlinarith

end

end SwingRepair
