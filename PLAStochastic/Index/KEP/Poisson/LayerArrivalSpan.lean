import PLAStochastic.Index.KEP.Poisson.LayerObjects
import PLAStochastic.Index.KEP.Poisson.CompletedStopping
import PLAStochastic.Index.GEP.RawDisc.Telescoping

/-!
# The normalized actual layer gap controls its integrated arrival span

On every finite completed leading block the original normalized gap lies
between the density-ratio bounds times the exponential arrival sum at its
base rank. This connects the proved layer moments to physical window events.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepPoissonLayerGap_arrival_bracket {f : ℝ → ℝ} {flo fhi L eps n x : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (j : ℕ)
    (hm : 0 < kepReferenceSpan eps j) {g : ℕ → ℝ} (hg : ∀ i, 0 ≤ g i)
    {r : ℕ} (hr : kepPoissonPivot hf eps n x j 1 g = r) :
    (flo / fhi) * (gapKeys g r / kepReferenceSpan eps j) ≤
        kepPoissonLayerGap hf eps n x j g ∧
      kepPoissonLayerGap hf eps n x j g ≤
        (fhi / flo) * (gapKeys g r / kepReferenceSpan eps j) := by
  have hunit : 0 ≤ n * f x / kepReferenceSpan eps j :=
    div_nonneg (mul_nonneg hn.le (hf.f_pos x).le) hm.le
  have hgap := kepPoissonArrival_gap_bracket hf hn (gapKeys_nonneg hg r) x
  rw [kepPoissonLayerGap_eq_pivot,
    kepPoissonPivot_eq_original_of_finite hf hr]
  change _ ≤ (n * f x / kepReferenceSpan eps j) *
      (kepPoissonArrival hf n x (gapKeys g r) - x) ∧
    (n * f x / kepReferenceSpan eps j) *
      (kepPoissonArrival hf n x (gapKeys g r) - x) ≤ _
  have hG : 0 ≤ gapKeys g r / kepReferenceSpan eps j :=
    div_nonneg (gapKeys_nonneg hg r) hm.le
  constructor
  · calc
      _ ≤ (f x / fhi) * (gapKeys g r / kepReferenceSpan eps j) := by
        apply mul_le_mul_of_nonneg_right _ hG
        exact div_le_div_of_nonneg_right (hf.lower x) hf.fhi_pos.le
      _ = (n * f x / kepReferenceSpan eps j) * (gapKeys g r / (n * fhi)) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hgap.1 hunit
  · calc
      _ ≤ (n * f x / kepReferenceSpan eps j) * (gapKeys g r / (n * flo)) :=
        mul_le_mul_of_nonneg_left hgap.2 hunit
      _ = (f x / flo) * (gapKeys g r / kepReferenceSpan eps j) := by field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hG
        exact div_le_div_of_nonneg_right (hf.upper x) hf.pos.le

end

end PGM
