import PLAStochastic.Index.KEP.Poisson.OneLayerTransfer
import PLAStochastic.Index.KEP.SpatialBudget

/-!
# Joint finiteness, fixed moment and spatial-error induction

The induction is on the original completed Poisson hierarchy and is restricted
to a monotone spatial cutoff. Every parent window, tail and moment input is
paid by the proved one-layer transfer from the actual child hypothesis.
The remaining scalar conditions are uniform parameter choices, separate from
the probabilistic induction.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

def kepFiniteComparisonConstant (A theta R : ℝ) : ℝ :=
  2 * A + 4 * (A + (2 / (theta / R) ^ 2 * 73) * A ^ 3) + 1

def kepStoppedComparisonConstant (A theta R : ℝ) : ℝ :=
  4 * A + 8 * (A + (Real.sqrt (24 / (theta / R) ^ 4 * 73) /
    (1 - Real.sqrt (1 / 2)) ^ 3) * A ^ 3) + 1

theorem kepFiniteComparisonConstant_pos {A theta R : ℝ} (hA : 0 ≤ A) :
    0 < kepFiniteComparisonConstant A theta R := by
  unfold kepFiniteComparisonConstant
  positivity

theorem kepStoppedComparisonConstant_pos {A theta R : ℝ} (hA : 0 ≤ A) :
    0 < kepStoppedComparisonConstant A theta R := by
  have hs : Real.sqrt (1 / 2 : ℝ) < 1 := (Real.sqrt_lt' one_pos).mpr (by norm_num)
  unfold kepStoppedComparisonConstant
  positivity

theorem kepPoisson_joint_induction {f : ℝ → ℝ}
    {flo fhi L eps theta D drift A delta Kbase : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (htheta : 0 < theta)
    (hD : 0 < D) (hdrift : 0 ≤ drift) (hdriftD : drift ≤ D) (hA : 0 ≤ A)
    (heps : 1 ≤ eps) (hclass : kepReferenceClassicalThreshold ≤ eps)
    (hzero : kepReferenceSpan eps 0 = 1) (hspan : ∀ j, 0 < kepReferenceSpan eps j)
    (hgrowth : ∀ j, kepReferenceSpan eps j ≤ kepReferenceSpan eps (j + 1))
    (href : ∀ j,
      (∀ᵐ z ∂(kepReferenceLaw eps j : Measure ℝ), 0 ≤ z) ∧
      (∫ z, z ∂(kepReferenceLaw eps j : Measure ℝ)) ≤ 1 ∧
      (Integrable (fun z => Real.exp (theta * z)) (kepReferenceLaw eps j : Measure ℝ) ∧
        ∫ z, Real.exp (theta * z) ∂(kepReferenceLaw eps j : Measure ℝ) ≤ 73) ∧
      (Integrable (fun z => Real.exp ((theta / (fhi / flo)) * z)) (kepReferenceLaw eps j : Measure ℝ) ∧
        ∫ z, Real.exp ((theta / (fhi / flo)) * z) ∂(kepReferenceLaw eps j : Measure ℝ) ≤ 73))
    (hKbase : 0 ≤ Kbase) (hKbaseD : Kbase ≤ D)
    (hbase : ∀ n, 1 ≤ n → ∀ x,
      measureHellinger (kepPoissonLayerMeasure hf eps n x 0) (kepReferenceLaw eps 0) ≤ Kbase / n ∧
      Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n x 0) ∧
        ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n x 0 ≤ 73)
    (hstep : ∀ n, 0 < n → ∀ j r,
      (∀ y, measureHellinger (kepPoissonLayerMeasure hf eps n y j) (kepReferenceLaw eps j) ≤ r) →
        ∀ x S, measureHellinger (kepPoissonParentStepKernel hf eps n x j S) (kepReferenceLaw eps j) ≤
          r + (drift * eps ^ 98 * (kepReferenceSpan eps j / n) ^ (2 / 3 : ℝ)) * |S| ^ (2 / 3 : ℝ))
    {M : ℕ} (hM1 : 1 ≤ M) (hM : (M : ℝ) ≤ A * eps ^ 2)
    (hQwindow : ∀ j, (iidLaw (kepReferenceLaw eps j)).real {g | (M : ℕ∞) < gapSegLen eps g} ≤ 1 / 16)
    (hQtail : ∀ j k, (iidLaw (kepReferenceLaw eps j)).real
      {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps g} ≤ (1 / 2 : ℝ) ^ k)
    (hdeltaWindow : kepFiniteComparisonConstant A theta (fhi / flo) * (D + drift) * delta ≤ 1 / 4)
    (hdeltaMean : D * delta * Real.sqrt (8 * 73 / theta ^ 2) ≤ 1)
    (hC : ∀ j, 0 < lawC eps (kepReferenceLaw eps j))
    (hsmall : ∀ j, 2 * theta / lawC eps (kepReferenceLaw eps j) ≤ (theta / (fhi / flo)) / 2)
    (hcost : ∀ j, 8 * 73 / (theta / (fhi / flo)) ^ 2 *
      (2 * theta / lawC eps (kepReferenceLaw eps j)) ≤ fhi / flo)
    (hscale : ∀ j, (3 * (fhi / flo) * (2 * theta / lawC eps (kepReferenceLaw eps j))) * M ≤ 1 / 144)
    (hdom : ∀ j, 2 * kepStoppedComparisonConstant A theta (fhi / flo) * eps ≤
      (lawC eps (kepReferenceLaw eps j)) ^ (2 / 3 : ℝ)) :
    ∀ n : ℝ, 1 ≤ n → ∀ j : ℕ, kepSpatialCutoff eps n j ≤ delta →
      (∀ x, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x j 1 g ≠ ⊤) ∧
      (∀ x, Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n x j) ∧
        ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n x j ≤ 73) ∧
      ∀ x, measureHellinger (kepPoissonLayerMeasure hf eps n x j) (kepReferenceLaw eps j) ≤
        kepSpatialError D eps n j := by
  intro n hn
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  intro j
  induction j with
  | zero =>
    intro _hcut
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact Filter.Eventually.of_forall fun g => by
        simp only [kepPoissonPivot, completedPivot_zero_layer]
        exact ENat.natCast_ne_top 1
    · intro x
      exact ⟨(hbase n hn x).2.1, (hbase n hn x).2.2⟩
    · intro x
      apply (hbase n hn x).1.trans
      unfold kepSpatialError
      rw [hzero]
      exact kep_base_spatial_error heps hn hKbase hKbaseD
  | succ j ih =>
    intro hcut
    have hcutChild : kepSpatialCutoff eps n j ≤ delta :=
      (kepSpatialCutoff_mono hn0 (hspan j).le (hgrowth j)).trans hcut
    obtain ⟨hfin, hchild, herr⟩ := ih hcutChild
    let q := (kepReferenceSpan eps j / n) ^ (2 / 3 : ℝ)
    let r := kepSpatialError D eps n j
    let b := drift * eps ^ 98 * q
    have hq : 0 ≤ q := Real.rpow_nonneg (div_nonneg (hspan j).le hn0.le) _
    have hr : 0 ≤ r := by dsimp [r, kepSpatialError]; positivity
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have h100 : eps ^ 100 * q ≤ delta := kep_spatial_cutoff_lower_powers heps hq hcutChild 100 (by omega)
    have h101 : eps ^ 101 * q ≤ delta := kep_spatial_cutoff_lower_powers heps hq hcutChild 101 (by omega)
    have hcomb : eps * r + eps ^ 3 * b = (D + drift) * eps ^ 101 * q := by
      dsimp [r, kepSpatialError, b, q]
      ring
    have hwindow : kepFiniteComparisonConstant A theta (fhi / flo) *
        (eps * r + eps ^ 3 * b) ≤ 1 / 4 := by
      rw [hcomb]
      have h := mul_le_mul_of_nonneg_left h101
        (mul_nonneg (kepFiniteComparisonConstant_pos (theta := theta) (R := fhi / flo) hA).le
          (by positivity : 0 ≤ D + drift))
      calc
        _ ≤ kepFiniteComparisonConstant A theta (fhi / flo) * (D + drift) * delta := by
          simpa only [mul_assoc] using h
        _ ≤ _ := hdeltaWindow
    have hmean : r * Real.sqrt (8 * 73 / theta ^ 2) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h100 hD.le)
        (Real.sqrt_nonneg (8 * 73 / theta ^ 2))
      calc
        _ ≤ D * delta * Real.sqrt (8 * 73 / theta ^ 2) := by
          simpa only [r, kepSpatialError, q, mul_assoc] using h
        _ ≤ _ := hdeltaMean
    have ht := kepPoisson_joint_one_layer_transfer hf hn0 htheta hr hb hA heps hclass j M hM1 hM
      (hspan j) hfin hchild herr (href j).1 (href j).2.1 (href j).2.2.1 (href j).2.2.2
      (hstep n hn0 j r herr) (hQwindow j) (hQtail j) hwindow hmean (hC j)
      (hsmall j) (hcost j) (hscale j)
    refine ⟨ht.1, ht.2.1, ?_⟩
    intro x
    apply (ht.2.2.1 x).trans
    change kepStoppedComparisonConstant A theta (fhi / flo) * (eps * r + eps ^ 3 * b) ≤ _
    rw [hcomb]
    have hK : 0 ≤ kepStoppedComparisonConstant A theta (fhi / flo) :=
      (kepStoppedComparisonConstant_pos hA).le
    have h1 : kepStoppedComparisonConstant A theta (fhi / flo) *
        (D + drift) * eps ^ 101 * q ≤
          (2 * kepStoppedComparisonConstant A theta (fhi / flo) * eps) * D * eps ^ 100 * q := by
      calc
        _ ≤ kepStoppedComparisonConstant A theta (fhi / flo) * (2 * D) * eps ^ 101 * q := by gcongr; linarith
        _ = _ := by ring
    have h2 := mul_le_mul_of_nonneg_right (hdom j)
      (mul_nonneg (mul_nonneg hD.le (by positivity : 0 ≤ eps ^ 100)) hq)
    have he : kepSpatialError D eps n (j + 1) =
        (lawC eps (kepReferenceLaw eps j)) ^ (2 / 3 : ℝ) * D * eps ^ 100 * q := by
      unfold kepSpatialError
      rw [kepReferenceSpan_succ_mul_lawC hclass j,
        kep_two_thirds_parent_scale (hspan j).le (hC j).le hn0]
      dsimp [q]
      ring
    rw [he]
    simpa only [mul_assoc] using h1.trans (by simpa only [mul_assoc] using h2)

end

end PGM
