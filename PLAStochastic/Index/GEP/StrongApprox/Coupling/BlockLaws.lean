import PLAStochastic.Index.GEP.StrongApprox.Coupling.IIDExtension
import PLAStochastic.Index.GEP.StrongApprox.Coupling.WalkTails
import PLAStochastic.Index.GEP.StrongApprox.Saddle.DyadicKernelLaws
import PLAStochastic.Index.Model.BlockGaps

/-! # Actual iid block statistics consumed by the dyadic coupling

These laws permit lifting the finite leaf coupling directly to the original
infinite gap and Gaussian sequences.
-/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Function
open scoped NNReal ENNReal

/-- The first `L` consecutive sums of `m` increments. -/
def saBlockTotals (m L : ℕ) (x : ℕ → ℝ) (j : Fin L) : ℝ :=
  ∑ i ∈ Finset.range m, x ((j : ℕ) * m + i)

theorem measurable_saBlockTotals (m L : ℕ) : Measurable (saBlockTotals m L) :=
  measurable_pi_lambda _ fun _ => Finset.measurable_sum _ fun _ _ => measurable_pi_apply _

/-- Leaf prefixes are exactly the original walk at block endpoints. -/
theorem saBlockTotals_prefix (m L : ℕ) (x : ℕ → ℝ) {k : ℕ} (hk : k ≤ L) :
    vkeys (saBlockTotals m L x) k = gapKeys x (k * m) := by
  change vkeys (fun j : Fin L => seq (blockGap gapCoord m) x j) k = _
  rw [vkeys_eq_gapKeys _ hk, gapKeys_blockGap]
  rfl

/-- Disjoint block totals have their full finite iid convolution-power law. -/
theorem saBlockTotals_law (ν : ProbabilityMeasure ℝ) (m L : ℕ) :
    (iidLaw ν).map (saBlockTotals m L) =
      Measure.pi (fun _ : Fin L => convPow (ν : Measure ℝ) m) := by
  let β : ProbabilityMeasure ℝ := ⟨convPow (ν : Measure ℝ) m, inferInstance⟩
  have hbase : (iidLaw ν).map (blockGap gapCoord m 0) = (β : Measure ℝ) := by
    change (iidLaw ν).map (fun x => ∑ i ∈ Finset.range m, x (0 * m + i)) =
      convPow (ν : Measure ℝ) m
    simp only [zero_mul, zero_add]
    exact map_gapKeys_eq_convPow ν m
  have hseq := map_seq_eq_iidLaw ((iidSeq_gapCoord ν).block m) β hbase.symm
  have he := sa_iidLaw_prefix β L
  have hrestrict : Measurable (fun x : ℕ → ℝ => fun i : Fin L => x i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)
  rw [← hseq, Measure.map_map hrestrict
    (measurable_seq ((iidSeq_gapCoord ν).block m).measurable)] at he
  exact he

/-- Applying a coordinatewise function to two independent product vectors preserves
independence across the coordinate index. -/
theorem sa_map_pi_pair {ι A B C : Type*} [Fintype ι]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : A × B → C} (hf : Measurable f) :
    ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => ν))).map
      (fun z i => f (z.1 i, z.2 i)) = Measure.pi (fun _ : ι => (μ.prod ν).map f) := by
  have he := (measurePreserving_arrowProdEquivProdArrow A B ι (fun _ : ι => μ)
    (fun _ : ι => ν)).symm.map_eq
  have : IsProbabilityMeasure ((μ.prod ν).map f) := isProbabilityMeasure_map hf.aemeasurable
  have hpi := Measure.pi_map_pi (μ := fun _ : ι => μ.prod ν) (fun _ => hf.aemeasurable)
  have hmap : Measurable (fun x : ι → A × B => fun i => f (x i)) :=
    measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
  rw [← he, Measure.map_map hmap
    (MeasurableEquiv.arrowProdEquivProdArrow A B ι).symm.measurable] at hpi
  exact hpi

/-- Smoothed and centered block totals of two independent iid sequences. -/
def saSmoothedBlockTotals (m L : ℕ) (s : ℝ) (q : (ℕ → ℝ) × (ℕ → ℝ)) : Fin L → ℝ :=
  fun j => saBlockTotals m L q.1 j - m + s * saBlockTotals m L q.2 j

theorem measurable_saSmoothedBlockTotals (m L : ℕ) (s : ℝ) :
    Measurable (saSmoothedBlockTotals m L s) := by
  apply measurable_pi_lambda
  intro j
  exact (((measurable_pi_apply j).comp ((measurable_saBlockTotals m L).comp measurable_fst)).sub_const _).add
    (measurable_const.mul ((measurable_pi_apply j).comp
      ((measurable_saBlockTotals m L).comp measurable_snd)))

/-- Gaussian scaling has the variance convention used by the smoothing densities. -/
theorem sa_gaussian_scale_nat (m : ℕ) (s : ℝ) :
    (gaussianReal 0 m).map (s * ·) = gaussianReal 0 ((m : ℝ≥0) * Real.toNNReal (s ^ 2)) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · ring
  · apply NNReal.eq
    simp [Real.toNNReal_of_nonneg (sq_nonneg s), mul_comm]

/-- The marginal law of each smoothed block is the actual density used in the saddle proof. -/
theorem saSmoothedBlockTotals_law (ν : ProbabilityMeasure ℝ) {s : ℝ} (hs : 0 < s)
    {m : ℕ} (hm : 0 < m) (L : ℕ) :
    ((iidLaw ν).prod (iidLaw gaussPM)).map (saSmoothedBlockTotals m L s) =
      Measure.pi (fun _ : Fin L => ((saDensity_centeredSum ν hs hm).law : Measure ℝ)) := by
  let μ := convPow (ν : Measure ℝ) m
  have hmμ : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (convPow (ν : Measure ℝ) m))
  have hblocks := map_prod_map (iidLaw ν) (iidLaw gaussPM)
    (measurable_saBlockTotals m L) (measurable_saBlockTotals m L)
  rw [saBlockTotals_law, saBlockTotals_law, show (gaussPM : Measure ℝ) = gaussianReal 0 1 from rfl,
    sa_convPow_standardGaussian] at hblocks
  have hlaw : (μ.prod (gaussianReal 0 m)).map (fun z => z.1 - m + s * z.2) =
      (saDensity_centeredSum ν hs hm).law := by
    rw [saDensity_centeredSum_law ν hs hm, sa_convPow_map_sub]
    simp only [mul_one]
    have hsub : Measurable (fun x : ℝ => x - m) := measurable_id.sub_const (m : ℝ)
    have hscale : Measurable (fun x : ℝ => s * x) := measurable_const.mul measurable_id
    have he := map_prod_map μ (gaussianReal 0 m) hsub hscale
    rw [sa_gaussian_scale_nat] at he
    rw [Measure.conv, he, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hpi := sa_map_pi_pair (ι := Fin L) μ (gaussianReal 0 m)
    (f := fun z => z.1 - m + s * z.2) (by fun_prop)
  rw [hlaw, hblocks, Measure.map_map (by fun_prop)
    ((measurable_saBlockTotals m L).prodMap (measurable_saBlockTotals m L))] at hpi
  exact hpi

/-- Centering and smoothing commute with taking a leaf prefix. -/
theorem saSmoothedBlockTotals_prefix (m L : ℕ) (s : ℝ)
    (q : (ℕ → ℝ) × (ℕ → ℝ)) {k : ℕ} (hk : k ≤ L) :
    vkeys (saSmoothedBlockTotals m L s q) k =
      gapKeys q.1 (k * m) - k * m + s * gapKeys q.2 (k * m) := by
  change vkeys (fun j : Fin L =>
    (seq (blockGap gapCoord m) q.1 j - m + s * seq (blockGap gapCoord m) q.2 j)) k = _
  rw [vkeys_eq_gapKeys (fun j : ℕ =>
    seq (blockGap gapCoord m) q.1 j - m + s * seq (blockGap gapCoord m) q.2 j) hk]
  simp only [gapKeys, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  change gapKeys (seq (blockGap gapCoord m) q.1) k - k * m +
    s * gapKeys (seq (blockGap gapCoord m) q.2) k = _
  rw [gapKeys_blockGap, gapKeys_blockGap]
  rfl

/-- Scaled Gaussian block totals. -/
def saScaledBlockTotals (m L : ℕ) (σ : ℝ) (z : ℕ → ℝ) : Fin L → ℝ :=
  fun j => σ * saBlockTotals m L z j

theorem measurable_saScaledBlockTotals (m L : ℕ) (σ : ℝ) :
    Measurable (saScaledBlockTotals m L σ) :=
  measurable_pi_lambda _ fun j => measurable_const.mul
    ((measurable_pi_apply j).comp (measurable_saBlockTotals m L))

theorem saScaledBlockTotals_law (m L : ℕ) (σ : ℝ) :
    (iidLaw gaussPM).map (saScaledBlockTotals m L σ) =
      Measure.pi (fun _ : Fin L => gaussianReal 0 ((m : ℝ≥0) * Real.toNNReal (σ ^ 2))) := by
  have hm : Measurable (fun x : Fin L → ℝ => fun i => σ * x i) := by fun_prop
  have he := Measure.pi_map_pi (μ := fun _ : Fin L => gaussianReal 0 m)
    (fun _ => (show Measurable (fun x : ℝ => σ * x) by fun_prop).aemeasurable)
  rw [sa_gaussian_scale_nat] at he
  have hb := saBlockTotals_law gaussPM m L
  change _ = Measure.pi (fun _ : Fin L => convPow (gaussianReal 0 1) m) at hb
  rw [sa_convPow_standardGaussian] at hb
  rw [← hb, Measure.map_map hm (measurable_saBlockTotals m L)] at he
  exact he

theorem saScaledBlockTotals_prefix (m L : ℕ) (σ : ℝ) (z : ℕ → ℝ)
    {k : ℕ} (hk : k ≤ L) :
    vkeys (saScaledBlockTotals m L σ z) k = σ * gapKeys z (k * m) := by
  change vkeys (fun j : Fin L => σ * seq (blockGap gapCoord m) z j) k = _
  rw [vkeys_eq_gapKeys (fun j : ℕ => σ * seq (blockGap gapCoord m) z j) hk,
    gapKeys_const_mul, gapKeys_blockGap]
  rfl

end

end PGM
