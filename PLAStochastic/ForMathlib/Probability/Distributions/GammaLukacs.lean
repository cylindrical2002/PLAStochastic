import PLAStochastic.ForMathlib.Probability.OrderStatistics.GammaRatio
import Mathlib.Probability.Distributions.Gamma

/-!
# Scale-invariant events of independent Gamma variables (Lukacs)

For independent `Gamma(aᵢ, 1)` coordinates `x : Fin t → ℝ` (`t ≥ 1`, `aᵢ > 0`) and a
measurable set `S` invariant under multiplication by positive scalars,
`law(S ∩ {∑ xᵢ ∈ A}) = law(S) · Gamma(∑ aᵢ, 1)(A)` (`pi_gammaMeasure_inter_sum`).

Proof: in partial-sum coordinates `γ = psMap x` (unimodular) the density
`∏ gammaPDF aᵢ (xᵢ)` is homogeneous along rays up to the factor `e^{-γ_last}`; slicing
at `γ_last = s > 0` and rescaling the slice by `s` gives the section integral
`s^{∑a - 1} e^{-s} · C_S` with a constant `C_S` depending only on `S`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal

namespace PGM

open PGM.Renyi

/-- The product of laws with densities `ρ i` has density `∏ i, ρ i (e i)`. -/
theorem pi_withDensity_prod {m : ℕ} (ρ : Fin m → ℝ → ℝ≥0∞) (hρ : ∀ i, Measurable (ρ i))
    [∀ i, SigmaFinite (volume.withDensity (ρ i))] :
    Measure.pi (fun i => volume.withDensity (ρ i)) =
      volume.withDensity (fun e : Fin m → ℝ => ∏ i, ρ i (e i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have : (univ.pi s).indicator (fun e : Fin m → ℝ => ∏ i, ρ i (e i)) =
      fun e => ∏ i, (s i).indicator (ρ i) (e i) := by
    funext e
    by_cases he : e ∈ univ.pi s
    · rw [indicator_of_mem he]
      exact Finset.prod_congr rfl fun i _ => (indicator_of_mem (he i (mem_univ i)) _).symm
    · rw [indicator_of_notMem he]
      simp only [mem_pi, mem_univ, true_implies, not_forall] at he
      obtain ⟨i, hi⟩ := he
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)).symm
  rw [this, lintegral_pi_prod _ fun i => (hρ i).indicator (hs i)]
  exact Finset.prod_congr rfl fun i _ => by
    rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

/-- Homogeneity of the Gamma density along rays. -/
theorem gammaPDFReal_mul {a s : ℝ} (hs : 0 < s) (x : ℝ) :
    gammaPDFReal a 1 (s * x) =
      s ^ (a - 1) * Real.exp (-(s - 1) * x) * gammaPDFReal a 1 x := by
  unfold gammaPDFReal
  by_cases hx : 0 ≤ x
  · rw [if_pos (mul_nonneg hs.le hx), if_pos hx, Real.mul_rpow hs.le hx]
    have : Real.exp (-(1 * (s * x))) = Real.exp (-(s - 1) * x) * Real.exp (-(1 * x)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  · have hsx : ¬ 0 ≤ s * x := fun h => hx ((mul_nonneg_iff_of_pos_left hs).mp h)
    rw [if_neg hsx, if_neg hx, mul_zero]

theorem prod_gammaPDFReal_mul {t : ℕ} (a : Fin t → ℝ) {s : ℝ} (hs : 0 < s) (x : Fin t → ℝ) :
    ∏ i, gammaPDFReal (a i) 1 (s * x i) =
      s ^ (∑ i, a i - t) * Real.exp (-(s - 1) * ∑ i, x i) * ∏ i, gammaPDFReal (a i) 1 (x i) := by
  simp_rw [gammaPDFReal_mul hs]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hs,
    ← Real.exp_sum, Finset.mul_sum, Finset.sum_sub_distrib]
  simp

/-! ### Partial-sum coordinates -/

/-- The partial-sum map as a linear equivalence (it has determinant `1`). -/
def psEquiv (k : ℕ) : (Fin (k + 1) → ℝ) ≃ₗ[ℝ] (Fin (k + 1) → ℝ) :=
  LinearMap.equivOfIsUnitDet (f := psMap k) (by rw [det_psMap]; exact isUnit_one)

theorem psEquiv_apply (k : ℕ) (x : Fin (k + 1) → ℝ) : psEquiv k x = psMap k x :=
  LinearMap.equivOfIsUnitDet_apply _ _

theorem psMap_last (k : ℕ) (x : Fin (k + 1) → ℝ) : psMap k x (Fin.last k) = ∑ i, x i := by
  rw [psMap_apply, Fin.val_last, gammaSum_last]

theorem sum_psEquiv_symm (k : ℕ) (γ : Fin (k + 1) → ℝ) :
    ∑ i, (psEquiv k).symm γ i = γ (Fin.last k) := by
  rw [← psMap_last, ← psEquiv_apply, LinearEquiv.apply_symm_apply]

theorem measurable_psEquiv_symm (k : ℕ) : Measurable (psEquiv k).symm :=
  ((psEquiv k).symm.toLinearMap.continuous_of_finiteDimensional).measurable

/-- The product Gamma density in partial-sum coordinates. -/
def gammaConeDens {k : ℕ} (a : Fin (k + 1) → ℝ) (γ : Fin (k + 1) → ℝ) : ℝ :=
  ∏ i, gammaPDFReal (a i) 1 ((psEquiv k).symm γ i)

theorem measurable_gammaConeDens {k : ℕ} (a : Fin (k + 1) → ℝ) :
    Measurable (gammaConeDens a) :=
  Finset.measurable_prod _ fun i _ =>
    (measurable_gammaPDFReal (a i) 1).comp ((measurable_pi_apply i).comp (measurable_psEquiv_symm k))

theorem gammaConeDens_nonneg {k : ℕ} {a : Fin (k + 1) → ℝ} (ha : ∀ i, 0 < a i)
    (γ : Fin (k + 1) → ℝ) : 0 ≤ gammaConeDens a γ :=
  Finset.prod_nonneg fun i _ => gammaPDFReal_nonneg (ha i) one_pos _

theorem gammaConeDens_smul {k : ℕ} (a : Fin (k + 1) → ℝ) {s : ℝ} (hs : 0 < s)
    (γ : Fin (k + 1) → ℝ) :
    gammaConeDens a (s • γ) =
      s ^ (∑ i, a i - (k + 1 : ℕ)) * Real.exp (-(s - 1) * γ (Fin.last k)) * gammaConeDens a γ := by
  unfold gammaConeDens
  rw [map_smul, ← sum_psEquiv_symm k γ]
  exact prod_gammaPDFReal_mul a hs _

theorem gammaConeDens_of_neg {k : ℕ} (a : Fin (k + 1) → ℝ) {γ : Fin (k + 1) → ℝ}
    (hγ : γ (Fin.last k) < 0) : gammaConeDens a γ = 0 := by
  rw [← sum_psEquiv_symm k γ] at hγ
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, (psEquiv k).symm γ i < 0 := by
    by_contra h
    push Not at h
    exact absurd (Finset.sum_nonneg h) (not_le.mpr hγ)
  unfold gammaConeDens
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp [gammaPDFReal, not_le.mpr hi]

/-! ### The slices of the partial-sum density -/

theorem piFinSuccAbove_last_symm_apply (k : ℕ) (s : ℝ) (γ : Fin k → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)).symm (s, γ) =
      Fin.snoc γ s := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_last']

theorem measurable_snoc_const (k : ℕ) (s : ℝ) :
    Measurable (fun γ : Fin k → ℝ => (Fin.snoc γ s : Fin (k + 1) → ℝ)) := by
  have h0 : Measurable (fun γ : Fin k → ℝ => (s, γ)) := measurable_const.prodMk measurable_id
  have h := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ)
    (Fin.last k)).symm.measurable.comp h0
  have e : (fun γ : Fin k → ℝ => (Fin.snoc γ s : Fin (k + 1) → ℝ)) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)).symm ∘
        fun γ => (s, γ) := by
    funext γ
    exact (piFinSuccAbove_last_symm_apply k s γ).symm
  rw [e]
  exact h

theorem snoc_eq_smul (k : ℕ) {s : ℝ} (hs : s ≠ 0) (γ : Fin k → ℝ) :
    (Fin.snoc γ s : Fin (k + 1) → ℝ) = s • (Fin.snoc (s⁻¹ • γ) 1 : Fin (k + 1) → ℝ) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp
  | cast i => simp [hs]

/-- The slice of a scale-invariant event at total `s > 0`. -/
theorem lintegral_slice_pos {k : ℕ} (a : Fin (k + 1) → ℝ)
    {R : Set (Fin (k + 1) → ℝ)} (hR : MeasurableSet R)
    (hRs : ∀ c : ℝ, 0 < c → ∀ γ, c • γ ∈ R ↔ γ ∈ R) (A : Set ℝ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ γ' : Fin k → ℝ, (R ∩ {γ | γ (Fin.last k) ∈ A}).indicator
        (fun γ => ENNReal.ofReal (gammaConeDens a γ)) (Fin.snoc γ' s) =
      A.indicator (fun s => ENNReal.ofReal (s ^ (∑ i, a i - 1) * Real.exp (-s))) s *
        (ENNReal.ofReal (Real.exp 1) * ∫⁻ u : Fin k → ℝ,
          R.indicator (fun γ => ENNReal.ofReal (gammaConeDens a γ)) (Fin.snoc u 1)) := by
  set Gd : (Fin (k + 1) → ℝ) → ℝ≥0∞ := fun γ => ENNReal.ofReal (gammaConeDens a γ) with hGd
  have hGdm : Measurable Gd := (measurable_gammaConeDens a).ennreal_ofReal
  set h : (Fin k → ℝ) → ℝ≥0∞ := fun u => R.indicator Gd (Fin.snoc u 1) with hh
  have hhm : Measurable h := (hGdm.indicator hR).comp (measurable_snoc_const k 1)
  set c : ℝ := s ^ (∑ i, a i - (k + 1 : ℕ)) * Real.exp (-(s - 1)) with hc
  have hpt : ∀ γ' : Fin k → ℝ, (R ∩ {γ | γ (Fin.last k) ∈ A}).indicator Gd (Fin.snoc γ' s) =
      A.indicator (fun _ => ENNReal.ofReal c) s * h (s⁻¹ • γ') := by
    intro γ'
    rw [snoc_eq_smul k hs.ne' γ']
    by_cases hA : s ∈ A
    · rw [indicator_of_mem hA]
      by_cases hR' : (Fin.snoc (s⁻¹ • γ') 1 : Fin (k + 1) → ℝ) ∈ R
      · have h1 : s • (Fin.snoc (s⁻¹ • γ') 1 : Fin (k + 1) → ℝ) ∈
            R ∩ {γ | γ (Fin.last k) ∈ A} :=
          ⟨(hRs s hs _).mpr hR', by simpa using hA⟩
        rw [indicator_of_mem h1, hh]
        simp only
        rw [indicator_of_mem hR', hGd]
        simp only
        rw [gammaConeDens_smul a hs, Fin.snoc_last, mul_one,
          ENNReal.ofReal_mul (by positivity)]
      · have h1 : s • (Fin.snoc (s⁻¹ • γ') 1 : Fin (k + 1) → ℝ) ∉
            R ∩ {γ | γ (Fin.last k) ∈ A} := fun h => hR' ((hRs s hs _).mp h.1)
        rw [indicator_of_notMem h1, hh]
        simp only
        rw [indicator_of_notMem hR', mul_zero]
    · rw [indicator_of_notMem hA, zero_mul]
      refine indicator_of_notMem ?_ _
      intro h1
      exact hA (by simpa using h1.2)
  simp_rw [hpt]
  rw [lintegral_const_mul _ (f := fun γ' => h (s⁻¹ • γ'))
    (hhm.comp (measurable_const_smul s⁻¹))]
  have hscale : ∫⁻ γ' : Fin k → ℝ, h (s⁻¹ • γ') = ENNReal.ofReal (s ^ k) * ∫⁻ u, h u := by
    rw [← lintegral_map hhm (measurable_const_smul s⁻¹),
      Measure.map_addHaar_smul volume (inv_ne_zero hs.ne'), lintegral_smul_measure,
      Module.finrank_fin_fun, inv_pow, inv_inv, abs_of_pos (pow_pos hs k), smul_eq_mul]
  rw [hscale]
  by_cases hA : s ∈ A
  · rw [indicator_of_mem hA, indicator_of_mem hA, ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [hc]
    have e1 : s ^ (∑ i, a i - (k + 1 : ℕ)) * s ^ k = s ^ (∑ i, a i - 1) := by
      rw [← Real.rpow_natCast s k, ← Real.rpow_add hs]
      congr 1
      push_cast
      ring
    have e2 : Real.exp (-(s - 1)) = Real.exp (-s) * Real.exp 1 := by
      rw [← Real.exp_add]; ring_nf
    rw [e2, ← e1]
    ring
  · rw [indicator_of_notMem hA, indicator_of_notMem hA, zero_mul, zero_mul]

/-! ### Scale-invariant events of independent Gamma variables -/

/-- The Gamma density restricted to a set, up to its normalizing constant. -/
theorem gammaMeasure_eq_mul_lintegral {b : ℝ} (hb : 0 < b) {A : Set ℝ} (hA : MeasurableSet A) :
    gammaMeasure b 1 A = ENNReal.ofReal (1 / Real.Gamma b) *
      ∫⁻ s, (Ioi 0).indicator (A.indicator
        fun s => ENNReal.ofReal (s ^ (b - 1) * Real.exp (-s))) s := by
  rw [gammaMeasure, withDensity_apply _ hA, ← lintegral_indicator hA,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hae : ∀ᵐ s : ℝ, s ≠ 0 := measure_eq_zero_iff_ae_notMem.1 (measure_singleton (0 : ℝ))
  refine lintegral_congr_ae (hae.mono fun s hs => ?_)
  beta_reduce
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · rw [indicator_of_notMem (show s ∉ Ioi 0 from not_lt.2 hneg.le), mul_zero]
    by_cases hsA : s ∈ A
    · rw [indicator_of_mem hsA, gammaPDF_of_neg hneg]
    · rw [indicator_of_notMem hsA]
  · rw [indicator_of_mem (show s ∈ Ioi 0 from hpos)]
    by_cases hsA : s ∈ A
    · rw [indicator_of_mem hsA, indicator_of_mem hsA, gammaPDF_of_nonneg hpos.le,
        ← ENNReal.ofReal_mul (by have := Real.Gamma_pos_of_pos hb; positivity)]
      congr 1
      rw [Real.one_rpow, one_mul]
      ring
    · rw [indicator_of_notMem hsA, indicator_of_notMem hsA, mul_zero]

/-- **Scale-invariant events of independent Gamma variables** (`t = k + 1` coordinates). -/
theorem pi_gammaMeasure_inter_sum_succ {k : ℕ} (a : Fin (k + 1) → ℝ) (ha : ∀ i, 0 < a i)
    {S : Set (Fin (k + 1) → ℝ)} (hS : MeasurableSet S)
    (hSs : ∀ c : ℝ, 0 < c → ∀ x ∈ S, c • x ∈ S) {A : Set ℝ} (hA : MeasurableSet A) :
    Measure.pi (fun i => gammaMeasure (a i) 1) (S ∩ {x | ∑ i, x i ∈ A}) =
      Measure.pi (fun i => gammaMeasure (a i) 1) S * gammaMeasure (∑ i, a i) 1 A := by
  set μ := Measure.pi (fun i => gammaMeasure (a i) 1) with hμdef
  set Gd : (Fin (k + 1) → ℝ) → ℝ≥0∞ := fun γ => ENNReal.ofReal (gammaConeDens a γ) with hGd
  have hGdm : Measurable Gd := (measurable_gammaConeDens a).ennreal_ofReal
  have : ∀ i, SigmaFinite (volume.withDensity (gammaPDF (a i) 1)) := fun i => by
    have := isProbabilityMeasure_gammaMeasure (ha i) one_pos
    exact (inferInstance : SigmaFinite (gammaMeasure (a i) 1))
  have hμ : μ = volume.withDensity (Gd ∘ psMap k) := by
    rw [hμdef, show (fun i => gammaMeasure (a i) 1) =
      fun i => volume.withDensity (gammaPDF (a i) 1) from rfl,
      pi_withDensity_prod (fun i => gammaPDF (a i) 1)
        fun i => (measurable_gammaPDFReal _ _).ennreal_ofReal]
    congr 1
    funext x
    simp only [comp_apply, hGd, gammaConeDens, ← psEquiv_apply, LinearEquiv.symm_apply_apply,
      gammaPDF]
    rw [ENNReal.ofReal_prod_of_nonneg fun i _ => gammaPDFReal_nonneg (ha i) one_pos _]
  have hmap : μ.map (psMap k) = volume.withDensity Gd := by
    rw [hμ]; exact map_withDensity_comp measurePreserving_psMap hGdm
  set R : Set (Fin (k + 1) → ℝ) := (psEquiv k).symm ⁻¹' S with hRdef
  have hR : MeasurableSet R := measurable_psEquiv_symm k hS
  have hSiff : ∀ c : ℝ, 0 < c → ∀ x, c • x ∈ S ↔ x ∈ S := by
    intro c hc x
    refine ⟨fun h => ?_, hSs c hc x⟩
    have := hSs c⁻¹ (inv_pos.2 hc) _ h
    rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
  have hRs : ∀ c : ℝ, 0 < c → ∀ γ, c • γ ∈ R ↔ γ ∈ R := by
    intro c hc γ
    simp only [hRdef, mem_preimage, map_smul]
    exact hSiff c hc _
  set C : ℝ≥0∞ := ENNReal.ofReal (Real.exp 1) *
    ∫⁻ u : Fin k → ℝ, R.indicator Gd (Fin.snoc u 1) with hC
  set f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (∑ i, a i - 1) * Real.exp (-s)) with hf
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp
    ((measurable_id.pow_const _).mul (Real.measurable_exp.comp measurable_neg))
  have hmain : ∀ B : Set ℝ, MeasurableSet B →
      μ (S ∩ {x | ∑ i, x i ∈ B}) = (∫⁻ s, (Ioi 0).indicator (B.indicator f) s) * C := by
    intro B hB
    have hlast : MeasurableSet {γ : Fin (k + 1) → ℝ | γ (Fin.last k) ∈ B} :=
      measurable_pi_apply _ hB
    have hpre : psMap k ⁻¹' (R ∩ {γ | γ (Fin.last k) ∈ B}) = S ∩ {x | ∑ i, x i ∈ B} := by
      ext x
      simp only [hRdef, mem_preimage, mem_inter_iff, mem_ofPred_eq, psMap_last]
      rw [← psEquiv_apply, LinearEquiv.symm_apply_apply]
    rw [← hpre, ← Measure.map_apply measurePreserving_psMap.measurable (hR.inter hlast), hmap,
      withDensity_apply _ (hR.inter hlast), ← lintegral_indicator (hR.inter hlast)]
    set F := (R ∩ {γ : Fin (k + 1) → ℝ | γ (Fin.last k) ∈ B}).indicator Gd with hF
    have hFm : Measurable F := hGdm.indicator (hR.inter hlast)
    let eqv := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)).symm
    rw [← h.lintegral_comp_emb eqv.symm.measurableEmbedding F, Measure.volume_eq_prod,
      lintegral_prod (fun p => F (eqv.symm p)) (hFm.comp eqv.symm.measurable).aemeasurable]
    have hsymm : ∀ (s : ℝ) (γ : Fin k → ℝ), eqv.symm (s, γ) = Fin.snoc γ s :=
      piFinSuccAbove_last_symm_apply k
    simp_rw [hsymm]
    have hae : ∀ᵐ s : ℝ, s ≠ 0 := measure_eq_zero_iff_ae_notMem.1 (measure_singleton (0 : ℝ))
    rw [← lintegral_mul_const _ ((hfm.indicator hB).indicator measurableSet_Ioi)]
    refine lintegral_congr_ae (hae.mono fun s hs => ?_)
    beta_reduce
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · rw [indicator_of_notMem (show s ∉ Ioi 0 from not_lt.2 hneg.le), zero_mul]
      have hz : ∀ γ' : Fin k → ℝ, F (Fin.snoc γ' s) = 0 := by
        intro γ'
        refine indicator_apply_eq_zero.2 fun _ => ?_
        simp only [hGd]
        rw [gammaConeDens_of_neg a (by simpa using hneg), ENNReal.ofReal_zero]
      simp_rw [hz, lintegral_zero]
    · rw [indicator_of_mem (show s ∈ Ioi 0 from hpos), hF]
      exact lintegral_slice_pos a hR hRs B hpos
  have hΓ : ∀ B : Set ℝ, MeasurableSet B → gammaMeasure (∑ i, a i) 1 B =
      ENNReal.ofReal (1 / Real.Gamma (∑ i, a i)) * ∫⁻ s, (Ioi 0).indicator (B.indicator f) s :=
    fun B hB => gammaMeasure_eq_mul_lintegral (Finset.sum_pos (fun i _ => ha i)
      Finset.univ_nonempty) hB
  have hsum : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have h1 : ENNReal.ofReal (1 / Real.Gamma (∑ i, a i)) *
      ∫⁻ s, (Ioi 0).indicator ((univ : Set ℝ).indicator f) s = 1 := by
    rw [← hΓ univ MeasurableSet.univ]
    have := isProbabilityMeasure_gammaMeasure hsum one_pos
    exact measure_univ
  have hSu : μ S = (∫⁻ s, (Ioi 0).indicator ((univ : Set ℝ).indicator f) s) * C := by
    rw [← hmain univ MeasurableSet.univ]
    congr 1
    ext x
    simp
  rw [hmain A hA, hSu, hΓ A hA]
  calc (∫⁻ s, (Ioi 0).indicator (A.indicator f) s) * C
      = (ENNReal.ofReal (1 / Real.Gamma (∑ i, a i)) *
          ∫⁻ s, (Ioi 0).indicator ((univ : Set ℝ).indicator f) s) *
          ((∫⁻ s, (Ioi 0).indicator (A.indicator f) s) * C) := by rw [h1, one_mul]
    _ = _ := by ring

/-- **Scale-invariant events of independent Gamma variables.**  If the coordinates of
`x : Fin t → ℝ` are independent `Gamma(aᵢ, 1)` (`t ≥ 1`, `aᵢ > 0`) and `S` is a measurable
set invariant under multiplication by positive scalars, then the total `∑ xᵢ` is
`Gamma(∑ aᵢ, 1)` and independent of the event `S`. -/
theorem pi_gammaMeasure_inter_sum {t : ℕ} (ht : 0 < t) (a : Fin t → ℝ) (ha : ∀ i, 0 < a i)
    {S : Set (Fin t → ℝ)} (hS : MeasurableSet S)
    (hSs : ∀ c : ℝ, 0 < c → ∀ x ∈ S, c • x ∈ S) {A : Set ℝ} (hA : MeasurableSet A) :
    Measure.pi (fun i => gammaMeasure (a i) 1) (S ∩ {x | ∑ i, x i ∈ A}) =
      Measure.pi (fun i => gammaMeasure (a i) 1) S * gammaMeasure (∑ i, a i) 1 A := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  exact pi_gammaMeasure_inter_sum_succ a ha hS hSs hA

end PGM
