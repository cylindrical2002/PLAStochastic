import PLAStochastic.Index.KEP.Poisson.JointInduction
import PLAStochastic.Index.KEP.Poisson.SpatialDrift
import PLAStochastic.Index.KEP.Poisson.BaseHellinger
import PLAStochastic.Index.KEP.ReferenceScale.GeometricWindow
import PLAStochastic.Index.KEP.ReferenceScale.UniformSmallMoments
import PLAStochastic.Index.KEP.CumulantScaleArithmetic

/-!
# Unconditional uniform Poisson layer comparison above the spatial cutoff

All constants are selected from the actual reference orbit and intensity
profile before epsilon, intensity, anchor and layer. The proved joint
induction closes finiteness, a fixed exponential moment and the two-thirds
Hellinger error on every layer inside the monotone comparison cutoff.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepPoisson_uniform_comparison {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) :
    ∃ theta D delta E : ℝ, 0 < theta ∧ 0 < D ∧ 0 < delta ∧ delta ≤ 1 ∧
      kepReferenceClassicalThreshold ≤ E ∧ 1 ≤ E ∧
      ∀ eps, E ≤ eps → ∀ n : ℝ, 1 ≤ n → ∀ j : ℕ, kepSpatialCutoff eps n j ≤ delta →
        (∀ x, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x j 1 g ≠ ⊤) ∧
        (∀ x, Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n x j) ∧
          ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n x j ≤ 73) ∧
        ∀ x, measureHellinger (kepPoissonLayerMeasure hf eps n x j) (kepReferenceLaw eps j) ≤
          kepSpatialError D eps n j := by
  obtain ⟨thetaBase, Kbase, hthetaBase, hKbase, hbase⟩ := kepPoisson_base_uniform_budgets hf
  obtain ⟨thetaRef, eRef, hthetaRef, href⟩ := kepReference_uniform_small_exponential_moment
  obtain ⟨Dw, eWindow, hDw, _, _, hwindow⟩ := kepReference_quadratic_geometric_window
  obtain ⟨eSpan, Bspan, _, _, hspan⟩ := kepReferenceSpan_budget
  obtain ⟨drift, eDrift, hdrift, _, hstep⟩ := kepPoisson_parent_step_spatial_drift hf
  let R := fhi / flo
  let cb := kepGraphMeanBracket
  let A := 2 * Dw
  have hR : 0 < R := div_pos hf.fhi_pos hf.pos
  have hR1 : 1 ≤ R := by
    have h := hf.ratio_le 0 0
    simpa only [div_self (hf.f_pos 0).ne'] using h
  have hcb : 0 < cb := zero_lt_one.trans_le kepGraphMeanBracket_ge_one
  have hA : 0 < A := by dsimp [A]; linarith
  let theta := min thetaBase (min thetaRef (1 / (864 * R * A * cb)))
  have htheta : 0 < theta := lt_min hthetaBase (lt_min hthetaRef (by positivity))
  have hthetaBaseLe : theta ≤ thetaBase := min_le_left _ _
  have hthetaRefLe : theta ≤ thetaRef := (min_le_right _ _).trans (min_le_left _ _)
  have hthetaScale : theta ≤ 1 / (864 * R * A * cb) :=
    (min_le_right _ _).trans (min_le_right _ _)
  let D := max 1 (max drift Kbase)
  have hD1 : 1 ≤ D := le_max_left _ _
  have hD : 0 < D := zero_lt_one.trans_le hD1
  have hdriftD : drift ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hKbaseD : Kbase ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  let Kf := kepFiniteComparisonConstant A theta R
  let Kp := kepStoppedComparisonConstant A theta R
  let S := Real.sqrt (8 * 73 / theta ^ 2)
  have hKf : 0 < Kf := kepFiniteComparisonConstant_pos hA.le
  have hKp : 0 < Kp := kepStoppedComparisonConstant_pos hA.le
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  let Z := 4 * Kf * (D + drift) + D * S + 1
  have hZ1 : 1 ≤ Z := by
    have h1 : 0 ≤ 4 * Kf * (D + drift) := by positivity
    have h2 : 0 ≤ D * S := by positivity
    dsimp [Z]
    linarith
  have hZ : 0 < Z := zero_lt_one.trans_le hZ1
  let delta := 1 / Z
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdelta1 : delta ≤ 1 := (div_le_one hZ).mpr hZ1
  have hZdelta : Z * delta = 1 := by dsimp [delta]; field_simp
  have hdeltaWindow : Kf * (D + drift) * delta ≤ 1 / 4 := by
    have h : 4 * Kf * (D + drift) ≤ Z := by
      have : 0 ≤ D * S := by positivity
      dsimp [Z]
      linarith
    have h' := mul_le_mul_of_nonneg_right h hdelta.le
    rw [hZdelta] at h'
    nlinarith
  have hdeltaMean : D * delta * S ≤ 1 := by
    have h : D * S ≤ Z := by
      have : 0 ≤ 4 * Kf * (D + drift) := by positivity
      dsimp [Z]
      linarith
    have h' := mul_le_mul_of_nonneg_right h hdelta.le
    rw [hZdelta] at h'
    nlinarith
  let E := max eRef (max eWindow (max eSpan (max eDrift
    (max kepReferenceClassicalThreshold (max 1
      (max (4 * R * cb) (max (16 * 73 * R * cb / theta) ((2 * Kp) ^ 3 * cb ^ 2))))))))
  have hEClass : kepReferenceClassicalThreshold ≤ E := by dsimp [E]; simp
  have hE1 : 1 ≤ E := by dsimp [E]; simp
  refine ⟨theta, D, delta, E, htheta, hD, hdelta, hdelta1, hEClass, hE1, ?_⟩
  intro eps heps
  have he := heps
  change max eRef (max eWindow (max eSpan (max eDrift
    (max kepReferenceClassicalThreshold (max 1
      (max (4 * R * cb) (max (16 * 73 * R * cb / theta) ((2 * Kp) ^ 3 * cb ^ 2)))))))) ≤ eps at he
  simp only [max_le_iff] at he
  obtain ⟨heRef, heWindow', heSpan, heDrift, hclass, he1, he4, heCost, heDom⟩ := he
  have he0 : 0 < eps := zero_lt_one.trans_le he1
  have he2 : eps ≤ eps ^ 2 := by nlinarith
  have hs := hspan eps heSpan
  obtain ⟨hM1, hM, _, _⟩ := hwindow eps heWindow' 0
  let M := ⌈Dw * eps ^ 2⌉₊
  have hM' : (M : ℝ) ≤ A * eps ^ 2 := hM
  have hQwindow' (j : ℕ) : (iidLaw (kepReferenceLaw eps j)).real
      {g | (M : ℕ∞) < gapSegLen eps g} ≤ 1 / 16 := (hwindow eps heWindow' j).2.2.1
  have hQtail' (j k : ℕ) : (iidLaw (kepReferenceLaw eps j)).real
      {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps g} ≤ (1 / 2 : ℝ) ^ k :=
    (hwindow eps heWindow' j).2.2.2 k
  have hcompression (j : ℕ) : eps ^ 2 / cb ≤ lawC eps (kepReferenceLaw eps j) :=
    (kepReference_lawC_bracket hclass j).1
  have hC (j : ℕ) : 0 < lawC eps (kepReferenceLaw eps j) :=
    (div_pos (sq_pos_of_pos he0) hcb).trans_le (hcompression j)
  have hC4 (j : ℕ) : 4 * R ≤ lawC eps (kepReferenceLaw eps j) := by
    apply le_trans _ (hcompression j)
    rw [le_div_iff₀ hcb]
    exact he4.trans he2
  have hCcost (j : ℕ) : 16 * 73 * R ≤ theta * lawC eps (kepReferenceLaw eps j) := by
    have h := heCost.trans he2
    rw [div_le_iff₀ htheta] at h
    have h' : 16 * 73 * R ≤ theta * (eps ^ 2 / cb) := by
      rw [show theta * (eps ^ 2 / cb) = (theta * eps ^ 2) / cb by ring,
        le_div_iff₀ hcb]
      nlinarith
    exact h'.trans (mul_le_mul_of_nonneg_left (hcompression j) htheta.le)
  have hsmall (j : ℕ) := kep_cumulant_small_tilt htheta hR (hC j) (hC4 j)
  have hcost (j : ℕ) := kep_cumulant_quadratic_cost htheta hR (hC j) (hCcost j)
  have hscale (j : ℕ) := kep_cumulant_stopping_scale htheta.le hR (hC j) hA hcb
    (hcompression j) hM' hthetaScale
  have hdom (j : ℕ) := kep_two_thirds_compression_dominates he0 hcb hKp.le
    (hcompression j) heDom
  have href' (j : ℕ) := href eps heRef j
  have hrefData (j : ℕ) :
      (∀ᵐ z ∂(kepReferenceLaw eps j : Measure ℝ), 0 ≤ z) ∧
      (∫ z, z ∂(kepReferenceLaw eps j : Measure ℝ)) ≤ 1 ∧
      (Integrable (fun z => Real.exp (theta * z)) (kepReferenceLaw eps j : Measure ℝ) ∧
        ∫ z, Real.exp (theta * z) ∂(kepReferenceLaw eps j : Measure ℝ) ≤ 73) ∧
      (Integrable (fun z => Real.exp ((theta / R) * z)) (kepReferenceLaw eps j : Measure ℝ) ∧
        ∫ z, Real.exp ((theta / R) * z) ∂(kepReferenceLaw eps j : Measure ℝ) ≤ 73) := by
    have hm := (href' j).2.2 theta htheta.le hthetaRefLe
    have hmScale := (href' j).2.2 (theta / R) (div_nonneg htheta.le hR.le)
      ((div_le_self htheta.le hR1).trans hthetaRefLe)
    exact ⟨(href' j).1, (href' j).2.1.le, ⟨hm.1, hm.2.trans (by norm_num)⟩,
      hmScale.1, hmScale.2.trans (by norm_num)⟩
  have hbaseData (n : ℝ) (hn : 1 ≤ n) (x : ℝ) :
      measureHellinger (kepPoissonLayerMeasure hf eps n x 0) (kepReferenceLaw eps 0) ≤ Kbase / n ∧
      Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n x 0) ∧
        ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n x 0 ≤ 73 := by
    have hn0 := zero_lt_one.trans_le hn
    have h : measureHellinger (kepPoissonLayerMeasure hf eps n x 0) (expMeasure 1) ≤ Kbase / n ∧
        Integrable (fun z => Real.exp (thetaBase * z)) (kepPoissonLayerMeasure hf eps n x 0) ∧
          ∫ z, Real.exp (thetaBase * z) ∂kepPoissonLayerMeasure hf eps n x 0 ≤ 2 := by
      simpa only [kepPoissonLayerMeasure_zero] using hbase n hn0 x
    have hpos := kepPoissonLayerMeasure_ae_nonneg hf hn0 x 0 (hs.2.1 0).le
    have hi : Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n x 0) := by
      apply h.2.1.mono' (by fun_prop)
      filter_upwards [hpos] with z hz
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hthetaBaseLe hz)
    have hb : ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n x 0 ≤ 2 := by
      apply (integral_mono_ae hi h.2.1 _).trans h.2.2
      filter_upwards [hpos] with z hz
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hthetaBaseLe hz)
    refine ⟨?_, hi, hb.trans (by norm_num)⟩
    simpa only [kepReferenceLaw_zero, expPM, ProbabilityMeasure.coe_mk] using h.1
  have hgrowth (j : ℕ) : kepReferenceSpan eps j ≤ kepReferenceSpan eps (j + 1) := by
    have h := hs.2.2.1 j
    have hp := (hs.2.1 j).le
    linarith
  exact kepPoisson_joint_induction hf htheta hD hdrift hdriftD hA.le he1 hclass hs.1 hs.2.1
    hgrowth hrefData hKbase.le hKbaseD hbaseData
    (fun n hn j r herr => hstep eps heDrift n hn j (hs.2.1 j).le r herr)
    hM1 hM' hQwindow' hQtail' hdeltaWindow hdeltaMean hC hsmall hcost hscale hdom

end

end PGM
