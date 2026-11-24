import PLAStochastic.Index.CEPS.Band.WidthContinuity

/-!
# Width Hadamard identity with slightly growing complex discount

This extends the summation argument of `Actual.Hadamard` using the uniform
killed gap, rather than the restriction `Re q ≥ 0`. The finite-time identity
and the actual pointwise density representatives are unchanged.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

/-- Absolute survival series on the slightly growing discount half-plane. -/
theorem cepsBand_summable_survival_norm {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l)
    (hlw : l ≤ 2 * w) (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) (y : ℝ) :
    Summable (fun n : ℕ => ‖Complex.exp (-q * n) *
      (krSurv (Icc 0 l) (ν : Measure ℝ) β a n y : ℂ)‖) := by
  have hs := (cepsBand_survival_moments hD hθ hvlo hvhi hν hw hl hlw β ha hq 0 y).1
  simp only [pow_zero, one_mul] at hs
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (krSurv_nonneg measurableSet_Icc ν β a _ y)] using hs

/-- Absolute pointwise density series on the same half-plane. -/
theorem cepsBand_summable_density_norm {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) (y z : ℝ) :
    Summable (fun n : ℕ => ‖Complex.exp (-q * ((n : ℂ) + 1)) *
      (krDens (Icc 0 l) ν f β a (n + 1) y z : ℂ)‖) := by
  have hs := (cepsBand_density_moments hD hθ hvlo hvhi hν hf hw hl hlw β ha hq 0 y z).1
  simp only [pow_zero, one_mul] at hs
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (krDens_nonneg ν hf.nonneg _ _ _)] using hs

/-- The actual width identity is valid throughout the killed-gap discount half-plane. -/
theorem cepsBand_bottomSurv_sub {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {w : ℝ} (hw : 2 ≤ w) (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re)
    {l₁ l₂ : ℝ} (hl₁ : w / 2 ≤ l₁) (hl : l₁ ≤ l₂) (hl₂ : l₂ ≤ 2 * w) :
    IntegrableOn (fun z => cepsBridgeSeries ν f β a q z * cepsTopSurv ν β a q z) (Ioc l₁ l₂) ∧
      cepsBottomSurv ν β a q l₂ - cepsBottomSurv ν β a q l₁ =
        ∫ z in Ioc l₁ l₂, cepsBridgeSeries ν f β a q z * cepsTopSurv ν β a q z := by
  have ha0 : a ≠ 0 := by intro h; simp only [h, abs_zero] at ha; linarith
  have hl0 : 0 ≤ l₁ := by linarith
  let L : ℕ → ℝ → ℂ := fun K z => Complex.exp (-q * ((K : ℂ) + 1)) *
    (cepsHadamardLayer ν f β a K z : ℂ)
  have hpt : ∀ z ∈ Icc l₁ l₂, HasSum (fun K => L K z)
      (cepsBridgeSeries ν f β a q z * cepsTopSurv ν β a q z) := by
    intro z hz
    let u := fun k : ℕ => Complex.exp (-q * ((k : ℂ) + 1)) *
      (krDens (Icc 0 z) ν f β a (k + 1) 0 z : ℂ)
    let v := fun m : ℕ => Complex.exp (-q * m) * (krSurv (Icc 0 z) (ν : Measure ℝ) β a m z : ℂ)
    have hus : Summable fun k => ‖u k‖ := cepsBand_summable_density_norm hD hθ hvlo hvhi hν hf hw
      (hl₁.trans hz.1) (hz.2.trans hl₂) β ha hq 0 z
    have hvs : Summable fun m => ‖v m‖ := cepsBand_summable_survival_norm hD hθ hvlo hvhi hν hw
      (hl₁.trans hz.1) (hz.2.trans hl₂) β ha hq z
    have hEs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hus hvs).of_norm
    have hcp := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hus hvs
    have hlayer : ∀ K, ∑ p ∈ Finset.antidiagonal K, u p.1 * v p.2 = L K z := by
      intro K
      dsimp [L]
      unfold cepsHadamardLayer
      rw [Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpK := Finset.mem_antidiagonal.1 hp
      have hexp : Complex.exp (-q * ((K : ℂ) + 1)) =
          Complex.exp (-q * ((p.1 : ℂ) + 1)) * Complex.exp (-q * (p.2 : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        rw [← hpK]
        push_cast
        ring
      rw [hexp]
      dsimp [u, v]
      push_cast
      ring
    change HasSum (fun K => L K z) ((∑' k, u k) * ∑' m, v m)
    rw [hcp]
    simp only [hlayer] at hEs ⊢
    exact hEs.hasSum
  have hlay := fun K => hf.integral_cepsHadamardLayer ha0 β hl0 hl K
  have hLint : ∀ K, IntegrableOn (L K) (Ioc l₁ l₂) := fun K =>
    ((hlay K).1.ofReal).const_mul _
  let F := fun K : ℕ => ‖Complex.exp (-q * ((K : ℂ) + 1))‖ *
    (krSurv (Icc 0 l₂) (ν : Measure ℝ) β a (K + 1) 0 -
      krSurv (Icc 0 l₁) (ν : Measure ℝ) β a (K + 1) 0)
  have hnn : ∀ K, 0 ≤ krSurv (Icc 0 l₂) (ν : Measure ℝ) β a (K + 1) 0 -
      krSurv (Icc 0 l₁) (ν : Measure ℝ) β a (K + 1) 0 := fun K =>
    (hf.cepsBand_survival_width_le ha0 β hl0 hl (K + 1)).1
  have hF0 : ∀ K, 0 ≤ F K := fun K => mul_nonneg (norm_nonneg _) (hnn K)
  have hRsum : Summable F := by
    have hs := (cepsBand_survival_moments hD hθ hvlo hvhi hν hw (hl₁.trans hl) hl₂ β ha hq 0 0).1
    simp only [pow_zero, one_mul] at hs
    have hs' := (summable_nat_add_iff 1).2 hs
    simp only [Nat.cast_add, Nat.cast_one] at hs'
    refine hs'.of_nonneg_of_le hF0 fun K => ?_
    exact mul_le_mul_of_nonneg_left (sub_le_self _
      (krSurv_nonneg measurableSet_Icc ν β a (K + 1) 0)) (norm_nonneg _)
  have hlin : ∑' K, ∫⁻ z in Ioc l₁ l₂, ‖L K z‖ₑ ≠ ⊤ := by
    have heq : ∀ K, ∫⁻ z in Ioc l₁ l₂, ‖L K z‖ₑ = ENNReal.ofReal (F K) := by
      intro K
      rw [← ofReal_integral_norm_eq_lintegral_enorm (hLint K)]
      congr 1
      have hn : ∀ z, ‖L K z‖ = ‖Complex.exp (-q * ((K : ℂ) + 1))‖ *
          cepsHadamardLayer ν f β a K z := by
        intro z
        dsimp [L]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hf.cepsHadamardLayer_nonneg β a K z)]
      simp_rw [hn]
      rw [integral_const_mul, (hlay K).2]
    simp_rw [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg hF0 hRsum]
    exact ENNReal.ofReal_ne_top
  have hexch : ∫ z in Ioc l₁ l₂, (∑' K, L K z) = ∑' K, ∫ z in Ioc l₁ l₂, L K z :=
    integral_tsum (fun K => (hLint K).aestronglyMeasurable) hlin
  have hpt' : ∀ z ∈ Ioc l₁ l₂, ∑' K, L K z =
      cepsBridgeSeries ν f β a q z * cepsTopSurv ν β a q z := fun z hz =>
    (hpt z ⟨hz.1.le, hz.2⟩).tsum_eq
  refine ⟨?_, ?_⟩
  · have hm : AEStronglyMeasurable (fun z => cepsBridgeSeries ν f β a q z * cepsTopSurv ν β a q z)
        (volume.restrict (Ioc l₁ l₂)) := by
      refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N z =>
        ∑ K ∈ Finset.range N, L K z) (fun N => (integrable_finsetSum _ fun K _ =>
          hLint K).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      exact (hpt z ⟨hz.1.le, hz.2⟩).tendsto_sum_nat
    refine ⟨hm, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 hlin)
    rw [← lintegral_tsum fun K => (hLint K).aestronglyMeasurable.enorm]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    rw [← hpt' z hz]
    exact enorm_tsum_le_tsum_enorm
  · have hs₁ := (cepsBand_summable_survival_norm hD hθ hvlo hvhi hν hw hl₁
        (hl.trans hl₂) β ha hq 0).of_norm
    have hs₂ := (cepsBand_summable_survival_norm hD hθ hvlo hvhi hν hw
        (hl₁.trans hl) hl₂ β ha hq 0).of_norm
    have hdiff : cepsBottomSurv ν β a q l₂ - cepsBottomSurv ν β a q l₁ =
        ∑' n : ℕ, Complex.exp (-q * n) * ((krSurv (Icc 0 l₂) (ν : Measure ℝ) β a n 0 -
          krSurv (Icc 0 l₁) (ν : Measure ℝ) β a n 0 : ℝ) : ℂ) := by
      unfold cepsBottomSurv
      rw [← hs₂.tsum_sub hs₁]
      congr 1
      funext n
      push_cast
      ring
    have hsum2 : Summable fun n : ℕ => Complex.exp (-q * n) *
        ((krSurv (Icc 0 l₂) (ν : Measure ℝ) β a n 0 -
          krSurv (Icc 0 l₁) (ν : Measure ℝ) β a n 0 : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_sub, mul_sub] using hs₂.sub hs₁
    rw [hdiff, tsum_eq_zero_add' ((summable_nat_add_iff 1).2 hsum2)]
    have h0 : Complex.exp (-q * ((0 : ℕ) : ℂ)) * ((krSurv (Icc 0 l₂) (ν : Measure ℝ) β a 0 0 -
        krSurv (Icc 0 l₁) (ν : Measure ℝ) β a 0 0 : ℝ) : ℂ) = 0 := by
      have e1 : ∀ z : ℝ, 0 ≤ z → krSurv (Icc 0 z) (ν : Measure ℝ) β a 0 0 = 1 := fun z hz => by
        rw [krSurv_eq_integral measurableSet_Icc]
        simp [krAlive_zero, indicator_of_mem (show (0 : ℝ) ∈ Icc 0 z from ⟨le_rfl, hz⟩)]
      rw [e1 l₂ (hl0.trans hl), e1 l₁ hl0]
      simp
    rw [h0, zero_add, ← setIntegral_congr_fun measurableSet_Ioc hpt', hexch]
    congr 1
    funext K
    dsimp [L]
    rw [integral_const_mul, integral_complex_ofReal, (hlay K).2]
    push_cast
    ring_nf

end
end PGM
