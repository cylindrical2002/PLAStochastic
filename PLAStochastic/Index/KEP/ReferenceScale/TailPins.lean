import PLAStochastic.Index.KEP.ReferenceScale.TailTransport
import PLAStochastic.Index.KEP.ReferenceScale.ActualBridgeWard

/-!
# Every exterior-tail pin, with the final Dirac suffix

The range has `n` terms for an `n`-step tail. Its last suffix has zero steps.
The exact identification uses the unchanged actual killed row `krRow` and the
pointwise actual density `krDens`; no density is substituted for the Dirac row.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

theorem kepTailFluxTest_eq_sum {p : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (w σ s : ℝ) (n : ℕ) (x : ℝ)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    kepTailFluxTest p w σ s n x φ =
      -∑ l ∈ Finset.range n,
        ((w - x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x w *
            kepTailTest p w s (n - 1 - l) w φ -
          (-x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x 0 *
            kepTailTest p w s (n - 1 - l) 0 φ) := by
  cases n with
  | zero => simp [kepTailFluxTest]
  | succ n =>
    have hs : (∫ y in Ioc 0 w, kepBridgeTransportFlux p w σ s n x y * φ y) =
        ∑ l ∈ Finset.range n,
          ((w - x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x w *
              kepTailTest p w s (n - l) w φ -
            (-x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x 0 *
              kepTailTest p w s (n - l) 0 φ) := by
      simp_rw [kepBridgeTransportFlux_eq_sum hp, Finset.sum_mul]
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro l hl
        have hl' := Finset.mem_range.mp hl
        have hlen : n - l = n - 1 - l + 1 := by omega
        rw [hlen]
        simp only [kepTailTest]
        have hk (b : ℝ) : Continuous (kepFixedBridge p w s (n - 1 - l) b) :=
          (continuous_kepFixedBridge hp w (n - 1 - l)).comp
            (continuous_const.prodMk (continuous_const.prodMk continuous_id))
        let U := (w - x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x w
        let V := (-x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x 0
        change (∫ y in Ioc 0 w,
          (U * kepFixedBridge p w s (n - 1 - l) w y -
            V * kepFixedBridge p w s (n - 1 - l) 0 y) * φ y) = _
        calc
          _ = ∫ y in Ioc 0 w,
              U * (kepFixedBridge p w s (n - 1 - l) w y * φ y) -
                V * (kepFixedBridge p w s (n - 1 - l) 0 y * φ y) := by
            apply integral_congr_ae
            exact ae_of_all _ fun y => by dsimp only; ring
          _ = _ := by
            rw [integral_sub (f := fun y => U *
              (kepFixedBridge p w s (n - 1 - l) w y * φ y))
              (g := fun y => V * (kepFixedBridge p w s (n - 1 - l) 0 y * φ y))
              (((hk w).mul hφ).const_mul U |>.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
              (((hk 0).mul hφ).const_mul V |>.integrableOn_Icc.mono_set Ioc_subset_Icc_self),
              integral_const_mul, integral_const_mul]
      · intro l hl
        have hk (b : ℝ) : Continuous (kepFixedBridge p w s (n - 1 - l) b) :=
          (continuous_kepFixedBridge hp w (n - 1 - l)).comp
            (continuous_const.prodMk (continuous_const.prodMk continuous_id))
        exact (by fun_prop : Continuous _).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    rw [kepTailFluxTest, hs, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, kepTailTest]
    ring

/-- The evaluation functional really is the actual killed row, at every step
count, including zero. The bounded test is only needed for the existing row API. -/
theorem kepTailTest_eq_krRow (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {D w σ : ℝ} (hf : Measurable f) (hf0 : ∀ t, 0 ≤ f t) (hfD : ∀ t, f t ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (f t)))
    (hσ : σ = 1 ∨ σ = -1) (s : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ Icc 0 w)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) :
    kepTailTest (kepLogStep f σ) w s n x φ =
      krRow (Icc 0 w) (ν : Measure ℝ) σ (σ * Real.exp s) n φ x := by
  cases n with
  | zero => simp only [kepTailTest, krRow_zero, indicator_of_mem hx]
  | succ n =>
    have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    rw [krRow_succ_eq_integral_krDens ν measurableSet_Icc measure_Icc_lt_top.ne
      hf hf0 hfD hν (mul_ne_zero hσ0 (Real.exp_ne_zero s)) n hφ hM,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Icc (0 : ℝ) w)
        (fun y hy => by rw [krDens_eq_zero_of_right_notMem ν hy, zero_mul]),
      integral_Icc_eq_integral_Ioc]
    unfold kepTailTest
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    dsimp only
    rw [kepLogBridge_eq_krDens ν hf hf0 hfD hν hσ s n hx ⟨hy.1.le, hy.2⟩]

def kepActualTailLogFlux (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (w σ a : ℝ) (n : ℕ) (x : ℝ) (φ : ℝ → ℝ) : ℝ :=
  -∑ l ∈ Finset.range n,
    ((w - x - (l + 1 : ℕ) * σ) * krDens (Icc 0 w) ν f σ (σ * a) (l + 1) x w *
        krRow (Icc 0 w) (ν : Measure ℝ) σ (σ * a) (n - 1 - l) φ w -
      (-x - (l + 1 : ℕ) * σ) * krDens (Icc 0 w) ν f σ (σ * a) (l + 1) x 0 *
        krRow (Icc 0 w) (ν : Measure ℝ) σ (σ * a) (n - 1 - l) φ 0)

theorem kepTailFluxTest_eq_actual (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {D w σ : ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t) (hfD : ∀ t, f t ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (f t)))
    (hσ : σ = 1 ∨ σ = -1) (s : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ Icc 0 w)
    {φ : ℝ → ℝ} (hφ : Continuous φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) :
    kepTailFluxTest (kepLogStep f σ) w σ s n x φ =
      kepActualTailLogFlux ν f w σ (Real.exp s) n x φ := by
  rw [kepTailFluxTest_eq_sum (continuous_kepLogStep hf σ) w σ s n x hφ]
  unfold kepActualTailLogFlux
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  have hw : 0 ≤ w := hx.1.trans hx.2
  have h0 : (0 : ℝ) ∈ Icc 0 w := ⟨le_rfl, hw⟩
  have hw' : w ∈ Icc (0 : ℝ) w := ⟨hw, le_rfl⟩
  rw [kepLogBridge_eq_krDens ν hf.measurable hf0 hfD hν hσ s l hx hw',
    kepLogBridge_eq_krDens ν hf.measurable hf0 hfD hν hσ s l hx h0,
    kepTailTest_eq_krRow ν hf.measurable hf0 hfD hν hσ s (n - 1 - l) hw' hφ.measurable hM,
    kepTailTest_eq_krRow ν hf.measurable hf0 hfD hν hσ s (n - 1 - l) h0 hφ.measurable hM]

theorem kepReference_tailFluxTest_eq_actual {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {w σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (s : ℝ) (n : ℕ)
    {x : ℝ} (hx : x ∈ Icc 0 w) {φ : ℝ → ℝ} (hφ : Continuous φ)
    {M : ℝ} (hM : ∀ y, |φ y| ≤ M) :
    let f := (kepReferenceDensity heps hj).density
    kepTailFluxTest (kepLogStep f σ) w σ s n x φ =
      kepActualTailLogFlux (kepReferenceLaw eps j) f w σ (Real.exp s) n x φ := by
  have hc := kepReferenceDensity_classical heps hj
  have hν : (kepReferenceLaw eps j : Measure ℝ) = volume.withDensity
      (fun t => ENNReal.ofReal ((kepReferenceDensity heps hj).density t)) := by
    rw [← kepReferenceDensity_toMeasure heps hj]
    rfl
  exact kepTailFluxTest_eq_actual (kepReferenceLaw eps j)
    (continuous_iff_continuousAt.mpr fun t => (hc.2.1 t).continuousAt)
    (kepReferenceDensity heps hj).nonneg (kepReferenceDensity_le_span heps hj)
    hν hσ s n hx hφ hM

end

end PGM
