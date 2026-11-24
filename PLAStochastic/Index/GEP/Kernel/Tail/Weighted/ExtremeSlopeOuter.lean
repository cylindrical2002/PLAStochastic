import PLAStochastic.Index.GEP.Kernel.Tail.Scalar.OuterGreen
import PLAStochastic.Index.GEP.SurvivalBound.AbsoluteBounds

/-!
# Physical-sum weighted outer rows at extreme slopes

The exponential reward is integrated against the actual path's physical gap
sum. At short times it is bounded by the unrestricted moment generating
function; at long times the band constraint implies a genuine large-deviation
event. Thus no factor `exp(s*w/a)` is introduced near slope zero.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 800000

/-- The actual physical-sum weighted survival mass. -/
def kernelPhysicalSurv (J : Set ℝ) (ν : ProbabilityMeasure ℝ)
    (β a s : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  ∫ g, krAlive J β a n y g * Real.exp (s * gapKeys g n) ∂iidLaw ν

theorem kernelPhysicalSurv_nonneg (J : Set ℝ) (ν : ProbabilityMeasure ℝ)
    (β a s : ℝ) (n : ℕ) (y : ℝ) : 0 ≤ kernelPhysicalSurv J ν β a s n y :=
  integral_nonneg fun _ => mul_nonneg (krAlive_nonneg _ _ _) (Real.exp_nonneg _)

theorem kernelPhysicalSurv_zero_weight {J : Set ℝ} (hJ : MeasurableSet J)
    (ν : ProbabilityMeasure ℝ) (β a : ℝ) (n : ℕ) (y : ℝ) :
    kernelPhysicalSurv J ν β a 0 n y = krSurv J (ν : Measure ℝ) β a n y := by
  simp only [kernelPhysicalSurv, zero_mul, Real.exp_zero, mul_one,
    krSurv_eq_integral hJ ν β a n y]

/-- Survival at an extreme slope and a time at least four band widths forces
the same weighted large-deviation event used by the original survival proof. -/
theorem kernel_physical_extreme_indicator (α w a : ℝ) (hw : 0 < w) (ha : 0 < a)
    (hfar : a ≤ 1 / 2 ∨ 2 ≤ a) (β a' : ℝ)
    (hdir : (β = 1 ∧ a' = a) ∨ (β = -1 ∧ a' = -a))
    (n : ℕ) (hn : 4 * w ≤ (n : ℝ)) (y : ℝ) (s : ℝ) (g : ℕ → ℝ) :
    krAlive (Icc α (α + w)) β a' n y g * Real.exp (s * gapKeys g n) ≤
      {g : ℕ → ℝ | 3 * n / 2 ≤ gapKeys g n ∨ gapKeys g n ≤ 5 * n / 8}.indicator
        (fun g => Real.exp (s * gapKeys g n)) g := by
  by_cases hy : y ∈ Icc α (α + w)
  · by_cases hz : kWalk y β a' g n ∈ Icc α (α + w)
    · have hband : -(w : ℝ) ≤ (n : ℝ) - a * gapKeys g n ∧
          (n : ℝ) - a * gapKeys g n ≤ w := by
        rcases hdir with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [mem_Icc, kWalk, mul_one] at hy hz
          constructor <;> linarith [hy.1, hy.2, hz.1, hz.2]
        · simp only [mem_Icc, kWalk] at hy hz
          constructor <;> nlinarith [hy.1, hy.2, hz.1, hz.2]
      have hbad : 3 * n / 2 ≤ gapKeys g n ∨ gapKeys g n ≤ 5 * n / 8 := by
        by_cases hS : 0 ≤ gapKeys g n
        · rcases hfar with halo | hahi
          · left
            have hh := mul_le_mul_of_nonneg_right halo hS
            nlinarith [hband.2]
          · right
            have hh := mul_le_mul_of_nonneg_right hahi hS
            nlinarith [hband.1]
        · right
          have hn0 : 0 ≤ (n : ℝ) := by positivity
          linarith
      have hmem : g ∈ {g : ℕ → ℝ | 3 * n / 2 ≤ gapKeys g n ∨ gapKeys g n ≤ 5 * n / 8} := hbad
      rw [indicator_of_mem hmem]
      exact mul_le_of_le_one_left (Real.exp_nonneg _) (krAlive_le_one _ _ _)
    · have he := krAlive_mul_indicator (J := Icc α (α + w)) (β := β) (a := a') n y g
      rw [indicator_of_notMem hz, mul_zero] at he
      rw [← he, zero_mul]
      exact indicator_nonneg (fun _ _ => Real.exp_nonneg _) _
  · rw [krAlive_eq_zero_of_notMem hy, zero_mul]
    exact indicator_nonneg (fun _ _ => Real.exp_nonneg _) _

/-- The physical-sum weighted survival mass has an exponential time tail at
both extreme slope ends. Its weight range is fixed independently of the later
arbitrary input-tail exponent. -/
theorem RegLaw.kernelPhysicalSurv_extreme_tail {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (α w a : ℝ) (hw : 0 < w) (ha : 0 < a) (hfar : a ≤ 1 / 2 ∨ 2 ≤ a)
    (β a' : ℝ) (hdir : (β = 1 ∧ a' = a) ∨ (β = -1 ∧ a' = -a))
    (n : ℕ) (hn : 4 * w ≤ (n : ℝ)) {s : ℝ}
    (hs0 : 0 ≤ s) (hsθ : s ≤ θ / 4) (hs : s ≤ surv_rate (θ / 2) (2 * D / θ) / 8) (y : ℝ) :
    kernelPhysicalSurv (Icc α (α + w)) ν β a' s n y ≤
      3 * Real.exp (-(surv_rate (θ / 2) (2 * D / θ) * n)) := by
  have hn1 : 1 ≤ n := by
    have : 0 < (n : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨hi, _⟩ := surv_mgf_le (half_pos hθ) (hν.pos' hθ hvlo) hν.mean
    (hν.expMom hθ) hs0 (by linarith) n
  have hbad : MeasurableSet {g : ℕ → ℝ | 3 * n / 2 ≤ gapKeys g n ∨ gapKeys g n ≤ 5 * n / 8} :=
    (measurableSet_le measurable_const (rawAsm_measurable_gapKeys n)).union
      (measurableSet_le (rawAsm_measurable_gapKeys n) measurable_const)
  apply (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun g => mul_nonneg (krAlive_nonneg _ _ _) (Real.exp_nonneg _))
    (hi.indicator hbad)
    (Filter.Eventually.of_forall fun g => kernel_physical_extreme_indicator α w a hw ha hfar β a' hdir n hn y s g)).trans
  exact surv_bad_integral_le (half_pos hθ) (hν.pos' hθ hvlo) hν.mean (hν.expMom hθ) hn1 hs0 hs

/-- At short times the unrestricted physical moment controls the actual
weighted path integral, with no inverse slope in the bound. -/
theorem RegLaw.kernelPhysicalSurv_head {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (J : Set ℝ) (β a : ℝ) {w s : ℝ} (hw : 1 ≤ w)
    (hs0 : 0 ≤ s) (hsθ : s ≤ θ / 4) (hsw : s ≤ 1 / w)
    (n : ℕ) (hn : (n : ℝ) ≤ 4 * w) (y : ℝ) :
    kernelPhysicalSurv J ν β a s n y ≤ Real.exp (4 * (1 + surv_mgfC (θ / 2) (2 * D / θ))) := by
  obtain ⟨hi, hb⟩ := surv_mgf_le (half_pos hθ) (hν.pos' hθ hvlo) hν.mean
    (hν.expMom hθ) hs0 (by linarith) n
  have hm : kernelPhysicalSurv J ν β a s n y ≤
      ∫ g, Real.exp (s * gapKeys g n) ∂iidLaw ν := by
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun g => mul_nonneg (krAlive_nonneg _ _ _) (Real.exp_nonneg _)) hi
    exact Filter.Eventually.of_forall fun g =>
      mul_le_of_le_one_left (Real.exp_nonneg _) (krAlive_le_one _ _ _)
  apply (hm.trans hb).trans
  apply Real.exp_le_exp.mpr
  have hw0 : 0 < w := by linarith
  have hsw' : s * w ≤ 1 := (le_div_iff₀ hw0).mp hsw
  have hs1 : s ≤ 1 := by nlinarith
  have hns : (n : ℝ) * s ≤ 4 := by
    have hh := mul_le_mul_of_nonneg_right hn hs0
    nlinarith
  have hC : 0 ≤ surv_mgfC (θ / 2) (2 * D / θ) := by
    unfold surv_mgfC
    exact div_nonneg (mul_nonneg (by norm_num) (div_nonneg
      (mul_nonneg (by norm_num) hν.D_nonneg) hθ.le)) (sq_nonneg _)
  have hs2 : s ^ 2 ≤ s := by nlinarith
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hs2 (mul_nonneg hn0 hC)
  have hh' := mul_le_mul_of_nonneg_left hns hC
  nlinarith

/-- Actual weighted outer Green sums are linear in width at both extreme
slope ends. The allowed physical weight is fixed by class constants and the
width; no eventual input-tail exponent occurs in the statement. -/
theorem kernel_regLaw_weighted_outer_green_extreme (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) :
    ∃ s₀ K : ℝ, 0 < s₀ ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ α w a : ℝ, 1 ≤ w → 0 < a → (a ≤ 1 / 2 ∨ 2 ≤ a) →
      ∀ β a' : ℝ, (β = 1 ∧ a' = a) ∨ (β = -1 ∧ a' = -a) →
      ∀ s : ℝ, 0 ≤ s → s ≤ s₀ → s ≤ 1 / w → ∀ y : ℝ,
        Summable (fun n : ℕ => kernelPhysicalSurv (Icc α (α + w)) ν β a' s n y) ∧
        (∑' n : ℕ, kernelPhysicalSurv (Icc α (α + w)) ν β a' s n y) ≤ K * w := by
  let c := surv_rate (θ / 2) (2 * D / θ)
  have hc : 0 < c := surv_rate_pos (by positivity) (by positivity)
  let B := 3 + Real.exp (4 * (1 + surv_mgfC (θ / 2) (2 * D / θ)))
  have hB : 0 < B := by positivity
  refine ⟨min (θ / 4) (c / 8), B * (6 + 1 / c), lt_min (by positivity) (by positivity), by positivity, ?_⟩
  intro ν hν α w a hw ha hfar β a' hdir s hs0 hs hsw y
  have hsθ : s ≤ θ / 4 := hs.trans (min_le_left _ _)
  have hsc : s ≤ c / 8 := hs.trans (min_le_right _ _)
  let F (n : ℕ) := kernelPhysicalSurv (Icc α (α + w)) ν β a' s n y
  have hF n : 0 ≤ F n := kernelPhysicalSurv_nonneg _ _ _ _ _ _ _
  have htail (n : ℕ) (hn : 4 * w ≤ (n : ℝ)) : F n ≤ B * Real.exp (-c * n) := by
    apply (hν.kernelPhysicalSurv_extreme_tail hθ hvlo α w a (by linarith) ha hfar β a' hdir n hn hs0 hsθ hsc y).trans
    have hB3 : 3 ≤ B := by dsimp [B]; linarith [Real.exp_pos (4 * (1 + surv_mgfC (θ / 2) (2 * D / θ)))]
    simpa only [c, neg_mul] using mul_le_mul_of_nonneg_right hB3 (Real.exp_nonneg (-c * n))
  have hFb (n : ℕ) : F n ≤ B := by
    by_cases hn : (n : ℝ) ≤ 4 * w
    · apply (hν.kernelPhysicalSurv_head hθ hvlo (Icc α (α + w)) β a' hw hs0 hsθ hsw n hn y).trans
      dsimp [B]
      linarith
    · apply (htail n (by linarith)).trans
      apply mul_le_of_le_one_right hB.le
      exact Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hsum (M : ℕ) : ∑ n ∈ Finset.range M, F n ≤ B * (6 + 1 / c) * w := by
    have hh := kernel_sum_head_exp_le
      (F := fun n => F n / B) (fun n => div_nonneg (hF n) hB.le)
      (fun n => (div_le_one hB).mpr (hFb n))
      (show 0 ≤ (4 : ℝ) by norm_num) hc hw
      (fun n hn => (div_le_iff₀ hB).mpr (by simpa [mul_comm] using htail n hn)) M
    rw [← Finset.sum_div] at hh
    have hh' := (div_le_iff₀ hB).mp hh
    norm_num at hh'
    exact hh'.trans_eq (by ring)
  exact ⟨summable_of_sum_range_le hF hsum, Real.tsum_le_of_sum_range_le hF hsum⟩

end
end PGM
