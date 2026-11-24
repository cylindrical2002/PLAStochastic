import PLAStochastic.Index.CEPS.Reward.TestEnvelope

/-! # Actual first-passage overshoots have exponential moments

Truncated bounded tests are identified by the proved renewal equation.
The exponential source envelope gives a truncation-independent bound;
monotone convergence then pays integrability, including unit discount.
-/

noncomputable section
open MeasureTheory Set Complex Filter Topology
namespace PGM.WienerHopf

def overshootExp (κ x : ℝ) (ω : ℕ → ℝ) : ℝ :=
  if firstEntry (Ioi x) ω < ⊤ then
    Real.exp (κ * (entryValue (Ioi x) ω - x)) else 0

theorem overshootExp_nonneg (κ x : ℝ) (ω : ℕ → ℝ) : 0 ≤ overshootExp κ x ω := by
  unfold overshootExp
  split_ifs
  · exact (Real.exp_pos _).le
  · rfl

theorem measurable_overshootExp (κ x : ℝ) : Measurable (overshootExp κ x) := by
  apply Measurable.ite (measurableSet_firstEntry_lt_top measurableSet_Ioi)
  · exact (measurable_const.mul
      ((measurable_entryValue measurableSet_Ioi).sub measurable_const)).exp
  · exact measurable_const

def overshootExpTest (κ : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  (min (n : ℝ) (Real.exp (κ * y)) : ℝ)

theorem measurable_overshootExpTest (κ : ℝ) (n : ℕ) :
    Measurable (overshootExpTest κ n) := by unfold overshootExpTest; fun_prop

theorem norm_overshootExpTest_le (κ : ℝ) (n : ℕ) (y : ℝ) :
    ‖overshootExpTest κ n y‖ ≤ n := by
  rw [overshootExpTest, norm_real, Real.norm_of_nonneg
    (le_min (Nat.cast_nonneg _) (Real.exp_pos _).le)]
  exact min_le_left _ _

theorem norm_overshootExpTest_le_exp (κ : ℝ) (n : ℕ) (y : ℝ) :
    ‖overshootExpTest κ n y‖ ≤ Real.exp (κ * y) := by
  rw [overshootExpTest, norm_real, Real.norm_of_nonneg
    (le_min (Nat.cast_nonneg _) (Real.exp_pos _).le)]
  exact min_le_right _ _

theorem passageTestReward_expTest_eq (κ x : ℝ) (n : ℕ) (ω : ℕ → ℝ) :
    passageTestReward 1 (overshootExpTest κ n) x ω =
      ((min (n : ℝ) (overshootExp κ x ω)) : ℝ) := by
  unfold passageTestReward overshootExp overshootExpTest
  split_ifs <;> simp

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {f : ℝ → ℝ} {D θ κ x : ℝ}

theorem integral_overshootExp_trunc_le (hf0 : ∀ y, 0 ≤ f y) (hfm : Measurable f)
    (hρ : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (hg : IsExpDensity (ladderDensity ρ f (Ioi 0) 1) D θ) (hθ : 0 < θ)
    (hκ : κ < θ) (hx : 0 ≤ x) (n : ℕ) :
    (∫ ω, min (n : ℝ) (overshootExp κ x ω) ∂pathLaw ρ) ≤
      rewardTestLocalBound D θ κ x := by
  have he := passageTestTransform_eq_rewardSolution hf0 hfm hρ hg hθ
    (s := 1) (by simp) (measurable_overshootExpTest κ n) (Nat.cast_nonneg n)
    (norm_overshootExpTest_le κ n) hx
  have hb := norm_rewardTestSolution_le hg hθ.le (measurable_overshootExpTest κ n)
    (B := 1) (κ := κ) (fun y _ => by simpa using norm_overshootExpTest_le_exp κ n y) hκ hx
  have hnorm : ‖passageTestTransform ρ 1 (overshootExpTest κ n) x‖ ≤
      rewardTestLocalBound D θ κ x := by rw [he]; simpa using hb
  have hcast : passageTestTransform ρ 1 (overshootExpTest κ n) x =
      ((∫ ω, min (n : ℝ) (overshootExp κ x ω) ∂pathLaw ρ) : ℝ) := by
    simp_rw [passageTestTransform, passageTestReward_expTest_eq]
    exact integral_complex_ofReal
  rw [hcast, norm_real, Real.norm_eq_abs] at hnorm
  exact (le_abs_self _).trans hnorm

/-- Exponential overshoot integrability is proved without prior first-passage finiteness. -/
theorem integrable_overshootExp (hf0 : ∀ y, 0 ≤ f y) (hfm : Measurable f)
    (hρ : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (hg : IsExpDensity (ladderDensity ρ f (Ioi 0) 1) D θ) (hθ : 0 < θ)
    (hκ : κ < θ) (hx : 0 ≤ x) : Integrable (overshootExp κ x) (pathLaw ρ) := by
  let F : ℕ → (ℕ → ℝ) → ℝ := fun n ω => min (n : ℝ) (overshootExp κ x ω)
  have hFm : ∀ n, Measurable (F n) := fun n => measurable_const.min (measurable_overshootExp κ x)
  have hF0 : ∀ n ω, 0 ≤ F n ω := fun n ω =>
    le_min (Nat.cast_nonneg _) (overshootExp_nonneg κ x ω)
  have hFi : ∀ n, Integrable (F n) (pathLaw ρ) := fun n =>
    (integrable_const (n : ℝ)).mono' (hFm n).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (hF0 n ω)]; exact min_le_left _ _)
  have hmono : ∀ ω, Monotone (fun n => ENNReal.ofReal (F n ω)) := by
    intro ω n m hnm
    apply ENNReal.ofReal_le_ofReal
    exact min_le_min (by exact_mod_cast hnm) le_rfl
  have hlim : ∀ ω, Tendsto (fun n => ENNReal.ofReal (F n ω)) atTop
      (𝓝 (ENNReal.ofReal (overshootExp κ x ω))) := by
    intro ω
    have he : (fun n : ℕ => ENNReal.ofReal (F n ω)) =ᶠ[atTop]
        (fun _ => ENNReal.ofReal (overshootExp κ x ω)) := by
      obtain ⟨N, hN⟩ := exists_nat_gt (overshootExp κ x ω)
      filter_upwards [eventually_ge_atTop N] with n hn
      dsimp [F]
      rw [min_eq_right (hN.le.trans (by exact_mod_cast hn))]
    exact tendsto_const_nhds.congr' he.symm
  have ht := lintegral_tendsto_of_tendsto_of_monotone (μ := pathLaw ρ)
    (fun n => (ENNReal.measurable_ofReal.comp (hFm n)).aemeasurable)
    (Eventually.of_forall hmono) (Eventually.of_forall hlim)
  have hbd : ∀ n, (∫⁻ ω, ENNReal.ofReal (F n ω) ∂pathLaw ρ) ≤
      ENNReal.ofReal (rewardTestLocalBound D θ κ x) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hFi n) (Eventually.of_forall (hF0 n))]
    exact ENNReal.ofReal_le_ofReal (integral_overshootExp_trunc_le hf0 hfm hρ hg hθ hκ hx n)
  have hfin : (∫⁻ ω, ENNReal.ofReal (overshootExp κ x ω) ∂pathLaw ρ) < ⊤ :=
    (le_of_tendsto ht (Eventually.of_forall hbd)).trans_lt ENNReal.ofReal_lt_top
  exact ⟨(measurable_overshootExp κ x).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (overshootExp_nonneg κ x))).mpr hfin⟩

end PGM.WienerHopf
