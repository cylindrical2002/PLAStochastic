import PLAStochastic.Swing.Gaussian.Survival.SmallDrift
import PLAStochastic.ForMathlib.Topology.UniformSpace.CompactJointConvergence

/-! Compact-uniform small-drift asymptotics for actual Gaussian survival. -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false


variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The paper's shift w+a is included before uniformity is asserted. -/
theorem gaussianInfiniteSurvival_small_drift_uniform_sequence
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (ha' : ∀ n, a n ≤ 1/2)
    (halim : Tendsto a atTop (𝓝 0)) {K : Set ℝ} (hK : IsCompact K) (hKn : K ⊆ Ici 0) :
    TendstoUniformlyOn (fun n w => gaussianInfiniteSurvival X μ (w+a n) (a n)/(2*a n))
      (gaussianRenewalPotential X μ) atTop K := by
  apply tendstoUniformlyOn_of_joint_sequence hK ((gaussianRenewalPotential_continuousOn hX hi hG).mono hKn)
  intro k hk u hu w hw hwt
  have hat := halim.comp hk
  have hxt : Tendsto (fun n => u n+a (k n)) atTop (𝓝 w) := by
    simpa only [add_zero, Function.comp_def] using! hwt.add hat
  exact gaussianInfiniteSurvival_small_drift hX hi hG
    (fun n => add_nonneg (hKn (hu n)) (ha (k n)).le) (fun n => ha (k n)) (fun n => ha' (k n))
    hxt hat (hKn hw)

/-- C.3 small-drift survival is uniform on every compact subset of the nonnegative half-line. -/
theorem gaussianInfiniteSurvival_small_drift_uniform
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {K : Set ℝ} (hK : IsCompact K) (hKn : K ⊆ Ici 0) :
    TendstoUniformlyOn (fun a w => gaussianInfiniteSurvival X μ (w+a) a/(2*a))
      (gaussianRenewalPotential X μ) (𝓝[>] 0) K := by
  apply tendstoUniformlyOn_of_seq_tendstoUniformlyOn
  intro a ha
  have ha0 : Tendsto a atTop (𝓝 0) := ha.mono_right nhdsWithin_le_nhds
  have har : ∀ᶠ n in atTop, 0 < a n ∧ a n ≤ 1/2 := by
    have hp := (tendsto_nhdsWithin_iff.mp ha).2
    have hu := ha0.eventually (Iio_mem_nhds (show (0 : ℝ) < 1/2 by norm_num))
    exact hp.and (hu.mono (fun _ h => h.le))
  let b := fun n => if 0 < a n ∧ a n ≤ 1/2 then a n else (1/4 : ℝ)
  have hb (n : ℕ) : 0 < b n ∧ b n ≤ 1/2 := by
    dsimp [b]
    split_ifs with h
    · exact h
    · norm_num
  have hba : b =ᶠ[atTop] a := har.mono (fun n hn => if_pos hn)
  have hb0 : Tendsto b atTop (𝓝 0) := ha0.congr' hba.symm
  have hh := gaussianInfiniteSurvival_small_drift_uniform_sequence hX hi hG
    (fun n => (hb n).1) (fun n => (hb n).2) hb0 hK hKn
  apply hh.congr
  filter_upwards [hba] with n hn
  intro w _
  rw [hn]

end SwingRepair
