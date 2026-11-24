import PLAStochastic.ForMathlib.Probability.Kernel.Doeblin.BoundedReward
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # At most one invariant probability for a kernel dominating a common measure

This is the uniqueness argument of Theorem 4.3, in the abstract form it is used:
if a Markov kernel has a fixed nonzero measure absolutely continuous with respect
to each of its transitions, then it has at most one invariant probability.

The proof is the paper's: with `ν = ν₁ + ν₂` and `G = dν₁/dν`, invariance of both
laws makes `G` harmonic, the conditional Jensen inequality then holds with
equality, so `G` is constant on each transition and hence on the common measure.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
namespace KernelUnique
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {α : Type*} [MeasurableSpace α]

/-! ### Two elementary facts about a probability measure -/

theorem integrable_sub_const_sq (P : Measure α) [IsFiniteMeasure P] {g : α → ℝ} (m : ℝ)
    (hg : Integrable g P) (hg2 : Integrable (fun x => g x ^ 2) P) :
    Integrable (fun x => (g x - m)^2) P := by
  have h1 : Integrable (fun x => 2*m*g x) P := hg.const_mul (2*m)
  have h2 : Integrable (fun x => g x ^ 2 - 2*m*g x) P := hg2.sub h1
  have h3 : Integrable (fun x => (g x ^ 2 - 2*m*g x) + m^2) P := h2.add (integrable_const _)
  refine h3.congr ?_
  filter_upwards with x
  ring

theorem integral_sub_const_sq (P : Measure α) [IsProbabilityMeasure P] {g : α → ℝ} (m : ℝ)
    (hg : Integrable g P) (hg2 : Integrable (fun x => g x ^ 2) P) :
    (∫ x, (g x - m)^2 ∂P) = (∫ x, g x ^ 2 ∂P) - 2*m*(∫ x, g x ∂P) + m^2 := by
  have h1 : Integrable (fun x => 2*m*g x) P := hg.const_mul (2*m)
  have h2 : Integrable (fun x => g x ^ 2 - 2*m*g x) P := hg2.sub h1
  have hcongr : (∫ x, (g x - m)^2 ∂P) = ∫ x, ((g x ^ 2 - 2*m*g x) + m^2) ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
  rw [hcongr, integral_add h2 (integrable_const (m^2)), integral_sub hg2 h1,
    integral_const_mul, integral_const]
  simp

theorem sq_integral_le_integral_sq (P : Measure α) [IsProbabilityMeasure P] {g : α → ℝ}
    (hg : Integrable g P) (hg2 : Integrable (fun x => g x ^ 2) P) :
    (∫ x, g x ∂P)^2 ≤ ∫ x, g x ^ 2 ∂P := by
  have hzero : 0 ≤ ∫ x, (g x - (∫ y, g y ∂P))^2 ∂P := integral_nonneg (fun x => sq_nonneg _)
  rw [integral_sub_const_sq P (∫ y, g y ∂P) hg hg2] at hzero
  nlinarith

theorem ae_eq_mean_of_sq_integral_eq (P : Measure α) [IsProbabilityMeasure P] {g : α → ℝ}
    (hg : Integrable g P) (hg2 : Integrable (fun x => g x ^ 2) P)
    (h : (∫ x, g x ^ 2 ∂P) = (∫ x, g x ∂P)^2) :
    ∀ᵐ x ∂P, g x = ∫ y, g y ∂P := by
  set m : ℝ := ∫ y, g y ∂P with hm
  have hval := integral_sub_const_sq P m hg hg2
  rw [h, ← hm] at hval
  have hz : (∫ x, (g x - m)^2 ∂P) = 0 := by
    rw [hval]
    ring
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (g x - m))
    (integrable_sub_const_sq P m hg hg2)).mp hz
  filter_upwards [hae] with x hx
  have hx0 : (g x - m)^2 = 0 := hx
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx0
  linarith

/-! ### Transferring an invariance identity to integrals -/

variable {K : Kernel α α}

theorem lintegral_kernel_of_invariant {ν : Measure α} (hν : Kernel.Invariant K ν)
    {g : α → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x, (∫⁻ y, g y ∂K x) ∂ν) = ∫⁻ x, g x ∂ν := by
  have h := Measure.lintegral_bind (μ := ⇑K) (m := ν) (Kernel.aemeasurable K)
    hg.aemeasurable
  rw [hν.def] at h
  exact h.symm

theorem kernel_integral_eq_toReal [IsMarkovKernel K] {g : α → ℝ} (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) {C : ℝ} (hC : ∀ x, g x ≤ C) (x : α) :
    ENNReal.ofReal (∫ y, g y ∂K x) = ∫⁻ y, ENNReal.ofReal (g y) ∂K x := by
  have hP : IsProbabilityMeasure (K x) := IsMarkovKernel.isProbabilityMeasure x
  have hval : (∫ y, g y ∂K x) = (∫⁻ y, ENNReal.ofReal (g y) ∂K x).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0)
      hg.aestronglyMeasurable
  have hfin : (∫⁻ y, ENNReal.ofReal (g y) ∂K x) ≠ ⊤ := by
    have hle : (∫⁻ y, ENNReal.ofReal (g y) ∂K x) ≤ ∫⁻ _y, ENNReal.ofReal C ∂K x :=
      lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hC y)
    refine ne_top_of_le_ne_top ?_ hle
    rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_ne_top
  rw [hval, ENNReal.ofReal_toReal hfin]

theorem integral_kernel_of_invariant [IsMarkovKernel K] {ν : Measure α} [IsFiniteMeasure ν]
    (hν : Kernel.Invariant K ν) {g : α → ℝ} (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) {C : ℝ} (hC : ∀ x, g x ≤ C) :
    (∫ x, (∫ y, g y ∂K x) ∂ν) = ∫ x, g x ∂ν := by
  have hPK : ∀ x, IsProbabilityMeasure (K x) := fun x => IsMarkovKernel.isProbabilityMeasure x
  have hQ0 : ∀ x, 0 ≤ ∫ y, g y ∂K x := fun x => integral_nonneg hg0
  have hgint : ∀ x, Integrable g (K x) := by
    intro x
    have := hPK x
    exact Doeblin.integrable_bounded_reward (K x) hg hg0 hC
  have hQC : ∀ x, (∫ y, g y ∂K x) ≤ C := by
    intro x
    have := hPK x
    calc (∫ y, g y ∂K x) ≤ ∫ _y, C ∂K x :=
          integral_mono (hgint x) (integrable_const C) hC
      _ = C := by simp
  have hQmeas : Measurable (fun x => ∫ y, g y ∂K x) := by
    have hsm : StronglyMeasurable (fun p : α × α => g p.2) :=
      (hg.comp measurable_snd).stronglyMeasurable
    exact (hsm.integral_kernel_prod_right' (κ := K)).measurable
  have hfin : (∫⁻ x, ENNReal.ofReal (g x) ∂ν) ≠ ⊤ := by
    have hle : (∫⁻ x, ENNReal.ofReal (g x) ∂ν) ≤ ∫⁻ _x, ENNReal.ofReal C ∂ν :=
      lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hC x)
    refine ne_top_of_le_ne_top ?_ hle
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν univ)
  have hstep : (∫ x, (∫ y, g y ∂K x) ∂ν) =
      (∫⁻ x, ENNReal.ofReal (∫ y, g y ∂K x) ∂ν).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hQ0)
      hQmeas.aestronglyMeasurable
  have hinner : (∫⁻ x, ENNReal.ofReal (∫ y, g y ∂K x) ∂ν) = ∫⁻ x, ENNReal.ofReal (g x) ∂ν := by
    have hcongr : (∫⁻ x, ENNReal.ofReal (∫ y, g y ∂K x) ∂ν) =
        ∫⁻ x, (∫⁻ y, ENNReal.ofReal (g y) ∂K x) ∂ν :=
      lintegral_congr fun x => kernel_integral_eq_toReal hg hg0 hC x
    rw [hcongr]
    exact lintegral_kernel_of_invariant hν (ENNReal.measurable_ofReal.comp hg)
  rw [hstep, hinner]
  exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0)
    hg.aestronglyMeasurable).symm

/-! ### The uniqueness argument -/

theorem integral_sub_sq (P : Measure α) [IsFiniteMeasure P] {u v : α → ℝ}
    (hu2 : Integrable (fun x => u x^2) P) (hv2 : Integrable (fun x => v x^2) P)
    (huv : Integrable (fun x => u x * v x) P) :
    (∫ x, (u x - v x)^2 ∂P) =
      (∫ x, u x^2 ∂P) - 2*(∫ x, u x * v x ∂P) + ∫ x, v x^2 ∂P := by
  have h2 : Integrable (fun x => 2*(u x * v x)) P := huv.const_mul 2
  have hsub : Integrable (fun x => u x^2 - 2*(u x * v x)) P := hu2.sub h2
  have hcongr : (∫ x, (u x - v x)^2 ∂P) =
      ∫ x, ((u x^2 - 2*(u x * v x)) + v x^2) ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
  rw [hcongr, integral_add hsub hv2, integral_sub hu2 h2, integral_const_mul]

/-- At most one invariant probability: the paper's argument that the density of
one invariant law against their sum is harmonic, hence constant on each
transition and therefore on the dominated measure. -/
theorem invariant_eq_half [IsMarkovKernel K] {lam : Measure α} (hlam : lam ≠ 0)
    (hac : ∀ x, lam ≪ K x)
    {ν₁ ν₂ : Measure α} [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h₁ : Kernel.Invariant K ν₁) (h₂ : Kernel.Invariant K ν₂)
    {A : Set α} (hA : MeasurableSet A) :
    ν₁ A = ENNReal.ofReal (1/2) * (ν₁ + ν₂) A := by
  set ν : Measure α := ν₁ + ν₂ with hνdef
  have hνfin : IsFiniteMeasure ν := by
    rw [hνdef]
    infer_instance
  have hνuniv : ν univ = 2 := by
    rw [hνdef, Measure.add_apply, measure_univ, measure_univ, one_add_one_eq_two]
  have hν : Kernel.Invariant K ν := by
    have : ν.bind ⇑K = ν := by
      ext B hB
      rw [hνdef, Measure.bind_apply hB (Kernel.aemeasurable K), lintegral_add_measure,
        Measure.add_apply, ← Measure.bind_apply hB (Kernel.aemeasurable K),
        ← Measure.bind_apply hB (Kernel.aemeasurable K), h₁.def, h₂.def]
    exact this
  have hle : ν₁ ≤ ν := by
    rw [hνdef]
    exact Measure.le_add_right le_rfl
  have hacν : ν₁ ≪ ν := Measure.absolutelyContinuous_of_le hle
  set f : α → ℝ≥0∞ := ν₁.rnDeriv ν with hfdef
  have hfmeas : Measurable f := Measure.measurable_rnDeriv _ _
  have hf1 : f ≤ᵐ[ν] 1 := Measure.rnDeriv_le_one_of_le hle
  have hflt : ∀ᵐ x ∂ν, f x < ⊤ := Measure.rnDeriv_lt_top _ _
  have hwd : ν.withDensity f = ν₁ := Measure.withDensity_rnDeriv_eq _ _ hacν
  set G : α → ℝ := fun x => min (f x).toReal 1 with hGdef
  have hGmeas : Measurable G := (hfmeas.ennreal_toReal).min measurable_const
  have hG0 : ∀ x, 0 ≤ G x := by
    intro x
    exact le_min ENNReal.toReal_nonneg zero_le_one
  have hG1 : ∀ x, G x ≤ 1 := fun x => min_le_right _ _
  have hGsq1 : ∀ x, G x ^ 2 ≤ 1 := by
    intro x
    nlinarith [hG0 x, hG1 x]
  have hGsq0 : ∀ x, 0 ≤ G x ^ 2 := fun x => sq_nonneg _
  have hGf : ∀ᵐ x ∂ν, ENNReal.ofReal (G x) = f x := by
    filter_upwards [hf1, hflt] with x hx1 hxlt
    have hle1 : (f x).toReal ≤ 1 := by
      have := ENNReal.toReal_mono (by norm_num) hx1
      simpa using this
    rw [hGdef]
    simp only [min_eq_left hle1]
    exact ENNReal.ofReal_toReal hxlt.ne
  have hdm : Measurable (fun x => ENNReal.ofReal (G x)) := ENNReal.measurable_ofReal.comp hGmeas
  have hν₁G : ν.withDensity (fun x => ENNReal.ofReal (G x)) = ν₁ := by
    rw [withDensity_congr_ae hGf]
    exact hwd
  -- change of measure for bounded rewards
  have hchange : ∀ h : α → ℝ, Measurable h → (∀ x, 0 ≤ h x) → (∀ x, h x ≤ 1) →
      (∫ x, h x ∂ν₁) = ∫ x, G x * h x ∂ν := by
    intro h hhm hh0 hh1
    rw [← hν₁G, integral_withDensity_eq_integral_toReal_smul hdm
      (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (ENNReal.ofReal (G x)).toReal • h x = G x * h x
    rw [ENNReal.toReal_ofReal (hG0 x), smul_eq_mul]
  -- the two kernel rewards
  set Q : α → ℝ := fun x => ∫ y, G y ∂K x with hQdef
  set Q2 : α → ℝ := fun x => ∫ y, G y ^ 2 ∂K x with hQ2def
  have hPK : ∀ x, IsProbabilityMeasure (K x) := fun x => IsMarkovKernel.isProbabilityMeasure x
  have hGint : ∀ x, Integrable G (K x) := by
    intro x
    have := hPK x
    exact Doeblin.integrable_bounded_reward (K x) hGmeas hG0 hG1
  have hGsqint : ∀ x, Integrable (fun y => G y ^ 2) (K x) := by
    intro x
    have := hPK x
    exact Doeblin.integrable_bounded_reward (K x) (hGmeas.pow_const 2) hGsq0 hGsq1
  have hQ0 : ∀ x, 0 ≤ Q x := fun x => integral_nonneg hG0
  have hQ1 : ∀ x, Q x ≤ 1 := by
    intro x
    have := hPK x
    calc Q x ≤ ∫ _y, (1 : ℝ) ∂K x := integral_mono (hGint x) (integrable_const 1) hG1
      _ = 1 := by simp
  have hQ20 : ∀ x, 0 ≤ Q2 x := fun x => integral_nonneg hGsq0
  have hQ21 : ∀ x, Q2 x ≤ 1 := by
    intro x
    have := hPK x
    calc Q2 x ≤ ∫ _y, (1 : ℝ) ∂K x := integral_mono (hGsqint x) (integrable_const 1) hGsq1
      _ = 1 := by simp
  have hQmeas : Measurable Q := by
    have hsm : StronglyMeasurable (fun p : α × α => G p.2) :=
      (hGmeas.comp measurable_snd).stronglyMeasurable
    exact (hsm.integral_kernel_prod_right' (κ := K)).measurable
  have hQ2meas : Measurable Q2 := by
    have hsm : StronglyMeasurable (fun p : α × α => G p.2 ^ 2) :=
      ((hGmeas.comp measurable_snd).pow_const 2).stronglyMeasurable
    exact (hsm.integral_kernel_prod_right' (κ := K)).measurable
  have hjensen : ∀ x, (Q x)^2 ≤ Q2 x := by
    intro x
    have := hPK x
    exact sq_integral_le_integral_sq (K x) (hGint x) (hGsqint x)
  -- integrability against the finite measures
  have hνG : Integrable G ν := Doeblin.integrable_bounded_reward ν hGmeas hG0 hG1
  have hνGsq : Integrable (fun x => G x ^ 2) ν :=
    Doeblin.integrable_bounded_reward ν (hGmeas.pow_const 2) hGsq0 hGsq1
  have hνQ : Integrable Q ν := Doeblin.integrable_bounded_reward ν hQmeas hQ0 hQ1
  have hνQsq : Integrable (fun x => Q x ^ 2) ν :=
    Doeblin.integrable_bounded_reward (H := 1) ν (hQmeas.pow_const 2)
      (fun x => sq_nonneg _) (fun x => by nlinarith [hQ0 x, hQ1 x])
  have hνQ2 : Integrable Q2 ν := Doeblin.integrable_bounded_reward ν hQ2meas hQ20 hQ21
  have hνQG : Integrable (fun x => Q x * G x) ν :=
    Doeblin.integrable_bounded_reward (H := 1) ν (hQmeas.mul hGmeas)
      (fun x => mul_nonneg (hQ0 x) (hG0 x))
      (fun x => by nlinarith [hQ0 x, hQ1 x, hG0 x, hG1 x])
  -- the four identities
  have hA1 : (∫ x, Q2 x ∂ν) = ∫ x, G x ^ 2 ∂ν :=
    integral_kernel_of_invariant hν (hGmeas.pow_const 2) hGsq0 hGsq1
  have hA2 : (∫ x, Q x * G x ∂ν) = ∫ x, Q x ∂ν₁ := by
    rw [hchange Q hQmeas hQ0 hQ1]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm _ _))
  have hA3 : (∫ x, Q x ∂ν₁) = ∫ x, G x ∂ν₁ :=
    integral_kernel_of_invariant h₁ hGmeas hG0 hG1
  have hA4 : (∫ x, G x ∂ν₁) = ∫ x, G x ^ 2 ∂ν := by
    rw [hchange G hGmeas hG0 hG1]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (sq (G x)).symm))
  have hA5 : (∫ x, Q x ^ 2 ∂ν) ≤ ∫ x, G x ^ 2 ∂ν := by
    rw [← hA1]
    exact integral_mono hνQsq hνQ2 hjensen
  -- harmonicity
  have hzero : (∫ x, (Q x - G x)^2 ∂ν) = 0 := by
    have hexp := integral_sub_sq ν hνQsq hνGsq hνQG
    have hQG : (∫ x, Q x * G x ∂ν) = ∫ x, G x ^ 2 ∂ν := by
      rw [hA2, hA3, hA4]
    rw [hQG] at hexp
    have hnn : 0 ≤ ∫ x, (Q x - G x)^2 ∂ν := integral_nonneg (fun x => sq_nonneg _)
    linarith
  have hQeq : ∀ᵐ x ∂ν, Q x = G x := by
    have hint : Integrable (fun x => (Q x - G x)^2) ν :=
      Doeblin.integrable_bounded_reward (H := 1) ν ((hQmeas.sub hGmeas).pow_const 2)
        (fun x => sq_nonneg _)
        (fun x => by nlinarith [hQ0 x, hQ1 x, hG0 x, hG1 x])
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (Q x - G x)) hint).mp hzero
    filter_upwards [hae] with x hx
    have hx0 : (Q x - G x)^2 = 0 := hx
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx0
    linarith
  -- the conditional variance vanishes
  have hQsqeq : (∫ x, Q x ^ 2 ∂ν) = ∫ x, G x ^ 2 ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hQeq] with x hx
    rw [hx]
  have hvarzero : (∫ x, (Q2 x - Q x ^ 2) ∂ν) = 0 := by
    rw [integral_sub hνQ2 hνQsq, hA1, hQsqeq]
    ring
  have hvarae : ∀ᵐ x ∂ν, Q2 x = Q x ^ 2 := by
    have hint : Integrable (fun x => Q2 x - Q x ^ 2) ν := hνQ2.sub hνQsq
    have hnn : ∀ x, 0 ≤ Q2 x - Q x ^ 2 := fun x => by linarith [hjensen x]
    have hae := (integral_eq_zero_iff_of_nonneg hnn hint).mp hvarzero
    filter_upwards [hae] with x hx
    have : Q2 x - Q x ^ 2 = 0 := hx
    linarith
  -- each transition sees a constant
  have hconst : ∀ᵐ x ∂ν, ∀ᵐ y ∂lam, G y = G x := by
    filter_upwards [hvarae, hQeq] with x hvar hQx
    have := hPK x
    have hvar' : (∫ y, G y ^ 2 ∂K x) = (∫ y, G y ∂K x)^2 := hvar
    have hmean : ∀ᵐ y ∂K x, G y = ∫ z, G z ∂K x :=
      ae_eq_mean_of_sq_integral_eq (K x) (hGint x) (hGsqint x) hvar'
    have hK : ∀ᵐ y ∂K x, G y = G x := by
      filter_upwards [hmean] with y hy
      rw [hy]
      exact hQx
    exact hac x hK
  -- so `G` is almost everywhere constant
  have hνne : ν ≠ 0 := by
    intro hc
    rw [hc] at hνuniv
    simp at hνuniv
  have hνbot : (ae ν).NeBot := ae_neBot.mpr hνne
  have hlambot : (ae lam).NeBot := ae_neBot.mpr hlam
  obtain ⟨x₀, hx₀⟩ := hconst.exists
  have hGconst : ∀ᵐ x ∂ν, G x = G x₀ := by
    filter_upwards [hconst] with x hx
    have hcomb : ∀ᵐ y ∂lam, G x = G x₀ := by
      filter_upwards [hx, hx₀] with y hy hy₀
      rw [← hy, hy₀]
    exact hcomb.exists.choose_spec
  -- evaluate the constant
  have hmass : (∫ x, G x ∂ν) = 1 := by
    have h1 : (∫ _x, (1 : ℝ) ∂ν₁) = ∫ x, G x * 1 ∂ν :=
      hchange (fun _ => 1) measurable_const (fun _ => zero_le_one) (fun _ => le_rfl)
    have h2 : (∫ _x, (1 : ℝ) ∂ν₁) = 1 := by simp
    have h3 : (∫ x, G x * 1 ∂ν) = ∫ x, G x ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_one (G x)))
    rw [h2, h3] at h1
    exact h1.symm
  have hhalf : G x₀ = 1/2 := by
    have hc : (∫ x, G x ∂ν) = ∫ _x, G x₀ ∂ν := integral_congr_ae hGconst
    rw [hmass, integral_const] at hc
    have hrv : (ν.real univ) = 2 := by
      have hdef : ν.real univ = (ν univ).toReal := rfl
      rw [hdef, hνuniv]
      simp
    rw [hrv, smul_eq_mul] at hc
    linarith
  -- rewrite the invariant law
  rw [← hν₁G, withDensity_apply _ hA]
  have hdens : ∀ᵐ x ∂(ν.restrict A), ENNReal.ofReal (G x) = ENNReal.ofReal (1/2) := by
    filter_upwards [ae_restrict_of_ae hGconst] with x hx
    rw [hx, hhalf]
  rw [lintegral_congr_ae hdens, lintegral_const, Measure.restrict_apply_univ]

/-- Uniqueness of the invariant probability. -/
theorem invariant_subsingleton [IsMarkovKernel K] {lam : Measure α} (hlam : lam ≠ 0)
    (hac : ∀ x, lam ≪ K x)
    {ν₁ ν₂ : Measure α} [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h₁ : Kernel.Invariant K ν₁) (h₂ : Kernel.Invariant K ν₂) : ν₁ = ν₂ := by
  ext A hA
  have e₁ := invariant_eq_half hlam hac h₁ h₂ hA
  have e₂ := invariant_eq_half hlam hac h₂ h₁ hA
  rw [add_comm ν₂ ν₁] at e₂
  rw [e₁, e₂]

end KernelUnique
end SwingRepair
