import PLAStochastic.Index.CEPS.Final.KernelPipelineGk
import PLAStochastic.Index.CEPS.Final.KernelPipelineCs
import PLAStochastic.Index.CEPS.Final.Main
import PLAStochastic.Index.CEPS.Jets.Continuity

/-! # The kernel-jet representation from the kernel packages

`cepsKernelJetRepresentation_of_packages`: the outer strip budgets and the central exact-root
kernel (`CepsKernelPackages`) give `CepsKernelJetRepresentation` with the concrete coefficients
`cepsKernelCs`, `cepsKernelGk`: Mean and Low are `Final.KernelMean`/`Final.KernelLow`, the box
representations come from the analytic pipeline, and coefficient regularity on small input
classes from the pipeline regularity together with the continuity of the jets (`Jets.Continuity`).
-/

noncomputable section
open Complex Metric Set Filter Topology MeasureTheory Finset
namespace PGM

theorem cepsKernelGk_regular (h : CepsKernelPackages) (j : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ p : ℕ → ℝ, (∀ i : Fin (cepsJetDim (4 * (j + 1))), |p i - cepsJetLaw cepsLambda i| ≤ ρ) →
        ∀ n : ℕ, ContDiff ℝ n (cepsKernelGk j p)) ∧
      ∀ m : ℕ, ∃ K c : ℝ, 0 < c ∧ ∃ e : ℕ, ∀ p : ℕ → ℝ,
        (∀ i : Fin (cepsJetDim (4 * (j + 1))), |p i - cepsJetLaw cepsLambda i| ≤ ρ) →
        ∀ y : ℝ, ‖iteratedDeriv m (cepsKernelGk j p) y‖ ≤ K * cepsStretchedWeight c e y := by
  obtain ⟨R, δ, K, c, e, g, E, H, hP, ρ₀, hρ₀, hΦ⟩ := cepsKernelGk_pipeline h j
  exact hP.phiRegular_of_eq hρ₀ hΦ

theorem cepsKernel_coeffReg (h : CepsKernelPackages) :
    CepsNormalCoeffReg cepsKernelJetBase cepsKernelGk := by
  intro N'
  choose ρ hρ hsm hbd using cepsKernelGk_regular h
  choose K c hc e hK using hbd
  have hne : (Finset.range (N' + 1)).Nonempty := ⟨0, by simp⟩
  set ρm := (Finset.range (N' + 1)).inf' hne ρ with hρm
  have hρm0 : 0 < ρm := (Finset.lt_inf'_iff hne).mpr fun j _ => hρ j
  obtain ⟨mJ, HJ⟩ := cepsJetLaw_mem_reference_box (cepsJetDim (4 * (N' + 1))) hρm0
  refine ⟨mJ, fun D θ vlo vhi η hD hθ hvlo hv hη => ?_⟩
  obtain ⟨r, hr, Hr⟩ := HJ D θ vlo vhi η hD hθ hvlo hv hη
  set B := ∑ j ∈ Finset.range (N' + 1), ∑ i ∈ Finset.range (N' + 2), |K j i|
  set d' := ∑ j ∈ Finset.range (N' + 1), ∑ i ∈ Finset.range (N' + 2), e j i
  refine ⟨r, hr, B, d', fun ν hν j hj => ?_⟩
  have hjr : j ∈ Finset.range (N' + 1) := Finset.mem_range.mpr (by omega)
  have hbox : ∀ i : Fin (cepsJetDim (4 * (j + 1))),
      |cepsJetLaw ν i - cepsJetLaw cepsLambda i| ≤ ρ j := by
    intro i
    have hle : cepsJetDim (4 * (j + 1)) ≤ cepsJetDim (4 * (N' + 1)) :=
      cepsJetDim_monotone (by omega)
    have := Hr ν hν ⟨i, lt_of_lt_of_le i.2 hle⟩
    exact this.trans (Finset.inf'_le _ hjr)
  refine ⟨by exact_mod_cast hsm j _ hbox (N' + 1), fun i hi y => ?_⟩
  have hir : i ∈ Finset.range (N' + 2) := Finset.mem_range.mpr (by omega)
  have h1 := hK j i (cepsJetLaw ν) hbox y
  have hy : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hw : cepsStretchedWeight (c j i) (e j i) y ≤ (1 + |y|) ^ (e j i) := by
    unfold cepsStretchedWeight
    have : Real.exp (-c j i * Real.sqrt |y|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hc j i, Real.sqrt_nonneg |y|])
    nlinarith [pow_pos (lt_of_lt_of_le one_pos hy) (e j i)]
  have hKB : |K j i| ≤ B :=
    (Finset.single_le_sum (f := fun i => |K j i|) (fun _ _ => abs_nonneg _) hir).trans
      (Finset.single_le_sum (f := fun j => ∑ i ∈ Finset.range (N' + 2), |K j i|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hjr)
  have hed : e j i ≤ d' :=
    (Finset.single_le_sum (f := fun i => e j i) (fun _ _ => Nat.zero_le _) hir).trans
      (Finset.single_le_sum (f := fun j => ∑ i ∈ Finset.range (N' + 2), e j i)
        (fun _ _ => Nat.zero_le _) hjr)
  calc ‖iteratedDeriv i (cepsKernelGk j (cepsKernelJetBase.jet ν)) y‖
      ≤ K j i * cepsStretchedWeight (c j i) (e j i) y := h1
    _ ≤ |K j i| * (1 + |y|) ^ (e j i) :=
        mul_le_mul (le_abs_self _) hw (cepsStretchedWeight_nonneg _ _ _) (abs_nonneg _)
    _ ≤ B * (1 + |y|) ^ d' :=
        mul_le_mul hKB (pow_le_pow_right₀ hy hed) (by positivity) ((abs_nonneg _).trans hKB)

/-- **The kernel-jet representation from the kernel packages.** -/
theorem cepsKernelJetRepresentation_of_packages (h : CepsKernelPackages) :
    CepsKernelJetRepresentation := by
  refine ⟨cepsKernelCs, cepsKernelGk, cepsKernel_normal_mean, cepsKernel_normal_low,
    cepsKernel_coeffReg h, cepsKernelCs_rep h, fun j => ?_⟩
  obtain ⟨R, δ, K, c, e, g, E, H, hP, ρ₀, hρ₀, hΦ⟩ := cepsKernelGk_pipeline h j
  exact ⟨_, hP.jetRepresentation_of_eq hρ₀ hΦ⟩

/-- The all-order expansion of `gepC ε / ε²` from the kernel packages. -/
theorem gepC_asymptoticExpansion_of_packages (h : CepsKernelPackages) :
    ∃! a : ℕ → ℝ, (∀ M : ℕ, ∃ K eps0 : ℝ, ∀ eps : ℝ, eps0 ≤ eps →
      |gepC eps / eps ^ 2 - ∑ j ∈ Finset.range (M + 1), a j * eps ^ (-(j : ℤ))| ≤
        K * eps ^ (-((M : ℤ) + 1))) ∧
      a 0 = BrownianAffine.optimalMeanConstant / BrownianAffine.optimalDispersionConstant :=
  gepC_asymptoticExpansion_of_kernelJets (cepsKernelJetRepresentation_of_packages h)

end PGM
