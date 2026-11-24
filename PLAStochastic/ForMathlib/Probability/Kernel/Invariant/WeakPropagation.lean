import PLAStochastic.ForMathlib.Probability.Kernel.Invariant.WeakLimit
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Propagating a weak limit through a convergent kernel family

`eq:transient-subsequentiallaws`, one step: if the laws `ρ_i` converge weakly
to `ρ`, the bounded Lipschitz test integrals of the kernels `K_i` converge to
those of `K` uniformly on bounded sets, and `K` is weakly Feller, then
`ρ_i K_i ⇒ ρ K`.  "Test against a bounded Lipschitz function, restrict the
input to a compact set, and use uniform convergence there; continuity of `Kf`
handles the limiting input."  Iterating the one-step statement propagates the
weak limit through any fixed number of transitions.

The filter is assumed countably generated, which lets Mathlib's Lipschitz
characterisation of weak convergence be used on the output side; every filter
in the applications (`atTop` on the budget, intersected with principal filters
and with the pull-back of a neighbourhood filter in the metrizable space of
probability measures) is countably generated.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
namespace KernelLimit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! ### Integrals against a composed measure -/

/-- `∫ f d(κ ∘ₘ m) = ∫ (∫ f dκ(x)) dm(x)` for integrable `f`. -/
theorem integral_comp_eq {κ : Kernel ℝ ℝ} [IsSFiniteKernel κ] {m : Measure ℝ} [SFinite m]
    {f : ℝ → ℝ} (hf : Integrable f (κ ∘ₘ m)) :
    ∫ y, f y ∂(κ ∘ₘ m) = ∫ x, ∫ y, f y ∂(κ x) ∂m := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  rw [Kernel.integral_comp hf]
  simp only [Kernel.const_apply]

theorem integrable_of_abs_le {ρ : Measure ℝ} [IsFiniteMeasure ρ] {f : ℝ → ℝ} {B : ℝ}
    (hf : Measurable f) (hfB : ∀ x, |f x| ≤ B) : Integrable f ρ := by
  refine (integrable_const B).mono' hf.aestronglyMeasurable (ae_of_all _ (fun x => ?_))
  simpa only [Real.norm_eq_abs] using hfB x

/-- The kernel integral of a bounded function is bounded by the same constant. -/
theorem abs_kernel_integral_le {K : Kernel ℝ ℝ} [IsMarkovKernel K] {f : ℝ → ℝ} {B : ℝ}
    (hf : Measurable f) (hfB : ∀ x, |f x| ≤ B) (r : ℝ) :
    |∫ y, f y ∂(K r)| ≤ B := by
  have hint : Integrable f (K r) := integrable_of_abs_le hf hfB
  calc |∫ y, f y ∂(K r)| ≤ ∫ y, |f y| ∂(K r) := abs_integral_le_integral_abs
    _ ≤ ∫ _y, B ∂(K r) := integral_mono hint.abs (integrable_const B) hfB
    _ = B := by simp

/-- `abs_integral_sub_le_of_unif` with an arbitrary sup bound `B` in place of `1`. -/
theorem abs_integral_sub_le_of_unif_bdd {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {u v : ℝ → ℝ} (hu : Measurable u) (hv : Measurable v) {B : ℝ}
    (huB : ∀ r, |u r| ≤ B) (hvB : ∀ r, |v r| ≤ B)
    {C δ : ℝ} (hδ : 0 ≤ δ) (hclose : ∀ r : ℝ, |r| ≤ C → |u r - v r| ≤ δ) :
    |(∫ r, u r ∂ρ) - ∫ r, v r ∂ρ| ≤ δ + 2 * B * ρ.real {x : ℝ | C < |x|} := by
  set S : Set ℝ := {x : ℝ | C < |x|} with hS
  have hSmeas : MeasurableSet S := measurableSet_abs_gt C
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (huB 0)
  have huint : Integrable u ρ := integrable_of_abs_le hu huB
  have hvint : Integrable v ρ := integrable_of_abs_le hv hvB
  have hdint : Integrable (fun r => |u r - v r|) ρ := (huint.sub hvint).abs
  have hindint : Integrable (S.indicator (fun _ => (1 : ℝ))) ρ :=
    (integrable_const (1 : ℝ)).indicator hSmeas
  have hbint : Integrable (fun r => δ + 2 * B * S.indicator (fun _ => (1 : ℝ)) r) ρ :=
    (integrable_const δ).add (hindint.const_mul (2 * B))
  have hpt : ∀ r : ℝ, |u r - v r| ≤ δ + 2 * B * S.indicator (fun _ => (1 : ℝ)) r := by
    intro r
    by_cases hr : |r| ≤ C
    · have hmem : r ∉ S := by
        simp only [hS, Set.mem_ofPred_eq, not_lt]
        exact hr
      rw [Set.indicator_of_notMem hmem]
      simpa using hclose r hr
    · have hmem : r ∈ S := by
        simp only [hS, Set.mem_ofPred_eq]
        exact lt_of_not_ge hr
      rw [Set.indicator_of_mem hmem]
      have h2 : |u r - v r| ≤ 2 * B := by
        calc |u r - v r| ≤ |u r| + |v r| := abs_sub _ _
          _ ≤ 2 * B := by linarith [huB r, hvB r]
      linarith
  have hindval : (∫ r, S.indicator (fun _ => (1 : ℝ)) r ∂ρ) = ρ.real S :=
    integral_indicator_one hSmeas
  have hval : (∫ r, (δ + 2 * B * S.indicator (fun _ => (1 : ℝ)) r) ∂ρ) =
      δ + 2 * B * ρ.real S := by
    rw [integral_add (integrable_const δ) (hindint.const_mul (2 * B)), integral_const,
      integral_const_mul, hindval]
    simp
  calc |(∫ r, u r ∂ρ) - ∫ r, v r ∂ρ| = |∫ r, (u r - v r) ∂ρ| := by
        rw [integral_sub huint hvint]
    _ ≤ ∫ r, |u r - v r| ∂ρ := abs_integral_le_integral_abs
    _ ≤ ∫ r, (δ + 2 * B * S.indicator (fun _ => (1 : ℝ)) r) ∂ρ :=
        integral_mono hdint hbint hpt
    _ = δ + 2 * B * ρ.real S := hval

/-! ### The one-step propagation -/

/-- The composed law as a probability measure. -/
def compProb (K : Kernel ℝ ℝ) [IsMarkovKernel K] (ρ : ProbabilityMeasure ℝ) :
    ProbabilityMeasure ℝ :=
  ⟨K ∘ₘ (ρ : Measure ℝ), inferInstance⟩

@[simp] theorem compProb_coe (K : Kernel ℝ ℝ) [IsMarkovKernel K] (ρ : ProbabilityMeasure ℝ) :
    (compProb K ρ : Measure ℝ) = K ∘ₘ (ρ : Measure ℝ) := rfl

/-- The integral of a bounded Lipschitz test function against a composed law,
written as the law-average of the kernel integrals. -/
theorem integral_compProb {K : Kernel ℝ ℝ} [IsMarkovKernel K] (ρ : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {L B : ℝ} (hf : IsBddLip f L B) :
    (∫ y, f y ∂(compProb K ρ : Measure ℝ)) = ∫ r, (∫ y, f y ∂(K r)) ∂(ρ : Measure ℝ) := by
  rw [compProb_coe]
  exact integral_comp_eq (integrable_of_abs_le hf.meas hf.bdd)

/-- **One step of `eq:transient-subsequentiallaws`.**  `ρ_i ⇒ ρ`, compact-uniform
convergence `K_i → K` on bounded Lipschitz test functions, and the weak Feller
property of `K` give `ρ_i K_i ⇒ ρ K`. -/
theorem tendsto_compProb {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {K : Kernel ℝ ℝ} [IsMarkovKernel K] {Ks : ι → Kernel ℝ ℝ} [∀ i, IsMarkovKernel (Ks i)]
    {ρs : ι → ProbabilityMeasure ℝ} {ρ : ProbabilityMeasure ℝ} (hρ : Tendsto ρs l (𝓝 ρ))
    (hcont : ∀ (f : ℝ → ℝ) (L B : ℝ), IsBddLip f L B →
      Continuous (fun r => ∫ y, f y ∂(K r)))
    (hunif : ∀ (f : ℝ → ℝ) (L B : ℝ), IsBddLip f L B → ∀ (C ε : ℝ), 0 < ε →
      ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
        |(∫ y, f y ∂(Ks i r)) - (∫ y, f y ∂(K r))| ≤ ε) :
    Tendsto (fun i => compProb (Ks i) (ρs i)) l (𝓝 (compProb K ρ)) := by
  rw [MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto]
  intro f hfbdd hflip
  obtain ⟨D, hD⟩ := hfbdd
  obtain ⟨Lnn, hL⟩ := hflip
  -- the test function as a bounded Lipschitz function with explicit constants
  have hf : IsBddLip f (Lnn : ℝ) (|f 0| + D) := by
    refine ⟨hL.continuous.measurable, fun x y => ?_, fun x => ?_⟩
    · have := hL.dist_le_mul x y
      rwa [Real.dist_eq, Real.dist_eq] at this
    · have := hD x 0
      rw [Real.dist_eq] at this
      calc |f x| = |(f x - f 0) + f 0| := by ring_nf
        _ ≤ |f x - f 0| + |f 0| := abs_add_le _ _
        _ ≤ |f 0| + D := by linarith
  set B : ℝ := |f 0| + D with hBdef
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hf.bdd 0)
  set Ψ : ℝ → ℝ := fun r => ∫ y, f y ∂(K r) with hΨdef
  have hΨmeas : Measurable Ψ := measurable_kernel_integral hf.meas
  have hΨabs : ∀ r, |Ψ r| ≤ B := fun r => abs_kernel_integral_le hf.meas hf.bdd r
  have hΨcont : Continuous Ψ := hcont f _ _ hf
  have hΦmeas : ∀ i, Measurable (fun r => ∫ y, f y ∂(Ks i r)) := fun i =>
    measurable_kernel_integral hf.meas
  have hΦabs : ∀ i r, |∫ y, f y ∂(Ks i r)| ≤ B := fun i r =>
    abs_kernel_integral_le hf.meas hf.bdd r
  -- rewrite both sides through the kernel integrals
  simp_rw [integral_compProb _ hf]
  -- the weak convergence applied to continuous bounded functions
  have hweak : ∀ (g : ℝ → ℝ) (C : ℝ), Continuous g → (∀ x, |g x| ≤ C) →
      Tendsto (fun i => ∫ x, g x ∂(ρs i : Measure ℝ)) l (𝓝 (∫ x, g x ∂(ρ : Measure ℝ))) :=
    fun g C hg hgC => tendsto_integral_of_tendsto hρ g C hg hgC
  have hlim2 : Tendsto (fun i => ∫ r, Ψ r ∂(ρs i : Measure ℝ)) l
      (𝓝 (∫ r, Ψ r ∂(ρ : Measure ℝ))) := hweak Ψ B hΨcont hΨabs
  have herr : Tendsto (fun i => (∫ r, (∫ y, f y ∂(Ks i r)) ∂(ρs i : Measure ℝ))
      - ∫ r, Ψ r ∂(ρs i : Measure ℝ)) l (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨C, hC⟩ := exists_eventually_measureReal_abs_gt_le (νs := fun i => (ρs i : Measure ℝ))
      (fun i => inferInstance) hweak (show (0 : ℝ) < ε/(8*(B+1)) by positivity)
    filter_upwards [hC, hunif f _ _ hf C (ε/2) (by linarith)] with i hCi hui
    rw [Real.norm_eq_abs]
    have hmass : 2 * B * (ρs i : Measure ℝ).real {x : ℝ | C < |x|} ≤ ε/4 := by
      have h1 : 2 * B * (ρs i : Measure ℝ).real {x : ℝ | C < |x|} ≤ 2 * B * (ε/(8*(B+1))) :=
        mul_le_mul_of_nonneg_left hCi (by positivity)
      have h2 : 2 * B * (ε/(8*(B+1))) ≤ ε/4 := by
        rw [show 2 * B * (ε/(8*(B+1))) = (ε/4) * (B/(B+1)) by field_simp; ring]
        have : B/(B+1) ≤ 1 := by
          rw [div_le_one (by linarith)]
          linarith
        nlinarith
      linarith
    calc |(∫ r, (∫ y, f y ∂(Ks i r)) ∂(ρs i : Measure ℝ)) - ∫ r, Ψ r ∂(ρs i : Measure ℝ)|
          ≤ ε/2 + 2 * B * (ρs i : Measure ℝ).real {x : ℝ | C < |x|} :=
          abs_integral_sub_le_of_unif_bdd (hΦmeas i) hΨmeas (hΦabs i) hΨabs
            (by linarith : (0 : ℝ) ≤ ε/2) hui
      _ ≤ ε/2 + ε/4 := by linarith
      _ < ε := by linarith
  have hsum := hlim2.add herr
  rw [add_zero] at hsum
  exact Tendsto.congr (fun i => by ring) hsum

/-! ### Iterating the one-step propagation -/

/-- `m` transitions of a kernel, on probability measures. -/
def compProbIter (K : Kernel ℝ ℝ) [IsMarkovKernel K] (m : ℕ) (ρ : ProbabilityMeasure ℝ) :
    ProbabilityMeasure ℝ :=
  (compProb K)^[m] ρ

@[simp] theorem compProbIter_zero (K : Kernel ℝ ℝ) [IsMarkovKernel K] (ρ : ProbabilityMeasure ℝ) :
    compProbIter K 0 ρ = ρ := rfl

theorem compProbIter_succ (K : Kernel ℝ ℝ) [IsMarkovKernel K] (m : ℕ) (ρ : ProbabilityMeasure ℝ) :
    compProbIter K (m+1) ρ = compProb K (compProbIter K m ρ) := by
  unfold compProbIter
  rw [Function.iterate_succ_apply']

theorem compProbIter_coe (K : Kernel ℝ ℝ) [IsMarkovKernel K] (m : ℕ) (ρ : ProbabilityMeasure ℝ) :
    (compProbIter K m ρ : Measure ℝ) = (fun ν : Measure ℝ => K ∘ₘ ν)^[m] (ρ : Measure ℝ) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [compProbIter_succ, compProb_coe, ih, Function.iterate_succ_apply']

/-- **`eq:transient-subsequentiallaws`.**  The weak limit propagates through any
fixed number of transitions: `ρ_i K_i^m ⇒ ρ K^m`. -/
theorem tendsto_compProbIter {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {K : Kernel ℝ ℝ} [IsMarkovKernel K] {Ks : ι → Kernel ℝ ℝ} [∀ i, IsMarkovKernel (Ks i)]
    {ρs : ι → ProbabilityMeasure ℝ} {ρ : ProbabilityMeasure ℝ} (hρ : Tendsto ρs l (𝓝 ρ))
    (hcont : ∀ (f : ℝ → ℝ) (L B : ℝ), IsBddLip f L B →
      Continuous (fun r => ∫ y, f y ∂(K r)))
    (hunif : ∀ (f : ℝ → ℝ) (L B : ℝ), IsBddLip f L B → ∀ (C ε : ℝ), 0 < ε →
      ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
        |(∫ y, f y ∂(Ks i r)) - (∫ y, f y ∂(K r))| ≤ ε) (m : ℕ) :
    Tendsto (fun i => compProbIter (Ks i) m (ρs i)) l (𝓝 (compProbIter K m ρ)) := by
  induction m with
  | zero => simpa using hρ
  | succ m ih =>
    simp_rw [compProbIter_succ]
    exact tendsto_compProb ih hcont hunif

end KernelLimit
end SwingRepair
