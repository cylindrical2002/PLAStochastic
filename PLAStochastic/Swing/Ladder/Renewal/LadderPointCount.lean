import PLAStochastic.Swing.Ladder.Law.EpochRegeneration
import PLAStochastic.Swing.Ladder.Renewal.RenewalMeasure

/-! # The renewal measure counts the actual ladder points

The successive ladder heights of the positive-drift Gaussian walk are iid with
the parameterised ladder law.  Hence the law of the `n`-th ladder level is the
`n`-fold convolution power, and the renewal measure of `LadderRenewalMeasure`
is exactly the expected number of ladder levels in a set.  This is the missing
link between the abstract renewal measure and the actual walk.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- An independent sum has the convolution of the two laws. -/
theorem map_add_of_indepFun [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (h : IndepFun f g μ) :
    μ.map (fun ω => f ω + g ω) = (μ.map f) ∗ (μ.map g) := by
  have hprod : μ.map (fun ω => (f ω, g ω)) = (μ.map f).prod (μ.map g) :=
    (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).mp h
  have hpair : Measurable (fun ω => (f ω, g ω)) := hf.prodMk hg
  calc μ.map (fun ω => f ω + g ω)
      = μ.map ((fun p : ℝ × ℝ => p.1 + p.2) ∘ (fun ω => (f ω, g ω))) := rfl
    _ = (μ.map (fun ω => (f ω, g ω))).map (fun p : ℝ × ℝ => p.1 + p.2) :=
        (Measure.map_map measurable_add hpair).symm
    _ = ((μ.map f).prod (μ.map g)).map (fun p : ℝ × ℝ => p.1 + p.2) := by rw [hprod]
    _ = (μ.map f) ∗ (μ.map g) := rfl

/-- The level of the `n`-th strict ascending ladder point. -/
def gaussianLadderSum (X : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, gaussianLadderHeightAt X a k ω

omit mΩ in
@[simp] theorem gaussianLadderSum_zero (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) :
    gaussianLadderSum X a 0 ω = 0 := by simp [gaussianLadderSum]

omit mΩ in
theorem gaussianLadderSum_succ (X : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) (ω : Ω) :
    gaussianLadderSum X a (n+1) ω =
      gaussianLadderSum X a n ω + gaussianLadderHeightAt X a n ω := by
  simp [gaussianLadderSum, Finset.sum_range_succ]

theorem gaussianLadderSum_measurable (hX : ∀ n, Measurable (X n)) (a : ℝ) (n : ℕ) :
    Measurable (gaussianLadderSum X a n) :=
  Finset.measurable_sum _ (fun k _ => gaussianLadderHeightAt_measurable hX a k)

/-- The `n`-th ladder level has the `n`-fold convolution of the ladder law. -/
theorem gaussianLadderSum_map [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    μ.map (gaussianLadderSum X a n) =
      measureConvPow (gaussianAscendingLadderLaw X μ a) n := by
  induction n with
  | zero =>
    rw [measureConvPow_zero]
    have : gaussianLadderSum X a 0 = fun _ : Ω => (0 : ℝ) := funext (fun ω => by simp)
    rw [this, Measure.map_const]
    simp
  | succ n ih =>
    have hfun : gaussianLadderSum X a (n+1) =
        fun ω => gaussianLadderSum X a n ω + gaussianLadderHeightAt X a n ω :=
      funext (fun ω => gaussianLadderSum_succ X a n ω)
    have hindep : IndepFun (gaussianLadderSum X a n) (gaussianLadderHeightAt X a n) μ := by
      have h := (gaussianLadderHeights_iIndepFun hX hi hG ha).indepFun_finsetSum_of_notMem
        (fun k => gaussianLadderHeightAt_measurable hX a k)
        (s := Finset.range n) (i := n) (by simp)
      have heq : (∑ j ∈ Finset.range n, gaussianLadderHeightAt X a j) =
          gaussianLadderSum X a n := by
        funext ω
        simp [gaussianLadderSum, Finset.sum_apply]
      rwa [heq] at h
    rw [hfun, map_add_of_indepFun (gaussianLadderSum_measurable hX a n)
      (gaussianLadderHeightAt_measurable hX a n) hindep, ih,
      gaussianLadderHeightAt_map hX hi hG ha n, measureConvPow_succ]

/-- The renewal measure of the actual ladder law is the expected number of
ladder levels in the set. -/
theorem ladderRenewalMeasure_eq_tsum_ladderSum [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a)
    {A : Set ℝ} (hA : MeasurableSet A) :
    ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a) A =
      ∑' n : ℕ, μ {ω | gaussianLadderSum X a n ω ∈ A} := by
  rw [ladderRenewalMeasure_apply _ hA]
  refine tsum_congr fun n => ?_
  rw [← gaussianLadderSum_map hX hi hG ha n,
    Measure.map_apply (gaussianLadderSum_measurable hX a n) hA]
  rfl

end SwingRepair
