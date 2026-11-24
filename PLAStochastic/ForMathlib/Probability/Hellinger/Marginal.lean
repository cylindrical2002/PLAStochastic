import PLAStochastic.ForMathlib.Probability.Hellinger.Joint

/-!
# Hellinger contraction when forgetting a coordinate

The output density is defined by its actual marginal integral. The proof applies
the reverse triangle inequality to each pair of square-root sections in `L²`,
then integrates by Fubini. In particular, a common conditional density kernel
contracts Hellinger distance.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

def marginalLeft (p : HellingerDensity (μ.prod ν)) : HellingerDensity μ where
  density x := ∫ y, p.density (x, y) ∂ν
  measurable := p.measurable.stronglyMeasurable.integral_prod_right'.measurable
  nonneg x := integral_nonneg fun y => p.nonneg (x, y)
  integrable := p.integrable.integral_prod_left
  integral_eq_one := (integral_prod p.density p.integrable).symm.trans p.integral_eq_one

omit [SFinite ν] in
/-- An integrable nonnegative function has square-root `L²` norm equal to its mass. -/
theorem norm_sqrt_toLp {f : β → ℝ} (hm : Measurable f) (hn : ∀ y, 0 ≤ f y)
    (hi : Integrable f ν) :
    ∃ hf : MemLp (fun y => Real.sqrt (f y)) 2 ν,
      ‖hf.toLp (fun y => Real.sqrt (f y))‖ = Real.sqrt (∫ y, f y ∂ν) := by
  have hf : MemLp (fun y => Real.sqrt (f y)) 2 ν :=
    (memLp_two_iff_integrable_sq hm.sqrt.aestronglyMeasurable).2
      (by simpa only [Real.sq_sqrt (hn _)] using hi)
  refine ⟨hf, ?_⟩
  have he := norm_toLp_sq hf
  simp only [Real.sq_sqrt (hn _)] at he
  rw [← he, Real.sqrt_sq (norm_nonneg _)]

theorem hellinger_sq_marginalLeft_le (p q : HellingerDensity (μ.prod ν)) :
    p.marginalLeft.hellinger q.marginalLeft ^ 2 ≤ p.hellinger q ^ 2 := by
  have hi : Integrable (fun z => (Real.sqrt (p.density z) - Real.sqrt (q.density z)) ^ 2)
      (μ.prod ν) := by
    simpa only [Pi.sub_apply] using (p.sqrt_memLp.sub q.sqrt_memLp).integrable_sq
  rw [hellinger_sq, hellinger_sq, integral_prod _ hi]
  apply integral_mono_ae
    (p.marginalLeft.sqrt_memLp.sub q.marginalLeft.sqrt_memLp).integrable_sq
    hi.integral_prod_left
  filter_upwards [p.integrable.prod_right_ae, q.integrable.prod_right_ae] with x hpx hqx
  have hpm : Measurable (fun y => p.density (x, y)) :=
    p.measurable.comp (measurable_const.prodMk measurable_id)
  have hqm : Measurable (fun y => q.density (x, y)) :=
    q.measurable.comp (measurable_const.prodMk measurable_id)
  obtain ⟨hp, hnp⟩ := norm_sqrt_toLp hpm
    (fun y => p.nonneg (x, y)) hpx
  obtain ⟨hq, hnq⟩ := norm_sqrt_toLp hqm
    (fun y => q.nonneg (x, y)) hqx
  let up := hp.toLp (fun y => Real.sqrt (p.density (x, y)))
  let uq := hq.toLp (fun y => Real.sqrt (q.density (x, y)))
  have hd : ‖up - uq‖ ^ 2 =
      ∫ y, (Real.sqrt (p.density (x, y)) - Real.sqrt (q.density (x, y))) ^ 2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub up uq, hp.coeFn_toLp, hq.coeFn_toLp] with y hsub hpy hqy
    simp only [hsub, Pi.sub_apply, show up y = Real.sqrt (p.density (x, y)) from hpy,
      show uq y = Real.sqrt (q.density (x, y)) from hqy,
      RCLike.inner_apply, conj_trivial, pow_two]
  change (Real.sqrt (∫ y, p.density (x, y) ∂ν) -
    Real.sqrt (∫ y, q.density (x, y) ∂ν)) ^ 2 ≤ _
  rw [← hnp, ← hnq, ← hd]
  have h := abs_norm_sub_norm_le up uq
  nlinarith [norm_nonneg (up - uq), abs_nonneg (‖up‖ - ‖uq‖), sq_abs (‖up‖ - ‖uq‖)]

theorem hellinger_marginalLeft_le (p q : HellingerDensity (μ.prod ν)) :
    p.marginalLeft.hellinger q.marginalLeft ≤ p.hellinger q := by
  have h := hellinger_sq_marginalLeft_le p q
  nlinarith [p.marginalLeft.hellinger_nonneg q.marginalLeft, p.hellinger_nonneg q]

def swap (p : HellingerDensity (μ.prod ν)) : HellingerDensity (ν.prod μ) where
  density z := p.density (z.2, z.1)
  measurable := p.measurable.comp measurable_swap
  nonneg z := p.nonneg (z.2, z.1)
  integrable := p.integrable.swap
  integral_eq_one := (integral_prod_swap p.density).trans p.integral_eq_one

theorem hellinger_swap (p q : HellingerDensity (μ.prod ν)) :
    p.swap.hellinger q.swap = p.hellinger q := by
  have he : p.swap.hellinger q.swap ^ 2 = p.hellinger q ^ 2 := by
    rw [hellinger_sq, hellinger_sq]
    exact integral_prod_swap (μ := μ) (ν := ν)
      (fun z => (Real.sqrt (p.density z) - Real.sqrt (q.density z)) ^ 2)
  nlinarith [p.swap.hellinger_nonneg q.swap, p.hellinger_nonneg q]

def marginalRight (p : HellingerDensity (μ.prod ν)) : HellingerDensity ν :=
  p.swap.marginalLeft

theorem hellinger_marginalRight_le (p q : HellingerDensity (μ.prod ν)) :
    p.marginalRight.hellinger q.marginalRight ≤ p.hellinger q := by
  change p.swap.marginalLeft.hellinger q.swap.marginalLeft ≤ _
  exact (hellinger_marginalLeft_le p.swap q.swap).trans_eq (hellinger_swap p q)

/-- Data processing for a jointly measurable common conditional density kernel. -/
theorem hellinger_common_kernel_le (p q : HellingerDensity μ)
    (k : α → HellingerDensity ν)
    (hk : Measurable (fun z : α × β => (k z.1).density z.2)) :
    (p.joint k hk).marginalRight.hellinger (q.joint k hk).marginalRight ≤
      p.hellinger q := by
  exact (hellinger_marginalRight_le (p.joint k hk) (q.joint k hk)).trans_eq
    (hellinger_joint_same p q k hk)

end

end ProbabilityTheory.HellingerDensity
