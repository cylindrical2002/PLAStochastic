import PLAStochastic.Index.KEP.ReferenceScale.ConvolutionWeakTests
import PLAStochastic.Index.KEP.ReferenceScale.OutputConvolutionSeries
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Exact physical second-test identities for the original output prefixes

The free cutoff splits into its actual surviving and stopped events. The
original convolution increment is C squared times the second derivative of
the genuine physical convolution test. The masked long-series bounds pay both
one cutoff term and every translated infinite tail.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kep_free_prefix_second_split (nu : ProbabilityMeasure ℝ) (eps : ℝ) (n : ℕ)
    {phi : ℝ → ℝ} (hphi : Measurable phi) {M : ℝ} (hb : ∀ t, |phi t| ≤ M) :
    (∫ g, phi (gapKeys g n) ∂iidLaw nu) =
      (∫ g in {g : ℕ → ℝ | (n : ℕ∞) < gapSegLen eps g}, phi (gapKeys g n) ∂iidLaw nu) +
      ∫ g in {g : ℕ → ℝ | gapSegLen eps g ≤ (n : ℕ∞)}, phi (gapKeys g n) ∂iidLaw nu := by
  have hi : Integrable (fun g : ℕ → ℝ => phi (gapKeys g n)) (iidLaw nu) :=
    (integrable_const M).mono'
      (hphi.comp ((measurable_pi_apply n).comp measurable_gapKeys)).aestronglyMeasurable
      (ae_of_all _ fun g => by simpa only [Real.norm_eq_abs] using hb (gapKeys g n))
  have hc : {g : ℕ → ℝ | (n : ℕ∞) < gapSegLen eps g}ᶜ =
      {g : ℕ → ℝ | gapSegLen eps g ≤ (n : ℕ∞)} := by
    ext g
    simp only [mem_compl_iff, mem_ofPred_eq, not_lt]
  have hh := integral_add_compl (measurableSet_lt_gapSegLen eps n) hi
  rw [hc] at hh
  exact hh.symm

theorem kep_physical_convolution_second_identity (nu : ProbabilityMeasure ℝ)
    {C : ℝ} (hC : C ≠ 0) (phi : ℝ → ℝ) (k : ℕ) (g : ℕ → ℝ) :
    kepPrefixConvolutionIncrement nu C phi k g = C ^ 2 *
      kepConvolutionTest nu (fun t => phi (t / C) / C ^ 2) (gapKeys g k) := by
  unfold kepPrefixConvolutionIncrement kepConvolutionTest
  rw [integral_div]
  field_simp

theorem kep_physical_free_second_identity (nu : ProbabilityMeasure ℝ)
    {C : ℝ} (hC : C ≠ 0) (phi : ℝ → ℝ) (k : ℕ) :
    (∫ g, phi (gapKeys g k / C) ∂iidLaw nu) =
      C ^ 2 * ∫ g, phi (gapKeys g k / C) / C ^ 2 ∂iidLaw nu := by
  rw [integral_div]
  field_simp

theorem kep_masked_series_tail_budget {eps : ℝ} {V : ℕ → ℝ}
    (hs : Summable (fun n : ℕ => if 16 * eps ≤ (n : ℝ) then |V n| else 0))
    (M : ℕ) (hM : 16 * eps ≤ (M : ℝ)) :
    Summable (fun n : ℕ => |V (n + M)|) ∧
      (∑' n : ℕ, |V (n + M)|) ≤
        (∑' n : ℕ, if 16 * eps ≤ (n : ℝ) then |V n| else 0) ∧
      |V M| ≤ ∑' n : ℕ, if 16 * eps ≤ (n : ℝ) then |V n| else 0 := by
  let F := fun n : ℕ => if 16 * eps ≤ (n : ℝ) then |V n| else 0
  have hnon : ∀ n, 0 ≤ F n := fun n => by dsimp [F]; split <;> positivity
  have he (n : ℕ) : F (n + M) = |V (n + M)| := by
    apply if_pos
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hsT : Summable (fun n : ℕ => F (n + M)) := (summable_nat_add_iff M).mpr hs
  simp_rw [he] at hsT
  have hb := tsum_comp_le_tsum_of_inj hs hnon (show Function.Injective (fun n : ℕ => n + M) from
    fun _a _b h => Nat.add_right_cancel h)
  change (∑' n : ℕ, F (n + M)) ≤ _ at hb
  simp_rw [he] at hb
  have hsingle := hs.le_tsum M (fun n _ => hnon n)
  change F M ≤ _ at hsingle
  rw [show F M = |V M| from if_pos hM] at hsingle
  exact ⟨hsT, hb, hsingle⟩

end

end PGM
