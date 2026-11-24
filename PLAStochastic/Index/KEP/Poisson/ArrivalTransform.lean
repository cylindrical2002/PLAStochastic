import PLAStochastic.Index.KEP.Poisson.Intensity
import PLAStochastic.Index.Model.ExpSequence
import PLAStochastic.Index.Model.IIDPairs

/-!
# The actual Poisson arrival transform from exponential innovations

The intensity primitive and its global inverse define every physical arrival.
The cumulative-intensity and restart identities hold pointwise. The physical
pair sequence is measurable and its keys are exactly these transformed arrivals.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

theorem kepIntensityInverse_hasDerivAt {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (t : ℝ) :
    HasDerivAt (kepIntensityOrderIso hf).symm
      (1 / f ((kepIntensityOrderIso hf).symm t)) t := by
  rw [one_div]
  apply HasDerivAt.of_local_left_inverse
    (kepIntensityOrderIso hf).symm.continuous.continuousAt
    (kepIntensityPrimitive_hasDerivAt hf _) (hf.f_pos _).ne'
  exact Filter.Eventually.of_forall fun v => (kepIntensityOrderIso hf).apply_symm_apply v

def kepPoissonArrival {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x t : ℝ) : ℝ :=
  (kepIntensityOrderIso hf).symm (kepIntensityPrimitive f x + t / n)

theorem kepPoissonArrival_zero {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ) :
    kepPoissonArrival hf n x 0 = x := by
  change (kepIntensityOrderIso hf).symm ((kepIntensityOrderIso hf) x + 0 / n) = x
  rw [zero_div, add_zero]
  exact (kepIntensityOrderIso hf).symm_apply_apply x

theorem kepPoissonArrival_intensity {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x t : ℝ) :
    kepIntensityPrimitive f (kepPoissonArrival hf n x t) =
      kepIntensityPrimitive f x + t / n :=
  (kepIntensityOrderIso hf).apply_symm_apply _

theorem kepPoissonArrival_restart {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x t s : ℝ) :
    kepPoissonArrival hf n (kepPoissonArrival hf n x t) s =
      kepPoissonArrival hf n x (t + s) := by
  change (kepIntensityOrderIso hf).symm
    (kepIntensityPrimitive f (kepPoissonArrival hf n x t) + s / n) = _
  rw [kepPoissonArrival_intensity, add_assoc, ← add_div]
  rfl

theorem kepPoissonArrival_continuous {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n : ℝ) :
    Continuous (fun p : ℝ × ℝ => kepPoissonArrival hf n p.1 p.2) :=
  (kepIntensityOrderIso hf).symm.continuous.comp
    (((kepIntensityPrimitive_continuous hf).comp continuous_fst).add
      (continuous_snd.div_const n))

theorem kepPoissonArrival_hasDerivAt {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x t : ℝ) :
    HasDerivAt (kepPoissonArrival hf n x)
      (1 / (n * f (kepPoissonArrival hf n x t))) t := by
  have h := (kepIntensityInverse_hasDerivAt hf (kepIntensityPrimitive f x + t / n)).comp t
    ((hasDerivAt_id t).div_const n |>.const_add (kepIntensityPrimitive f x))
  change HasDerivAt (kepPoissonArrival hf n x)
    (1 / f (kepPoissonArrival hf n x t) * (1 / n)) t at h
  have he : 1 / (n * f (kepPoissonArrival hf n x t)) =
      1 / f (kepPoissonArrival hf n x t) * (1 / n) := by
    rw [one_div, mul_inv_rev]
    ring
  rw [he]
  exact h

theorem kepPoissonArrival_ge {f : ℝ → ℝ} {flo fhi L n t : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (ht : 0 ≤ t) (x : ℝ) :
    x ≤ kepPoissonArrival hf n x t := by
  rw [← (kepIntensityOrderIso hf).le_iff_le, kepIntensityOrderIso_apply,
    kepIntensityOrderIso_apply, kepPoissonArrival_intensity]
  exact le_add_of_nonneg_right (div_nonneg ht hn.le)

theorem kepPoissonArrival_gap_bracket {f : ℝ → ℝ} {flo fhi L n t : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (ht : 0 ≤ t) (x : ℝ) :
    t / (n * fhi) ≤ kepPoissonArrival hf n x t - x ∧
      kepPoissonArrival hf n x t - x ≤ t / (n * flo) := by
  have h := kepIntensityPrimitive_bracket hf (kepPoissonArrival_ge hf hn ht x)
  rw [kepPoissonArrival_intensity, add_sub_cancel_left] at h
  constructor
  · rw [← div_div, div_le_iff₀ hf.fhi_pos]
    linarith only [h.2]
  · rw [← div_div, le_div_iff₀ hf.pos]
    linarith only [h.1]

def kepPoissonNormalizedGap {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x t : ℝ) : ℝ :=
  n * f x * (kepPoissonArrival hf n x t - x)

def kepPoissonKeys {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ) (g : ℕ → ℝ) (k : ℕ) : ℝ :=
  kepPoissonArrival hf n x (gapKeys g k)

def kepPoissonPairs {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ) (g : ℕ → ℝ) (k : ℕ) : ℝ × ℕ :=
  (kepPoissonKeys hf n x g (k + 1) - kepPoissonKeys hf n x g k, 1)

theorem measurable_kepPoissonKeys {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n : ℝ) (k : ℕ) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => kepPoissonKeys hf n p.1 p.2 k) := by
  have hk : Measurable (fun g : ℕ → ℝ => gapKeys g k) :=
    (measurable_pi_apply k).comp measurable_gapKeys
  change Measurable (fun p : ℝ × (ℕ → ℝ) =>
    (kepIntensityOrderIso hf).symm (kepIntensityPrimitive f p.1 + gapKeys p.2 k / n))
  apply (kepIntensityOrderIso hf).symm.continuous.measurable.comp
  exact ((kepIntensityPrimitive_continuous hf).measurable.comp measurable_fst).add
    ((hk.comp measurable_snd).div_const n)

theorem measurable_kepPoissonPairs {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n : ℝ) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => kepPoissonPairs hf n p.1 p.2) := by
  refine measurable_pi_lambda _ fun k => ?_
  exact ((measurable_kepPoissonKeys hf n (k + 1)).sub
    (measurable_kepPoissonKeys hf n k)).prodMk measurable_const

theorem pairKeys_kepPoissonPairs {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ) (g : ℕ → ℝ) (k : ℕ) :
    pairKeys (kepPoissonPairs hf n x g) k = kepPoissonKeys hf n x g k - x := by
  induction k with
  | zero => simp [pairKeys, kepPoissonKeys, gapKeys, kepPoissonArrival_zero]
  | succ k ih =>
    rw [pairKeys, Finset.sum_range_succ]
    change pairKeys (kepPoissonPairs hf n x g) k +
      (kepPoissonKeys hf n x g (k + 1) - kepPoissonKeys hf n x g k) = _
    rw [ih]
    ring

end

end PGM
