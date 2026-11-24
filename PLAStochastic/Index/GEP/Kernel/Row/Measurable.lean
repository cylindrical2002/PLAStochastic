import PLAStochastic.Index.GEP.Kernel.Row.KilledTransition
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Joint measurability of the actual pointwise killed kernels

The shift, slope and two endpoints can vary measurably over an arbitrary
parameter space. The killing set, gap law and measurable density representative
remain fixed. The proof uses the original path integral defining `krDens`.

Weighted infinite sums below use Lean's total `tsum`, including its default
value outside the summability set. These measurability statements impose no
uniform summability hypothesis and prove no convergence assertion. On the
domains covered by `GEPKernelRowWeightedSum`, they apply to the actual convergent
Green series. They do not assert measurability of arbitrarily selected long-row
decompositions `G` and `R`.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

variable {X : Type*} [MeasurableSpace X]
variable {J : Set ℝ} {f : ℝ → ℝ}
variable {β a y z : X → ℝ} {g : X → (ℕ → ℝ)}

theorem measurable_kWalk_param (hy : Measurable y) (hβ : Measurable β)
    (ha : Measurable a) (hg : Measurable g) (n : ℕ) :
    Measurable (fun p => kWalk (y p) (β p) (a p) (g p) n) := by
  unfold kWalk
  exact (hy.add (hβ.const_mul n)).sub
    (ha.mul ((measurable_pi_apply n).comp (measurable_gapKeys.comp hg)))

theorem measurable_krAlive_param (hJ : MeasurableSet J) (hβ : Measurable β)
    (ha : Measurable a) (hy : Measurable y) (hg : Measurable g) (n : ℕ) :
    Measurable (fun p => krAlive J (β p) (a p) n (y p) (g p)) := by
  unfold krAlive
  refine Finset.measurable_prod _ fun l _ => ?_
  exact (measurable_const.indicator hJ).comp (measurable_kWalk_param hy hβ ha hg l)

theorem measurable_krKer_param (hJ : MeasurableSet J) (hf : Measurable f)
    (hβ : Measurable β) (ha : Measurable a) (hy : Measurable y) (hz : Measurable z) :
    Measurable (fun p => krKer J f (β p) (a p) (y p) (z p)) := by
  unfold krKer
  exact (((measurable_const.indicator hJ).comp hy).mul
    ((measurable_const.indicator hJ).comp hz)).mul
    ((hf.comp (((hy.add hβ).sub hz).div ha)).div (continuous_abs.measurable.comp ha))

/-- Every parameter in the original density integrand can vary measurably. -/
theorem measurable_krDens_integrand_param (hJ : MeasurableSet J) (hf : Measurable f)
    (hβ : Measurable β) (ha : Measurable a) (hy : Measurable y) (hz : Measurable z)
    (hg : Measurable g) (n : ℕ) :
    Measurable (fun p => krAlive J (β p) (a p) n (y p) (g p) *
      krKer J f (β p) (a p) (kWalk (y p) (β p) (a p) (g p) n) (z p)) :=
  (measurable_krAlive_param hJ hβ ha hy hg n).mul
    (measurable_krKer_param hJ hf hβ ha (measurable_kWalk_param hy hβ ha hg n) hz)

/-- Joint measurability comes from integrating the actual path formula; no
choice of a parameter-dependent density representative is involved. -/
theorem measurable_krDens_param (ν : ProbabilityMeasure ℝ)
    (hJ : MeasurableSet J) (hf : Measurable f)
    (hβ : Measurable β) (ha : Measurable a) (hy : Measurable y) (hz : Measurable z)
    (n : ℕ) : Measurable (fun p => krDens J ν f (β p) (a p) n (y p) (z p)) :=
  (measurable_krDens_integrand_param hJ hf (hβ.comp measurable_fst)
    (ha.comp measurable_fst) (hy.comp measurable_fst) (hz.comp measurable_fst)
    measurable_snd (n - 1)).stronglyMeasurable.integral_prod_right'.measurable

/-- The product coordinates are `((shift, slope), (initial, terminal))`. -/
theorem measurable_krDens_joint (ν : ProbabilityMeasure ℝ)
    (hJ : MeasurableSet J) (hf : Measurable f) (n : ℕ) :
    Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      krDens J ν f p.1.1 p.1.2 n p.2.1 p.2.2) :=
  measurable_krDens_param ν hJ hf (measurable_fst.comp measurable_fst)
    (measurable_snd.comp measurable_fst) (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_snd) n

/-- General measurable weights include the exponential and length rewards.
This is a statement about the total `tsum`, without a convergence hypothesis. -/
theorem measurable_tsum_weighted_krDens_param (ν : ProbabilityMeasure ℝ)
    (hJ : MeasurableSet J) (hf : Measurable f)
    (hβ : Measurable β) (ha : Measurable a) (hy : Measurable y) (hz : Measurable z)
    {W : ℕ → X → ℝ} (hW : ∀ n, Measurable (W n)) :
    Measurable (fun p => ∑' n : ℕ, W n p * krDens J ν f (β p) (a p) (n+1) (y p) (z p)) :=
  Measurable.tsum fun n => (hW n).mul (measurable_krDens_param ν hJ hf hβ ha hy hz (n+1))

theorem measurable_tsum_expw_krDens_param (ν : ProbabilityMeasure ℝ)
    (hJ : MeasurableSet J) (hf : Measurable f)
    (hβ : Measurable β) (ha : Measurable a) (hy : Measurable y) (hz : Measurable z)
    {ε w : X → ℝ} (hε : Measurable ε) (hw : Measurable w) :
    Measurable (fun p => ∑' n : ℕ, Real.exp (ε p * ((n+1 : ℕ) : ℝ) / w p ^ 2) *
      krDens J ν f (β p) (a p) (n+1) (y p) (z p)) :=
  measurable_tsum_weighted_krDens_param ν hJ hf hβ ha hy hz
    (fun n => (((hε.mul_const ((n+1 : ℕ) : ℝ)).div (hw.pow_const 2)).exp))

theorem measurable_tsum_expw_weighted_krDens_param (ν : ProbabilityMeasure ℝ)
    (hJ : MeasurableSet J) (hf : Measurable f)
    (hβ : Measurable β) (ha : Measurable a) (hy : Measurable y) (hz : Measurable z)
    {ε w : X → ℝ} (hε : Measurable ε) (hw : Measurable w) :
    Measurable (fun p => ∑' n : ℕ, Real.exp (ε p * ((n+1 : ℕ) : ℝ) / w p ^ 2) *
      (((n : ℝ) + 1 + w p) * krDens J ν f (β p) (a p) (n+1) (y p) (z p))) := by
  apply Measurable.tsum
  intro n
  exact (((hε.mul_const ((n+1 : ℕ) : ℝ)).div (hw.pow_const 2)).exp).mul
    ((hw.const_add ((n : ℝ) + 1)).mul (measurable_krDens_param ν hJ hf hβ ha hy hz (n+1)))

end
end PGM
