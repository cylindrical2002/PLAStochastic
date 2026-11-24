import PLAStochastic.Index.Endpoint.LayerInduction
import PLAStochastic.Index.Model.ExpSequence
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The G-EP layer map on gap laws

Objects of the additive G-EP theorem (research note
`research/2026-09-28-gep-closure/closure-assembly.md`), stated on laws rather than on
random sequences.

* `iidLaw ν` is the canonical iid gap sequence with law `ν`.
* `lawC eps ν` is `C_ε(ν) = E T`, the mean number of keys in the first ALG-OPT segment.
* `stopSum eps g` is the key at the end of the first segment, `S_T = g 0 + ⋯ + g (T-1)`.
* `lawPhi eps ν` is the normalised layer map `Φ_ε ν = Law(S_T / C_ε(ν))`.
* `RegLaw D θ vlo vhi ν` is the regular class of `joint-response.md` §1: a law on `(0, ∞)`
  with mean one, a density `f ≤ D e^{-θx}`, and variance in `[vlo, vhi]`.
* `dEta η ν ρ = ∫_0^∞ e^{ηx} |F_ν(x) - F_ρ(x)| dx` is the weighted `W₁` distance.
* `W2Le μ ν w` says that some coupling of `μ` and `ν` has `E (X - Y)² ≤ w²`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- The canonical iid gap sequence with law `ν`. -/
def iidLaw (ν : ProbabilityMeasure ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => (ν : Measure ℝ))

instance (ν : ProbabilityMeasure ℝ) : IsProbabilityMeasure (iidLaw ν) := by
  unfold iidLaw; infer_instance

/-- `C_ε(ν)`: the mean number of keys in the first ALG-OPT segment of iid `ν` gaps. -/
def lawC (eps : ℝ) (ν : ProbabilityMeasure ℝ) : ℝ :=
  ∫ g, ((gapSegLen eps g).toNat : ℝ) ∂(iidLaw ν)

/-- The next-layer gap: the key that starts the second segment. -/
def stopSum (eps : ℝ) (g : ℕ → ℝ) : ℝ := gapKeys g (gapSegLen eps g).toNat

theorem measurable_stopSum (eps : ℝ) : Measurable (stopSum eps) := by
  have hT : Measurable fun g : ℕ → ℝ => (gapSegLen eps g).toNat :=
    measurable_from_top.comp (isStoppingRule_gapSegLen eps).measurable
  have hm : Measurable (fun p : (ℕ → ℝ) × ℕ => gapKeys p.1 p.2) :=
    measurable_from_prod_countable_left fun n =>
      (measurable_pi_apply n).comp measurable_gapKeys
  exact hm.comp (measurable_id.prodMk hT)

/-- The normalised layer map `Φ_ε ν = Law(S_T / C_ε(ν))`. -/
def lawPhi (eps : ℝ) (ν : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  ⟨(iidLaw ν).map (fun g => stopSum eps g / lawC eps ν),
    Measure.isProbabilityMeasure_map ((measurable_stopSum eps).div_const _).aemeasurable⟩

/-- Mean of a law. -/
def lawMean (ν : ProbabilityMeasure ℝ) : ℝ := ∫ x, x ∂(ν : Measure ℝ)

/-- Variance of a law. -/
def lawVar (ν : ProbabilityMeasure ℝ) : ℝ := ∫ x, (x - lawMean ν) ^ 2 ∂(ν : Measure ℝ)

/-- The regular class of `joint-response.md` §1: mean-one laws on `(0, ∞)` with a density
bounded by `D e^{-θx}` and variance in `[vlo, vhi]`. -/
structure RegLaw (D θ vlo vhi : ℝ) (ν : ProbabilityMeasure ℝ) : Prop where
  density : ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, x ≤ 0 → f x = 0) ∧
    (∀ x, f x ≤ D * Real.exp (-θ * x)) ∧
    (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))
  mean : lawMean ν = 1
  var_ge : vlo ≤ lawVar ν
  var_le : lawVar ν ≤ vhi

/-- The weighted `W₁` distance `d_η(ν, ρ) = ∫_0^∞ e^{ηx} |F_ν(x) - F_ρ(x)| dx`. -/
def dEta (η : ℝ) (ν ρ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), Real.exp (η * x) * |cdf (ν : Measure ℝ) x - cdf (ρ : Measure ℝ) x|

/-- Some coupling of `μ` and `ν` has `E (X - Y)² ≤ w²` (so `W₂(μ, ν) ≤ w` when `0 ≤ w`). -/
def W2Le (μ ν : ProbabilityMeasure ℝ) (w : ℝ) : Prop :=
  ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧ π.map Prod.fst = (μ : Measure ℝ) ∧
    π.map Prod.snd = (ν : Measure ℝ) ∧ Integrable (fun p => (p.1 - p.2) ^ 2) π ∧
    ∫ p, (p.1 - p.2) ^ 2 ∂π ≤ w ^ 2

/-- The standard exponential law as a probability measure. -/
def expPM : ProbabilityMeasure ℝ := ⟨expMeasure 1, inferInstance⟩

end

end PGM
