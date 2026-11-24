import PLAStochastic.Index.GEP.LayerLaw.Defs
import Mathlib.MeasureTheory.Group.Convolution

/-!
# WP2 (`OrbitClosure`): shared definitions

Design note: `research/2026-09-28-lean-gep-additive/wp2-design.md`.

The orbit closure is proved on laws.  A law `ρ` of normalised layer gaps is described by

* `MomClass b β vmin ρ`: support in `(0, ∞)`, finite third moment, mean one, variance in
  `[vmin, b]` and `E|X - 1|³ ≤ β v^{3/2}` (the normalised form of `LayerOK`);
* `ExpMom θ B ρ`: `E e^{θ X} ≤ B`;
* `LocBd D μ`: `μ A ≤ D |A|` for Borel `A` (the measure form of a density bound `D`,
  as in `LocalGapLaw` of `PLAStochastic/Index/OneLayer/ThresholdMargin.lean`);
* `EnvBd K c μ`: `μ` is dominated by `K e^{-c x} 1_{x > 0} dx` (the envelope of `RegLaw`).

The one-layer analysis uses

* `convPow μ n`: the `n`-fold convolution power (the law of `S_n`);
* `stopMeas eps ρ t`: the joint stopping measure `A ↦ P(T = t, S_t ∈ A)` of the first ALG-OPT
  segment of iid `ρ` gaps (`density-tail.md` (4.1));
* `qdev t a = min((a - t)²/t, |a - t|)`: the Bernstein deviation exponent `Q_t(a)` of
  `density-tail.md` (4.5).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-! ## Local bounds and envelopes -/

/-- Measure form of a bounded density: `μ A ≤ D |A|` for every Borel set `A`. -/
def LocBd (D : ℝ) (μ : Measure ℝ) : Prop :=
  ∀ A : Set ℝ, MeasurableSet A → μ A ≤ ENNReal.ofReal D * volume A

/-- The exponential envelope `x ↦ K e^{-c x}` on `(0, ∞)`, zero on `(-∞, 0]`. -/
def envFun (K c : ℝ) : ℝ → ℝ := (Ioi (0 : ℝ)).indicator fun x => K * Real.exp (-c * x)

/-- `μ` is dominated by the exponential envelope `K e^{-c x} 1_{x > 0} dx`. -/
def EnvBd (K c : ℝ) (μ : Measure ℝ) : Prop :=
  μ ≤ volume.withDensity fun x => ENNReal.ofReal (envFun K c x)

/-! ## Moment classes of normalised gap laws -/

/-- The moment class of a normalised gap law: positive support, `L³`, mean one, variance in
`[vmin, b]` and normalised third absolute central moment at most `β`. -/
structure MomClass (b β vmin : ℝ) (ρ : ProbabilityMeasure ℝ) : Prop where
  pos : (ρ : Measure ℝ) (Iic 0) = 0
  memLp3 : MemLp id 3 (ρ : Measure ℝ)
  mean : lawMean ρ = 1
  var_ge : vmin ≤ lawVar ρ
  var_le : lawVar ρ ≤ b
  third_le : ∫ x, |x - 1| ^ 3 ∂(ρ : Measure ℝ) ≤ β * Real.sqrt (lawVar ρ) ^ 3

/-- An exponential moment `E e^{θ X} ≤ B`. -/
structure ExpMom (θ B : ℝ) (ρ : ProbabilityMeasure ℝ) : Prop where
  integrable : Integrable (fun x => Real.exp (θ * x)) (ρ : Measure ℝ)
  le : ∫ x, Real.exp (θ * x) ∂(ρ : Measure ℝ) ≤ B

/-! ## Convolution powers, the joint stopping measure, the deviation exponent -/

/-- The `n`-fold convolution power of a measure on `ℝ`: the law of `X₁ + ⋯ + Xₙ`. -/
def convPow (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => convPow μ n ∗ μ

theorem convPow_zero (μ : Measure ℝ) : convPow μ 0 = Measure.dirac 0 := rfl

theorem convPow_succ (μ : Measure ℝ) (n : ℕ) : convPow μ (n + 1) = convPow μ n ∗ μ := rfl

theorem isProbabilityMeasure_convPow (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ n, IsProbabilityMeasure (convPow μ n)
  | 0 => by rw [convPow_zero]; infer_instance
  | n + 1 => by
    have := isProbabilityMeasure_convPow μ n
    rw [convPow_succ]; infer_instance

instance (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (convPow μ n) :=
  isProbabilityMeasure_convPow μ n

theorem convPow_one (μ : Measure ℝ) [SFinite μ] : convPow μ 1 = μ := by
  rw [convPow_succ, convPow_zero]
  exact Measure.dirac_zero_conv μ

/-- The joint stopping measure `A ↦ P(T = t, S_t ∈ A)` of the first ALG-OPT segment of iid
`ρ` gaps, with `T = gapSegLen eps` and `S_t = gapKeys g t`. -/
def stopMeas (eps : ℝ) (ρ : ProbabilityMeasure ℝ) (t : ℕ) : Measure ℝ :=
  ((iidLaw ρ).restrict {g | gapSegLen eps g = (t : ℕ∞)}).map fun g => gapKeys g t

/-- The deviation exponent `Q_t(a) = min((a - t)²/t, |a - t|)`. -/
def qdev (t a : ℝ) : ℝ := min ((a - t) ^ 2 / t) |a - t|

end

end PGM
