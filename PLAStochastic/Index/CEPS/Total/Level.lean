import PLAStochastic.Index.CEPS.Scaled.TrueTransformBudget
import PLAStochastic.Index.CEPS.Reward.RenewalData
import PLAStochastic.Index.CEPS.Canonical.DomainExists
import PLAStochastic.Index.CEPS.Jets.Shrink
import PLAStochastic.Index.CEPS.Actual.Defs

/-!
# WP10: dyadic levels and the class-independent normal transform `Gn`

`CepsNormalClose Gn` (and the other premises of `Glue/Defs.lean`) fix `Gn` before the class
constants, while the normal objects (roots, `dom.canonL`, the cutoff `δ`) depend on them. Each
law `ν` is therefore assigned its least dyadic level `n(ν)` (`cepsLevelIndex`): level `n` means one
density `f` of `ν` with the `RegLaw` bounds at scale `2^n`, variance in `[2^{-n}, 2^n]`, and the
step density `f(1 - ·)` in the weighted Sobolev class of order `cepsLevelOrder` and weight `2^{-n}`
with size at most `2^n` (`CepsLevel`). Level `n` carries a fixed canonical domain
(`cepsLevelDomain n`, by choice) of the step class `(2^n e^{2^{-n}}, 2^{-n}, 2^n)` and a fixed
cutoff `cepsLevelCutoff n`. The normal transform is the scaled normal expression of `Scaled/` at
these data:

  `cepsNormalGn ε ν z = cepsScaledTrueNormalExpression dom_{n(ν)} ρW (2ε)⁻¹ δ_{n(ν)} z`,

`ρW = ν ∘ (1 - ·)⁻¹`. On every input class `n(ν)` takes finitely many values, so class-uniform
constants are maxima over finitely many levels.
-/

noncomputable section
open MeasureTheory Set
open PGM.WienerHopf

namespace PGM

/-- Sobolev order of the level classes. -/
def cepsLevelOrder : ℕ := 6

/-- `2^n`: density, variance and Sobolev-size scale of level `n`. -/
def cepsLevelScale (n : ℕ) : ℝ := (2 : ℝ) ^ n

/-- `2^{-n}`: decay rate, variance floor and Sobolev weight of level `n`. -/
def cepsLevelRate (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

theorem cepsLevelScale_pos (n : ℕ) : 0 < cepsLevelScale n := by unfold cepsLevelScale; positivity

theorem cepsLevelRate_pos (n : ℕ) : 0 < cepsLevelRate n := by unfold cepsLevelRate; positivity

theorem cepsLevelScale_mono {n k : ℕ} (h : n ≤ k) : cepsLevelScale n ≤ cepsLevelScale k :=
  pow_le_pow_right₀ (by norm_num) h

theorem cepsLevelRate_anti {n k : ℕ} (h : n ≤ k) : cepsLevelRate k ≤ cepsLevelRate n :=
  inv_anti₀ (by positivity) (cepsLevelScale_mono h)

/-- **Level-`n` density** `f` of `ν`: the `RegLaw` bounds at scale `2^n`, variance in
`[2^{-n}, 2^n]`, and the step density `f(1 - ·)` in the weighted Sobolev class of order
`cepsLevelOrder` and weight `2^{-n}` with size at most `2^n`. -/
def CepsLevelDensity (n : ℕ) (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, x ≤ 0 → f x = 0) ∧
    (∀ x, f x ≤ cepsLevelScale n * Real.exp (-cepsLevelRate n * x)) ∧
    (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
    lawMean ν = 1 ∧ cepsLevelRate n ≤ lawVar ν ∧ lawVar ν ≤ cepsLevelScale n ∧
    CepsSobolevClass cepsLevelOrder (cepsLevelRate n) (fun x => f (1 - x)) ∧
    cepsSobolev cepsLevelOrder (cepsLevelRate n) (fun x => f (1 - x)) ≤ cepsLevelScale n

/-- **Level `n`.** -/
def CepsLevel (n : ℕ) (ν : ProbabilityMeasure ℝ) : Prop :=
  ∃ f : ℝ → ℝ, CepsLevelDensity n ν f

open Classical in
/-- The least level of `ν` (`0` if there is none). -/
def cepsLevelIndex (ν : ProbabilityMeasure ℝ) : ℕ :=
  if h : ∃ n, CepsLevel n ν then Nat.find h else 0

theorem cepsLevelIndex_spec {ν : ProbabilityMeasure ℝ} {n : ℕ} (h : CepsLevel n ν) :
    CepsLevel (cepsLevelIndex ν) ν ∧ cepsLevelIndex ν ≤ n := by
  classical
  have he : ∃ n, CepsLevel n ν := ⟨n, h⟩
  unfold cepsLevelIndex
  rw [dif_pos he]
  exact ⟨Nat.find_spec he, Nat.find_min' he h⟩

/-- Step-class density constant of level `n`. -/
def cepsLevelStepD (n : ℕ) : ℝ := cepsLevelScale n * Real.exp (cepsLevelRate n)

theorem cepsLevelStepD_pos (n : ℕ) : 0 < cepsLevelStepD n :=
  mul_pos (cepsLevelScale_pos n) (Real.exp_pos _)

/-- The canonical domain of level `n` (chosen once for all laws). -/
def cepsLevelDomain (n : ℕ) :
    CepsCanonDomain (cepsLevelStepD n) (cepsLevelRate n) (cepsLevelScale n) :=
  Classical.choice (cepsCanonDomain_exists (cepsLevelStepD_pos n) (cepsLevelRate_pos n)
    (cepsLevelScale_pos n))

/-- The drift cutoff of level `n`. -/
def cepsLevelCutoff (n : ℕ) : ℝ :=
  min (min (cepsLevelDomain n).renewalMu ((cepsLevelDomain n).μ₀ / 8))
    (min ((cepsLevelDomain n).trueDecayScaleBase (cepsLevelScale n) / 4) (1 / 2))

/-- **The class-independent normal transform** `Ĝ(b, z)`, `b = (2ε)⁻¹`. -/
def cepsNormalGn (eps : ℝ) (ν : ProbabilityMeasure ℝ) (z : ℂ) : ℂ :=
  cepsScaledTrueNormalExpression (cepsLevelDomain (cepsLevelIndex ν))
    ((ν : Measure ℝ).map fun x => 1 - x) (2 * eps)⁻¹ (cepsLevelCutoff (cepsLevelIndex ν)) z

theorem cepsLevelCutoff_le (n : ℕ) :
    cepsLevelCutoff n ≤ (cepsLevelDomain n).renewalMu ∧
      cepsLevelCutoff n ≤ (cepsLevelDomain n).μ₀ / 8 ∧
      cepsLevelCutoff n ≤ (cepsLevelDomain n).trueDecayScaleBase (cepsLevelScale n) / 4 ∧
      cepsLevelCutoff n ≤ 1 / 2 := by
  unfold cepsLevelCutoff
  exact ⟨(min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
    (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩

/-- Level data give the step law of `W = 1 - X` in the level step class. -/
theorem CepsLevelDensity.stepLaw {n : ℕ} {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ}
    (h : CepsLevelDensity n ν f) :
    RegLaw (cepsLevelScale n) (cepsLevelRate n) (cepsLevelRate n) (cepsLevelScale n) ν ∧
      CepsGapDensity ν f (cepsLevelScale n) ∧
      IsStepLaw ((ν : Measure ℝ).map fun x => 1 - x) (fun x => f (1 - x)) (cepsLevelStepD n)
        (cepsLevelRate n) (cepsLevelScale n) ∧
      CepsSobolevClass cepsLevelOrder (cepsLevelRate n) (fun x => f (1 - x)) ∧
      cepsSobolev cepsLevelOrder (cepsLevelRate n) (fun x => f (1 - x)) ≤ cepsLevelScale n := by
  obtain ⟨hfm, hf0, hneg, hfb, hν, hmean, hvlo, hvhi, hS, hSM⟩ := h
  have hθ := cepsLevelRate_pos n
  have hD := cepsLevelScale_pos n
  have hreg : RegLaw (cepsLevelScale n) (cepsLevelRate n) (cepsLevelRate n) (cepsLevelScale n) ν :=
    ⟨⟨f, hfm, hf0, hneg, hfb, hν⟩, hmean, hvlo, hvhi⟩
  have hsq : Integrable (fun x : ℝ => (x - 1) ^ 2) (ν : Measure ℝ) := by
    have e : (fun x : ℝ => (x - 1) ^ 2) = fun x => x ^ 2 - 2 * x + 1 := by ext x; ring
    rw [e]
    exact ((hreg.tail_sq hθ).1.sub ((hreg.tail_mean hθ).1.const_mul 2)).add (integrable_const _)
  have hX : IsGapLaw (ν : Measure ℝ) f (cepsLevelScale n) (cepsLevelRate n) (cepsLevelScale n) :=
    ⟨inferInstance, hν, hfm, hf0, hneg, fun x _ => hfb x, hsq, hmean, by
      simpa [lawVar, hmean] using hvhi⟩
  have hgap : CepsGapDensity ν f (cepsLevelScale n) := by
    refine ⟨hfm, hf0, fun x => ?_, hneg, hν⟩
    rcases le_or_gt x 0 with hx | hx
    · rw [hneg x hx]; exact hD.le
    · exact (hfb x).trans (mul_le_of_le_one_right hD.le (Real.exp_le_one_iff.mpr (by nlinarith)))
  exact ⟨hreg, hgap, hX.toStepLaw hθ.le hD.le, hS, hSM⟩

/-- Level data give the step law of `W = 1 - X` in the level step class. -/
theorem CepsLevel.stepLaw {n : ℕ} {ν : ProbabilityMeasure ℝ} (h : CepsLevel n ν) :
    ∃ f : ℝ → ℝ, CepsLevelDensity n ν f ∧
      RegLaw (cepsLevelScale n) (cepsLevelRate n) (cepsLevelRate n) (cepsLevelScale n) ν ∧
      CepsGapDensity ν f (cepsLevelScale n) ∧
      IsStepLaw ((ν : Measure ℝ).map fun x => 1 - x) (fun x => f (1 - x)) (cepsLevelStepD n)
        (cepsLevelRate n) (cepsLevelScale n) ∧
      CepsSobolevClass cepsLevelOrder (cepsLevelRate n) (fun x => f (1 - x)) ∧
      cepsSobolev cepsLevelOrder (cepsLevelRate n) (fun x => f (1 - x)) ≤ cepsLevelScale n := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, hf, hf.stepLaw⟩

end PGM
