import PLAStochastic.Index.GEP.DirectTerm.Defs

/-!
# WP4 `RawDisc`: complex survival integrals and the survival bound

`RawDisc` (`PLAStochastic/Index/GEP/DirectTerm/Defs.lean`) is split into

* **(SurvivalBound)** the analytic core: along `ν_z = (1 - z) ν + z σ`, the complex survival
  integrals `V_{k,z}(G) = ∫ G(S_k) 1{T > k} dν_z^{⊗k}` have a summable majorant `B k`, uniform on a
  disc of fixed radius, with `∑ B ≤ K ε^p` (raw-output-response (1)–(2), analytic-response §4–6,
  mixed-kernel-response §2–4, raw-measure-tools);
* **(assembly)** the occupation series `f z = F 0 + ∑_k ∫ (F(S_k + x) - F(S_k)) 1{T > k} dν_z^{⊗(k+1)}`
  is holomorphic with `‖f‖ ≤ K ε^p`, equals `E_{ν_t}[F(S_T)]` for real `t ∈ [0, r]`, and has
  `f'(0) = ∫ I_F d(σ - ν)`; this gives `RawDisc` from `SurvivalBound`.

Complex measures are never formed.  `ν_z^{⊗k}` is expanded over the words `S ⊆ {0, …, k-1}`
(coordinates drawn from `σ`): `cSurv` is the polynomial
`∑_S (1-z)^{k-|S|} z^{|S|} ∫ G(S_k) 1{T > k} d wordLaw ν σ S`, with `wordLaw ν σ S` the product law
having `σ` at the coordinates in `S` and `ν` elsewhere.  The event `{k < T}` and `S_k = gapKeys g k`
read only `g 0, …, g (k-1)`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- The product law with `σ` at the coordinates in `S` and `ν` elsewhere. -/
def wordLaw (ν σ : ProbabilityMeasure ℝ) (S : Finset ℕ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun i : ℕ => (((if i ∈ S then σ else ν : ProbabilityMeasure ℝ)) : Measure ℝ))

instance (ν σ : ProbabilityMeasure ℝ) (S : Finset ℕ) : IsProbabilityMeasure (wordLaw ν σ S) := by
  unfold wordLaw; infer_instance

/-- The complex survival integral `∫ G(S_k) 1{k < T} d((1 - z) ν + z σ)^{⊗k}`, expanded over words. -/
def cSurv (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (k : ℕ) (G : ℝ → ℝ) : ℂ :=
  ∑ S ∈ (Finset.range k).powerset, (1 - z) ^ (k - S.card) * z ^ S.card *
    (((∫ g, {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator
        (fun g => G (gapKeys g k)) g ∂(wordLaw ν σ S)) : ℝ) : ℂ)

/-- **Survival bound on a fixed disc.**  For the regular class there is an output weight `γ > 0`
such that for every direction exponential moment `θσ > 0` there are `r > 0`, `K`, `e0` and a
power `p` with: for `ε ≥ e0`, `ν` regular, `σ` a direction law and every test
`|G(y)| ≤ e^{γ y / ε²}` (`y ≥ 0`), the complex survival integrals on `ball 0 r` have a common
summable majorant `B` with `∑ B ≤ K ε^p`. -/
def SurvivalBound : Prop :=
  ∀ D θ vlo vhi : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi →
    ∃ γ : ℝ, 0 < γ ∧ ∀ A θσ : ℝ, 0 < θσ → ∃ (r K e0 : ℝ) (p : ℕ), 0 < r ∧
      ∀ eps, e0 ≤ eps → ∀ ν σ : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
        SigmaLaw A θσ σ → ∀ G : ℝ → ℝ, Measurable G →
          (∀ y, 0 ≤ y → |G y| ≤ Real.exp (γ * y / eps ^ 2)) →
          ∃ B : ℕ → ℝ, Summable B ∧ ∑' k, B k ≤ K * eps ^ p ∧
            ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ k, ‖cSurv eps ν σ z k G‖ ≤ B k

end

end PGM
