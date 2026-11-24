import PLAStochastic.Index.KEP.Poisson.CompletedStopping
import PLAStochastic.Index.KEP.CompletedPivotRestart

/-!
# All successive Poisson restarts from the actual leading stopping law

At a finite completed pivot, the fresh physical sequence has precisely the
state-dependent original law. Almost sure finiteness of the leading block
at every physical anchor therefore proves finiteness of every successive
completed pivot. Higher-layer finiteness is not assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepPoissonPivot_succ_of_finite_restarts {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {eps n x : ℝ} {ell i r s : ℕ}
    {g : ℕ → ℝ} (hr : kepPoissonPivot hf eps n x ell i g = r)
    (hs : kepPoissonPivot hf eps n (kepPoissonKeys hf n x g r) ell 1
      (fun k => g (r + k)) = s) :
    kepPoissonPivot hf eps n x ell (i + 1) g = (r + s : ℕ) := by
  have hs' : completedPivot eps (fun k => kepPoissonPairs hf n x g (r + k)) ell 1 = s := by
    rw [← kepPoissonPairs_shift]
    exact hs
  exact completedPivot_succ_of_finite_restarts (fun _ => rfl) hr hs'

theorem kepPoissonPivot_all_finite_of_leading {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n : ℝ) (ell : ℕ)
    (hfin : ∀ x : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x ell 1 g ≠ ⊤) :
    ∀ x : ℝ, ∀ i : ℕ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x ell i g ≠ ⊤ := by
  intro x i
  induction i with
  | zero =>
    exact Filter.Eventually.of_forall fun g => by
      simp only [kepPoissonPivot, completedPivot_zero]
      exact ENat.natCast_ne_top 0
  | succ i hi =>
    let tau := kepPoissonPivot hf eps n x ell i
    let D := kepPoissonStoppedAnchor hf n x tau
    have htau : IsStoppingRule tau := isStoppingRule_kepPoissonPivot hf eps n x ell i
    have hD : Measurable D := measurable_kepPoissonStoppedAnchor hf n x htau
    let mu := expSeqMeasure.map D
    let : IsProbabilityMeasure mu := Measure.isProbabilityMeasure_map hD.aemeasurable
    have hset : MeasurableSet {p : ℝ × (ℕ → ℝ) |
        kepPoissonPivot hf eps n p.1 ell 1 p.2 ≠ ⊤} :=
      ((measurable_kepPoissonPivot hf eps n ell 1) (measurableSet_singleton ⊤)).compl
    have hprod : ∀ᵐ p ∂mu.prod expSeqMeasure,
        kepPoissonPivot hf eps n p.1 ell 1 p.2 ≠ ⊤ :=
      (Measure.ae_prod_iff_ae_ae hset).mpr (Filter.Eventually.of_forall hfin)
    have hjoint := kepPoisson_restart_joint hf n x htau hi
    have hnext : ∀ᵐ g ∂expSeqMeasure,
        kepPoissonPivot hf eps n (D g) ell 1 (shiftBy tau g) ≠ ⊤ := by
      rw [← hjoint] at hprod
      exact (ae_map_iff (hD.prodMk (measurable_shiftBy htau)).aemeasurable hset).mp hprod
    filter_upwards [hi, hnext] with g hg hn
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hg
    have hr' : tau g = (r : ℕ∞) := hr.symm
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hn
    have hs' : kepPoissonPivot hf eps n (kepPoissonKeys hf n x g r) ell 1
        (fun k => g (r + k)) = (s : ℕ∞) := by
      have hs0 : kepPoissonPivot hf eps n (D g) ell 1 (shiftBy tau g) = (s : ℕ∞) := hs.symm
      have hshift : shiftBy tau g = fun k => g (r + k) := by
        funext k
        change g ((tau g).toNat + k) = g (r + k)
        rw [hr', ENat.toNat_natCast]
      simpa only [D, kepPoissonStoppedAnchor, hr', ENat.toNat_natCast, hshift] using hs0
    rw [kepPoissonPivot_succ_of_finite_restarts hf hr' hs']
    exact ENat.natCast_ne_top (r + s)

end

end PGM
