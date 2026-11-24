import PLAStochastic.Index.KEP.Poisson.ArrivalWindowLaw
import PLAStochastic.Index.KEP.Poisson.ModelKCoordinates
import PLAStochastic.Index.KEP.Poisson.FiniteHeightReadout
import PLAStochastic.Index.GEP.RawDisc.Telescoping

/-!
# The actual Poisson window height is the completed leading-block event

The integrated-intensity window coordinates give exactly the original
quantile keys up to the window count. Finite-prefix height therefore reads
the completed original leading pivot, without a future-finiteness input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Renyi
open scoped ENNReal unitInterval Nat

theorem kepArrivalWindowCoordinates_key {s M p : ℝ} (hM : 0 < M) (hp : 0 < p)
    (hs : s = M * p) (g : ℕ → ℝ) (N t : ℕ) (ht0 : 0 < t) (htN : t ≤ N) :
    padPos (padScale p (kepArrivalWindowCoordinates s N g)) t = gapKeys g t / M := by
  unfold padPos padScale padFin kepArrivalWindowCoordinates
  rw [if_neg ht0.ne', dif_pos (show t - 1 < N by omega)]
  simp only [Nat.sub_add_cancel ht0]
  rw [hs]
  field_simp

theorem kepPoissonWindow_keys_prefix {f : ℝ → ℝ} {A B flo fhi L M u p : ℝ}
    (hf : DensityK f A B flo fhi L) (hM : 0 < M)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hp : 0 < p) (hp1 : p ≤ 1)
    {g : ℕ → ℝ} (hg : ∀ i, 0 ≤ g i)
    (hcount : g ∈ kepArrivalCountEvent (M * p) (kepArrivalCount (M * p) g)) :
    ∀ t ≤ kepArrivalCount (M * p) g,
      winKeys (quantK f A B) u (kepArrivalWindowConfiguration (M * p) p g).2 t =
        kepPoissonKeys (kepExtendedDensity_profile hf) (M / (1 - u)) (quantK f A B u) g t := by
  intro t ht
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · simp [winKeys, padPos, kepPoissonKeys, gapKeys, kepPoissonArrival_zero]
  have hkey := kepArrivalWindowCoordinates_key hM hp rfl g
    (kepArrivalCount (M * p) g) t ht0 ht
  have hgt : gapKeys g t ≤ M * p := by
    simpa only [Nat.sub_add_cancel ht0] using
      hcount.1 ⟨t - 1, by omega⟩
  have hw : gapKeys g t / M ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (gapKeys_nonneg hg t) hM.le, ?_⟩
    rw [div_le_one hM]
    exact hgt.trans (by nlinarith)
  change quantK f A B (u + (1 - u) *
    padPos (padScale p (kepArrivalWindowCoordinates (M * p) (kepArrivalCount (M * p) g) g)) t) =
      kepPoissonArrival (kepExtendedDensity_profile hf) (M / (1 - u)) (quantK f A B u)
        (gapKeys g t)
  rw [hkey]
  have he := kepPoissonArrival_modelK_window hf hM hu0 hu1 hw
  have hmul : M * (gapKeys g t / M) = gapKeys g t := by field_simp
  rw [hmul] at he
  exact he.symm

theorem kepPoissonWindow_tailEvent_iff {f : ℝ → ℝ} {A B flo fhi L M u p eps : ℝ}
    (hf : DensityK f A B flo fhi L) (hM : 0 < M)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hp : 0 < p) (hp1 : p ≤ 1)
    (heps : 1 / 2 ≤ eps) {ell : ℕ} (hell : 1 ≤ ell)
    {g : ℕ → ℝ} (hg : ∀ i, 0 ≤ g i)
    (hcount : g ∈ kepArrivalCountEvent (M * p) (kepArrivalCount (M * p) g)) :
    kepArrivalWindowConfiguration (M * p) p g ∈ tailEvent eps (quantK f A B) u ell ↔
      ((kepArrivalCount (M * p) g : ℕ) : ℕ∞) <
        kepPoissonPivot (kepExtendedDensity_profile hf) eps (M / (1 - u)) (quantK f A B u) ell 1 g := by
  change epHeight eps (winKeys (quantK f A B) u
    (kepArrivalWindowConfiguration (M * p) p g).2) (kepArrivalCount (M * p) g + 1) ≤ ell ↔ _
  rw [epHeight_congr (p' := kepPoissonKeys (kepExtendedDensity_profile hf)
      (M / (1 - u)) (quantK f A B u) g)
    (fun t ht => kepPoissonWindow_keys_prefix hf hM hu0 hu1 hp hp1 hg hcount t (by omega))]
  exact kepPoisson_height_le_iff_completedPivot (kepExtendedDensity_profile hf) heps
    (M / (1 - u)) (quantK f A B u) g (kepArrivalCount (M * p) g) hell

end

end PGM
