import Mathlib.Analysis.Calculus.FDeriv.Partial

/-! # Product differentiability with one continuous partial

Only the first partial must exist nearby and be jointly continuous at the
point. Differentiability of the second slice at that point is sufficient.
-/

noncomputable section
open Filter Asymptotics Set
open scoped Topology
namespace PGM

private theorem parameter_difference_littleO
    {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E}
    {v w : α → E} {l : Filter α} (hv : Tendsto v l (𝓝 u)) (hw : Tendsto w l (𝓝 u))
    {f : α → E → F} {f' : α → E → E →L[ℝ] F}
    (df' : ∀ᶠ p in l ×ˢ 𝓝 u, HasFDerivAt (f p.1) (f' p.1 p.2) p.2)
    {φ : E →L[ℝ] F} (cf' : Tendsto (fun p : α × E => f' p.1 p.2) (l ×ˢ 𝓝 u) (𝓝 φ)) :
    (fun χ => f χ (v χ) - f χ (w χ) - φ (v χ - w χ)) =o[l] (fun χ => v χ - w χ) := by
  rw [isLittleO_iff]
  intro ε hε
  have hd : ∀ᶠ χ in l, ∀ z ∈ segment ℝ (w χ) (v χ),
      HasFDerivWithinAt (f χ) (f' χ z) Set.univ z := by
    have h := df'.mono (fun _ h => h.hasFDerivWithinAt (s := Set.univ))
    have h' : ∀ᶠ p in l ×ˢ 𝓝[Set.univ] u, HasFDerivWithinAt (f p.1) (f' p.1 p.2) Set.univ p.2 :=
      by simpa only [nhdsWithin_univ] using h
    exact h'.segment_of_prod_nhdsWithin hw hv (by simp)
  have hc : ∀ᶠ χ in l, ∀ z ∈ segment ℝ (w χ) (v χ), ‖f' χ z - φ‖ < ε := by
    simp_rw [Metric.tendsto_nhds, dist_eq_norm_sub] at cf'
    have h' : ∀ᶠ p in l ×ˢ 𝓝[Set.univ] u, ‖f' p.1 p.2 - φ‖ < ε :=
      by simpa only [nhdsWithin_univ] using cf' ε hε
    exact h'.segment_of_prod_nhdsWithin hw hv (by simp)
  filter_upwards [hd, hc] with χ hd hc
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (hd z hz).mono (Set.subset_univ _)) (fun z hz => (hc z hz).le)
    (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)

set_option maxHeartbeats 800000 in
theorem hasFDerivAt_uncurry_of_continuous_fst
    {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E₁ × E₂} {f : E₁ → E₂ → F} {f₁ : E₁ → E₂ → E₁ →L[ℝ] F}
    {f₂ : E₂ →L[ℝ] F}
    (df₁ : ∀ᶠ v in 𝓝 u, HasFDerivAt (fun x => f x v.2) (f₁ v.1 v.2) v.1)
    (cf₁ : ContinuousAt (fun v : E₁ × E₂ => f₁ v.1 v.2) u)
    (df₂ : HasFDerivAt (f u.1) f₂ u.2) :
    HasFDerivAt (fun v : E₁ × E₂ => f v.1 v.2) ((f₁ u.1 u.2).coprod f₂) u := by
  have hmap : Tendsto (fun p : (E₁ × E₂) × E₁ => (p.2, p.1.2))
      (𝓝 u ×ˢ 𝓝 u.1) (𝓝 u) := by
    have h1 : Tendsto (fun p : (E₁ × E₂) × E₁ => p.2) (𝓝 u ×ˢ 𝓝 u.1) (𝓝 u.1) := tendsto_snd
    have h2 : Tendsto (fun p : (E₁ × E₂) × E₁ => p.1.2) (𝓝 u ×ˢ 𝓝 u.1) (𝓝 u.2) :=
      (continuousAt_snd (p := u)).tendsto.comp tendsto_fst
    have he : 𝓝 u = 𝓝 u.1 ×ˢ 𝓝 u.2 := by cases u; exact nhds_prod_eq
    exact (h1.prodMk h2).mono_right he.ge
  have hfirst : (fun v : E₁ × E₂ =>
      f v.1 v.2 - f u.1 v.2 - f₁ u.1 u.2 (v.1 - u.1)) =o[𝓝 u] (fun v => v.1 - u.1) := by
    apply parameter_difference_littleO (f := fun v x => f x v.2)
      (f' := fun v x => f₁ x v.2) continuousAt_fst.tendsto tendsto_const_nhds
    · exact hmap.eventually df₁
    · exact cf₁.tendsto.comp hmap
  have hO : (fun v : E₁ × E₂ => v.1 - u.1) =O[𝓝 u] (fun v => v - u) :=
    isBigO_of_le _ (fun v => norm_fst_le (v - u))
  have hsecond := df₂.comp u (hasFDerivAt_snd (𝕜 := ℝ) (p := u))
  rw [hasFDerivAt_iff_isLittleO] at hsecond ⊢
  convert (hfirst.trans_isBigO hO).add hsecond using 1
  ext v
  change f v.1 v.2 - f u.1 u.2 - (f₁ u.1 u.2 (v.1 - u.1) + f₂ (v.2 - u.2)) =
    (f v.1 v.2 - f u.1 v.2 - f₁ u.1 u.2 (v.1 - u.1)) +
      (f u.1 v.2 - f u.1 u.2 - f₂ (v.2 - u.2))
  abel

end PGM
