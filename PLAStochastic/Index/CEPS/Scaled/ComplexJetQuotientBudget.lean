import PLAStochastic.Index.CEPS.Scaled.ComplexJetQuotientCompact
import PLAStochastic.Index.CEPS.Scaled.ComplexJetQuotientHomogeneity
import PLAStochastic.Index.CEPS.Scaled.ComplexJetQuadraticBudget

/-! # Uniform finite complex input-vector budgets for the actual spatial quotient -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsComplexJetPad_norm_le {d : ℕ} {p : Fin d → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hp : ‖p‖ ≤ M) (i : ℕ) : ‖cepsComplexJetPad d p i‖ ≤ M := by
  by_cases hi : i < d
  · rw [cepsComplexJetPad_apply p hi]
    exact (norm_le_pi_norm p ⟨i, hi⟩).trans hp
  · simp only [cepsComplexJetPad, dif_neg hi, norm_zero]
    exact hM

/-- The original finite quotient is uniformly close to half the input variance on one
scale radius proportional to the inverse drift-frequency weight. The finite vector need
not arise from a density; all marker/root collisions and the joint origin are included. -/
theorem cepsComplexCumulantJetQuotient_uniform_budget (d N : ℕ) {M vlo vhi S ε : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ (lam : ℝ) (z b ξ : ℂ), 0 ≤ z.re →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ‖ξ‖ ≤ S * (1 + |lam| + Real.sqrt ‖z‖) →
        ‖cepsComplexCumulantJetQuotient (cepsComplexJetPad d p) N lam z b ξ -
          cepsComplexJetPad d p (cepsJetCode (.inl 0)) / 2‖ ≤ ε := by
  let A := cepsFiniteQuadraticRootBound vlo
  let c := cepsFiniteQuadraticGapLower vlo vhi
  let L := max M (max 1 (max (2 * A) S))
  have hA : 0 < A := cepsFiniteQuadraticRootBound_pos hlo
  have hc : 0 < c := cepsFiniteQuadraticGapLower_pos hlo
  let δroot := cepsFiniteRootScaleRadius A c ((N : ℝ) * M) M
  have hδroot : 0 < δroot :=
    (cepsFiniteRootScaleRadius_admissible hA hc (mul_nonneg (Nat.cast_nonneg N) hM) hM).1
  obtain ⟨δq, hδq, hQ⟩ := cepsFiniteQuotientAt_uniform_zero_budget d N L hε
  refine ⟨min δroot δq, lt_min hδroot hδq, ?_⟩
  intro p hp hv hhi lam z b ξ hz hb hξ
  let P := cepsComplexJetPad d p
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + F
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hX : 0 < X := by dsimp [X]; linarith
  have hXF : F ≤ X := by dsimp [X]; linarith
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hXn : ‖(X : ℂ)‖ = X := by rw [norm_real, Real.norm_eq_abs, abs_of_pos hX]
  have hbX : ‖b‖ * X ≤ min δroot δq := by
    simpa only [X, F, add_assoc] using hb
  have hbF : ‖b‖ * F ≤ δroot :=
    (mul_le_mul_of_nonneg_left hXF (norm_nonneg b)).trans (hbX.trans (min_le_left _ _))
  have hpκ : ∀ j ≤ N, ‖P (cepsJetCode (.inl j))‖ ≤ M :=
    fun j _ => cepsComplexJetPad_norm_le hM hp _
  have hRplus := (cepsComplexCumulantRootModel_right_stability N hM hlo hpκ hv hhi lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hbF N).2
  have hRminus := (cepsComplexCumulantRootModel_right_stability N hM hlo hpκ hv hhi lam hz
    (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1) hbF N).2
  let a := cepsComplexCumulantRootModel P N lam z 1 N b / (X : ℂ)
  let e := cepsComplexCumulantRootModel P N lam z (-1) N b / (X : ℂ)
  let t := ξ / (X : ℂ)
  have ha : ‖a‖ ≤ 2 * A := by
    dsimp [a]
    rw [norm_div, hXn, div_le_iff₀ hX]
    exact hRplus.trans (mul_le_mul_of_nonneg_left hXF (by positivity))
  have he : ‖e‖ ≤ 2 * A := by
    dsimp [e]
    rw [norm_div, hXn, div_le_iff₀ hX]
    exact hRminus.trans (mul_le_mul_of_nonneg_left hXF (by positivity))
  have ht : ‖t‖ ≤ S := by
    dsimp [t]
    rw [norm_div, hXn, div_le_iff₀ hX]
    simpa only [X, F, add_assoc] using hξ
  have hl : ‖lam / X‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hX, div_le_one hX]
    exact (le_add_of_nonneg_right (Real.sqrt_nonneg ‖z‖)).trans hXF
  have hzF : ‖z‖ ≤ F ^ 2 := by
    calc
      _ = Real.sqrt ‖z‖ ^ 2 := (Real.sq_sqrt (norm_nonneg z)).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_add_of_nonneg_left (abs_nonneg lam)) 2
  have hzX : ‖z / (X : ℂ) ^ 2‖ ≤ (1 : ℝ) := by
    rw [norm_div, norm_pow, hXn, div_le_one (pow_pos hX 2)]
    exact hzF.trans (pow_le_pow_left₀ hF hXF 2)
  let u : CepsFiniteQuotientParams d := (p, lam / X, z / (X : ℂ) ^ 2, a, e, t)
  have hu : ‖u‖ ≤ L := by
    have hML : M ≤ L := le_max_left _ _
    have h1L : 1 ≤ L := (le_max_left _ _).trans (le_max_right _ _)
    have hAL : 2 * A ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    have hSL : S ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    dsimp only [u]
    simp only [Prod.norm_def, max_le_iff]
    exact ⟨hp.trans hML, hl.trans h1L, hzX.trans h1L, ha.trans hAL, he.trans hAL, ht.trans hSL⟩
  have hbq : ‖(X : ℂ) * b‖ ≤ δq := by
    rw [norm_mul, hXn, mul_comm]
    exact hbX.trans (min_le_right _ _)
  have hbudget := hQ ((X : ℂ) * b) u hbq hu
  have hLam : X * (lam / X) = lam := mul_div_cancel₀ lam hX.ne'
  have hZ : (X : ℂ) ^ 2 * (z / (X : ℂ) ^ 2) = z := mul_div_cancel₀ z (pow_ne_zero 2 hXc)
  have hnode (w : ℂ) : (X : ℂ) * (w / (X : ℂ)) = w := mul_div_cancel₀ w hXc
  have hscale := cepsComplexCumulantQuotientSpatialUnit_second_slope_homogeneous P N
    (lam / X) (z / (X : ℂ) ^ 2) b a e t hX
  rw [hLam, hZ] at hscale
  dsimp only [a, e, t] at hscale
  rw [hnode, hnode, hnode] at hscale
  change ‖cepsComplexCumulantJetQuotient P N lam z b ξ - P (cepsJetCode (.inl 0)) / 2‖ ≤ ε
  change ‖dslope (dslope (cepsComplexCumulantQuotientSpatialUnit P N lam z b)
    (cepsComplexCumulantRootModel P N lam z 1 N b))
      (cepsComplexCumulantRootModel P N lam z (-1) N b) ξ - P (cepsJetCode (.inl 0)) / 2‖ ≤ ε
  rw [hscale]
  exact hbudget

theorem cepsComplexCumulantJetQuotient_uniform_nonzero_budget (d N : ℕ)
    {M vlo vhi S : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ (lam : ℝ) (z b ξ : ℂ), 0 ≤ z.re →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ‖ξ‖ ≤ S * (1 + |lam| + Real.sqrt ‖z‖) →
        vlo / 4 ≤ ‖cepsComplexCumulantJetQuotient (cepsComplexJetPad d p) N lam z b ξ‖ ∧
        ‖cepsComplexCumulantJetQuotient (cepsComplexJetPad d p) N lam z b ξ‖ ≤ vhi / 2 + vlo / 4 ∧
        cepsComplexCumulantJetQuotient (cepsComplexJetPad d p) N lam z b ξ ≠ 0 := by
  obtain ⟨δ, hδ, hQ⟩ := cepsComplexCumulantJetQuotient_uniform_budget d N
    (M := M) (vhi := vhi) (S := S) hM hlo (by positivity : 0 < vlo / 4)
  refine ⟨δ, hδ, ?_⟩
  intro p hp hv hhi lam z b ξ hz hb hξ
  let V := cepsComplexJetPad d p (cepsJetCode (.inl 0))
  let Q := cepsComplexCumulantJetQuotient (cepsComplexJetPad d p) N lam z b ξ
  have he : ‖Q - V / 2‖ ≤ vlo / 4 := hQ p hp hv hhi lam z b ξ hz hb hξ
  have hvn : vlo ≤ ‖V‖ := hv.trans (re_le_norm _)
  have hlow : vlo / 4 ≤ ‖Q‖ := by
    have hh := norm_sub_norm_le (V / 2) Q
    rw [norm_sub_rev, norm_div, norm_ofNat] at hh
    linarith
  have hupp : ‖Q‖ ≤ vhi / 2 + vlo / 4 := by
    have hh := norm_add_le (Q - V / 2) (V / 2)
    rw [sub_add_cancel, norm_div, norm_ofNat] at hh
    linarith
  exact ⟨hlow, hupp, norm_pos_iff.mp ((by positivity : 0 < vlo / 4).trans_le hlow)⟩

end PGM
