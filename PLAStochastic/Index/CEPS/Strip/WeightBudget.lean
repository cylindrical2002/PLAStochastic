import PLAStochastic.Index.CEPS.Strip.RootAdmissible
import PLAStochastic.Index.CEPS.Scaled.ComplexJetWeightSpatial
import PLAStochastic.Index.CEPS.Scaled.ComplexJetRootKernelBudget

/-! # Quotient, canonical weight and spatial-kernel budgets on admissible frequencies

These are the admissible-frequency forms of `ComplexJetQuotientBudget`,
`ComplexJetWeightBudget`, `ComplexJetWeightSpatial` and `ComplexJetRootKernelBudget`.
The radii are chosen before the finite vector, the drift and the frequency.
-/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsComplexCumulantJetQuotient_uniform_budget_adm (d N : ℕ) {M vlo vhi S ε : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ∀ (lam : ℝ) (z b ξ : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
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
  intro p hp hv lam z b ξ hz hb hξ
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
  have hRplus := (cepsComplexCumulantRootModel_stability_adm N hM hlo hpκ hv lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hbF N).2
  have hRminus := (cepsComplexCumulantRootModel_stability_adm N hM hlo hpκ hv lam hz
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

theorem cepsComplexCumulantJetQuotient_uniform_nonzero_budget_adm (d N : ℕ)
    {M vlo vhi S : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ (lam : ℝ) (z b ξ : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ‖ξ‖ ≤ S * (1 + |lam| + Real.sqrt ‖z‖) →
        vlo / 4 ≤ ‖cepsComplexCumulantJetQuotient (cepsComplexJetPad d p) N lam z b ξ‖ ∧
        ‖cepsComplexCumulantJetQuotient (cepsComplexJetPad d p) N lam z b ξ‖ ≤ vhi / 2 + vlo / 4 ∧
        cepsComplexCumulantJetQuotient (cepsComplexJetPad d p) N lam z b ξ ≠ 0 := by
  obtain ⟨δ, hδ, hQ⟩ := cepsComplexCumulantJetQuotient_uniform_budget_adm d N
    (M := M) (vhi := vhi) (S := S) hM hlo (by positivity : 0 < vlo / 4)
  refine ⟨δ, hδ, ?_⟩
  intro p hp hv hhi lam z b ξ hz hb hξ
  let V := cepsComplexJetPad d p (cepsJetCode (.inl 0))
  let Q := cepsComplexCumulantJetQuotient (cepsComplexJetPad d p) N lam z b ξ
  have he : ‖Q - V / 2‖ ≤ vlo / 4 := hQ p hp hv lam z b ξ hz hb hξ
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

theorem cepsComplexKernelJetWeight_uniform_zero_budget_adm (d N : ℕ) {M vlo vhi S ε : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ∀ (lam : ℝ) (z b ξ : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ‖ξ‖ ≤ S * (1 + |lam| + Real.sqrt ‖z‖) →
        ‖cepsComplexKernelJetWeight (cepsComplexJetPad d p) N lam z b ξ -
          cepsFiniteKernelWeightZero d p‖ ≤ ε := by
  let A := cepsFiniteQuadraticRootBound vlo
  let c := cepsFiniteQuadraticGapLower vlo vhi
  let L := max M (max 1 (max (2 * A) S))
  have hA : 0 < A := cepsFiniteQuadraticRootBound_pos hlo
  have hc : 0 < c := cepsFiniteQuadraticGapLower_pos hlo
  let δroot := cepsFiniteRootScaleRadius A c ((N : ℝ) * M) M
  have hδroot : 0 < δroot :=
    (cepsFiniteRootScaleRadius_admissible hA hc (mul_nonneg (Nat.cast_nonneg N) hM) hM).1
  obtain ⟨δw, hδw, hW⟩ := cepsFiniteKernelWeightAt_uniform_zero_budget d N L hε
  refine ⟨min δroot δw, lt_min hδroot hδw, ?_⟩
  intro p hp hv lam z b ξ hz hb hξ
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hXF : F ≤ X := by dsimp [F, X]; linarith
  have hX : 0 < X := by dsimp [X]; positivity
  have hXn : ‖(X : ℂ)‖ = X := by rw [norm_real, Real.norm_eq_abs, abs_of_pos hX]
  have hbF : ‖b‖ * F ≤ δroot :=
    (mul_le_mul_of_nonneg_left hXF (norm_nonneg b)).trans (hb.trans (min_le_left _ _))
  have hpκ : ∀ j ≤ N, ‖cepsComplexJetPad d p (cepsJetCode (.inl j))‖ ≤ M :=
    fun j _ => cepsComplexJetPad_norm_le hM hp _
  have hplus := (cepsComplexCumulantRootModel_stability_adm N hM hlo hpκ hv lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hbF N).2.trans
      (mul_le_mul_of_nonneg_left hXF (by positivity : 0 ≤ 2 * A))
  have hminus := (cepsComplexCumulantRootModel_stability_adm N hM hlo hpκ hv lam hz
    (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1) hbF N).2.trans
      (mul_le_mul_of_nonneg_left hXF (by positivity : 0 ≤ 2 * A))
  obtain ⟨u, hup, hu, hue⟩ := cepsComplexKernelJetWeight_normalization d N p hp lam z b ξ hplus hminus hξ
  have hbW : ‖(X : ℂ) * b‖ ≤ δw := by
    rw [norm_mul, hXn, mul_comm]
    exact hb.trans (min_le_right _ _)
  have hh := hW ((X : ℂ) * b) u hbW hu
  rw [hup, hue] at hh
  exact hh

theorem cepsComplexKernelJetWeight_uniform_nonzero_budget_adm (d N : ℕ)
    {M vlo vhi S : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ (lam : ℝ) (z b ξ : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ‖ξ‖ ≤ S * (1 + |lam| + Real.sqrt ‖z‖) →
        vlo / 4 * Real.exp (-2 * M) ≤ ‖cepsComplexKernelJetWeight (cepsComplexJetPad d p) N lam z b ξ‖ ∧
        ‖cepsComplexKernelJetWeight (cepsComplexJetPad d p) N lam z b ξ‖ ≤
          vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M) ∧
        cepsComplexKernelJetWeight (cepsComplexJetPad d p) N lam z b ξ ≠ 0 := by
  obtain ⟨δ, hδ, hW⟩ := cepsComplexKernelJetWeight_uniform_zero_budget_adm d N
    (M := M) (vhi := vhi) (S := S) hM hlo (by positivity : 0 < vlo / 4 * Real.exp (-2 * M))
  refine ⟨δ, hδ, ?_⟩
  intro p hp hv hhi lam z b ξ hz hb hξ
  let W := cepsComplexKernelJetWeight (cepsComplexJetPad d p) N lam z b ξ
  let W₀ := cepsFiniteKernelWeightZero d p
  have he : ‖W - W₀‖ ≤ vlo / 4 * Real.exp (-2 * M) := hW p hp hv lam z b ξ hz hb hξ
  have hbase := cepsFiniteKernelWeightZero_norm_budget hM hp hv hlo.le hhi
  have hlow : vlo / 4 * Real.exp (-2 * M) ≤ ‖W‖ := by
    have hh := norm_sub_norm_le W₀ W
    rw [norm_sub_rev] at hh
    linarith [hbase.1]
  have hupp : ‖W‖ ≤ vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M) := by
    have hh := norm_add_le (W - W₀) W₀
    rw [sub_add_cancel] at hh
    linarith [hbase.2]
  exact ⟨hlow, hupp, norm_pos_iff.mp ((by positivity : 0 < vlo / 4 * Real.exp (-2 * M)).trans_le hlow)⟩

theorem cepsComplexKernelJetWeight_root_slope_uniform_budget_adm (d N : ℕ) {M vlo vhi ε : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ∀ (lam : ℝ) (z b : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ‖dslope (cepsComplexKernelJetWeight (cepsComplexJetPad d p) N lam z b)
          (cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z (-1) N b)
          (cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z 1 N b)‖ ≤
          4 * ε / (cepsFiniteWeightSpatialWindow vlo * (1 + |lam| + Real.sqrt ‖z‖)) := by
  let A := cepsFiniteQuadraticRootBound vlo
  let c := cepsFiniteQuadraticGapLower vlo vhi
  let S := cepsFiniteWeightSpatialWindow vlo
  have hA : 0 < A := cepsFiniteQuadraticRootBound_pos hlo
  have hc : 0 < c := cepsFiniteQuadraticGapLower_pos hlo
  have hS : 0 < S := cepsFiniteWeightSpatialWindow_pos hlo
  let δroot := cepsFiniteRootScaleRadius A c ((N : ℝ) * M) M
  have hδroot : 0 < δroot :=
    (cepsFiniteRootScaleRadius_admissible hA hc (mul_nonneg (Nat.cast_nonneg N) hM) hM).1
  obtain ⟨δw, hδw, hW⟩ := cepsComplexKernelJetWeight_uniform_zero_budget_adm d N
    (M := M) (vhi := vhi) (S := S) hM hlo hε
  refine ⟨min δroot δw, lt_min hδroot hδw, ?_⟩
  intro p hp hv lam z b hz hb
  let P := cepsComplexJetPad d p
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let R := S * X
  let W := cepsComplexKernelJetWeight P N lam z b
  let W₀ := cepsFiniteKernelWeightZero d p
  let a := cepsComplexCumulantRootModel P N lam z (-1) N b
  let t := cepsComplexCumulantRootModel P N lam z 1 N b
  have hXF : F ≤ X := by dsimp [F, X]; linarith
  have hX : 0 < X := by dsimp [X]; positivity
  have hR : 0 < R := mul_pos hS hX
  have hbF : ‖b‖ * F ≤ δroot :=
    (mul_le_mul_of_nonneg_left hXF (norm_nonneg b)).trans (hb.trans (min_le_left _ _))
  have hpκ : ∀ j ≤ N, ‖P (cepsJetCode (.inl j))‖ ≤ M :=
    fun j _ => cepsComplexJetPad_norm_le hM hp _
  have ha : ‖a‖ ≤ 2 * A * F := (cepsComplexCumulantRootModel_stability_adm N hM hlo hpκ hv lam hz
    (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1) hbF N).2
  have ht : ‖t‖ ≤ 2 * A * F := (cepsComplexCumulantRootModel_stability_adm N hM hlo hpκ hv lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hbF N).2
  have hnodes : 2 * A * F < R / 2 := by
    have hh := mul_le_mul_of_nonneg_left hXF (by positivity : 0 ≤ 2 * A)
    dsimp [R, S, cepsFiniteWeightSpatialWindow]
    nlinarith
  have hbound : ∀ ξ ∈ ball (0 : ℂ) R, ‖W ξ - W₀‖ ≤ ε := by
    intro ξ hξ
    exact hW p hp hv lam z b ξ hz (hb.trans (min_le_right _ _))
      (mem_ball_zero_iff.mp hξ).le
  have hd := cepsComplexKernelJetWeight_spatial_differentiable P N lam z b
  have hs := cepsNormal_norm_dslope_sub_le_of_bound hR hd.differentiableOn
    (differentiable_const W₀).differentiableOn hbound
    (mem_ball_zero_iff.mpr (ha.trans_lt hnodes)) (mem_ball_zero_iff.mpr (ht.trans_lt hnodes))
  have hconst : dslope (fun _ : ℂ => W₀) a t = 0 := by
    by_cases hta : t = a
    · rw [hta, dslope_same]
      exact deriv_const a W₀
    · rw [dslope_of_ne _ hta, slope_def_field, sub_self, zero_div]
  rw [hconst, sub_zero] at hs
  exact hs

theorem cepsComplexKernelGJetModel_root_uniform_budget_adm (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ (lam : ℝ) (z b : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ∀ (sign : ℂ), sign = 1 ∨ sign = -1 → ∀ k : ℕ,
          let r := cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z sign k b
          vlo / 4 * Real.exp (-2 * M) * Real.exp (-(r * (1 + b * lam)).re) ≤
            ‖cepsComplexKernelGJetModel (cepsComplexJetPad d p) N lam z b r‖ ∧
          ‖cepsComplexKernelGJetModel (cepsComplexJetPad d p) N lam z b r‖ ≤
            (vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M)) *
              Real.exp (-(r * (1 + b * lam)).re) ∧
          cepsComplexKernelGJetModel (cepsComplexJetPad d p) N lam z b r ≠ 0 := by
  let A := cepsFiniteQuadraticRootBound vlo
  let c := cepsFiniteQuadraticGapLower vlo vhi
  have hA : 0 < A := cepsFiniteQuadraticRootBound_pos hlo
  have hc : 0 < c := cepsFiniteQuadraticGapLower_pos hlo
  let δroot := cepsFiniteRootScaleRadius A c ((N : ℝ) * M) M
  have hδroot : 0 < δroot :=
    (cepsFiniteRootScaleRadius_admissible hA hc (mul_nonneg (Nat.cast_nonneg N) hM) hM).1
  obtain ⟨δw, hδw, hW⟩ := cepsComplexKernelJetWeight_uniform_nonzero_budget_adm d N
    (M := M) (vhi := vhi) (S := 2 * A) hM hlo
  refine ⟨min δroot δw, lt_min hδroot hδw, ?_⟩
  intro p hp hv hhi lam z b hz hb sign hsign k
  let P := cepsComplexJetPad d p
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let r := cepsComplexCumulantRootModel P N lam z sign k b
  have hFX : F ≤ X := by dsimp [F, X]; linarith
  have hbF : ‖b‖ * F ≤ δroot :=
    (mul_le_mul_of_nonneg_left hFX (norm_nonneg b)).trans (hb.trans (min_le_left _ _))
  have hpκ : ∀ j ≤ N, ‖P (cepsJetCode (.inl j))‖ ≤ M :=
    fun j _ => cepsComplexJetPad_norm_le hM hp _
  have hr : ‖r‖ ≤ 2 * A * X := (cepsComplexCumulantRootModel_stability_adm N hM hlo hpκ hv lam hz
    hsign hbF k).2.trans (mul_le_mul_of_nonneg_left hFX (by positivity))
  have hw := hW p hp hv hhi lam z b r hz (hb.trans (min_le_right _ _)) hr
  change _ ∧ _ ∧ cepsComplexKernelGJetModel P N lam z b r ≠ 0
  have hn : ‖cepsComplexKernelGJetModel P N lam z b r‖ =
      Real.exp (-(r * (1 + b * lam)).re) * ‖cepsComplexKernelJetWeight P N lam z b r‖ := by
    rw [cepsComplexKernelGJetModel_eq_weight, norm_mul, norm_exp, neg_mul, neg_re]
  refine ⟨?_, ?_, ?_⟩
  · rw [hn]
    calc
      _ ≤ ‖cepsComplexKernelJetWeight P N lam z b r‖ * Real.exp (-(r * (1 + b * lam)).re) :=
        mul_le_mul_of_nonneg_right hw.1 (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  · rw [hn]
    calc
      _ = ‖cepsComplexKernelJetWeight P N lam z b r‖ * Real.exp (-(r * (1 + b * lam)).re) := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hw.2.1 (Real.exp_pos _).le
  · rw [cepsComplexKernelGJetModel_eq_weight]
    exact mul_ne_zero (exp_ne_zero _) hw.2.2

end PGM
