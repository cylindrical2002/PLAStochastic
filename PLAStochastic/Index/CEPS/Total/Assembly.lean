import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# WP10: the algebra of the S-9 assembly (C20)

Pure bookkeeping, independent of the CEPS objects. With the exact representation
`E = φ^{m+1} - d ∫_{(-1,∞)} J` (theorem (E)), the outer tails (S-7: the positive side against the
drawup occupation `F`, `d F = 1 - G`, and the negative side), the drawup approximation (S-8,
`G ≈ A_δ`), the pair approximation on `[-δ, δ]` (S-6, `J ≈ Ĵ`) and the half-line primitive
(P12) `d ∫_{[b,δ]} J^∞ = A_δ - A_b`, the actual transform is the normal transform

  `Ĝ = A_b - d ∫_{[-δ,δ]} (Ĵ - 1_{μ ≥ b} J^∞)`

up to `‖d‖ (e₁ + e₂ + 2δ e₄) + e₃`: the upper endpoint `A_δ` of the primitive cancels the drawup
main term.
-/

noncomputable section
open MeasureTheory Set

namespace PGM

/-- **S-9, algebra.** -/
theorem norm_assembly_sub_le {J Jn Jinf : ℝ → ℂ} {φ E F G Aδ Ab : ℂ} {m : ℕ}
    {δ b e₁ e₂ e₃ e₄ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hb : 0 < b)
    (hE : E = φ ^ (m + 1) - (1 - φ) * ∫ μ in Ioi (-1 : ℝ), J μ)
    (hJ : IntegrableOn J (Ioi (-1 : ℝ)))
    (hpos : ‖(∑ k ∈ Finset.range (m + 1), φ ^ k) + (∫ μ in Ici δ, J μ) - F‖ ≤ e₁)
    (hneg : ‖∫ μ in Ioo (-1 : ℝ) (-δ), J μ‖ ≤ e₂)
    (hF : (1 - φ) * F = 1 - G) (hG : ‖G - Aδ‖ ≤ e₃)
    (hpair : ∀ μ ∈ Icc (-δ) δ, ‖J μ - Jn μ‖ ≤ e₄) (hJn : IntegrableOn Jn (Icc (-δ) δ))
    (hJinf : IntegrableOn Jinf (Icc b δ))
    (hftc : (1 - φ) * ∫ μ in Icc b δ, Jinf μ = Aδ - Ab) :
    ‖E - (Ab - (1 - φ) * ∫ μ in Icc (-δ) δ, (Jn μ - (Ici b).indicator Jinf μ))‖ ≤
      ‖1 - φ‖ * (e₁ + e₂ + 2 * δ * e₄) + e₃ := by
  set d := 1 - φ
  -- split `(-1, ∞)`
  have hsplit : Ioi (-1 : ℝ) = (Ioo (-1) (-δ) ∪ Icc (-δ) δ) ∪ Ioi δ := by
    ext x; simp only [mem_Ioi, mem_union, mem_Ioo, mem_Icc]
    constructor
    · intro hx
      by_cases h1 : x < -δ
      · exact Or.inl (Or.inl ⟨hx, h1⟩)
      · by_cases h2 : x ≤ δ
        · exact Or.inl (Or.inr ⟨le_of_not_gt h1, h2⟩)
        · exact Or.inr (lt_of_not_ge h2)
    · rintro ((⟨h1, -⟩ | ⟨h1, -⟩) | h1) <;> linarith
  have hJ1 : IntegrableOn J (Ioo (-1) (-δ)) := hJ.mono_set (fun x hx => by
    simp only [mem_Ioi, mem_Ioo] at hx ⊢; exact hx.1)
  have hJ2 : IntegrableOn J (Icc (-δ) δ) := hJ.mono_set (fun x hx => by
    simp only [mem_Ioi, mem_Icc] at hx ⊢; linarith [hx.1])
  have hJ3 : IntegrableOn J (Ioi δ) := hJ.mono_set (fun x hx => by
    simp only [mem_Ioi] at hx ⊢; linarith)
  have hd12 : Disjoint (Ioo (-1 : ℝ) (-δ)) (Icc (-δ) δ) := by
    rw [Set.disjoint_left]; intro x h1 h2; simp only [mem_Ioo, mem_Icc] at h1 h2; linarith
  have hd3 : Disjoint (Ioo (-1 : ℝ) (-δ) ∪ Icc (-δ) δ) (Ioi δ) := by
    rw [Set.disjoint_left]; intro x h1 h2
    simp only [mem_union, mem_Ioo, mem_Icc, mem_Ioi] at h1 h2
    rcases h1 with h | h <;> linarith [h.2]
  have hI : ∫ μ in Ioi (-1 : ℝ), J μ = (∫ μ in Ioo (-1) (-δ), J μ) +
      (∫ μ in Icc (-δ) δ, J μ) + ∫ μ in Ici δ, J μ := by
    rw [hsplit, setIntegral_union hd3 measurableSet_Ioi (hJ1.union hJ2) hJ3,
      setIntegral_union hd12 measurableSet_Icc hJ1 hJ2, integral_Ici_eq_integral_Ioi]
  -- the geometric sum
  have hgeom : φ ^ (m + 1) = 1 - d * ∑ k ∈ Finset.range (m + 1), φ ^ k := by
    have := mul_neg_geom_sum φ (m + 1)
    simp only [d]; linear_combination this
  -- the pair on `[-δ, δ]`
  have hvol : (volume : Measure ℝ).real (Icc (-δ) δ) = 2 * δ := by
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
  have hdiff : ‖∫ μ in Icc (-δ) δ, (J μ - Jn μ)‖ ≤ e₄ * (2 * δ) := by
    rw [← hvol]
    exact norm_setIntegral_le_of_norm_le_const (by simp [Real.volume_Icc]) hpair
  have hsub : ∫ μ in Icc (-δ) δ, J μ = (∫ μ in Icc (-δ) δ, (J μ - Jn μ)) +
      ∫ μ in Icc (-δ) δ, Jn μ := by
    have h := integral_add (μ := volume.restrict (Icc (-δ) δ)) (hJ2.sub hJn) hJn
    simp only [Pi.sub_apply, sub_add_cancel] at h
    exact h
  -- the half-line subtraction
  have he : Ici b ∩ Icc (-δ) δ = Icc b δ := by
    ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
  have hind : IntegrableOn ((Ici b).indicator Jinf) (Icc (-δ) δ) := by
    refine (integrable_indicator_iff measurableSet_Ici).mpr ?_
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ici, he]
    exact hJinf
  have hhalf : ∫ μ in Icc (-δ) δ, (Ici b).indicator Jinf μ = ∫ μ in Icc b δ, Jinf μ := by
    rw [setIntegral_indicator measurableSet_Ici, inter_comm, he]
  have hsplit2 : ∫ μ in Icc (-δ) δ, Jn μ = (∫ μ in Icc (-δ) δ, (Jn μ - (Ici b).indicator Jinf μ)) +
      ∫ μ in Icc b δ, Jinf μ := by
    have h := integral_add (μ := volume.restrict (Icc (-δ) δ)) (hJn.sub hind) hind
    simp only [Pi.sub_apply, sub_add_cancel] at h
    rw [h, hhalf]
  -- assemble
  set S := ∑ k ∈ Finset.range (m + 1), φ ^ k
  set I₁ := ∫ μ in Ioo (-1 : ℝ) (-δ), J μ
  set I₃ := ∫ μ in Ici δ, J μ
  set R := ∫ μ in Icc (-δ) δ, (J μ - Jn μ)
  set K := ∫ μ in Icc (-δ) δ, (Jn μ - (Ici b).indicator Jinf μ)
  set P := ∫ μ in Icc b δ, Jinf μ
  have hkey : E - (Ab - d * K) = (G - Aδ) - d * (S + I₃ - F) - d * I₁ - d * R := by
    rw [hE, hI, hsub, hsplit2, hgeom]
    linear_combination (-1 : ℂ) * hF - hftc
  rw [hkey]
  have hd0 : 0 ≤ ‖d‖ := norm_nonneg _
  calc ‖(G - Aδ) - d * (S + I₃ - F) - d * I₁ - d * R‖
      ≤ ‖G - Aδ‖ + ‖d * (S + I₃ - F)‖ + ‖d * I₁‖ + ‖d * R‖ := by
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl
    _ ≤ e₃ + ‖d‖ * e₁ + ‖d‖ * e₂ + ‖d‖ * (e₄ * (2 * δ)) := by
        rw [norm_mul, norm_mul, norm_mul]
        gcongr
    _ = ‖d‖ * (e₁ + e₂ + 2 * δ * e₄) + e₃ := by ring

end PGM
