import PLAStochastic.Index.CEPS.Scaled.ComplexJetPolynomialBudget
import PLAStochastic.Index.CEPS.Scaled.ComplexJetRootHomogeneity
import PLAStochastic.ForMathlib.Analysis.Complex.QuadraticNewtonBudget

/-! # Uniform finite Newton stability from explicit coordinate and quadratic-root budgets -/

noncomputable section
open Complex
namespace PGM

def cepsFiniteRootErrorConstant (A c L : ℝ) : ℝ := 1 + 2 * (8 * A ^ 3 * L + 1) / c

def cepsFiniteRootScaleRadius (A c L V : ℝ) : ℝ :=
  min (1 / (2 * A)) (min (A / cepsFiniteRootErrorConstant A c L)
    (c / (1 + V * cepsFiniteRootErrorConstant A c L)))

theorem cepsFiniteRootErrorConstant_pos {A c L : ℝ} (hA : 0 < A) (hc : 0 < c)
    (hL : 0 ≤ L) : 0 < cepsFiniteRootErrorConstant A c L := by
  unfold cepsFiniteRootErrorConstant
  positivity

theorem cepsFiniteRootScaleRadius_admissible {A c L V : ℝ}
    (hA : 0 < A) (hc : 0 < c) (hL : 0 ≤ L) (hV : 0 ≤ V) :
    0 < cepsFiniteRootScaleRadius A c L V ∧
    2 * A * cepsFiniteRootScaleRadius A c L V ≤ 1 ∧
    cepsFiniteRootErrorConstant A c L * cepsFiniteRootScaleRadius A c L V ≤ A ∧
    (V / 2 * (cepsFiniteRootErrorConstant A c L) ^ 2 *
      cepsFiniteRootScaleRadius A c L V + 8 * A ^ 3 * L + 1) / c ≤
        cepsFiniteRootErrorConstant A c L := by
  let K := cepsFiniteRootErrorConstant A c L
  let δ := cepsFiniteRootScaleRadius A c L V
  have hK : 0 < K := cepsFiniteRootErrorConstant_pos hA hc hL
  have hden : 0 < 1 + V * K := by positivity
  have hδ : 0 < δ := by dsimp [δ, cepsFiniteRootScaleRadius]; positivity
  have hδA : δ ≤ 1 / (2 * A) := min_le_left _ _
  have hδK : δ ≤ A / K := (min_le_right _ _).trans (min_le_left _ _)
  have hδV : δ ≤ c / (1 + V * K) := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : 2 * A * δ ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * A)).mp hδA
    nlinarith
  have hKA : K * δ ≤ A := by
    have hh := (le_div_iff₀ hK).mp hδK
    nlinarith
  have hVK : V * K * δ ≤ c := by
    have hh := (le_div_iff₀ hden).mp hδV
    nlinarith
  have hC : 8 * A ^ 3 * L + 1 ≤ c * K / 2 := by
    dsimp [K, cepsFiniteRootErrorConstant]
    field_simp
    nlinarith
  have hterm : V / 2 * K ^ 2 * δ ≤ c * K / 2 := by
    have hh := mul_le_mul_of_nonneg_right hVK (hK.le : 0 ≤ K)
    nlinarith
  refine ⟨hδ, hsmall, hKA, ?_⟩
  rw [div_le_iff₀ hc]
  nlinarith

/-- Every finite Newton iteration stays in the same coefficient-only scale disc. The
base-root and gap budgets can be supplied uniformly on a complex variance box. -/
theorem cepsComplexCumulantRootModel_stability {p : ℕ → ℂ} (N : ℕ)
    {M A c F : ℝ} (hM : 0 ≤ M) (hA : 0 < A) (hc : 0 < c) (hF : 0 < F)
    (hp : ∀ j ≤ N, ‖p (cepsJetCode (.inl j))‖ ≤ M)
    (hv : p (cepsJetCode (.inl 0)) ≠ 0) (lam : ℝ) (z sign : ℂ)
    (hsign : sign ^ 2 = 1) (hl : ‖(lam : ℂ)‖ ≤ F) (hz : ‖z‖ ≤ F ^ 2)
    (hr : ‖cepsComplexCumulantRootBase p lam z sign‖ ≤ A * F)
    (hgap : c * F ≤ ‖cepsComplexCumulantRootGap p lam z sign‖)
    {b : ℂ} (hb : ‖b‖ * F ≤ cepsFiniteRootScaleRadius A c ((N : ℝ) * M) M) (k : ℕ) :
    ‖cepsComplexCumulantRootModel p N lam z sign k b -
      cepsComplexCumulantRootBase p lam z sign‖ ≤
        cepsFiniteRootErrorConstant A c ((N : ℝ) * M) * ‖b‖ * F ^ 2 ∧
    ‖cepsComplexCumulantRootModel p N lam z sign k b‖ ≤ 2 * A * F := by
  let L := (N : ℝ) * M
  let K := cepsFiniteRootErrorConstant A c L
  let δ := cepsFiniteRootScaleRadius A c L M
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 < K := cepsFiniteRootErrorConstant_pos hA hc hL
  obtain ⟨hδ, hsmall, hKA, hstable⟩ := cepsFiniteRootScaleRadius_admissible hA hc hL hM
  have hstableV : (‖p (cepsJetCode (.inl 0))‖ / 2 * K ^ 2 * δ + 8 * A ^ 3 * L + 1) / c ≤ K := by
    apply le_trans _ hstable
    gcongr
    exact hp 0 (Nat.zero_le N)
  have hbase := cepsComplexCumulantRootBase_quadratic_equation p lam z sign hv hsign
  have hbound (k : ℕ)
      (he : ‖cepsComplexCumulantRootModel p N lam z sign k b -
          cepsComplexCumulantRootBase p lam z sign‖ ≤ K * ‖b‖ * F ^ 2) :
      ‖cepsComplexCumulantRootModel p N lam z sign k b‖ ≤ 2 * A * F := by
    have ht := norm_add_le (cepsComplexCumulantRootModel p N lam z sign k b -
      cepsComplexCumulantRootBase p lam z sign) (cepsComplexCumulantRootBase p lam z sign)
    rw [sub_add_cancel] at ht
    have he' : K * ‖b‖ * F ^ 2 ≤ A * F := by
      calc
        _ = K * (‖b‖ * F) * F := by ring
        _ ≤ K * δ * F := by gcongr
        _ ≤ A * F := mul_le_mul_of_nonneg_right hKA hF.le
    exact ht.trans ((add_le_add (he.trans he') hr).trans_eq (by ring))
  induction k with
  | zero =>
    have he : ‖cepsComplexCumulantRootModel p N lam z sign 0 b -
        cepsComplexCumulantRootBase p lam z sign‖ ≤ K * ‖b‖ * F ^ 2 := by
      simp only [cepsComplexCumulantRootModel, sub_self, norm_zero]
      positivity
    exact ⟨he, hbound 0 he⟩
  | succ k ih =>
    have hs : ‖b * cepsComplexCumulantRootModel p N lam z sign k b‖ ≤ 1 := by
      rw [norm_mul]
      calc
        _ ≤ ‖b‖ * (2 * A * F) := mul_le_mul_of_nonneg_left ih.2 (norm_nonneg _)
        _ = 2 * A * (‖b‖ * F) := by ring
        _ ≤ 2 * A * δ := mul_le_mul_of_nonneg_left hb (by positivity)
        _ ≤ 1 := hsmall
    have hP : ‖cepsCgfComplexJetPolynomial p N (b * cepsComplexCumulantRootModel p N lam z sign k b) -
        p (cepsJetCode (.inl 0)) / 2‖ ≤
          L * ‖b‖ * ‖cepsComplexCumulantRootModel p N lam z sign k b‖ := by
      simpa only [L, norm_mul, mul_assoc] using cepsCgfComplexJetPolynomial_sub_variance_norm_le N hM hp hs
    have he := quadraticNewtonStep_scaled_error_le hA hc hL hK.le hδ.le hF hb hKA
      hstableV hr hl hz (rfl : cepsComplexCumulantRootGap p lam z sign =
        (lam : ℂ) + p (cepsJetCode (.inl 0)) * cepsComplexCumulantRootBase p lam z sign)
      hgap hbase ih.1 hP
    exact ⟨he, hbound (k + 1) he⟩

end PGM
