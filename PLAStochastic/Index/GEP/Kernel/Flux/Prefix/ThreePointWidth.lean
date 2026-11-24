import PLAStochastic.Index.GEP.SurvivalBound.Certificate.Geometry
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# WP4: exact three-point boundary geometry

This file proves the algebra and differential factors in
`research/2026-09-28-gep-closure/input-flux-kernel.md`, §§1–2.  The three points are
`(0,0)`, `(A,L)` and `(A+B,L+M)`, with positive physical lengths `A,B`.
The exact optimal half-width is `|L*B-M*A| / (2*(A+B))`.

The results here are finite-dimensional geometry. They do not assert the coarea
formula, uniqueness of the active facet, or an a.e. derivative of `lawJC`.
-/

namespace PGM

noncomputable section

open Filter Topology

/-- The signed three-point half-width. -/
def fluxSignedWidth (L M A B : ℝ) : ℝ := (L * B - M * A) / (2 * (A + B))

/-- The exact three-point optimal half-width. -/
def fluxWidth (L M A B : ℝ) : ℝ := |fluxSignedWidth L M A B|

/-- Feasibility of the three points, using their actual ranks and key spacings. -/
def fluxTripleFeasible (eps L M A B : ℝ) : Prop :=
  ∃ a b : ℝ, |b| ≤ eps ∧ |L - (a * A + b)| ≤ eps ∧
    |L + M - (a * (A + B) + b)| ≤ eps

/-- The chord slope of the two outside points. -/
def fluxSlope (L M A B : ℝ) : ℝ := (L + M) / (A + B)

theorem fluxWidth_eq (L M A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    fluxWidth L M A B = |L * B - M * A| / (2 * (A + B)) := by
  rw [fluxWidth, fluxSignedWidth, abs_div, abs_of_pos (by positivity : 0 < 2 * (A + B))]

theorem flux_chord_residuals {L M A B : ℝ} (h : A + B ≠ 0) :
    L - (fluxSlope L M A B * A + fluxSignedWidth L M A B) = fluxSignedWidth L M A B ∧
    L + M - (fluxSlope L M A B * (A + B) + fluxSignedWidth L M A B) =
      -fluxSignedWidth L M A B := by
  unfold fluxSlope fluxSignedWidth
  constructor <;> field_simp <;> ring

/-- The exact optimal half-width, with no regularity hypothesis on a gap law. -/
theorem fluxTripleFeasible_iff {eps L M A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    fluxTripleFeasible eps L M A B ↔ fluxWidth L M A B ≤ eps := by
  rw [fluxWidth_eq L M A B hA hB, div_le_iff₀ (by positivity : 0 < 2 * (A + B))]
  constructor
  · rintro ⟨a, b, hb, hmid, hend⟩
    obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
    obtain ⟨hm₁, hm₂⟩ := abs_le.mp hmid
    obtain ⟨he₁, he₂⟩ := abs_le.mp hend
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg hA.le (sub_nonneg.mpr he₂),
        mul_nonneg hB.le (sub_nonneg.mpr hb₂),
        mul_nonneg (add_pos hA hB).le (sub_nonneg.mpr hm₁)]
    · nlinarith [mul_nonneg hA.le (sub_nonneg.mpr he₁),
        mul_nonneg hB.le (sub_nonneg.mpr hb₁),
        mul_nonneg (add_pos hA hB).le (sub_nonneg.mpr hm₂)]
  · intro h
    have hw : |fluxSignedWidth L M A B| ≤ eps := by
      rw [fluxSignedWidth, abs_div, abs_of_pos (by positivity : 0 < 2 * (A + B)),
        div_le_iff₀ (by positivity : 0 < 2 * (A + B))]
      exact h
    obtain ⟨hm, he⟩ := flux_chord_residuals (L := L) (M := M) (add_pos hA hB).ne'
    refine ⟨fluxSlope L M A B, fluxSignedWidth L M A B, hw, ?_, ?_⟩
    · rwa [hm]
    · simpa only [he, abs_neg] using hw

/-- Every feasible prefix satisfies the exact three-point bound at each ordered triple. -/
theorem fluxWidth_le_of_prefix {eps : ℝ} {p : ℕ → ℝ} {k r s t : ℕ}
    (hf : prefixAffineFeasible eps p (k + 1)) (hr : r < s) (hs : s < t) (ht : t ≤ k)
    (hA : p r < p s) (hB : p s < p t) :
    fluxWidth ((s : ℝ) - r) ((t : ℝ) - s) (p s - p r) (p t - p s) ≤ eps := by
  apply (fluxTripleFeasible_iff (sub_pos.mpr hA) (sub_pos.mpr hB)).mp
  obtain ⟨a, b, h⟩ := hf
  refine ⟨a, a * p r + b - r, ?_, ?_, ?_⟩
  · have hh := h r (by omega)
    convert hh using 1
    rw [← abs_neg]
    congr 1
    ring
  · convert h s (by omega) using 1
    congr 1
    ring
  · convert h t (by omega) using 1
    congr 1
    ring

/-- An oriented boundary is a linear equation in the two physical block lengths. -/
theorem flux_boundary_linear {L M A B eps σ : ℝ} (h : A + B ≠ 0) :
    fluxSignedWidth L M A B = σ * eps ↔
      (L - 2 * σ * eps) * B = (M + 2 * σ * eps) * A := by
  rw [fluxSignedWidth, div_eq_iff (mul_ne_zero (by norm_num) h)]
  constructor <;> intro h' <;> nlinarith

/-- The two physical sums at a nonzero chord slope are exactly the (AB) parameters. -/
theorem flux_boundary_AB {L M A B eps σ : ℝ} (hS : A + B ≠ 0) (hLM : L + M ≠ 0)
    (hb : fluxSignedWidth L M A B = σ * eps) :
    A = (L - 2 * σ * eps) / fluxSlope L M A B ∧
    B = (M + 2 * σ * eps) / fluxSlope L M A B := by
  have he := (flux_boundary_linear hS).mp hb
  have ha : fluxSlope L M A B ≠ 0 := div_ne_zero hLM hS
  constructor <;> rw [eq_div_iff ha] <;> unfold fluxSlope
  · rw [← mul_div_assoc, div_eq_iff hS]
    nlinarith
  · rw [← mul_div_assoc, div_eq_iff hS]
    nlinarith

/-- Positive physical block lengths force both (AB) numerators to be positive. -/
theorem flux_boundary_numerators_pos {L M A B eps σ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hLM : 0 < L + M)
    (hb : fluxSignedWidth L M A B = σ * eps) :
    0 < L - 2 * σ * eps ∧ 0 < M + 2 * σ * eps := by
  have ha : 0 < fluxSlope L M A B := div_pos hLM (add_pos hA hB)
  obtain ⟨heA, heB⟩ := flux_boundary_AB (add_pos hA hB).ne' hLM.ne' hb
  constructor
  · have hh := (eq_div_iff ha.ne').mp heA
    rw [← hh]
    exact mul_pos hA ha
  · have hh := (eq_div_iff ha.ne').mp heB
    rw [← hh]
    exact mul_pos hB ha

/-- One of the two rank blocks on an oriented boundary is longer than `2 eps`. -/
theorem flux_boundary_long_block {L M A B eps σ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hLM : 0 < L + M) (hσ : σ = 1 ∨ σ = -1)
    (hb : fluxSignedWidth L M A B = σ * eps) : 2 * eps < L ∨ 2 * eps < M := by
  obtain ⟨hL, hM⟩ := flux_boundary_numerators_pos hA hB hLM hb
  rcases hσ with rfl | rfl
  · left
    linarith
  · right
    linarith

/-- The signed linear equation of a three-point facet. -/
def fluxFacet (L M eps σ A B : ℝ) : ℝ :=
  (L - 2 * σ * eps) * B - (M + 2 * σ * eps) * A

theorem flux_boundary_iff_facet {L M A B eps σ : ℝ} (h : A + B ≠ 0) :
    fluxSignedWidth L M A B = σ * eps ↔ fluxFacet L M eps σ A B = 0 := by
  rw [flux_boundary_linear h, fluxFacet, sub_eq_zero]

/-- The section constraint consists of two linear inequalities, including their signs. -/
theorem fluxWidth_le_iff_facets {L M A B eps : ℝ} (hA : 0 < A) (hB : 0 < B) :
    fluxWidth L M A B ≤ eps ↔
      fluxFacet L M eps 1 A B ≤ 0 ∧ 0 ≤ fluxFacet L M eps (-1) A B := by
  rw [fluxWidth_eq L M A B hA hB, div_le_iff₀ (by positivity : 0 < 2 * (A + B)), abs_le]
  unfold fluxFacet
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith

theorem fluxFacet_insert_left (L M eps σ A B x : ℝ) :
    fluxFacet L M eps σ (A + x) B =
      fluxFacet L M eps σ A B - (M + 2 * σ * eps) * x := by
  unfold fluxFacet
  ring

theorem fluxFacet_insert_right (L M eps σ A B x : ℝ) :
    fluxFacet L M eps σ A (B + x) =
      fluxFacet L M eps σ A B + (L - 2 * σ * eps) * x := by
  unfold fluxFacet
  ring

/-- A gap in the first block crosses the facet at a unique explicit point. -/
theorem fluxFacet_insert_left_eq_zero_iff {L M eps σ A B x : ℝ}
    (h : M + 2 * σ * eps ≠ 0) :
    fluxFacet L M eps σ (A + x) B = 0 ↔
      x = fluxFacet L M eps σ A B / (M + 2 * σ * eps) := by
  rw [fluxFacet_insert_left, eq_div_iff h]
  constructor <;> intro h' <;> nlinarith

/-- A gap in the second block crosses the facet at a unique explicit point. -/
theorem fluxFacet_insert_right_eq_zero_iff {L M eps σ A B x : ℝ}
    (h : L - 2 * σ * eps ≠ 0) :
    fluxFacet L M eps σ A (B + x) = 0 ↔
      x = -fluxFacet L M eps σ A B / (L - 2 * σ * eps) := by
  rw [fluxFacet_insert_right, eq_div_iff h]
  constructor <;> intro h' <;> nlinarith

end

end PGM
