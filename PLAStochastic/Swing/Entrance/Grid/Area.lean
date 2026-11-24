import PLAStochastic.Swing.Entrance.Grid.Limit
import PLAStochastic.Swing.Entrance.Grid.RiemannSum

/-!
# The reflected grid area at the cut, (E20)

On the rescaled grid path `y = E f(· h_E)` the reflected area at index `n` is exactly
`s_E (h ∑_{k ≤ n} t_k f(t_k) - (E β) h ∑_{k ≤ n} t_k²)` with `t_k = k h`, `h = E^{-2}`. At the
cut both sums are right-endpoint Riemann sums over `[0, τ h] → [0, σ]`, while `E β → m_*` and
`s_E = s` eventually, so the grid area converges to the Brownian area
`I = s ∫_0^σ t (f t - m_* t) dt` for every entrance-regular path.
-/

open MeasureTheory BrownianAffine Filter Finset
open scoped NNReal ENNReal Topology

namespace SwingRepair

noncomputable section

/-- The reflected grid area of the grid path as a pair of Riemann sums. -/
theorem entranceGridArea_gridPath_eq {f : ℝ → ℝ} {E : ℝ≥0} (hE : E ≠ 0) (n : ℕ) :
    entranceGridArea (entranceGridPath f E) E n =
      entranceSide (entranceGridPath f E) E n *
        ((gaussianBudgetMesh E : ℝ) * ∑ k ∈ Icc 1 n,
            ((k : ℝ) * gaussianBudgetMesh E) * f ((k : ℝ) * gaussianBudgetMesh E) -
          ((E : ℝ) * entranceFrozenSlope (entranceGridPath f E) E n) *
            ((gaussianBudgetMesh E : ℝ) * ∑ k ∈ Icc 1 n, ((k : ℝ) * gaussianBudgetMesh E) ^ 2)) := by
  set s := entranceSide (entranceGridPath f E) E n
  set β := entranceFrozenSlope (entranceGridPath f E) E n
  have hE' : (E : ℝ) ≠ 0 := by exact_mod_cast hE
  have hterm : ∀ k ∈ Icc 1 n,
      (E : ℝ)⁻¹ ^ 5 * ((k : ℝ) * (s * entranceGridPath f E k - s * β * k)) =
        s * ((gaussianBudgetMesh E : ℝ) *
            (((k : ℝ) * gaussianBudgetMesh E) * f ((k : ℝ) * gaussianBudgetMesh E)) -
          ((E : ℝ) * β) * ((gaussianBudgetMesh E : ℝ) * ((k : ℝ) * gaussianBudgetMesh E) ^ 2)) := by
    intro k _
    unfold entranceGridPath
    generalize f ((k : ℝ) * (gaussianBudgetMesh E : ℝ)) = u
    rw [coe_gaussianBudgetMesh]
    field_simp
  calc entranceGridArea (entranceGridPath f E) E n
      = ∑ k ∈ Icc 1 n, (E : ℝ)⁻¹ ^ 5 *
          ((k : ℝ) * (s * entranceGridPath f E k - s * β * k)) := by
        unfold entranceGridArea
        rw [mul_sum]
    _ = ∑ k ∈ Icc 1 n, s * ((gaussianBudgetMesh E : ℝ) *
            (((k : ℝ) * gaussianBudgetMesh E) * f ((k : ℝ) * gaussianBudgetMesh E)) -
          ((E : ℝ) * β) * ((gaussianBudgetMesh E : ℝ) * ((k : ℝ) * gaussianBudgetMesh E) ^ 2)) :=
        sum_congr rfl hterm
    _ = _ := by
        simp only [mul_sum, ← sum_sub_distrib]

section Grid

variable {f : C(ℝ, ℝ)} {σ : ℝ≥0} (hr : EntranceRegular f σ)
  {ι : Type*} {l : Filter ι} {E : ι → ℝ≥0} (hE1 : ∀ i, 1 ≤ E i)
  (hE : Tendsto (fun i => (E i : ℝ)) l atTop)
include hr hE1 hE

/-- (E20): the reflected grid area at the cut converges to the Brownian signed area `I`. -/
theorem tendsto_entranceGridArea :
    Tendsto (fun i => entranceGridArea (entranceGridPath f (E i)) (E i)
      (entranceCut (entranceGridPath f (E i)) (E i)).toNat) l (𝓝 (entranceArea f)) := by
  have hτ := tendsto_cut_mul_mesh hr hE1 hE
  have hmesh := gaussianBudgetMesh_tendsto hE
  have hpos : ∀ᶠ i in l, 0 < (gaussianBudgetMesh (E i) : ℝ) :=
    Eventually.of_forall fun i => gaussianBudgetMesh_pos (ne_zero_of_one_le_nnreal (hE1 i))
  have hA := tendsto_riemannSum (g := fun t => t * f t) (continuous_id.mul f.continuous)
    hpos hmesh hτ
  have hB := tendsto_riemannSum (g := fun t => t ^ 2) (continuous_pow 2) hpos hmesh hτ
  rw [integral_pow] at hB
  have hB' : Tendsto (fun i => (gaussianBudgetMesh (E i) : ℝ) *
      ∑ k ∈ Icc 1 (entranceCut (entranceGridPath f (E i)) (E i)).toNat,
        ((k : ℝ) * gaussianBudgetMesh (E i)) ^ 2) l (𝓝 ((σ : ℝ) ^ 3 / 3)) := by
    convert hB using 2
    norm_num
  rw [hr.area_eq]
  apply (((hA.sub ((tendsto_mul_entranceFrozenSlope hr hE1 hE).mul hB')).const_mul
    (entranceSign f))).congr'
  filter_upwards [eventually_entranceSide_eq hr hE1 hE] with i hs
  rw [entranceGridArea_gridPath_eq (ne_zero_of_one_le_nnreal (hE1 i)), hs]

end Grid

end

end SwingRepair
