import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Complex.Basic

/-! # Finite coordinate expansion of multilinear Taylor terms -/

noncomputable section
open Finset
namespace PGM

/-- Every diagonal multilinear Taylor term expands in the finite coordinate basis. -/
theorem multilinear_diagonal_eq_sum_coordinates {d n : ℕ}
    (P : ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin d → ℂ) ℂ) (x : Fin d → ℂ) :
    P (fun _ => x) = ∑ w : Fin n → Fin d,
      (∏ k : Fin n, x (w k)) * P (fun k => Pi.single (w k) (1 : ℂ)) := by
  classical
  have hx : x = ∑ i : Fin d, x i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Pi.single_apply]
  calc
    P (fun _ => x) = P.toMultilinearMap
        (fun _ => ∑ i : Fin d, x i • Pi.single i (1 : ℂ)) :=
      congrArg P (funext fun _ => hx)
    _ = ∑ w : Fin n → Fin d, P (fun k => x (w k) • Pi.single (w k) (1 : ℂ)) :=
      P.toMultilinearMap.map_sum (fun _ i => x i • Pi.single i (1 : ℂ))
    _ = _ := by
      apply sum_congr rfl
      intro w _
      simpa only [smul_eq_mul] using P.map_smul_univ (fun k => x (w k))
        (fun k => Pi.single (w k) (1 : ℂ))

/-- Multiplicities of the coordinates in a Taylor word. -/
def finiteTaylorWordCounts {d n : ℕ} (w : Fin n → Fin d) (i : Fin d) : ℕ :=
  (univ.filter fun k => w k = i).card

theorem finiteTaylorWordCounts_le {d n : ℕ} (w : Fin n → Fin d) (i : Fin d) :
    finiteTaylorWordCounts w i ≤ n := by
  simpa only [finiteTaylorWordCounts, card_univ, Fintype.card_fin] using
    card_le_card (filter_subset (fun k => w k = i) univ)

theorem finiteTaylorWordCounts_degree {d n : ℕ} (w : Fin n → Fin d) :
    ∑ i, finiteTaylorWordCounts w i = n := by
  have h := Finset.sum_fiberwise (s := (univ : Finset (Fin n))) w (fun _ => (1 : ℕ))
  simpa [finiteTaylorWordCounts] using h

theorem prod_coordinates_eq_monomial {d n : ℕ} (w : Fin n → Fin d) (x : Fin d → ℂ) :
    (∏ k, x (w k)) = ∏ i, x i ^ finiteTaylorWordCounts w i := by
  have h := Finset.prod_fiberwise' (s := (univ : Finset (Fin n))) w x
  simpa only [prod_const, finiteTaylorWordCounts] using h.symm

/-- Fixed monomial coefficients extracted from a genuine multilinear Taylor series. -/
def finiteCoordinateTaylorCoeff {d : ℕ}
    (p : FormalMultilinearSeries ℂ (Fin d → ℂ) ℂ) (α : Fin d → ℕ) : ℂ :=
  ∑ w : Fin (∑ i, α i) → Fin d with finiteTaylorWordCounts w = α,
    p (∑ i, α i) (fun k => Pi.single (w k) (1 : ℂ))

/-- Rectangular finite coordinate support. -/
def finiteCoordinateTaylorBox (d N : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun _ => range (N + 1)

/-- A homogeneous multilinear Taylor term has exactly the fixed coordinate coefficients
of its total degree. The rectangular support introduces only zero coefficients here. -/
theorem multilinear_diagonal_eq_coordinate_box {d : ℕ}
    (p : FormalMultilinearSeries ℂ (Fin d → ℂ) ℂ) (n : ℕ) (x : Fin d → ℂ) :
    p n (fun _ => x) = ∑ α ∈ finiteCoordinateTaylorBox d n,
      if (∑ i, α i) = n then finiteCoordinateTaylorCoeff p α * (∏ i, x i ^ α i) else 0 := by
  classical
  rw [multilinear_diagonal_eq_sum_coordinates]
  have hmap : ∀ w ∈ (univ : Finset (Fin n → Fin d)),
      finiteTaylorWordCounts w ∈ finiteCoordinateTaylorBox d n := by
    intro w _
    simp only [finiteCoordinateTaylorBox, Fintype.mem_piFinset, mem_range]
    exact fun i => Nat.lt_succ_of_le (finiteTaylorWordCounts_le w i)
  rw [← sum_fiberwise_of_maps_to hmap]
  apply sum_congr rfl
  intro α _
  by_cases hα : (∑ i, α i) = n
  · simp only [if_pos hα]
    have hT : finiteCoordinateTaylorCoeff p α =
        ∑ w : Fin n → Fin d with finiteTaylorWordCounts w = α,
          p n (fun k => Pi.single (w k) (1 : ℂ)) := by
      subst n
      rfl
    rw [hT, sum_mul]
    apply sum_congr rfl
    intro w hw
    rw [prod_coordinates_eq_monomial, (mem_filter.mp hw).2]
    ring
  · simp only [if_neg hα]
    apply sum_eq_zero
    intro w hw
    have hwα := (mem_filter.mp hw).2
    have hd := finiteTaylorWordCounts_degree w
    rw [hwα] at hd
    exact False.elim (hα hd)

end PGM
