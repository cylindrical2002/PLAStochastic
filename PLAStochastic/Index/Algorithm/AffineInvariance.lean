import PLAStochastic.Index.Algorithm.RankHierarchy
import PLAStochastic.Index.Algorithm.EndpointHierarchy

/-!
# Affine invariance of the endpoint and rank-equispaced hierarchies

ALG-OPT only reads feasibility of windows, which is invariant under every nonzero
affine change of the keys.  Hence the whole ALG-PGM and ALG-RE hierarchies, and in
particular both heights, are unchanged by `p ↦ s p + c` with `s ≠ 0`.
-/

namespace PGM

theorem epLayer_affine {eps : ℝ} {p : ℕ → ℝ} {s c : ℝ} (hs : s ≠ 0) (n : ℕ) :
    ∀ ℓ, epLayer eps (fun i => s * p i + c) n ℓ =
      ((fun j => s * (epLayer eps p n ℓ).1 j + c), (epLayer eps p n ℓ).2)
  | 0 => rfl
  | ℓ + 1 => by
    have ih := epLayer_affine (eps := eps) (p := p) (c := c) hs n ℓ
    show ((fun j => (epLayer eps (fun i => s * p i + c) n ℓ).1
          (finCut eps (epLayer eps (fun i => s * p i + c) n ℓ).1
            (epLayer eps (fun i => s * p i + c) n ℓ).2 j)),
        finSegCount eps (epLayer eps (fun i => s * p i + c) n ℓ).1
          (epLayer eps (fun i => s * p i + c) n ℓ).2) = _
    rw [ih]
    simp only [finCut_affine hs, finSegCount_affine hs]
    rfl

theorem epHeight_affine {eps : ℝ} {p : ℕ → ℝ} {s c : ℝ} (hs : s ≠ 0) (n : ℕ) :
    epHeight eps (fun i => s * p i + c) n = epHeight eps p n := by
  unfold epHeight
  simp only [epLayer_affine hs]

theorem reLayer_affine {eps : ℝ} {p : ℕ → ℝ} {s c : ℝ} (hs : s ≠ 0) (n : ℕ) :
    ∀ ℓ, reLayer eps (fun i => s * p i + c) n ℓ = reLayer eps p n ℓ
  | 0 => rfl
  | ℓ + 1 => by
    have ih := reLayer_affine (eps := eps) (p := p) (c := c) hs n ℓ
    simp only [reLayer, ih]
    rw [finSegCount_affine (P := fun j => p (j * (reLayer eps p n ℓ).1)) hs]

theorem reHeight_affine {eps : ℝ} {p : ℕ → ℝ} {s c : ℝ} (hs : s ≠ 0) (n : ℕ) :
    reHeight eps (fun i => s * p i + c) n = reHeight eps p n := by
  unfold reHeight
  simp only [reLayer_affine hs]

end PGM
