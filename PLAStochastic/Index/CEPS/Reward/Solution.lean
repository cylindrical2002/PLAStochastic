import PLAStochastic.Index.CEPS.Reward.Conv

/-! # Solving the half-line renewal equation

The explicit solution is unique among measurable functions supported on
the nonnegative half-line and bounded on every finite interval.
-/

noncomputable section
open MeasureTheory Set
namespace PGM.WienerHopf

def rewardSolution (g b : ℝ → ℂ) : ℝ → ℂ :=
  halfLine b + convC (renewalDensity g) (halfLine b)

variable {g b : ℝ → ℂ} {D θ : ℝ}

theorem halfBdd_rewardSolution (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ)
    (hb : HalfBdd (halfLine b)) : HalfBdd (rewardSolution g b) :=
  hb.add ((halfBdd_renewalDensity hg hθ).convC hb)

theorem convC_add_left {f h k : ℝ → ℂ} (hf : HalfBdd f) (hh : HalfBdd h)
    (hk : HalfBdd k) (x : ℝ) : convC (f + h) k x = convC f k x + convC h k x := by
  rw [convC_comm, convC_add_right hk hf hh, convC_comm k f, convC_comm k h]

theorem rewardSolution_eq_add_convC (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ)
    (hb : HalfBdd (halfLine b)) {x : ℝ} (hx : 0 ≤ x) :
    rewardSolution g b x = b x + convC g (rewardSolution g b) x := by
  have hg' := hg.halfBdd hθ
  have hu := halfBdd_renewalDensity hg hθ
  have he : renewalDensity g = g + convC g (renewalDensity g) := by
    funext y
    exact renewalDensity_eq_add_convC hg hθ y
  have hconv : convC (renewalDensity g) (halfLine b) x =
      convC g (halfLine b) x + convC (convC g (renewalDensity g)) (halfLine b) x := by
    calc
      _ = convC (g + convC g (renewalDensity g)) (halfLine b) x :=
        congrArg (fun f => convC f (halfLine b) x) he
      _ = _ := convC_add_left hg' (hg'.convC hu) hb x
  change halfLine b x + convC (renewalDensity g) (halfLine b) x =
    b x + convC g (halfLine b + convC (renewalDensity g) (halfLine b)) x
  rw [halfLine_of_nonneg b hx, convC_add_right hg' hb (hu.convC hb),
    convC_assoc hg' hu hb, hconv]

/-- Uniqueness consumes an independently established renewal equation. -/
theorem eq_rewardSolution_of_renewal (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ)
    (hb : HalfBdd (halfLine b)) {R : ℝ → ℂ} (hR : HalfBdd R)
    (heq : ∀ x, 0 ≤ x → R x = b x + convC g R x) : R = rewardSolution g b := by
  have hF := halfBdd_rewardSolution hg hθ hb
  have hδ := hR.sub hF
  have hz := eq_zero_of_eq_convC hg hθ hδ (fun x hx => by
    change R x - rewardSolution g b x = convC g (R - rewardSolution g b) x
    rw [convC_sub_right (hg.halfBdd hθ) hR hF x, heq x hx,
      rewardSolution_eq_add_convC hg hθ hb hx]
    ring)
  funext x
  exact sub_eq_zero.mp (hz x)

end PGM.WienerHopf
