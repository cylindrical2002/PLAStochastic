import PLAStochastic.Index.GEP.Kernel.Marked.Pin.Displacement

/-!
# All-time crossing suppression for an actual marked pair of pins

The designated step is retained in `kernelMarkedDens`. The other pin crosses
the same two endpoints, so its centered displacement bound supplies crossing
suppression at every time. Exact paired conjugacy removes the endpoint tilt
before taking any absolute bound. The deterministic insertion factor remains
explicit. No Green sum or regularity assumption is introduced here.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- A marked density with a genuine random left side costs at most the one-step
density bound. The left row's survival mass is retained until the last inequality. -/
theorem kernelFar_markedDens_le_div {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (β t : ℝ) {a : ℝ} (ha : a ≠ 0) {l : ℕ} (hl : 1 ≤ l) (r : ℕ) (y z : ℝ) :
    kernelMarkedDens J ν f β a t l r y z ≤ D / |a| := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  have hD0 : 0 ≤ D / |a| := div_nonneg ((hf0 0).trans (hfD 0)) (abs_nonneg _)
  have hI := (kr_integrable_krDens_right (β := β) (a := a) ν hJ hJfin hf hf0 hfD
    (k + 1) y).mul_const (D / |a|)
  have hb : kernelMarkedDens J ν f β a t (k + 1) r y z ≤
      ∫ u, krDens J ν f β a (k + 1) y u * (D / |a|) := by
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun u => mul_nonneg
        (krDens_nonneg ν hf0 _ _ _) (krDens_nonneg ν hf0 _ _ _)) hI
    exact Filter.Eventually.of_forall fun u => mul_le_mul_of_nonneg_left
      (krDens_le_div ν hf0 hfD r (u + β - a * t) z) (krDens_nonneg ν hf0 _ _ _)
  rw [integral_mul_const, integral_krDens ν hJ hJfin hf hf0 hfD hν ha] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_right (krSurv_le_one hJ ν β a (k + 1) y) hD0).trans_eq
    (one_mul _))

/-- A marked pin times the oppositely ordered ordinary pin has simultaneous
quadratic slope and Bernstein crossing suppression, for all three positive
random lengths. The insertion factor is exactly `lam*t-lam/a`; in particular
there is no artificial `exp (abs lam * width / a)` endpoint loss. -/
theorem kernel_regLaw_saddle_marked_pin_crossing (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ δ c d C : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < c ∧ 0 < d ∧ 0 < C ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ a : ℝ, |a - 1| ≤ δ → ∀ J : Set ℝ, MeasurableSet J → volume J ≠ ⊤ →
        ∀ t y z : ℝ, ∀ l r M : ℕ, 1 ≤ l → 1 ≤ r → 1 ≤ M →
          kernelMarkedDens J ν f 1 a t l r y z * krDens J ν f 1 a M z y ≤
            C * Real.exp (-c * ((l : ℝ) + r + M) * (a - 1) ^ 2 +
              kernelTiltSaddle D θ vlo ν a * t - kernelTiltSaddle D θ vlo ν a / a -
              d * min ((z - y) ^ 2 / (M : ℝ)) |z - y|) := by
  let D' := 2 * D * Real.exp θ
  let θ' := θ / 4
  let vlo' := 3 * vlo / 16
  let vhi' := 5 * vhi
  have hD' : 0 < D' := by positivity
  have hθ' : 0 < θ' := by positivity
  have hvlo' : 0 < vlo' := by positivity
  have hv' : vlo' ≤ vhi' := by dsimp [vlo', vhi']; linarith
  obtain ⟨d, hd, hdisp⟩ := kernel_regLaw_displacement D' θ' vlo' vhi' hD' hθ' hvlo' hv'
  obtain ⟨δ, c, hδ, hδhi, hc, hdata⟩ := kernel_regLaw_saddle_scaled D θ vlo vhi hD hθ hvlo hv
  refine ⟨δ, c, d, D' * (D' * Real.exp θ'), hδ, hδhi, hc, hd, by positivity, ?_⟩
  intro ν hν
  obtain ⟨f, hf, hf0, hfD, hfz, hfe, hνf, hscaled⟩ := hdata ν hν
  refine ⟨f, hf, hf0, hνf, ?_⟩
  intro a ha J hJ hJfin t y z l r M hl hr hM
  obtain ⟨τ, hτ, hτf, hlam, hrate, hreg, hgf, hg, hg0, hgz, hgD, hge, _, hds⟩ := hscaled a ha
  let lam := kernelTiltSaddle D θ vlo ν a
  let ρ := kernelScaledLaw τ a
  let g := kernelScaledDensity a (kernelTiltDensity ν lam f)
  have ha0 : 0 < a := by linarith [(abs_le.mp ha).1]
  have halo : 1 / 2 ≤ a := by linarith [(abs_le.mp ha).1]
  have hlam' : |lam| ≤ θ / 2 := (hlam.trans (min_le_left _ _)).trans
    ((saTiltRadius_le_half _ _ (by positivity)).trans (by linarith))
  have hft : Measurable (kernelTiltDensity ν lam f) := by unfold kernelTiltDensity; fun_prop
  have hft0 (x : ℝ) : 0 ≤ kernelTiltDensity ν lam f x :=
    mul_nonneg (Real.exp_nonneg _) (hf0 x)
  have hftD (x : ℝ) : kernelTiltDensity ν lam f x ≤ D * Real.exp θ :=
    hν.kernelTiltDensity_le hθ hvlo hfz hfe hlam' x
  have hmark : kernelMarkedDens J τ (kernelTiltDensity ν lam f) 1 a t l r y z ≤ D' := by
    apply (kernelFar_markedDens_le_div hJ hJfin τ hft hft0 hftD hτf 1 t ha0.ne' hl r y z).trans
    rw [abs_of_pos ha0, div_le_iff₀ ha0]
    dsimp [D']
    have hh := mul_le_mul_of_nonneg_right halo (show 0 ≤ D * Real.exp θ by positivity)
    nlinarith
  have hpin : krDens J τ (kernelTiltDensity ν lam f) 1 a M z y ≤
      (D' * Real.exp θ') * Real.exp (-d * min ((z - y) ^ 2 / (M : ℝ)) |z - y|) := by
    have he : krDens J τ (kernelTiltDensity ν lam f) 1 a M z y =
        krDens J ρ g 1 1 M z y := by
      simpa only [one_mul] using hds J hJ 1 M z y
    rw [he]
    have hh := hdisp ρ hreg g hg hg0 hgz hge hgf J hJ 1 (Or.inl rfl) M hM z y
    have hs : (y - z) ^ 2 = (z - y) ^ 2 := by ring
    simpa only [hs, abs_sub_comm y z] using hh
  have hpair := kernel_marked_pin_tilt hJ ν τ hf hf0 hfD
    ((hν.univClass hθ hvlo).kernel_integrable_exp_raw hlam') hτ hftD 1 t ha0.ne' hl hr hM y z
  simp only [mul_one] at hpair
  change kernelMarkedDens J ν f 1 a t l r y z * krDens J ν f 1 a M z y =
    Real.exp (-((l : ℝ) + r + M) * kernelTiltRate ν a lam + lam * t - lam / a) *
      (kernelMarkedDens J τ (kernelTiltDensity ν lam f) 1 a t l r y z *
        krDens J τ (kernelTiltDensity ν lam f) 1 a M z y) at hpair
  rw [hpair]
  have hexp : Real.exp (-((l : ℝ) + r + M) * kernelTiltRate ν a lam + lam * t - lam / a) ≤
      Real.exp (-c * ((l : ℝ) + r + M) * (a - 1) ^ 2 + lam * t - lam / a) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hrate (show 0 ≤ (l : ℝ) + r + M by positivity)
    nlinarith
  calc
    _ ≤ Real.exp (-c * ((l : ℝ) + r + M) * (a - 1) ^ 2 + lam * t - lam / a) *
        (D' * ((D' * Real.exp θ') *
          Real.exp (-d * min ((z - y) ^ 2 / (M : ℝ)) |z - y|))) :=
      mul_le_mul hexp (mul_le_mul hmark hpin (krDens_nonneg τ hft0 _ _ _) hD'.le)
        (mul_nonneg (kernelMarkedDens_nonneg τ hft0 _ _ _ _ _) (krDens_nonneg τ hft0 _ _ _))
        (Real.exp_nonneg _)
    _ = _ := by
      dsimp only [lam]
      simp only [sub_eq_add_neg, Real.exp_add]
      ring

end
end PGM
