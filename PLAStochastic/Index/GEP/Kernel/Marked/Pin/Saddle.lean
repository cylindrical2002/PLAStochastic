import PLAStochastic.Index.GEP.Kernel.Marked.Pin.Crossing
import PLAStochastic.Index.GEP.Kernel.Marked.Pin.Spectral

/-!
# Simultaneous drift, crossing and time decay of actual marked pin pairs

All constants precede the original law. A centered saddle law supplies both
crossing and spectral bounds for the same pointwise density representative.
Their geometric mean is taken before exact paired tilt conjugacy is undone.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- Two exponential majorants may be combined while retaining half of each
exponent. The sum of their constants avoids choosing a square-root coefficient. -/
theorem kernelFar_geometric_bound {u A B x y : ℝ} (hu : 0 ≤ u) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : u ≤ A * Real.exp x) (hy : u ≤ B * Real.exp y) :
    u ≤ (A + B) * Real.exp ((x + y) / 2) := by
  have hp := mul_le_mul hx hy hu (mul_nonneg hA (Real.exp_nonneg x))
  have hc : A * B ≤ (A + B) ^ 2 := by nlinarith [sq_nonneg A, sq_nonneg B, mul_nonneg hA hB]
  have he : Real.exp ((x + y) / 2) ^ 2 = Real.exp (x + y) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  apply (sq_le_sq₀ hu (by positivity : 0 ≤ (A + B) * Real.exp ((x + y) / 2))).mp
  rw [mul_pow, he]
  calc
    u ^ 2 ≤ A * B * Real.exp (x + y) := by
      rw [Real.exp_add]
      nlinarith [hp]
    _ ≤ (A + B) ^ 2 * Real.exp (x + y) := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)

/-- The actual marked pin pair has all three decay mechanisms simultaneously,
at every positive pair of random sides and every positive other-pin length.
The only input dependence outside the decay is the exact insertion tilt.
This covers the compact saddle neighborhood, before any slope integration. -/
theorem kernel_regLaw_saddle_marked_pin_decay (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ δ c d k K : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < c ∧ 0 < d ∧ 0 < k ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ a : ℝ, |a - 1| ≤ δ → ∀ α w : ℝ, 1 ≤ w → ∀ t y z : ℝ,
        ∀ l r M : ℕ, 1 ≤ l → 1 ≤ r → 1 ≤ M →
          kernelMarkedDens (Icc α (α + w)) ν f 1 a t l r y z *
            krDens (Icc α (α + w)) ν f 1 a M z y ≤
            K * w * Real.exp (-c * ((l : ℝ) + r + M) * (a - 1) ^ 2 +
              kernelTiltSaddle D θ vlo ν a * t - kernelTiltSaddle D θ vlo ν a / a -
              d * min ((z - y) ^ 2 / (M : ℝ)) |z - y| -
              k * (((l : ℝ) + r + M) - 8) / w ^ 2) := by
  let D' := 2 * D * Real.exp θ
  let θ' := θ / 4
  let vlo' := 3 * vlo / 16
  let vhi' := 5 * vhi
  have hD' : 0 < D' := by positivity
  have hθ' : 0 < θ' := by positivity
  have hvlo' : 0 < vlo' := by positivity
  have hv' : vlo' ≤ vhi' := by dsimp [vlo', vhi']; linarith
  obtain ⟨d, hd, hdisp⟩ := kernel_regLaw_displacement D' θ' vlo' vhi' hD' hθ' hvlo' hv'
  obtain ⟨k, hk, hspec⟩ := kernel_regLaw_marked_pair_spectral D' θ' vlo' vhi' 1
    hD' hθ' hvlo' hv' (by norm_num)
  obtain ⟨δ, c, hδ, hδhi, hc, hdata⟩ := kernel_regLaw_saddle_scaled D θ vlo vhi hD hθ hvlo hv
  let K := D' ^ 2 * (Real.exp θ' + 2 + 18 * D')
  have hK : 0 < K := by positivity
  refine ⟨δ, c, d / 2, k / 8, K, hδ, hδhi, hc, by positivity, by positivity, hK, ?_⟩
  intro ν hν
  obtain ⟨f, hf, hf0, hfD, hfz, hfe, hνf, hscaled⟩ := hdata ν hν
  refine ⟨f, hf, hf0, hνf, ?_⟩
  intro a ha α w hw t y z l r M hl hr hM
  obtain ⟨τ, hτ, _, hlam, hrate, hreg, hgf, hg, hg0, hgz, hgD, hge, _, hds⟩ := hscaled a ha
  let lam := kernelTiltSaddle D θ vlo ν a
  let ρ := kernelScaledLaw τ a
  let g := kernelScaledDensity a (kernelTiltDensity ν lam f)
  let J := Icc α (α + w)
  let N : ℝ := (l : ℝ) + r + M
  let Q := min ((z - y) ^ 2 / (M : ℝ)) |z - y|
  let P := kernelMarkedDens J ρ g 1 1 (a * t) l r y z * krDens J ρ g 1 1 M z y
  have hJ : MeasurableSet J := measurableSet_Icc
  have hJfin : volume J ≠ ⊤ := by simp [J]
  have hP0 : 0 ≤ P := mul_nonneg (kernelMarkedDens_nonneg ρ hg0 _ _ _ _ _) (krDens_nonneg ρ hg0 _ _ _)
  have ha0 : 0 < a := by linarith [(abs_le.mp ha).1]
  have hlam' : |lam| ≤ θ / 2 := (hlam.trans (min_le_left _ _)).trans
    ((saTiltRadius_le_half _ _ (by positivity)).trans (by linarith))
  have hftD (x : ℝ) : kernelTiltDensity ν lam f x ≤ D * Real.exp θ :=
    hν.kernelTiltDensity_le hθ hvlo hfz hfe hlam' x
  have hscale (n : ℕ) (u v : ℝ) : krDens J τ (kernelTiltDensity ν lam f) 1 a n u v =
      krDens J ρ g 1 1 n u v := by simpa only [one_mul] using hds J hJ 1 n u v
  have hmScale : kernelMarkedDens J τ (kernelTiltDensity ν lam f) 1 a t l r y z =
      kernelMarkedDens J ρ g 1 1 (a * t) l r y z := by
    unfold kernelMarkedDens
    apply integral_congr_ae
    filter_upwards [] with u
    rw [hscale, hscale]
    simp only [one_mul]
  have hmark : kernelMarkedDens J ρ g 1 1 (a * t) l r y z ≤ D' := by
    simpa only [abs_one, div_one] using kernelFar_markedDens_le_div hJ hJfin ρ hg hg0 hgD
      hgf 1 (a * t) (by norm_num : (1 : ℝ) ≠ 0) hl r y z
  have hpin : krDens J ρ g 1 1 M z y ≤ (D' * Real.exp θ') * Real.exp (-d * Q) := by
    have hh := hdisp ρ hreg g hg hg0 hgz hge hgf J hJ 1 (Or.inl rfl) M hM z y
    have hs : (y - z) ^ 2 = (z - y) ^ 2 := by ring
    simpa only [hs, abs_sub_comm y z] using hh
  have hcross : P ≤ (D' * (D' * Real.exp θ')) * Real.exp (-d * Q) := by
    have hh := mul_le_mul hmark hpin (krDens_nonneg ρ hg0 _ _ _) hD'.le
    simpa only [mul_assoc] using hh
  have hspectral : P ≤ (D' * (1 + 3 * Real.sqrt (D' * w))) ^ 2 *
      Real.exp (-(k * (N - 8) / (4 * w ^ 2))) := by
    simpa only [div_one] using hspec ρ hreg g hg hg0 hgD hgf α w 1 1 hw
      (by norm_num : (1 : ℝ) ≤ |(1 : ℝ)|) (a * t) y z l r M hl hr hM
  have hgeom := kernelFar_geometric_bound hP0 (by positivity) (sq_nonneg _) hcross hspectral
  have hcoef : D' * (D' * Real.exp θ') + (D' * (1 + 3 * Real.sqrt (D' * w))) ^ 2 ≤ K * w := by
    have hs : Real.sqrt (D' * w) ^ 2 = D' * w := Real.sq_sqrt (by positivity)
    have hsq : (1 + 3 * Real.sqrt (D' * w)) ^ 2 ≤ 2 + 18 * D' * w := by
      nlinarith [sq_nonneg (1 - 3 * Real.sqrt (D' * w))]
    have hh := mul_le_mul_of_nonneg_left hsq (sq_nonneg D')
    have he := mul_le_mul_of_nonneg_left hw (show 0 ≤ D' ^ 2 * (Real.exp θ' + 2) by positivity)
    dsimp [K]
    nlinarith
  have hbound : P ≤ K * w * Real.exp ((-d * Q + -(k * (N - 8) / (4 * w ^ 2))) / 2) :=
    hgeom.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _))
  have hpair := kernel_marked_pin_tilt hJ ν τ hf hf0 hfD
    ((hν.univClass hθ hvlo).kernel_integrable_exp_raw hlam') hτ hftD 1 t ha0.ne' hl hr hM y z
  simp only [mul_one] at hpair
  change kernelMarkedDens J ν f 1 a t l r y z * krDens J ν f 1 a M z y =
    Real.exp (-N * kernelTiltRate ν a lam + lam * t - lam / a) *
      (kernelMarkedDens J τ (kernelTiltDensity ν lam f) 1 a t l r y z *
        krDens J τ (kernelTiltDensity ν lam f) 1 a M z y) at hpair
  rw [hmScale, hscale] at hpair
  rw [hpair]
  have hexp : Real.exp (-N * kernelTiltRate ν a lam + lam * t - lam / a) ≤
      Real.exp (-c * N * (a - 1) ^ 2 + lam * t - lam / a) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hrate (show 0 ≤ N by positivity)
    nlinarith
  calc
    _ ≤ Real.exp (-c * N * (a - 1) ^ 2 + lam * t - lam / a) *
        (K * w * Real.exp ((-d * Q + -(k * (N - 8) / (4 * w ^ 2))) / 2)) :=
      mul_le_mul hexp hbound hP0 (Real.exp_nonneg _)
    _ = _ := by
      change _ = K * w * Real.exp (-c * N * (a - 1) ^ 2 + lam * t - lam / a -
        d / 2 * Q - k / 8 * (N - 8) / w ^ 2)
      rw [mul_left_comm _ (K * w), ← Real.exp_add]
      congr 2
      ring

end
end PGM
