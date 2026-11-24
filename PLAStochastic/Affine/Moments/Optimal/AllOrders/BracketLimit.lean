import PLAStochastic.ForMathlib.Analysis.Complex.ContinuationAtGammaPoles
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Evaluating the Mellin bracket at the positive integers

The Mellin identity for the optimal lifetime has the shape
`G q = 8^q Γ(-q) / (3(q+1)) · 𝓑_D(q)` on `Re q < -3/2`, where `G` is entire and
`𝓑_D` is built from a spectral function `D` and the Riemann zeta function.
For an abstract `D` that is holomorphic away from the half-integers `1/2 - r` and has
the values `D(-N) = -[N = 0]`, the identity continues to the complement of a countable
closed set, and at every positive integer `n` the pole of `Γ(-q)` meets the zero of
`𝓑_D(n)`, leaving `G n` as an explicit combination of first derivatives.
-/

open Complex Filter Set Topology

namespace BrownianAffine

/-- The bracket `𝓑_D(q)` of the Mellin identity (T5). -/
noncomputable def mellinBracket (D : ℂ → ℂ) (q : ℂ) : ℂ :=
  4 * (2 * q + 1) * (2 * q + 3) * (D (-q - 1) - riemannZeta (-2 * q - 2)) +
    4 * q * (2 * q + 1) * (D (-q) - riemannZeta (-2 * q)) + q * (q - 1) * D (1 - q)

/-- The prefactor `8^q / (3(q+1))` of the Mellin identity. -/
noncomputable def mellinPrefactor (q : ℂ) : ℂ := (8 : ℂ) ^ q / (3 * (q + 1))

/-- The poles that can occur in the Mellin identity: the naturals, `-1`, and the
half-integers `r - 3/2`. -/
def mellinSingular : Set ℂ :=
  range (fun n : ℕ => (n : ℂ)) ∪ {-1} ∪ range (fun r : ℕ => (r : ℂ) - 3 / 2)

theorem isClosed_range_natCast_complex : IsClosed (range (fun n : ℕ => (n : ℂ))) := by
  have hR : IsClosed (range (fun n : ℕ => (n : ℝ))) :=
    Nat.isClosedEmbedding_coe_real.isClosed_range
  have h := Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _ hR
  rwa [← range_comp] at h

theorem mellinSingular_countable : mellinSingular.Countable :=
  ((countable_range _).union (countable_singleton _)).union (countable_range _)

theorem mellinSingular_isClosed : IsClosed mellinSingular := by
  refine (isClosed_range_natCast_complex.union isClosed_singleton).union ?_
  have h := (Homeomorph.subRight ((3 : ℂ) / 2)).isClosedMap _ isClosed_range_natCast_complex
  rwa [← range_comp] at h

theorem re_ge_of_mem_mellinSingular {q : ℂ} (hq : q ∈ mellinSingular) : -3 / 2 ≤ q.re := by
  rcases hq with (⟨n, rfl⟩ | h) | ⟨r, rfl⟩
  · simp only [natCast_re]
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  · rw [mem_singleton_iff] at h
    subst h
    norm_num
  · simp only [sub_re, natCast_re]
    have : (0 : ℝ) ≤ r := r.cast_nonneg
    norm_num

/-- Away from the half-integers. -/
def NotHalfPole (s : ℂ) : Prop := ∀ r : ℕ, s ≠ 1 / 2 - r

theorem notHalfPole_neg_sub_one {q : ℂ} (hq : q ∉ mellinSingular) : NotHalfPole (-q - 1) := by
  intro r h
  apply hq
  right
  exact ⟨r, by linear_combination h⟩

theorem notHalfPole_neg {q : ℂ} (hq : q ∉ mellinSingular) : NotHalfPole (-q) := by
  intro r h
  apply hq
  right
  exact ⟨r + 1, by push_cast; linear_combination h⟩

theorem notHalfPole_one_sub {q : ℂ} (hq : q ∉ mellinSingular) : NotHalfPole (1 - q) := by
  intro r h
  apply hq
  right
  exact ⟨r + 2, by push_cast; linear_combination h⟩

theorem differentiableAt_mellinBracket {D : ℂ → ℂ}
    (hD : ∀ s, NotHalfPole s → DifferentiableAt ℂ D s) {q : ℂ}
    (h1 : NotHalfPole (-q - 1)) (h2 : NotHalfPole (-q)) (h3 : NotHalfPole (1 - q))
    (hz1 : -2 * q - 2 ≠ 1) (hz2 : -2 * q ≠ 1) :
    DifferentiableAt ℂ (mellinBracket D) q := by
  have d1 : DifferentiableAt ℂ (fun q : ℂ => D (-q - 1)) q :=
    (hD _ h1).comp q (by fun_prop)
  have d2 : DifferentiableAt ℂ (fun q : ℂ => D (-q)) q := (hD _ h2).comp q (by fun_prop)
  have d3 : DifferentiableAt ℂ (fun q : ℂ => D (1 - q)) q := (hD _ h3).comp q (by fun_prop)
  have z1 : DifferentiableAt ℂ (fun q : ℂ => riemannZeta (-2 * q - 2)) q :=
    (differentiableAt_riemannZeta hz1).comp q (by fun_prop)
  have z2 : DifferentiableAt ℂ (fun q : ℂ => riemannZeta (-2 * q)) q :=
    (differentiableAt_riemannZeta hz2).comp q (by fun_prop)
  unfold mellinBracket
  fun_prop

theorem differentiableAt_mellinPrefactor {q : ℂ} (hq : q ≠ -1) :
    DifferentiableAt ℂ mellinPrefactor q := by
  have h3 : (3 : ℂ) * (q + 1) ≠ 0 := by
    refine mul_ne_zero three_ne_zero ?_
    intro h
    exact hq (by linear_combination h)
  unfold mellinPrefactor
  exact ((differentiableAt_id.const_cpow (Or.inl (by norm_num : (8 : ℂ) ≠ 0)))).div
    (by fun_prop) h3

/-- The Mellin right side is holomorphic off `mellinSingular`. -/
theorem differentiableOn_mellin {D : ℂ → ℂ} (hD : ∀ s, NotHalfPole s → DifferentiableAt ℂ D s) :
    DifferentiableOn ℂ (fun q => mellinPrefactor q * Gamma (-q) * mellinBracket D q)
      mellinSingularᶜ := by
  intro q hq
  have hnat : ∀ m : ℕ, -q ≠ -m := by
    intro m h
    exact hq (Or.inl (Or.inl ⟨m, by linear_combination h⟩))
  have hm1 : q ≠ -1 := fun h => hq (Or.inl (Or.inr h))
  have hz1 : -2 * q - 2 ≠ 1 := by
    intro h
    exact hq (Or.inr ⟨0, by push_cast; linear_combination h / 2⟩)
  have hz2 : -2 * q ≠ 1 := by
    intro h
    exact hq (Or.inr ⟨1, by push_cast; linear_combination h / 2⟩)
  have hG : DifferentiableAt ℂ (fun q : ℂ => Gamma (-q)) q :=
    (differentiableAt_Gamma _ hnat).comp q differentiableAt_id.neg
  exact (((differentiableAt_mellinPrefactor hm1).mul hG).mul
    (differentiableAt_mellinBracket hD (notHalfPole_neg_sub_one hq) (notHalfPole_neg hq)
      (notHalfPole_one_sub hq) hz1 hz2)).differentiableWithinAt

/-- Continuation of the Mellin identity off the singular set. -/
theorem eqOn_mellin_of_re_lt {D G : ℂ → ℂ} (hD : ∀ s, NotHalfPole s → DifferentiableAt ℂ D s)
    (hG : Differentiable ℂ G)
    (hmel : ∀ q : ℂ, q.re < -3 / 2 → G q = mellinPrefactor q * Gamma (-q) * mellinBracket D q) :
    EqOn G (fun q => mellinPrefactor q * Gamma (-q) * mellinBracket D q) mellinSingularᶜ := by
  have hV : IsOpen {q : ℂ | q.re < -3 / 2} := isOpen_lt continuous_re continuous_const
  have hVne : ({q : ℂ | q.re < -3 / 2}).Nonempty := ⟨-2, by norm_num⟩
  have hVC : {q : ℂ | q.re < -3 / 2} ⊆ mellinSingularᶜ := by
    intro q hq hS
    exact absurd (re_ge_of_mem_mellinSingular hS) (not_le.mpr hq)
  exact (eqOn_compl_of_countable_closed mellinSingular_countable mellinSingular_isClosed
    (differentiableOn_mellin hD) hG hV hVne hVC (fun q hq => (hmel q hq).symm)).symm

/-- Near a positive integer, all other points avoid the singular set. -/
theorem eventually_not_mem_mellinSingular (n : ℕ) :
    ∀ᶠ q in 𝓝[≠] (n : ℂ), q ∉ mellinSingular := by
  have hball : Metric.ball (n : ℂ) (1 / 2) ∈ 𝓝 (n : ℂ) := Metric.ball_mem_nhds _ (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with q hq hqn hS
  rw [Metric.mem_ball, dist_eq_norm] at hq
  rcases hS with (⟨m, rfl⟩ | h) | ⟨r, rfl⟩
  · have hmn : m ≠ n := fun h => hqn (by simp [h])
    rw [show (m : ℂ) - n = ((m : ℤ) - n : ℤ) by push_cast; ring, Complex.norm_intCast] at hq
    have hne : ((m : ℤ) - n) ≠ 0 := by omega
    have h1 : (1 : ℝ) ≤ |(((m : ℤ) - n : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hne
    linarith
  · rw [mem_singleton_iff] at h
    subst h
    have : ‖(-1 : ℂ) - n‖ = n + 1 := by
      rw [show (-1 : ℂ) - n = -((n + 1 : ℕ) : ℂ) by push_cast; ring, norm_neg, Complex.norm_natCast]
      push_cast
      ring
    rw [this] at hq
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  · have hre := (Complex.re_le_norm (((r : ℂ) - 3 / 2) - n))
    have hre' : (((r : ℂ) - 3 / 2) - n).re = (r : ℝ) - n - 3 / 2 := by simp; ring
    have him : ‖((r : ℂ) - 3 / 2) - n‖ = |(r : ℝ) - n - 3 / 2| := by
      rw [show ((r : ℂ) - 3 / 2) - n = (((r : ℝ) - n - 3 / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [him] at hq
    have hint : (1 / 2 : ℝ) ≤ |(r : ℝ) - n - 3 / 2| := by
      have hk : ∀ k : ℤ, (1 / 2 : ℝ) ≤ |(k : ℝ) - 3 / 2| := by
        intro k
        rcases le_or_gt k 1 with hk | hk
        · have : (k : ℝ) ≤ 1 := by exact_mod_cast hk
          rw [abs_of_neg (by linarith)]
          linarith
        · have : (2 : ℝ) ≤ k := by exact_mod_cast hk
          rw [abs_of_nonneg (by linarith)]
          linarith
      simpa using hk ((r : ℤ) - n)
    linarith

/-- The value at a positive integer: the limit of the Mellin right side. -/
theorem eq_of_mellin_at_nat {D G : ℂ → ℂ} (hD : ∀ s, NotHalfPole s → DifferentiableAt ℂ D s)
    (hG : Differentiable ℂ G)
    (hmel : ∀ q : ℂ, q.re < -3 / 2 → G q = mellinPrefactor q * Gamma (-q) * mellinBracket D q)
    {n : ℕ} (hH : DifferentiableAt ℂ (fun q => mellinPrefactor q * mellinBracket D q) n)
    (h0 : mellinBracket D n = 0) :
    G n = (-1) ^ (n + 1) / n.factorial * deriv (fun q => mellinPrefactor q * mellinBracket D q) n := by
  have heq := eqOn_mellin_of_re_lt hD hG hmel
  have hlim := tendsto_Gamma_neg_mul_of_zero hH (by simp [h0])
  have hGlim : Tendsto G (𝓝[≠] (n : ℂ)) (𝓝 (G n)) :=
    (hG.continuous.tendsto _).mono_left nhdsWithin_le_nhds
  refine tendsto_nhds_unique hGlim (hlim.congr' ?_)
  filter_upwards [eventually_not_mem_mellinSingular n] with q hq
  rw [heq hq]
  ring

theorem notHalfPole_neg_nat (N : ℕ) : NotHalfPole (-(N : ℂ)) := by
  intro r h
  have h2 : ((2 * r - 2 * N : ℤ) : ℂ) = 1 := by push_cast; linear_combination 2 * h
  have h3 : (2 * r - 2 * N : ℤ) = 1 := by exact_mod_cast h2
  omega

theorem riemannZeta_neg_two_mul_natCast {k : ℕ} (hk : 1 ≤ k) : riemannZeta (-2 * (k : ℂ)) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  push_cast
  exact riemannZeta_neg_two_mul_nat_add_one j

/-- At a positive integer the bracket vanishes, and the derivative of the full right side
reduces to the prefactor times the derivative of the bracket. -/
theorem mellinBracket_nat_and_deriv {D : ℂ → ℂ}
    (hD : ∀ s, NotHalfPole s → DifferentiableAt ℂ D s)
    (hDval : ∀ N : ℕ, D (-(N : ℂ)) = if N = 0 then -1 else 0) {n : ℕ} (hn : 1 ≤ n) :
    mellinBracket D n = 0 ∧
      DifferentiableAt ℂ (fun q => mellinPrefactor q * mellinBracket D q) n ∧
      deriv (fun q => mellinPrefactor q * mellinBracket D q) n =
        mellinPrefactor n *
          (4 * (2 * n + 1) * (2 * n + 3) *
              (-deriv D (-((n + 1 : ℕ) : ℂ)) + 2 * deriv riemannZeta (-2 * n - 2)) +
            4 * n * (2 * n + 1) * (-deriv D (-(n : ℂ)) + 2 * deriv riemannZeta (-2 * n)) +
            (2 * n - 1) * D (1 - n) - n * (n - 1) * deriv D (1 - n)) := by
  set x : ℂ := (n : ℂ) with hx
  have e1 : -x - 1 = -((n + 1 : ℕ) : ℂ) := by rw [hx]; push_cast; ring
  have e3 : 1 - x = -((n - 1 : ℕ) : ℂ) := by rw [hx, Nat.cast_sub hn]; push_cast; ring
  -- derivatives of the four spectral and zeta pieces
  have hi1 : HasDerivAt (fun q : ℂ => -q - 1) (-1) x := (hasDerivAt_id' x).neg.sub_const 1
  have hi2 : HasDerivAt (fun q : ℂ => -q) (-1) x := (hasDerivAt_id' x).neg
  have hi3 : HasDerivAt (fun q : ℂ => 1 - q) (-1) x := (hasDerivAt_id' x).const_sub 1
  have hD1 : HasDerivAt (fun q : ℂ => D (-q - 1)) (-deriv D (-((n + 1 : ℕ) : ℂ))) x := by
    have hd := hD (-x - 1) (by rw [e1]; exact notHalfPole_neg_nat _)
    have h := hd.hasDerivAt.comp x hi1
    rw [e1] at h
    simpa only [Function.comp_def, mul_neg, mul_one] using h
  have hD2 : HasDerivAt (fun q : ℂ => D (-q)) (-deriv D (-(n : ℂ))) x := by
    have hd := hD (-x) (by rw [hx]; exact notHalfPole_neg_nat _)
    have h := hd.hasDerivAt.comp x hi2
    rw [hx] at h
    simpa only [Function.comp_def, mul_neg, mul_one] using h
  have hD3 : HasDerivAt (fun q : ℂ => D (1 - q)) (-deriv D (1 - n)) x := by
    have hd := hD (1 - x) (by rw [e3]; exact notHalfPole_neg_nat _)
    have h := hd.hasDerivAt.comp x hi3
    rw [hx] at h
    simpa only [Function.comp_def, mul_neg, mul_one] using h
  have hne1 : -2 * x - 2 ≠ 1 := by
    rw [hx]
    intro h
    have h2 : ((-2 * n - 3 : ℤ) : ℂ) = 0 := by push_cast; linear_combination h
    have h3 : (-2 * n - 3 : ℤ) = 0 := by exact_mod_cast h2
    omega
  have hne2 : -2 * x ≠ 1 := by
    rw [hx]
    intro h
    have h2 : ((-2 * n - 1 : ℤ) : ℂ) = 0 := by push_cast; linear_combination h
    have h3 : (-2 * n - 1 : ℤ) = 0 := by exact_mod_cast h2
    omega
  have hj1 : HasDerivAt (fun q : ℂ => -2 * q - 2) (-2) x := by
    simpa using ((hasDerivAt_id' x).const_mul (-2)).sub_const 2
  have hj2 : HasDerivAt (fun q : ℂ => -2 * q) (-2) x := by
    simpa using (hasDerivAt_id' x).const_mul (-2)
  have hZ1 : HasDerivAt (fun q : ℂ => riemannZeta (-2 * q - 2))
      (deriv riemannZeta (-2 * n - 2) * (-2)) x := by
    have h := (differentiableAt_riemannZeta hne1).hasDerivAt.comp x hj1
    rw [hx] at h
    exact h
  have hZ2 : HasDerivAt (fun q : ℂ => riemannZeta (-2 * q)) (deriv riemannZeta (-2 * n) * (-2)) x := by
    have h := (differentiableAt_riemannZeta hne2).hasDerivAt.comp x hj2
    rw [hx] at h
    exact h
  -- values at the integer
  have v1 : D (-x - 1) - riemannZeta (-2 * x - 2) = 0 := by
    rw [e1, hDval, if_neg (by omega), show -2 * x - 2 = -2 * ((n + 1 : ℕ) : ℂ) by rw [hx]; push_cast; ring,
      riemannZeta_neg_two_mul_natCast (by omega)]
    ring
  have v2 : D (-x) - riemannZeta (-2 * x) = 0 := by
    rw [hx, hDval, if_neg (by omega), riemannZeta_neg_two_mul_natCast hn]
    ring
  have v3 : x * (x - 1) * D (1 - x) = 0 := by
    rcases Nat.lt_or_ge 1 n with h | h
    · rw [e3, hDval, if_neg (by omega)]
      ring
    · have : n = 1 := by omega
      rw [hx, this]
      push_cast
      ring
  have hB0 : mellinBracket D x = 0 := by
    unfold mellinBracket
    rw [v1, v2, v3]
    ring
  -- derivative of the bracket
  have hB : HasDerivAt (mellinBracket D)
      (4 * (2 * x + 1) * (2 * x + 3) *
          (-deriv D (-((n + 1 : ℕ) : ℂ)) + 2 * deriv riemannZeta (-2 * n - 2)) +
        4 * x * (2 * x + 1) * (-deriv D (-(n : ℂ)) + 2 * deriv riemannZeta (-2 * n)) +
        (2 * x - 1) * D (1 - n) - x * (x - 1) * deriv D (1 - n)) x := by
    have hA : HasDerivAt (fun q : ℂ => 4 * (2 * q + 1) * (2 * q + 3))
        (4 * (2 * (2 * x + 3) + 2 * (2 * x + 1))) x := by
      have := ((((hasDerivAt_id' x).const_mul 2).add_const 1).mul
        (((hasDerivAt_id' x).const_mul 2).add_const 3)).const_mul 4
      exact (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by simp only [Pi.mul_apply]; ring)).congr_deriv
        (by ring)
    have hBq : HasDerivAt (fun q : ℂ => 4 * q * (2 * q + 1)) (4 * (2 * x + 1) + 4 * x * 2) x := by
      have := ((hasDerivAt_id' x).const_mul 4).mul (((hasDerivAt_id' x).const_mul 2).add_const 1)
      exact (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by simp only [Pi.mul_apply])).congr_deriv
        (by ring)
    have hC : HasDerivAt (fun q : ℂ => q * (q - 1)) (2 * x - 1) x := by
      have := (hasDerivAt_id' x).mul ((hasDerivAt_id' x).sub_const 1)
      exact (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => by simp only [Pi.mul_apply])).congr_deriv
        (by ring)
    have h := ((hA.mul (hD1.sub hZ1)).add (hBq.mul (hD2.sub hZ2))).add (hC.mul hD3)
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)).congr_deriv ?_
    · simp only [mellinBracket, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    · simp only [Pi.sub_apply]
      rw [v1, v2, hx]
      ring
  have hP : DifferentiableAt ℂ mellinPrefactor x := by
    apply differentiableAt_mellinPrefactor
    rw [hx]
    intro h
    have h2 : ((n + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination h
    exact Nat.succ_ne_zero n (by exact_mod_cast h2)
  have hprod : HasDerivAt (fun q => mellinPrefactor q * mellinBracket D q) _ x :=
    hP.hasDerivAt.mul hB
  refine ⟨hB0, hprod.differentiableAt, ?_⟩
  rw [hprod.deriv, hB0, mul_zero, zero_add, hx]

/-- The value of an entire function obeying the Mellin identity at a positive integer. -/
theorem eq_at_nat_of_mellin {D G : ℂ → ℂ} (hD : ∀ s, NotHalfPole s → DifferentiableAt ℂ D s)
    (hDval : ∀ N : ℕ, D (-(N : ℂ)) = if N = 0 then -1 else 0) (hG : Differentiable ℂ G)
    (hmel : ∀ q : ℂ, q.re < -3 / 2 → G q = mellinPrefactor q * Gamma (-q) * mellinBracket D q)
    {n : ℕ} (hn : 1 ≤ n) :
    G n = (8 : ℂ) ^ n * (-1) ^ (n + 1) / (3 * (n + 1) * n.factorial) *
      (4 * (2 * n + 1) * (2 * n + 3) *
          (-deriv D (-((n + 1 : ℕ) : ℂ)) + 2 * deriv riemannZeta (-2 * n - 2)) +
        4 * n * (2 * n + 1) * (-deriv D (-(n : ℂ)) + 2 * deriv riemannZeta (-2 * n)) +
        (2 * n - 1) * D (1 - n) - n * (n - 1) * deriv D (1 - n)) := by
  obtain ⟨h0, hdiff, hderiv⟩ := mellinBracket_nat_and_deriv hD hDval hn
  rw [eq_of_mellin_at_nat hD hG hmel hdiff h0, hderiv]
  unfold mellinPrefactor
  rw [Complex.cpow_natCast]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h1 : (3 * ((n : ℂ) + 1)) ≠ 0 := by
    refine mul_ne_zero three_ne_zero ?_
    have : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simpa using this
  field_simp

end BrownianAffine
