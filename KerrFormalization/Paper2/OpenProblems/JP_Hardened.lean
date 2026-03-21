import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# JP Integrability — Hardened Submission

Self-contained Johannsen-Psaltis equatorial probe.

The goal is to formalize the structural contrast:

- Paper 2 `Delta -> Delta + eps r` deformations hit the radial channel, which
  couples to `K_rr` and therefore vanishes on the equator because of the
  `cos^2(theta)` factor.
- Johannsen-Psaltis modifies `g_tt`, so the equatorial channel couples through
  `K_tt`, which stays nonzero for spinning black holes.
-/

noncomputable section

open Real

/-- Kerr Sigma. -/
def kerrSigma (a r theta : ℝ) : ℝ :=
  r ^ 2 + a ^ 2 * (Real.cos theta) ^ 2

/-- Kerr Delta. -/
def kerrDelta (M a r : ℝ) : ℝ :=
  r ^ 2 - 2 * M * r + a ^ 2

/-- Kerr `g_tt`. -/
def kerr_gtt (M a r theta : ℝ) : ℝ :=
  -(1 - 2 * M * r / kerrSigma a r theta)

/-- Johannsen-Psaltis deviation profile for the `alpha_13` mode. -/
def jp_h (M a alpha13 r theta : ℝ) : ℝ :=
  alpha13 * M ^ 3 * r / (kerrSigma a r theta) ^ 2

/-- JP-modified `g_tt = g_tt^Kerr (1 + h)`. -/
def jp_gtt (M a alpha13 r theta : ℝ) : ℝ :=
  kerr_gtt M a r theta * (1 + jp_h M a alpha13 r theta)

/-- At the equator `theta = pi / 2`, `Sigma = r^2`. -/
theorem sigma_equatorial (a r : ℝ) :
    kerrSigma a r (Real.pi / 2) = r ^ 2 := by
  unfold kerrSigma
  simp [Real.cos_pi_div_two]

/-- At the equator the JP deviation reduces to `alpha13 * M^3 / r^3`. -/
theorem jp_h_equatorial
    (M a alpha13 r : ℝ) (hr : r ≠ 0) :
    jp_h M a alpha13 r (Real.pi / 2) = alpha13 * M ^ 3 / r ^ 3 := by
  unfold jp_h
  rw [sigma_equatorial]
  field_simp [hr]
  ring

/-- Exact equatorial JP correction to `g_tt`. -/
theorem jp_gtt_correction_equatorial
    (M a alpha13 r : ℝ)
    (hr : r ≠ 0) :
    jp_gtt M a alpha13 r (Real.pi / 2) - kerr_gtt M a r (Real.pi / 2) =
      alpha13 * M ^ 3 * (2 * M - r) / r ^ 4 := by
  unfold jp_gtt
  rw [jp_h_equatorial M a alpha13 r hr]
  unfold kerr_gtt
  rw [sigma_equatorial]
  field_simp [hr]
  ring

/-- The JP `g_tt` correction is nonzero on the equator away from `r = 2M`. -/
theorem jp_gtt_correction_equatorial_nonzero
    (M a alpha13 r : ℝ)
    (hM : M > 0) (hr : r > 0) (hAlpha : alpha13 ≠ 0)
    (h_not_2M : r ≠ 2 * M) :
    jp_gtt M a alpha13 r (Real.pi / 2) - kerr_gtt M a r (Real.pi / 2) ≠ 0 := by
  rw [jp_gtt_correction_equatorial M a alpha13 r hr.ne']
  apply div_ne_zero
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact hAlpha
    · exact pow_ne_zero 3 hM.ne'
  · exact sub_ne_zero.mpr (Ne.symm h_not_2M)

/-- Form C `K_tt`. -/
def formC_Ktt (M a r theta : ℝ) : ℝ :=
  a ^ 2 * (kerrDelta M a r * (Real.cos theta) ^ 2 + r ^ 2 * (Real.sin theta) ^ 2) /
    kerrSigma a r theta

/-- At the equator `K_tt = a^2`. -/
theorem formC_Ktt_equatorial
    (M a r : ℝ) (hr : r ≠ 0) :
    formC_Ktt M a r (Real.pi / 2) = a ^ 2 := by
  unfold formC_Ktt
  rw [sigma_equatorial]
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  field_simp [hr]
  ring

/-- Form C `K_rr`. -/
def formC_Krr (M a r theta : ℝ) : ℝ :=
  -(a ^ 2) * kerrSigma a r theta * (Real.cos theta) ^ 2 / kerrDelta M a r

/-- At the equator `K_rr = 0`. -/
theorem formC_Krr_equatorial (M a r : ℝ) :
    formC_Krr M a r (Real.pi / 2) = 0 := by
  unfold formC_Krr
  simp [sigma_equatorial, Real.cos_pi_div_two]

/-- Headline theorem: the JP equatorial `g_tt` correction times the live Form C
`K_tt` channel is nonzero. -/
theorem jp_breaks_equatorial_integrability
    (M a alpha13 r : ℝ)
    (hM : M > 0) (ha : a > 0) (haM : a < M)
    (hr : r > 0) (hAlpha : alpha13 ≠ 0)
    (hDelta : kerrDelta M a r ≠ 0)
    (h_not_2M : r ≠ 2 * M) :
    (jp_gtt M a alpha13 r (Real.pi / 2) - kerr_gtt M a r (Real.pi / 2)) *
      formC_Ktt M a r (Real.pi / 2) ≠ 0 := by
  rw [formC_Ktt_equatorial M a r hr.ne']
  apply mul_ne_zero
  · exact jp_gtt_correction_equatorial_nonzero M a alpha13 r hM hr hAlpha h_not_2M
  · exact sq_ne_zero_of_ne_zero ha.ne'

/-- Formal statement of the Paper 2 vs JP equatorial dichotomy. -/
theorem paper2_vs_jp_equatorial
    (M a r : ℝ)
    (hM : M > 0) (ha : a > 0) (hr : r > 0) (hDelta : kerrDelta M a r ≠ 0) :
    formC_Krr M a r (Real.pi / 2) = 0 ∧
    formC_Ktt M a r (Real.pi / 2) ≠ 0 := by
  constructor
  · exact formC_Krr_equatorial M a r
  · rw [formC_Ktt_equatorial M a r hr.ne']
    exact sq_ne_zero_of_ne_zero ha.ne'

end
