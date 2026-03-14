import KerrFormalization.Kerr.ComponentLemmas
import Mathlib.Data.Set.Basic

/-!
# Kerr ergoregion and ergosphere

Definitions and basic component-level lemmas for the Kerr ergoregion in
Boyer-Lindquist coordinates.
-/

namespace KerrFormalization
namespace Kerr

open LocalCoordinates

/-- Kerr ergoregion: the set where `g_tt > 0`. -/
def ergoregion (M a : ℝ) : Set (CoordinateSpace 4) :=
  {x | gttField M a x > 0}

/-- Kerr ergosphere: the set where `g_tt = 0`. -/
def ergosphere (M a : ℝ) : Set (CoordinateSpace 4) :=
  {x | gttField M a x = 0}

@[simp] theorem mem_ergoregion_iff (M a : ℝ) (x : CoordinateSpace 4) :
    x ∈ ergoregion M a ↔ gttField M a x > 0 := Iff.rfl

@[simp] theorem mem_ergosphere_iff (M a : ℝ) (x : CoordinateSpace 4) :
    x ∈ ergosphere M a ↔ gttField M a x = 0 := Iff.rfl

/-- Useful rewrite: `g_tt = (2 M r / Σ) - 1`. -/
theorem gtt_eq_ratio_minus_one (M a : ℝ) (x : CoordinateSpace 4) :
    gttField M a x = (2 * M * x rIdx) / sigma a (x rIdx) (x thetaIdx) - 1 := by
  simp [gttField]

/-- Ergoregion criterion in Boyer-Lindquist coordinates. -/
theorem mem_ergoregion_iff_ratio_gt_one (M a : ℝ) (x : CoordinateSpace 4) :
    x ∈ ergoregion M a ↔
      1 < (2 * M * x rIdx) / sigma a (x rIdx) (x thetaIdx) := by
  rw [mem_ergoregion_iff, gtt_eq_ratio_minus_one]
  constructor <;> intro h <;> linarith [h]

/-- Ergosphere criterion in Boyer-Lindquist coordinates. -/
theorem mem_ergosphere_iff_ratio_eq_one (M a : ℝ) (x : CoordinateSpace 4) :
    x ∈ ergosphere M a ↔
      (2 * M * x rIdx) / sigma a (x rIdx) (x thetaIdx) = 1 := by
  rw [mem_ergosphere_iff, gtt_eq_ratio_minus_one]
  constructor <;> intro h <;> linarith [h]

/-- Points in the ergoregion are not on the ergosphere. -/
theorem ergoregion_disjoint_ergosphere_pointwise (M a : ℝ) (x : CoordinateSpace 4)
    (hx : x ∈ ergoregion M a) :
    x ∉ ergosphere M a := by
  intro hxSphere
  rw [mem_ergoregion_iff] at hx
  rw [mem_ergosphere_iff] at hxSphere
  linarith

/-- Equivalent sign test for non-membership in the ergoregion. -/
theorem not_mem_ergoregion_iff (M a : ℝ) (x : CoordinateSpace 4) :
    x ∉ ergoregion M a ↔ gttField M a x ≤ 0 := by
  rw [mem_ergoregion_iff]
  exact not_lt

end Kerr
end KerrFormalization
