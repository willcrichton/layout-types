import Mathlib.Data.List.Basic
import Mathlib.Data.List.Zip
import Mathlib.Data.List.BigOperators.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LiftLets
-- import LeanCopilot

import «LayoutTypes».Data
import «LayoutTypes».Layout

lemma scaled_lt_preserves_le {n1 n2 : ℕ} {x: ℝ} {r : ℝ⁺}
  (h_n_le : n1 < n2) (h_x_le : r ≥ x)
  : n1 * r  + x ≤ n2 * r := by
  have h : (↑n1 + (1 : ℝ)) ≤ ↑n2 := by norm_cast
  have : (↑n1 + 1) * (r : ℝ) ≤ n2 * r := mul_le_mul_of_nonneg_right h (by simp)
  linarith

def boxes_disjoint (boxes : List Box) :=
  ∀ (n1 n2 : Fin boxes.length), n1 < n2 → (boxes.get n1).disjoint (boxes.get n2)

def intervals_disjoint (intervals : List Interval) :=
  ∀ (i1 i2 : Fin intervals.length), i1 < i2 → (intervals.get i1).disjoint (intervals.get i2)

def height_intervals (sizes_at_y : List (Size × ℝ)) :=
  sizes_at_y.map λ (size, y) => Interval.mk y (y + size.h)

theorem vert_layout_disjoint {sizes_at_y : List (Size × ℝ)}
  (h_intv_disjoint : intervals_disjoint (height_intervals sizes_at_y))
  : boxes_disjoint (vert_layout sizes_at_y)
  := by
  let boxes := vert_layout sizes_at_y
  unfold boxes_disjoint; intros n1 n2 hneq
  simp [vert_layout, Box.disjoint]; apply Or.inr

  have : sizes_at_y.length = boxes.length := by simp [vert_layout]
  let n1' : Fin sizes_at_y.length := ⟨n1, by simp [*]⟩
  let n2' : Fin sizes_at_y.length := ⟨n2, by simp [*]⟩
  let t1 := sizes_at_y.get n1'; let size1 := t1.1; let y1 := t1.2
  let t2 := sizes_at_y.get n2'; let size2 := t2.1; let y2 := t2.2
  let i1 := Interval.mk y1 (y1 + size1.h)
  let i2 := Interval.mk y2 (y2 + size2.h)
  show i1.disjoint i2

  let intvls := height_intervals sizes_at_y
  let n1'' : Fin intvls.length := ⟨n1, by simp [*, height_intervals]⟩
  let n2'' : Fin intvls.length := ⟨n2, by simp [*, height_intervals]⟩
  have h1 : i1 = intvls.get n1''  := by simp [*, height_intervals]
  have h2 : i2 = intvls.get n2'' := by simp [*, height_intervals]
  rw [h1, h2]
  exact h_intv_disjoint n1'' n2'' (by simp [*])

theorem vert_layout_scaled_disjoint (sizes : List Size) (scale : ℝ⁺)
  (h_size_bounded : ∀ s ∈ sizes, scale ≥ s.h)
  : boxes_disjoint (vert_layout_scaled sizes scale)
  := by
  simp [vert_layout_scaled]
  apply vert_layout_disjoint
  simp [intervals_disjoint]
  intros n1 n2 h_lt

  let sizes_at_y := sizes.enum.map λ (idx, size) => (size, (idx : ℝ) * scale)
  have : sizes.length = (height_intervals sizes_at_y).length := by simp [*, height_intervals]
  let n1_enum : Fin sizes.enum.length := ⟨n1, by simp [*]⟩
  let n2_enum : Fin sizes.enum.length := ⟨n2, by simp [*]⟩
  simp [
    intervals_disjoint, height_intervals, Interval.disjoint, Size.h,
    sizes.get_enum n1_enum, sizes.get_enum n2_enum
  ]
  let n1_sizes : Fin sizes.length := ⟨n1, by simp [*]⟩
  apply Or.inr
  apply scaled_lt_preserves_le h_lt
  apply h_size_bounded; apply List.get_mem sizes n1_sizes

theorem foo {a b c d : ℝ} (h1 : a ≤ b) (h2 : b + c ≤ d) : a + c ≤ d := by linarith

theorem vert_layout_fluid_disjoint (sizes : List Size)
  : boxes_disjoint (vert_layout_fluid sizes)
  := by
  simp [vert_layout_fluid]
  apply vert_layout_disjoint
  simp [height_intervals, prefix_sums, List.zip, List.map_zipWith, List.zipWith_map_right]
  simp [intervals_disjoint, Interval.disjoint]
  intros i1 i2 h_lt; apply Or.intro_right; simp [Coe.coe]; norm_cast

  let heights := sizes.map Size.h
  let intervals := List.zipWith (fun s i =>
    Interval.mk
      (Coe.coe (heights.take i).sum)
      (Coe.coe (heights.take i).sum + s.h))
    sizes (List.range sizes.length)

  have : i1 < sizes.length := by
    have : intervals.length = sizes.length := by simp
    linarith [i1.isLt]

  have h_take_i1_eq := heights.sum_take_succ i1 (by simp [*])
  simp at h_take_i1_eq
  rw [←h_take_i1_eq]

  apply heights.monotone_sum_take
  have := Iff.mp Fin.lt_iff_val_lt_val h_lt
  linarith

-- theorem Layout.para_disjoint (l : Layout) (p : Para)
--   (h_height_ge_font : (p.line_height : ℝ) ≥ p.font_size)
--   : boxes_disjoint (l.para p)
--   := by
--   simp [Layout.para]
--   let wrapped : WrappedLines p.font_size := l.wrapper p.contents p.font_size
--   have height_bounded : ∀ s ∈ wrapped.lines, (p.line_height : ℝ) ≥ s.h := by
--     intros s s_in; have := wrapped.height_bounded s s_in; linarith
--   exact vert_layout_scaled_disjoint height_bounded
