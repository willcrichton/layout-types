/- Primitives for 2D objects. -/

import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.List.MinMax
import «LayoutTypes».Utils

abbrev Pos := ℚ × ℚ
@[simp] abbrev Pos.x (p : Pos) := p.1
@[simp] abbrev Pos.y (p : Pos) := p.2

abbrev Size := ℚ⁺ × ℚ⁺
@[simp] abbrev Size.w (s : Size) := s.1
@[simp] abbrev Size.h (s : Size) := s.2

instance : Coe (ℚ⁺ × ℚ⁺) (ℚ × ℚ) where
   coe := λ v => (v.fst, v.snd)

structure Region where
  lo : Pos
  hi : Pos
  lo_le_hi : lo ≤ hi
deriving Repr

-- def Region.asSet (r : Region) := Set.Ico r.lo r.hi
def Region.xs (r : Region) := Set.Ico r.lo.x r.hi.x
def Region.ys (r : Region) := Set.Ico r.lo.y r.hi.y
def Region.contains (r : Region) (p : Pos) := r.lo ≤ p ∧ p.fst < r.hi.fst ∧ p.snd < r.hi.snd
def Region.overlaps (r1 r2 : Region) := r1.contains r2.lo ∨ r1.contains r2.hi
def Region.disjoint (r1 r2 : Region) := ¬(r1.overlaps r2)

instance Region.instSup : Sup Region where
  sup := λ r1 r2 => ⟨r1.lo ⊓ r2.lo, r1.hi ⊔ r2.hi, by
    have h := r2.lo_le_hi
    simp [Prod.instLE_mathlib] at h
    simp [Prod.instSup, Prod.instInf]
    apply And.intro
    exact Or.intro_right _ (Or.intro_right _ h.left)
    exact Or.intro_right _ (Or.intro_right _ h.right)⟩

instance : SemilatticeSup Region := SemilatticeSup.mk'
  (by simp [Region.instSup, sup_comm, inf_comm])
  (by simp [Region.instSup, inf_assoc, sup_assoc])
  (by simp [Region.instSup])

structure Box where
  pos : Pos
  size : Size
deriving Repr

@[simp] instance zeroBox : Zero Box where
  zero := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩

theorem tuple_sub_pos {t1 t2 : ℚ × ℚ} (h_lt : t1 ≤ t2) : 0 ≤ t2 - t1 := by
  simp [Prod.instLE_mathlib] at *; apply And.intro <;> linarith

def regionSize (r : Region) : Size :=
  let size := r.hi - r.lo
  have : 0 ≤ size := tuple_sub_pos r.lo_le_hi
  have h_le_parts := Iff.mp Prod.le_def this
  (⟨size.fst, And.left h_le_parts⟩, ⟨size.snd, And.right h_le_parts⟩)

@[simp] instance boxEqRegion : Box ≃ Region where
  toFun := λ b => ⟨b.pos, b.pos + b.size, by simp [Prod.instLE_mathlib]⟩
  invFun := λ r => Box.mk r.lo (regionSize r)
  left_inv := by
    intros b; simp
    rw [Box.mk.injEq]; apply And.intro
    case left => rfl
    case right => simp [regionSize]; rfl
  right_inv := by
    intros r; simp
    rw [Region.mk.injEq]
    simp [regionSize]
    rw [Prod.mk.injEq]; apply And.intro
    all_goals simp

instance : Coe Box Region where coe := boxEqRegion.toFun
instance : Coe Region Box where coe := boxEqRegion.invFun

-- Lift a bunch of Region methods and instances onto Box using the isomorphism
@[simp] def boxReflCongr {α} := boxEqRegion.arrowCongr (Equiv.refl α)
@[simp] def boxRegionCongr := boxEqRegion.arrowCongr boxEqRegion
@[simp] def boxRegionCongr2 := boxEqRegion.arrowCongr boxRegionCongr
@[simp] def boxRegionReflCongr {α} := boxEqRegion.arrowCongr (@boxReflCongr α)
@[simp] def Box.xs := boxReflCongr.invFun Region.xs
@[simp] def Box.ys := boxReflCongr.invFun Region.ys
@[simp] def Box.lo := boxReflCongr.invFun Region.lo
@[simp] def Box.hi := boxReflCongr.invFun Region.hi

instance Box.instSup : Sup Box where sup := boxRegionCongr2.invFun (· ⊔ ·)
instance : SemilatticeSup Box := SemilatticeSup.mk'
  (by simp [Region.instSup, Box.instSup, sup_comm, inf_comm])
  (by simp [Region.instSup, Box.instSup, inf_assoc, sup_assoc, regionSize])
  (by simp [Region.instSup, Box.instSup, regionSize]; intro; rfl)
instance : LE Box where le := boxRegionReflCongr.invFun (· ≤ ·)

def Box.disjoint := boxRegionReflCongr.invFun Region.disjoint
-- def Box.disjoint_inf := boxRegionReflCongr.invFun NonemptyInterval.disjoint_inf

def boxMin (b : Box) (bs : List Box) : Pos :=
  let minX := bs.map (·.pos.x) |>.foldl min b.pos.x
  let minY := bs.map (·.pos.y) |>.foldl min b.pos.y
  ⟨minX, minY⟩

def boxMax (b : Box) (bs: List Box) : Pos :=
  let maxX := bs.map (·.hi.x) |>.foldl max b.hi.x
  let maxY := bs.map (·.hi.y) |>.foldl max b.hi.y
  ⟨maxX, maxY⟩

def boxCover (b : Box) (bs : List Box) : Box :=
  bs.foldl (· ⊔ ·) b

def Box.offset (b : Box) (p : Pos) : Box :=
  { b with pos := b.pos + p }
