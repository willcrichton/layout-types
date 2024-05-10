import Mathlib.Data.NNRat.Defs
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Linarith.Frontend

notation "ℚ⁺" => NNRat

abbrev Pos := ℚ × ℚ
@[simp] abbrev Pos.x (p : Pos) := p.1
@[simp] abbrev Pos.y (p : Pos) := p.2

abbrev Size := ℚ⁺ × ℚ⁺
@[simp] abbrev Size.w (s : Size) := s.1
@[simp] abbrev Size.h (s : Size) := s.2

instance : Coe (ℚ⁺ × ℚ⁺) (ℚ × ℚ) where
   coe := λ v => (v.fst, v.snd)

abbrev Region := NonemptyInterval Pos
@[simp] abbrev Region.lo (r : Region) := r.fst
@[simp] abbrev Region.hi (r : Region) := r.snd
def Region.xs (r : Region) : NonemptyInterval ℚ := NonemptyInterval.mk (r.lo.x, r.hi.x) (by
  have := r.fst_le_snd
  simp [LE.le] at *
  exact this.left)
def Region.ys (r : Region) := NonemptyInterval.mk (r.lo.y, r.hi.y) (by
  have := r.fst_le_snd
  simp [LE.le] at *
  exact this.right)

def NonemptyInterval.disjoint {α} [LE α] (i1 i2 : NonemptyInterval α) : Prop :=
  ¬(i1.fst ≤ i2.snd) ∨ ¬(i2.fst ≤ i1.snd)

def NonemptyInterval.disjoint_inf {α} [Lattice α] [@DecidableRel α (· ≤ ·)] (i1 i2 : NonemptyInterval α) : Prop :=
  (WithBot.some i1) ⊓ (WithBot.some i2) = ⊥

structure Box where
  pos : Pos
  size : Size

instance zeroBox : Zero Box where
  zero := ⟨0, 0⟩

theorem tuple_sub_pos {t1 t2 : ℚ × ℚ} (h_lt : t1 ≤ t2) : 0 ≤ t2 - t1 := by
  simp [Prod.instLE_mathlib] at *; apply And.intro <;> linarith

def regionSize (r : Region) : Size :=
  let size := r.snd - r.fst
  have : 0 ≤ size := tuple_sub_pos r.fst_le_snd
  have h_le_parts := Iff.mp Prod.le_def this
  (⟨size.fst, And.left h_le_parts⟩, ⟨size.snd, And.right h_le_parts⟩)

@[simp]
instance boxEqRegion : Box ≃ Region where
  toFun := λ b => ⟨(b.pos, b.pos + b.size), by simp [Prod.instLE_mathlib]⟩
  invFun := λ r => Box.mk r.fst (regionSize r)
  left_inv := by
    intros b; simp
    rw [Box.mk.injEq]; apply And.intro
    case left => rfl
    case right => simp [regionSize]; rfl
  right_inv := by
    intros r; simp
    rw [NonemptyInterval.mk.injEq]
    simp [regionSize]
    rw [Prod.mk.injEq]; apply And.intro
    case left => simp
    case right =>
      rw [Prod.mk.injEq]; apply And.intro
      all_goals simp

instance : Coe Box Region where coe := boxEqRegion.toFun
instance : Coe Region Box where coe := boxEqRegion.invFun

@[simp] def boxReflCongr {α} := boxEqRegion.arrowCongr (Equiv.refl α)
@[simp] def boxRegionCongr := boxEqRegion.arrowCongr boxEqRegion
@[simp] def boxRegionCongr2 := boxEqRegion.arrowCongr boxRegionCongr
@[simp] def boxRegionReflCongr {α} := boxEqRegion.arrowCongr (@boxReflCongr α)
@[simp] def Box.xs := boxReflCongr.invFun Region.xs
@[simp] def Box.ys := boxReflCongr.invFun Region.ys
@[simp] def Box.lo := boxReflCongr.invFun Region.lo
@[simp] def Box.hi := boxReflCongr.invFun Region.hi

instance boxSup : Sup Box where sup := boxRegionCongr2.invFun (· ⊔ ·)
instance : SemilatticeSup Box := SemilatticeSup.mk'
  (by simp [boxSup, sup_comm])
  (by simp [boxSup, inf_assoc, sup_assoc, regionSize])
  (by simp [boxSup, regionSize]; intro; rfl)
instance : LE Box where le := boxRegionReflCongr.invFun (· ≤ ·)

def Box.disjoint := boxRegionReflCongr.invFun NonemptyInterval.disjoint
def Box.disjoint_inf := boxRegionReflCongr.invFun NonemptyInterval.disjoint_inf

def boxCover (boxes : List Box) :=
  boxes.foldl (· ⊔ ·) 0

def Box.offset (b : Box) (p : Pos) : Box :=
  { b with pos := b.pos + p }
