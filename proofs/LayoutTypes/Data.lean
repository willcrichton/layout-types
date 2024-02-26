import Mathlib.Data.Real.Basic

structure PosReal where
  val : ℝ
  isPos : val ≥ 0

notation "ℝ⁺" => PosReal

instance : Coe ℝ⁺ ℝ where
  coe x := x.val

structure Interval where
  lo : ℝ
  hi : ℝ

def Interval.disjoint (i1 i2 : Interval) : Prop :=
  i1.lo ≥ i2.hi ∨ i1.hi ≤ i2.lo

structure Vec2 where
  x : ℝ
  y : ℝ

structure Size where
  size : Vec2
  positive : size.x ≥ 0 ∧ size.y ≥ 0

def Size.w (s : Size) : ℝ := s.size.x
def Size.h (s : Size) : ℝ := s.size.y

structure Box where
  pos : Vec2
  size : Size

def Box.disjoint (b1 b2 : Box) : Prop :=
  let b1w := Interval.mk b1.pos.x (b1.pos.x + b1.size.w)
  let b1h := Interval.mk b1.pos.y (b1.pos.y + b1.size.h)
  let b2w := Interval.mk b2.pos.x (b2.pos.x + b2.size.w)
  let b2h := Interval.mk b2.pos.y (b2.pos.y + b2.size.h)
  (b1w.disjoint b2w) ∨ (b1h.disjoint b2h)

structure Para where
  contents : String
  font_size : ℝ⁺
  line_height : ℝ⁺
