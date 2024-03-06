import Mathlib.Data.Real.NNReal

notation "ℝ⁺" => NNReal

structure Interval where
  lo : ℝ
  hi : ℝ

def Interval.disjoint (i1 i2 : Interval) : Prop :=
  i1.lo ≥ i2.hi ∨ i1.hi ≤ i2.lo

structure Vec2 where
  x : ℝ
  y : ℝ

structure Size where
  w : ℝ⁺
  h : ℝ⁺

structure Box where
  pos : Vec2
  size : Size

def Box.x_interval (b : Box) := Interval.mk b.pos.x (b.pos.x + b.size.w)
def Box.y_interval (b : Box) := Interval.mk b.pos.y (b.pos.y + b.size.h)

def Box.disjoint (b1 b2 : Box) :=
  (b1.x_interval.disjoint b2.x_interval) ∨
  (b1.y_interval.disjoint b2.y_interval)

structure BoxGroup (α : Type) where
  box : Box
  children : List α

inductive Element
  | atom (b : Box)
  | group (g : BoxGroup Element)

-- TODO: PICK BACK UP FROM HERE
-- . refactor layout algorithms to return Elements instead of Boxes
-- . figure out exactly how to handle relative coordinates when wrapping elements into Groups
-- . implement fluid layout for blocks
-- . prove the whole thing correct
-- . replace the Interval structure with one of the mathlib intervals??

def Element.box
  | atom b => b
  | group g => g.box

structure Para where
  contents : String
  font_size : ℝ⁺
  line_height : ℝ⁺

inductive Block where
  | para (p : Para)

structure Document where
  blocks : List Block
