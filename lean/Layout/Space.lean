import Mathlib.Data.Rat.Init
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation

abbrev Vector (n : ℕ) := Matrix (Fin 1) (Fin n)
abbrev Vector.nth {n α} (v : Vector n α) := v 0
abbrev Pos := Vector 2 ℚ
abbrev Pos.x (p : Pos) := p.nth 0
abbrev Pos.y (p : Pos) := p.nth 1

instance : Repr Pos where
  reprPrec p _ := f!"({p.x}, {p.y})"

instance : Min Pos where
  min p1 p2 := !![min p1.x p2.x, min p1.y p2.y]

instance : Max Pos where
  max p1 p2 := !![max p1.x p2.x, max p1.y p2.y]


abbrev Size := Vector 2 ℚ
abbrev Size.w (s : Size) := s.nth 0
abbrev Size.h (s : Size) := s.nth 1

structure Rect where
  pos : Pos
  size : Size

instance : Zero Rect where
  zero := {pos := !![0, 0], size := !![0, 0]}

def Rect.endpoint (r : Rect) : Pos :=
  r.pos + r.size

def Rect.union (r1 r2 : Rect) : Rect :=
  let pos := min r1.pos r2.pos
  let endpoint := max r1.endpoint r2.endpoint
  let size := endpoint - pos
  { pos, size }

class Bounded (α : Type) where
  bounds : α → Rect

class Positioned (α : Type) where
  pos : α → Pos
  setPos : α → Pos → α
