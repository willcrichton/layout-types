import «Layout».Space
import «Layout».Element

def vstackAt {α} [Bounded α] [Positioned α] (y : ℚ) (els : List α) : List α :=
  match els with
  | [] => []
  | el :: els =>
    let el' := Positioned.setPos el !![0, y]
    let y' := y + (Bounded.bounds el).size.h
    el' :: vstackAt y' els

def vstack {α} [Bounded α] [Positioned α] (els : List α) : List α := vstackAt 0 els

def hstackAt {α} [Bounded α] [Positioned α] (x : ℚ) (els : List α) : List α :=
  match els with
  | [] => []
  | el :: els =>
    let el' := Positioned.setPos el !![x, 0]
    let x' := x + (Bounded.bounds el).size.w
    el' :: hstackAt x' els

def hstack {α} [Bounded α] [Positioned α] (els : List α) : List α := hstackAt 0 els


#html
  open Element in
  let els := [
    text {
      pos := !![0, 0],
      s := "Hello world",
      style := {fontSize := 12, bold := false}
    },
    text {
      pos := !![0, 0],
      s := "Lorem ipsum dolor sit amet",
      style := {fontSize := 12, bold := false}
    }
  ]
  let root := Element.frame (Frame.mk !![0, 0] (vstack els))
  toSvg root 100 100
