-- NONOS Operating System (AGPL-3.0-or-later)

/-!
What a wiring class forces, and what classes over one cell forget.

The circuit ties cells that must be equal with a permutation: the grand product
forces every cell of a cycle equal. A binding therefore holds exactly when its
cells share a cycle, and what has to be checked is the layer below the product,
which lays the classes into that permutation.

Laying a class rotates its cells into one cycle. Laying further classes over a
cell that already carries an image rewrites it, and a cell can be rotated out
to a fixed point: it is then on no cycle with anything and the binding that was
meant to hold it is gone, silently, while every other binding still holds. The
published note root over both inputs' terminals is emitted as one class for
this reason rather than as one class per input.
-/

namespace Shield.Wiring

abbrev Cell := Nat

/-- Where each cell is sent. The identity ties nothing. -/
abbrev Sigma := Cell → Cell

/-- Send `a` to `b` and leave every other cell where it was. -/
def link (s : Sigma) (a b : Cell) : Sigma :=
  fun x => if x = a then b else s x

/-- The last cell of a non-empty class. -/
def lastOf (a : Cell) : List Cell → Cell
  | [] => a
  | b :: rest => lastOf b rest

/-- Each cell takes the image of the next, read from the permutation as it
stood before the class was laid. -/
def shift (s t : Sigma) : List Cell → Sigma
  | [] => t
  | [_] => t
  | x :: y :: rest => shift s (link t x (s y)) (y :: rest)

/-- One class laid over `s`: the cells rotate, and the last takes what the
first was holding. This is `wire_pack::build`, one class at a time. -/
def apply (s : Sigma) : List Cell → Sigma
  | [] => s
  | a :: rest => shift s (link s (lastOf a rest) (s a)) (a :: rest)

/-- A class laid over nothing. -/
def cls (cells : List Cell) : Sigma := apply id cells

/-- A class of two ties its pair: each cell is sent to the other. -/
theorem a_pair_is_a_two_cycle : cls [0, 1] 0 = 1 ∧ cls [0, 1] 1 = 0 :=
  ⟨rfl, rfl⟩

/-- A class of three ties all three: the cycle reaches every cell and returns,
which is what makes the product force them equal. This is the shape the note
root takes over the published word and both inputs' walked terminals. -/
theorem a_triple_is_one_cycle :
    cls [0, 1, 2] 0 = 1 ∧ cls [0, 1, 2] 1 = 2 ∧ cls [0, 1, 2] 2 = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- Every cell of the class is reached from the first, so none is left out. -/
theorem a_triple_reaches_every_cell :
    cls [0, 1, 2] 0 = 1 ∧ cls [0, 1, 2] (cls [0, 1, 2] 0) = 2 :=
  ⟨rfl, rfl⟩

/-- A cell no class names keeps its image, so laying a class costs nothing
outside it. -/
theorem an_untouched_cell_is_unmoved : cls [0, 1, 2] 7 = 7 := rfl

/-- The same three cells tied pairwise instead: first and second, second and
third, then first and third. Every pair is true and the third is implied by the
other two, which is what makes it look harmless. -/
def pairwise : Sigma := apply (apply (apply id [0, 1]) [1, 2]) [0, 2]

/-- The first cell is rotated out to a fixed point. It is on no cycle with
anything, so nothing forces it equal to the cells it was tied to, and no error
is raised anywhere. -/
theorem a_redundant_class_drops_a_binding : pairwise 0 = 0 := rfl

/-- The other two are left tied to each other alone. -/
theorem the_survivors_hold_only_each_other :
    pairwise 1 = 2 ∧ pairwise 2 = 1 :=
  ⟨rfl, rfl⟩

end Shield.Wiring
