

def compose.{u, v, w} {α : Type u} {β : Type v} {γ : Type w}
  (f : α → Option β) (g : β → Option γ) (x : α) : Option γ :=
  match f x with
    | some b => g b
    | none   => none


def boolInhabited : Inhabited Bool := ⟨true⟩


def natInhabited : Inhabited Nat := ⟨0⟩


def prodInhabited.{u, v} {α : Type u} {β : Type v}
  [Inhabited α] [Inhabited β] : Inhabited (α × β) :=
  ⟨default, default⟩
