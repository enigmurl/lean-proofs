structure Color where
  (red : Nat) (green : Nat) (blue : Nat)
  deriving Repr

inductive K
| mk (red: Nat) (green: Nat) (blue: Nat) : K

def k_red (k : K) : Nat :=
  match k with
  | K.mk r _ _ => r

def compose (α β γ : Type) (f: α → Option β) (g: β → Option γ) : (α → Option γ) :=
  fun a => match f a with
  | Option.some b => g b
  | Option.none => Option.none

def nat_inhabited : Inhabited Nat := Inhabited.mk 0
def bool_inhabited : Inhabited Bool := Inhabited.mk false

def prod_inhabited {α β : Type} (a: Inhabited α) (b: Inhabited β) : Inhabited (α × β) :=
  Inhabited.mk (Prod.mk a.default b.default)

def func_inhabited {α β : Type} (a: Inhabited α) : Inhabited (β → α) :=
  Inhabited.mk (fun _ => a.default)

def y := K.mk 255 255 0
def yellow := Color.mk 255 255 0

-- #eval Color.red yellow

namespace Hidden
inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α
namespace List
def append (as bs : List α) : List α :=
 match as with
 | nil       => bs
 | cons a as => cons a (append as bs)
theorem nil_append (as : List α) : append nil as = as :=
 rfl
theorem cons_append (a : α) (as bs : List α)
                    : List.append (cons a as) bs = cons a (append as bs) :=
 rfl

theorem append_nil (as : List α) : append as nil = as :=
  List.recOn (motive := fun x => append x nil = x)
      as
      (show append nil nil = nil from rfl)
      (fun (a: α) (l1: List α) (ih: append l1 nil = l1) =>
        show append (cons a l1) nil = (cons a l1) from
          calc append (cons a l1) nil
            _ = cons a (append l1 nil) := rfl
            _ = cons a l1 := by rw [ih]
      )
def length {α : Type u} (as : List α) : Nat :=
  match as with
  | nil => 0
  | cons _ bs => Nat.succ (length bs)

theorem length_concat {α : Type u} (as bs : List α) : length (append as bs) = length as + length bs :=
  List.recOn (motive := fun l => length (append l bs) = length l + length bs)
    as
    (calc (nil.append bs).length
      _ = (bs.length) := by rw [nil_append]
      _ = bs.length + 0 := rfl
      _ = bs.length + nil.length := rfl
      _ = nil.length + bs.length := by rw [Nat.add_comm]
    )
    (fun (a: α) (as : List α) (ih: length (append as bs) = length as + length bs) =>
        calc length (append (cons a as) bs)
          _ = length (cons a (append as bs)) := rfl
          _ = Nat.succ (length (append as bs)) := rfl
          _ = Nat.succ (length as + length bs) := by rw [ih]
          _ = Nat.succ (length bs + length as) := by rw [Nat.add_comm]
          _ = length bs + Nat.succ (length as) := by rw [Nat.add_succ]
          _ = Nat.succ (length as) + length bs:= by rw [Nat.add_comm]
          _ = length (cons a as) + length bs := rfl
    )

end List
end Hidden
