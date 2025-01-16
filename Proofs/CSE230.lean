import Mathlib.Tactic

namespace MyBool
def my_max (a b : Nat) :=
  if a > b then a
  else b

#check my_max

inductive Bool where
    | false : Bool
    | true : Bool

def neg (b : Bool) :=
    match b with
    | Bool.false => Bool.true
    | Bool.true => Bool.false

theorem not_true_eq_false : (neg Bool.false) = Bool.true := rfl

theorem not_ne : ∀ (b : Bool), ¬(neg b = b) := by
    intro b
    -- <;> for all goals
    cases b -- <;> simp [not]
    case true =>
        intro h
        contradiction
    case false => exact λ h : neg Bool.false = Bool.false =>
        Bool.noConfusion h

theorem not_not_eq  : ∀ (b : Bool), neg (neg b) = b := by
    intro b
    cases b <;> rfl

def xor (b1 b2 : Bool) : Bool :=
    match b1, b2 with
    | Bool.true, Bool.false => Bool.true
    | Bool.false, Bool.true => Bool.true
    | _, _ => Bool.false

def xor_comm : ∀ (b1 b2 : Bool),  xor b1 b2 = xor b2 b1 := by
    intro b1 b2
    cases b1
    . case false =>
        cases b2
        rfl
        rfl
    . case true =>
        cases b2
        rfl
        rfl
    -- cases b1 <;>
    -- cases b2 <;> rfl
end MyBool

namespace MyNat
inductive Nat : Type where
| zero : Nat
| succ : Nat → Nat
deriving Repr

open Nat
def adder (n m : Nat) : Nat :=
    match n with
    | zero => m
    | succ n' => succ <| adder n' m

def one := succ zero
def two := succ one
def three := succ two
def four := succ three
def five := succ four
example : adder one two = three := by rfl


def zero_add (m: Nat) : adder zero m = m :=
    by rfl

def add_zero (m: Nat) : adder m zero = m := by
    induction m
    case zero => rfl
    case succ =>
        rename_i m' ih
        rw [adder]
        rw [ih]

        -- calc adder m'.succ zero
            -- _ = succ (adder m' zero) := by rfl
            -- _ = succ m' := by rw[ih]

theorem add_succ (n m : Nat) : adder m (succ n) = succ (adder m n) := by
    induction m
    . case zero => rfl
    . case succ m' ih =>
        simp [adder]
        rw [ih]

theorem add_comm (n m : Nat) : adder n m = adder m n := by
    induction n
    case zero => rw [add_zero, zero_add]
    case succ n' ih =>
        simp [adder, add_succ]
        exact ih

-- note that this can be
-- done using tail recursion, but regular add can't
def itadd (n m: Nat) : Nat :=
    match n with
    | zero => m
    | succ n' => itadd n' (succ m)

theorem add_eq_itadd : ∀ (n m: Nat), itadd n m = adder n m := by
    intro n m
    induction n generalizing m
    case zero =>
        rfl
    case succ n' ih =>
        simp[itadd, adder]
        simp[ih]
        simp[add_succ]

end MyNat

namespace MyList
inductive List (α: Type) where
    | nil: List α
    | cons: α → List α → List α
    deriving Repr
open List

variable {a: Type}
def myapp  (xs ys : List α) : List α :=
    match xs with
    | nil => ys
    | cons head xs' => cons head <| myapp xs' ys

theorem app_nil (α: Type) (xs : List α) : myapp xs nil = xs := by
    induction xs
    rfl
    case cons x xs ih =>
        rw [myapp, ih]

theorem app_assoc (xs ys zs : List α) : myapp (myapp xs ys) zs = myapp xs (myapp ys zs) := by
    induction xs
    case nil => rfl
    case cons x xs ih =>
        rw [myapp]
        simp [myapp]
        rw [ih]

def rev {α: Type} (xs : List α) : List α :=
    match xs with
    | nil => nil
    | cons x xs' => myapp (rev xs') (List.cons x nil)

theorem rev_app : ∀ {α: Type} (xs: List α) (ys: List α), rev (myapp xs ys) = myapp (rev ys) (rev xs) := by
    intro a xs ys
    induction xs
    case nil => simp[myapp, rev, app_nil]
    case cons x xs' ih =>
        simp[myapp, rev, app_nil, ih]
        simp[app_assoc]

theorem rev_rev : ∀ {α: Type} (xs: List α), rev (rev xs) = xs := by
    intros α xs
    induction xs
    case nil => rfl
    case cons x xs' ih =>
        simp [rev, myapp, rev_app]
        rw [ih]
end MyList

namespace MySum
def sum (n : Nat) : Nat :=
    match n with
    | 0 => 0
    | n' + 1 => n + sum n'

def tail_rec_sum (n res : Nat) : Nat :=
    match n with
    | 0 => res
    | n' + 1 => tail_rec_sum n' (res + n)

def tr_sum (n : Nat) : Nat := tail_rec_sum n 0


-- so typically the left hand side
-- should be converted to the right hand side
theorem tail_rec_sum_add : ∀ (n res: ℕ), tail_rec_sum n res = (sum n) + res := by
    intro n
    induction n
    case zero =>
        intro res
        simp[sum, tail_rec_sum]
    case succ n' ih =>
        intro res
        simp_arith[tail_rec_sum, sum, ih]
        -- rw [←ih (res + (n' + 1))]


theorem sum_eq_tr_sum : ∀ (n : Nat), sum n = tr_sum n := by
    intro n
    match n with
    | Nat.zero => rfl
    | Nat.succ n' =>
        simp[tr_sum, tail_rec_sum, sum]
        simp[tail_rec_sum_add, Nat.add_comm]
end MySum

namespace Aexp

inductive Aexp: Type where
| const : Nat → Aexp
| plus : Aexp → Aexp → Aexp
deriving Repr
open Aexp

def eval (e: Aexp) : Nat :=
    match e with
    | const c => c
    | plus u v => eval u + eval v

def eval_acc (e: Aexp) (acc: ℕ) : ℕ :=
    match e with
    | const c => c + acc
    | plus u v => eval_acc u (eval_acc v acc)

def eval' (e: Aexp) : Nat := eval_acc e 0

theorem eval_eq_eval_acc : ∀ (e: Aexp) (acc: Nat), eval_acc e acc = eval e + acc := by
    intro e n
    induction e generalizing n
    case const c => rfl
    case plus l r ihl ihr =>
        simp_arith[eval_acc, ihl, ihr, eval]

theorem eval_eq_eval' : ∀ (e: Aexp), eval e = eval' e := by
    simp[eval', eval_eq_eval_acc]

end Aexp
