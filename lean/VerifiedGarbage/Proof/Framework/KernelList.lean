import Mathlib.Util.CompileInductive

/-!
# List functions for the kernel

The kernel evaluates the taint analyses (`VG.Taint`), and is slow at the
library's list functions: they are structurally recursive, which compiles to
`brecOn`, and `==` and `≤` on `Nat` go through `Decidable` instances. The
functions here are the same functions written with `List.rec` and
`Nat.beq`/`Nat.ble` (which the kernel evaluates natively), each proven equal
to the library's, so that an analysis can be evaluated in these terms and
reasoned about in the library's. (`Mathlib.Util.CompileInductive` compiles
`List.rec`, for the analyses' hints, which are computed in compiled code.)
-/

namespace VG.KList

variable {α β : Type}

def any (l : List α) (p : α → Bool) : Bool := List.rec false (fun a _ ih => p a || ih) l

def all (l : List α) (p : α → Bool) : Bool := List.rec true (fun a _ ih => p a && ih) l

def filter (p : α → Bool) (l : List α) : List α :=
  List.rec [] (fun a _ ih => bif p a then a :: ih else ih) l

def find? (p : α → Bool) (l : List α) : Option α :=
  List.rec none (fun a _ ih => bif p a then some a else ih) l

def map (f : α → β) (l : List α) : List β := List.rec [] (fun a _ ih => f a :: ih) l

def append (xs ys : List α) : List α := List.rec ys (fun a _ ih => a :: ih) xs

theorem any_eq (l : List α) (p : α → Bool) : any l p = l.any p := by
  induction l <;> simp_all [any]

theorem all_eq (l : List α) (p : α → Bool) : all l p = l.all p := by
  induction l <;> simp_all [all]

theorem filter_eq (p : α → Bool) (l : List α) : filter p l = l.filter p := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp_all [filter]

theorem find?_eq (p : α → Bool) (l : List α) : find? p l = l.find? p := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp_all [find?]

theorem map_eq (f : α → β) (l : List α) : map f l = l.map f := by
  induction l <;> simp_all [map]

theorem append_eq (xs ys : List α) : append xs ys = xs ++ ys := by
  induction xs <;> simp_all [append]

theorem beq_eq (a b : Nat) : Nat.beq a b = (a == b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]

theorem ble_eq (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_iff]

end VG.KList
