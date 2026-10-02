/-!
# Abstract domains for straight-line bitwise code

Straight-line code that only moves words around and combines them with
bitwise operations, rotations, logical shifts and constants (bitsliced
code, bit-matrix transposes, …) can be checked by *evaluating* it over an
abstract domain instead of symbolically executing it. A `Dom α w` gives
the abstract version of each operation on `w`-bit words (`none` when the
domain cannot represent the result), and `Dom.Sound R` says that the
abstract operations track the concrete ones through the relation `R`
between abstract and concrete words. Each ISA's evaluator
(`Framework/<ISA>/Straight.lean`) runs its instructions over any sound
domain; `Framework/Bitslice/Table.lean` and `Lanes.lean` have the domains.
-/

namespace VG.Bitslice

/-- The abstract versions of the operations of bitwise straight-line code
on `w`-bit words; `none` when the domain cannot represent the result. -/
structure Dom (α : Type) (w : Nat) where
  xor : α → α → Option α
  and : α → α → Option α
  or : α → α → Option α
  /-- Rotation right by a count. -/
  ror : Nat → α → Option α
  /-- Logical shift right by a count. -/
  shr : Nat → α → Option α
  const : BitVec w → Option α

/-- The abstract operations track the concrete ones through `R`. -/
structure Dom.Sound {α : Type} {w : Nat} (D : Dom α w) (R : α → BitVec w → Prop) : Prop where
  xor : ∀ {a b c : α} {x y : BitVec w}, R a x → R b y → D.xor a b = some c → R c (x ^^^ y)
  and : ∀ {a b c : α} {x y : BitVec w}, R a x → R b y → D.and a b = some c → R c (x &&& y)
  or : ∀ {a b c : α} {x y : BitVec w}, R a x → R b y → D.or a b = some c → R c (x ||| y)
  ror : ∀ {n : Nat} {a c : α} {x : BitVec w}, R a x → D.ror n a = some c → R c (x.rotateRight n)
  shr : ∀ {n : Nat} {a c : α} {x : BitVec w}, R a x → D.shr n a = some c → R c (x >>> n)
  const : ∀ {v : BitVec w} {c : α}, D.const v = some c → R c v

end VG.Bitslice
