import VerifiedGarbage.Impl.Mont.X86_64

/-!
# Short Weierstrass curves on x86-64: points, scalar multiplication, powers

Code for any curve `y² = x³ + ax + b` over a prime field of `n` 64-bit
words, with the Montgomery arithmetic of `Impl/Mont/X86_64.lean`. Field
elements are in Montgomery form (`x R mod p`, `R = 2^(64 n)`) in slots of
the working space; a point is three slots, projective coordinates
`(X : Y : Z)`.

* `rcb`: the sum of two points by the complete formulas of Renes, Costello
  and Batina (Algorithm 1, any `a`), in their 40 steps, as field operations
  on slots (`FOp`); the curve's `a` and `3b` are slots too.
* `ladder`: `[k]G` by double-and-add from the top bit, 256 times (or as many
  bits as the table has): `D = R + R`, `S = D + G` and `R = D` or `S` by a
  mask of the bit, so every iteration does the same.
* `pow`: `x^e` by square-and-multiply over the bits of a public exponent,
  also always multiplying and selecting by a mask, so that one loop serves
  every exponent.
* `bits`: the bits of a little-endian number in a slot, one byte each.

The only branches are on loop counters, and every address is `rdi` plus a
constant, or plus a counter: nothing but `rdi` may affect timing.
-/

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont.X86_64

/-- A field operation on slots (byte offsets of the working space). -/
inductive FOp
  | mul (o a b : Nat)
  | add (o a b : Nat)
  | sub (o a b : Nat)

def FOp.code (M : Mod) : FOp → List Instr
  | .mul o a b => Mont.X86_64.mul M o a b
  | .add o a b => Mont.X86_64.add M o a b
  | .sub o a b => Mont.X86_64.sub M o a b

/-- A straight-line sequence of field operations. -/
def fprog (M : Mod) (ops : List FOp) : List Instr := ops.flatMap (FOp.code M)

/-- Straight-line code as a sequence of blocks (the same instructions as their
concatenation; the kernel handles many short blocks better than one long one). -/
def blocks : List (List Instr) → Prog isa
  | [] => .block []
  | [b] => .block b
  | b :: bs => .seq (.block b) (blocks bs)

/-- `fprog`, a block per operation. -/
def fprogB (M : Mod) (ops : List FOp) : Prog isa := blocks (ops.map (FOp.code M))

/-- A point: the slots of its three coordinates. -/
structure Pt where
  x : Nat
  y : Nat
  z : Nat

/-- The slots the complete addition uses: the curve's `a` and `3b`, and six
temporaries. -/
structure RcbSlots where
  a : Nat
  b3 : Nat
  t0 : Nat
  t1 : Nat
  t2 : Nat
  t3 : Nat
  t4 : Nat
  t5 : Nat

/-- `o = p + q` (Algorithm 1 of Renes, Costello and Batina, in its stated
order; `o`'s slots are written as temporaries too, so they must be apart
from `p`'s and `q`'s). -/
def rcb (S : RcbSlots) (p q o : Pt) : List FOp :=
  [.mul S.t0 p.x q.x, .mul S.t1 p.y q.y, .mul S.t2 p.z q.z,
    .add S.t3 p.x p.y, .add S.t4 q.x q.y, .mul S.t3 S.t3 S.t4,
    .add S.t4 S.t0 S.t1, .sub S.t3 S.t3 S.t4, .add S.t4 p.x p.z,
    .add S.t5 q.x q.z, .mul S.t4 S.t4 S.t5, .add S.t5 S.t0 S.t2,
    .sub S.t4 S.t4 S.t5, .add S.t5 p.y p.z, .add o.x q.y q.z,
    .mul S.t5 S.t5 o.x, .add o.x S.t1 S.t2, .sub S.t5 S.t5 o.x,
    .mul o.z S.a S.t4, .mul o.x S.b3 S.t2, .add o.z o.x o.z,
    .sub o.x S.t1 o.z, .add o.z S.t1 o.z, .mul o.y o.x o.z,
    .add S.t1 S.t0 S.t0, .add S.t1 S.t1 S.t0, .mul S.t2 S.a S.t2,
    .mul S.t4 S.b3 S.t4, .add S.t1 S.t1 S.t2, .sub S.t2 S.t0 S.t2,
    .mul S.t2 S.a S.t2, .add S.t4 S.t4 S.t2, .mul S.t0 S.t1 S.t4,
    .add o.y o.y S.t0, .mul S.t0 S.t5 S.t4, .mul o.x S.t3 o.x,
    .sub o.x o.x S.t0, .mul S.t0 S.t3 S.t1, .mul o.z S.t5 o.z,
    .add o.z o.z S.t0]

/-- `[o] = [a]` if the mask `rcx` is zero, `[b]` if it is all ones, `n`
words, through `rax` and `rdx`. -/
def sel : Nat → Nat → Nat → Nat → List Instr
  | 0, _, _, _ => []
  | k + 1, o, a, b => [.mov .rax (.mem (sc a)), .mov .rdx (.mem (sc b)), .alu .xor .rdx (.reg .rax),
      .alu .and .rdx (.reg .rcx), .alu .xor .rax (.reg .rdx), .store (sc o) .rax] ++
      sel k (o + 8) (a + 8) (b + 8)

/-- `o = a` or `b`, a point, by the mask `rcx`. -/
def selPt (n : Nat) (o a b : Pt) : List Instr :=
  sel n o.x a.x b.x ++ sel n o.y a.y b.y ++ sel n o.z a.z b.z

/-- `[o] = [a]`, `n` words, through `rax`. -/
def copy : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, o, a => [.mov .rax (.mem (sc a)), .store (sc o) .rax] ++ copy k (o + 8) (a + 8)

/-- `[rdi + rbx + d]`: byte `rbx` of a table at `d`. -/
def tbl (d : Nat) : MemOp := { base := .rdi, index := some .rbx, disp := d }

/-- The mask `rcx = -[rdi + rbx + d]` of the bit of iteration `rbx`. -/
def bitMask (d : Nat) : List Instr :=
  [.movzx8 .rax (tbl d), .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax)]

/-- What scalar multiplication needs: the field, the slots of `G` and of the
points, the slots of the complete addition, and the table of the scalar's
bits (byte `t` is bit `t`), with `nbits` bits. -/
structure LadderCfg where
  M : Mod
  S : RcbSlots
  G : Pt
  R : Pt
  D : Pt
  T : Pt
  bits : Nat
  nbits : Nat

/-- One iteration of the ladder, for the bit `t = rbx - 1`: `D = R + R`,
`T = D + G`, then `R = T` if bit `t` is set, else `D`. -/
def ladderBody (L : LadderCfg) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <| .seq (fprogB L.M (rcb L.S L.R L.R L.D)) <|
    .seq (fprogB L.M (rcb L.S L.D L.G L.T)) <|
    .block (bitMask L.bits ++ selPt L.M.n L.R L.D L.T ++ [.alu .test .rbx (.reg .rbx)])

/-- The ladder over the bits `nbits - 1` down to 0, from `R` as set up by the
caller (the point at infinity). -/
def ladder (L : LadderCfg) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 L.nbits))]) (.loop (ladderBody L) .ne)

/-- What a power needs: the modulus, the slots of the accumulator, of a
temporary, of the base and of `R mod m` (Montgomery's one), and the table of
the exponent's bits, with `nbits` bits. -/
structure PowCfg where
  M : Mod
  acc : Nat
  tmp : Nat
  base : Nat
  one : Nat
  bits : Nat
  nbits : Nat

/-- One iteration: `acc = acc²`, `tmp = acc · base`, and `acc = tmp` if the
exponent's bit `rbx - 1` is set. -/
def powBody (P : PowCfg) : Prog isa :=
  .seq (.block ([.alu .sub .rbx (.imm 1)] ++ Mont.X86_64.mul P.M P.acc P.acc P.acc)) <|
  .seq (.block (Mont.X86_64.mul P.M P.tmp P.acc P.base)) <|
    .block (bitMask P.bits ++ sel P.M.n P.acc P.acc P.tmp ++ [.alu .test .rbx (.reg .rbx)])

/-- `[acc] = [base]^e` (in Montgomery form), from the top bit of `e`. -/
def pow (P : PowCfg) : Prog isa :=
  .seq (.block (copy P.M.n P.acc P.one ++ [.mov32 .rbx (.imm (BitVec.ofNat 32 P.nbits))]))
    (.loop (powBody P) .ne)

/-- `[rdi + 8 rbx + d + j]`: bit `j` of byte `rbx` of a number, in a table at `d`. -/
def bitAt (d j : Nat) : MemOp := { base := .rdi, index := some .rbx, scale := 8, disp := d + j }

/-- The table at `dst` of the bits of the `nbytes`-byte little-endian number at
`src`: byte `8i + j` is bit `j` of byte `i` (so byte `t` is bit `t`). -/
def bits (src dst nbytes : Nat) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 0)]) (.loop (.block (
    [.movzx8 .rax (tbl src)] ++
    ((List.range 8).flatMap fun j =>
      [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
      [.alu .and .rdx (.imm 1), .store8 (bitAt dst j) .rdx]) ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm (BitVec.ofNat 32 nbytes))])) .ne)

/-! ## Numbers as bytes -/

/-- `[rdi + o] = ` the `n`-word big-endian number at `[src]`, little-endian. -/
def loadBE (n : Nat) (o : Nat) (src : Reg) : List Instr :=
  (List.range n).flatMap fun j =>
    [.mov .rax (.mem { base := src, disp := ((8 * (n - 1 - j) : Nat) : Int) }), .bswap .rax,
      .store (sc (o + 8 * j)) .rax]

/-- `[dst + d] = ` the `n`-word number at `[rdi + a]`, big-endian, masked with
`rcx`. -/
def storeBE (n : Nat) (dst : Reg) (d a : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    [.mov .rax (.mem (sc (a + 8 * j))), .alu .and .rax (.reg .rcx), .bswap .rax,
      .store { base := dst, disp := ((d + 8 * (n - 1 - j) : Nat) : Int) } .rax]

/-- `[rdi + o] = x`, `n` words. -/
def setConst (n : Nat) (o x : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    [.movImm64 .rax (BitVec.ofNat 64 (x >>> (64 * j))), .store (sc (o + 8 * j)) .rax]

end VG.Impl.Weierstrass.X86_64
