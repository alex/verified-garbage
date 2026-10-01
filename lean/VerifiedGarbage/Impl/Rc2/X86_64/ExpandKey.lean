import VerifiedGarbage.Impl.Rc2.X86_64.Sse2Lookup

/-! # RC2 key expansion on baseline x86-64

The public key length controls copying and expansion. The effective bit
count controls the reduction mask and descending loop. PITABLE selection
always scans all 256 candidates with eight parallel SSE2 arithmetic masks.
-/

namespace VG.Impl.Rc2.X86_64

open VG.X86_64

def saved : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

def save (base : Reg) (offset : Nat) : List Instr :=
  saved.zipIdx |>.map fun (r, i) => .store (memOp base (offset + 8 * i)) r

def restore (base : Reg) (offset : Nat) : List Instr :=
  saved.zipIdx |>.map fun (r, i) => .mov r (.mem (memOp base (offset + 8 * i)))

def indexed (base index : Reg) (disp : Int := 0) : MemOp := { base, index := some index, disp }

def copyKey : List Instr :=
  [.movzx8 .rax (indexed .r12 .rbx), .store8 (indexed .r14 .rbx) .rax,
   .alu .add .rbx (.imm 1), .alu .cmp .rbx (.reg .r13)]

def fillKey : List Instr :=
  [.movzx8 .rax (indexed .r14 .rbx (-1)), rr .r9 .rbx, .alu .sub .r9 (.reg .r13),
   .movzx8 .rcx (indexed .r14 .r9), .alu .add .rax (.reg .rcx)] ++ Sse2.piLookup ++
    [.store8 (indexed .r14 .rbx) .rax, .alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 128)]

/-- TM = 2^(T1 mod 8) - 1, with TM = 255 for a multiple of eight. All
tests here are on the public effective bit count, not the key. -/
def maskCode : Prog isa :=
  .seq (.block [rr .r9 .r15, .alu .and .r9 (.imm 7), imm .rdx 255])
    ((List.range 7).foldr (fun i rest =>
      .seq (.block [.alu .cmp .r9 (.imm (BitVec.ofNat 32 (i + 1)))])
        (.seq (.ite .e (.block [imm .rdx (2 ^ (i + 1) - 1)]) (.block [])) rest)) (.block []))

def reduceKey : List Instr :=
  [.movzx8 .rax (indexed .r14 .rbx), .alu .and .rax (.reg .rdx)] ++ Sse2.piLookup ++
    [.store8 (indexed .r14 .rbx) .rax]

def descendKey : List Instr :=
  [.alu .sub .rbx (.imm 1), .movzx8 .rax (indexed .r14 .rbx 1), rr .r9 .rbx,
   .alu .add .r9 (.reg .rbp), .movzx8 .rcx (indexed .r14 .r9), .alu .xor .rax (.reg .rcx)] ++
    Sse2.piLookup ++ [.store8 (indexed .r14 .rbx) .rax, .alu .cmp .rbx (.imm 0)]

def expandCopyFill : Prog isa :=
  .seq (.loop (.block copyKey) .ne)
    (.seq (.block [.alu .cmp .rbx (.imm 128)])
      (.ite .ne (.loop (.block fillKey) .ne) (.block [])))

def expandReduce : Prog isa :=
  .seq (.block [rr .rbp .r15, .alu .add .rbp (.imm 7), .shift .shr .rbp 3,
      imm .rbx 128, .alu .sub .rbx (.reg .rbp)])
    (.seq maskCode
      (.seq (.block reduceKey)
        (.seq (.block [.alu .cmp .rbx (.imm 0)])
          (.ite .ne (.loop (.block descendKey) .ne) (.block [])))))

def expandKey : Prog isa :=
  .seq (.block (save .r8 0 ++
      [rr .r12 .rdi, rr .r13 .rsi, rr .r14 .rcx, rr .r15 .rdx, imm .rbx 0]))
    (.seq expandCopyFill (.seq expandReduce (.block (restore .r8 0))))

end VG.Impl.Rc2.X86_64
