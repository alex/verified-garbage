import VerifiedGarbage.Impl.Rc2.X86.Lookup

/-! # RC2 key expansion on baseline x86

EBP holds the original key, ESI its length (then the reduction length),
EDI the output, and ECX the public index. The effective-bit count and scratch
pointer are read from their original stack arguments. PITABLE uses only
EAX, EBX and EDX, so no secret-dependent address or branch is needed.
-/

namespace VG.Impl.Rc2.X86

open VG.X86

def saved : List Reg := [.ebp, .ebx, .esi, .edi]

def save : List Instr :=
  saved.zipIdx |>.map fun (r, i) => .store (memOp .eax (4 * i)) r

def restore : List Instr :=
  saved.zipIdx |>.map fun (r, i) => .mov r (.mem (memOp .eax (4 * i)))

def copyKey : List Instr :=
  [rr .edx .ebp, .alu .add .edx (.reg .ecx), .movzx8 .eax (memOp .edx 0),
   rr .edx .edi, .alu .add .edx (.reg .ecx), .store8 (memOp .edx 0) .al,
   .alu .add .ecx (.imm 1), .alu .cmp .ecx (.reg .esi)]

def fillInput : List Instr :=
  [rr .edx .edi, .alu .add .edx (.reg .ecx), .alu .sub .edx (.imm 1),
   .movzx8 .eax (memOp .edx 0), rr .ebx .ecx, .alu .sub .ebx (.reg .esi),
   rr .edx .edi, .alu .add .edx (.reg .ebx), .movzx8 .ebx (memOp .edx 0), .alu .add .eax (.reg .ebx)]

def storeKey : List Instr :=
  [rr .edx .edi, .alu .add .edx (.reg .ecx), .store8 (memOp .edx 0) .al]

def fillFinish : List Instr :=
  storeKey ++ ([.alu .add .ecx (.imm 1), .alu .cmp .ecx (.imm 128)] : List Instr)

def fillKey : List Instr := fillInput ++ piLookup ++ fillFinish

def maskCode : Prog isa :=
  .seq (.block [.mov .edx (.mem (memOp .esp 12)), .alu .and .edx (.imm 7), imm .ebx 255])
    ((List.range 7).foldr (fun i rest =>
      .seq (.block [.alu .cmp .edx (.imm (BitVec.ofNat 32 (i + 1)))])
        (.seq (.ite .e (.block [imm .ebx (2 ^ (i + 1) - 1)]) (.block [])) rest)) (.block []))

def reduceInput : List Instr :=
  [rr .edx .edi, .alu .add .edx (.reg .ecx), .movzx8 .eax (memOp .edx 0),
   .alu .and .eax (.reg .ebx)]

def reduceKey : List Instr := reduceInput ++ piLookup ++ storeKey

def descendInput : List Instr :=
  [.alu .sub .ecx (.imm 1), rr .edx .edi, .alu .add .edx (.reg .ecx),
   .alu .add .edx (.imm 1), .movzx8 .eax (memOp .edx 0), rr .ebx .ecx,
   .alu .add .ebx (.reg .esi), rr .edx .edi, .alu .add .edx (.reg .ebx),
   .movzx8 .ebx (memOp .edx 0), .alu .xor .eax (.reg .ebx)]

def descendKey : List Instr :=
  descendInput ++ piLookup ++ (storeKey ++ ([.alu .cmp .ecx (.imm 0)] : List Instr))

def expandCopyFill : Prog isa :=
  .seq (.loop (.block copyKey) .ne)
    (.seq (.block [.alu .cmp .ecx (.imm 128)])
      (.ite .ne (.loop (.block fillKey) .ne) (.block [])))

def reduceSetup : List Instr :=
  [.mov .esi (.mem (memOp .esp 12)), .alu .add .esi (.imm 7), .shift .shr .esi 3,
   imm .ecx 128, .alu .sub .ecx (.reg .esi)]

def expandReduce : Prog isa :=
  .seq (.block reduceSetup)
    (.seq maskCode
      (.seq (.block reduceKey)
        (.seq (.block [.alu .cmp .ecx (.imm 0)])
          (.ite .ne (.loop (.block descendKey) .ne) (.block [])))))

def expandKey : Prog isa :=
  .seq (.block [.mov .eax (.mem (memOp .esp 20))])
    (.seq (.block (save ++
        ([.mov .ebp (.mem (memOp .esp 4)), .mov .esi (.mem (memOp .esp 8)),
          .mov .edi (.mem (memOp .esp 16)), imm .ecx 0] : List Instr)))
      (.seq expandCopyFill (.seq expandReduce
        (.block (([.mov .eax (.mem (memOp .esp 20))] : List Instr) ++ restore)))))

end VG.Impl.Rc2.X86
