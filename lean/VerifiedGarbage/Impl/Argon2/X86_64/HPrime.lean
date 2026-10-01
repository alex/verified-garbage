import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Argon2 H′ on x86-64

The variable-length hash calls a supplied BLAKE2b streaming backend. All
hashing, the length prefix, chaining and output copying are assembly code.
The caller's 16 KiB scratch contains the 192-byte hash state at offset 0,
576 bytes of BLAKE2b scratch at 192, the digest at 768, the four-byte
length prefix at 832, and saved registers at 840. The remaining scratch
is available to the enclosing Argon2 derivation.
-/

namespace VG.Impl.Argon2.X86_64.HPrime

open VG.X86_64

/-- Streaming entry points supplied by a BLAKE2b variant. -/
structure Hash where
  initName : String
  init : Prog isa
  updateName : String
  update : Prog isa
  finalizeName : String
  finalize : Prog isa

def at_ (r : Reg) (d : Nat := 0) : MemOp := { base := r, disp := d }

def saved : List (Reg × Nat) :=
  [(.rbp, 840), (.r12, 848), (.r13, 856), (.r14, 864), (.r15, 872), (.rbx, 880)]

/-- Preserve the caller and retain all input arguments across hash calls. -/
def setup : List Instr :=
  saved.map (fun (r, d) => .store (at_ .r8 d) r) ++
    [.mov .rbx (.reg .r8), .mov .r12 (.reg .rdi), .mov .r13 (.reg .rsi),
      .mov .r14 (.reg .rdx), .mov .r15 (.reg .rcx), .store32 (at_ .rbx 832) .rcx]

def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rbx d))

/-- Point the empty key into the workspace, retaining the digest length. -/
def initArgs : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rdx (.reg .rbx), .alu .add .rdx (.imm 832),
    .mov32 .rcx (.imm 0)]

/-- Initialize an unkeyed hash with the digest length in `rsi`. -/
def init (h : Hash) : Prog isa :=
  .seq (.block initArgs)
    (.call h.initName h.init)

/-- Supply the hash state and the hash's private scratch allocation. -/
def updateArgs : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .r8 (.reg .rbx), .alu .add .r8 (.imm 192)]

/-- Update from `rdx, rcx` with the byte count in `rsi`. -/
def update (h : Hash) : Prog isa :=
  .seq (.block updateArgs)
    (.call h.updateName h.update)

/-- The hash state, digest buffer and private hash scratch. -/
def finalizeArgs : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rdx (.reg .rbx), .alu .add .rdx (.imm 768),
    .mov .rcx (.reg .rbx), .alu .add .rcx (.imm 192)]

/-- Finalize the hash with the byte count in `rsi`. -/
def finalize (h : Hash) : Prog isa :=
  .seq (.block finalizeArgs)
    (.call h.finalizeName h.finalize)

/-- H(min(out_len, 64), LE32(out_len) || input). -/
def first (h : Hash) : Prog isa :=
  .seq (.block [.mov .rsi (.reg .r15), .alu .cmp .rsi (.imm 65)])
  (.seq (.ite .b (.block []) (.block [.mov32 .rsi (.imm 64)]))
  (.seq (init h)
  (.seq (.block [.mov32 .rsi (.imm 0), .mov .rdx (.reg .rbx), .alu .add .rdx (.imm 832), .mov32 .rcx (.imm 4)])
  (.seq (update h)
  (.seq (.block [.mov32 .rsi (.imm 4), .mov .rdx (.reg .r12), .mov .rcx (.reg .r13)])
  (.seq (update h)
  (.seq (.block [.mov .rsi (.reg .r13), .alu .add .rsi (.imm 4)]) (finalize h))))))))

/-- Hash the 64-byte previous digest, with the new digest length in `rsi`. -/
def next (h : Hash) : Prog isa :=
  .seq (init h)
  (.seq (.block [.mov32 .rsi (.imm 0), .mov .rdx (.reg .rbx), .alu .add .rdx (.imm 768), .mov32 .rcx (.imm 64)])
  (.seq (update h)
  (.seq (.block [.mov32 .rsi (.imm 64)]) (finalize h))))

/-- Copy one byte and advance the source, destination and countdown. -/
def copyByte : List Instr :=
  [.movzx8 .rcx (at_ .rdx), .store8 (at_ .r14) .rcx,
    .alu .add .rdx (.imm 1), .alu .add .r14 (.imm 1), .alu .sub .rax (.imm 1)]

/-- Copy `rax > 0` digest bytes to `r14`, advancing that output pointer. -/
def copy : Prog isa :=
  .seq (.block [.mov .rdx (.reg .rbx), .alu .add .rdx (.imm 768)])
    (.loop (.block copyByte) .ne)

/-- Emit one 32-byte prefix and reduce the remaining output length. -/
def emitPrefix : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 32)])
    (.seq copy (.block [.alu .sub .r15 (.imm 32)]))

/-- Emit further prefixes while more than 64 output bytes remain. -/
def chain (h : Hash) : Prog isa :=
  .loop (.seq (.block [.mov32 .rsi (.imm 64)])
    (.seq (next h) (.seq emitPrefix (.block [.alu .cmp .r15 (.imm 65)])))) .ae

/-- H′, including the short-output case and the final 33–64-byte hash. -/
def code (h : Hash) : Prog isa :=
  .seq (.block setup)
  (.seq (first h)
  (.seq (.block [.alu .cmp .r15 (.imm 65)])
  (.seq (.ite .b (.block [])
    (.seq emitPrefix
    (.seq (.block [.alu .cmp .r15 (.imm 65)])
    (.seq (.ite .b (.block []) (chain h))
    (.seq (.block [.mov .rsi (.reg .r15)]) (next h))))))
  (.seq (.block [.mov .rax (.reg .r15)])
  (.seq copy (.block restore))))))

end VG.Impl.Argon2.X86_64.HPrime
