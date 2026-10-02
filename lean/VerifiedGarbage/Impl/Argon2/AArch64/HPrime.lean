import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Argon2 H′ on ARM64

The variable-length hash calls a supplied BLAKE2b streaming backend. All
hashing, the length prefix, chaining and output copying are assembly code.
The caller's 16 KiB scratch contains the 192-byte hash state at offset 0,
576 bytes of BLAKE2b scratch at 192, the digest at 768, the four-byte
length prefix at 832, and saved registers at 840–895 (including x30). The remaining scratch
is available to the enclosing Argon2 derivation.
-/

namespace VG.Impl.Argon2.AArch64.HPrime

open VG.AArch64

/-- Streaming entry points supplied by a BLAKE2b variant. -/
structure Hash where
  initName : String
  init : Prog isa
  updateName : String
  update : Prog isa
  finalizeName : String
  finalize : Prog isa


def saved : List (Reg × Nat) :=
  [(.x19, 840), (.x20, 848), (.x21, 856), (.x22, 864), (.x23, 872), (.x30, 888), (.x24, 880)]

/-- Preserve the caller and retain all input arguments across hash calls. -/
def setup : List Instr :=
  saved.map (fun (r, d) => .str .x r .x4 d) ++
    [.addImm .x .x24 .x4 0, .addImm .x .x20 .x0 0, .addImm .x .x21 .x1 0,
      .addImm .x .x22 .x2 0, .addImm .x .x23 .x3 0, .str .w .x3 .x24 832]

def restore : List Instr := saved.map fun (r, d) => .ldr .x r .x24 d

/-- Point the empty key into the workspace, retaining the digest length. -/
def initArgs : List Instr :=
  [.addImm .x .x0 .x24 0, .addImm .x .x2 .x24 0, .addImm .x .x2 .x2 832,
    .movz .x .x3 0 0]

/-- Initialize an unkeyed hash with the digest length in `x1`. -/
def init (h : Hash) : Prog isa :=
  .seq (.block initArgs)
    (.call h.initName h.init)

/-- Supply the hash state and the hash's private scratch allocation. -/
def updateArgs : List Instr :=
  [.addImm .x .x0 .x24 0, .addImm .x .x4 .x24 0, .addImm .x .x4 .x4 192]

/-- Update from `x2, x3` with the byte count in `x1`. -/
def update (h : Hash) : Prog isa :=
  .seq (.block updateArgs)
    (.call h.updateName h.update)

/-- The hash state, digest buffer and private hash scratch. -/
def finalizeArgs : List Instr :=
  [.addImm .x .x0 .x24 0, .addImm .x .x2 .x24 0, .addImm .x .x2 .x2 768,
    .addImm .x .x3 .x24 0, .addImm .x .x3 .x3 192]

/-- Finalize the hash with the byte count in `x1`. -/
def finalize (h : Hash) : Prog isa :=
  .seq (.block finalizeArgs)
    (.call h.finalizeName h.finalize)

/-- Absorb a fixed workspace buffer, starting a fresh byte count. -/
def fixedArgs (offset size : Nat) : List Instr :=
  [.movz .x .x1 0 0, .addImm .x .x2 .x24 0,
    .addImm .x .x2 .x2 offset, .movz .x .x3 (BitVec.ofNat 16 size) 0]

/-- Absorb a workspace buffer into an empty hash state. -/
def absorbFixed (h : Hash) (offset size : Nat) : Prog isa :=
  .seq (.block (fixedArgs offset size)) (update h)

/-- The first digest has `min(out_len, 64)` bytes. -/
def chooseLength : Prog isa :=
  .seq (.block [.addImm .x .x1 .x23 0, .subImm .x .x9 .x1 65, .lsr .x .x9 .x9 63])
    (.ite (.nonzero .x .x9) (.block []) (.block [.movz .x .x1 64 0]))

/-- Absorb the caller's input after the four-byte length prefix. -/
def inputArgs : List Instr :=
  [.movz .x .x1 4 0, .addImm .x .x2 .x20 0, .addImm .x .x3 .x21 0]

/-- Absorb the caller's bytes after the length prefix. -/
def absorbInput (h : Hash) : Prog isa :=
  .seq (.block inputArgs) (update h)

/-- Finish the hash after the four-byte prefix and the caller's input. -/
def finishInput (h : Hash) : Prog isa :=
  .seq (.block [.addImm .x .x1 .x21 0, .addImm .x .x1 .x1 4]) (finalize h)

/-- H(min(out_len, 64), LE32(out_len) || input). -/
def first (h : Hash) : Prog isa :=
  .seq chooseLength
  (.seq (init h)
  (.seq (absorbFixed h 832 4)
  (.seq (absorbInput h)
  (finishInput h))))

/-- Hash the 64-byte previous digest, with the new digest length in `x1`. -/
def next (h : Hash) : Prog isa :=
  .seq (init h)
  (.seq (absorbFixed h 768 64)
  (.seq (.block [.movz .x .x1 64 0]) (finalize h)))

/-- Copy one byte and advance the source, destination and countdown. -/
def copyByte : List Instr :=
  [.ldrb .x3 .x2 0, .strb .x3 .x22 0,
    .addImm .x .x2 .x2 1, .addImm .x .x22 .x22 1, .subImm .x .x8 .x8 1]

/-- Copy `x8 > 0` digest bytes to `x22`, advancing that output pointer. -/
def copy : Prog isa :=
  .seq (.block [.addImm .x .x2 .x24 0, .addImm .x .x2 .x2 768])
    (.loop (.block copyByte) (.nonzero .x .x8))

/-- Emit one 32-byte prefix and reduce the remaining output length. -/
def emitPrefix : Prog isa :=
  .seq (.block [.movz .x .x8 32 0])
    (.seq copy (.block [.subImm .x .x23 .x23 32]))

/-- Emit further prefixes while more than 64 output bytes remain. -/
def chain (h : Hash) : Prog isa :=
  .loop (.seq (.block [.movz .x .x1 64 0])
    (.seq (next h) (.seq emitPrefix (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63])))) (.zero .x .x9)

/-- Produce the final digest after the 32-byte prefixes of a long output. -/
def extendDigest (h : Hash) : Prog isa :=
  .seq emitPrefix
  (.seq (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63])
  (.seq (.ite (.nonzero .x .x9) (.block []) (chain h))
  (.seq (.block [.addImm .x .x1 .x23 0]) (next h))))

def copyRemaining : Prog isa := .seq (.block [.addImm .x .x8 .x23 0]) copy

/-- Emit H′ from its first digest, extending it for outputs over 64 bytes. -/
def finishOutput (h : Hash) : Prog isa :=
  .seq (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63])
  (.seq (.ite (.nonzero .x .x9) (.block []) (extendDigest h)) copyRemaining)

/-- H′, including the short-output case and the final 33–64-byte hash. -/
def code (h : Hash) : Prog isa :=
  .seq (.block setup)
  (.seq (first h)
  (.seq (finishOutput h) (.block restore)))

end VG.Impl.Argon2.AArch64.HPrime
