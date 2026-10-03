import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitch

/-!
# ChaCha20-Poly1305: AArch64, with Poly1305 inside the ChaCha20 kernel

`sealWith` and `openWith` (`../AArch64.lean`) encrypt the data with one
call and absorb it with another. With the eight-block kernel, `sealStitched`
and `openStitched` instead process the data's whole chunks of 512 bytes with
`Stitch.bulk`, which absorbs the ciphertext while it computes the keystream,
and only the rest with those calls:

* the counter is set to 1 and the stream's arguments to the data
  (`cryptSetup`); with fewer than 512 bytes, nothing more happens here;
* otherwise `x27` and `x28` are saved in the context (`[800, 816)`), the
  clamped key is stored where `Stitch.chunk` reads it (bytes 160–175 of the
  stream's working space) and the accumulator loaded into `x21`–`x23`
  (`polyIn`), the chunks run (`Stitch.bulk`), and the accumulator is reduced
  and stored, `x21` (the context) recomputed from `x0`, `x27` and `x28`
  restored, and `x22`, `x23` set to the data not yet absorbed: everything
  after the chunks when decrypting, and also the last chunk when encrypting
  (`polyOut`);
* the rest of the data is encrypted (`vg_chacha20_xor`, from where the
  chunks stopped) and absorbed (from `x22`), in the order the direction
  needs.

The registers `x21`–`x25` and `x30` hold other values meanwhile; the
prologue saved them, and `restore` restores them.
-/

namespace VG.Impl.ChaCha20Poly1305.AArch64

open VG.AArch64
open VG.Impl.ChaCha20.AArch64 (XorCallee)
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Impl.Poly1305.AArch64 (const64)

/-- The counter set to 1, the stream's arguments set to the data (as in
`cryptWith`), and `x5 = 1` if there are fewer than 512 bytes. -/
def cryptSetup : List Instr :=
  [.movz .w .x9 1 0, .str .w .x9 .x21 112, .addImm .x .x0 .x21 64, mov .x1 .x22,
    mov .x2 .x23, .addImm .x .x3 .x21 128] ++ VG.Impl.ChaCha20.AArch64.Mixed8.check

/-- `x27` and `x28` saved, the clamped key stored at `ctx[288, 304)`, and the
accumulator loaded into `x21`–`x23` (`x21`, the base, last). -/
def polyIn : List Instr :=
  [.str .x .x27 .x21 800, .str .x .x28 .x21 808] ++
  const64 .x24 0x0ffffffc0fffffff ++
  [.ldr .x .x25 .x21 472, .logic .and .x .x25 .x25 .x24, .str .x .x25 .x21 288] ++
  const64 .x24 0x0ffffffc0ffffffc ++
  [.ldr .x .x25 .x21 480, .logic .and .x .x25 .x25 .x24, .str .x .x25 .x21 296,
   .ldr .x .x22 .x21 456, .ldr .x .x23 .x21 464, .ldr .x .x21 .x21 448]

/-- The accumulator reduced (`Poly1305.AArch64.Radix64.reduce`) and stored,
`x21`, `x27` and `x28` restored, and in `x22`, `x23` the data not yet
absorbed. -/
def polyOut (enc : Bool) : List Instr :=
  [mov .x4 .x21, mov .x5 .x22, mov .x6 .x23] ++ VG.Impl.Poly1305.AArch64.Radix64.reduce ++
  [.subImm .x .x21 .x0 64, .str .x .x4 .x21 448, .str .x .x5 .x21 456, .str .x .x6 .x21 464,
   .ldr .x .x27 .x21 800, .ldr .x .x28 .x21 808] ++
  (if enc then [.subImm .x .x22 .x1 512, .addImm .x .x23 .x2 512] else [mov .x22 .x1, mov .x23 .x2])

/-- The whole chunks. -/
def cryptStitched (enc : Bool) : Prog isa :=
  .seq (.block cryptSetup)
    (.ite (.nonzero .x .x5) (.block [])
      (.seq (.block polyIn) (.seq (Stitch.bulk enc) (.block (polyOut enc)))))

/-- The data from `x22` (`x23` bytes) encrypted or decrypted, continuing the
stream's counter. -/
def cryptRest (c : XorCallee) : Prog isa :=
  .seq (.block [.addImm .x .x0 .x21 64, mov .x1 .x22, mov .x2 .x23, .addImm .x .x3 .x21 128])
    (.call c.name c.code)

def sealStitched (c : XorCallee) : Prog isa :=
  .seq prologue
  (.seq (macPad .x24 .x25)
  (.seq (.block lengths)
  (.seq (cryptStitched true)
  (.seq (.call c.name c.code)
  (.seq (macPad .x22 .x23)
  (.seq absorbLengths
  (.seq (finalizeTo 48)
    (.block restore))))))))

def openStitched (c : XorCallee) : Prog isa :=
  .seq prologue
  (.seq (macPad .x24 .x25)
  (.seq (.block lengths)
  (.seq (cryptStitched false)
  (.seq (macPad .x22 .x23)
  (.seq (cryptRest c)
  (.seq absorbLengths
  (.seq (finalizeTo 640)
    (.block (compare ++ restore)))))))))

/-- The code for a stream backend: stitched with the eight-block kernel or not. -/
def sealCode (c : XorCallee) (stitched : Bool) : Prog isa :=
  if stitched then sealStitched c else sealWith c

def openCode (c : XorCallee) (stitched : Bool) : Prog isa :=
  if stitched then openStitched c else openWith c

end VG.Impl.ChaCha20Poly1305.AArch64
