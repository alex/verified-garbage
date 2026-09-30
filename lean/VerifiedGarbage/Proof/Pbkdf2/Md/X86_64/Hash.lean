import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64
import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Hash
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.Contract

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: the hash function

Untrusted: everything here is checked by Lean. `HashOK H` is what the proofs
know of the hash function whose code `H` describes: its streaming code is
the generic Merkle–Damgård code (`Proof/MdStream/X86_64/`) for a hash
function `md` (`Md`) whose pieces do what they should (`Shape`, `Taints`),
calling a verified compression function (`CalleeOk`); its specification
`SH` is `md` from the initial hash value `iv`, with the digest the first `D`
bytes of `md`'s; its streaming `init` is verified; and its sizes fit.

From it, the streaming functions are verified against the contracts HMAC's
generic proofs call them with (`HashOK.stream`), so those proofs hold for
it.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Hmac.Generic.X86_64 (initK)
open VG.Proof.Hmac.Generic.Common (bytesAt_reloc)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

/-- What the proofs need of a Merkle–Damgård hash function's code. -/
structure HashOK (H : Hash) where
  /-- The hash function, as the streaming proofs see it. -/
  md : Md H.P.B H.P.N H.P.L
  dims : Dims H.P
  shape : Shape md
  taints : Taints H.P
  /-- The compression function is verified. -/
  comp : CalleeOk md H.compC
  /-- The hash value is determined by its bytes, wherever they are. -/
  reloc : ∀ (m m' : Mem) (p q : Addr), (∀ i < H.P.N, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) →
    md.stateAt m' q = md.stateAt m p
  /-- The length field is right for every message shorter than 2⁶⁴ bytes. -/
  lenOk : ∀ n, n < 2 ^ 64 → md.lenOk n
  /-- The specification: `md` from `iv`, with a `D`-byte digest. -/
  SH : StreamingHash
  iv : md.HV
  repr : ∀ mem p m, SH.Repr mem p m ↔ md.Repr iv mem p m
  hash : ∀ m, SH.H.hash m = (md.hash iv m).take H.D
  hB : SH.H.blockSize = H.P.B
  hS : SH.stateBytes = H.P.N + H.P.B
  hD : SH.digestBytes = H.D
  /-- The sizes: the digest is whole 32-bit words of the hash value, and a
  block holds it with its padding; the saved registers are aligned. -/
  hD0 : 0 < H.D
  hDN : H.D ≤ H.P.N
  hD4 : H.D % 4 = 0
  hN4 : H.P.N % 4 = 0
  hDL : H.D + H.P.L + 4 ≤ H.P.B
  hL4 : H.P.L % 4 = 0
  hNL : H.P.N + H.P.L ≤ H.P.B
  hso : H.P.so % 8 = 0 ∧ H.P.so + 48 ≤ 8 * 128
  /-- The working space our functions get holds `iterate`'s, and our
  functions' parts fit their offsets. -/
  fits : H.P.so + 48 + H.P.N + H.P.B ≤ 8 * H.W
  hW : H.W ≤ 256
  /-- The streaming `init`. -/
  init : Verified X86_64.target H.initC (initK (H.P.N + H.P.B) SH.Repr)
  initDepth : H.initC.depth ≤ 1
  initSp : NoSp H.initC
  /-- Facts about the streaming `update` and `finalize` that the kernel
  checks for each hash function: they never load MXCSR (so they keep its
  control bits) or write `rsp`, and make calls one deep. -/
  updMx : H.updC.allInstrs (fun i => !loadsMxcsr i) = true
  finMx : H.finC.allInstrs (fun i => !loadsMxcsr i) = true
  updSp : NoSp H.updC
  finSp : NoSp H.finC
  updDepth : H.updC.depth ≤ 1
  finDepth : H.finC.depth ≤ 1

namespace HashOK

variable {H : Hash} (hH : HashOK H)

include hH in
theorem B_le : H.P.B ≤ 128 := by rcases hH.dims.B with h | h <;> omega

include hH in
theorem B_pos : 0 < H.P.B := hH.dims.pos

include hH in
theorem N_le : H.P.N ≤ 64 := hH.dims.N.2

/-- The representation moves with the state's bytes. -/
theorem md_reloc {m m' : Mem} {p q : Addr} {msg : List Byte} {iv : hH.md.HV}
    (h : ∀ i < H.P.N + H.P.B, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : hH.md.Repr iv m p msg) : hH.md.Repr iv m' q msg := by
  have hB := hH.B_pos
  refine ⟨by rw [hH.reloc m m' p q fun i hi => h i (by omega)]; exact hr.1, ?_⟩
  rw [← hr.2]
  exact bytesAt_reloc h (o := H.P.N) (k := msg.length % H.P.B) (by have := Nat.mod_lt msg.length hB; omega)

theorem sh_reloc (m m' : Mem) (p q : Addr) (msg : List Byte)
    (h : ∀ i < H.P.N + H.P.B, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : hH.SH.Repr m p msg) : hH.SH.Repr m' q msg :=
  (hH.repr _ _ _).2 (hH.md_reloc h ((hH.repr _ _ _).1 hr))

/-! ## The streaming functions -/

/-- `update` is verified against the contract HMAC's proofs call it with. -/
theorem upd : Verified X86_64.target H.updC
    (Proof.Hmac.Generic.X86_64.updK (H.P.N + H.P.B) (H.P.so + 48) hH.SH.Repr) :=
  Verified.of_implies (MdStream.X86_64.Update.verified hH.dims hH.taints hH.comp hH.updMx)
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => (hH.repr _ _ _).2 (h hH.iv m ((hH.repr _ _ _).1 hr) hc)
      pub := fun _ _ _ _ h => h
      sat := (MdStream.X86_64.Update.verified hH.dims hH.taints hH.comp hH.updMx).2.2 }

/-- `finalize` is verified against the contract HMAC's proofs call it with:
its first `D` bytes are the digest. -/
theorem fin : Verified X86_64.target H.finC
    (Proof.Hmac.Generic.X86_64.finK (H.P.N + H.P.B) (H.P.so + 48) H.P.N H.D hH.SH.Repr hH.SH.H.hash) :=
  Verified.of_implies (MdStream.X86_64.Finalize.verified hH.dims hH.shape hH.taints hH.comp hH.finMx)
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hl hc => by
        rw [hH.hash, h hH.iv m ((hH.repr _ _ _).1 hr) (hH.lenOk _ hl) hc]
      pub := fun _ _ _ _ h => h
      sat := (MdStream.X86_64.Finalize.verified hH.dims hH.shape hH.taints hH.comp hH.finMx).2.2 }

/-- The streaming functions, as HMAC's generic proofs need them. -/
def stream : Proof.Hmac.Generic.X86_64.HashOK H.stream where
  SH := hH.SH
  Wb := H.P.so + 48
  hS := hH.hS
  hD := hH.hD
  hB := hH.hB
  hDF := hH.hDN
  hF := hH.N_le
  hD0 := hH.hD0
  hS0 := by show 0 < H.P.N + H.P.B; have := hH.B_pos; omega
  hSB := by show H.P.N + H.P.B ≤ 256; have := hH.B_le; have := hH.N_le; omega
  hB0 := hH.B_pos
  hBB := hH.B_le
  hWb := by show H.P.so + 48 ≤ 8 * ((H.P.so + 48) / 8); have := hH.hso; omega
  hW := by show (H.P.so + 48) / 8 ≤ 128; have := hH.hso; omega
  repr := hH.sh_reloc
  init := hH.init
  upd := hH.upd
  fin := hH.fin
  initDepth := hH.initDepth
  updDepth := hH.updDepth
  finDepth := hH.finDepth
  initSp := hH.initSp
  updSp := hH.updSp
  finSp := hH.finSp

end HashOK

end VG.Proof.Pbkdf2.Md.X86_64
