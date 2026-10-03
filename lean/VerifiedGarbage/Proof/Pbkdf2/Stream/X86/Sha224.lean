import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha256

/-!
# SHA-224's streaming functions on x86 (32-bit), for every backend

`HashOK` for SHA-224 (`sha224OK`), for any of SHA-256's backends on x86
(`Sha256Stream`): SHA-256's streaming functions from SHA-224's initial hash
value (`vg_sha224_init`, then the backend's `update` and `finalize`, whose
contracts hold from any initial hash value), with the digest the first 28
bytes of the final hash value.
-/

namespace VG.Proof.Pbkdf2.Stream.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Sha256.X86.Variants (hmacHash224)
open VG.Proof.Hmac.Generic.Common (readW_reloc bytesAt_reloc)

/-- SHA-224's streaming functions with `v`'s `update` and `finalize`. -/
abbrev sha224H (v : Sha256Stream) : Hash := hmacHash224 v.suffix v.upd v.fin

/-- The representation moves with the state's bytes. -/
theorem sha224_repr (m m' : Mem) (p q : Addr) (msg : List Byte)
    (h : ∀ i < 96, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha256.ReprFrom Spec.Sha256.H0_224 m p msg) :
    Spec.Sha256.ReprFrom Spec.Sha256.H0_224 m' q msg := by
  refine ⟨?_, ?_⟩
  · rw [← hr.1]
    apply Vector.ext
    intro j hj
    simp only [Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact readW_reloc h (by omega)
  · rw [← hr.2]
    exact bytesAt_reloc h (o := 32) (k := msg.length % 64) (by omega)

theorem sha224_initSp : NoSp Impl.Sha256.X86.Stream.init224 := nosp_of (by lit_decide)
theorem sha224_initSU : stackUse Impl.Sha256.X86.Stream.init224 ≤ 20 := by lit_decide

/-- SHA-224's streaming functions with `v`'s `update` and `finalize`, verified. -/
def sha224OK (v : Sha256Stream) : HashOK (sha224H v) where
  SH := Spec.Hmac.sha224S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := show 28 ≤ 32 by decide
  hF := show 32 ≤ 64 by decide
  hD0 := show 0 < 28 by decide
  hS0 := show 0 < 96 by decide
  hSB := show 96 ≤ 256 by decide
  hB0 := show 0 < 64 by decide
  hBB := show 64 ≤ 128 by decide
  hWb := show 160 ≤ 8 * 20 by decide
  hW := show 20 ≤ 64 by decide
  repr := sha224_repr
  init := Proof.Sha256.X86.Stream.init224_verified
  upd := v.updOK.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0_224 m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.updOK.2.2 }
  fin := v.finOK.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 28 (Spec.Sha256.bytesAt s'.mem _ 32) = Spec.Sha256.sha224 m
        rw [h Spec.Sha256.H0_224 m hr hc]
        rfl
      pub := fun _ _ _ _ h => h
      sat := v.finOK.2.2 }
  initSp := sha224_initSp
  updSp := v.updSp
  finSp := v.finSp
  initSU := sha224_initSU
  updSU := v.updSU
  finSU := v.finSU

end VG.Proof.Pbkdf2.Stream.X86
