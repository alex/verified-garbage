import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
import VerifiedGarbage.Proof.Sha512.X86.Stream.Update
import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize
import VerifiedGarbage.Proof.Sha1.X86.Stream.Init
import VerifiedGarbage.Proof.Sha1.X86.Stream.Md
import VerifiedGarbage.Proof.Md5.X86.Stream.Init
import VerifiedGarbage.Proof.Md5.X86.Stream.Md

/-!
# HMAC over any streaming hash function on x86 (32-bit): the hash functions

`HashOK` for SHA-1, MD5 and the SHA-512 family, from their own proofs, as on
the other targets (`Proof/Pbkdf2/Stream/Arm/Hashes.lean`). Their contracts are
`initK`, `updK` and `finK` at their sizes, but for the SHA-512 family's
`update` and `finalize`, which hold from any initial hash value, and whose
`finalize` only reads its arguments (`finKr`). Another hash function with
streaming functions verified on x86 is one more `HashOK` here, and a
registration file for each of its functions. SHA-256's, for each of its
backends, are in `Sha256.lean`.
-/

namespace VG.Proof.Pbkdf2.Stream.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Hmac.Generic.Common (sha1_repr md5_repr sha512_repr finalHash_length)

/-- No instruction of `c` writes `esp`, from a check that runs in the kernel. -/
theorem nosp_of {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .esp) = true) : NoSp c :=
  NoSp.of_all h

/-- A `finalize` that only reads its arguments is verified against `finK`,
which lets it write them. -/
theorem finK_of_finKr {c : Prog isa} {S Wb F D : Nat} {R : Mem → Addr → List Byte → Prop}
    {hash : List Byte → List Byte} (h : Verified X86.target c (finKr S Wb F D R hash)) :
    Verified X86.target c (finK S Wb F D R hash) := by
  have pre : ∀ s, (finK S Wb F D R hash).pre s → (finKr S Wb F D R hash).pre (s.withRegions
      [⟨argAddr s 0, 20⟩] [⟨(arg s 0).setWidth 64, S⟩, ⟨(arg s 3).setWidth 64, F⟩, ⟨(arg s 4).setWidth 64, Wb⟩]) := by
    intro s h
    obtain ⟨_, _, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
    simp only [finKr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr]
    exact ⟨trivial, trivial, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
  have pre' : ∀ s, (finKr S Wb F D R hash).pre s → (finK S Wb F D R hash).pre (s.withRegions []
      [⟨(arg s 0).setWidth 64, S⟩, ⟨(arg s 3).setWidth 64, F⟩, ⟨(arg s 4).setWidth 64, Wb⟩, ⟨argAddr s 0, 20⟩]) := by
    intro s h
    obtain ⟨_, _, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
    simp only [finK, arg_withRegions, argAddr_withRegions, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr]
    exact ⟨trivial, trivial, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
  refine Verified.narrowTo h _ _ pre (fun s h => ?_) (fun s h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h)
    (h.2.2.elim fun s hs => ⟨_, pre' s hs⟩)
  · obtain ⟨h1, h2, _⟩ := h
    rw [h1, h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), 0,
        by simp, by simp⟩
    · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
  · obtain ⟨_, h2, _⟩ := h
    rw [h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩

/-! ## SHA-1 -/

def sha1H : Hash := ⟨64, 84, 20, 20, 20, "vg_sha1_init", Impl.Sha1.X86.Stream.init,
  "vg_sha1_update", Impl.Sha1.X86.Stream.update, "vg_sha1_finalize", Impl.Sha1.X86.Stream.finalize⟩

def sha1OK : HashOK sha1H where
  SH := Spec.Hmac.sha1S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := by decide
  hF := by decide
  hD0 := by decide
  hS0 := by decide
  hSB := by decide
  hB0 := by decide
  hBB := by decide
  hWb := by decide
  hW := by decide
  repr := sha1_repr
  init := Proof.Sha1.X86.Stream.init_verified
  upd := Proof.Sha1.X86.Stream.Update.update_verified
  fin := Proof.Sha1.X86.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 20 (Spec.Sha1.bytesAt s'.mem _ 20) = _
        rw [List.take_of_length_le (by simp [Spec.Sha1.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha1.X86.Stream.Finalize.finalize_verified.2.2 }
  initSp := nosp_of (by lit_decide)
  updSp := nosp_of (by lit_decide)
  finSp := nosp_of (by lit_decide)
  initSU := by lit_decide
  updSU := by lit_decide
  finSU := by lit_decide

/-! ## MD5 -/

def md5H : Hash := ⟨64, 80, 16, 16, 14, "vg_md5_init", Impl.Md5.X86.Stream.init,
  "vg_md5_update", Impl.Md5.X86.Stream.update, "vg_md5_finalize", Impl.Md5.X86.Stream.finalize⟩

def md5OK : HashOK md5H where
  SH := Spec.Hmac.md5S
  Wb := 112
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := by decide
  hF := by decide
  hD0 := by decide
  hS0 := by decide
  hSB := by decide
  hB0 := by decide
  hBB := by decide
  hWb := by decide
  hW := by decide
  repr := md5_repr
  init := Proof.Md5.X86.Stream.init_verified
  upd := Proof.Md5.X86.Stream.Update.update_verified
  fin := Proof.Md5.X86.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 16 (Spec.Md5.bytesAt s'.mem _ 16) = _
        rw [List.take_of_length_le (by simp [Spec.Md5.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Md5.X86.Stream.Finalize.finalize_verified.2.2 }
  initSp := nosp_of (by lit_decide)
  updSp := nosp_of (by lit_decide)
  finSp := nosp_of (by lit_decide)
  initSU := by lit_decide
  updSU := by lit_decide
  finSU := by lit_decide

/-! ## The SHA-512 family -/

/-- The SHA-512 family member with initial hash value `iv` and a `D`-byte digest. -/
def sha512H (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Hash :=
  ⟨128, 192, D, 64, 34, initN, Impl.Sha512.X86.Stream.init iv, "vg_sha512_update",
    Impl.Sha512.X86.Stream.update, "vg_sha512_finalize", Impl.Sha512.X86.Stream.finalize⟩

theorem sha512_updSp : NoSp Impl.Sha512.X86.Stream.update := nosp_of (by lit_decide)
theorem sha512_finSp : NoSp Impl.Sha512.X86.Stream.finalize := nosp_of (by lit_decide)
theorem sha512_updSU : stackUse Impl.Sha512.X86.Stream.update = 20 := by lit_decide
theorem sha512_finSU : stackUse Impl.Sha512.X86.Stream.finalize = 20 := by lit_decide

/-- `HashOK` for a member of the SHA-512 family, whose digest is the first
`D` bytes of the final hash value. -/
def sha512FamOK (SH : Spec.Hmac.StreamingHash) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue)
    (hS : SH.stateBytes = 192) (hD : SH.digestBytes = D) (hB : SH.H.blockSize = 128)
    (hR : SH.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, SH.H.hash m = (Spec.Sha512.finalHash iv m).take D) (hD0 : 0 < D) (hD64 : D ≤ 64)
    (hISp : NoSp (Impl.Sha512.X86.Stream.init iv)) (hISU : stackUse (Impl.Sha512.X86.Stream.init iv) = 0) :
    HashOK (sha512H D initN iv) where
  SH := SH
  Wb := 272
  hS := hS
  hD := hD
  hB := hB
  hDF := hD64
  hF := Nat.le_refl 64
  hD0 := hD0
  hS0 := show 0 < 192 by decide
  hSB := show 192 ≤ 256 by decide
  hB0 := show 0 < 128 by decide
  hBB := Nat.le_refl 128
  hWb := show 272 ≤ 8 * 34 by decide
  hW := show 34 ≤ 64 by decide
  repr := hR ▸ sha512_repr iv
  init := hR ▸ Proof.Sha512.X86.Stream.init_verified iv
  upd := hR ▸ Proof.Sha512.X86.Stream.Update.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h iv m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha512.X86.Stream.Update.update_verified.2.2 }
  fin := finK_of_finKr <| Proof.Sha512.X86.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr hl hc => by
        show List.take D (Spec.Sha512.bytesAt s'.mem _ 64) = _
        rw [hh, h iv m (hR ▸ hr) hl hc]
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha512.X86.Stream.Finalize.finalize_verified.2.2 }
  initSp := hISp
  updSp := sha512_updSp
  finSp := sha512_finSp
  initSU := by show stackUse (Impl.Sha512.X86.Stream.init iv) ≤ 20; rw [hISU]; decide
  updSU := by show stackUse Impl.Sha512.X86.Stream.update ≤ 20; rw [sha512_updSU]
  finSU := by show stackUse Impl.Sha512.X86.Stream.finalize ≤ 20; rw [sha512_finSU]

def sha384H : Hash := sha512H 48 "vg_sha384_init" Spec.Sha512.H0_384
def sha512H' : Hash := sha512H 64 "vg_sha512_init" Spec.Sha512.H0_512
def sha512_224H : Hash := sha512H 28 "vg_sha512_224_init" Spec.Sha512.H0_512_224
def sha512_256H : Hash := sha512H 32 "vg_sha512_256_init" Spec.Sha512.H0_512_256

def sha384OK : HashOK sha384H := sha512FamOK Spec.Hmac.sha384S 48 "vg_sha384_init" Spec.Sha512.H0_384
  rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (nosp_of (by lit_decide)) (by lit_decide)
def sha512OK : HashOK sha512H' := sha512FamOK Spec.Hmac.sha512S 64 "vg_sha512_init" Spec.Sha512.H0_512
  rfl rfl rfl rfl (fun m => (List.take_of_length_le (Nat.le_of_eq (finalHash_length _ m))).symm) (by decide) (by decide)
  (nosp_of (by lit_decide)) (by lit_decide)
def sha512_224OK : HashOK sha512_224H := sha512FamOK Spec.Hmac.sha512_224S 28 "vg_sha512_224_init"
  Spec.Sha512.H0_512_224 rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (nosp_of (by lit_decide))
  (by lit_decide)
def sha512_256OK : HashOK sha512_256H := sha512FamOK Spec.Hmac.sha512_256S 32 "vg_sha512_256_init"
  Spec.Sha512.H0_512_256 rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (nosp_of (by lit_decide))
  (by lit_decide)

end VG.Proof.Pbkdf2.Stream.X86
