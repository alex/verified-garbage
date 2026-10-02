import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
import VerifiedGarbage.Proof.Hmac.Generic.X86.Hashes
import VerifiedGarbage.Proof.Sha512.Md
import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize

/-!
# HMAC and PBKDF2-HMAC on x86 (32-bit): the Merkle–Damgård hash functions

MD5, SHA-1 and the SHA-512 family as `Hash`es of `Impl/Pbkdf2/Md/X86.lean`:
their streaming functions (`Proof/Hmac/Generic/X86/Hashes.lean`), their
compression functions and the code writing their digests
(`Impl.MdStream.X86.out32` for MD5 and SHA-1, SHA-512's `outW`), and what the
proofs know of them (`MdOk`), from their own proofs: the `Md` of the generic
streaming proofs (`Proof/Md5/Md.lean` and the others), the digests their code
writes (`out512_ok` for the SHA-512 family), and their compression functions'
contracts, which are `cmpK`. SHA-256, whose compression function has a
variant for each backend on x86, is in `Sha256.lean`.
-/

namespace VG.Proof.Pbkdf2.Md.X86

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.MdStream (Md)
open VG.Proof.Hmac.Generic.X86 (md5H sha1H sha512H md5OK sha1OK sha384OK sha512OK sha512_224OK sha512_256OK)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)

/-! ## The hash functions -/

/-- MD5: a 16-byte hash value, a little-endian length field and digest. -/
def md5M : Hash :=
  ⟨md5H, 16, 8, false, 64, "vg_md5_compress", Impl.Md5.X86.compress, Impl.Md5.X86.Stream.params.out⟩

/-- SHA-1: a 20-byte hash value, a big-endian length field and digest. -/
def sha1M : Hash :=
  ⟨sha1H, 20, 8, true, 112, "vg_sha1_compress", Impl.Sha1.X86.compress, Impl.Sha1.X86.Stream.params.out⟩

/-- The member of the SHA-512 family with a `D`-byte digest and initial hash
value `iv`: a 64-byte hash value, a big-endian 16-byte length field, and the
digest of the whole hash value (`D` bytes of which are output). -/
def sha512M (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Hash :=
  ⟨sha512H D initN iv, 64, 16, true, 224, "vg_sha512_compress", Impl.Sha512.X86.compress,
    (List.range 8).flatMap Impl.Sha512.X86.Stream.outW⟩

def sha384M : Hash := sha512M 48 "vg_sha384_init" Spec.Sha512.H0_384
def sha512M' : Hash := sha512M 64 "vg_sha512_init" Spec.Sha512.H0_512
def sha512_224M : Hash := sha512M 28 "vg_sha512_224_init" Spec.Sha512.H0_512_224
def sha512_256M : Hash := sha512M 32 "vg_sha512_256_init" Spec.Sha512.H0_512_256

/-! ## The digest of a SHA-512 hash value -/

section
open VG.Impl.Sha512.X86.Stream (outW)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_movm wp_store wp_bswap contains_addr sub_offset)
open VG.Proof.Sha512.X86.Stream (ea_at)
open VG.Proof.Sha512.X86.Stream.Finalize (writeW_bswap flat_length)
open VG.Proof.Sha512.Word64 (lo hi wordBytes_split)
open VG.Proof.Sha512.X86 (lo_rd64 hi_rd64)
open VG.Proof.Sha512.X86 (stateAt_get)
open Spec.Sha512 (stateAt wordBytes)

/-- What `outW` has written after `k` words of the hash value at `x` (in
`ebx`) to `y` (in `eax`), from the memory `m₀`. -/
structure Out512 (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes s₀.mem ((s₀.gpr .eax).setWidth 64)
    (((stateAt s₀.mem ((s₀.gpr .ebx).setWidth 64)).toList.take k).flatMap wordBytes)

theorem out512_step {s₀ : State} (hbx : (s₀.gpr .ebx).toNat + 64 ≤ 2 ^ 32)
    (hax : (s₀.gpr .eax).toNat + 64 ≤ 2 ^ 32)
    (hin : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .ebx).setWidth 64) 64)
    (hout : InRegions s₀.wr ((s₀.gpr .eax).setWidth 64) 64)
    (hd : Region.Disjoint ⟨(s₀.gpr .ebx).setWidth 64, 64⟩ ⟨(s₀.gpr .eax).setWidth 64, 64⟩)
    {k : Nat} (hk : k < 8) {s : State} (h : Out512 s₀ k s) {rest : List Instr} {Q : State → Prop}
    (hnext : ∀ s', Out512 s₀ (k + 1) s' → WP isa (.block rest) s' Q) :
    WP isa (.block (outW k ++ rest)) s Q := by
  set x := s₀.gpr .ebx
  set y := s₀.gpr .eax
  have hebx : s.gpr .ebx = x := h.gpr _ (by decide) (by decide)
  have heax : s.gpr .eax = y := h.gpr _ (by decide) (by decide)
  have hP := flat_length (stateAt s₀.mem (x.setWidth 64)) k (Nat.le_of_lt hk)
  have sub : ∀ {rs : List Region} {b : BitVec 32}, b.toNat + 64 ≤ 2 ^ 32 → InRegions rs (b.setWidth 64) 64 →
      ∀ o, o + 4 ≤ 8 → InRegions rs (addr b (8 * k + o)) 4 := by
    intro rs b hb ⟨R, hR, hc⟩ o ho
    refine ⟨R, hR, ?_⟩
    rw [addr_eq (by omega)]
    have := Offset.contains_base (b.setWidth 64) (d := 8 * k + o) (n := 4) (k := 64) (by omega) (by omega)
    simp only [Region.Contains] at hc this ⊢
    have e : (b.setWidth 64 + BitVec.ofNat 64 (8 * k + o) - R.base).toNat ≤ (b.setWidth 64 - R.base).toNat + (8 * k + o) := by
      rw [show b.setWidth 64 + BitVec.ofNat 64 (8 * k + o) - R.base = (b.setWidth 64 - R.base) + BitVec.ofNat 64 (8 * k + o) by
        rw [VG.Offset.add_sub_comm], BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * k + o) (by omega)]
      exact Nat.mod_le _ _
    omega
  -- The word's halves, unchanged since the start.
  have hread : ∀ o, o + 4 ≤ 8 → s.mem.readW (addr x (8 * k + o)) 32 = s₀.mem.readW (addr x (8 * k + o)) 32 := by
    intro o ho'
    rw [h.mem]
    have hc : (⟨y.setWidth 64, 64⟩ : Region).Contains (y.setWidth 64)
        (((stateAt s₀.mem (x.setWidth 64)).toList.take k).flatMap wordBytes).length := by
      have := Offset.contains_base (y.setWidth 64) (d := 0) (n := 8 * k) (k := 64) (by omega) (by omega)
      rw [hP]; rwa [show y.setWidth 64 + BitVec.ofNat 64 0 = y.setWidth 64 from BitVec.add_zero _] at this
    refine (writeBytes_frame _ _ _ hc).readW
      (r := ⟨addr x (8 * k + o), 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    rw [addr_eq (by omega)]
    exact hd.sub_left (Offset.sub_base _ (by omega))
  have hw := stateAt_get (st := x) hbx s₀.mem hk
  have wlo : s₀.mem.readW (addr x (8 * k + 0)) 32 = lo (stateAt s₀.mem (x.setWidth 64))[k] := by
    rw [hw, lo_rd64, Nat.add_zero]
  have whi : s₀.mem.readW (addr x (8 * k + 4)) 32 = hi (stateAt s₀.mem (x.setWidth 64))[k] := by
    rw [hw, hi_rd64]
  simp only [outW, List.cons_append, List.nil_append]
  refine wp_movm (a := addr x (8 * k + 0)) (by rw [ea_at, hebx, Nat.add_zero])
    (by rw [h.rd, h.wr]; exact sub hbx hin 0 (by omega)) fun s₁ u₁ => ?_
  refine wp_movm (a := addr x (8 * k + 4)) (by rw [ea_at, u₁.other _ (by decide), hebx])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact sub hbx hin 4 (by omega)) fun s₂ u₂ =>
    wp_bswap fun s₃ u₃ => wp_bswap fun s₄ u₄ => ?_
  have heax₄ : s₄.gpr .eax = y := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), heax]
  refine wp_store (a := addr y (8 * k + 0)) (by rw [ea_at, heax₄, Nat.add_zero])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact sub hax hout 0 (by omega)) fun s₅ u₅ => ?_
  refine wp_store (a := addr y (8 * k + 4)) (by rw [ea_at, u₅.gpr, heax₄])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact sub hax hout 4 (by omega)) fun s₆ u₆ =>
    hnext s₆ ⟨fun r h1 h2 => ?_, by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
      by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], ?_⟩
  · rw [u₆.gpr, u₅.gpr, u₄.other r h1, u₃.other r h2, u₂.other r h2, u₁.other r h1, h.gpr r h1 h2]
  · have v2 : s₄.gpr .edx = bswap (hi (stateAt s₀.mem (x.setWidth 64))[k]) := by
      rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.mem, hread 4 (by omega), whi]
    have v1 : s₅.gpr .ecx = bswap (lo (stateAt s₀.mem (x.setWidth 64))[k]) := by
      rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hread 0 (by omega), wlo]
    have a0 : addr y (8 * k + 0) = y.setWidth 64 +
        BitVec.ofNat 64 (((stateAt s₀.mem (x.setWidth 64)).toList.take k).flatMap wordBytes).length := by
      rw [hP, addr_eq (by omega), Nat.add_zero]
    have a4 : addr y (8 * k + 4) = y.setWidth 64 +
        BitVec.ofNat 64 (((stateAt s₀.mem (x.setWidth 64)).toList.take k).flatMap wordBytes).length +
        BitVec.ofNat 64 (Spec.Sha256.wordBytes (hi (stateAt s₀.mem (x.setWidth 64))[k])).length := by
      rw [hP, addr_eq (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]; rfl
    rw [u₆.mem, v1, u₅.mem, v2, u₄.mem, u₃.mem, u₂.mem, u₁.mem, writeW_bswap, writeW_bswap, a0, a4,
      writeBytes_append _ _ _ _ (by simp [Spec.Sha256.wordBytes]), ← wordBytes_split, h.mem,
      writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, Vector.getElem_toList]

theorem out512_ok : OutOk Proof.Sha512.md ((List.range 8).flatMap outW) := by
  intro s₀ hbx hax hin hout hd
  have all : ∀ j ≤ 8, ∀ s, Out512 s₀ (8 - j) s → WP isa (.block (((List.range 8).drop (8 - j)).flatMap outW)) s
      fun s' => Out512 s₀ 8 s' := by
    intro j
    induction j with
    | zero =>
      intro _ s h
      rw [show (List.range 8).drop (8 - 0) = [] from rfl, List.flatMap_nil]
      exact WP.block_nil h
    | succ j ih =>
      intro hj s h
      rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.getElem_range]
      refine out512_step hbx hax hin hout hd (by omega) h fun s' h' => ?_
      rw [show 8 - (j + 1) + 1 = 8 - j by omega] at h' ⊢
      exact ih (by omega) s' h'
  have := all 8 (Nat.le_refl _) s₀ ⟨fun _ _ _ => rfl, rfl, rfl, by simp [writeBytes_nil]⟩
  rw [show 8 - 8 = 0 from rfl, List.drop_zero] at this
  refine WP.mono this fun s' h => ⟨h.gpr, h.rd, h.wr, ?_⟩
  rw [h.mem, List.take_of_length_le (by simp)]
  rfl

end

/-! ## What the proofs know of them -/

/-- The weaker register guarantee `OutOk` asks of `Impl.MdStream.X86`'s
`out`, from its `Shape`. -/
theorem outOk_of_shape {P : Impl.MdStream.X86.Params} {H : Md 64 P.N 8} (hs : Proof.MdStream.X86.Shape H) :
    OutOk H P.out := fun s hbx hax hin hout hd =>
  WP.mono (hs.out s hbx hax hin hout hd) fun _ ⟨g, rd, wr, m⟩ => ⟨fun r h _ => g r h, rd, wr, m⟩

def md5Ok : MdOk md5M where
  hH := md5OK
  md := Proof.Md5.md
  iv := Spec.Md5.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Md5.hash m = _
    rw [Proof.Md5.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm, by decide, by decide⟩
  back _ _ _ h := h
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 16) h (by omega)
  tail := by decide
  out := outOk_of_shape Proof.Md5.X86.Stream.shape
  comp := ⟨Proof.Md5.X86.compress_verified, NoSp.of_all (by lit_decide), by lit_decide⟩
  sizes := ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩

def sha1Ok : MdOk sha1M where
  hH := sha1OK
  md := Proof.Sha1.md
  iv := Spec.Sha1.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha1.hash m = _
    rw [Proof.Sha1.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm, by decide, by decide⟩
  back _ _ _ h := h
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega)
  tail := by decide
  out := outOk_of_shape Proof.Sha1.X86.Stream.shape
  comp := ⟨Proof.Sha1.X86.compress_verified, NoSp.of_all (by lit_decide), by lit_decide⟩
  sizes := ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩

/-- `MdOk` for a member of the SHA-512 family, whose digest is the first `D`
bytes of the final hash value. -/
def sha512Ok {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue}
    (hO : VG.Proof.Hmac.Generic.X86.HashOK (sha512H D initN iv)) (hR : hO.SH.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, hO.SH.H.hash m = (Spec.Sha512.finalHash iv m).take D) (hB : hO.SH.H.blockSize = 128)
    (hS : hO.SH.stateBytes = 192) (hD : hO.SH.digestBytes = D) (hD64 : D ≤ 64)
    (tail : Proof.Sha512.md.tailPad D = (sha512M D initN iv).tailB) (sizes : Sizes (sha512M D initN iv)) :
    MdOk (sha512M D initN iv) where
  hH := hO
  md := Proof.Sha512.md
  iv := iv
  link := ⟨hB, hS, hD, fun _ _ _ h => by rw [hR] at h; exact h, hh, hD64, by have := sizes.DL; omega⟩
  back _ _ _ h := by rw [hR]; exact h
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega)
  tail := tail
  out := out512_ok
  comp := ⟨Proof.Sha512.X86.Compress.compress_verified, Proof.Sha512.X86.Stream.compress_nosp,
    Proof.Sha512.X86.Stream.compress_stackUse⟩
  sizes := sizes

def sha384Ok : MdOk sha384M := sha512Ok sha384OK rfl (fun _ => rfl) rfl rfl rfl (by decide) (by decide) ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩
def sha512Ok' : MdOk sha512M' := sha512Ok sha512OK rfl
  (fun m => (List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))).symm)
  rfl rfl rfl (by decide) (by decide) ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩
def sha512_224Ok : MdOk sha512_224M := sha512Ok sha512_224OK rfl (fun _ => rfl) rfl rfl rfl (by decide)
  (by decide) ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩
def sha512_256Ok : MdOk sha512_256M := sha512Ok sha512_256OK rfl (fun _ => rfl) rfl rfl rfl (by decide)
  (by decide) ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩

end VG.Proof.Pbkdf2.Md.X86
