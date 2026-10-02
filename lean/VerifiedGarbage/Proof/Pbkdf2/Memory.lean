import VerifiedGarbage.Proof.Pbkdf2.Hmac
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Hmac.Common

/-!
# PBKDF2-HMAC-SHA-256's iteration: memory lemmas

Facts about bytes of memory, regions, the exclusive-or of words and the
iteration itself that the proofs of every target share, so that none imports
another target's proof.
-/

namespace VG.Proof.Pbkdf2.Memory

open VG.Proof.Sha256.Stream (writeBytes writeBytes_append write_eq_writeBytes)
open VG.Spec.Sha256 (bytesAt stateAt blockAt HashValue)
open VG.Proof.Hmac.Common (bytesAt_add read_congr₂ stateAt_eq_of_bytes writeBytes_at bytesAt_getD'
  bytesAt_length bytesAt_writeBytes_self)

/-! ## Helpers

Copies of lemmas of the x86-64 SHA-256 proofs, which this module does not
import; the lemmas about bytes are the target-independent HMAC ones
(`Proof/Hmac/Common.lean`). -/

private theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

private theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := by
  intro a ha
  simp only [Region.Contains] at *
  have : (a - base).toNat ≤ (a - (base + BitVec.ofNat 64 off)).toNat + off := by
    rw [show a - base = (a - (base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by bv_omega,
      BitVec.toNat_add, toNat_ofNat_lt ho]
    exact Nat.mod_le _ _
  omega

/-! ## Memory -/

theorem frame_bytesAt {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem contains_base {a : Addr} {n len : Nat} (h : n ≤ len) : (⟨a, len⟩ : Region).Contains a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem off_contains {a x : Addr} {o n len : Nat} (h : (x - (a + BitVec.ofNat 64 o)).toNat < n)
    (hl : o + n ≤ len) (ho : o < 2 ^ 64) : (⟨a, len⟩ : Region).Contains x 1 :=
  sub_offset (off := o) (len := n) hl ho x (by simp only [Region.Contains]; omega)

/-- Bytes from `p + a` are not among the first `a` from `p`. -/
theorem sep_after {p x : Addr} {a n : Nat} (h₁ : (x - (p + BitVec.ofNat 64 a)).toNat < n) (h₂ : (x - p).toNat < a)
    (ha : a + n < 2 ^ 64) : False := by
  rw [show x - p = (x - (p + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by bv_omega, BitVec.toNat_add,
    toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h₂
  omega

/-- A block of 32 bytes followed by the padding. -/
theorem blockAt_eq {m : Mem} {p : Addr} (h : bytesAt m (p + 32) 32 = pad96) :
    blockAt m p = block96 (bytesAt m p 32) := by
  simp only [Spec.Sha256.blockAt, block96]
  apply Proof.Sha256.Stream.parseBlock_congr
  intro k hk
  have e := bytesAt_add m p 32 32
  rw [show BitVec.ofNat 64 32 = (32 : Addr) from rfl, h] at e
  rw [← e, bytesAt_getD' _ _ (by omega : k < 32 + 32)]

theorem writeW_xor (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 64 ^^^ m'.readW b 64) =
      writeBytes m d (Spec.Pbkdf2.xorBytes (bytesAt m' b 8) (bytesAt m' a 8)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (64 : Nat) / 8 = 8 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [Spec.Pbkdf2.xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [Spec.Pbkdf2.xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁, BitVec.xor_comm]

theorem xorBytes_length (a b : List Byte) (h : a.length = b.length) :
    (Spec.Pbkdf2.xorBytes a b).length = a.length := by
  simp [Spec.Pbkdf2.xorBytes, h]

/-- A copied hash value. -/
theorem stateAt_copy (m m' : Mem) (q p : Addr) :
    stateAt (writeBytes m q (bytesAt m' p 32)) q = stateAt m' p := by
  apply stateAt_eq_of_bytes
  intro i hi
  rw [writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ hi]

theorem digest_self (m : Mem) (q : Addr) (H : HashValue) :
    bytesAt (writeBytes m q (Pbkdf2.digest H)) q 32 = Pbkdf2.digest H := by
  have := bytesAt_writeBytes_self m q (Pbkdf2.digest H) (by rw [Pbkdf2.digest_length]; omega)
  rwa [Pbkdf2.digest_length] at this

theorem writeW_bytes (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) (xs : List Byte)
    (h : ((List.range (w / 8)).map fun j => (v.setWidth (8 * (w / 8))).extractLsb' (8 * j) 8) = xs) :
    m.writeW a v = writeBytes m a xs := by
  rw [Mem.writeW, write_eq_writeBytes, h]

theorem writeBytes_append' (m : Mem) {q q' : Addr} (xs ys : List Byte) (hq : q' = q + BitVec.ofNat 64 xs.length)
    (h : xs.length + ys.length < 2 ^ 64) : writeBytes (writeBytes m q xs) q' ys = writeBytes m q (xs ++ ys) := by
  subst hq; exact writeBytes_append m q xs ys h

/-! ## Regions -/

theorem add_ofNat (a : Addr) (o j : Nat) : a + BitVec.ofNat 64 o + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (o + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## The result -/

theorem iterate_congr {f g : List Byte → List Byte} (hfg : ∀ u, u.length = 32 → f u = g u)
    (hg : ∀ u, (g u).length = 32) :
    ∀ n u t, u.length = 32 → Spec.Pbkdf2.iterate f n u t = Spec.Pbkdf2.iterate g n u t := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro u t hu
    simp only [Spec.Pbkdf2.iterate]
    rw [hfg u hu]
    exact ih _ _ (hg u)

end VG.Proof.Pbkdf2.Memory
