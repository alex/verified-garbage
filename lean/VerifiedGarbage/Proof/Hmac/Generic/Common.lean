import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.Spec.Md5
import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC over any streaming hash function: lemmas shared by every target

Untrusted: everything here is checked by Lean. Addresses and regions, the
bytes `init`'s loops write, and the streaming states of SHA-1, MD5 and the
SHA-512 family moved between addresses, about memory alone: every target's
proof uses them, so they import no target's ISA or proofs.
-/

namespace VG.Proof.Hmac.Generic.Common

open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeW8_apply)
open VG.Proof.Hmac.Common (bytesAt_add bytesAt_length bytesAt_writeBytes_self read_congr₂)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad)

private theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

private theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [Offset.add_sub_cancel_left, toNat_ofNat_lt ho]
  exact h

/-! ## Bytes -/

/-- A byte written is a one-byte `writeBytes`. -/
theorem writeW_byte (m : Mem) (a : Addr) (b : Byte) : m.writeW a b = writeBytes m a [b] := by
  funext x
  rw [writeW8_apply]
  simp only [writeBytes, List.length_singleton]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 1 := fun h' => h (by
      have : (x - a).toNat = 0 := by omega_nat
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by simpa using this)
      rw [BitVec.sub_eq_iff_eq_add] at this; simpa using this)
    simp only [h, this, ↓reduceIte]

/-- One more byte written after `k`. -/
theorem writeBytes_snoc (m : Mem) (q : Addr) (xs : List Byte) (b : Byte) (hl : xs.length + 1 < 2 ^ 64) :
    (writeBytes m q xs).writeW (q + BitVec.ofNat 64 xs.length) b = writeBytes m q (xs ++ [b]) := by
  rw [writeW_byte, writeBytes_append _ _ _ _ (by simpa using hl)]

theorem bytesAt_snoc' (m : Mem) (p : Addr) (k : Nat) :
    bytesAt m p (k + 1) = bytesAt m p k ++ [m (p + BitVec.ofNat 64 k)] := by
  rw [bytesAt_add]; simp [bytesAt]

theorem bytesAt_prefix_congr {m m' : Mem} {p : Addr} {j : Nat} (h : ∀ i < j, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    bytesAt m' p j = bytesAt m p j := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem bytesAt_take (m : Mem) (p : Addr) {D F : Nat} (h : D ≤ F) :
    bytesAt m p D = (bytesAt m p F).take D := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem bytesAt_writeBytes_self' {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} (hl : xs.length = n)
    (hn : n < 2 ^ 64) : bytesAt (writeBytes m q xs) q n = xs := by
  subst hl; exact bytesAt_writeBytes_self m q xs hn

theorem xorBytes_snoc (a b : List Byte) (x y : Byte) (h : a.length = b.length) :
    Spec.Pbkdf2.xorBytes (a ++ [x]) (b ++ [y]) = Spec.Pbkdf2.xorBytes a b ++ [x ^^^ y] := by
  simp [Spec.Pbkdf2.xorBytes, List.zipWith_append h]

theorem xorBytes_length' (a b : List Byte) (h : a.length = b.length) :
    (Spec.Pbkdf2.xorBytes a b).length = a.length := by
  simp [Spec.Pbkdf2.xorBytes, h]

theorem take_map_xor {K : List Byte} {n : Nat} (h : K.length = n) (p : Byte) :
    (K.take n).map (· ^^^ p) = xorPad K p := by
  rw [List.take_of_length_le (by omega_nat)]; rfl

/-! ## Addresses and regions -/

theorem add_ofNat_ne (p : Addr) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    p + BitVec.ofNat 64 a ≠ p + BitVec.ofNat 64 b := fun e =>
  h (by
    have := congrArg BitVec.toNat ((BitVec.add_right_inj p).mp e)
    rwa [toNat_ofNat_lt ha, toNat_ofNat_lt hb] at this)

theorem add_ofNat_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Every byte of a sub-region of a region in `rs` is in `rs`. -/
theorem inRegions_of_sub {rs : List Region} {R : Region} (hR : R ∈ rs) {p : Addr} {n : Nat}
    (hs : Region.Sub ⟨p, n⟩ R) (hn : n < 2 ^ 64) {k : Nat} (hk : k < n) :
    InRegions rs (p + BitVec.ofNat 64 k) 1 :=
  ⟨R, hR, hs _ (contains_offset (by omega_nat) (by omega_nat))⟩

/-- A byte of `⟨p, n⟩` is not among the first `k ≤ n` of a disjoint region. -/
theorem not_mem_of_disjoint {p q : Addr} {n k j : Nat} (hd : Region.Disjoint ⟨p, n⟩ ⟨q, n⟩) (hj : j < n)
    (hk : k ≤ n) (hn : n < 2 ^ 64) : ¬ ((p + BitVec.ofNat 64 j) - q).toNat < k := fun h =>
  hd _ (contains_offset (base := p) (len := n) (off := j) (n := 1)
    (by omega_nat) (by omega_nat)) (by
    show ((p + BitVec.ofNat 64 j) - q).toNat + 1 ≤ n; omega_nat)

theorem InRegions.right' {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- Parts of a region at offsets `a` and `b` do not overlap. -/
theorem off_disj (p : Addr) {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m < 2 ^ 64)
    (hb : b + n < 2 ^ 64) :
    Region.Disjoint ⟨p + BitVec.ofNat 64 a, m⟩ ⟨p + BitVec.ofNat 64 b, n⟩ :=
  Offset.disjoint p h (by omega_nat) (by omega_nat)

/-- The start of a region and a part of it at offset `b`. -/
theorem off_disj0 (p : Addr) {m b n : Nat} (h : m ≤ b) (hb : b + n < 2 ^ 64) :
    Region.Disjoint ⟨p, m⟩ ⟨p + BitVec.ofNat 64 b, n⟩ :=
  Offset.base_disjoint p h (by omega_nat)

/-- A region of `rs` covers itself (each target's `Covers [r] rs`). -/
theorem covers_one {rs : List Region} {r : Region} (h : r ∈ rs) :
    ∀ a n, InRegions [r] a n → InRegions rs a n := fun _ _ ⟨r', hr', hc⟩ => by
  simp only [List.mem_singleton] at hr'
  exact ⟨r, h, hr' ▸ hc⟩

theorem sub_of_off {rs : List Region} {base : Addr} {L : Nat} (h : ⟨base, L⟩ ∈ rs) {o n : Nat}
    (hn : o + n ≤ L) : ∃ r' ∈ rs, ∃ off, (⟨base + BitVec.ofNat 64 o, n⟩ : Region).base =
      r'.base + BitVec.ofNat 64 off ∧ off + (⟨base + BitVec.ofNat 64 o, n⟩ : Region).len ≤ r'.len :=
  ⟨_, h, o, rfl, hn⟩

theorem sub_of_self {rs : List Region} {r : Region} (h : r ∈ rs) {n : Nat} (hn : n ≤ r.len) :
    ∃ r' ∈ rs, ∃ off, (⟨r.base, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + (⟨r.base, n⟩ : Region).len ≤ r'.len :=
  ⟨r, h, 0, by simp, by simpa using hn⟩

theorem bytes_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  bytesAt_prefix_congr fun _ hi => hf.bytes (R := ⟨p, n⟩) hd hn hi

theorem readW_writeW_ne (m : Mem) {a b : Addr} (v : BitVec 64) (h : Region.Disjoint ⟨a, 8⟩ ⟨b, 8⟩) :
    (m.writeW b v).readW a 64 = m.readW a 64 :=
  (Frame.writeW (Frame.refl [⟨b, 8⟩] m) (r := ⟨b, 8⟩) (List.mem_singleton_self _) v
    (Region.contains_self _ _)).readW (r := ⟨a, 8⟩)
    (Region.contains_self _ _) (by simpa using h) (by decide)

/-! ## `init`'s key and pad loops

`K₀ ⊕ ipad` is written at `P` and `K₀ ⊕ opad` at `P + B`, byte by byte: first
the key's `kl` bytes (read at `K`), then the zeros that pad it to `B`. -/

section
variable (B : Nat) (P K : Addr) (K0 : List Byte) (m₀ : Mem)

/-- `j` bytes of each block written, and nothing else. -/
structure BufMem (j : Nat) (m : Mem) : Prop where
  bufI : bytesAt m P j = (K0.take j).map (· ^^^ Spec.Hmac.ipad)
  bufO : bytesAt m (P + BitVec.ofNat 64 B) j = (K0.take j).map (· ^^^ Spec.Hmac.opad)
  frame : Frame [⟨P, 2 * B⟩] m₀ m

end

theorem buf_write {B : Nat} {P : Addr} {K0 : List Byte} {m₀ : Mem} {j : Nat} {m : Mem}
    (h : BufMem B P K0 m₀ j m) (hB : B ≤ 128) (hj : j < B) (hl : j < K0.length) :
    BufMem B P K0 m₀ (j + 1) ((m.writeW (P + BitVec.ofNat 64 j) (K0[j] ^^^ Spec.Hmac.ipad)).writeW
      (P + BitVec.ofNat 64 B + BitVec.ofNat 64 j) (K0[j] ^^^ Spec.Hmac.opad)) := by
  have neI : ∀ i < B, P + BitVec.ofNat 64 i ≠ P + BitVec.ofNat 64 B + BitVec.ofNat 64 j := fun i hi => by
    rw [add_ofNat_add]; exact add_ofNat_ne _ (by omega_nat) (by omega_nat) (by omega_nat)
  have neO : ∀ i < j, P + BitVec.ofNat 64 B + BitVec.ofNat 64 i ≠ P + BitVec.ofNat 64 j := fun i hi => by
    rw [add_ofNat_add]; exact add_ofNat_ne _ (by omega_nat) (by omega_nat) (by omega_nat)
  refine ⟨?_, ?_, ?_⟩
  · rw [bytesAt_snoc', List.take_succ_eq_append_getElem hl, List.map_append, ← h.bufI]
    congr 1
    · refine bytesAt_prefix_congr fun i hi => ?_
      simp only [writeW8_apply, neI i (by omega_nat),
        add_ofNat_ne P (a := i) (b := j) (by omega_nat) (by omega_nat) (by omega_nat), ↓reduceIte]
    · simp only [writeW8_apply, neI j hj, ↓reduceIte, List.map_cons, List.map_nil]
  · rw [bytesAt_snoc', List.take_succ_eq_append_getElem hl, List.map_append, ← h.bufO]
    congr 1
    · refine bytesAt_prefix_congr fun i hi => ?_
      have e1 : P + BitVec.ofNat 64 B + BitVec.ofNat 64 i ≠ P + BitVec.ofNat 64 B + BitVec.ofNat 64 j := by
        rw [add_ofNat_add, add_ofNat_add]; exact add_ofNat_ne _ (by omega_nat) (by omega_nat) (by omega_nat)
      simp only [writeW8_apply, e1, neO i hi, ↓reduceIte]
    · simp only [writeW8_apply, ↓reduceIte, List.map_cons, List.map_nil]
  · refine (h.frame.writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
    · exact contains_offset (by omega_nat) (by omega_nat)
    · rw [add_ofNat_add]; exact contains_offset (by omega_nat) (by omega_nat)

/-- The key: its `kl` bytes at `K`, then zeros up to `B`. -/
def K0 (m : Mem) (K : Addr) (kl B : Nat) : List Byte := bytesAt m K kl ++ List.replicate (B - kl) 0

theorem K0_length (m : Mem) (K : Addr) {kl B : Nat} (h : kl ≤ B) : (K0 m K kl B).length = B := by
  simp [K0, bytesAt_length]; omega_nat

theorem K0_lt {m : Mem} {K : Addr} {kl B j : Nat} (hj : j < kl) (h : j < (K0 m K kl B).length) :
    (K0 m K kl B)[j] = m (K + BitVec.ofNat 64 j) := by
  simp only [K0]
  rw [List.getElem_append_left (by rw [bytesAt_length]; exact hj)]
  simp [bytesAt]

theorem K0_ge {m : Mem} {K : Addr} {kl B j : Nat} (hj : kl ≤ j) (h : j < (K0 m K kl B).length) :
    (K0 m K kl B)[j] = 0 := by
  simp only [K0]
  rw [List.getElem_append_right (by rw [bytesAt_length]; exact hj)]
  simp

/-! ## The hash functions' states, moved -/

/-- A word read at the same offset from two addresses whose bytes agree. -/
theorem readW_reloc {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ i < n, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) {o w : Nat}
    (hw : o + w / 8 ≤ n) :
    m'.readW (q + BitVec.ofNat 64 o) w = m.readW (p + BitVec.ofNat 64 o) w := by
  simp only [Mem.readW]
  refine congrArg (BitVec.setWidth _) ?_
  refine read_congr₂ fun i hi => ?_
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, h (o + i) (by omega_nat)]

/-- Bytes read at the same offset from two addresses whose bytes agree. -/
theorem bytesAt_reloc {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ i < n, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) {o k : Nat}
    (hk : o + k ≤ n) :
    Spec.Sha256.bytesAt m' (q + BitVec.ofNat 64 o) k = Spec.Sha256.bytesAt m (p + BitVec.ofNat 64 o) k := by
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, h (o + i) (by omega_nat)]

theorem sha1_repr (m m' : Mem) (p q : Addr) (msg : List Byte)
    (h : ∀ i < 84, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha1.Repr m p msg) : Spec.Sha1.Repr m' q msg := by
  refine ⟨?_, ?_⟩
  · rw [← hr.1]
    apply Vector.ext
    intro j hj
    simp only [Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact readW_reloc h (by omega_nat)
  · rw [← hr.2]
    exact bytesAt_reloc h (o := 20) (k := msg.length % 64) (by omega_nat)

theorem md5_repr (m m' : Mem) (p q : Addr) (msg : List Byte)
    (h : ∀ i < 80, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : Spec.Md5.Repr m p msg) : Spec.Md5.Repr m' q msg := by
  refine ⟨?_, ?_⟩
  · rw [← hr.1]
    apply Vector.ext
    intro j hj
    simp only [Spec.Md5.stateAt, Vector.getElem_ofFn]
    exact readW_reloc h (by omega_nat)
  · rw [← hr.2]
    exact bytesAt_reloc h (o := 16) (k := msg.length % 64) (by omega_nat)

theorem sha512_repr (iv : Spec.Sha512.HashValue) (m m' : Mem) (p q : Addr) (msg : List Byte)
    (h : ∀ i < 192, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha512.Repr iv m p msg) : Spec.Sha512.Repr iv m' q msg := by
  refine ⟨?_, ?_⟩
  · rw [← hr.1]
    apply Vector.ext
    intro j hj
    simp only [Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact readW_reloc h (by omega_nat)
  · rw [← hr.2]
    exact bytesAt_reloc h (o := 64) (k := msg.length % 128) (by omega_nat)

theorem finalHash_length (iv : Spec.Sha512.HashValue) (m : List Byte) :
    (Spec.Sha512.finalHash iv m).length = 64 := by
  simp [Spec.Sha512.finalHash, Spec.Sha512.wordBytes, List.map_const']

end VG.Proof.Hmac.Generic.Common
