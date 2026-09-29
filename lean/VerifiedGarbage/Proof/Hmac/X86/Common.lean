import VerifiedGarbage.Proof.Sha256.X86.Stream.Finalize
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Impl.Hmac.X86

/-!
# HMAC-SHA-256 on x86 (32-bit): common lemmas

Untrusted: everything here is checked by Lean. Words copied between memory
regions, byte-swapped or not.
-/

namespace VG.Proof.Hmac.X86

open VG VG.X86 VG.Impl.Hmac.X86
open VG.Proof.Sha256.X86.Stream
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil)
open VG.Proof.Hmac.Common (writeW_readW bytesAt_add bytesAt_writeBytes_sep)
open VG.Proof.Sha256.X86.Stream.Finalize (writeW_bswap)
open VG.Spec.Sha256 (bytesAt wordBytes)

/-- The bytes of `n` words at `[x + o]`, each big-endian. -/
def beWords (m : Mem) (x : BitVec 32) (o n : Nat) : List Byte :=
  (List.range n).flatMap fun k => wordBytes (m.readW (addr x (o + 4 * k)) 32)

theorem beWords_length (m : Mem) (x : BitVec 32) (o n : Nat) : (beWords m x o n).length = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [beWords, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append] at ih ⊢
    rw [ih]; simp [wordBytes]; omega

theorem beWords_succ (m : Mem) (x : BitVec 32) (o n : Nat) :
    beWords m x o (n + 1) = beWords m x o n ++ wordBytes (m.readW (addr x (o + 4 * n)) 32) := by
  simp [beWords, List.range_succ, List.flatMap_append]

/-- A word of `n` words at `[x + o]`, within the 32-bit address space. -/
theorem addr_word {x : BitVec 32} {o n k : Nat} (h : x.toNat + o + 4 * n ≤ 2 ^ 32) (hk : k < n) :
    addr x (o + 4 * k) = x.setWidth 64 + BitVec.ofNat 64 o + BitVec.ofNat 64 (4 * k) := by
  rw [addr_eq (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Reading a word outside the bytes written. -/
theorem readW_writeBytes_sep (m : Mem) {a q : Addr} (xs : List Byte) (h : Mem.Sep a 4 q xs.length) :
    (writeBytes m q xs).readW a 32 = m.readW a 32 := by
  simp only [Mem.readW]
  congr 1
  apply VG.Proof.Hmac.Common.read_congr₂
  intro i hi
  simp only [writeBytes]
  split
  · rename_i hlt
    refine (h (a + BitVec.ofNat 64 i) ?_ hlt).elim
    rw [show a + BitVec.ofNat 64 i - a = BitVec.ofNat 64 i by bv_omega, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rfl

/-- Copying `n` words from `[x + o₁]` to `[y + o₂]`, byte-swapped: the bytes
written are the words read, big-endian. -/
theorem bswapWords_ok {src dst : Reg} (hs : src ≠ .ecx) (hd : dst ≠ .ecx) {x y : BitVec 32} {o₁ o₂ : Nat}
    (n : Nat) : ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr src = x → s.gpr dst = y → x.toNat + o₁ + 4 * n ≤ 2 ^ 32 → y.toNat + o₂ + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions (s.rd ++ s.wr) (addr x (o₁ + 4 * k)) 4) →
    (∀ k < n, InRegions s.wr (addr y (o₂ + 4 * k)) 4) →
    Mem.Sep (x.setWidth 64 + BitVec.ofNat 64 o₁) (4 * n) (y.setWidth 64 + BitVec.ofNat 64 o₂) (4 * n) →
    (∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (y.setWidth 64 + BitVec.ofNat 64 o₂) (beWords s.mem x o₁ n) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (bswapWord src dst o₁ o₂) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [beWords, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hx hy fx fy hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q hx hy (by omega) (by omega) (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun a ha hb => hsep a (by omega) (by omega)) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [bswapWord, List.cons_append, List.nil_append]
    refine wp_movm (a := addr x (o₁ + 4 * n)) (by rw [ea_at, g₁ _ hs, hx])
      (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => wp_bswap fun s₃ u₃ => ?_
    refine wp_store (a := addr y (o₂ + 4 * n)) (by rw [ea_at, u₃.other _ hd, u₂.other _ hd, g₁ _ hd, hy])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega)) fun s₄ u₄ => ?_
    refine k s₄ (fun r hr => by rw [u₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr])
      (by rw [u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]) ?_
    have hrd : s₁.mem.readW (addr x (o₁ + 4 * n)) 32 = s.mem.readW (addr x (o₁ + 4 * n)) 32 := by
      rw [m₁, addr_word fx (by omega : n < n + 1)]
      simp only [Mem.readW]
      congr 1
      apply VG.Proof.Hmac.Common.read_congr₂
      intro i hi
      simp only [writeBytes]
      split
      · rename_i hlt
        rw [beWords_length] at hlt
        refine (hsep (x.setWidth 64 + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * n) + BitVec.ofNat 64 i) ?_
          (by omega)).elim
        rw [show x.setWidth 64 + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * n) + BitVec.ofNat 64 i -
            (x.setWidth 64 + BitVec.ofNat 64 o₁) = BitVec.ofNat 64 (4 * n + i) by
            rw [BitVec.ofNat_add]; bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega
      · rfl
    rw [u₄.mem, u₃.gpr, u₂.gpr, u₃.mem, u₂.mem, hrd, writeW_bswap, m₁, addr_word fy (by omega : n < n + 1),
      beWords_succ, ← writeBytes_append _ _ _ _ (by simp [beWords_length, wordBytes]; omega), beWords_length]

/-- Copying `n` words from `[x + o₁]` to `[y + o₂]`. -/
theorem copyWords_ok {src dst : Reg} (hs : src ≠ .ecx) (hd : dst ≠ .ecx) {x y : BitVec 32} {o₁ o₂ : Nat}
    (n : Nat) : ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr src = x → s.gpr dst = y → x.toNat + o₁ + 4 * n ≤ 2 ^ 32 → y.toNat + o₂ + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions (s.rd ++ s.wr) (addr x (o₁ + 4 * k)) 4) →
    (∀ k < n, InRegions s.wr (addr y (o₂ + 4 * k)) 4) →
    Mem.Sep (x.setWidth 64 + BitVec.ofNat 64 o₁) (4 * n) (y.setWidth 64 + BitVec.ofNat 64 o₂) (4 * n) →
    (∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (y.setWidth 64 + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 o₁) (4 * n)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (copyWord src dst o₁ o₂) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hx hy fx fy hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q hx hy (by omega) (by omega) (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun a ha hb => hsep a (by omega) (by omega)) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [copyWord, List.cons_append, List.nil_append]
    refine wp_movm (a := addr x (o₁ + 4 * n)) (by rw [ea_at, g₁ _ hs, hx])
      (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_store (a := addr y (o₂ + 4 * n)) (by rw [ea_at, u₂.other _ hd, g₁ _ hd, hy])
      (by rw [u₂.wr, wr₁]; exact hout n (by omega)) fun s₃ u₃ => ?_
    refine k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
      (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) ?_
    rw [u₃.mem, u₂.gpr, u₂.mem, addr_word fx (by omega : n < n + 1), addr_word fy (by omega : n < n + 1), m₁]
    have := VG.Proof.Hmac.Common.copy_mem s.mem (x.setWidth 64 + BitVec.ofNat 64 o₁)
      (y.setWidth 64 + BitVec.ofNat 64 o₂) n 4 (by rw [show 4 * n + 4 = 4 * (n + 1) by omega]; exact hsep)
      (by omega)
    simp only [Nat.reduceMul] at this
    rw [this, show 4 * (n + 1) = 4 * n + 4 by omega]

end VG.Proof.Hmac.X86
