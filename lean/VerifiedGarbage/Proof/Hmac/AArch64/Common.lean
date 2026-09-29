import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Md
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Common
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Impl.Hmac.AArch64
import VerifiedGarbage.Spec.Hmac
import VerifiedGarbage.Proof.Sha256.AArch64.Contract

/-!
# HMAC-SHA-256 on AArch64: common lemmas

Untrusted: everything here is checked by Lean. Words copied between memory
regions; the memory lemmas themselves are target-independent and shared by
every target (`VG.Proof.Hmac.Common`).
-/

namespace VG.Proof.Hmac

open Spec.Hmac
open Spec.Sha256 (Repr bytesAt)

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for
`vg_hmac_sha256_init(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 20])`,
for a key of at most 64 bytes (the SHA-256 block size): makes the streaming
state at `inner` represent `K₀ ⊕ ipad` and the one at `outer` represent
`K₀ ⊕ opad`, for the key `K₀` made of the `key_len` bytes at `key`.

The code may read `key` (`key_len` bytes) and read and write `inner` and
`outer` (96 bytes each) and `scratch` (160 bytes, whose contents on exit are
unspecified). These may not overlap each other, nor the 16 bytes below the
stack pointer (the frame saving `x30`), which do not wrap around. The
pointers and `key_len` are public; the key is secret. -/
def initSha256AArch64 : Contract AArch64.isa where
  pre s :=
    let inner : Region := ⟨s.gpr .x0, 96⟩
    let outer : Region := ⟨s.gpr .x1, 96⟩
    let key : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 160⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    (s.gpr .x3).toNat ≤ 64 ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧
    stack.Disjoint scratch
  post s s' :=
    let k0 := blockKey sha256 (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    Repr s'.mem (s.gpr .x0) (xorPad k0 ipad) ∧ Repr s'.mem (s.gpr .x1) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for
`vg_hmac_sha256_finalize(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, scratch: *mut [u64; 30])`:
if, for a 64-byte key `K₀` and a text, the streaming state at `inner`
represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes (modulo 2⁶⁴), and the one at
`outer` represents `K₀ ⊕ opad`, leaves the HMAC-SHA-256 of the text under
`K₀` in bytes 176 to 207 of `scratch`.

The MAC is left in `scratch`, as on x86-64, so that both targets share one
Rust signature (and one Rust wrapper).

The code may read `outer` (96 bytes), and read and write `inner` (96 bytes,
whose contents on exit are unspecified) and `scratch` (240 bytes, whose
contents on exit are unspecified apart from the MAC). These may not overlap
each other, nor the 32 bytes below the stack pointer (the frames saving `x30`
here and in `vg_sha256_finalize`), which do not wrap around. The pointers
and `count` are public; the states are secret. -/
def finalizeSha256AArch64 : Contract AArch64.isa where
  pre s :=
    let inner : Region := ⟨s.gpr .x0, 96⟩
    let outer : Region := ⟨s.gpr .x1, 96⟩
    let scratch : Region := ⟨s.gpr .x3, 240⟩
    let stack : Region := ⟨s.sp - 32, 32⟩
    s.rd = [outer] ∧ s.wr = [inner, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    32 ≤ s.sp.toNat ∧ stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint scratch
  post s s' := ∀ k0 text, k0.length = 64 →
    Repr s.mem (s.gpr .x0) (xorPad k0 ipad ++ text) →
    s.gpr .x2 = BitVec.ofNat 64 (64 + text.length) →
    Repr s.mem (s.gpr .x1) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .x3 + 176) 32 = hmacBlockKey sha256 k0 text
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.Hmac

namespace VG.Proof.Hmac.AArch64
open VG VG.AArch64
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.Hmac.Common (copy_mem)
open VG.Spec.Sha256 (bytesAt)
open VG.Impl.Hmac.AArch64 (cp32 cp64)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_ldr32 wp_str32 wp_ldr wp_str)

theorem add_off (p : Addr) (o j : Nat) :
    p + BitVec.ofNat 64 (o + j) = p + BitVec.ofNat 64 o + BitVec.ofNat 64 j := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem copy32_ok {src dst : Reg} (hs : src ≠ .x9) (hd : dst ≠ .x9) (o₁ o₂ : Nat) (n : Nat)
    (ho : o₁ % 4 = 0 ∧ o₂ % 4 = 0) (hb : o₁ + 4 * n ≤ 4096 * 4 ∧ o₂ + 4 * n ≤ 4096 * 4) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (4 * n) (s.gpr dst + BitVec.ofNat 64 o₂) (4 * n) →
    (∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (4 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (cp32 src dst o₁ o₂) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by rw [Nat.mul_zero, VG.Proof.Hmac.Common.bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih ⟨by omega, by omega⟩ _ s Q (fun j hj => hin j (by omega))
      (fun j hj => hout j (by omega)) (fun x hx hy => hsep x (by omega) (by omega))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [cp32, List.cons_append, List.nil_append]
    refine wp_ldr32 (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * n))
      ⟨by omega, by omega⟩ (by rw [g₁ _ hs, add_off]) (by rw [rd₁, wr₁]; exact hin n (by omega))
      fun s₂ u₂ => ?_
    refine wp_str32 (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * n))
      ⟨by omega, by omega⟩ (by rw [u₂.other _ hd, g₁ _ hd, add_off])
      (by rw [u₂.wr, wr₁]; exact hout n (by omega))
      fun s₃ u₃ => k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
        (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) (by rw [u₃.sp, u₂.sp, sp₁]) ?_
    rw [u₃.mem, u₂.gpr, u₂.mem, m₁, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq,
      Nat.mul_succ]
    exact copy_mem s.mem _ _ n 4 (by rwa [← Nat.mul_succ]) (by omega)

theorem copy64_ok {src dst : Reg} (hs : src ≠ .x9) (hd : dst ≠ .x9) (o₁ o₂ : Nat) (n : Nat)
    (ho : o₁ % 8 = 0 ∧ o₂ % 8 = 0) (hb : o₁ + 8 * n ≤ 4096 * 8 ∧ o₂ + 8 * n ≤ 4096 * 8) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (8 * k)) 8) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (8 * n) (s.gpr dst + BitVec.ofNat 64 o₂) (8 * n) →
    (∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (8 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (cp64 src dst o₁ o₂) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by rw [Nat.mul_zero, VG.Proof.Hmac.Common.bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih ⟨by omega, by omega⟩ _ s Q (fun j hj => hin j (by omega))
      (fun j hj => hout j (by omega)) (fun x hx hy => hsep x (by omega) (by omega))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [cp64, List.cons_append, List.nil_append]
    refine wp_ldr (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (8 * n))
      ⟨by omega, by omega⟩ (by rw [g₁ _ hs, add_off]) (by rw [rd₁, wr₁]; exact hin n (by omega))
      fun s₂ u₂ => ?_
    refine wp_str (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (8 * n))
      ⟨by omega, by omega⟩ (by rw [u₂.other _ hd, g₁ _ hd, add_off])
      (by rw [u₂.wr, wr₁]; exact hout n (by omega))
      fun s₃ u₃ => k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
        (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) (by rw [u₃.sp, u₂.sp, sp₁]) ?_
    rw [u₃.mem, u₂.gpr, u₂.mem, m₁, Nat.mul_succ]
    exact copy_mem s.mem _ _ n 8 (by rwa [← Nat.mul_succ]) (by omega)

end VG.Proof.Hmac.AArch64
