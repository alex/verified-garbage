import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Md
import VerifiedGarbage.Impl.Hmac.X86_64
import VerifiedGarbage.Spec.Hmac
import VerifiedGarbage.Proof.Sha256.X86_64.Contract
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC-SHA-256 on x86-64: common lemmas

Untrusted: everything here is checked by Lean. Words copied between memory
regions (the lemmas about memory alone, shared by every target, are in
`Proof/Hmac/Common.lean`).
-/

namespace VG.Proof.Hmac

open Spec.Hmac
open Spec.Sha256 (Repr bytesAt)

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86-64 contract for
`vg_hmac_sha256_init(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 76])`,
for a key of at most 64 bytes (the SHA-256 block size): makes the streaming
state at `inner` represent `K₀ ⊕ ipad` and the one at `outer` represent
`K₀ ⊕ opad`, for the key `K₀` made of the `key_len` bytes at `key`.

The code may read `key` (`key_len` bytes) and read and write `inner` and
`outer` (96 bytes each) and `scratch` (608 bytes, whose contents on exit are
unspecified). These may not overlap each other, nor the return address on
the stack. The pointers and `key_len` are public; the key is secret. -/
def initSha256X86_64 : Contract X86_64.isa where
  pre s :=
    let inner : Region := ⟨s.gpr .rdi, 96⟩
    let outer : Region := ⟨s.gpr .rsi, 96⟩
    let key : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 608⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    (s.gpr .rcx).toNat ≤ 64 ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧ stack.Disjoint scratch
  post s s' :=
    let k0 := blockKey sha256 (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    Repr s'.mem (s.gpr .rdi) (xorPad k0 ipad) ∧ Repr s'.mem (s.gpr .rsi) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86-64 contract for
`vg_hmac_sha256_finalize(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, scratch: *mut [u64; 86])`:
if, for a 64-byte key `K₀` and a text, the streaming state at `inner`
represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes (modulo 2⁶⁴), and the one at
`outer` represents `K₀ ⊕ opad`, leaves the HMAC-SHA-256 of the text under
`K₀` in bytes 176 to 207 of `scratch`.

The MAC is left in `scratch` rather than written through a pointer of its
own so that the code can address every region from the two pointers it
keeps in registers across the inlined SHA-256 finalizations.

The code may read `outer` (96 bytes), and read and write `inner` (96 bytes,
whose contents on exit are unspecified) and `scratch` (688 bytes, whose
contents on exit are unspecified apart from the MAC). These may not overlap
each other, nor the return address on the stack. The pointers and `count`
are public; the states are secret. -/
def finalizeSha256X86_64 : Contract X86_64.isa where
  pre s :=
    let inner : Region := ⟨s.gpr .rdi, 96⟩
    let outer : Region := ⟨s.gpr .rsi, 96⟩
    let scratch : Region := ⟨s.gpr .rcx, 688⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 16, 16⟩
    s.rd = [outer] ∧ s.wr = [inner, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint scratch
  post s s' := ∀ k0 text, k0.length = 64 →
    Repr s.mem (s.gpr .rdi) (xorPad k0 ipad ++ text) →
    s.gpr .rdx = BitVec.ofNat 64 (64 + text.length) →
    Repr s.mem (s.gpr .rsi) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .rcx + 176) 32 = hmacBlockKey sha256 k0 text
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Hmac

namespace VG.Proof.Hmac.X86_64
open VG VG.X86_64
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.Hmac.Common (copy_mem bytesAt_zero)
open VG.Spec.Sha256 (bytesAt)

open VG.Impl.Sha256.X86_64 (at_)
open VG.Impl.Hmac.X86_64 (cp32 cp64)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov32m wp_store32 wp_movm wp_store)

theorem ea_off (s : State) (b : Reg) (o j : Nat) :
    s.ea (at_ b (o + j)) = s.gpr b + BitVec.ofNat 64 o + BitVec.ofNat 64 j := by
  simp only [State.ea, at_, Proof.Sha256.X86_64.ofInt_natCast, BitVec.ofNat_add, BitVec.add_assoc]

theorem copy32_ok {src dst : Reg} (hs : src ≠ .rax) (hd : dst ≠ .rax) (o₁ o₂ : Nat) (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (4 * n) (s.gpr dst + BitVec.ofNat 64 o₂) (4 * n) →
    4 * n < 2 ^ 64 →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (4 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (cp32 src dst o₁ o₂) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by rw [Nat.mul_zero, bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep hlt k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q (fun j hj => hin j (by omega_nat)) (fun j hj => hout j (by omega_nat))
      (fun x hx hy => hsep x (by omega_nat) (by omega_nat)) (by omega_nat) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [cp32, List.cons_append, List.nil_append]
    refine wp_mov32m (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * n))
      (by rw [ea_off, g₁ _ hs]) (by rw [rd₁, wr₁]; exact hin n (by omega_nat)) fun s₂ u₂ => ?_
    refine wp_store32 (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * n))
      (by rw [ea_off, u₂.other _ hd, g₁ _ hd]) (by rw [u₂.wr, wr₁]; exact hout n (by omega_nat))
      fun s₃ g₃ m₃ rd₃ wr₃ => k s₃ (fun r hr => by rw [g₃, u₂.other r hr, g₁ r hr])
        (by rw [rd₃, u₂.rd, rd₁]) (by rw [wr₃, u₂.wr, wr₁]) ?_
    rw [m₃, u₂.gpr, u₂.mem, m₁, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq,
      Nat.mul_succ]
    exact copy_mem s.mem _ _ n 4 (by rwa [← Nat.mul_succ]) (by omega_nat)

theorem copy64_ok {src dst : Reg} (hs : src ≠ .rax) (hd : dst ≠ .rax) (o₁ o₂ : Nat) (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (8 * k)) 8) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (8 * n) (s.gpr dst + BitVec.ofNat 64 o₂) (8 * n) →
    8 * n < 2 ^ 64 →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (8 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (cp64 src dst o₁ o₂) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by rw [Nat.mul_zero, bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep hlt k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q (fun j hj => hin j (by omega_nat)) (fun j hj => hout j (by omega_nat))
      (fun x hx hy => hsep x (by omega_nat) (by omega_nat)) (by omega_nat) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [cp64, List.cons_append, List.nil_append]
    refine wp_movm (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (8 * n))
      (by rw [ea_off, g₁ _ hs]) (by rw [rd₁, wr₁]; exact hin n (by omega_nat)) fun s₂ u₂ => ?_
    refine wp_store (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (8 * n))
      (by rw [ea_off, u₂.other _ hd, g₁ _ hd]) (by rw [u₂.wr, wr₁]; exact hout n (by omega_nat))
      fun s₃ g₃ m₃ rd₃ wr₃ => k s₃ (fun r hr => by rw [g₃, u₂.other r hr, g₁ r hr])
        (by rw [rd₃, u₂.rd, rd₁]) (by rw [wr₃, u₂.wr, wr₁]) ?_
    rw [m₃, u₂.gpr, u₂.mem, m₁, Nat.mul_succ]
    exact copy_mem s.mem _ _ n 8 (by rwa [← Nat.mul_succ]) (by omega_nat)

end VG.Proof.Hmac.X86_64
