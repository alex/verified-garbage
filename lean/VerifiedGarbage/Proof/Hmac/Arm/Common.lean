import VerifiedGarbage.Proof.Sha256.Arm.Stream.Md
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Common
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Impl.Hmac.Arm
import VerifiedGarbage.Spec.Hmac
import VerifiedGarbage.Proof.Sha256.Arm.Contract
import VerifiedGarbage.Proof.Hmac.Arm.Lit
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC-SHA-256 on ARMv7: common lemmas

Words copied between memory regions; the memory lemmas themselves are
target-independent and shared by every target (`VG.Proof.Hmac.Common`).
-/

namespace VG.Proof.Hmac

open Spec.Hmac
open Spec.Sha256 (Repr bytesAt)

open VG.Arm in
/-- 32-bit ARM contract for `vg_hmac_sha256_init(inner: *mut [u8; 96], outer:
*mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 20])`, for a
key of at most 64 bytes (the SHA-256 block size): makes the streaming state at
`inner` represent `K₀ ⊕ ipad` and the one at `outer` represent `K₀ ⊕ opad`, for
the key `K₀` made of the `key_len` bytes at `key`.

Under AAPCS, `inner`, `outer`, `key` and `key_len` are in `r0`–`r3`, and
`scratch` is the stack argument 0. The code may read that argument (4 bytes
at `sp`) and `key` (`key_len` bytes), and read and write `inner` and `outer`
(96 bytes each) and `scratch` (160 bytes, whose contents on exit are
unspecified). The writable buffers may not overlap each other, the key or
the argument; and nothing may wrap around the end of the (32-bit) address
space. `sp`, the pointers and `key_len` are public; the key is secret. -/
def initSha256Arm : Contract Arm.isa where
  pre s :=
    let inner : Region := ⟨State.addr (s.gpr .r0), 96⟩
    let outer : Region := ⟨State.addr (s.gpr .r1), 96⟩
    let key : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 160⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    (s.gpr .r3).toNat ≤ 64 ∧ s.rd = [key, args] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint outer ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 96 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 96 ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 160 ≤ 2 ^ 32 ∧
    s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' :=
    let k0 := blockKey sha256 (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    Repr s'.mem (State.addr (s.gpr .r0)) (xorPad k0 ipad) ∧
      Repr s'.mem (State.addr (s.gpr .r1)) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

open VG.Arm in
/-- 32-bit ARM contract for `vg_hmac_sha256_finalize(inner: *mut [u8; 96],
outer: *const [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64;
30])`: if, for a 64-byte key `K₀` and a text, the streaming state at `inner`
represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes (modulo 2⁶⁴), and the one at
`outer` represents `K₀ ⊕ opad`, writes the HMAC-SHA-256 of the text under `K₀`
to `out`.

Under AAPCS, `inner` and `outer` are in `r0` and `r1`, `count` in `r2:r3`,
and `out` and `scratch` are the stack arguments 0 and 1. The code may read
those arguments (8 bytes at `sp`) and `outer` (96 bytes), and read and write
`inner` (96 bytes, whose contents on exit are unspecified), `out` (32 bytes)
and `scratch` (240 bytes, whose contents on exit are unspecified). The
writable buffers may not overlap each other, `outer` or the arguments; and
nothing may wrap around the end of the (32-bit) address space. `sp`, the
pointers and `count` are public; the states are secret. -/
def finalizeSha256Arm : Contract Arm.isa where
  pre s :=
    let inner : Region := ⟨State.addr (s.gpr .r0), 96⟩
    let outer : Region := ⟨State.addr (s.gpr .r1), 96⟩
    let out : Region := ⟨State.addr (stackArg s 0), 32⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 240⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [outer, args] ∧ s.wr = [inner, out, scratch] ∧
    inner.Disjoint out ∧ inner.Disjoint scratch ∧ out.Disjoint scratch ∧
    outer.Disjoint inner ∧ outer.Disjoint out ∧ outer.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 96 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 96 ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 240 ≤ 2 ^ 32 ∧
    s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ k0 text, k0.length = 64 →
    Repr s.mem (State.addr (s.gpr .r0)) (xorPad k0 ipad ++ text) →
    Proof.Sha256.countArm s = BitVec.ofNat 64 (64 + text.length) →
    Repr s.mem (State.addr (s.gpr .r1)) (xorPad k0 opad) →
    bytesAt s'.mem (State.addr (stackArg s 0)) 32 = hmacBlockKey sha256 k0 text
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.Hmac

namespace VG.Proof.Hmac.Arm
open VG VG.Arm
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.Hmac.Common (copy_mem)
open VG.Spec.Sha256 (bytesAt)
open VG.Impl.Hmac.Arm (cp)
open VG.Proof.MdStream.Arm (Upd Mupd wp_ldr wp_str)

theorem add_off (p : Addr) (o j : Nat) :
    p + BitVec.ofNat 64 (o + j) = p + BitVec.ofNat 64 o + BitVec.ofNat 64 j := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- Copying `n` words from `[src + o₁]` to `[dst + o₂]`, through `t`. -/
theorem copy_ok {t src dst : Reg} (hs : src ≠ t) (hd : dst ≠ t) (o₁ o₂ : Nat) (n : Nat)
    (hb : o₁ + 4 * n ≤ 4096 ∧ o₂ + 4 * n ≤ 4096) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (s.gpr src).toNat + o₁ + 4 * n ≤ 2 ^ 32 → (s.gpr dst).toNat + o₂ + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr src) + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (State.addr (s.gpr src) + BitVec.ofNat 64 o₁) (4 * n)
      (State.addr (s.gpr dst) + BitVec.ofNat 64 o₂) (4 * n) →
    (∀ s', (∀ r, r ≠ t → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (State.addr (s.gpr dst) + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (State.addr (s.gpr src) + BitVec.ofNat 64 o₁) (4 * n)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (cp t src dst o₁ o₂) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl
      (by rw [Nat.mul_zero, VG.Proof.Hmac.Common.bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q fs fd hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih ⟨by omega_nat, by omega_nat⟩ _ s Q (by omega_nat) (by omega_nat) (fun j hj => hin j (by omega_nat))
      (fun j hj => hout j (by omega_nat)) (fun x hx hy => hsep x (by omega_nat) (by omega_nat))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [cp, List.cons_append, List.nil_append]
    refine wp_ldr (a := State.addr (s.gpr src) + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * n))
      (by omega_nat) (by rw [g₁ _ hs, addr_add (by omega_nat), add_off])
      (by rw [rd₁, wr₁]; exact hin n (by omega_nat)) fun s₂ u₂ => ?_
    refine wp_str (a := State.addr (s.gpr dst) + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * n))
      (by omega_nat) (by rw [u₂.other _ hd, g₁ _ hd, addr_add (by omega_nat), add_off])
      (by rw [u₂.wr, wr₁]; exact hout n (by omega_nat))
      fun s₃ u₃ => k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
        (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) (by rw [u₃.sp, u₂.sp, sp₁]) ?_
    rw [u₃.mem, u₂.gpr, u₂.mem, m₁, Nat.mul_succ]
    exact copy_mem s.mem _ _ n 4 (by rwa [← Nat.mul_succ]) (by omega_nat)

end VG.Proof.Hmac.Arm
