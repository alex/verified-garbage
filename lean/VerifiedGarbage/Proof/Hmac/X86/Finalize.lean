import Batteries.Logic
import VerifiedGarbage.Proof.Sha256.X86.Stream.Finalize
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Impl.Hmac.X86
import VerifiedGarbage.Proof.Hmac.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Spec.Hmac
import VerifiedGarbage.Proof.Sha256.X86.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Hmac.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.TaintWeaken
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC-SHA-256 on x86 (32-bit): `finalize`

The compressor-dependent correctness proof is generic in
`Proof/Hmac/Sha256/X86/Finalize.lean`; this module keeps the shared memory,
state and scalar constant-time facts. Lemmas `init` uses too, then `finalize`.
-/

/-!
## Common lemmas

Words copied between memory regions, byte-swapped or not.
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
    rw [ih]; simp [wordBytes]; omega_nat

theorem beWords_succ (m : Mem) (x : BitVec 32) (o n : Nat) :
    beWords m x o (n + 1) = beWords m x o n ++ wordBytes (m.readW (addr x (o + 4 * n)) 32) := by
  simp [beWords, List.range_succ, List.flatMap_append]

/-- A word of `n` words at `[x + o]`, within the 32-bit address space. -/
theorem addr_word {x : BitVec 32} {o n k : Nat} (h : x.toNat + o + 4 * n ≤ 2 ^ 32) (hk : k < n) :
    addr x (o + 4 * k) = x.setWidth 64 + BitVec.ofNat 64 o + BitVec.ofNat 64 (4 * k) := by
  rw [addr_eq (by omega_nat), BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Reading a word outside the bytes written. -/
theorem readW_writeBytes_sep (m : Mem) {a q : Addr} (xs : List Byte) (h : Mem.Sep a 4 q xs.length) :
    (writeBytes m q xs).readW a 32 = m.readW a 32 := by
  simp only [Mem.readW]
  refine congrArg (BitVec.setWidth 32) ?_
  apply VG.Proof.Hmac.Common.read_congr₂
  intro i hi
  simp only [writeBytes]
  split
  · rename_i hlt
    refine (h (a + BitVec.ofNat 64 i) ?_ hlt).elim
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_nat)]
    omega_nat
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
    refine ih _ s Q hx hy (by omega_nat) (by omega_nat) (fun j hj => hin j (by omega_nat)) (fun j hj => hout j (by omega_nat))
      (fun a ha hb => hsep a (by omega_nat) (by omega_nat)) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [bswapWord, List.cons_append, List.nil_append]
    refine wp_movm (a := addr x (o₁ + 4 * n)) (by rw [ea_at, g₁ _ hs, hx])
      (by rw [rd₁, wr₁]; exact hin n (by omega_nat)) fun s₂ u₂ => wp_bswap fun s₃ u₃ => ?_
    refine wp_store (a := addr y (o₂ + 4 * n)) (by rw [ea_at, u₃.other _ hd, u₂.other _ hd, g₁ _ hd, hy])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega_nat)) fun s₄ u₄ => ?_
    refine k s₄ (fun r hr => by rw [u₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr])
      (by rw [u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]) ?_
    have hrd : s₁.mem.readW (addr x (o₁ + 4 * n)) 32 = s.mem.readW (addr x (o₁ + 4 * n)) 32 := by
      rw [m₁, addr_word fx (by omega_nat : n < n + 1)]
      simp only [Mem.readW]
      refine congrArg (BitVec.setWidth 32) ?_
      apply VG.Proof.Hmac.Common.read_congr₂
      intro i hi
      simp only [writeBytes]
      split
      · rename_i hlt
        rw [beWords_length] at hlt
        refine (hsep (x.setWidth 64 + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * n) + BitVec.ofNat 64 i) ?_
          (by omega_nat)).elim
        rw [Offset.add_add (x.setWidth 64 + BitVec.ofNat 64 o₁), Offset.add_sub_cancel_left,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_nat)]
        omega_nat
      · rfl
    rw [u₄.mem, u₃.gpr, u₂.gpr, u₃.mem, u₂.mem, hrd, writeW_bswap, m₁, addr_word fy (by omega_nat : n < n + 1),
      beWords_succ, ← writeBytes_append _ _ _ _ (by simp [beWords_length, wordBytes]; omega_nat), beWords_length]

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
    refine ih _ s Q hx hy (by omega_nat) (by omega_nat) (fun j hj => hin j (by omega_nat)) (fun j hj => hout j (by omega_nat))
      (fun a ha hb => hsep a (by omega_nat) (by omega_nat)) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [copyWord, List.cons_append, List.nil_append]
    refine wp_movm (a := addr x (o₁ + 4 * n)) (by rw [ea_at, g₁ _ hs, hx])
      (by rw [rd₁, wr₁]; exact hin n (by omega_nat)) fun s₂ u₂ => ?_
    refine wp_store (a := addr y (o₂ + 4 * n)) (by rw [ea_at, u₂.other _ hd, g₁ _ hd, hy])
      (by rw [u₂.wr, wr₁]; exact hout n (by omega_nat)) fun s₃ u₃ => ?_
    refine k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
      (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) ?_
    rw [u₃.mem, u₂.gpr, u₂.mem, addr_word fx (by omega_nat : n < n + 1), addr_word fy (by omega_nat : n < n + 1), m₁]
    have := VG.Proof.Hmac.Common.copy_mem s.mem (x.setWidth 64 + BitVec.ofNat 64 o₁)
      (y.setWidth 64 + BitVec.ofNat 64 o₂) n 4 (by rw [show 4 * n + 4 = 4 * (n + 1) by omega_nat]; exact hsep)
      (by omega_nat)
    simp only [Nat.reduceMul] at this
    rw [this, show 4 * (n + 1) = 4 * n + 4 by omega_nat]

end VG.Proof.Hmac.X86

/-!
## `finalize`

The inner hash is the code of
`vg_sha256_finalize` up to writing the digest (`finalizeHash`), run on our
state with its permissions narrowed to those of `vg_sha256_finalize` and
reasoned about with that function's own proof (`WP.narrowSp`); the outer
hash is one compression of a block laid out at known offsets. The
compressions call the compression function, using the 20 bytes below `esp`.
-/

namespace VG.Proof.Hmac

open Spec.Hmac
open Spec.Sha256 (Repr bytesAt)

open VG.X86 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86 (32-bit) contract for
`vg_hmac_sha256_init(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 20])`,
whose arguments are on the stack (cdecl), for a key of at most 64 bytes (the
SHA-256 block size): makes the streaming state at `inner` represent
`K₀ ⊕ ipad` and the one at `outer` represent `K₀ ⊕ opad`, for the key `K₀`
made of the `key_len` bytes at `key`.

The code may read `key` (`key_len` bytes), and read and write the arguments
(20 bytes above the return address, whose contents on exit are unspecified),
`inner` and `outer` (96 bytes each) and `scratch` (160 bytes, whose contents
on exit are unspecified). The writable buffers may not overlap each other,
the key, the return address or the 20 bytes of stack below it (where the
code calls the compression function), and nothing may wrap around the end
of the (32-bit) address space. `esp`, the pointers and `key_len` are public;
the key is secret. -/
def initSha256X86 : Contract X86.isa where
  pre s :=
    let inner : Region := ⟨(arg s 0).setWidth 64, 96⟩
    let outer : Region := ⟨(arg s 1).setWidth 64, 96⟩
    let key : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 160⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    (arg s 3).toNat ≤ 64 ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch, args] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint outer ∧ args.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧ key.Disjoint args ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 96 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 96 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 160 ≤ 2 ^ 32 ∧
    20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' :=
    let k0 := blockKey sha256 (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
    Repr s'.mem ((arg s 0).setWidth 64) (xorPad k0 ipad) ∧
      Repr s'.mem ((arg s 1).setWidth 64) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

open VG.X86 in
/-- The 64-bit `count` argument of `vg_hmac_sha256_finalize`: its arguments
2 (the low word) and 3 (the high word). -/
def countFinalizeX86 (s : X86.State) : BitVec 64 := arg s 3 ++ arg s 2

open VG.X86 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86 (32-bit) contract for
`vg_hmac_sha256_finalize(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 30])`,
whose arguments are on the stack (cdecl: `inner`, `outer`, the low and high
words of `count`, `out`, `scratch`): if, for a 64-byte key `K₀` and a text,
the streaming state at `inner` represents `(K₀ ⊕ ipad) ‖ text`, of `count`
bytes (modulo 2⁶⁴), and the one at `outer` represents `K₀ ⊕ opad`, writes the
HMAC-SHA-256 of the text under `K₀` to `out`.

The code may read `outer` (96 bytes), and read and write the arguments (24
bytes above the return address, whose contents on exit are unspecified),
`inner` (96 bytes, whose contents on exit are unspecified), `out` (32 bytes)
and `scratch` (240 bytes, whose contents on exit are unspecified). The
writable buffers may not overlap each other, `outer` or the return address;
none of the buffers may overlap the 20 bytes of stack below the return
address (where the code calls the compression function); and nothing may
wrap around the end of the (32-bit) address space. `esp`, the pointers and
`count` are public; the states are secret. -/
def finalizeSha256X86 : Contract X86.isa where
  pre s :=
    let inner : Region := ⟨(arg s 0).setWidth 64, 96⟩
    let outer : Region := ⟨(arg s 1).setWidth 64, 96⟩
    let out : Region := ⟨(arg s 4).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 240⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [outer] ∧ s.wr = [inner, out, scratch, args] ∧
    inner.Disjoint out ∧ inner.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    outer.Disjoint inner ∧ outer.Disjoint out ∧ outer.Disjoint scratch ∧ outer.Disjoint args ∧
    ret.Disjoint inner ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 96 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 96 ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 5).toNat + 240 ≤ 2 ^ 32 ∧
    20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post s s' := ∀ k0 text, k0.length = 64 →
    Repr s.mem ((arg s 0).setWidth 64) (xorPad k0 ipad ++ text) →
    countFinalizeX86 s = BitVec.ofNat 64 (64 + text.length) →
    Repr s.mem ((arg s 1).setWidth 64) (xorPad k0 opad) →
    bytesAt s'.mem ((arg s 4).setWidth 64) 32 = hmacBlockKey sha256 k0 text
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

end VG.Proof.Hmac

namespace VG.Proof.Hmac.X86.Finalize

open VG VG.X86 VG.Impl.Hmac.X86
open VG.Impl.Sha256.X86 (at_)
open VG.Impl.Sha256.X86.Stream (compressAt restore saved)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame writeBytes_append repr_congr compressList_append
  hash_one lenBytes rest)
open VG.Proof.Hmac.X86
open VG.Proof.Hmac.Common (bytesAt_length)
open VG.Spec.Sha256 (HashValue stateAt blockAt compress parseBlock bytesAt wordBytes Repr)
open VG.Proof.Sha256 (countX86)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)
open VG.Proof.Hmac (countFinalizeX86)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev inn : BitVec 32 := arg s₀ 0
abbrev ou : BitVec 32 := arg s₀ 1
abbrev out : BitVec 32 := arg s₀ 4
abbrev scr : BitVec 32 := arg s₀ 5
abbrev inA : Addr := (inn s₀).setWidth 64
abbrev ouA : Addr := (ou s₀).setWidth 64
abbrev outA : Addr := (out s₀).setWidth 64
abbrev scA : Addr := (scr s₀).setWidth 64
abbrev inR : Region := ⟨inA s₀, 96⟩
abbrev ouR : Region := ⟨ouA s₀, 96⟩
abbrev outR : Region := ⟨outA s₀, 32⟩
abbrev scR : Region := ⟨scA s₀, 240⟩
abbrev argR : Region := ⟨addr (esp₀ s₀) 4, 24⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (esp₀ s₀) 20

/-- The regions `vg_sha256_finalize` gets: its state (our inner state), its
output (ours), the first 160 bytes of our scratch space, and the first 20
bytes of our arguments. -/
abbrev finW : List Region := [inR s₀, outR s₀, ⟨scA s₀, 160⟩, ⟨addr (esp₀ s₀) 4, 20⟩]

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [ouR s₀]
  wr : s₀.wr = [inR s₀, outR s₀, scR s₀, argR s₀]
  in_out : (inR s₀).Disjoint (outR s₀)
  in_scr : (inR s₀).Disjoint (scR s₀)
  out_scr : (outR s₀).Disjoint (scR s₀)
  a_in : (argR s₀).Disjoint (inR s₀)
  a_out : (argR s₀).Disjoint (outR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  o_in : (ouR s₀).Disjoint (inR s₀)
  o_out : (ouR s₀).Disjoint (outR s₀)
  o_scr : (ouR s₀).Disjoint (scR s₀)
  o_a : (ouR s₀).Disjoint (argR s₀)
  ret_in : (retR s₀).Disjoint (inR s₀)
  ret_out : (retR s₀).Disjoint (outR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_in : (stkR s₀).Disjoint (inR s₀)
  stk_ou : (stkR s₀).Disjoint (ouR s₀)
  stk_out : (stkR s₀).Disjoint (outR s₀)
  stk_scr : (stkR s₀).Disjoint (scR s₀)
  in_fit : (inn s₀).toNat + 96 ≤ 2 ^ 32
  ou_fit : (ou s₀).toNat + 96 ≤ 2 ^ 32
  out_fit : (out s₀).toNat + 32 ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 240 ≤ 2 ^ 32
  sp_lo : 20 ≤ (esp₀ s₀).toNat
  sp_fit : (esp₀ s₀).toNat + 28 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : Proof.Hmac.finalizeSha256X86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25⟩ := h
  have e := stk_eq h24
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    by show (below _ _).Disjoint _; rw [e]; exact h16, by show (below _ _).Disjoint _; rw [e]; exact h17,
    by show (below _ _).Disjoint _; rw [e]; exact h18, by show (below _ _).Disjoint _; rw [e]; exact h19,
    h20, h21, h22, h23, h24, h25⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem scr_in {d n : Nat} (hd : d + n ≤ 240) (hn : 0 < n) : (scR s₀).Contains (addr (scr s₀) d) n :=
  contains_addr hd hn hp.scr_fit

theorem in_in {d n : Nat} (hd : d + n ≤ 96) (hn : 0 < n) : (inR s₀).Contains (addr (inn s₀) d) n :=
  contains_addr hd hn hp.in_fit

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  unfold argR
  rw [addr_eq (by omega_nat), addr_eq (by omega_nat)]
  exact Offset.contains _ hd₁ (by omega_nat) (by omega_nat)

/-- A word of the scratch space, as a region. -/
theorem scr_sub {d : Nat} (hd : d + 4 ≤ 240) : Region.Sub ⟨addr (scr s₀) d, 4⟩ (scR s₀) := by
  rw [addr_eq (by have := hp.scr_fit; omega_nat)]
  exact sub_offset hd (by omega_nat)

/-- An argument word, as a region. -/
theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  unfold argR
  rw [addr_eq (by omega_nat), addr_eq (by omega_nat)]
  exact Offset.sub _ hd₁ (by omega_nat)

theorem arg_scr_sep {d e : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) (he : e + 4 ≤ 240) :
    Mem.Sep (addr (esp₀ s₀) d) 4 (addr (scr s₀) e) 4 := by
  intro x hx hy
  exact hp.a_scr x (hp.arg_sub hd₁ hd x (by simp only [Region.Contains]; omega_nat))
    (hp.scr_sub he x (by simp only [Region.Contains]; omega_nat))

theorem scr_arg_sep {d e : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) (he : e + 4 ≤ 240) :
    Mem.Sep (addr (scr s₀) e) 4 (addr (esp₀ s₀) d) 4 := by
  intro x hx hy
  exact hp.a_scr x (hp.arg_sub hd₁ hd x (by simp only [Region.Contains]; omega_nat))
    (hp.scr_sub he x (by simp only [Region.Contains]; omega_nat))

end Pre

theorem ret_a {s₀ : State} (hp : Pre s₀) : (retR s₀).Disjoint (argR s₀) := by
  have := hp.sp_fit
  unfold retR argR
  rw [addr_eq (by omega_nat)]
  exact Offset.base_disjoint _ (Nat.le_refl 4) (by omega_nat)

theorem ret_stk {s₀ : State} (hp : Pre s₀) : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_lo
  unfold retR stkR below
  rw [Taint.sub_setWidth (by omega_nat)]
  have h := Offset.disjoint_below_above ((esp₀ s₀).setWidth 64) (m := 20) (a := 0) (l := 4) (by omega_nat)
  rw [BitVec.add_zero] at h
  exact h.symm

/-! ## Rearranging the arguments -/

/-- Memory after the prologue: `outer` in `scratch[176]`, and the arguments
of `vg_sha256_finalize`. -/
def proMem (s₀ : State) : Mem :=
  ((((s₀.mem.writeW (addr (scr s₀) 176) (ou s₀)).writeW (addr (esp₀ s₀) 8) (arg s₀ 2)).writeW
    (addr (esp₀ s₀) 12) (arg s₀ 3)).writeW (addr (esp₀ s₀) 16) (out s₀)).writeW (addr (esp₀ s₀) 20) (scr s₀)

theorem proMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scR s₀, argR s₀] s₀.mem (proMem s₀) := by
  simp only [proMem]
  exact (((((Frame.refl _ _).writeW (by simp) _ (hp.scr_in (d := 176) (by omega_nat) (by omega_nat))).writeW (by simp) _
    (hp.arg_in (d := 8) (by omega_nat) (by omega_nat))).writeW (by simp) _ (hp.arg_in (d := 12) (by omega_nat) (by omega_nat))).writeW
    (by simp) _ (hp.arg_in (d := 16) (by omega_nat) (by omega_nat))).writeW (by simp) _
    (hp.arg_in (d := 20) (by omega_nat) (by omega_nat))

/-- Reading an argument word after the prologue. -/
theorem proMem_arg {s₀ : State} (hp : Pre s₀) (i : Nat) (hi : i < 5) :
    (proMem s₀).readW (addr (esp₀ s₀) (4 + 4 * i)) 32 =
      [inn s₀, arg s₀ 2, arg s₀ 3, out s₀, scr s₀].getD i 0 := by
  have := hp.sp_fit
  have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), 4 ≤ d → d + 4 ≤ 28 → 4 ≤ e → e + 4 ≤ 28 →
      d + 4 ≤ e ∨ e + 4 ≤ d →
      (m.writeW (addr (esp₀ s₀) e) v).readW (addr (esp₀ s₀) d) 32 = m.readW (addr (esp₀ s₀) d) 32 :=
    fun m v d e _ h₂ _ h₄ h => readW_writeW_addr m v (by omega_nat) (by omega_nat) h
  have s176 : ∀ d, 4 ≤ d → d + 4 ≤ 28 →
      (s₀.mem.writeW (addr (scr s₀) 176) (ou s₀)).readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 :=
    fun d h₁ h₂ => Mem.readW_writeW_sep (hp.arg_scr_sep h₁ h₂ (by omega_nat)) (by decide)
  rcases (by omega_nat : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> simp only [proMem, List.getD_cons_zero, List.getD_cons_succ]
  · rw [w _ _ 4 20 (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat),
      w _ _ 4 16 (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat),
      w _ _ 4 12 (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat),
      w _ _ 4 8 (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat), s176 4 (by omega_nat) (by omega_nat)]; rfl
  · rw [w _ _ 8 20 (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat),
      w _ _ 8 16 (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat),
      w _ _ 8 12 (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat), Mem.readW_writeW_self32]
  · rw [w _ _ 12 20 (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat),
      w _ _ 12 16 (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat), Mem.readW_writeW_self32]
  · rw [w _ _ 16 20 (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat) (by omega_nat), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

theorem proMem_176 {s₀ : State} (hp : Pre s₀) : (proMem s₀).readW (addr (scr s₀) 176) 32 = ou s₀ := by
  simp only [proMem]
  rw [Mem.readW_writeW_sep (hp.scr_arg_sep (d := 20) (by omega_nat) (by omega_nat) (by omega_nat)) (by decide),
    Mem.readW_writeW_sep (hp.scr_arg_sep (d := 16) (by omega_nat) (by omega_nat) (by omega_nat)) (by decide),
    Mem.readW_writeW_sep (hp.scr_arg_sep (d := 12) (by omega_nat) (by omega_nat) (by omega_nat)) (by decide),
    Mem.readW_writeW_sep (hp.scr_arg_sep (d := 8) (by omega_nat) (by omega_nat) (by omega_nat)) (by decide),
    Mem.readW_writeW_self32]

/-- After the prologue. -/
structure Pro (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  gpr : ∀ r, r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  mem : s.mem = proMem s₀

theorem pro_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block [.mov .edx (.mem (at_ .esp 24)), .mov .ecx (.mem (at_ .esp 8)), .store (at_ .edx 176) .ecx,
      .mov .ecx (.mem (at_ .esp 12)), .store (at_ .esp 8) .ecx,
      .mov .ecx (.mem (at_ .esp 16)), .store (at_ .esp 12) .ecx,
      .mov .ecx (.mem (at_ .esp 20)), .store (at_ .esp 16) .ecx, .store (at_ .esp 20) .edx]) s₀ (Pro s₀) := by
  have hsp := hp.sp_fit
  have rin : ∀ (s : State), s.rd = s₀.rd → s.wr = s₀.wr → ∀ d, 4 ≤ d → d + 4 ≤ 28 →
      InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
    fun s h₁ h₂ d h₃ h₄ => ⟨argR s₀, by simp [h₁, h₂, hp.wr], hp.arg_in h₃ h₄⟩
  have win : ∀ (s : State), s.wr = s₀.wr → ∀ d, 4 ≤ d → d + 4 ≤ 28 → InRegions s.wr (addr (esp₀ s₀) d) 4 :=
    fun s h₂ d h₃ h₄ => ⟨argR s₀, by simp [h₂, hp.wr], hp.arg_in h₃ h₄⟩
  refine wp_movm (a := addr (esp₀ s₀) 24) (ea_at _ _ _) (rin _ rfl rfl 24 (by omega_nat) (by omega_nat)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .edx = scr s₀ := u₁.gpr
  have sp₁ : s₁.gpr .esp = esp₀ s₀ := u₁.other _ (by decide)
  refine wp_movm (a := addr (esp₀ s₀) 8) (by rw [ea_at, sp₁]) (by rw [u₁.rd, u₁.wr]; exact rin _ rfl rfl 8 (by omega_nat) (by omega_nat))
    fun s₂ u₂ => ?_
  refine wp_store (a := addr (scr s₀) 176) (by rw [ea_at, u₂.other _ (by decide), e₁])
    (by rw [u₂.wr, u₁.wr]; exact ⟨scR s₀, by simp [hp.wr], hp.scr_in (by omega_nat) (by omega_nat)⟩) fun s₃ u₃ => ?_
  have ld : ∀ d, 4 ≤ d → d + 4 ≤ 28 →
      (s₀.mem.writeW (addr (scr s₀) 176) (ou s₀)).readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 :=
    fun d h₁ h₂ => Mem.readW_writeW_sep (hp.arg_scr_sep h₁ h₂ (by omega_nat)) (by decide)
  have m₃ : s₃.mem = s₀.mem.writeW (addr (scr s₀) 176) (ou s₀) := by
    rw [u₃.mem, u₂.gpr, u₂.mem, u₁.mem]; rfl
  have g₃ : ∀ r, r ≠ .ecx → r ≠ .edx → s₃.gpr r = s₀.gpr r := fun r h h' => by
    rw [u₃.gpr, u₂.other r h, u₁.other r h']
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have sp₃ : s₃.gpr .esp = esp₀ s₀ := g₃ _ (by decide) (by decide)
  have ed₃ : s₃.gpr .edx = scr s₀ := by rw [u₃.gpr, u₂.other _ (by decide), e₁]
  refine wp_movm (a := addr (esp₀ s₀) 12) (by rw [ea_at, sp₃]) (rin _ rd₃ wr₃ 12 (by omega_nat) (by omega_nat))
    fun s₄ u₄ => ?_
  refine wp_store (a := addr (esp₀ s₀) 8) (by rw [ea_at, u₄.other _ (by decide), sp₃])
    (by rw [u₄.wr]; exact win _ wr₃ 8 (by omega_nat) (by omega_nat)) fun s₅ u₅ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 16) (by rw [ea_at, u₅.gpr, u₄.other _ (by decide), sp₃])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact rin _ rd₃ wr₃ 16 (by omega_nat) (by omega_nat)) fun s₆ u₆ => ?_
  refine wp_store (a := addr (esp₀ s₀) 12) (by rw [ea_at, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), sp₃])
    (by rw [u₆.wr, u₅.wr, u₄.wr]; exact win _ wr₃ 12 (by omega_nat) (by omega_nat)) fun s₇ u₇ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 20)
    (by rw [ea_at, u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), sp₃])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact rin _ rd₃ wr₃ 20 (by omega_nat) (by omega_nat))
    fun s₈ u₈ => ?_
  have g₈ : ∀ r, r ≠ .ecx → s₈.gpr r = s₃.gpr r := fun r h => by
    rw [u₈.other r h, u₇.gpr, u₆.other r h, u₅.gpr, u₄.other r h]
  refine wp_store (a := addr (esp₀ s₀) 16) (by rw [ea_at, g₈ _ (by decide), sp₃])
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr]; exact win _ wr₃ 16 (by omega_nat) (by omega_nat)) fun s₉ u₉ => ?_
  refine wp_store (a := addr (esp₀ s₀) 20) (by rw [ea_at, u₉.gpr, g₈ _ (by decide), sp₃])
    (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr]; exact win _ wr₃ 20 (by omega_nat) (by omega_nat))
    fun s₁₀ u₁₀ => WP.block_nil ⟨?_, ?_, fun r h h' => ?_, ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃]
  · rw [u₁₀.gpr, u₉.gpr, g₈ r h, g₃ r h h']
  · -- The values read are the original arguments, unchanged by the earlier stores.
    have a : ∀ d, 4 ≤ d → d + 4 ≤ 28 → s₃.mem.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 :=
      fun d h₁ h₂ => by rw [m₃, ld d h₁ h₂]
    have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ 28 → e + 4 ≤ 28 → d + 4 ≤ e ∨ e + 4 ≤ d →
        (m.writeW (addr (esp₀ s₀) e) v).readW (addr (esp₀ s₀) d) 32 = m.readW (addr (esp₀ s₀) d) 32 :=
      fun m v d e h₂ h₄ h => readW_writeW_addr m v (by omega_nat) (by omega_nat) h
    have m₅ : s₅.mem = s₃.mem.writeW (addr (esp₀ s₀) 8) (arg s₀ 2) := by
      rw [u₅.mem, u₄.gpr, u₄.mem, a 12 (by omega_nat) (by omega_nat)]; rfl
    have m₇ : s₇.mem = (s₃.mem.writeW (addr (esp₀ s₀) 8) (arg s₀ 2)).writeW (addr (esp₀ s₀) 12) (arg s₀ 3) := by
      rw [u₇.mem, u₆.gpr, u₆.mem, m₅, w _ _ 16 8 (by omega_nat) (by omega_nat) (by omega_nat), a 16 (by omega_nat) (by omega_nat)]; rfl
    have m₉ : s₉.mem = s₇.mem.writeW (addr (esp₀ s₀) 16) (out s₀) := by
      rw [u₉.mem, u₈.gpr, u₈.mem, m₇, w _ _ 20 12 (by omega_nat) (by omega_nat) (by omega_nat),
        w _ _ 20 8 (by omega_nat) (by omega_nat) (by omega_nat), a 20 (by omega_nat) (by omega_nat)]; rfl
    rw [u₁₀.mem, m₉, m₇, u₉.gpr, g₈ _ (by decide), ed₃, m₃]; rfl

/-! ## The inner hash -/

abbrev SPre := VG.Proof.Sha256.X86.Stream.Finalize.Pre
abbrev SDone := VG.Proof.Sha256.X86.Stream.Finalize.Done

theorem finalizeHash_eq : finalizeHash = .seq (.block (([.mov .eax (.mem (at_ .esp 20))] : List Instr) ++
      VG.Impl.Sha256.X86.Stream.save .eax ++
      ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
       .mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp 128) .ecx,
       .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp 132) .ecx,
       .mov .ecx (.mem (at_ .esp 16)), .store (at_ .ebp 136) .ecx,
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm 63),
       .mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .mov .ecx (.imm 0x80),
       .store8 (at_ .edx 32) .cl, .alu .add .edi (.imm 1),
       .mov .esi (.imm 0), .alu .cmp .edi (.imm 57)] : List Instr)))
    (.seq (.ite .ae (.block [.mov .esi (.imm 1)]) (.block []))
      (.loop VG.Impl.Sha256.X86.Stream.finalizeBody .e)) := rfl

theorem finalizeHash_nosp : NoSp finalizeHash := NoSp.of_all (by lit_decide)

theorem finalizeHash_stack : stackUse finalizeHash = 20 := by lit_decide

/-- The state after the prologue, with the permissions of `vg_sha256_finalize`. -/
abbrev narrow (s₀ s : State) : State := s.withRegions [] (finW s₀)

theorem narrow_arg {s₀ s : State} (hp : Pre s₀) (h : Pro s₀ s) {i : Nat} (hi : i < 5) :
    arg (narrow s₀ s) i = [inn s₀, arg s₀ 2, arg s₀ 3, out s₀, scr s₀].getD i 0 := by
  have sp : s.gpr .esp = esp₀ s₀ := h.gpr _ (by decide) (by decide)
  show s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = _
  rw [h.mem, sp]; exact proMem_arg hp i hi

theorem narrow_pre {s₀ s : State} (hp : Pre s₀) (h : Pro s₀ s) : SPre (narrow s₀ s) := by
  have sp : s.gpr .esp = esp₀ s₀ := h.gpr .esp (by decide) (by decide)
  have a0 : arg (narrow s₀ s) 0 = inn s₀ := narrow_arg hp h (by omega_nat)
  have a3 : arg (narrow s₀ s) 3 = out s₀ := narrow_arg hp h (by omega_nat)
  have a4 : arg (narrow s₀ s) 4 = scr s₀ := narrow_arg hp h (by omega_nat)
  have s160 : Region.Sub ⟨scA s₀, 160⟩ (scR s₀) := Region.sub_prefix (by omega_nat)
  have a20 : Region.Sub ⟨addr (esp₀ s₀) 4, 20⟩ (argR s₀) := Region.sub_prefix (by omega_nat)
  have fs := hp.scr_fit
  have fsp := hp.sp_fit
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show finW s₀ = [⟨(arg (narrow s₀ s) 0).setWidth 64, 96⟩, ⟨(arg (narrow s₀ s) 3).setWidth 64, 32⟩,
      ⟨(arg (narrow s₀ s) 4).setWidth 64, 160⟩, ⟨addr (s.gpr .esp) 4, 20⟩]
    rw [a0, a3, a4, sp]
  · show Region.Disjoint ⟨(arg (narrow s₀ s) 0).setWidth 64, 96⟩ ⟨(arg (narrow s₀ s) 3).setWidth 64, 32⟩
    rw [a0, a3]; exact hp.in_out
  · show Region.Disjoint ⟨(arg (narrow s₀ s) 0).setWidth 64, 96⟩ ⟨(arg (narrow s₀ s) 4).setWidth 64, 160⟩
    rw [a0, a4]; exact hp.in_scr.sub_right s160
  · show Region.Disjoint ⟨(arg (narrow s₀ s) 3).setWidth 64, 32⟩ ⟨(arg (narrow s₀ s) 4).setWidth 64, 160⟩
    rw [a3, a4]; exact hp.out_scr.sub_right s160
  · show Region.Disjoint ⟨addr (s.gpr .esp) 4, 20⟩ ⟨(arg (narrow s₀ s) 0).setWidth 64, 96⟩
    rw [a0, sp]; exact hp.a_in.sub_left a20
  · show Region.Disjoint ⟨addr (s.gpr .esp) 4, 20⟩ ⟨(arg (narrow s₀ s) 3).setWidth 64, 32⟩
    rw [a3, sp]; exact hp.a_out.sub_left a20
  · show Region.Disjoint ⟨addr (s.gpr .esp) 4, 20⟩ ⟨(arg (narrow s₀ s) 4).setWidth 64, 160⟩
    rw [a4, sp]; exact (hp.a_scr.sub_left a20).sub_right s160
  · show Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg (narrow s₀ s) 0).setWidth 64, 96⟩
    rw [a0, sp]; exact hp.ret_in
  · show Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg (narrow s₀ s) 3).setWidth 64, 32⟩
    rw [a3, sp]; exact hp.ret_out
  · show Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg (narrow s₀ s) 4).setWidth 64, 160⟩
    rw [a4, sp]; exact hp.ret_scr.sub_right s160
  · show Region.Disjoint (below (s.gpr .esp) 20) ⟨(arg (narrow s₀ s) 0).setWidth 64, 96⟩
    rw [a0, sp]; exact hp.stk_in
  · show Region.Disjoint (below (s.gpr .esp) 20) ⟨(arg (narrow s₀ s) 3).setWidth 64, 32⟩
    rw [a3, sp]; exact hp.stk_out
  · show Region.Disjoint (below (s.gpr .esp) 20) ⟨(arg (narrow s₀ s) 4).setWidth 64, 160⟩
    rw [a4, sp]; exact hp.stk_scr.sub_right s160
  · show (arg (narrow s₀ s) 0).toNat + 96 ≤ 2 ^ 32
    rw [a0]; exact hp.in_fit
  · show (arg (narrow s₀ s) 3).toNat + 32 ≤ 2 ^ 32
    rw [a3]; exact hp.out_fit
  · show (arg (narrow s₀ s) 4).toNat + 160 ≤ 2 ^ 32
    rw [a4]; omega_nat
  · show 20 ≤ (s.gpr .esp).toNat
    rw [sp]; exact hp.sp_lo
  · show (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
    rw [sp]; omega_nat

/-! ## The outer block -/

/-- The little-endian bytes of a word. -/
def le (v : BitVec 32) : List Byte := (List.range 4).map fun j => v.extractLsb' (8 * j) 8

theorem writeW_le (m : Mem) (a : Addr) (v : BitVec 32) : m.writeW a v = writeBytes m a (le v) := by
  rw [Mem.writeW, VG.Proof.Sha256.Stream.write_eq_writeBytes]; rfl

/-- The rest of the outer block after the digest: `0x80`, zeros and the length 768, big-endian. -/
def padBytes : List Byte := le 0x80 ++ le 0 ++ le 0 ++ le 0 ++ le 0 ++ le 0 ++ le 0 ++ le 0x00030000

theorem padBytes_eq : padBytes = [0x80] ++ List.replicate 23 0 ++ [0, 0, 0, 0, 0, 0, 3, 0] := by decide

theorem padWords_eq : padWords = [.mov .ecx (.imm 0x80), .store (at_ .ebx 64) .ecx, .mov .ecx (.imm 0),
    .store (at_ .ebx 68) .ecx, .store (at_ .ebx 72) .ecx, .store (at_ .ebx 76) .ecx, .store (at_ .ebx 80) .ecx,
    .store (at_ .ebx 84) .ecx, .store (at_ .ebx 88) .ecx, .mov .ecx (.imm 0x00030000), .store (at_ .ebx 92) .ecx] :=
  rfl

/-- Memory after the middle block, from `m`: the inner state holds the outer
hash value and, in its buffer, the inner digest and `padBytes`. -/
def midMem (s₀ : State) (m : Mem) : Mem :=
  writeBytes (writeBytes (writeBytes m (inA s₀ + BitVec.ofNat 64 32) (beWords m (inn s₀) 0 8))
      (inA s₀ + BitVec.ofNat 64 0) (bytesAt m (ouA s₀ + BitVec.ofNat 64 0) (4 * 8)))
    (inA s₀ + BitVec.ofNat 64 64) padBytes

/-- Consecutive words written after some bytes. -/
theorem writeW_after (m : Mem) (q : Addr) (xs : List Byte) (v : BitVec 32) {d : Nat} (hd : d = xs.length)
    (h : xs.length + 4 < 2 ^ 64) :
    (writeBytes m q xs).writeW (q + BitVec.ofNat 64 d) v = writeBytes m q (xs ++ le v) := by
  subst hd; rw [writeW_le, writeBytes_append _ _ _ _ (by simp [le]; omega_nat)]

theorem le_length (v : BitVec 32) : (le v).length = 4 := by simp [le]

/-- What the middle block needs. -/
structure MidPre (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = inn s₀
  ebp : s.gpr .ebp = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  ou : s.mem.readW (addr (scr s₀) 176) 32 = ou s₀

/-- After it. -/
structure Mid (s₀ s s' : State) : Prop where
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r
  eax : s'.gpr .eax = inn s₀ + 32
  mem : s'.mem = midMem s₀ s.mem

theorem mid_ok {s₀ s : State} (hp : Pre s₀) (h : MidPre s₀ s) :
    WP isa (.block ((List.range 8).flatMap (bswapWord .ebx .ebx 0 32) ++ .mov .edx (.mem (at_ .ebp 176)) ::
      (List.range 8).flatMap (copyWord .edx .ebx 0 0) ++ padWords ++
      ([.mov .eax (.reg .ebx), .alu .add .eax (.imm 32)] : List Instr)))
      s (Mid s₀ s) := by
  have fi := hp.in_fit
  have fo := hp.ou_fit
  have fsp := hp.sp_fit
  have inn_in : ∀ d, d + 4 ≤ 96 → InRegions s.wr (addr (inn s₀) d) 4 :=
    fun d hd => ⟨inR s₀, by simp [h.wr, hp.wr], hp.in_in hd (by omega_nat)⟩
  simp only [List.append_assoc, List.cons_append]
  refine bswapWords_ok (by decide) (by decide) 8 _ s _ h.ebx h.ebx (by omega_nat) (by omega_nat)
    (fun k hk => by have := inn_in (0 + 4 * k) (by omega_nat); exact ⟨_, List.mem_append_right _ this.choose_spec.1,
      this.choose_spec.2⟩)
    (fun k hk => inn_in (32 + 4 * k) (by omega_nat)) ?_ fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  · exact Offset.sep _ (Or.inl (by omega_nat)) (by omega_nat) (by omega_nat)
  have e₁ : s₁.gpr .ebx = inn s₀ := by rw [g₁ _ (by decide), h.ebx]
  have p₁ : s₁.gpr .ebp = scr s₀ := by rw [g₁ _ (by decide), h.ebp]
  have sp₁ : s₁.gpr .esp = esp₀ s₀ := by rw [g₁ _ (by decide), h.esp]
  have wr₁' : s₁.wr = s₀.wr := wr₁.trans h.wr
  have rd₁' : s₁.rd = s₀.rd := rd₁.trans h.rd
  have hs : (scR s₀).Contains (addr (scr s₀) 176) 4 := hp.scr_in (by omega_nat) (by omega_nat)
  refine wp_movm (a := addr (scr s₀) 176) (by rw [ea_at, p₁])
    ⟨scR s₀, by simp [rd₁', wr₁', hp.wr], hs⟩ fun s₂ u₂ => ?_
  have ou₂ : s₂.gpr .edx = ou s₀ := by
    rw [u₂.gpr, m₁, readW_writeBytes_sep _ _ ?_, h.ou]
    rw [beWords_length]
    exact hp.in_scr.symm.sep hs (contains_offset (by omega_nat) (by omega_nat))
  have rd₂ : s₂.rd = s₀.rd := u₂.rd.trans rd₁'
  have wr₂ : s₂.wr = s₀.wr := u₂.wr.trans wr₁'
  have e₂ : s₂.gpr .ebx = inn s₀ := by rw [u₂.other _ (by decide), e₁]
  refine copyWords_ok (by decide) (by decide) 8 _ s₂ _ ou₂ e₂ (by omega_nat) (by omega_nat)
    (fun k hk => ⟨ouR s₀, by simp [rd₂, wr₂, hp.rd], contains_addr (by omega_nat) (by omega_nat) fo⟩)
    (fun k hk => by rw [wr₂, ← h.wr]; exact inn_in (0 + 4 * k) (by omega_nat))
    (hp.o_in.sep (contains_offset (by omega_nat) (by omega_nat)) (contains_offset (by omega_nat) (by omega_nat)))
    fun s₃ g₃ rd₃ wr₃ m₃ => ?_
  have e₃ : s₃.gpr .ebx = inn s₀ := by rw [g₃ _ (by decide), e₂]
  have rd₃' : s₃.rd = s₀.rd := rd₃.trans rd₂
  have wr₃' : s₃.wr = s₀.wr := wr₃.trans wr₂
  -- The padding words.
  have padA : ∀ k, k < 8 → addr (inn s₀) (64 + 4 * k) = inA s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * k) :=
    fun k hk => addr_word (n := 8) (by omega_nat) hk
  have pin : ∀ (t : State), t.wr = s₀.wr → ∀ k, k < 8 →
      InRegions t.wr (inA s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * k)) 4 :=
    fun t ht k hk => by rw [← padA k hk, ht, ← h.wr]; exact inn_in (64 + 4 * k) (by omega_nat)
  rw [padWords_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_movi fun s₄ u₄ => ?_
  refine wp_store (a := inA s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * 0))
    (by rw [ea_at, u₄.other _ (by decide), e₃, ← padA 0 (by omega_nat)]) (by rw [u₄.wr]; exact pin _ wr₃' 0 (by omega_nat))
    fun s₅ u₅ => wp_movi fun s₆ u₆ => ?_
  have x₆ : ∀ r, r ≠ .ecx → s₆.gpr r = s₃.gpr r := fun r h => by rw [u₆.other r h, u₅.gpr, u₄.other r h]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, wr₃']
  have st : ∀ (t : State), t.wr = s₀.wr → (∀ r, r ≠ .ecx → t.gpr r = s₃.gpr r) → ∀ k, k < 8 →
      t.ea (at_ .ebx (64 + 4 * k)) = inA s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * k) :=
    fun t _ ht k hk => by rw [ea_at, ht _ (by decide), e₃, padA k hk]
  refine wp_store (st _ wr₆ x₆ 1 (by omega_nat)) (pin _ wr₆ 1 (by omega_nat)) fun s₇ u₇ => ?_
  refine wp_store (st _ (by rw [u₇.wr, wr₆]) (fun r h => by rw [u₇.gpr, x₆ r h]) 2 (by omega_nat))
    (pin _ (by rw [u₇.wr, wr₆]) 2 (by omega_nat)) fun s₈ u₈ => ?_
  refine wp_store (st _ (by rw [u₈.wr, u₇.wr, wr₆]) (fun r h => by rw [u₈.gpr, u₇.gpr, x₆ r h]) 3 (by omega_nat))
    (pin _ (by rw [u₈.wr, u₇.wr, wr₆]) 3 (by omega_nat)) fun s₉ u₉ => ?_
  refine wp_store (st _ (by rw [u₉.wr, u₈.wr, u₇.wr, wr₆])
      (fun r h => by rw [u₉.gpr, u₈.gpr, u₇.gpr, x₆ r h]) 4 (by omega_nat))
    (pin _ (by rw [u₉.wr, u₈.wr, u₇.wr, wr₆]) 4 (by omega_nat)) fun s₁₀ u₁₀ => ?_
  refine wp_store (st _ (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆])
      (fun r h => by rw [u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.gpr, x₆ r h]) 5 (by omega_nat))
    (pin _ (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆]) 5 (by omega_nat)) fun s₁₁ u₁₁ => ?_
  refine wp_store (st _ (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆])
      (fun r h => by rw [u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.gpr, x₆ r h]) 6 (by omega_nat))
    (pin _ (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆]) 6 (by omega_nat)) fun s₁₂ u₁₂ => ?_
  refine wp_movi fun s₁₃ u₁₃ => ?_
  have x₁₃ : ∀ r, r ≠ .ecx → s₁₃.gpr r = s₃.gpr r := fun r h => by
    rw [u₁₃.other r h, u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.gpr, x₆ r h]
  have wr₁₃ : s₁₃.wr = s₀.wr := by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆]
  refine wp_store (st _ wr₁₃ x₁₃ 7 (by omega_nat)) (pin _ wr₁₃ 7 (by omega_nat)) fun s₁₄ u₁₄ => ?_
  -- `eax`.
  have x₁₄ : ∀ r, r ≠ .ecx → s₁₄.gpr r = s₃.gpr r := fun r h => by rw [u₁₄.gpr, x₁₃ r h]
  have wr₁₄ : s₁₄.wr = s₀.wr := by rw [u₁₄.wr, wr₁₃]
  have rd₁₄ : s₁₄.rd = s₀.rd := by
    rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃']
  refine wp_mov fun s₁₇ u₁₇ => wp_addi fun s₁₈ u₁₈ => WP.block_nil ⟨?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_⟩
  · rw [u₁₈.rd, u₁₇.rd, rd₁₄]
  · rw [u₁₈.wr, u₁₇.wr, wr₁₄]
  · rw [u₁₈.other r h₁, u₁₇.other r h₁, x₁₄ r h₂, g₃ r h₂, u₂.other r h₃, g₁ r h₂]
  · rw [u₁₈.gpr, u₁₇.gpr, x₁₄ _ (by decide), e₃]
  · have hq : inA s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * 0) = inA s₀ + BitVec.ofNat 64 64 := by simp
    have hl : ∀ xs : List Byte, xs.length ≤ 28 → xs.length + 4 < 2 ^ 64 := fun _ h => by omega_nat
    rw [u₁₈.mem, u₁₇.mem,
      u₁₄.mem, u₁₃.gpr, u₁₃.mem, u₁₂.mem, u₁₁.gpr, u₁₁.mem, u₁₀.gpr, u₁₀.mem, u₉.gpr, u₉.mem,
      u₈.gpr, u₈.mem, u₇.gpr, u₇.mem, u₆.gpr, u₆.mem, u₅.mem, u₄.gpr, u₄.mem, hq, writeW_le _ (inA s₀ + BitVec.ofNat 64 64),
      writeW_after _ _ _ _ (by simp [le_length]) (hl _ (by simp [le_length])),
      writeW_after _ _ _ _ (by simp [le_length]) (hl _ (by simp [le_length])),
      writeW_after _ _ _ _ (by simp [le_length]) (hl _ (by simp [le_length])),
      writeW_after _ _ _ _ (by simp [le_length]) (hl _ (by simp [le_length])),
      writeW_after _ _ _ _ (by simp [le_length]) (hl _ (by simp [le_length])),
      writeW_after _ _ _ _ (by simp [le_length]) (hl _ (by simp [le_length])),
      writeW_after _ _ _ _ (by simp [le_length]) (hl _ (by simp [le_length])),
      m₃, u₂.mem, m₁, VG.Proof.Hmac.Common.bytesAt_writeBytes_sep _ _ ?_ (by omega_nat)]
    · rfl
    · rw [beWords_length]
      exact hp.o_in.sep (contains_offset (by omega_nat) (by omega_nat)) (contains_offset (by omega_nat) (by omega_nat))

/-! ## What the middle block leaves -/

/-- `List.ofFn` as a map over `List.finRange` (Mathlib's `List.ofFn_eq_map`). -/
theorem ofFn_eq_map {n : Nat} {α : Type} (f : Fin n → α) : List.ofFn f = (List.finRange n).map f :=
  List.map_ofFn.symm

/-- Mathlib's `List.flatMap_congr`. -/
theorem flatMap_congr {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem beWords_stateAt (m : Mem) {x : BitVec 32} (hx : x.toNat + 32 ≤ 2 ^ 32) :
    beWords m x 0 8 = (stateAt m (x.setWidth 64)).toList.flatMap wordBytes := by
  simp only [beWords, stateAt, Vector.toList_ofFn, ofFn_eq_map]
  rw [List.flatMap_map, ← List.flatMap_map (f := Fin.val)
    (g := fun k => wordBytes (m.readW (x.setWidth 64 + BitVec.ofNat 64 (4 * k)) 32)),
    show (List.finRange 8).map Fin.val = List.range 8 from rfl]
  refine flatMap_congr fun k hk => ?_
  have hk := List.mem_range.mp hk
  rw [Nat.zero_add, addr_eq (by omega_nat)]

theorem bytesAt_writeW_sep (m : Mem) {p a : Addr} {n : Nat} (v : BitVec 32) (h : Mem.Sep p n a 4)
    (hn : n < 2 ^ 64) : bytesAt (m.writeW a v) p n = bytesAt m p n := by
  rw [writeW_le]; exact VG.Proof.Hmac.Common.bytesAt_writeBytes_sep _ _ (by rwa [le_length]) hn

theorem padBytes_length : padBytes.length = 32 := by decide

theorem sep_off (b : Addr) {d e n k : Nat} (h : d + n ≤ e ∨ e + k ≤ d) (hd : d + n < 2 ^ 32) (he : e + k < 2 ^ 32) :
    Mem.Sep (b + BitVec.ofNat 64 d) n (b + BitVec.ofNat 64 e) k := Offset.sep b h (by omega_nat) (by omega_nat)

section
variable {s₀ : State} (hp : Pre s₀) (m : Mem)
include hp

omit hp in
theorem midMem_frame : Frame [inR s₀, argR s₀] m (midMem s₀ m) := by
  simp only [midMem]
  refine (((writeBytes_frame (R := inR s₀) _ _ _ ?_).trans (writeBytes_frame (R := inR s₀) _ _ _ ?_)).trans
    (writeBytes_frame (R := inR s₀) _ _ _ ?_)).mono (by simp)
  · rw [beWords_length]; exact contains_offset (by omega_nat) (by omega_nat)
  · rw [bytesAt_length]; exact contains_offset (by omega_nat) (by omega_nat)
  · rw [padBytes_length]; exact contains_offset (by omega_nat) (by omega_nat)

omit hp in
/-- The inner state holds the outer hash value. -/
theorem midMem_state : stateAt (midMem s₀ m) (inA s₀) = stateAt m (ouA s₀) := by
  have s0_64 : Mem.Sep (inA s₀ + BitVec.ofNat 64 0) 32 (inA s₀ + BitVec.ofNat 64 64) padBytes.length := by
    rw [padBytes_length]; exact sep_off _ (by omega_nat) (by omega_nat) (by omega_nat)
  have hb : bytesAt (midMem s₀ m) (inA s₀ + BitVec.ofNat 64 0) 32 = bytesAt m (ouA s₀ + BitVec.ofNat 64 0) 32 := by
    simp only [midMem]
    rw [VG.Proof.Hmac.Common.bytesAt_writeBytes_sep _ _ s0_64 (by omega_nat)]
    have := VG.Proof.Hmac.Common.bytesAt_writeBytes_self
      (writeBytes m (inA s₀ + BitVec.ofNat 64 32) (beWords m (inn s₀) 0 8)) (inA s₀ + BitVec.ofNat 64 0)
      (bytesAt m (ouA s₀ + BitVec.ofNat 64 0) (4 * 8)) (by rw [bytesAt_length]; omega_nat)
    rw [bytesAt_length] at this
    exact this
  refine VG.Proof.Hmac.Common.stateAt_eq_of_bytes fun i hi => ?_
  have h₁ := bytesAt_getD (k := i) hb (by omega_nat)
  rw [show inA s₀ + BitVec.ofNat 64 0 = inA s₀ by simp] at h₁
  rw [h₁, VG.Proof.Hmac.Common.bytesAt_getD' _ _ hi, show ouA s₀ + BitVec.ofNat 64 0 = ouA s₀ by simp]

omit hp in
/-- The block after it: the digest, then `padBytes`. -/
theorem midMem_block :
    bytesAt (midMem s₀ m) (inA s₀ + BitVec.ofNat 64 32) (32 + 32) = beWords m (inn s₀) 0 8 ++ padBytes := by
  have s32_64 : Mem.Sep (inA s₀ + BitVec.ofNat 64 32) 32 (inA s₀ + BitVec.ofNat 64 64) padBytes.length := by
    rw [padBytes_length]; exact sep_off _ (by omega_nat) (by omega_nat) (by omega_nat)
  have s32_0 : Mem.Sep (inA s₀ + BitVec.ofNat 64 32) 32 (inA s₀ + BitVec.ofNat 64 0)
      (bytesAt m (ouA s₀ + BitVec.ofNat 64 0) (4 * 8)).length := by
    rw [bytesAt_length]; exact sep_off _ (by omega_nat) (by omega_nat) (by omega_nat)
  simp only [midMem]
  rw [VG.Proof.Hmac.Common.bytesAt_add,
    show inA s₀ + BitVec.ofNat 64 32 + BitVec.ofNat 64 32 = inA s₀ + BitVec.ofNat 64 64 by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · rw [VG.Proof.Hmac.Common.bytesAt_writeBytes_sep _ _ s32_64 (by omega_nat),
      VG.Proof.Hmac.Common.bytesAt_writeBytes_sep _ _ s32_0 (by omega_nat)]
    have := VG.Proof.Hmac.Common.bytesAt_writeBytes_self m (inA s₀ + BitVec.ofNat 64 32) (beWords m (inn s₀) 0 8)
      (by rw [beWords_length]; omega_nat)
    rwa [beWords_length] at this
  · have := VG.Proof.Hmac.Common.bytesAt_writeBytes_self
      (writeBytes (writeBytes m (inA s₀ + BitVec.ofNat 64 32) (beWords m (inn s₀) 0 8)) (inA s₀ + BitVec.ofNat 64 0)
        (bytesAt m (ouA s₀ + BitVec.ofNat 64 0) (4 * 8))) (inA s₀ + BitVec.ofNat 64 64) padBytes
      (by rw [padBytes_length]; omega_nat)
    rwa [padBytes_length] at this

end

/-! ## The outer compression -/

theorem blk_eq {s₀ : State} (hp : Pre s₀) : (inn s₀ + 32).setWidth 64 = inA s₀ + BitVec.ofNat 64 32 := by
  show addr (inn s₀) 32 = _
  exact addr_eq (by have := hp.in_fit; omega_nat)

theorem out_ok {s₀ s : State} (hp : Pre s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hebx : s.gpr .ebx = inn s₀) (hebp : s.gpr .ebp = scr s₀) (hsp : s.gpr .esp = esp₀ s₀)
    (hout : s.mem.readW (addr (scr s₀) 136) 32 = out s₀)
    (hsv : ∀ p ∈ saved, s.mem.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1) :
    WP isa (.block (.mov .eax (.mem (at_ .ebp 136)) :: (List.range 8).flatMap (bswapWord .ebx .eax 0 0) ++
      .mov .eax (.reg .ebp) :: restore .eax)) s fun s' =>
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧
      s'.mem = writeBytes s.mem (outA s₀ + BitVec.ofNat 64 0) (beWords s.mem (inn s₀) 0 8) := by
  have fi := hp.in_fit
  have fo := hp.out_fit
  have sin : ∀ d, d + 4 ≤ 240 → InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
    fun d hd => ⟨scR s₀, by simp [hrd, hwr, hp.wr], hp.scr_in hd (by omega_nat)⟩
  rw [List.cons_append]
  refine wp_movm (a := addr (scr s₀) 136) (by rw [ea_at, hebp]) (sin 136 (by omega_nat)) fun s₁ u₁ => ?_
  refine bswapWords_ok (src := .ebx) (dst := .eax) (by decide) (by decide) 8 _ s₁ _
    (by rw [u₁.other _ (by decide), hebx]) (by rw [u₁.gpr, hout]) (by omega_nat) (by omega_nat)
    (fun k hk => ⟨inR s₀, by simp [u₁.rd, u₁.wr, hrd, hwr, hp.wr], hp.in_in (by omega_nat) (by omega_nat)⟩)
    (fun k hk => ⟨outR s₀, by simp [u₁.wr, hwr, hp.wr], contains_addr (by omega_nat) (by omega_nat) fo⟩)
    (hp.in_out.sep (contains_offset (by omega_nat) (by omega_nat)) (contains_offset (by omega_nat) (by omega_nat)))
    fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  refine wp_mov fun s₃ u₃ => ?_
  have e₃ : s₃.gpr .eax = scr s₀ := by rw [u₃.gpr, g₂ _ (by decide), u₁.other _ (by decide), hebp]
  have m₃ : s₃.mem = writeBytes s.mem (outA s₀ + BitVec.ofNat 64 0) (beWords s.mem (inn s₀) 0 8) := by
    rw [u₃.mem, m₂, u₁.mem]
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, rd₂, u₁.rd, hrd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, wr₂, u₁.wr, hwr]
  -- The saved registers, which the MAC does not overwrite.
  have rs : ∀ p ∈ saved, s₃.mem.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1 := by
    intro p hp'
    have hd : 112 ≤ p.2 ∧ p.2 + 4 ≤ 128 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl <;> simp
    rw [m₃, readW_writeBytes_sep _ _ ?_, hsv p hp']
    rw [beWords_length]
    exact hp.out_scr.symm.sep (hp.scr_in (by omega_nat) (by omega_nat)) (contains_offset (by omega_nat) (by omega_nat))
  have sin₃ : ∀ d, d + 4 ≤ 240 → InRegions (s₃.rd ++ s₃.wr) (addr (scr s₀) d) 4 :=
    fun d hd => by rw [rd₃, wr₃, ← hrd, ← hwr]; exact sin d hd
  simp only [restore, saved, List.map_cons, List.map_nil]
  refine wp_movm (a := addr (scr s₀) 112) (by rw [ea_at, e₃]) (sin₃ 112 (by omega_nat)) fun s₄ u₄ => ?_
  refine wp_movm (a := addr (scr s₀) 116) (by rw [ea_at, u₄.other _ (by decide), e₃])
    (by rw [u₄.rd, u₄.wr]; exact sin₃ 116 (by omega_nat)) fun s₅ u₅ => ?_
  refine wp_movm (a := addr (scr s₀) 120) (by rw [ea_at, u₅.other _ (by decide), u₄.other _ (by decide), e₃])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact sin₃ 120 (by omega_nat)) fun s₆ u₆ => ?_
  refine wp_movm (a := addr (scr s₀) 124)
    (by rw [ea_at, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), e₃])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact sin₃ 124 (by omega_nat)) fun s₇ u₇ => WP.block_nil ?_
  have mm : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  refine ⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃], fun r hr => ?_,
    by rw [mm, m₃]⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
    exact rs (.ebx, 112) (by simp [saved])
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem]
    exact rs (.esi, 116) (by simp [saved])
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem]
    exact rs (.edi, 120) (by simp [saved])
  · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem]
    exact rs (.ebp, 124) (by simp [saved])
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), g₂ _ (by decide), u₁.other _ (by decide), hsp]

/-! ## Correctness -/

/-- Everything we may write. -/
abbrev allR (s₀ : State) : List Region := [inR s₀, outR s₀, scR s₀, argR s₀, stkR s₀]

theorem xorPad_length (k : List Byte) (p : Byte) : (xorPad k p).length = k.length := by simp [xorPad]

/-- The outer hash, of `(K₀ ⊕ opad) ‖ d`, from the outer hash value and the block after it. -/
theorem outer_hash {k0 d : List Byte} (hk : k0.length = 64) (hd : d.length = 32) :
    Spec.Sha256.hash (xorPad k0 opad ++ d) =
      (compress (Spec.Sha256.compressList Spec.Sha256.H0 (xorPad k0 opad) 1)
        (parseBlock fun t => (d ++ padBytes).getD t 0)).toList.flatMap wordBytes := by
  have hl : (xorPad k0 opad ++ d).length = 96 := by simp [xorPad_length, hk, hd]
  rw [hash_one (by rw [hl]; omega_nat), hl, compressList_append (by rw [xorPad_length, hk]),
    show (96 : Nat) / 64 = 1 from rfl]
  refine congrArg (fun b => (compress (Spec.Sha256.compressList Spec.Sha256.H0 (xorPad k0 opad) 1) b).toList.flatMap
    wordBytes) (congrArg parseBlock (funext fun t => ?_))
  refine congrArg (fun l : List Byte => l.getD t 0) ?_
  have hr : rest (xorPad k0 opad ++ d) = d := by
    simp only [rest, hl, show 64 * (96 / 64) = (xorPad k0 opad).length by rw [xorPad_length, hk]]
    exact List.drop_left
  have hlb : lenBytes (xorPad k0 opad ++ d) = [0, 0, 0, 0, 0, 0, 3, 0] := by
    simp only [lenBytes, hl]; decide
  rw [hr, hlb, padBytes_eq]
  simp only [List.append_assoc]

/-! ## Constant time -/

/-- The initial taint: `esp + 4` is the base of the (public) arguments, whose
words at offsets 0, 16 and 20 are the base addresses of `inner`, `out` and
`scratch`. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [96, 32, 240, 24], bases := [(.esp, 3, 4)],
    slots := [(3, 0, 24)], wbases := [(3, 0, 0), (3, 16, 1), (3, 20, 2)], room := 20 }

theorem argWord_eq {s : State} (hsp : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32) {k : Nat} (hk : k < 24) :
    addr (s.gpr .esp) 4 + BitVec.ofNat 64 k = argAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [argAddr]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * (k / 4))).setWidth 64 = addr (s.gpr .esp) (4 + 4 * (k / 4))
    from rfl, addr_eq (by omega_nat), addr_eq (by omega_nat), BitVec.add_assoc, BitVec.add_assoc,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 2; omega_nat

theorem wf₀ {s : State} (h : Proof.Hmac.finalizeSha256X86.pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have hi := hp.in_fit; have ho := hp.out_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  have hlo := hp.sp_lo
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, k1, -, k2, k3, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, ?_,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ h => (List.not_mem_nil h).elim⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.in_out, hp.in_scr, hp.a_in.symm⟩, ⟨hp.out_scr, hp.a_out.symm⟩, hp.a_scr.symm, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · simp only [addr_toNat]; omega_nat
    · simp only [addr_toNat]; omega_nat
    · simp only [addr_toNat]; omega_nat
    · simp only; rw [addr_eq (by omega_nat), BitVec.toNat_add, addr_toNat, BitVec.toNat_ofNat]; omega_nat
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'
    subst hp'
    simp [VG.X86.Taint.region, hp.wr]
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (esp₀ s) 4 + BitVec.ofNat 64 0) 32) 0 = inA s
      simp [addr, inn, arg, argAddr]
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (esp₀ s) 4 + BitVec.ofNat 64 16) 32) 0 = outA s
      rw [argWord_eq hs (k := 16) (by omega_nat)]
      simp [addr, out, arg]
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (esp₀ s) 4 + BitVec.ofNat 64 20) 32) 0 = scA s
      rw [argWord_eq hs (k := 20) (by omega_nat)]
      simp [addr, scr, arg]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact k1
    · exact k2
    · exact k3
    · have := hp.sp_fit
      unfold argR
      rw [addr_eq (by omega_nat)]
      exact Offset.disjoint_below_above _ (m := 20) (a := 4) (l := 24) (by omega_nat)

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Hmac.finalizeSha256X86.pre s₁) (h₂ : Proof.Hmac.finalizeSha256X86.pre s₂)
    (hpub : Proof.Hmac.finalizeSha256X86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂, ?_, ?_,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [inR, outR, scR, argR, inA, outA, scA, inn, out, scr, esp₀, ha 0 (by omega_nat), ha 4 (by omega_nat),
      ha 5 (by omega_nat), hesp]
  · intro sl hsl
    simp only [τ₀, List.mem_singleton] at hsl
    subst hsl; decide
  · intro sl hsl k _ hk
    simp only [τ₀, List.mem_singleton] at hsl
    subst hsl
    simp only [Nat.zero_add] at hk
    simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp₁.wr, hp₂.wr]
    show s₁.mem (addr (esp₀ s₁) 4 + BitVec.ofNat 64 k) = s₂.mem (addr (esp₀ s₂) 4 + BitVec.ofNat 64 k)
    rw [argWord_eq hp₁.sp_fit hk, argWord_eq hp₂.sp_fit hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_nat)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_nat))]
    exact congrArg _ (ha _ (by omega_nat))

/-- Memory holding the arguments `0x1000, 0x1100, 0, 0, 0x2000, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x11 else if a = 0x4015 then 0x20 else
  if a = 0x4019 then 0x30 else 0

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x1100, 96⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩, ⟨0x3000, 240⟩, ⟨0x4004, 24⟩]

/-- What the analysis forgets wherever the hint records a taint
(`taint_decide_weaken`): the public words of `inner` and `out` (data, never
addresses), the count in `scratch[128..136)` (only data too), and the
arguments once `vg_sha256_finalize`'s code has stored `out` at
`scratch[136]` (nothing reads them afterwards); and repeated slots. Inside
the compression function, `k` frames come first among the regions. The
kernel then evaluates the compression function's thousands of instructions
with a third of the public slots. -/
def forget (τ : VG.X86.Taint.T) : VG.X86.Taint.T :=
  let k := (τ.stk.filter Option.isSome).length
  let args := !τ.slots.any fun (i, o, _) => i == k + 2 && o == 136
  { τ with slots := (τ.slots.filter fun (i, o, _) =>
      i < k || (i == k + 2 && o != 128 && o != 132) || (i == k + 3 && args)).eraseDups }

theorem finalize_ct : ConstantTime isa Proof.Hmac.finalizeSha256X86.pre
    Proof.Hmac.finalizeSha256X86.pub finalize :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
    (by taint_decide_weaken forget)

/-- `finalizeSha256X86` with the 688 bytes of scratch of the shared contract
(sized for the x86-64 AVX2 compression function), of which the code uses 240. -/
def finalizeWide : Contract isa :=
  { Proof.Hmac.finalizeSha256X86 with
    pre := fun s =>
      let inner : Region := ⟨(arg s 0).setWidth 64, 96⟩
      let outer : Region := ⟨(arg s 1).setWidth 64, 96⟩
      let out : Region := ⟨(arg s 4).setWidth 64, 32⟩
      let scratch : Region := ⟨(arg s 5).setWidth 64, 688⟩
      let args : Region := ⟨argAddr s 0, 24⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
      s.rd = [outer] ∧ s.wr = [inner, out, scratch, args] ∧
      inner.Disjoint out ∧ inner.Disjoint scratch ∧ out.Disjoint scratch ∧
      args.Disjoint inner ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      outer.Disjoint inner ∧ outer.Disjoint out ∧ outer.Disjoint scratch ∧ outer.Disjoint args ∧
      ret.Disjoint inner ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 96 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 96 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 5).toNat + 688 ≤ 2 ^ 32 ∧
      20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 }

/-- The regions `finalizeSha256X86` lets the code write. -/
def narrowWr (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 96⟩, ⟨(arg s 4).setWidth 64, 32⟩, ⟨(arg s 5).setWidth 64, 240⟩,
    ⟨argAddr s 0, 24⟩]

/-- Rewrites the contracts at a narrowed state (`arg` does not unfold
cheaply). -/
local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Hmac.finalizeSha256X86, Proof.Hmac.countFinalizeX86,
    VG.Proof.Hmac.X86.Finalize.finalizeWide, VG.Proof.Hmac.X86.Finalize.narrowWr, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions,
    VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem, VG.X86.State.withRegions_rd,
    VG.X86.State.withRegions_wr] $(loc)?)

theorem finalizeWide_pre (s : State) (h : finalizeWide.pre s) :
    Proof.Hmac.finalizeSha256X86.pre (s.withRegions s.rd (narrowWr s)) := by
  obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉,
    h₂₀, h₂₁, h₂₂, h₂₃, h₂₄, h₂₅⟩ := h
  narrow
  exact ⟨h₁, trivial, h₃, h₄.sub_right (Region.sub_of_ble rfl), h₅.sub_right (Region.sub_of_ble rfl),
    h₆, h₇, h₈.sub_right (Region.sub_of_ble rfl), h₉, h₁₀, h₁₁.sub_right (Region.sub_of_ble rfl), h₁₂,
    h₁₃, h₁₄, h₁₅.sub_right (Region.sub_of_ble rfl), h₁₆, h₁₇, h₁₈, h₁₉.sub_right (Region.sub_of_ble rfl),
    h₂₀, h₂₁, h₂₂, Region.end_le_of_ble rfl h₂₃, h₂₄, h₂₅⟩

/-- A state satisfying `finalizeWide.pre`. -/
def wideSat : State :=
  { sat with wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩, ⟨0x3000, 688⟩, ⟨0x4004, 24⟩] }

theorem finalizeWide_implies :
    finalizeWide.Implies (Spec.Hmac.finalizeSha256OutContract X86.abi 20) := by
  have a0 : arg wideSat 0 = 0x1000 := by decide
  have a1 : arg wideSat 1 = 0x1100 := by decide
  have a4 : arg wideSat 4 = 0x2000 := by decide
  have a5 : arg wideSat 5 = 0x3000 := by decide
  have e : argAddr wideSat 0 = 0x4004 := by decide
  have esp : wideSat.gpr .esp = 0x4000 := rfl
  sig_implies [Spec.Hmac.finalizeSha256OutContract, Spec.Hmac.finalizeSha256OutSig, finalizeWide,
    Proof.Hmac.finalizeSha256X86, Proof.Hmac.countFinalizeX86, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a4, a5, e, esp] using wideSat

end VG.Proof.Hmac.X86.Finalize
