import VerifiedGarbage.Spec.ChaCha20Poly1305
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.X86.Block
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Poly1305.X86.Init
import VerifiedGarbage.Proof.Poly1305.X86.Blocks
import VerifiedGarbage.Proof.Poly1305.X86.Finalize
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.ChaCha20.X86.Xor
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Lit
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega

section

/-!
# ChaCha20-Poly1305 on x86 (32-bit): the entry state, regions and invariant
-/

open VG.PowLit

namespace VG.Proof.ChaCha20Poly1305

open Spec.ChaCha20Poly1305
open Spec.Poly1305 (bytesAt)

open VG.X86 in
/-- The precondition of both functions: `ctx` (1024 bytes), `data` and the
arguments (20 bytes above the return address) may be read and written, `aad`
read; none of them overlaps another, and `ctx`, `aad` and `data` do not
overlap the return address or the 32 bytes of stack below it, where the calls
store their arguments and return addresses (and `vg_chacha20_xor` those of
its own calls); nothing wraps around the end of the address space. -/
def preX86 (s : X86.State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 1024⟩
  let aad : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
  let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
  let args : Region := ⟨argAddr s 0, 20⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 32, 32⟩
  s.rd = [aad] ∧ s.wr = [ctx, data, args] ∧
  ctx.Disjoint aad ∧ ctx.Disjoint data ∧ aad.Disjoint data ∧
  args.Disjoint ctx ∧ args.Disjoint aad ∧ args.Disjoint data ∧
  ret.Disjoint ctx ∧ ret.Disjoint aad ∧ ret.Disjoint data ∧
  stack.Disjoint ctx ∧ stack.Disjoint aad ∧ stack.Disjoint data ∧
  (arg s 0).toNat + 1024 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
  (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ 32 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 24 ≤ 2 ^ 32

open VG.X86 in
def pubX86 (s₁ s₂ : X86.State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

open VG.X86 in
/-- `vg_chacha20_poly1305_seal(ctx, aad, aad_len, data, len)`. -/
def sealX86 : Contract X86.isa where
  pre := preX86
  post s s' :=
    let ctx := (arg s 0).setWidth 64
    encrypt (bytesAt s.mem ctx 32) (bytesAt s.mem (ctx + 32) 12)
        (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
        (bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) =
      (bytesAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat, bytesAt s'.mem (ctx + 48) 16)
  pub := pubX86

open VG.X86 in
/-- `vg_chacha20_poly1305_open(ctx, aad, aad_len, data, len) -> u32`. -/
def openX86 : Contract X86.isa where
  pre := preX86
  post s s' :=
    let ctx := (arg s 0).setWidth 64
    match decrypt (bytesAt s.mem ctx 32) (bytesAt s.mem (ctx + 32) 12)
        (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
        (bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) (bytesAt s.mem (ctx + 48) 16) with
    | some pt => s'.gpr .eax = 1 ∧ bytesAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat = pt
    | none => s'.gpr .eax = 0
  pub := pubX86

end VG.Proof.ChaCha20Poly1305

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86
open VG.Impl.ChaCha20.X86 (at_)
open VG.Proof.ChaCha20.X86 (contains_off toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev E : BitVec 32 := s₀.gpr .esp
abbrev CX : BitVec 32 := arg s₀ 0
abbrev AD : BitVec 32 := arg s₀ 1
abbrev ALN : BitVec 32 := arg s₀ 2
abbrev DP : BitVec 32 := arg s₀ 3
abbrev LN : BitVec 32 := arg s₀ 4
abbrev AL : Nat := (ALN s₀).toNat
abbrev L : Nat := (LN s₀).toNat
abbrev cx : Addr := (CX s₀).setWidth 64
abbrev ad : Addr := (AD s₀).setWidth 64
abbrev dp : Addr := (DP s₀).setWidth 64
/-- The key, the nonce, the additional data, the data and the tag on entry. -/
abbrev K : List Byte := bytesAt s₀.mem (cx s₀) 32
abbrev N : List Byte := bytesAt s₀.mem (cx s₀ + 32) 12
abbrev A : List Byte := bytesAt s₀.mem (ad s₀) (AL s₀)
abbrev D : List Byte := bytesAt s₀.mem (dp s₀) (L s₀)
abbrev T0 : List Byte := bytesAt s₀.mem (cx s₀ + 48) 16
/-- The one-time Poly1305 key. -/
abbrev otk : List Byte := Spec.ChaCha20Poly1305.polyKeyGen (K s₀) (N s₀)
abbrev ctxR : Region := ⟨cx s₀, 1024⟩
abbrev aR : Region := ⟨ad s₀, AL s₀⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
/-- The stack below the return address that the calls use. -/
abbrev stkR : Region := below (E s₀) 32
/-- `ctx[k, k + n)`. -/
abbrev sub (k n : Nat) : Region := ⟨cx s₀ + BitVec.ofNat 64 k, n⟩
/-- `ctx + k`, as the code computes it. -/
abbrev C32 (k : Nat) : BitVec 32 := CX s₀ + BitVec.ofNat 32 k
end

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [aR s₀]
  wr : s₀.wr = [ctxR s₀, dR s₀, argR s₀]
  c_a : (ctxR s₀).Disjoint (aR s₀)
  c_d : (ctxR s₀).Disjoint (dR s₀)
  a_d : (aR s₀).Disjoint (dR s₀)
  g_c : (argR s₀).Disjoint (ctxR s₀)
  g_a : (argR s₀).Disjoint (aR s₀)
  g_d : (argR s₀).Disjoint (dR s₀)
  ret_c : (retR s₀).Disjoint (ctxR s₀)
  ret_a : (retR s₀).Disjoint (aR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  stk_c : (stkR s₀).Disjoint (ctxR s₀)
  stk_a : (stkR s₀).Disjoint (aR s₀)
  stk_d : (stkR s₀).Disjoint (dR s₀)
  fit_c : (CX s₀).toNat + 1024 ≤ 2 ^ 32
  fit_a : (AD s₀).toNat + AL s₀ ≤ 2 ^ 32
  fit_d : (DP s₀).toNat + L s₀ ≤ 2 ^ 32
  sp_lo : 32 ≤ (E s₀).toNat
  sp_hi : (E s₀).toNat + 24 ≤ 2 ^ 32

theorem APre.of (s₀ : State) (h : preX86 s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  have e : stkR s₀ = ⟨(E s₀).setWidth 64 - 32, 32⟩ := by
    simp only [stkR, below]; rw [Taint.sub_setWidth h18]; rfl
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, e ▸ h12, e ▸ h13, e ▸ h14, h15, h16, h17, h18, h19⟩

/-! ## Addresses -/

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- `[x + k]`, when it does not wrap. -/
theorem add_setWidth {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 k := addr_eq h

theorem add_toNat {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, toNat_ofNat32 (by lit_omega), Nat.mod_eq_of_lt h]

section
variable {s₀ : State} (hp : APre s₀)
include hp

theorem APre.c64 {k : Nat} (hk : k < 1024) : (C32 s₀ k).setWidth 64 = cx s₀ + BitVec.ofNat 64 k :=
  add_setWidth (by have := hp.fit_c; omega)

theorem APre.cNat {k : Nat} (hk : k < 1024) : (C32 s₀ k).toNat = (CX s₀).toNat + k :=
  add_toNat (by have := hp.fit_c; omega)

theorem APre.ea_ctx {d : Nat} (hd : d < 1024) : addr (CX s₀) d = cx s₀ + BitVec.ofNat 64 d :=
  hp.c64 hd

theorem APre.in_ctx {a w : Nat} (h : a + w ≤ 1024) : InRegions s₀.wr (cx s₀ + BitVec.ofNat 64 a) w :=
  ⟨ctxR s₀, by simp [hp.wr], contains_off h (by lit_omega)⟩

theorem APre.in_ctx' {a w : Nat} (h : a + w ≤ 1024) :
    InRegions (s₀.rd ++ s₀.wr) (cx s₀ + BitVec.ofNat 64 a) w :=
  ⟨ctxR s₀, by simp [hp.wr], contains_off h (by lit_omega)⟩

theorem APre.arg_contains {i : Nat} (hi : i < 5) : (argR s₀).Contains (argAddr s₀ i) 4 := by
  have := hp.sp_hi
  simp only [E] at this
  simp only [argR, argAddr]
  rw [show s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i) = (s₀.gpr .esp + BitVec.ofNat 32 4) +
    BitVec.ofNat 32 (4 * i) by rw [BitVec.add_assoc, ← BitVec.ofNat_add],
    add_setWidth (x := s₀.gpr .esp + BitVec.ofNat 32 4) (by rw [add_toNat (by lit_omega)]; omega)]
  exact contains_off (by lit_omega) (by lit_omega)

theorem APre.in_arg {i : Nat} (hi : i < 5) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨argR s₀, by simp [hp.wr], hp.arg_contains hi⟩

theorem APre.E64 {n : Nat} (hn : n ≤ 32) :
    (E s₀ - BitVec.ofNat 32 n).setWidth 64 = (E s₀).setWidth 64 - BitVec.ofNat 64 n :=
  Taint.sub_setWidth (by have := hp.sp_lo; omega)

end

theorem toNat_setWidth64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp [BitVec.toNat_setWidth]; omega

theorem ea_esp (s : State) (d : Nat) : s.ea (at_ .esp d) = addr (s.gpr .esp) d := rfl

theorem argAddr_eq (s₀ : State) (i : Nat) : argAddr s₀ i = addr (E s₀) (4 + 4 * i) := rfl

/-! ## Regions -/

theorem sub_ctx (s₀ : State) {k n : Nat} (h : k + n ≤ 1024) : Region.Sub (sub s₀ k n) (ctxR s₀) :=
  Offset.sub_base (cx s₀) h

theorem sub_sub (s₀ : State) {a m k n : Nat} (h₁ : a ≤ k) (h₂ : k + n ≤ a + m) (_h₃ : a + m ≤ 1024) :
    Region.Sub (sub s₀ k n) (sub s₀ a m) := Offset.sub (cx s₀) h₁ h₂

theorem sub_disj (s₀ : State) {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 1024)
    (hb : b + m ≤ 1024) : (sub s₀ a n).Disjoint (sub s₀ b m) := Offset.disjoint (cx s₀) h (by lit_omega) (by lit_omega)

theorem contains_sub (s₀ : State) {k n a w : Nat} (h₁ : k ≤ a) (h₂ : a + w ≤ k + n) (h₃ : k + n ≤ 1024) :
    (sub s₀ k n).Contains (cx s₀ + BitVec.ofNat 64 a) w := Offset.contains (cx s₀) h₁ h₂ (by lit_omega)

theorem stk_below (s₀ : State) {n : Nat} (hn : n ≤ 32) (hp : APre s₀) :
    Region.Sub (below (E s₀) n) (stkR s₀) := below_sub hn hp.sp_lo

section
variable {s₀ : State} (hp : APre s₀)
include hp

theorem APre.stk_sub {k n : Nat} (h : k + n ≤ 1024) : (stkR s₀).Disjoint (sub s₀ k n) :=
  hp.stk_c.sub_right (sub_ctx s₀ h)

theorem APre.below_sub {m k n : Nat} (hm : m ≤ 32) (h : k + n ≤ 1024) :
    (below (E s₀) m).Disjoint (sub s₀ k n) := (hp.stk_sub h).sub_left (stk_below s₀ hm hp)

theorem APre.g_sub {k n : Nat} (h : k + n ≤ 1024) : (argR s₀).Disjoint (sub s₀ k n) :=
  hp.g_c.sub_right (sub_ctx s₀ h)

theorem APre.ret_sub {k n : Nat} (h : k + n ≤ 1024) : (retR s₀).Disjoint (sub s₀ k n) :=
  hp.ret_c.sub_right (sub_ctx s₀ h)

theorem APre.d_sub {k n : Nat} (h : k + n ≤ 1024) : (dR s₀).Disjoint (sub s₀ k n) :=
  hp.c_d.symm.sub_right (sub_ctx s₀ h)

theorem APre.a_sub {k n : Nat} (h : k + n ≤ 1024) : (aR s₀).Disjoint (sub s₀ k n) :=
  hp.c_a.symm.sub_right (sub_ctx s₀ h)

/-- The arguments are above the stack the calls use. -/
theorem APre.g_stk : (argR s₀).Disjoint (stkR s₀) := by
  have h₂ := hp.sp_hi
  have := Offset.disjoint_base ((E s₀).setWidth 64 - BitVec.ofNat 64 32) (d := 36) (n := 20) (k := 32)
    (by decide) (by decide)
  rw [show (E s₀).setWidth 64 - BitVec.ofNat 64 32 + BitVec.ofNat 64 36 = (E s₀).setWidth 64 + BitVec.ofNat 64 4 by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl] at this
  simp only [stkR, below, hp.E64 (Nat.le_refl _), argR, argAddr]
  rw [show s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0) = s₀.gpr .esp + BitVec.ofNat 32 4 from rfl,
    add_setWidth (by simp only [E] at h₂; omega)]
  exact this

theorem APre.ret_stk : (retR s₀).Disjoint (stkR s₀) := by
  have := Offset.disjoint_base ((E s₀).setWidth 64 - BitVec.ofNat 64 32) (d := 32) (n := 4) (k := 32)
    (by decide) (by decide)
  rw [BitVec.sub_add_cancel] at this
  simp only [stkR, below, hp.E64 (Nat.le_refl _)]
  exact this

end

/-! ## Memory -/

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem sub_off (p : Addr) {a n len : Nat} (h : a + n ≤ len) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, n⟩ ⟨p, len⟩ := Offset.sub_base p h

/-- A Poly1305 state outside a frame is unchanged. -/
theorem Repr.frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr}
    (hd : ∀ r ∈ rs, (⟨P, 128⟩ : Region).Disjoint r) {key msg : List Byte} (h : Repr m P key msg) :
    Repr m' P key msg := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · rw [show (P + 24 : Addr) = P + BitVec.ofNat 64 24 from rfl,
      bytesAt_frame hf (n := 32) (fun r hr => (hd r hr).sub_left (sub_off P (a := 24) (by lit_omega)))
      (by lit_omega)]
    exact h2
  · rw [bytesAt_frame hf (n := 24) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by lit_omega)))
      (by lit_omega)]
    exact h3

/-! ## The saved registers and the invariant -/

/-- Our caller's `ebx, esi, edi, ebp`, saved in `ctx[592, 608)`. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (cx s₀ + BitVec.ofNat 64 ·) s₀.gpr saved

theorem saved_bound : ∀ p ∈ saved, 592 ≤ p.2 ∧ p.2 + 4 ≤ 608 := by decide

theorem saved_contains (s₀ : State) : ∀ p ∈ saved, (sub s₀ 592 16).Contains (cx s₀ + BitVec.ofNat 64 p.2) 4 :=
  fun p hp => have h := saved_bound p hp; contains_sub s₀ h.1 h.2 (by lit_omega)

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sub s₀ 592 16).Disjoint r) : Saved s₀ m' :=
  Spill.Saved.of_frame h hf (saved_contains s₀) hd

/-- The working space: `ctx[64, 1024)`. -/
abbrev workR (s₀ : State) : Region := sub s₀ 64 960

/-- What holds between the parts of the code. -/
structure Inv (s₀ : State) (s : State) : Prop where
  edi : s.gpr .edi = CX s₀
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [workR s₀, dR s₀, stkR s₀] s₀.mem s.mem

/-- The arguments are never written. -/
theorem Inv.arg {s₀ s : State} (hp : APre s₀) (h : Inv s₀ s) {i : Nat} (hi : i < 5) :
    s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  refine h.frame.readW (hp.arg_contains hi) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hp.g_sub (by lit_omega)
  · exact hp.g_d
  · exact hp.g_stk

/-- The invariant survives code that keeps `edi` and `esp` and writes only
the working space (not the saved registers), the data and the stack. -/
theorem Inv.step {s₀ s s' : State} (h : Inv s₀ s) (hedi : s'.gpr .edi = s.gpr .edi)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hsub : ∀ r ∈ rs, ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ 592 16).Disjoint r) : Inv s₀ s' where
  edi := by rw [hedi, h.edi]
  esp := by rw [hesp, h.esp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  saved := h.saved.frame hf hsv
  frame := h.frame.trans (hf.sub hsub)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-! ## Pointers -/

set_option simprocs false in
theorem ptr_ok (d r : Reg) (k : Nat) (s : State) :
    WP isa (.block (ptr d r k)) s fun s' =>
      s'.gpr d = s.gpr r + BitVec.ofNat 32 k ∧ (∀ q, q ≠ d → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ptr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨trivial, fun q hq => by simp [hq], trivial⟩

/-! ## Covering the callees' regions -/

theorem covers_ctx {s₀ : State} (hp : APre s₀) {wr : List Region} (hwr : ctxR s₀ ∈ wr) (rs : List Region)
    (h : ∀ r ∈ rs, ∃ k, r = sub s₀ k r.len ∧ k + r.len ≤ 1024) : Covers rs wr := by
  refine Covers.of_sub fun r hr => ?_
  obtain ⟨k, hrk, hk⟩ := h r hr
  have _ := hp
  exact ⟨ctxR s₀, hwr, k, by rw [hrk], hk⟩

end VG.Proof.ChaCha20Poly1305.X86

end

/-!
# ChaCha20-Poly1305 on x86 (32-bit): the calls

Each call of a verified function, in a frame of its arguments (`callWith`),
from its proof of `Verified` (`WP.callWith`): what it needs of the state it is
called from (`CallPre`, which the constant-time proof uses too), and what
holds when it returns.
-/

open VG.PowLit

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86
open VG.Proof.ChaCha20.X86 (contains_off toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-! ## The callees -/

theorem block_nosp : NoSp Impl.ChaCha20.X86.block := NoSp.of_all (by lit_decide)
theorem xor_nosp : NoSp Impl.ChaCha20.X86.Xor.xor := NoSp.of_all (by lit_decide)
theorem init_nosp : NoSp Impl.Poly1305.X86.init := NoSp.of_all (by lit_decide)
theorem blocks_nosp : NoSp Impl.Poly1305.X86.blocks := NoSp.of_all (by lit_decide)
theorem finalize_nosp : NoSp Impl.Poly1305.X86.finalize := NoSp.of_all (by lit_decide)

theorem block_stack : stackUse Impl.ChaCha20.X86.block = 0 := by lit_decide
theorem xor_stack : stackUse Impl.ChaCha20.X86.Xor.xor = 12 := by lit_decide
theorem init_stack : stackUse Impl.Poly1305.X86.init = 0 := by lit_decide
theorem blocks_stack : stackUse Impl.Poly1305.X86.blocks = 0 := by lit_decide
theorem finalize_stack : stackUse Impl.Poly1305.X86.finalize = 0 := by lit_decide

/-! ## The state a call is made from -/

structure At (s₀ s : State) : Prop where
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem Inv.at {s₀ s : State} (h : Inv s₀ s) : At s₀ s := ⟨h.esp, h.rd, h.wr⟩

/-- Part of the stack below the return address. -/
theorem stk_part {s₀ : State} (hp : APre s₀) {a n : Nat} (h : n ≤ a) (ha : a ≤ 32) :
    Region.Sub ⟨(E s₀ - BitVec.ofNat 32 a).setWidth 64, n⟩ (stkR s₀) :=
  fun x hx => below_sub ha hp.sp_lo x (Region.sub_prefix h x hx)

section
variable {s₀ s : State} (hp : APre s₀) (h : At s₀ s) {rs : List Reg} (hk : rs.length ≤ 5)
include hp h hk

theorem At.fit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat := by
  rw [h.esp]; have := hp.sp_lo; omega

omit hp hk in
theorem At.argAddr0 :
    argAddr (pushed rs s).callEntry 0 = (E s₀ - BitVec.ofNat 32 (4 * rs.length)).setWidth 64 := by
  rw [callEntry_argAddr0, h.esp]

omit hp hk in
theorem At.esp64 :
    ((pushed rs s).callEntry.gpr .esp).setWidth 64 =
      (E s₀ - BitVec.ofNat 32 (4 * rs.length + 4)).setWidth 64 := by
  rw [callEntry_esp', h.esp]

theorem At.espNat : ((pushed rs s).callEntry.gpr .esp).toNat = (E s₀).toNat - (4 * rs.length + 4) := by
  rw [callEntry_espNat (h.fit hp hk), h.esp]

end

/-- A region at offset `o` within one of `rs'`. -/
theorem within {r : Region} {rs' : List Region} (r' : Region) (hr' : r' ∈ rs') (o : Nat)
    (hb : r.base = r'.base + BitVec.ofNat 64 o) (hl : o + r.len ≤ r'.len) :
    ∃ r' ∈ rs', ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len :=
  ⟨r', hr', o, hb, hl⟩

/-! ## `vg_chacha20_block` -/

/-- The permissions it is called with. -/
abbrev rdBlk (s₀ : State) : List Region := [sub s₀ 64 64, below (E s₀) 8]
abbrev wrBlk (s₀ : State) : List Region := [sub s₀ 128 256]

theorem block_pre {s₀ s : State} (hp : APre s₀) (h : At s₀ s) (hecx : s.gpr .ecx = C32 s₀ 64)
    (hedx : s.gpr .edx = C32 s₀ 128) :
    CallPre Proof.ChaCha20.blockX86 [.edx, .ecx] (rdBlk s₀) (wrBlk s₀) s := by
  have hk : [Reg.edx, .ecx].length ≤ 5 := by decide
  have fit := h.fit hp hk
  have a0 : arg (pushed [.edx, .ecx] s).callEntry 0 = C32 s₀ 64 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hecx
  have a1 : arg (pushed [.edx, .ecx] s).callEntry 1 = C32 s₀ 128 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hedx
  have e := hp.sp_lo
  have e' := hp.fit_c
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.ChaCha20.blockX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, h.argAddr0,
      h.esp64, h.espNat hp hk, hp.c64 (k := 64) (by lit_omega), hp.c64 (k := 128) (by lit_omega),
      hp.cNat (k := 64) (by lit_omega), hp.cNat (k := 128) (by lit_omega), List.length_cons, List.length_nil]
    refine ⟨trivial, trivial, sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega),
      (hp.below_sub (m := 8) (by lit_omega) (by lit_omega)), ?_, by omega, by omega, by omega⟩
    exact (hp.stk_sub (by lit_omega)).sub_left (stk_part hp (by lit_omega) (by lit_omega))
  · rw [h.esp, h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact within (ctxR s₀) (by simp) 64 rfl (by show 64 + 64 ≤ 1024; omega)
    · exact within (below (E s₀) 8) (by simp) 0 (by simp) (by simp)
    · exact within (ctxR s₀) (by simp) 128 rfl (by show 128 + 256 ≤ 1024; omega)
  · rw [h.esp, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact within (ctxR s₀) (by simp) 128 rfl (by show 128 + 256 ≤ 1024; omega)

/-! ## What holds after a call -/

/-- The call's frame and return address are on the stack below `esp`. -/
theorem At.entry_frame {s₀ s : State} (hp : APre s₀) (h : At s₀ s) {rs : List Reg} (hk : rs.length ≤ 5)
    (hrs : Reg.esp ∉ rs) : Frame [stkR s₀] s.mem (pushed rs s).callEntry.mem :=
  (callEntry_frame (h.fit hp hk) hrs).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by rw [h.esp]; exact below_sub (by lit_omega) hp.sp_lo⟩

/-- A call returns in a state from which calls can be made, with the
callee-saved registers. -/
theorem At.ret {s₀ s s' : State} (h : At s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) : At s₀ s' :=
  ⟨by rw [cs .esp (by simp [calleeSaved]), h.esp], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

theorem block_call {s₀ s : State} (hp : APre s₀) (h : At s₀ s) (hecx : s.gpr .ecx = C32 s₀ 64)
    (hedx : s.gpr .edx = C32 s₀ 128) {Q : State → Prop}
    (hQ : ∀ s', At s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [sub s₀ 128 256, stkR s₀] s.mem s'.mem →
      stateAt s'.mem (cx s₀ + BitVec.ofNat 64 128) =
        Spec.ChaCha20.block (stateAt s.mem (cx s₀ + BitVec.ofNat 64 64)) → Q s') :
    WP isa (callWith [.edx, .ecx] "vg_chacha20_block" Impl.ChaCha20.X86.block) s Q := by
  have hk : [Reg.edx, .ecx].length ≤ 5 := by decide
  have fit := h.fit hp hk
  have e := hp.sp_lo
  refine WP.callWith Proof.ChaCha20.X86.block_correct block_nosp (by simp) (by decide)
    (by rw [block_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega)
    (block_pre hp h hecx hedx) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [block_stack, h.esp] at f'
  refine hQ s' (h.ret rd' wr' cs') cs' (f'.sub fun r hr => ?_) ?_
  · simp only [wrBlk, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      List.length_cons, List.length_nil] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, below_sub (by lit_omega) hp.sp_lo⟩
  · have a0 : arg (pushed [.edx, .ecx] s).callEntry 0 = C32 s₀ 64 := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hecx
    have a1 : arg (pushed [.edx, .ecx] s).callEntry 1 = C32 s₀ 128 := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hedx
    simp only [Proof.ChaCha20.blockX86, arg_withRegions, State.withRegions_mem, a0, a1,
      hp.c64 (k := 64) (by lit_omega), hp.c64 (k := 128) (by lit_omega), m₂] at post
    rw [post, VG.Proof.ChaCha20.X86.Xor.stateAt_frame (h.entry_frame hp hk (by decide)) (by
      simp only [List.mem_singleton, forall_eq]; exact (hp.stk_sub (by lit_omega)).symm)]

/-! ## `vg_poly1305_init` -/

abbrev rdInit (s₀ : State) : List Region := [sub s₀ 128 32, below (E s₀) 8]
abbrev wrInit (s₀ : State) : List Region := [sub s₀ 448 128]

theorem init_pre {s₀ s : State} (hp : APre s₀) (h : At s₀ s) (hecx : s.gpr .ecx = C32 s₀ 128)
    (hedx : s.gpr .edx = C32 s₀ 448) :
    CallPre Proof.Poly1305.initX86 [.ecx, .edx] (rdInit s₀) (wrInit s₀) s := by
  have hk : [Reg.ecx, .edx].length ≤ 5 := by decide
  have fit := h.fit hp hk
  have a0 : arg (pushed [.ecx, .edx] s).callEntry 0 = C32 s₀ 448 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hedx
  have a1 : arg (pushed [.ecx, .edx] s).callEntry 1 = C32 s₀ 128 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hecx
  have e := hp.sp_lo
  have e' := hp.fit_c
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Poly1305.initX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, h.argAddr0,
      h.esp64, h.espNat hp hk, hp.c64 (k := 448) (by lit_omega), hp.c64 (k := 128) (by lit_omega),
      hp.cNat (k := 448) (by lit_omega), hp.cNat (k := 128) (by lit_omega), List.length_cons, List.length_nil]
    refine ⟨trivial, trivial, sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega),
      (hp.below_sub (m := 8) (by lit_omega) (by lit_omega)), ?_, by omega, by omega, by omega⟩
    exact (hp.stk_sub (by lit_omega)).sub_left (stk_part hp (by lit_omega) (by lit_omega))
  · rw [h.esp, h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact within (ctxR s₀) (by simp) 128 rfl (by show 128 + 32 ≤ 1024; omega)
    · exact within (below (E s₀) 8) (by simp) 0 (by simp) (by simp)
    · exact within (ctxR s₀) (by simp) 448 rfl (by show 448 + 128 ≤ 1024; omega)
  · rw [h.esp, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact within (ctxR s₀) (by simp) 448 rfl (by show 448 + 128 ≤ 1024; omega)

theorem init_call {s₀ s : State} (hp : APre s₀) (h : At s₀ s) (hecx : s.gpr .ecx = C32 s₀ 128)
    (hedx : s.gpr .edx = C32 s₀ 448) {Q : State → Prop}
    (hQ : ∀ s', At s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [sub s₀ 448 128, stkR s₀] s.mem s'.mem →
      Repr s'.mem (cx s₀ + BitVec.ofNat 64 448) (bytesAt s.mem (cx s₀ + BitVec.ofNat 64 128) 32) [] →
      Q s') :
    WP isa (callWith [.ecx, .edx] "vg_poly1305_init" Impl.Poly1305.X86.init) s Q := by
  have hk : [Reg.ecx, .edx].length ≤ 5 := by decide
  have fit := h.fit hp hk
  have e := hp.sp_lo
  refine WP.callWith Proof.Poly1305.X86.init_ok init_nosp (by simp) (by decide)
    (by rw [init_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega)
    (init_pre hp h hecx hedx) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [init_stack, h.esp] at f'
  refine hQ s' (h.ret rd' wr' cs') cs' (f'.sub fun r hr => ?_) ?_
  · simp only [wrInit, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      List.length_cons, List.length_nil] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, below_sub (by lit_omega) hp.sp_lo⟩
  · have a0 : arg (pushed [.ecx, .edx] s).callEntry 0 = C32 s₀ 448 := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hedx
    have a1 : arg (pushed [.ecx, .edx] s).callEntry 1 = C32 s₀ 128 := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hecx
    simp only [Proof.Poly1305.initX86, arg_withRegions, State.withRegions_mem, a0, a1,
      hp.c64 (k := 448) (by lit_omega), hp.c64 (k := 128) (by lit_omega), m₂] at post
    rwa [bytesAt_frame (h.entry_frame hp hk (by decide)) (by
      simp only [List.mem_singleton, forall_eq]; exact (hp.stk_sub (by lit_omega)).symm) (by lit_omega)] at post

/-! ## `vg_poly1305_blocks` -/

/-- What the `len` bytes at `P` absorbed must be: within memory the functions
may read, and apart from the Poly1305 state and the stack. -/
structure BSrc (s₀ : State) (P : BitVec 32) (len : Nat) : Prop where
  fit : P.toNat + len ≤ 2 ^ 32
  poly : (sub s₀ 448 128).Disjoint ⟨P.setWidth 64, len⟩
  stk : (stkR s₀).Disjoint ⟨P.setWidth 64, len⟩
  cov : ∃ r' ∈ s₀.rd ++ s₀.wr, ∃ o, P.setWidth 64 = r'.base + BitVec.ofNat 64 o ∧ o + len ≤ r'.len

abbrev rdBlocks (s₀ : State) (P : BitVec 32) (n : Nat) : List Region :=
  [⟨P.setWidth 64, 16 * n⟩, below (E s₀) 12]
abbrev wrBlocks (s₀ : State) : List Region := [sub s₀ 448 128]

theorem blocks_pre {s₀ s : State} (hp : APre s₀) (h : At s₀ s) {rn rp rst : Reg}
    (hesp : Reg.esp ∉ [rn, rp, rst]) {P : BitVec 32} {n : Nat} (hs : BSrc s₀ P (16 * n))
    (hst : s.gpr rst = C32 s₀ 448) (hP : s.gpr rp = P) (hn : s.gpr rn = BitVec.ofNat 32 n) :
    CallPre Proof.Poly1305.blocksX86 [rn, rp, rst] (rdBlocks s₀ P n) (wrBlocks s₀) s := by
  have hk : [rn, rp, rst].length ≤ 5 := by simp
  have fit := h.fit hp hk
  have hf := hs.fit
  have a0 : arg (pushed [rn, rp, rst] s).callEntry 0 = C32 s₀ 448 := by
    rw [callEntry_arg fit hesp (by simp)]; exact hst
  have a1 : arg (pushed [rn, rp, rst] s).callEntry 1 = P := by
    rw [callEntry_arg fit hesp (by simp)]; exact hP
  have a2 : (arg (pushed [rn, rp, rst] s).callEntry 2).toNat = n := by
    rw [callEntry_arg fit hesp (by simp)]
    show (s.gpr rn).toNat = n
    rw [hn, toNat_ofNat32 (by lit_omega)]
  have e := hp.sp_lo
  have e' := hp.fit_c
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Poly1305.blocksX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, a2, h.argAddr0,
      h.esp64, h.espNat hp hk, hp.c64 (k := 448) (by lit_omega), hp.cNat (k := 448) (by lit_omega),
      List.length_cons, List.length_nil]
    refine ⟨trivial, trivial, hs.poly, (hp.below_sub (m := 12) (by lit_omega) (by lit_omega)), ?_, by omega,
      hf, by omega⟩
    exact (hp.stk_sub (by lit_omega)).sub_left (stk_part hp (by lit_omega) (by lit_omega))
  · rw [h.esp, h.rd, h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨r', hr', o, hb, hl⟩ := hs.cov
      refine ⟨r', ?_, o, hb, hl⟩
      rcases List.mem_append.mp hr' with hr' | hr'
      · exact List.mem_append_left _ hr'
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr')
    · exact within (below (E s₀) 12) (by simp) 0 (by simp) (by simp)
    · exact within (ctxR s₀) (by simp [hp.wr]) 448 rfl (by show 448 + 128 ≤ 1024; omega)
  · rw [h.esp, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact within (ctxR s₀) (by simp) 448 rfl (by show 448 + 128 ≤ 1024; omega)

theorem blocks_call {s₀ s : State} (hp : APre s₀) (h : At s₀ s) {rn rp rst : Reg}
    (hesp : Reg.esp ∉ [rn, rp, rst]) {P : BitVec 32} {n : Nat} (hs : BSrc s₀ P (16 * n))
    (hst : s.gpr rst = C32 s₀ 448) (hP : s.gpr rp = P) (hn : s.gpr rn = BitVec.ofNat 32 n)
    {Q : State → Prop}
    (hQ : ∀ s', At s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [sub s₀ 448 128, stkR s₀] s.mem s'.mem →
      (∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        Repr s'.mem (cx s₀ + BitVec.ofNat 64 448) key (msg ++ bytesAt s.mem (P.setWidth 64) (16 * n))) →
      Q s') :
    WP isa (callWith [rn, rp, rst] "vg_poly1305_blocks" Impl.Poly1305.X86.blocks) s Q := by
  have hk : [rn, rp, rst].length ≤ 5 := by simp
  have fit := h.fit hp hk
  have e := hp.sp_lo
  have hf := hs.fit
  refine WP.callWith Proof.Poly1305.X86.blocks_ok blocks_nosp (by simp) hesp
    (by rw [blocks_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega)
    (blocks_pre hp h hesp hs hst hP hn) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [blocks_stack, h.esp] at f'
  refine hQ s' (h.ret rd' wr' cs') cs' (f'.sub fun r hr => ?_) fun key msg hr => ?_
  · simp only [wrBlocks, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      List.length_cons, List.length_nil] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, below_sub (by lit_omega) hp.sp_lo⟩
  · have a0 : arg (pushed [rn, rp, rst] s).callEntry 0 = C32 s₀ 448 := by
      rw [callEntry_arg fit hesp (by simp)]; exact hst
    have a1 : arg (pushed [rn, rp, rst] s).callEntry 1 = P := by
      rw [callEntry_arg fit hesp (by simp)]; exact hP
    have a2 : (arg (pushed [rn, rp, rst] s).callEntry 2).toNat = n := by
      rw [callEntry_arg fit hesp (by simp)]
      show (s.gpr rn).toNat = n
      rw [hn, toNat_ofNat32 (by lit_omega)]
    simp only [Proof.Poly1305.blocksX86, arg_withRegions, State.withRegions_mem, a0, a1, a2,
      hp.c64 (k := 448) (by lit_omega), m₂] at post
    have ef := h.entry_frame hp hk hesp
    have := post key msg (Repr.frame ef (by
      simp only [List.mem_singleton, forall_eq]; exact (hp.stk_sub (by lit_omega)).symm) hr)
    rwa [bytesAt_frame ef (by simp only [List.mem_singleton, forall_eq]; exact hs.stk.symm)
      (by lit_omega)] at this

/-! ## `vg_chacha20_xor` -/

abbrev wrXor (s₀ : State) : List Region := [sub s₀ 64 64, dR s₀, sub s₀ 128 320, below (E s₀) 16]

theorem xor_pre {s₀ s : State} (hp : APre s₀) (h : At s₀ s) (heax : s.gpr .eax = C32 s₀ 64)
    (hecx : s.gpr .ecx = DP s₀) (hedx : s.gpr .edx = LN s₀) (hesi : s.gpr .esi = C32 s₀ 128) :
    CallPre Proof.ChaCha20.xorX86 [.esi, .edx, .ecx, .eax] [] (wrXor s₀) s := by
  have hk : [Reg.esi, .edx, .ecx, .eax].length ≤ 5 := by decide
  have fit := h.fit hp hk
  have a0 : arg (pushed [.esi, .edx, .ecx, .eax] s).callEntry 0 = C32 s₀ 64 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact heax
  have a1 : arg (pushed [.esi, .edx, .ecx, .eax] s).callEntry 1 = DP s₀ := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hecx
  have a2 : arg (pushed [.esi, .edx, .ecx, .eax] s).callEntry 2 = LN s₀ := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hedx
  have a3 : arg (pushed [.esi, .edx, .ecx, .eax] s).callEntry 3 = C32 s₀ 128 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact hesi
  have e := hp.sp_lo
  have e₂ := hp.sp_hi
  have e' := hp.fit_c
  have es : (E s₀ - BitVec.ofNat 32 20).setWidth 64 - 12 = (E s₀ - BitVec.ofNat 32 32).setWidth 64 := by
    rw [hp.E64 (by lit_omega), hp.E64 (by lit_omega), BitVec.sub_sub]; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.ChaCha20.xorX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, h.argAddr0,
      h.esp64, h.espNat hp hk, hp.c64 (k := 64) (by lit_omega), hp.c64 (k := 128) (by lit_omega),
      hp.cNat (k := 64) (by lit_omega), hp.cNat (k := 128) (by lit_omega), List.length_cons, List.length_nil, es]
    refine ⟨trivial, trivial, (hp.d_sub (by lit_omega)).symm, sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega),
      hp.d_sub (by lit_omega), hp.below_sub (by lit_omega) (by lit_omega),
      (hp.stk_d.sub_left (stk_below s₀ (n := 16) (by lit_omega) hp)),
      hp.below_sub (by lit_omega) (by lit_omega), ?_, ?_, ?_, ?_, ?_, ?_, by omega, hp.fit_d, by omega, by omega,
      by omega⟩
    · exact (hp.stk_sub (by lit_omega)).sub_left (stk_part hp (by lit_omega) (by lit_omega))
    · exact hp.stk_d.sub_left (stk_part hp (by lit_omega) (by lit_omega))
    · exact (hp.stk_sub (by lit_omega)).sub_left (stk_part hp (by lit_omega) (by lit_omega))
    · exact (hp.stk_sub (by lit_omega)).sub_left (stk_part hp (by lit_omega) (by lit_omega))
    · exact hp.stk_d.sub_left (stk_part hp (by lit_omega) (by lit_omega))
    · exact (hp.stk_sub (by lit_omega)).sub_left (stk_part hp (by lit_omega) (by lit_omega))
  · rw [h.esp, h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact within (ctxR s₀) (by simp) 64 rfl (by show 64 + 64 ≤ 1024; omega)
    · exact within (dR s₀) (by simp) 0 (by simp) (by simp)
    · exact within (ctxR s₀) (by simp) 128 rfl (by show 128 + 320 ≤ 1024; omega)
    · exact within (below (E s₀) 16) (by simp) 0 (by simp) (by simp)
  · rw [h.esp, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact within (ctxR s₀) (by simp) 64 rfl (by show 64 + 64 ≤ 1024; omega)
    · exact within (dR s₀) (by simp) 0 (by simp) (by simp)
    · exact within (ctxR s₀) (by simp) 128 rfl (by show 128 + 320 ≤ 1024; omega)
    · exact within (below (E s₀) 16) (by simp) 0 (by simp) (by simp)

theorem xor_call {s₀ s : State} (hp : APre s₀) (h : At s₀ s) (heax : s.gpr .eax = C32 s₀ 64)
    (hecx : s.gpr .ecx = DP s₀) (hedx : s.gpr .edx = LN s₀) (hesi : s.gpr .esi = C32 s₀ 128)
    {Q : State → Prop}
    (hQ : ∀ s', At s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s'.mem →
      Spec.ChaCha20.bytesAt s'.mem (dp s₀) (L s₀) =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem (dp s₀) (L s₀))
          (keystream (stateAt s.mem (cx s₀ + BitVec.ofNat 64 64)) (L s₀)) → Q s') :
    WP isa (callWith [.esi, .edx, .ecx, .eax] "vg_chacha20_xor" Impl.ChaCha20.X86.Xor.xor) s Q := by
  have hk : [Reg.esi, .edx, .ecx, .eax].length ≤ 5 := by decide
  have fit := h.fit hp hk
  have e := hp.sp_lo
  refine WP.callWith Proof.ChaCha20.X86.Xor.xor_correct xor_nosp (by simp) (by decide)
    (by rw [xor_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega)
    (xor_pre hp h heax hecx hedx hesi) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [xor_stack, h.esp] at f'
  refine hQ s' (h.ret rd' wr' cs') cs' (f'.sub fun r hr => ?_) ?_
  · simp only [wrXor, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      List.length_cons, List.length_nil] at hr
    have m1 : sub s₀ 64 384 ∈ [sub s₀ 64 384, dR s₀, stkR s₀] := List.mem_cons_self ..
    have m2 : dR s₀ ∈ [sub s₀ 64 384, dR s₀, stkR s₀] := List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have m3 : stkR s₀ ∈ [sub s₀ 64 384, dR s₀, stkR s₀] :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, m1, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨_, m2, fun _ h => h⟩
    · exact ⟨_, m1, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · exact ⟨stkR s₀, m3, below_sub (by lit_omega) hp.sp_lo⟩
    · exact ⟨stkR s₀, m3, below_sub (by lit_omega) hp.sp_lo⟩
  · have a0 : arg (pushed [.esi, .edx, .ecx, .eax] s).callEntry 0 = C32 s₀ 64 := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact heax
    have a1 : arg (pushed [.esi, .edx, .ecx, .eax] s).callEntry 1 = DP s₀ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hecx
    have a2 : arg (pushed [.esi, .edx, .ecx, .eax] s).callEntry 2 = LN s₀ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hedx
    simp only [Proof.ChaCha20.xorX86, arg_withRegions, State.withRegions_mem, a0, a1, a2,
      hp.c64 (k := 64) (by lit_omega), m₂] at post
    have ef := h.entry_frame hp hk (by decide)
    rw [post, show Spec.ChaCha20.bytesAt = bytesAt from rfl, bytesAt_frame ef (by
      simp only [List.mem_singleton, forall_eq]; exact hp.stk_d.symm) (by have := (LN s₀).isLt; omega),
      VG.Proof.ChaCha20.X86.Xor.stateAt_frame ef (by
      simp only [List.mem_singleton, forall_eq]; exact (hp.stk_sub (by lit_omega)).symm)]

/-! ## `vg_poly1305_finalize` -/

/-- Its arguments: the Poly1305 state, `count = 0` (both words), `out` and
its working space, `ctx[672, 800)`, pushed last to first. -/
abbrev finRegs : List Reg := [.ebx, .ecx, .eax, .eax, .esi]

abbrev rdFin (s₀ : State) : List Region := [below (E s₀) 20]
abbrev wrFin (s₀ : State) (out : Nat) : List Region := [sub s₀ 448 128, sub s₀ out 16, sub s₀ 672 128]

/-- Where the tag may be written. -/
def OutOk (out : Nat) : Prop := out = 48 ∨ out = 640

section
variable {s₀ s : State} (hp : APre s₀) (h : At s₀ s) {out : Nat} (ho : OutOk out)
  (hebx : s.gpr .ebx = C32 s₀ 672) (hecx : s.gpr .ecx = C32 s₀ out) (heax : s.gpr .eax = 0)
  (hesi : s.gpr .esi = C32 s₀ 448)
include hp h hebx hecx heax hesi

theorem fin_args :
    arg (pushed finRegs s).callEntry 0 = C32 s₀ 448 ∧ arg (pushed finRegs s).callEntry 1 = 0 ∧
      arg (pushed finRegs s).callEntry 2 = 0 ∧ arg (pushed finRegs s).callEntry 3 = C32 s₀ out ∧
      arg (pushed finRegs s).callEntry 4 = C32 s₀ 672 := by
  have fit := h.fit hp (rs := finRegs) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [callEntry_arg fit (by decide) (by decide)]
  exacts [hesi, heax, heax, hecx, hebx]

include ho in
theorem finalize_pre : CallPre Proof.Poly1305.finalizeX86 finRegs (rdFin s₀) (wrFin s₀ out) s := by
  have ho' : out + 16 ≤ 1024 := by unfold OutOk at ho; omega
  have hk : finRegs.length ≤ 5 := by decide
  obtain ⟨a0, a1, a2, a3, a4⟩ := fin_args hp h hebx hecx heax hesi (out := out)
  have e := hp.sp_lo
  have e₂ := hp.sp_hi
  have e' := hp.fit_c
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Poly1305.finalizeX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a3, a4, h.argAddr0,
      h.esp64, h.espNat hp hk, hp.c64 (k := 448) (by lit_omega), hp.c64 (k := 672) (by lit_omega),
      hp.c64 (k := out) (by lit_omega), hp.cNat (k := 448) (by lit_omega), hp.cNat (k := 672) (by lit_omega),
      hp.cNat (k := out) (by lit_omega), List.length_cons, List.length_nil]
    unfold OutOk at ho
    refine ⟨trivial, trivial, sub_disj s₀ (by lit_omega) (by lit_omega) ho', sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega),
      sub_disj s₀ (by lit_omega) ho' (by lit_omega), hp.below_sub (by lit_omega) (by lit_omega), hp.below_sub (by lit_omega) ho',
      hp.below_sub (by lit_omega) (by lit_omega), ?_, ?_, ?_, by omega, by omega, by omega, by omega⟩
    · exact (hp.stk_sub (by lit_omega)).sub_left (stk_part hp (by lit_omega) (by lit_omega))
    · exact (hp.stk_sub ho').sub_left (stk_part hp (by lit_omega) (by lit_omega))
    · exact (hp.stk_sub (by lit_omega)).sub_left (stk_part hp (by lit_omega) (by lit_omega))
  · rw [h.esp, h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact within (below (E s₀) 20) (by simp) 0 (by simp) (by simp)
    · exact within (ctxR s₀) (by simp) 448 rfl (by show 448 + 128 ≤ 1024; omega)
    · exact within (ctxR s₀) (by simp) out rfl ho'
    · exact within (ctxR s₀) (by simp) 672 rfl (by show 672 + 128 ≤ 1024; omega)
  · rw [h.esp, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact within (ctxR s₀) (by simp) 448 rfl (by show 448 + 128 ≤ 1024; omega)
    · exact within (ctxR s₀) (by simp) out rfl ho'
    · exact within (ctxR s₀) (by simp) 672 rfl (by show 672 + 128 ≤ 1024; omega)

include ho in
theorem finalize_call {Q : State → Prop}
    (hQ : ∀ s', At s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [sub s₀ 448 128, sub s₀ out 16, sub s₀ 672 128, stkR s₀] s.mem s'.mem →
      (∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        bytesAt s'.mem (cx s₀ + BitVec.ofNat 64 out) 16 = mac key msg) → Q s') :
    WP isa (callWith finRegs "vg_poly1305_finalize" Impl.Poly1305.X86.finalize) s Q := by
  have ho' : out + 16 ≤ 1024 := by unfold OutOk at ho; omega
  have hk : finRegs.length ≤ 5 := by decide
  have e := hp.sp_lo
  refine WP.callWith Proof.Poly1305.X86.finalize_ok finalize_nosp (by simp) (by decide)
    (by rw [finalize_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega)
    (finalize_pre hp h ho hebx hecx heax hesi) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [finalize_stack, h.esp] at f'
  refine hQ s' (h.ret rd' wr' cs') cs' (f'.sub fun r hr => ?_) fun key msg hr => ?_
  · simp only [wrFin, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      List.length_cons, List.length_nil] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, below_sub (by lit_omega) hp.sp_lo⟩
  · obtain ⟨a0, a1, a2, a3, -⟩ := fin_args hp h hebx hecx heax hesi (out := out)
    simp only [Proof.Poly1305.finalizeX86, Proof.Poly1305.countX86, arg_withRegions, State.withRegions_mem,
      a0, a1, a2, a3, hp.c64 (k := 448) (by lit_omega), hp.c64 (k := out) (by lit_omega), m₂] at post
    exact post key msg (Proof.Poly1305.Repr.buffered (Repr.frame (h.entry_frame hp hk (by decide)) (by
      simp only [List.mem_singleton, forall_eq]; exact (hp.stk_sub (by lit_omega)).symm) hr))
      (by rw [hr.1]; rfl)

end

end VG.Proof.ChaCha20Poly1305.X86

/-!
# ChaCha20-Poly1305 on x86 (32-bit): absorbing padded data

`absorbOne k` absorbs the 16 bytes at `ctx + k`; `macPad p n` absorbs the
bytes whose address and length are the stack arguments at `esp + p` and `esp +
n`, and zeros to a multiple of 16: `msg ++ x ++ pad16 x`. Each stage is stated
separately, for the constant-time proof.
-/

open VG.PowLit

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86
open VG.Impl.ChaCha20.X86 (at_)
open VG.Proof.ChaCha20.X86 (contains_off toNat_ofNat_lt)
open VG.Proof.Poly1305.X86 (wp_movm wp_store wp_movzx8 wp_store8 wp_addx wp_subx wp_movi wp_mov wp_andx
  wp_shr Upd Mupd readSrc_imm readSrc_reg)
open VG.Proof.Poly1305 (writeW8_apply)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20Poly1305 (pad16)

theorem writeW32_zero_apply (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 32)) x = if (x - a).toNat < 4 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

theorem addr_zero_add (x : BitVec 32) (j : Nat) : addr (x + BitVec.ofNat 32 j) 0 = addr x j := by
  simp [addr]

theorem add_ofNat_one (x : BitVec 32) (j : Nat) :
    x + BitVec.ofNat 32 j + 1 = x + BitVec.ofNat 32 (j + 1) := by
  rw [BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]

/-! ## Frames within the working space -/

theorem work_sub (s₀ : State) {k n : Nat} (h₁ : 64 ≤ k) (h₂ : k + n ≤ 1024) :
    ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub (sub s₀ k n) r' :=
  ⟨workR s₀, by simp, sub_sub s₀ h₁ (by lit_omega) (by lit_omega)⟩

theorem stk_work (s₀ : State) : ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub (stkR s₀) r' :=
  ⟨stkR s₀, by simp, fun _ h => h⟩

/-- The invariant survives a part that writes only `ctx[k, k + n)` (apart from
the saved registers) and the stack, and keeps `edi`. -/
theorem Inv.part {s₀ s s' : State} (hp : APre s₀) (h : Inv s₀ s) (h' : At s₀ s')
    (hedi : s'.gpr .edi = s.gpr .edi) {k n : Nat} (h₁ : 64 ≤ k) (h₂ : k + n ≤ 1024)
    (h₃ : k + n ≤ 592 ∨ 608 ≤ k) (hf : Frame [sub s₀ k n, stkR s₀] s.mem s'.mem) : Inv s₀ s' :=
  h.step hedi (by rw [h'.esp, h.esp]) (by rw [h'.rd, h.rd]) (by rw [h'.wr, h.wr]) hf
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact work_sub s₀ h₁ h₂
      · exact stk_work s₀)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) h₂
      · exact (hp.stk_sub (by lit_omega)).symm)

/-! ## Absorbing 16 bytes of the context -/

theorem bsrc_ctx {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k + 16 ≤ 448 ∨ (576 ≤ k ∧ k + 16 ≤ 1024)) :
    BSrc s₀ (C32 s₀ k) 16 := by
  have := hp.fit_c
  refine ⟨by rw [hp.cNat (by lit_omega)]; omega, ?_, ?_,
    ⟨ctxR s₀, by simp [hp.wr], k, hp.c64 (by lit_omega), by show k + 16 ≤ 1024; omega⟩⟩
  · rw [hp.c64 (by lit_omega)]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [hp.c64 (by lit_omega)]; exact hp.stk_sub (by lit_omega)

/-- Ready to call `vg_poly1305_blocks` for the 16 bytes at `ctx + k`. -/
structure OneA (s₀ : State) (k : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  eax : s.gpr .eax = BitVec.ofNat 32 1
  ecx : s.gpr .ecx = C32 s₀ k
  edx : s.gpr .edx = C32 s₀ 448

theorem oneA_ok {s₀ : State} {s : State} (h : Inv s₀ s) (k : Nat) :
    WP isa (.block (([.mov .eax (.imm 1)] : List Instr) ++ ptr .ecx .edi k ++ ptr .edx .edi 448)) s fun s' =>
      OneA s₀ k s' ∧ s'.mem = s.mem := by
  rw [show ([.mov .eax (.imm 1)] ++ ptr .ecx .edi k ++ ptr .edx .edi 448 : List Instr) =
    .mov .eax (.imm 1) :: (ptr .ecx .edi k ++ ptr .edx .edi 448) from rfl]
  refine wp_movi fun s₁ u₁ _ => ?_
  refine WP.block_append (WP.mono (ptr_ok .ecx .edi k s₁) fun s₂ ⟨e₂, g₂, rd₂, wr₂, m₂⟩ => ?_)
  refine WP.mono (ptr_ok .edx .edi 448 s₂) fun s₃ ⟨e₃, g₃, rd₃, wr₃, m₃⟩ => ?_
  have edi : s₂.gpr .edi = CX s₀ := by rw [g₂ _ (by decide), u₁.other _ (by decide), h.edi]
  have mm : s₃.mem = s.mem := by rw [m₃, m₂, u₁.mem]
  refine ⟨⟨h.step (by rw [g₃ _ (by decide), g₂ _ (by decide), u₁.other _ (by decide)])
      (by rw [g₃ _ (by decide), g₂ _ (by decide), u₁.other _ (by decide)])
      (by rw [rd₃, rd₂, u₁.rd]) (by rw [wr₃, wr₂, u₁.wr]) (rs := []) (by rw [mm]; exact Frame.refl _ _)
      (by simp) (by simp),
    by rw [g₃ _ (by decide), g₂ _ (by decide), u₁.gpr]; rfl,
    by rw [g₃ _ (by decide), e₂, u₁.other _ (by decide), h.edi], by rw [e₃, edi]⟩, mm⟩

theorem absorbOne_eq (k : Nat) : absorbOne k =
    .seq (.block (([.mov .eax (.imm 1)] : List Instr) ++ ptr .ecx .edi k ++ ptr .edx .edi 448))
      (callWith [.eax, .ecx, .edx] "vg_poly1305_blocks" Impl.Poly1305.X86.blocks) := rfl

theorem oneB_ok {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k + 16 ≤ 448 ∨ (576 ≤ k ∧ k + 16 ≤ 1024))
    {s : State} (h : OneA s₀ k s) :
    WP isa (callWith [.eax, .ecx, .edx] "vg_poly1305_blocks" Impl.Poly1305.X86.blocks) s fun s' =>
      Inv s₀ s' ∧ Frame [sub s₀ 448 128, stkR s₀] s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        Repr s'.mem (cx s₀ + BitVec.ofNat 64 448) key (msg ++ bytesAt s.mem (cx s₀ + BitVec.ofNat 64 k) 16) := by
  have := hp.fit_c
  refine blocks_call hp h.inv.at (n := 1) (by decide) (bsrc_ctx hp hk) h.edx h.ecx h.eax
    fun s' at' cs' f' repr' => ⟨h.inv.part hp at' (cs' .edi (by simp [calleeSaved])) (k := 448) (n := 128)
      (by lit_omega) (by lit_omega) (by lit_omega) f', f', fun key msg hr => ?_⟩
  have := repr' key msg hr
  rwa [hp.c64 (by lit_omega)] at this

theorem absorbOne_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) {k : Nat}
    (hk : k + 16 ≤ 448 ∨ (576 ≤ k ∧ k + 16 ≤ 1024)) :
    WP isa (absorbOne k) s fun s' =>
      Inv s₀ s' ∧ Frame [sub s₀ 448 128, stkR s₀] s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        Repr s'.mem (cx s₀ + BitVec.ofNat 64 448) key (msg ++ bytesAt s.mem (cx s₀ + BitVec.ofNat 64 k) 16) := by
  rw [absorbOne_eq]
  exact WP.seq (WP.mono (oneA_ok h k) fun s₁ ⟨h₁, m₁⟩ => by
    rw [← m₁]; exact oneB_ok hp hk h₁)

/-! ## The bytes absorbed -/

/-- What `macPad` needs of the `len` bytes at `P` it absorbs. -/
structure Src (s₀ : State) (P : BitVec 32) (len : Nat) : Prop where
  fit : P.toNat + len ≤ 2 ^ 32
  ctx : (ctxR s₀).Disjoint ⟨P.setWidth 64, len⟩
  stk : (stkR s₀).Disjoint ⟨P.setWidth 64, len⟩
  mem : (⟨P.setWidth 64, len⟩ : Region) ∈ s₀.rd ++ s₀.wr

theorem Src.bsrc {s₀ : State} {P : BitVec 32} {len : Nat} (hs : Src s₀ P len) {n : Nat} (hn : n ≤ len) :
    BSrc s₀ P n :=
  ⟨by have := hs.fit; omega, (hs.ctx.sub_left (sub_ctx s₀ (by lit_omega))).sub_right (Region.sub_prefix hn),
   hs.stk.sub_right (Region.sub_prefix hn), ⟨_, hs.mem, 0, by simp, by simpa using hn⟩⟩

theorem shr4 (x : BitVec 32) : x >>> 4 = BitVec.ofNat 32 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, toNat_ofNat32 (by have := x.isLt; omega)]

theorem and15 (x : BitVec 32) : x &&& 15 = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    toNat_ofNat32 (by lit_omega)]

/-! ## The whole blocks -/

/-- Ready to call `vg_poly1305_blocks` for the whole blocks of the bytes whose
address and length are arguments `i` and `i + 1`. -/
structure MA (s₀ : State) (i : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  ebx : s.gpr .ebx = arg s₀ i
  ebp : s.gpr .ebp = arg s₀ (i + 1)
  eax : s.gpr .eax = BitVec.ofNat 32 ((arg s₀ (i + 1)).toNat / 16)
  ecx : s.gpr .ecx = C32 s₀ 448

theorem maA_ok {s₀ : State} (hp : APre s₀) {i : Nat} (hi : i + 1 < 5) {s : State} (h : Inv s₀ s) :
    WP isa (.block (([.mov .ebx (.mem (at_ .esp (4 + 4 * i))), .mov .ebp (.mem (at_ .esp (8 + 4 * i))),
      .mov .eax (.reg .ebp), .shift .shr .eax 4] : List Instr) ++ ptr .ecx .edi 448)) s fun s' =>
      MA s₀ i s' ∧ s'.mem = s.mem := by
  have i₁ : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by rw [h.rd, h.wr]; exact hp.in_arg (by lit_omega)
  have i₂ : InRegions (s.rd ++ s.wr) (argAddr s₀ (i + 1)) 4 := by rw [h.rd, h.wr]; exact hp.in_arg hi
  have a₂ : argAddr s₀ (i + 1) = addr (E s₀) (8 + 4 * i) := by
    rw [argAddr_eq, show 4 + 4 * (i + 1) = 8 + 4 * i by omega]
  rw [List.cons_append]
  refine wp_movm (a := argAddr s₀ i) (by rw [ea_at, h.esp]; rfl) i₁ fun s₁ u₁ _ => ?_
  rw [List.cons_append]
  refine wp_movm (a := argAddr s₀ (i + 1)) (by rw [ea_at, u₁.other _ (by decide), h.esp, a₂])
    (by rw [u₁.rd, u₁.wr]; exact i₂) fun s₂ u₂ _ => ?_
  rw [List.cons_append]
  refine wp_mov fun s₃ u₃ _ => ?_
  rw [List.cons_append]
  refine wp_shr (by lit_omega) fun s₄ u₄ => ?_
  refine WP.mono (ptr_ok .ecx .edi 448 s₄) fun s₅ ⟨e₅, g₅, rd₅, wr₅, m₅⟩ => ?_
  have mm : s₅.mem = s.mem := by rw [m₅, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have edi : s₄.gpr .edi = CX s₀ := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.edi]
  have ebp : s₂.gpr .ebp = arg s₀ (i + 1) := by rw [u₂.gpr, u₁.mem]; exact h.arg hp hi
  refine ⟨⟨h.step (by rw [g₅ _ (by decide), edi, h.edi])
      (by rw [g₅ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide)])
      (by rw [rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [wr₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (rs := [])
      (by rw [mm]; exact Frame.refl _ _) (by simp) (by simp), ?_, ?_, ?_, by rw [e₅, edi]⟩, mm⟩
  · rw [g₅ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    exact h.arg hp (by lit_omega)
  · rw [g₅ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), ebp]
  · rw [g₅ _ (by decide), u₄.gpr, u₃.gpr, ebp, shr4]

/-- After the whole blocks. -/
structure MB (s₀ : State) (i : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  ebx : s.gpr .ebx = arg s₀ i
  ebp : s.gpr .ebp = arg s₀ (i + 1)

theorem maB_ok {s₀ : State} (hp : APre s₀) {i : Nat} (hs : Src s₀ (arg s₀ i) (arg s₀ (i + 1)).toNat)
    {s : State} (h : MA s₀ i s) :
    WP isa (callWith [.eax, .ebx, .ecx] "vg_poly1305_blocks" Impl.Poly1305.X86.blocks) s fun s' =>
      MB s₀ i s' ∧ Frame [sub s₀ 448 128, stkR s₀] s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        Repr s'.mem (cx s₀ + BitVec.ofNat 64 448) key
          (msg ++ bytesAt s.mem ((arg s₀ i).setWidth 64) (16 * ((arg s₀ (i + 1)).toNat / 16))) :=
  blocks_call hp h.inv.at (by decide) (hs.bsrc (Nat.mul_div_le _ _)) h.ecx h.ebx h.eax
    fun s' at' cs' f' repr' =>
      ⟨⟨h.inv.part hp at' (cs' .edi (by simp [calleeSaved])) (k := 448) (n := 128) (by lit_omega) (by lit_omega)
        (by lit_omega) f', by rw [cs' .ebx (by simp [calleeSaved]), h.ebx],
        by rw [cs' .ebp (by simp [calleeSaved]), h.ebp]⟩, f', repr'⟩

/-- The length of the tail tested. -/
structure MC (s₀ : State) (i : Nat) (s : State) : Prop extends MB s₀ i s where
  edx : s.gpr .edx = BitVec.ofNat 32 ((arg s₀ (i + 1)).toNat % 16)
  zf : s.zf = some (decide ((arg s₀ (i + 1)).toNat % 16 = 0))

set_option simprocs false in
theorem maC_ok {s₀ : State} {i : Nat} {s : State} (h : MB s₀ i s) :
    WP isa (.block [.mov .edx (.reg .ebp), .alu .and .edx (.imm 15)]) s fun s' =>
      MC s₀ i s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true]
  have e : s.gpr .ebp &&& 15 = BitVec.ofNat 32 ((arg s₀ (i + 1)).toNat % 16) := by rw [h.ebp, and15]
  refine ⟨⟨⟨h.inv.step (by simp (config := {decide := true})) (by simp (config := {decide := true})) rfl rfl
    (rs := []) (Frame.refl _ _) (by simp) (by simp), by simp (config := {decide := true}) [h.ebx],
    by simp (config := {decide := true}) [h.ebp]⟩, by simp; exact e, ?_⟩, trivial⟩
  simp only [e]
  by_cases h0 : (arg s₀ (i + 1)).toNat % 16 = 0
  · simp [h0]
  · have : BitVec.ofNat 32 ((arg s₀ (i + 1)).toNat % 16) ≠ 0 := by
      intro he; have := congrArg BitVec.toNat he; rw [toNat_ofNat32 (by lit_omega)] at this; exact h0 this
    simp only [h0, decide_false, Option.some.injEq, beq_eq_false_iff_ne, ne_eq]
    exact this

/-! ## The tail, padded -/

/-- The zeroed block. -/
theorem zero16 (m : Mem) (c : Addr) {j : Nat} (hj : j < 16) :
    ((((m.writeW (c + BitVec.ofNat 64 576) (0 : BitVec 32)).writeW (c + BitVec.ofNat 64 580) (0 : BitVec 32)).writeW
      (c + BitVec.ofNat 64 584) (0 : BitVec 32)).writeW (c + BitVec.ofNat 64 588) (0 : BitVec 32))
        (c + BitVec.ofNat 64 (576 + j)) = 0 := by
  have key : ∀ d, d ≤ 12 → ((c + BitVec.ofNat 64 (576 + j) - (c + BitVec.ofNat 64 (576 + d))).toNat < 4 ↔
      d ≤ j ∧ j < d + 4) := by
    intro d hd
    rw [Offset.sub_toNat' c (by lit_omega) (by lit_omega)]
    split <;> omega
  simp only [writeW32_zero_apply]
  rw [show (588 : Nat) = 576 + 12 from rfl, show (584 : Nat) = 576 + 8 from rfl,
    show (580 : Nat) = 576 + 4 from rfl, show c + BitVec.ofNat 64 576 = c + BitVec.ofNat 64 (576 + 0) from rfl]
  simp only [key 12 (by lit_omega), key 8 (by lit_omega), key 4 (by lit_omega), key 0 (by lit_omega)]
  split_ifs <;> first | rfl | omega

/-- The tail's start, its length in `edx`, and `ecx` at the zeroed block. -/
structure PD (s₀ : State) (i : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  esi : s.gpr .esi = arg s₀ i + BitVec.ofNat 32 (16 * ((arg s₀ (i + 1)).toNat / 16))
  ecx : s.gpr .ecx = C32 s₀ 576
  edx : s.gpr .edx = BitVec.ofNat 32 ((arg s₀ (i + 1)).toNat % 16)

theorem tail_start (P N : BitVec 32) :
    N - BitVec.ofNat 32 (N.toNat % 16) + P = P + BitVec.ofNat 32 (16 * (N.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have := N.isLt
  have := P.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def, toNat_ofNat32 (by lit_omega)]; omega), toNat_ofNat32 (by lit_omega), toNat_ofNat32 (by lit_omega)]
  omega

theorem pd_ok {s₀ : State} (hp : APre s₀) {i : Nat} {s : State} (h : MC s₀ i s) :
    WP isa (.block (([.mov .esi (.reg .ebp), .alu .sub .esi (.reg .edx), .alu .add .esi (.reg .ebx),
      .mov .eax (.imm 0), .store (at_ .edi 576) .eax, .store (at_ .edi 580) .eax,
      .store (at_ .edi 584) .eax, .store (at_ .edi 588) .eax] : List Instr) ++ ptr .ecx .edi 576)) s fun s' =>
      PD s₀ i s' ∧ Frame [sub s₀ 576 16] s.mem s'.mem ∧
      ∀ j < 16, s'.mem (cx s₀ + BitVec.ofNat 64 (576 + j)) = 0 := by
  have hi := h.inv
  have o : ∀ d, d + 4 ≤ 1024 → InRegions s.wr (cx s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [hi.wr]; exact hp.in_ctx hd
  simp only [List.cons_append]
  refine wp_mov fun s₁ u₁ _ => wp_subx (readSrc_reg _ _) fun s₂ u₂ _ =>
    wp_addx (readSrc_reg _ _) fun s₃ u₃ _ => wp_movi fun s₄ u₄ _ => ?_
  have edi₄ : s₄.gpr .edi = CX s₀ := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hi.edi]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have c : ∀ d, d < 1024 → ∀ s' : State, s'.gpr .edi = CX s₀ → s'.ea (at_ .edi d) = cx s₀ + BitVec.ofNat 64 d :=
    fun d hd s' he => by rw [ea_at, he, hp.ea_ctx hd]
  refine wp_store (c 576 (by lit_omega) _ edi₄) (by rw [wr₄]; exact o 576 (by lit_omega)) fun s₅ u₅ => ?_
  refine wp_store (c 580 (by lit_omega) _ (by rw [u₅.gpr, edi₄])) (by rw [u₅.wr, wr₄]; exact o 580 (by lit_omega))
    fun s₆ u₆ => ?_
  refine wp_store (c 584 (by lit_omega) _ (by rw [u₆.gpr, u₅.gpr, edi₄]))
    (by rw [u₆.wr, u₅.wr, wr₄]; exact o 584 (by lit_omega)) fun s₇ u₇ => ?_
  refine wp_store (c 588 (by lit_omega) _ (by rw [u₇.gpr, u₆.gpr, u₅.gpr, edi₄]))
    (by rw [u₇.wr, u₆.wr, u₅.wr, wr₄]; exact o 588 (by lit_omega)) fun s₈ u₈ => ?_
  refine WP.mono (ptr_ok .ecx .edi 576 s₈) fun s₉ ⟨e₉, g₉, rd₉, wr₉, m₉⟩ => ?_
  have g8 : s₈.gpr = s₄.gpr := by rw [u₈.gpr, u₇.gpr, u₆.gpr, u₅.gpr]
  have eax₄ : s₄.gpr .eax = 0 := u₄.gpr
  have hm : s₉.mem = (((s.mem.writeW (cx s₀ + BitVec.ofNat 64 576) (0 : BitVec 32)).writeW
      (cx s₀ + BitVec.ofNat 64 580) (0 : BitVec 32)).writeW (cx s₀ + BitVec.ofNat 64 584) (0 : BitVec 32)).writeW
      (cx s₀ + BitVec.ofNat 64 588) (0 : BitVec 32) := by
    rw [m₉, u₈.mem, u₇.gpr, u₇.mem, u₆.gpr, u₆.mem, u₅.gpr, u₅.mem, eax₄, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hf : Frame [sub s₀ 576 16] s.mem s₉.mem := by
    rw [hm]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega))).writeW
      (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))).writeW
      (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))).writeW
      (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  have g9 : ∀ r, r ≠ .ecx → s₉.gpr r = s₄.gpr r := fun r hr => by rw [g₉ r hr, g8]
  refine ⟨⟨hi.part hp ⟨by rw [g9 _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hi.esp], by rw [rd₉, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd,
      u₃.rd, u₂.rd, u₁.rd, hi.rd], by rw [wr₉, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄, hi.wr]⟩
      (by rw [g9 _ (by decide), edi₄, hi.edi]) (k := 576) (n := 16) (by lit_omega) (by lit_omega) (by lit_omega)
      (hf.mono (by simp)), ?_, by rw [e₉, g8, edi₄], ?_⟩, hf, fun j hj => by rw [hm]; exact zero16 _ _ hj⟩
  · rw [g9 _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), u₁.other _ (by decide), h.ebp, h.edx, h.ebx, tail_start]
  · rw [g9 _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.edx]

/-! ## Copying the tail -/

/-- The `t` bytes at `Q` that the copy loop copies. -/
structure Tail (s₀ : State) (Q : BitVec 32) (t : Nat) : Prop where
  lt : t < 16
  fit : Q.toNat + t ≤ 2 ^ 32
  src : ∀ j < t, InRegions (s₀.rd ++ s₀.wr) (Q.setWidth 64 + BitVec.ofNat 64 j) 1
  disj : (⟨Q.setWidth 64, t⟩ : Region).Disjoint (sub s₀ 576 16)

/-- Before byte `i` of the tail is copied into the block, from the state `s₂`
in which the block was zeroed. -/
structure CpInv (s₀ s₂ : State) (Q : BitVec 32) (t i : Nat) (s : State) : Prop where
  esi : s.gpr .esi = Q + BitVec.ofNat 32 i
  ecx : s.gpr .ecx = C32 s₀ (576 + i)
  edx : s.gpr .edx = BitVec.ofNat 32 (t - i)
  keep : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ecx → r ≠ .edx → s.gpr r = s₂.gpr r
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame [sub s₀ 576 16] s₂.mem s.mem
  buf : ∀ j < 16, s.mem (cx s₀ + BitVec.ofNat 64 (576 + j)) =
    if j < i then s₂.mem (Q.setWidth 64 + BitVec.ofNat 64 j) else 0

def copyBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .store8 (at_ .ecx 0) .al, .alu .add .esi (.imm 1), .alu .add .ecx (.imm 1),
    .alu .sub .edx (.imm 1)]

theorem ctx_ne {s₀ : State} {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    cx s₀ + BitVec.ofNat 64 (576 + j) ≠ cx s₀ + BitVec.ofNat 64 (576 + k) := by
  intro he
  have e : BitVec.ofNat 64 (576 + j) = BitVec.ofNat 64 (576 + k) := by
    have := congrArg (· - cx s₀) he; simpa using this
  have := congrArg BitVec.toNat e
  rw [toNat_ofNat_lt (by lit_omega), toNat_ofNat_lt (by lit_omega)] at this
  omega

theorem copy_step {s₀ : State} (hp : APre s₀) {s₂ : State} (hr₂ : s₂.rd = s₀.rd) (hw₂ : s₂.wr = s₀.wr)
    {Q : BitVec 32} {t : Nat} (ht : Tail s₀ Q t) {i : Nat} (hi : i < t) {s : State}
    (h : CpInv s₀ s₂ Q t i s) :
    WP isa (.block copyBody) s fun s' => CpInv s₀ s₂ Q t (i + 1) s' ∧ s'.zf = some (decide (i + 1 = t)) := by
  have hlt := ht.lt
  have hf := ht.fit
  have hc := hp.fit_c
  have hQ : addr (Q + BitVec.ofNat 32 i) 0 = Q.setWidth 64 + BitVec.ofNat 64 i := by
    rw [addr_zero_add, addr_eq (by lit_omega)]
  have hO : addr (C32 s₀ (576 + i)) 0 = cx s₀ + BitVec.ofNat 64 (576 + i) := by
    rw [show C32 s₀ (576 + i) = CX s₀ + BitVec.ofNat 32 (576 + i) from rfl, addr_zero_add, hp.ea_ctx (by lit_omega)]
  refine wp_movzx8 (a := Q.setWidth 64 + BitVec.ofNat 64 i) (by rw [ea_at, h.esi, hQ])
    (by rw [h.rd, h.wr, hr₂, hw₂]; exact ht.src i hi) fun s₃ u₃ => ?_
  refine wp_store8 (a := cx s₀ + BitVec.ofNat 64 (576 + i)) (by rw [ea_at, u₃.other _ (by decide), h.ecx, hO])
    (by rw [u₃.wr, h.wr, hw₂]; exact hp.in_ctx (by lit_omega)) fun s₄ u₄ => ?_
  refine wp_addx (readSrc_imm _ _) fun s₅ u₅ _ => wp_addx (readSrc_imm _ _) fun s₆ u₆ _ =>
    wp_subx (readSrc_imm _ _) fun s₇ u₇ z₇ => WP.block_nil ?_
  -- The byte copied is byte `i` of the tail, unchanged since `s₂`.
  have hbyte : s.mem (Q.setWidth 64 + BitVec.ofNat 64 i) = s₂.mem (Q.setWidth 64 + BitVec.ofNat 64 i) :=
    h.frame.bytes (R := ⟨Q.setWidth 64, t⟩) (by simp only [List.mem_singleton, forall_eq]; exact ht.disj)
      (show t ≤ 2 ^ 64 by omega) hi
  have hmem : s₇.mem = s.mem.writeW (cx s₀ + BitVec.ofNat 64 (576 + i))
      (s₂.mem (Q.setWidth 64 + BitVec.ofNat 64 i)) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, show Reg8.al.reg = .eax from rfl, u₃.gpr, u₃.mem,
      BitVec.setWidth_setWidth_of_le _ (by lit_omega), BitVec.setWidth_eq, hbyte]
  have hedx : s.gpr .edx - 1 = BitVec.ofNat 32 (t - (i + 1)) := by
    rw [h.edx]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_ofNat32 (by lit_omega)]; simp; omega),
      toNat_ofNat32 (by lit_omega), toNat_ofNat32 (by lit_omega)]
    simp; omega
  refine ⟨⟨?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, h.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, h.wr], ?_, fun k hk => ?_⟩, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide), h.esi,
      add_ofNat_one]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), h.ecx]
    show CX s₀ + BitVec.ofNat 32 (576 + i) + 1 = CX s₀ + BitVec.ofNat 32 (576 + i + 1)
    rw [add_ofNat_one]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), hedx]
  · rw [u₇.other _ h₄, u₆.other _ h₃, u₅.other _ h₂, u₄.gpr, u₃.other _ h₁, h.keep r h₁ h₂ h₃ h₄]
  · rw [hmem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  · rw [hmem, writeW8_apply]
    by_cases hki : k = i
    · subst hki
      rw [ite_eq_left rfl, ite_eq_left (by lit_omega)]
    · rw [ite_eq_right (ctx_ne hk (by lit_omega) hki), h.buf k hk]
      rcases Nat.lt_or_ge k i with hk' | hk'
      · rw [ite_eq_left hk', ite_eq_left (by lit_omega)]
      · rw [ite_eq_right (by lit_omega), ite_eq_right (by lit_omega)]
  · rw [z₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), hedx]
    refine congrArg some ?_
    by_cases he : i + 1 = t
    · rw [decide_eq_true he, show t - (i + 1) = 0 by omega]; rfl
    · rw [decide_eq_false he]
      refine beq_eq_false_iff_ne.mpr fun h0 => ?_
      have := congrArg BitVec.toNat h0
      rw [toNat_ofNat32 (by lit_omega)] at this
      simp at this; omega

theorem copyLoop_eq : (Code.loop (.block [.movzx8 .eax (at_ .esi 0), .store8 (at_ .ecx 0) .al,
    .alu .add .esi (.imm 1), .alu .add .ecx (.imm 1), .alu .sub .edx (.imm 1)]) .ne : Prog isa) =
    .loop (.block copyBody) .ne := rfl

theorem copy_ok {s₀ : State} (hp : APre s₀) {s₂ : State} (hr₂ : s₂.rd = s₀.rd) (hw₂ : s₂.wr = s₀.wr)
    {Q : BitVec 32} {t : Nat} (ht : Tail s₀ Q t) (ht0 : 0 < t) (h₂ : CpInv s₀ s₂ Q t 0 s₂) :
    WP isa (.loop (.block copyBody) .ne) s₂ (CpInv s₀ s₂ Q t t) := by
  let Inv : Nat → State → Prop := fun n s => ∃ i, n = t - i ∧ i < t ∧ CpInv s₀ s₂ Q t i s
  have hstep : ∀ n s, Inv n s → WP isa (.block copyBody) s (fun s' =>
      (eval .ne s' = some false ∧ CpInv s₀ s₂ Q t t s') ∨ (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨i, rfl, hi, hI⟩
    refine WP.mono (copy_step hp hr₂ hw₂ ht hi hI) fun s' ⟨h', hz⟩ => ?_
    by_cases hl : i + 1 = t
    · exact .inl ⟨by simp [eval, hz, hl], hl ▸ h'⟩
    · exact .inr ⟨by simp [eval, hz, hl], t - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep t s₂ ⟨0, by simp, ht0, h₂⟩

/-- The padded block's bytes. -/
theorem padded_bytes {s₀ : State} {m mz : Mem} {Q : Addr} {t : Nat} (ht : t < 16)
    (h : ∀ j < 16, m (cx s₀ + BitVec.ofNat 64 (576 + j)) = if j < t then mz (Q + BitVec.ofNat 64 j) else 0) :
    bytesAt m (cx s₀ + BitVec.ofNat 64 576) 16 = bytesAt mz Q t ++ List.replicate (16 - t) 0 := by
  apply List.ext_getElem
  · simp [bytesAt]; omega
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [show cx s₀ + BitVec.ofNat 64 576 + BitVec.ofNat 64 k = cx s₀ + BitVec.ofNat 64 (576 + k) by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add], h k h₁]
    by_cases hk : k < t
    · rw [List.getElem_append_left (by simp [hk])]
      simp [hk]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [hk]

/-! ## The tail absorbed -/

/-- The frame of the Poly1305 state and the padded block, and the calls. -/
abbrev macR (s₀ : State) : List Region := [sub s₀ 448 144, stkR s₀]

theorem Src.tail {s₀ : State} {P : BitVec 32} {len : Nat} (hs : Src s₀ P len) :
    Tail s₀ (P + BitVec.ofNat 32 (16 * (len / 16))) (len % 16) := by
  have hf := hs.fit
  have hk : 16 * (len / 16) + len % 16 = len := Nat.div_add_mod _ _
  by_cases h0 : len % 16 = 0
  · rw [h0]
    refine ⟨by omega, by have := (P + BitVec.ofNat 32 (16 * (len / 16))).isLt; omega,
      fun j hj => absurd hj (by lit_omega), fun x hx _ => ?_⟩
    simp only [Region.Contains] at hx; omega
  have e : (P + BitVec.ofNat 32 (16 * (len / 16))).setWidth 64 =
      P.setWidth 64 + BitVec.ofNat 64 (16 * (len / 16)) := add_setWidth (by lit_omega)
  have hsub : ∀ {a n : Nat}, a + n ≤ len % 16 →
      Region.Sub ⟨(P + BitVec.ofNat 32 (16 * (len / 16))).setWidth 64 + BitVec.ofNat 64 a, n⟩
        ⟨P.setWidth 64, len⟩ := fun {a n} h => by
    rw [e, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact sub_off _ (by lit_omega)
  refine ⟨Nat.mod_lt _ (by lit_omega), by rw [add_toNat (by lit_omega)]; omega, fun j hj => ?_, ?_⟩
  · exact ⟨_, hs.mem, hsub (a := j) (n := 1) (by lit_omega) _ (Region.contains_self _ _)⟩
  · have hd := (hs.ctx.sub_left (sub_ctx s₀ (k := 576) (n := 16) (by lit_omega))).symm
    refine hd.sub_left ?_
    have := hsub (a := 0) (n := len % 16) (by lit_omega)
    simpa using this

theorem padTail_eq : padTail =
    .seq (.block (([.mov .esi (.reg .ebp), .alu .sub .esi (.reg .edx), .alu .add .esi (.reg .ebx),
      .mov .eax (.imm 0), .store (at_ .edi 576) .eax, .store (at_ .edi 580) .eax,
      .store (at_ .edi 584) .eax, .store (at_ .edi 588) .eax] : List Instr) ++ ptr .ecx .edi 576))
    (.seq (.loop (.block copyBody) .ne) (absorbOne 576)) := rfl

/-- After the copy loop. -/
theorem copied_inv {s₀ : State} (hp : APre s₀) {i : Nat} {s₂ s₃ : State} (h₂ : PD s₀ i s₂)
    {Q : BitVec 32} {t : Nat} (h₃ : CpInv s₀ s₂ Q t t s₃) : Inv s₀ s₃ :=
  h₂.inv.part hp ⟨by rw [h₃.keep _ (by decide) (by decide) (by decide) (by decide), h₂.inv.esp],
    by rw [h₃.rd, h₂.inv.rd], by rw [h₃.wr, h₂.inv.wr]⟩
    (h₃.keep _ (by decide) (by decide) (by decide) (by decide)) (k := 576) (n := 16) (by lit_omega) (by lit_omega)
    (by lit_omega) (h₃.frame.mono (by simp))

theorem cp0 {s₀ : State} {i : Nat} {s₂ : State} (h₂ : PD s₀ i s₂)
    (hz : ∀ j < 16, s₂.mem (cx s₀ + BitVec.ofNat 64 (576 + j)) = 0) :
    CpInv s₀ s₂ (arg s₀ i + BitVec.ofNat 32 (16 * ((arg s₀ (i + 1)).toNat / 16)))
      ((arg s₀ (i + 1)).toNat % 16) 0 s₂ :=
  ⟨by rw [h₂.esi]; simp, h₂.ecx, by rw [h₂.edx]; rfl, fun _ _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _,
    fun j hj => by rw [hz j hj]; simp⟩

theorem padTail_ok {s₀ : State} (hp : APre s₀) {i : Nat} (hs : Src s₀ (arg s₀ i) (arg s₀ (i + 1)).toNat)
    (h0 : (arg s₀ (i + 1)).toNat % 16 ≠ 0) {s : State} (h : MC s₀ i s) :
    WP isa padTail s fun s' => Inv s₀ s' ∧ Frame (macR s₀) s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        Repr s'.mem (cx s₀ + BitVec.ofNat 64 448) key (msg ++
          (bytesAt s.mem ((arg s₀ i + BitVec.ofNat 32 (16 * ((arg s₀ (i + 1)).toNat / 16))).setWidth 64)
            ((arg s₀ (i + 1)).toNat % 16) ++ List.replicate (16 - (arg s₀ (i + 1)).toNat % 16) 0)) := by
  have ht := hs.tail
  rw [padTail_eq]
  refine WP.seq (WP.mono (pd_ok hp h) fun s₂ ⟨h₂, f₂, z₂⟩ => ?_)
  refine WP.seq (WP.mono (copy_ok hp (by rw [h₂.inv.rd]) (by rw [h₂.inv.wr]) ht (by lit_omega) (cp0 h₂ z₂))
    fun s₃ h₃ => ?_)
  refine WP.mono (absorbOne_ok hp (copied_inv hp h₂ h₃) (k := 576) (.inr ⟨(Nat.le_refl _), by omega⟩))
    fun s₄ ⟨i₄, f₄, r₄⟩ => ⟨i₄, ?_, fun key msg hr => ?_⟩
  · refine ((f₂.trans h₃.frame).sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 448 144, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨sub s₀ 448 144, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · have f23 : Frame [sub s₀ 576 16] s.mem s₃.mem := f₂.trans h₃.frame
    have := r₄ key msg (Repr.frame f23 (by
      simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) hr)
    rwa [padded_bytes ht.lt h₃.buf, bytesAt_frame f₂ (by
      simp only [List.mem_singleton, forall_eq]; exact ht.disj) (by have := ht.lt; omega)] at this

theorem macPad_eq (p n : Nat) : macPad p n =
    .seq (.block (([.mov .ebx (.mem (at_ .esp p)), .mov .ebp (.mem (at_ .esp n)), .mov .eax (.reg .ebp),
      .shift .shr .eax 4] : List Instr) ++ ptr .ecx .edi 448))
    (.seq (callWith [.eax, .ebx, .ecx] "vg_poly1305_blocks" Impl.Poly1305.X86.blocks)
    (.seq (.block [.mov .edx (.reg .ebp), .alu .and .edx (.imm 15)])
      (.ite .e (.block []) padTail))) := rfl

/-- The bytes whose address and length are arguments `i` and `i + 1`, padded
with zeros, absorbed. -/
theorem macPad_ok {s₀ : State} (hp : APre s₀) {i : Nat} (hi : i + 1 < 5)
    (hs : Src s₀ (arg s₀ i) (arg s₀ (i + 1)).toNat) {s : State} (h : Inv s₀ s) :
    WP isa (macPad (4 + 4 * i) (8 + 4 * i)) s fun s' => Inv s₀ s' ∧ Frame (macR s₀) s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        Repr s'.mem (cx s₀ + BitVec.ofNat 64 448) key (msg ++
          (bytesAt s.mem ((arg s₀ i).setWidth 64) (arg s₀ (i + 1)).toNat ++
            pad16 (bytesAt s.mem ((arg s₀ i).setWidth 64) (arg s₀ (i + 1)).toNat))) := by
  have hf := hs.fit
  rw [macPad_eq]
  refine WP.seq (WP.mono (maA_ok hp hi h) fun s₁ ⟨h₁, m₁⟩ => ?_)
  refine WP.seq (WP.mono (maB_ok hp hs h₁) fun s₂ ⟨h₂, f₂, r₂⟩ => ?_)
  rw [m₁] at f₂ r₂
  refine WP.seq (WP.mono (maC_ok h₂) fun s₃ ⟨h₃, m₃⟩ => ?_)
  have hk : 16 * ((arg s₀ (i + 1)).toNat / 16) + (arg s₀ (i + 1)).toNat % 16 = (arg s₀ (i + 1)).toNat := Nat.div_add_mod _ _
  have fr₃ : Frame (macR s₀) s.mem s₃.mem := by
    rw [m₃]
    exact f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨sub s₀ 448 144, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  have x_eq : bytesAt s.mem ((arg s₀ i).setWidth 64) (arg s₀ (i + 1)).toNat = bytesAt s.mem ((arg s₀ i).setWidth 64) (16 * ((arg s₀ (i + 1)).toNat / 16)) ++
      bytesAt s.mem ((arg s₀ i).setWidth 64 + BitVec.ofNat 64 (16 * ((arg s₀ (i + 1)).toNat / 16))) ((arg s₀ (i + 1)).toNat % 16) := by
    rw [← VG.Proof.Poly1305.bytesAt_add, hk]
  have hlenX : (bytesAt s.mem ((arg s₀ i).setWidth 64) (arg s₀ (i + 1)).toNat).length = (arg s₀ (i + 1)).toNat := VG.Proof.Poly1305.length_bytesAt _ _ _
  refine WP.ite (decide ((arg s₀ (i + 1)).toNat % 16 = 0)) (by simp only [eval, h₃.zf]) (fun hz => ?_) (fun hz => ?_)
  · have h0 : (arg s₀ (i + 1)).toNat % 16 = 0 := by simpa using hz
    refine WP.block_nil ⟨h₃.inv, fr₃, fun key msg hr => ?_⟩
    rw [m₃]
    have := r₂ key msg hr
    rwa [show pad16 (bytesAt s.mem ((arg s₀ i).setWidth 64) (arg s₀ (i + 1)).toNat) = [] by simp [pad16, hlenX, h0],
      List.append_nil, ← show 16 * ((arg s₀ (i + 1)).toNat / 16) = (arg s₀ (i + 1)).toNat by omega]
  · have h0 : (arg s₀ (i + 1)).toNat % 16 ≠ 0 := by simpa using hz
    refine WP.mono (padTail_ok hp (i := i) hs h0 h₃) fun s₄ ⟨i₄, f₄, r₄⟩ => ⟨i₄, fr₃.trans f₄, fun key msg hr => ?_⟩
    have := r₄ key _ (by rw [m₃]; exact r₂ key msg hr)
    have e : (arg s₀ i + BitVec.ofNat 32 (16 * ((arg s₀ (i + 1)).toNat / 16))).setWidth 64 =
        (arg s₀ i).setWidth 64 + BitVec.ofNat 64 (16 * ((arg s₀ (i + 1)).toNat / 16)) := add_setWidth (by lit_omega)
    rw [e, m₃, bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((hs.ctx.sub_left (sub_ctx s₀ (k := 448) (n := 128) (by lit_omega))).symm).sub_left
          (sub_off _ (by lit_omega))
      · exact (hs.stk.symm).sub_left (sub_off _ (by lit_omega))) (by lit_omega)] at this
    rw [show pad16 (bytesAt s.mem ((arg s₀ i).setWidth 64) (arg s₀ (i + 1)).toNat) = List.replicate (16 - (arg s₀ (i + 1)).toNat % 16) 0 by
      simp [pad16, hlenX, h0], x_eq]
    simpa only [List.append_assoc] using this

end VG.Proof.ChaCha20Poly1305.X86

section

/-!
# ChaCha20-Poly1305 on x86 (32-bit): the prologue

Saving the registers, the ChaCha20 state for counter 0, the one-time key and
the Poly1305 state for it. Each stage is stated separately (`Pro1`, …), for
the constant-time proof.
-/

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86
open VG.Impl.ChaCha20.X86 (at_)
open VG.Proof.ChaCha20.X86 (contains_off toNat_ofNat_lt readW_writeW_off)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-! ## Loading the context and saving the registers -/

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block [.mov .eax (.mem (at_ .esp 4))]) s₀ fun s => s = s₀.setReg .eax (CX s₀) := by
  have i₀ : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 4 :=
    hp.in_arg (i := 0) (by lit_omega)
  have v₀ : s₀.mem.readW ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 32 = CX s₀ := rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea, at_, State.load32,
    i₀, v₀, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']

/-- The memory after the registers are saved. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (cx s₀ + BitVec.ofNat 64 ·) s₀.gpr saved

theorem saveMem_frame (s₀ : State) : Frame [sub s₀ 592 16] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ (saved_contains s₀)

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) :=
  Spill.saveMem_saved_ofNat _ _ _ (by decide : Spill.Fits 608 saved) (by decide)

theorem save_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block (save ++ ([.mov .edi (.reg .eax)] : List Instr))) (s₀.setReg .eax (CX s₀)) fun s =>
      s.gpr .edi = CX s₀ ∧ (∀ r, r ≠ .eax → r ≠ .edi → s.gpr r = s₀.gpr r) ∧ s.mem = saveMem s₀ ∧
      s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have e : ∀ p ∈ saved, addr (CX s₀) p.2 = cx s₀ + BitVec.ofNat 64 p.2 :=
    fun p h => hp.ea_ctx (by have := saved_bound p h; lit_omega)
  have geax : (s₀.setReg .eax (CX s₀)).gpr .eax = CX s₀ := RegUpd.gpr_setReg_self _ _ _
  refine Spill.save_ok saved (fun p h => by
      rw [geax, e p h]; exact hp.in_ctx (by have := saved_bound p h; lit_omega))
    fun s₁ u => Wp.wp_mov fun s₂ u₂ => WP.block_nil ⟨by rw [u₂.gpr, u.gpr, geax], fun r h₁ h₂ => ?_,
      ?_, by rw [u₂.rd, u.rd]; rfl, by rw [u₂.wr, u.wr]; rfl⟩
  · rw [u₂.other _ h₂, u.gpr]; exact RegUpd.gpr_setReg_of_ne _ _ h₁
  · rw [u₂.mem, u.mem, geax]
    exact Spill.saveMem_congr _ _ e fun p h => RegUpd.gpr_setReg_of_ne _ _ (by revert p h; decide)

/-! ## The ChaCha20 state -/

/-- The word `stW k` stores, from memory `m` and the context `c`. -/
def wordOf (m : Mem) (c : Addr) (k : Nat) : BitVec 32 :=
  if k < 4 then [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574].getD k 0
  else if k < 12 then m.readW (c + BitVec.ofNat 64 (4 * (k - 4))) 32
  else if k = 12 then 0
  else m.readW (c + BitVec.ofNat 64 (32 + 4 * (k - 13))) 32

set_option simprocs false in
theorem stW_ok {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < 16) {s : State}
    (hedi : s.gpr .edi = CX s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block (stW k)) s fun s' =>
      s'.mem = s.mem.writeW (cx s₀ + BitVec.ofNat 64 (64 + 4 * k)) (wordOf s.mem (cx s₀) k) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o := hp.in_ctx (a := 64 + 4 * k) (w := 4) (by lit_omega)
  have eo := hp.c64 (k := 64 + 4 * k) (by lit_omega)
  rw [← hwr] at o
  unfold stW stSrc wordOf
  split_ifs with h₁ h₂ h₃
  · apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, State.ea,
      at_, readSrc, State.store32, State.setReg, hedi, eo, o, ite_true, ite_false, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  · have i := hp.in_ctx' (a := 4 * (k - 4)) (w := 4) (by lit_omega)
    have ei := hp.c64 (k := 4 * (k - 4)) (by lit_omega)
    rw [← hrd, ← hwr] at i
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, State.ea,
      at_, readSrc, State.load32, State.store32, State.setReg, hedi, eo, ei, o, i, ite_true, ite_false,
      Option.map_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  · apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, State.ea,
      at_, readSrc, State.store32, State.setReg, hedi, eo, o, ite_true, ite_false, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  · have i := hp.in_ctx' (a := 32 + 4 * (k - 13)) (w := 4) (by lit_omega)
    have ei := hp.c64 (k := 32 + 4 * (k - 13)) (by lit_omega)
    rw [← hrd, ← hwr] at i
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, State.ea,
      at_, readSrc, State.load32, State.store32, State.setReg, hedi, eo, ei, o, i, ite_true, ite_false,
      Option.map_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

/-- The context's words `[a, a + 4)` outside `[64, 64 + n)`. -/
theorem readW_frame_ctx {c : Addr} {m m' : Mem} {n : Nat} (hf : Frame [⟨c + BitVec.ofNat 64 64, n⟩] m m')
    {a : Nat} (ha : a + 4 ≤ 64) (hn : n ≤ 960) :
    m'.readW (c + BitVec.ofNat 64 a) 32 = m.readW (c + BitVec.ofNat 64 a) 32 := by
  refine hf.readW (r := ⟨c + BitVec.ofNat 64 a, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  exact Offset.disjoint c (.inl ha) (by lit_omega) (by lit_omega)

theorem wordOf_frame {c : Addr} {m m' : Mem} {n : Nat} (hf : Frame [⟨c + BitVec.ofNat 64 64, n⟩] m m')
    (hn : n ≤ 960) {k : Nat} (hk : k < 16) : wordOf m' c k = wordOf m c k := by
  unfold wordOf
  split_ifs
  · rfl
  · exact readW_frame_ctx hf (by lit_omega) hn
  · rfl
  · exact readW_frame_ctx hf (by lit_omega) hn

theorem initState_step (j : Nat) : (List.range (j + 1)).flatMap stW = (List.range j).flatMap stW ++ stW j := by
  simp [List.range_succ, List.flatMap_append]

/-- The first `j` words of the ChaCha20 state. -/
theorem initState_ok {s₀ : State} (hp : APre s₀) {j : Nat} (hj : j ≤ 16) {s : State}
    (hedi : s.gpr .edi = CX s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block ((List.range j).flatMap stW)) s fun s' =>
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨cx s₀ + BitVec.ofNat 64 64, 4 * j⟩] s.mem s'.mem ∧
      ∀ i < j, s'.mem.readW (cx s₀ + BitVec.ofNat 64 (64 + 4 * i)) 32 = wordOf s.mem (cx s₀) i := by
  induction j with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by lit_omega)⟩
  | succ j ih =>
    rw [initState_step]
    refine WP.block_append (WP.mono (ih (by lit_omega)) fun s₁ ⟨g₁, rd₁, wr₁, f₁, w₁⟩ => ?_)
    refine WP.mono (stW_ok hp (k := j) (by lit_omega) (by rw [g₁ _ (by decide), hedi]) (by rw [rd₁, hrd])
      (by rw [wr₁, hwr])) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
    refine ⟨fun r hr => by rw [g₂ r hr, g₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_, fun i hi => ?_⟩
    · rw [m₂]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by lit_omega)
      · exact Offset.contains (cx s₀) (by lit_omega) (by lit_omega) (by lit_omega)
    · rw [m₂, wordOf_frame f₁ (by lit_omega) (by lit_omega)]
      by_cases h : i = j
      · subst h; exact Mem.readW_writeW_self32 _ _ _
      · rw [readW_writeW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega)]
        exact w₁ i (by lit_omega)

theorem consts_eq : ∀ i < 4, ([0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] : List (BitVec 32)).getD i 0 =
    Spec.ChaCha20.constants.getD i 0 := by decide

/-- The words stored are the initial ChaCha20 state for the key, counter 0
and the nonce. -/
theorem stateAt_initState {s₀ : State} {m₁ m' : Mem} (hf₁ : Frame [sub s₀ 592 16] s₀.mem m₁)
    (hw : ∀ i < 16, m'.readW (cx s₀ + BitVec.ofNat 64 (64 + 4 * i)) 32 = wordOf m₁ (cx s₀) i) :
    stateAt m' (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
  have r₁ : ∀ a, a + 4 ≤ 44 → m₁.readW (cx s₀ + BitVec.ofNat 64 a) 32 =
      s₀.mem.readW (cx s₀ + BitVec.ofNat 64 a) 32 := by
    intro a ha
    refine hf₁.readW (r := sub s₀ a 4) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  apply Vector.ext
  intro i hi
  simp only [stateAt, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  rw [show cx s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * i) = cx s₀ + BitVec.ofNat 64 (64 + 4 * i) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add], hw i hi]
  unfold wordOf
  split_ifs with h₁ h₂ h₃
  · exact consts_eq i h₁
  · rw [r₁ _ (by lit_omega), show (K s₀) = Spec.ChaCha20.bytesAt s₀.mem (cx s₀) 32 from rfl,
      wordLE_bytesAt s₀.mem (cx s₀) (n := 32) (j := i - 4) (by lit_omega)]
  · rfl
  · rw [r₁ _ (by lit_omega)]
    rw [show (N s₀) = Spec.ChaCha20.bytesAt s₀.mem (cx s₀ + 32) 12 from rfl,
      wordLE_bytesAt s₀.mem (cx s₀ + 32) (n := 12) (j := i - 13) (by lit_omega)]
    congr 1
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl

/-- The first `n ≤ 64` bytes of a ChaCha20 state in memory. -/
theorem bytesAt_serialize (m : Mem) (p : Addr) {n : Nat} (hn : n ≤ 64) :
    bytesAt m p n = (Spec.ChaCha20.serialize (stateAt m p)).take n := by
  apply List.ext_getElem
  · simp [bytesAt, VG.Proof.ChaCha20.length_serialize]; omega
  · intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    have e := VG.Proof.ChaCha20.serialize_stateAt m p (i := i) (by lit_omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_serialize]; omega), Option.getD_some] at e
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, e]

/-! ## The stages -/

/-- After the registers are saved and the ChaCha20 state stored: ready to
call the block function. -/
structure Pro2 (s₀ s : State) : Prop where
  at_ : At s₀ s
  edi : s.gpr .edi = CX s₀
  ecx : s.gpr .ecx = C32 s₀ 64
  edx : s.gpr .edx = C32 s₀ 128
  saved : Saved s₀ s.mem
  frame : Frame [sub s₀ 64 64, sub s₀ 592 16] s₀.mem s.mem
  st : stateAt s.mem (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)

/-- After the block function: the one-time key at `ctx + 128`. -/
structure Pro3 (s₀ s : State) : Prop where
  at_ : At s₀ s
  edi : s.gpr .edi = CX s₀
  saved : Saved s₀ s.mem
  frame : Frame [workR s₀, stkR s₀] s₀.mem s.mem
  st : stateAt s.mem (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  key : bytesAt s.mem (cx s₀ + BitVec.ofNat 64 128) 32 = otk s₀

/-- Ready to call `vg_poly1305_init`. -/
structure Pro4 (s₀ s : State) : Prop extends Pro3 s₀ s where
  ecx : s.gpr .ecx = C32 s₀ 128
  edx : s.gpr .edx = C32 s₀ 448

/-- After the prologue. -/
structure PostP (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  fine : Frame [workR s₀, stkR s₀] s₀.mem s.mem
  poly : Repr s.mem (cx s₀ + BitVec.ofNat 64 448) (otk s₀) []
  st : stateAt s.mem (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)

theorem B2_eq : save ++ ([.mov .edi (.reg .eax)] : List Instr) ++ initState ++ ptr .ecx .edi 64 ++ ptr .edx .edi 128 =
    (save ++ ([.mov .edi (.reg .eax)] : List Instr)) ++ (initState ++ (ptr .ecx .edi 64 ++ ptr .edx .edi 128)) := by
  simp only [List.append_assoc]

theorem pro2_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block (save ++ ([.mov .edi (.reg .eax)] : List Instr) ++ initState ++ ptr .ecx .edi 64 ++ ptr .edx .edi 128))
      (s₀.setReg .eax (CX s₀)) (Pro2 s₀) := by
  rw [B2_eq]
  refine WP.block_append (WP.mono (save_ok hp) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.block_append (WP.mono (initState_ok hp (j := 16) (Nat.le_refl _) e₁ rd₁ wr₁)
    fun s₂ ⟨g₂, rd₂, wr₂, f₂, w₂⟩ => ?_)
  refine WP.block_append (WP.mono (ptr_ok .ecx .edi 64 s₂) fun s₃ ⟨e₃, g₃, rd₃, wr₃, m₃⟩ => ?_)
  refine WP.mono (ptr_ok .edx .edi 128 s₃) fun s₄ ⟨e₄, g₄, rd₄, wr₄, m₄⟩ => ?_
  have edi₂ : s₂.gpr .edi = CX s₀ := by rw [g₂ _ (by decide), e₁]
  have hsp : s₄.gpr .esp = E s₀ := by
    rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide) (by decide)]
  refine ⟨⟨hsp, by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩,
    by rw [g₄ _ (by decide), g₃ _ (by decide), edi₂], by rw [g₄ _ (by decide), e₃, edi₂],
    by rw [e₄, g₃ _ (by decide), edi₂], ?_, ?_, ?_⟩
  · rw [m₄, m₃]
    exact (m₁ ▸ saveMem_saved s₀).frame f₂ (by
      simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  · rw [m₄, m₃]
    exact ((m₁ ▸ saveMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  · rw [m₄, m₃]
    exact stateAt_initState (m₁ ▸ saveMem_frame s₀) w₂

theorem pro3_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Pro2 s₀ s) :
    WP isa (callWith [.edx, .ecx] "vg_chacha20_block" Impl.ChaCha20.X86.block) s (Pro3 s₀) := by
  refine block_call hp h.at_ h.ecx h.edx fun s' at' cs' f' blk' => ?_
  have hd : ∀ {k n : Nat}, k + n ≤ 1024 → (k + n ≤ 128 ∨ 128 + 256 ≤ k) →
      ∀ r ∈ [sub s₀ 128 256, stkR s₀], (sub s₀ k n).Disjoint r := by
    intro k n h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact (hp.stk_sub h₁).symm
  have st' : stateAt s'.mem (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [VG.Proof.ChaCha20.X86.Xor.stateAt_frame f' (hd (k := 64) (n := 64) (by lit_omega) (by lit_omega)), h.st]
  refine ⟨at', by rw [cs' _ (by simp [calleeSaved]), h.edi],
    h.saved.frame f' (hd (by lit_omega) (by lit_omega)), ?_, st', ?_⟩
  · refine (h.frame.sub fun r hr => ?_).trans (f'.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨workR s₀, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · rw [bytesAt_serialize _ _ (by lit_omega), blk', h.st]; rfl

theorem pro4_ok {s₀ : State} {s : State} (h : Pro3 s₀ s) :
    WP isa (.block (ptr .ecx .edi 128 ++ ptr .edx .edi 448)) s (Pro4 s₀) := by
  refine WP.block_append (WP.mono (ptr_ok .ecx .edi 128 s) fun s₁ ⟨e₁, g₁, rd₁, wr₁, m₁⟩ => ?_)
  refine WP.mono (ptr_ok .edx .edi 448 s₁) fun s₂ ⟨e₂, g₂, rd₂, wr₂, m₂⟩ => ?_
  have edi₁ : s₁.gpr .edi = CX s₀ := by rw [g₁ _ (by decide), h.edi]
  have mm : s₂.mem = s.mem := by rw [m₂, m₁]
  exact ⟨⟨⟨by rw [g₂ _ (by decide), g₁ _ (by decide), h.at_.esp], by rw [rd₂, rd₁, h.at_.rd],
    by rw [wr₂, wr₁, h.at_.wr]⟩, by rw [g₂ _ (by decide), edi₁], by rw [mm]; exact h.saved,
    by rw [mm]; exact h.frame, by rw [mm]; exact h.st, by rw [mm]; exact h.key⟩,
    by rw [g₂ _ (by decide), e₁, h.edi], by rw [e₂, edi₁]⟩

theorem post_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Pro4 s₀ s) :
    WP isa (callWith [.ecx, .edx] "vg_poly1305_init" Impl.Poly1305.X86.init) s (PostP s₀) := by
  refine init_call hp h.at_ h.ecx h.edx fun s' at' cs' f' repr' => ?_
  have hd : ∀ {k n : Nat}, k + n ≤ 1024 → (k + n ≤ 448 ∨ 448 + 128 ≤ k) →
      ∀ r ∈ [sub s₀ 448 128, stkR s₀], (sub s₀ k n).Disjoint r := by
    intro k n h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact (hp.stk_sub h₁).symm
  have fine : Frame [workR s₀, stkR s₀] s₀.mem s'.mem :=
    h.frame.trans (f'.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  refine ⟨⟨by rw [cs' _ (by simp [calleeSaved]), h.edi], at'.esp, at'.rd, at'.wr,
    h.saved.frame f' (hd (by lit_omega) (by lit_omega)), fine.sub fun r hr => ?_⟩, fine, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · rwa [h.key] at repr'
  · rw [VG.Proof.ChaCha20.X86.Xor.stateAt_frame f' (hd (k := 64) (n := 64) (by lit_omega) (by lit_omega)), h.st]

theorem prologue_eq : prologue =
    .seq (.block [.mov .eax (.mem (at_ .esp 4))])
    (.seq (.block (save ++ ([.mov .edi (.reg .eax)] : List Instr) ++ initState ++ ptr .ecx .edi 64 ++ ptr .edx .edi 128))
    (.seq (callWith [.edx, .ecx] "vg_chacha20_block" Impl.ChaCha20.X86.block)
    (.seq (.block (ptr .ecx .edi 128 ++ ptr .edx .edi 448))
      (callWith [.ecx, .edx] "vg_poly1305_init" Impl.Poly1305.X86.init)))) := rfl

theorem prologue_ok {s₀ : State} (hp : APre s₀) : WP isa prologue s₀ (PostP s₀) := by
  rw [prologue_eq]
  refine WP.seq (WP.mono (load_ok hp) fun s₁ e₁ => ?_)
  subst e₁
  exact WP.seq (WP.mono (pro2_ok hp) fun s₂ h₂ => WP.seq (WP.mono (pro3_ok hp h₂) fun s₃ h₃ =>
    WP.seq (WP.mono (pro4_ok h₃) fun s₄ h₄ => post_ok hp h₄)))

end VG.Proof.ChaCha20Poly1305.X86

end

/-!
# ChaCha20-Poly1305 on x86 (32-bit): the other parts

The lengths block, the encryption, the tag, comparing tags, and restoring the
registers.
-/

open VG.PowLit

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86
open VG.Impl.ChaCha20.X86 (at_)
open VG.Proof.ChaCha20.X86 (contains_off toNat_ofNat_lt readW_writeW_off)
open VG.Proof.Poly1305.X86 (wp_movm wp_store wp_movi wp_mov Upd Mupd leNum_bytesAt_4)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream)

/-! ## The lengths block -/

theorem bytesAt_word (m : Mem) (p : Addr) : bytesAt m p 4 = leBytes 4 (m.readW p 32).toNat := by
  rw [VG.Proof.Poly1305.bytesAt_leBytes]; simp [Mem.readW]

/-- Eight bytes, a word and a zero word. -/
theorem bytesAt_len (m : Mem) (p : Addr) (h : m.readW (p + BitVec.ofNat 64 4) 32 = 0) :
    bytesAt m p 8 = leBytes 8 (m.readW p 32).toNat := by
  rw [show (8 : Nat) = 4 + 4 from rfl, VG.Proof.Poly1305.bytesAt_add, bytesAt_word, bytesAt_word, h,
    VG.Proof.Poly1305.leBytes_add, Nat.div_eq_of_lt (by have := (m.readW p 32).isLt; omega)]
  rfl

theorem lengths_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block lengths) s fun s' => Inv s₀ s' ∧ Frame [sub s₀ 656 16] s.mem s'.mem ∧
      bytesAt s'.mem (cx s₀ + BitVec.ofNat 64 656) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
  have o : ∀ d, d + 4 ≤ 1024 → InRegions s.wr (cx s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.wr]; exact hp.in_ctx hd
  have c : ∀ d, d < 1024 → ∀ s' : State, s'.gpr .edi = CX s₀ → s'.ea (at_ .edi d) = cx s₀ + BitVec.ofNat 64 d :=
    fun d hd s' he => by rw [ea_at, he, hp.ea_ctx hd]
  have i₂ : InRegions (s.rd ++ s.wr) (argAddr s₀ 2) 4 := by rw [h.rd, h.wr]; exact hp.in_arg (by lit_omega)
  have i₄ : InRegions (s.rd ++ s.wr) (argAddr s₀ 4) 4 := by rw [h.rd, h.wr]; exact hp.in_arg (by lit_omega)
  refine wp_movm (a := argAddr s₀ 2) (by rw [ea_at, h.esp]; rfl) i₂ fun s₁ u₁ _ => ?_
  refine wp_store (c 656 (by lit_omega) _ (by rw [u₁.other _ (by decide), h.edi]))
    (by rw [u₁.wr]; exact o 656 (by lit_omega)) fun s₂ u₂ => ?_
  refine wp_movm (a := argAddr s₀ 4) (by rw [ea_at, u₂.gpr, u₁.other _ (by decide), h.esp]; rfl)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i₄) fun s₃ u₃ _ => ?_
  refine wp_store (c 664 (by lit_omega) _ (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.edi]))
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact o 664 (by lit_omega)) fun s₄ u₄ => ?_
  refine wp_movi fun s₅ u₅ _ => ?_
  have edi₅ : s₅.gpr .edi = CX s₀ := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.edi]
  refine wp_store (c 660 (by lit_omega) _ edi₅) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact o 660 (by lit_omega))
    fun s₆ u₆ => ?_
  refine wp_store (c 668 (by lit_omega) _ (by rw [u₆.gpr, edi₅]))
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact o 668 (by lit_omega)) fun s₇ u₇ => WP.block_nil ?_
  have v₁ : s₁.gpr .eax = ALN s₀ := by rw [u₁.gpr]; exact h.arg hp (by lit_omega)
  have v₃ : s₃.gpr .eax = LN s₀ := by
    rw [u₃.gpr, u₂.mem, u₁.mem, Mem.readW_writeW_sep ((hp.g_sub (k := 656) (n := 4) (by lit_omega)).sep
      (hp.arg_contains (by lit_omega)) (Region.contains_self _ _)) (by decide)]
    exact h.arg hp (by lit_omega)
  have hm : s₇.mem = (((s.mem.writeW (cx s₀ + BitVec.ofNat 64 656) (ALN s₀)).writeW (cx s₀ + BitVec.ofNat 64 664)
      (LN s₀)).writeW (cx s₀ + BitVec.ofNat 64 660) (0 : BitVec 32)).writeW (cx s₀ + BitVec.ofNat 64 668)
      (0 : BitVec 32) := by
    rw [u₇.mem, u₆.gpr, u₆.mem, u₅.gpr, u₅.mem, u₄.mem, v₃, u₃.mem, u₂.mem, v₁, u₁.mem]
  have hf : Frame [sub s₀ 656 16] s.mem s₇.mem := by
    rw [hm]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega))).writeW
      (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))).writeW
      (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))).writeW
      (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  refine ⟨h.part hp ⟨by rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), h.esp], by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
      by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]⟩ (by rw [u₇.gpr, u₆.gpr, edi₅, h.edi])
      (k := 656) (n := 16) (by lit_omega) (by lit_omega) (by lit_omega) (hf.mono (by simp)), hf, ?_⟩
  have e : ∀ a b : Nat, cx s₀ + BitVec.ofNat 64 a + BitVec.ofNat 64 b = cx s₀ + BitVec.ofNat 64 (a + b) :=
    fun a b => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [show (16 : Nat) = 8 + 8 from rfl, VG.Proof.Poly1305.bytesAt_add, e, bytesAt_len _ _ (by rw [e, hm]; simp
    [readW_writeW_off _ _ _ (show 656 + 4 < 2 ^ 32 by omega) (show 668 < 2 ^ 32 by omega) (by lit_omega),
      Mem.readW_writeW_self32]), bytesAt_len _ _ (by rw [e, hm]; simp
    [Mem.readW_writeW_self32])]
  rw [hm, readW_writeW_off _ _ _ (show 656 + 8 < 2 ^ 32 by omega) (show 668 < 2 ^ 32 by omega) (by lit_omega),
    readW_writeW_off _ _ _ (show 656 + 8 < 2 ^ 32 by omega) (show 660 < 2 ^ 32 by omega) (by lit_omega),
    Mem.readW_writeW_self32, readW_writeW_off _ _ _ (show 656 < 2 ^ 32 by omega) (show 668 < 2 ^ 32 by omega) (by lit_omega),
    readW_writeW_off _ _ _ (show 656 < 2 ^ 32 by omega) (show 660 < 2 ^ 32 by omega) (by lit_omega),
    readW_writeW_off _ _ _ (show 656 < 2 ^ 32 by omega) (show 664 < 2 ^ 32 by omega) (by lit_omega),
    Mem.readW_writeW_self32]

/-! ## Encrypting -/

theorem set12_initState (key nonce : List Byte) :
    (Spec.ChaCha20.initState key 0 nonce).set 12 1 = Spec.ChaCha20.initState key 1 nonce := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_set, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  by_cases h : 12 = i
  · subst h; simp
  · simp only [h, ite_false, show ¬ i = 12 from fun h' => h h'.symm]

/-- Setting the block counter in memory. -/
theorem stateAt_ctr (m : Mem) (c : Addr) :
    stateAt (m.writeW (c + BitVec.ofNat 64 112) (1 : BitVec 32)) (c + BitVec.ofNat 64 64) =
      (stateAt m (c + BitVec.ofNat 64 64)).set 12 1 := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_set, Vector.getElem_ofFn]
  rw [show c + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * i) = c + BitVec.ofNat 64 (64 + 4 * i) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
  by_cases h : 12 = i
  · subst h; simp only [ite_true]; exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact readW_writeW_off m c 1 (by lit_omega) (by lit_omega) (by lit_omega)

/-- Ready to call `vg_chacha20_xor`. -/
structure CrA (s₀ s : State) : Prop where
  inv : Inv s₀ s
  eax : s.gpr .eax = C32 s₀ 64
  ecx : s.gpr .ecx = DP s₀
  edx : s.gpr .edx = LN s₀
  esi : s.gpr .esi = C32 s₀ 128

theorem crA_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block (([.mov .eax (.imm 1), .store (at_ .edi 112) .eax] : List Instr) ++ ptr .eax .edi 64 ++
      ([.mov .ecx (.mem (at_ .esp 16)), .mov .edx (.mem (at_ .esp 20))] : List Instr) ++ ptr .esi .edi 128)) s fun s' =>
      CrA s₀ s' ∧ s'.mem = s.mem.writeW (cx s₀ + BitVec.ofNat 64 112) (1 : BitVec 32) := by
  rw [show ([.mov .eax (.imm 1), .store (at_ .edi 112) .eax] ++ ptr .eax .edi 64 ++
      [.mov .ecx (.mem (at_ .esp 16)), .mov .edx (.mem (at_ .esp 20))] ++ ptr .esi .edi 128 : List Instr) =
    .mov .eax (.imm 1) :: .store (at_ .edi 112) .eax :: (ptr .eax .edi 64 ++
      (.mov .ecx (.mem (at_ .esp 16)) :: .mov .edx (.mem (at_ .esp 20)) :: ptr .esi .edi 128)) from rfl]
  refine wp_movi fun s₁ u₁ _ => ?_
  refine wp_store (a := cx s₀ + BitVec.ofNat 64 112) (by rw [ea_at, u₁.other _ (by decide), h.edi,
    hp.ea_ctx (by lit_omega)]) (by rw [u₁.wr, h.wr]; exact hp.in_ctx (by lit_omega)) fun s₂ u₂ => ?_
  have hm₂ : s₂.mem = s.mem.writeW (cx s₀ + BitVec.ofNat 64 112) (1 : BitVec 32) := by
    rw [u₂.mem, u₁.gpr, u₁.mem]
  have edi₂ : s₂.gpr .edi = CX s₀ := by rw [u₂.gpr, u₁.other _ (by decide), h.edi]
  have hf₂ : Frame [sub s₀ 112 4, stkR s₀] s.mem s₂.mem := by
    rw [hm₂]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (contains_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega))
  have inv₂ : Inv s₀ s₂ := h.part hp ⟨by rw [u₂.gpr, u₁.other _ (by decide), h.esp],
    by rw [u₂.rd, u₁.rd, h.rd], by rw [u₂.wr, u₁.wr, h.wr]⟩ (by rw [edi₂, h.edi]) (by lit_omega) (by lit_omega)
    (by lit_omega) hf₂
  refine WP.block_append (WP.mono (ptr_ok .eax .edi 64 s₂) fun s₃ ⟨e₃, g₃, rd₃, wr₃, m₃⟩ => ?_)
  have esp₃ : s₃.gpr .esp = E s₀ := by rw [g₃ _ (by decide), inv₂.esp]
  have in₃ : ∀ i, i < 5 → InRegions (s₃.rd ++ s₃.wr) (argAddr s₀ i) 4 := fun i hi => by
    rw [rd₃, wr₃, inv₂.rd, inv₂.wr]; exact hp.in_arg hi
  refine wp_movm (a := argAddr s₀ 3) (by rw [ea_at, esp₃]; rfl) (in₃ 3 (by lit_omega)) fun s₄ u₄ _ => ?_
  refine wp_movm (a := argAddr s₀ 4) (by rw [ea_at, u₄.other _ (by decide), esp₃]; rfl)
    (by rw [u₄.rd, u₄.wr]; exact in₃ 4 (by lit_omega)) fun s₅ u₅ _ => ?_
  refine WP.mono (ptr_ok .esi .edi 128 s₅) fun s₆ ⟨e₆, g₆, rd₆, wr₆, m₆⟩ => ?_
  have edi₅ : s₅.gpr .edi = CX s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), edi₂]
  have mm : s₆.mem = s₂.mem := by rw [m₆, u₅.mem, u₄.mem, m₃]
  refine ⟨⟨inv₂.step (by rw [g₆ _ (by decide), edi₅, edi₂])
    (by rw [g₆ _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide)])
    (by rw [rd₆, u₅.rd, u₄.rd, rd₃]) (by rw [wr₆, u₅.wr, u₄.wr, wr₃]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp) (by simp), ?_, ?_, ?_, by rw [e₆, edi₅]⟩, by rw [mm, hm₂]⟩
  · rw [g₆ _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), e₃, edi₂]
  · rw [g₆ _ (by decide), u₅.other _ (by decide), u₄.gpr, m₃]; exact inv₂.arg hp (by lit_omega)
  · rw [g₆ _ (by decide), u₅.gpr, u₄.mem, m₃]; exact inv₂.arg hp (by lit_omega)

theorem crypt_eq : crypt =
    .seq (.block (([.mov .eax (.imm 1), .store (at_ .edi 112) .eax] : List Instr) ++ ptr .eax .edi 64 ++
      ([.mov .ecx (.mem (at_ .esp 16)), .mov .edx (.mem (at_ .esp 20))] : List Instr) ++ ptr .esi .edi 128))
    (callWith [.esi, .edx, .ecx, .eax] "vg_chacha20_xor" Impl.ChaCha20.X86.Xor.xor) := rfl

theorem crB_ok {s₀ : State} (hp : APre s₀) {s : State} (h : CrA s₀ s) :
    WP isa (callWith [.esi, .edx, .ecx, .eax] "vg_chacha20_xor" Impl.ChaCha20.X86.Xor.xor) s fun s' =>
      Inv s₀ s' ∧ Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s'.mem ∧
      Spec.ChaCha20.bytesAt s'.mem (dp s₀) (L s₀) =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem (dp s₀) (L s₀))
          (keystream (stateAt s.mem (cx s₀ + BitVec.ofNat 64 64)) (L s₀)) :=
  xor_call hp h.inv.at h.eax h.ecx h.edx h.esi fun s' at' cs' f' x' =>
    ⟨h.inv.step (cs' .edi (by simp [calleeSaved])) (by rw [at'.esp, h.inv.esp]) (by rw [at'.rd, h.inv.rd])
      (by rw [at'.wr, h.inv.wr]) f'
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact work_sub s₀ (by lit_omega) (by lit_omega)
        · exact ⟨dR s₀, by simp, fun _ h => h⟩
        · exact stk_work s₀)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
        · exact (hp.d_sub (by lit_omega)).symm
        · exact (hp.stk_sub (by lit_omega)).symm), f', x'⟩

theorem length_encrypt (key nonce m : List Byte) : (Spec.ChaCha20.encrypt key 1 nonce m).length = m.length := by
  rw [encrypt_eq, List.length_zipWith, VG.Proof.ChaCha20.length_keystream, Nat.min_self]

/-- The data encrypted (or decrypted) from block counter 1. -/
theorem crypt_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa crypt s fun s' => Inv s₀ s' ∧ Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s'.mem ∧
      (stateAt s.mem (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) →
        bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀))) := by
  rw [crypt_eq]
  refine WP.seq (WP.mono (crA_ok hp h) fun s₁ ⟨h₁, m₁⟩ => ?_)
  refine WP.mono (crB_ok hp h₁) fun s₂ ⟨i₂, f₂, x₂⟩ => ⟨i₂, ?_, fun hst => ?_⟩
  · refine (?_ : Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s₁.mem).trans f₂
    rw [m₁]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  · have d₁ : bytesAt s₁.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) := by
      rw [m₁]
      exact bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self (sub s₀ 112 4)) _
        (contains_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega))) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hp.d_sub (by lit_omega))
        (Nat.le_of_lt (Nat.lt_trans (LN s₀).isLt (by decide)))
    have st₁ : stateAt s₁.mem (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 1 (N s₀) := by
      rw [m₁, stateAt_ctr, hst, set12_initState]
    rw [show bytesAt = Spec.ChaCha20.bytesAt from rfl, x₂, st₁, show Spec.ChaCha20.bytesAt = bytesAt from rfl,
      d₁, encrypt_eq, VG.Proof.Poly1305.length_bytesAt]

/-! ## The tag -/

/-- Ready to call `vg_poly1305_finalize`. -/
structure FiA (s₀ : State) (out : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  ebx : s.gpr .ebx = C32 s₀ 672
  ecx : s.gpr .ecx = C32 s₀ out
  eax : s.gpr .eax = 0
  esi : s.gpr .esi = C32 s₀ 448

theorem fiA_ok {s₀ : State} {s : State} (h : Inv s₀ s) (out : Nat) :
    WP isa (.block (ptr .ebx .edi 672 ++ ptr .ecx .edi out ++ ([.mov .eax (.imm 0)] : List Instr) ++ ptr .esi .edi 448)) s
      fun s' => FiA s₀ out s' ∧ s'.mem = s.mem := by
  rw [show (ptr .ebx .edi 672 ++ ptr .ecx .edi out ++ [.mov .eax (.imm 0)] ++ ptr .esi .edi 448 : List Instr) =
    ptr .ebx .edi 672 ++ (ptr .ecx .edi out ++ (.mov .eax (.imm 0) :: ptr .esi .edi 448)) by simp]
  refine WP.block_append (WP.mono (ptr_ok .ebx .edi 672 s) fun s₁ ⟨e₁, g₁, rd₁, wr₁, m₁⟩ => ?_)
  refine WP.block_append (WP.mono (ptr_ok .ecx .edi out s₁) fun s₂ ⟨e₂, g₂, rd₂, wr₂, m₂⟩ => ?_)
  refine wp_movi fun s₃ u₃ _ => ?_
  refine WP.mono (ptr_ok .esi .edi 448 s₃) fun s₄ ⟨e₄, g₄, rd₄, wr₄, m₄⟩ => ?_
  have edi₁ : s₁.gpr .edi = CX s₀ := by rw [g₁ _ (by decide), h.edi]
  have edi₂ : s₂.gpr .edi = CX s₀ := by rw [g₂ _ (by decide), edi₁]
  have edi₃ : s₃.gpr .edi = CX s₀ := by rw [u₃.other _ (by decide), edi₂]
  have mm : s₄.mem = s.mem := by rw [m₄, u₃.mem, m₂, m₁]
  refine ⟨⟨h.step (by rw [g₄ _ (by decide), edi₃, h.edi])
    (by rw [g₄ _ (by decide), u₃.other _ (by decide), g₂ _ (by decide), g₁ _ (by decide)])
    (by rw [rd₄, u₃.rd, rd₂, rd₁]) (by rw [wr₄, u₃.wr, wr₂, wr₁]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp) (by simp), ?_, ?_, ?_, ?_⟩, mm⟩
  · rw [g₄ _ (by decide), u₃.other _ (by decide), g₂ _ (by decide), e₁, h.edi]
  · rw [g₄ _ (by decide), u₃.other _ (by decide), e₂, edi₁]
  · rw [g₄ _ (by decide), u₃.gpr]
  · rw [e₄, edi₃]

theorem finalizeTo_eq (out : Nat) : finalizeTo out =
    .seq (.block (ptr .ebx .edi 672 ++ ptr .ecx .edi out ++ ([.mov .eax (.imm 0)] : List Instr) ++ ptr .esi .edi 448))
      (callWith finRegs "vg_poly1305_finalize" Impl.Poly1305.X86.finalize) := rfl

/-- What the tag's computation keeps: enough to restore the registers. -/
structure Fin (s₀ s : State) : Prop where
  at_ : At s₀ s
  edi : s.gpr .edi = CX s₀
  saved : Saved s₀ s.mem

theorem Inv.fin {s₀ s : State} (h : Inv s₀ s) : Fin s₀ s := ⟨h.at, h.edi, h.saved⟩

theorem fiB_ok {s₀ : State} (hp : APre s₀) {out : Nat} (ho : OutOk out) {s : State} (h : FiA s₀ out s) :
    WP isa (callWith finRegs "vg_poly1305_finalize" Impl.Poly1305.X86.finalize) s fun s' =>
      Fin s₀ s' ∧ Frame [sub s₀ 448 128, sub s₀ out 16, sub s₀ 672 128, stkR s₀] s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        bytesAt s'.mem (cx s₀ + BitVec.ofNat 64 out) 16 = mac key msg := by
  refine finalize_call hp h.inv.at ho h.ebx h.ecx h.eax h.esi fun s' at' cs' f' t' =>
    ⟨⟨at', by rw [cs' .edi (by simp [calleeSaved]), h.inv.edi], h.inv.saved.frame f' fun r hr => ?_⟩, f', t'⟩
  unfold OutOk at ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · exact (hp.stk_sub (by lit_omega)).symm

theorem finalizeTo_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) {out : Nat} (ho : OutOk out) :
    WP isa (finalizeTo out) s fun s' => Fin s₀ s' ∧
      Frame [sub s₀ 448 128, sub s₀ out 16, sub s₀ 672 128, stkR s₀] s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        bytesAt s'.mem (cx s₀ + BitVec.ofNat 64 out) 16 = mac key msg := by
  rw [finalizeTo_eq]
  exact WP.seq (WP.mono (fiA_ok h out) fun s₁ ⟨h₁, m₁⟩ => by rw [← m₁]; exact fiB_ok hp ho h₁)

/-! ## Restoring the registers -/

theorem restore_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Fin s₀ s) :
    WP isa (.block restore) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧
      s'.gpr .eax = s.gpr .eax ∧ s'.mem = s.mem := by
  have e : ∀ p ∈ saved, addr (CX s₀) p.2 = cx s₀ + BitVec.ofNat 64 p.2 :=
    fun p h => hp.ea_ctx (by have := saved_bound p h; lit_omega)
  rw [show restore = Spill.restoreCode .edi ([(.ebx, 592), (.esi, 596), (.ebp, 604)] ++ [(.edi, 600)]) ++ []
    from rfl]
  refine Spill.restoreBase_ok _ (by decide) (fun p hp' => ?_)
    (by rw [h.edi]; exact (h.saved.congr (fun p h => (e p h).symm) fun _ _ => rfl).sub (by decide))
    fun s' r' => WP.block_nil ⟨r'.abi (by decide) (by decide) h.at_.esp, r'.other _ (by decide), r'.mem⟩
  have hp'' : p ∈ saved := by revert p hp'; decide
  have := saved_bound p hp''
  rw [h.edi, e p hp'', h.at_.rd, h.at_.wr]
  exact hp.in_ctx' (by lit_omega)

/-! ## Comparing the tags -/

theorem bytesAt4_eq {m : Mem} {p q : Addr} : bytesAt m p 4 = bytesAt m q 4 ↔ m.readW p 32 = m.readW q 32 := by
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; rw [← leNum_bytesAt_4, ← leNum_bytesAt_4, h]
  · intro h; rw [bytesAt_word, bytesAt_word, h]

theorem bytesAt16 (m : Mem) (c : Addr) (a : Nat) :
    bytesAt m (c + BitVec.ofNat 64 a) 16 = bytesAt m (c + BitVec.ofNat 64 a) 4 ++
      (bytesAt m (c + BitVec.ofNat 64 (a + 4)) 4 ++ (bytesAt m (c + BitVec.ofNat 64 (a + 8)) 4 ++
        bytesAt m (c + BitVec.ofNat 64 (a + 12)) 4)) := by
  rw [show (16 : Nat) = 4 + (4 + (4 + 4)) from rfl, VG.Proof.Poly1305.bytesAt_add,
    VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.bytesAt_add]
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem app_inj {a b c d : List Byte} (h : a.length = c.length) : a ++ b = c ++ d ↔ a = c ∧ b = d :=
  ⟨fun e => List.append_inj e h, fun ⟨e₁, e₂⟩ => e₁ ▸ e₂ ▸ rfl⟩

/-- The tags differ in no bit if and only if they are equal. -/
theorem tag_eq (m : Mem) (c : Addr) :
    ((((m.readW (c + BitVec.ofNat 64 640) 32 ^^^ m.readW (c + BitVec.ofNat 64 48) 32) |||
      (m.readW (c + BitVec.ofNat 64 644) 32 ^^^ m.readW (c + BitVec.ofNat 64 52) 32)) |||
      (m.readW (c + BitVec.ofNat 64 648) 32 ^^^ m.readW (c + BitVec.ofNat 64 56) 32)) |||
      (m.readW (c + BitVec.ofNat 64 652) 32 ^^^ m.readW (c + BitVec.ofNat 64 60) 32)) = 0#32 ↔
      bytesAt m (c + BitVec.ofNat 64 640) 16 = bytesAt m (c + BitVec.ofNat 64 48) 16 := by
  have l : ∀ p, (bytesAt m p 4).length = 4 := fun p => VG.Proof.Poly1305.length_bytesAt _ _ _
  rw [bytesAt16, bytesAt16, app_inj (by rw [l, l]), app_inj (by rw [l, l]), app_inj (by rw [l, l]),
    bytesAt4_eq, bytesAt4_eq, bytesAt4_eq, bytesAt4_eq]
  simp only [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, and_assoc]

set_option simprocs false in
theorem compare_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Fin s₀ s) :
    WP isa (.block Impl.ChaCha20Poly1305.X86.compare) s fun s' =>
      s'.gpr .eax = (if bytesAt s.mem (cx s₀ + BitVec.ofNat 64 640) 16 =
        bytesAt s.mem (cx s₀ + BitVec.ofNat 64 48) 16 then 1 else 0) ∧
      (∀ q, q ≠ .eax → q ≠ .ecx → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i : ∀ d, d + 4 ≤ 1024 → InRegions (s.rd ++ s.wr) (cx s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.at_.rd, h.at_.wr]; exact hp.in_ctx' hd
  have e : ∀ d, d < 1024 → (CX s₀ + BitVec.ofNat 32 d).setWidth 64 = cx s₀ + BitVec.ofNat 64 d :=
    fun d hd => hp.c64 hd
  apply WP.of_runBlock
  simp (config := {decide := true}) only [Impl.ChaCha20Poly1305.X86.compare, diff, List.cons_append,
    List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.ea, at_, readSrc, execAlu, arithFlags,
    State.load32, State.setReg, State.setFlags, h.edi, e 640 (by lit_omega), e 48 (by lit_omega), e 644 (by lit_omega),
    e 52 (by lit_omega), e 648 (by lit_omega), e 56 (by lit_omega), e 652 (by lit_omega), e 60 (by lit_omega),
    i 640 (by lit_omega), i 48 (by lit_omega), i 644 (by lit_omega), i 52 (by lit_omega), i 648 (by lit_omega), i 56 (by lit_omega),
    i 652 (by lit_omega), i 60 (by lit_omega), ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q h₁ h₂ => by simp [h₁, h₂], trivial⟩
  have ht := tag_eq s.mem (cx s₀)
  generalize ((((s.mem.readW (cx s₀ + BitVec.ofNat 64 640) 32 ^^^ s.mem.readW (cx s₀ + BitVec.ofNat 64 48) 32) |||
      (s.mem.readW (cx s₀ + BitVec.ofNat 64 644) 32 ^^^ s.mem.readW (cx s₀ + BitVec.ofNat 64 52) 32)) |||
      (s.mem.readW (cx s₀ + BitVec.ofNat 64 648) 32 ^^^ s.mem.readW (cx s₀ + BitVec.ofNat 64 56) 32)) |||
      (s.mem.readW (cx s₀ + BitVec.ofNat 64 652) 32 ^^^ s.mem.readW (cx s₀ + BitVec.ofNat 64 60) 32)) = x at ht ⊢
  by_cases hb : bytesAt s.mem (cx s₀ + BitVec.ofNat 64 640) 16 = bytesAt s.mem (cx s₀ + BitVec.ofNat 64 48) 16
  · rw [ite_eq_left hb, ht.mpr hb]; decide
  · have hx : ¬ x.toNat < 1 := fun h' => hb (ht.mp (BitVec.eq_of_toNat_eq (by simp; omega)))
    rw [ite_eq_right hb]; simp [hx]

end VG.Proof.ChaCha20Poly1305.X86
