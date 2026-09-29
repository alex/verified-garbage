import VerifiedGarbage.Spec.ChaCha20Poly1305
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.Arm.Xor
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Impl.ChaCha20Poly1305.Arm

/-!
# ChaCha20-Poly1305 on ARMv7: the entry state, regions and invariant

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20Poly1305

open Spec.ChaCha20Poly1305
open Spec.Poly1305 (bytesAt)

open VG.Arm in
/-- The precondition of both functions: `ctx` (1024 bytes) and `data` may be
read and written, `aad` and the stack argument read; the written ones overlap
nothing else; none of them overlaps the 8 bytes below the stack pointer;
nothing wraps around the end of the address space. -/
def preArm (s : Arm.State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 1024⟩
  let aad : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
  let data : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
  let args : Region := ⟨stackArgAddr s 0, 4⟩
  let below : Region := ⟨State.addr s.sp - 8, 8⟩
  s.rd = [aad, args] ∧ s.wr = [ctx, data] ∧
  ctx.Disjoint aad ∧ ctx.Disjoint data ∧ aad.Disjoint data ∧ ctx.Disjoint args ∧ data.Disjoint args ∧
  below.Disjoint ctx ∧ below.Disjoint aad ∧ below.Disjoint data ∧
  (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
  (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧ s.sp.toNat + 4 ≤ 2 ^ 32

open VG.Arm in
def pubArm (s₁ s₂ : Arm.State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
  s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

open VG.Arm in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_chacha20_poly1305_seal(ctx, aad, aad_len, data, len)`. -/
def sealArm : Contract Arm.isa where
  pre := preArm
  post s s' :=
    let ctx := State.addr (s.gpr .r0)
    encrypt (bytesAt s.mem ctx 32) (bytesAt s.mem (ctx + 32) 12)
        (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
        (bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat) =
      (bytesAt s'.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat, bytesAt s'.mem (ctx + 48) 16)
  pub := pubArm

open VG.Arm in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_chacha20_poly1305_open(ctx, aad, aad_len, data, len) -> u32`. -/
def openArm : Contract Arm.isa where
  pre := preArm
  post s s' :=
    let ctx := State.addr (s.gpr .r0)
    match decrypt (bytesAt s.mem ctx 32) (bytesAt s.mem (ctx + 32) 12)
        (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
        (bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat) (bytesAt s.mem (ctx + 48) 16) with
    | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat = pt
    | none => s'.gpr .r0 = 0
  pub := pubArm

end VG.Proof.ChaCha20Poly1305

namespace VG.Proof.ChaCha20Poly1305.Arm

open VG VG.Arm VG.Impl.ChaCha20Poly1305.Arm
open VG.Proof.Sha256.Arm.Stream (Upd Mupd Fupd)
open VG.Proof.ChaCha20.Arm (toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-- `p + d`, as a 64-bit address. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

/-! ## The entry state -/

section
variable (s₀ : State)
/-- The context, the additional data and the data, as 32-bit pointers. -/
abbrev cP : BitVec 32 := s₀.gpr .r0
abbrev aP : BitVec 32 := s₀.gpr .r1
abbrev dP : BitVec 32 := s₀.gpr .r3
abbrev cx : Addr := State.addr (cP s₀)
abbrev ad : Addr := State.addr (aP s₀)
abbrev dp : Addr := State.addr (dP s₀)
abbrev AL : Nat := (s₀.gpr .r2).toNat
abbrev L : Nat := (stackArg s₀ 0).toNat
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
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩
/-- The 8 bytes below the stack pointer, which the frame pushes. -/
abbrev belR : Region := ⟨State.addr s₀.sp - 8, 8⟩
/-- `ctx[k, k + n)`. -/
abbrev sub (k n : Nat) : Region := ⟨off (cx s₀) k, n⟩
/-- `ctx + k`, as the code computes it. -/
abbrev ptr (k : Nat) : BitVec 32 := cP s₀ + BitVec.ofNat 32 k
end

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [aR s₀, argR s₀]
  wr : s₀.wr = [ctxR s₀, dR s₀]
  c_a : (ctxR s₀).Disjoint (aR s₀)
  c_d : (ctxR s₀).Disjoint (dR s₀)
  a_d : (aR s₀).Disjoint (dR s₀)
  c_arg : (ctxR s₀).Disjoint (argR s₀)
  d_arg : (dR s₀).Disjoint (argR s₀)
  b_c : (belR s₀).Disjoint (ctxR s₀)
  b_a : (belR s₀).Disjoint (aR s₀)
  b_d : (belR s₀).Disjoint (dR s₀)
  fit_c : (cP s₀).toNat + 1024 ≤ 2 ^ 32
  fit_a : (aP s₀).toNat + AL s₀ ≤ 2 ^ 32
  fit_d : (dP s₀).toNat + L s₀ ≤ 2 ^ 32
  sp8 : 8 ≤ s₀.sp.toNat
  spfit : s₀.sp.toNat + 4 ≤ 2 ^ 32

theorem APre.of (s₀ : State) (h : preArm s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

theorem toNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem addr_toNat (p : BitVec 32) : (State.addr p).toNat = p.toNat :=
  VG.Proof.ChaCha20.Arm.Xor.addr_toNat p

/-! ## Regions -/

theorem sub_off (p : Addr) {a n len : Nat} (h : a + n ≤ len) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, n⟩ ⟨p, len⟩ := by
  intro x hx
  simp only [Region.Contains] at *
  have : (x - p).toNat ≤ (x - (p + BitVec.ofNat 64 a)).toNat + a := by
    rw [show x - p = (x - (p + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by bv_omega,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    exact le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

theorem sub_ctx (s₀ : State) {k n : Nat} (h : k + n ≤ 1024) : Region.Sub (sub s₀ k n) (ctxR s₀) :=
  sub_off _ h

theorem sub_disj (s₀ : State) {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 1024)
    (hb : b + m ≤ 1024) : (sub s₀ a n).Disjoint (sub s₀ b m) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem sub_sub (s₀ : State) {a m k n : Nat} (h₁ : a ≤ k) (h₂ : k + n ≤ a + m) (h₃ : a + m ≤ 1024) :
    Region.Sub (sub s₀ k n) (sub s₀ a m) := by
  intro x hx
  simp only [Region.Contains, off] at *
  have e : x - (cx s₀ + BitVec.ofNat 64 a) = (x - (cx s₀ + BitVec.ofNat 64 k)) + BitVec.ofNat 64 (k - a) := by
    rw [show k = a + (k - a) by omega, BitVec.ofNat_add]; bv_omega
  rw [e, BitVec.toNat_add, toNat_ofNat_lt (by omega)]
  exact le_trans (Nat.add_le_add_right (Nat.mod_le _ _) _) (by omega)

theorem contains_sub (s₀ : State) {k n a w : Nat} (h₁ : k ≤ a) (h₂ : a + w ≤ k + n) (h₃ : k + n ≤ 1024) :
    (sub s₀ k n).Contains (off (cx s₀) a) w := by
  simp only [Region.Contains]
  rw [show cx s₀ + BitVec.ofNat 64 a - (cx s₀ + BitVec.ofNat 64 k) = BitVec.ofNat 64 (a - k) by
    rw [show a = k + (a - k) by omega, BitVec.ofNat_add]; bv_omega, toNat_ofNat_lt (by omega)]
  omega

theorem contains_ctx (s₀ : State) {a w : Nat} (h : a + w ≤ 1024) : (ctxR s₀).Contains (off (cx s₀) a) w := by
  simp only [Region.Contains]
  rw [show cx s₀ + BitVec.ofNat 64 a - cx s₀ = BitVec.ofNat 64 a by bv_omega, toNat_ofNat_lt (by omega)]
  omega

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  show p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem off_add (p : Addr) (a b : Nat) : off p a + BitVec.ofNat 64 b = off p (a + b) :=
  off_off p a b

theorem off_zero (p : Addr) : off p 0 = p := by simp

namespace APre
variable {s₀ : State} (hp : APre s₀)
include hp

theorem in_ctx {a w : Nat} (h : a + w ≤ 1024) : InRegions s₀.wr (off (cx s₀) a) w :=
  ⟨ctxR s₀, by simp [hp.wr], contains_ctx s₀ h⟩

theorem in_ctx' {a w : Nat} (h : a + w ≤ 1024) : InRegions (s₀.rd ++ s₀.wr) (off (cx s₀) a) w :=
  ⟨ctxR s₀, by simp [hp.wr], contains_ctx s₀ h⟩

/-- `ctx + k`, computed in 32 bits, is `cx + k`. -/
theorem addr_ptr {k : Nat} (h : k < 1024) : State.addr (ptr s₀ k) = off (cx s₀) k :=
  addr_add (by have := hp.fit_c; omega)

theorem addr_cP_off {d : Nat} (h : d < 1024) :
    State.addr (cP s₀ + BitVec.ofNat 32 d) = off (cx s₀) d :=
  hp.addr_ptr h

theorem ptr_toNat {k : Nat} (h : k < 1024) : (ptr s₀ k).toNat = (cP s₀).toNat + k := by
  have := hp.fit_c
  rw [BitVec.toNat_add, toNat32 (by omega), Nat.mod_eq_of_lt (by omega)]

end APre

/-! ## Covering the callees' regions -/

theorem covers_sub {s₀ s : State} (hp : APre s₀) (hwr : s.wr = s₀.wr) (rs : List Region)
    (h : ∀ r ∈ rs, ∃ k, r = sub s₀ k r.len ∧ k + r.len ≤ 1024) : Covers rs s.wr := by
  refine Covers.of_sub fun r hr => ?_
  obtain ⟨k, hrk, hk⟩ := h r hr
  exact ⟨ctxR s₀, by simp [hwr, hp.wr], k, by rw [hrk], hk⟩

theorem covers_left {rs wr : List Region} (rd : List Region) (h : Covers rs wr) : Covers rs (rd ++ wr) :=
  fun a n hi => by
    obtain ⟨r, hr, hc⟩ := h a n hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- A callee's working space (at `ctx + a`, `n` bytes) and argument (at
`ctx + b`, `m` bytes) in the context. -/
theorem covers2 {s₀ s : State} (hp : APre s₀) (hwr : s.wr = s₀.wr) {a n b m : Nat}
    (ha : a + n ≤ 1024) (hb : b + m ≤ 1024) :
    Covers ([sub s₀ b m] ++ [sub s₀ a n]) (s.rd ++ s.wr) :=
  covers_left _ (covers_sub hp hwr _ fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨b, rfl, hb⟩
    · exact ⟨a, rfl, ha⟩)

theorem covers1 {s₀ s : State} (hp : APre s₀) (hwr : s.wr = s₀.wr) {a n : Nat} (ha : a + n ≤ 1024) :
    Covers [sub s₀ a n] s.wr :=
  covers_sub hp hwr _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨a, rfl, ha⟩

/-! ## What a part keeps -/

/-- `s'` differs from `s` only in memory within `rs` and in registers that
are not callee-saved (or are `lr`). -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem Kept.trans {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : Kept rs s₁ s₂) (h₂ : Kept rs s₂ s₃) :
    Kept rs s₁ s₃ :=
  ⟨fun r hr h => by rw [h₂.cs r hr h, h₁.cs r hr h], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame⟩

theorem Kept.sub {rs rs' : List Region} {s s' : State} (h : Kept rs s s')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : Kept rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.sub hs⟩

theorem Kept.mem_eq {s s' : State} (hk : Kept [] s s') : s'.mem = s.mem :=
  funext fun x => hk.frame x fun _ h => absurd h List.not_mem_nil

/-- A block that writes no callee-saved register keeps them, and the stack
pointer. -/
theorem WP.kept {is : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block is) s Q)
    (hc : (is.all fun i => preserved.all fun r => dstOf i != some r) = true) :
    WP isa (.block is) s fun s' => Q s' ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he (.inl rfl), Exec.sp he⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  simpa using this

/-- Kept, from a block's facts. -/
theorem Kept.of {rs : List Region} {s s' : State} (hg : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    Kept rs s s' :=
  ⟨fun r hr _ => hg r hr, hsp, hrd, hwr, hf⟩

/-! ## The saved registers and the invariant -/

/-- Our caller's `r4`–`r11` and our return address, saved in `ctx[480, 516)`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (off (cx s₀) p.2) 32 = s₀.gpr p.1

theorem saved_bound : ∀ p ∈ saved, savOff ≤ p.2 ∧ p.2 + 4 ≤ savOff + 36 := by decide

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sub s₀ savOff 36).Disjoint r) : Saved s₀ m' := by
  intro p hp
  have hb := saved_bound p hp
  rw [hf.readW (contains_sub s₀ (w := 32 / 8) hb.1 hb.2 (by simp [savOff])) hd (by decide), h p hp]

/-- The values we keep in `r7`–`r11`. -/
structure Regs (s₀ s : State) : Prop where
  r7 : s.gpr .r7 = cP s₀
  r8 : s.gpr .r8 = aP s₀
  r9 : s.gpr .r9 = s₀.gpr .r2
  r10 : s.gpr .r10 = dP s₀
  r11 : s.gpr .r11 = stackArg s₀ 0

theorem Regs.kept {s₀ s s' : State} (h : Regs s₀ s) (hk : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) :
    Regs s₀ s' :=
  ⟨by rw [hk _ (by decide) (by decide), h.r7], by rw [hk _ (by decide) (by decide), h.r8],
    by rw [hk _ (by decide) (by decide), h.r9], by rw [hk _ (by decide) (by decide), h.r10],
    by rw [hk _ (by decide) (by decide), h.r11]⟩

/-- What holds between the parts of the code: the registers, the stack
pointer and the regions, the saved registers, and the memory changed only
in the context, the data and the stack below the stack pointer. -/
structure Inv (s₀ : State) (s : State) : Prop where
  regs : Regs s₀ s
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [ctxR s₀, dR s₀, belR s₀] s₀.mem s.mem

/-- The invariant survives a part that keeps the callee-saved registers and
writes only the context outside the saved registers, and the data. -/
theorem Inv.step {s₀ s s' : State} {rs : List Region} (h : Inv s₀ s) (hk : Kept rs s s')
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [ctxR s₀, dR s₀, belR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ savOff 36).Disjoint r) : Inv s₀ s' where
  regs := h.regs.kept hk.cs
  sp := by rw [hk.sp, h.sp]
  rd := by rw [hk.rd, h.rd]
  wr := by rw [hk.wr, h.wr]
  saved := h.saved.frame hk.frame hsv
  frame := h.frame.trans (hk.frame.sub hsub)

/-- A part that writes `ctx[k, k + n)` keeps the invariant. -/
theorem Inv.step1 {s₀ s s' : State} (h : Inv s₀ s) {k n : Nat} (hk : Kept [sub s₀ k n] s s')
    (h₂ : k + n ≤ 1024) (h₃ : k + n ≤ savOff ∨ savOff + 36 ≤ k) : Inv s₀ s' :=
  h.step hk (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨ctxR s₀, by simp, sub_ctx s₀ h₂⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by simp only [savOff] at h₃ ⊢; omega) (by simp [savOff]) h₂)

/-- A part that writes no memory keeps the invariant. -/
theorem Inv.step0 {s₀ s s' : State} (h : Inv s₀ s) (hk : Kept [] s s') : Inv s₀ s' :=
  h.step hk (fun _ hr => absurd hr List.not_mem_nil) (fun _ hr => absurd hr List.not_mem_nil)

end VG.Proof.ChaCha20Poly1305.Arm
