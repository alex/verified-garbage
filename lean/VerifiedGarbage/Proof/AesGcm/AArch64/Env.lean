import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# AES-GCM on AArch64: where everything is

Untrusted: everything here is checked by Lean. The key context (256 bytes at
`Ctx`), the streaming state (80 bytes at `St`) and the working space (2560
bytes at `W`) (`Lay`): the state is disjoint from the parts of `W` other than
`[16, 96)` (where `seal` and `open` keep it), and the context from both.
`Perm` says the state may read the context and write the state and `W`;
`Env` adds the registers that hold the three addresses throughout, and the
stack pointer. `arun` runs a block symbolically.
-/

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)

/-- Runs a block of the instructions the AES-GCM code uses. -/
macro "arun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write,
    sp_write, ite_true, ite_false, Option.bind_some, Option.map_some, BitVec.setWidth_eq, and_self,
    mov, ptr, imm, tO, uO, aadO, alenO, dataO, lenO, tlO, vO, rO, scrO, List.cons_append, List.nil_append,
    List.append_assoc, $ts,*]) <;> try rfl)

/-- The part of a region at an offset is covered when the region is. -/
theorem covers_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : Covers [⟨p + BitVec.ofNat 64 d, n⟩] rs := by
  intro a m ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine h a m ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a - p = (a - (p + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d := by
    rw [Offset.sub_add_eq]; exact (BitVec.sub_add_cancel _ _).symm
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem in_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 d) n :=
  covers_off h hd hk _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem in_left {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_left {rd wr rs : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) :=
  fun a n hi => in_left (h a n hi)

theorem covers_cons {r : Region} {rs ts : List Region} (h₁ : Covers [r] ts) (h₂ : Covers rs ts) :
    Covers (r :: rs) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁ a n ⟨x, List.mem_singleton_self _, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

theorem covers_nil {ts : List Region} : Covers [] ts := fun _ _ ⟨_, h, _⟩ => by cases h

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

theorem covers_append {xs ys ts : List Region} (h₁ : Covers xs ts) (h₂ : Covers ys ts) :
    Covers (xs ++ ys) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact h₁ a n ⟨x, hx, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

theorem covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
    Covers [⟨p, n⟩] rs := fun a m ⟨r, hr, hc⟩ => by
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

/-- The regions: the context, the state and the parts of `W`. -/
structure Lay (Ctx St W : Addr) : Prop where
  cw : Ctx.toNat + 256 ≤ 2 ^ 64
  sw : St.toNat + 80 ≤ 2 ^ 64
  ww : W.toNat + 2560 ≤ 2 ^ 64
  cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨St, 80⟩
  cw' : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩
  sa : (⟨St, 80⟩ : Region).Disjoint ⟨W, 16⟩
  sb : (⟨St, 80⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 96, 2464⟩

/-- What a state may access. -/
structure Perm (Ctx St W : Addr) (s : State) : Prop where
  ctx : Covers [⟨Ctx, 256⟩] (s.rd ++ s.wr)
  st : Covers [⟨St, 80⟩] s.wr
  w : Covers [⟨W, 2560⟩] s.wr

/-- The registers holding the context, the state and `W`, the stack
pointer, and what the state may access. -/
structure Env (Ctx St W SP : Addr) (s : State) : Prop where
  x19 : s.gpr .x19 = W
  x20 : s.gpr .x20 = St
  x21 : s.gpr .x21 = Ctx
  sp : s.sp = SP
  perm : Perm Ctx St W s

theorem Perm.of_eq {Ctx St W : Addr} {s s' : State} (h : Perm Ctx St W s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Perm Ctx St W s' := by
  obtain ⟨a, b, c⟩ := h; exact ⟨by rw [hrd, hwr]; exact a, by rw [hwr]; exact b, by rw [hwr]; exact c⟩

/-- An environment, after code that keeps `x19`–`x21`, the stack pointer and
the permissions. -/
theorem Env.keep {Ctx St W SP : Addr} {s s' : State} (h : Env Ctx St W SP s)
    (hg : ∀ r ∈ [Reg.x19, .x20, .x21], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env Ctx St W SP s' :=
  ⟨by rw [hg _ (by simp), h.x19], by rw [hg _ (by simp), h.x20], by rw [hg _ (by simp), h.x21],
    by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- An environment, after a call. -/
theorem Env.of_saved {Ctx St W SP : Addr} {s s' : State} (h : Env Ctx St W SP s)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env Ctx St W SP s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

namespace Lay

/-! ### Sub-regions -/

theorem ctxSub {Ctx : Addr} {d n : Nat} (h : d + n ≤ 256) : Region.Sub ⟨Ctx + BitVec.ofNat 64 d, n⟩ ⟨Ctx, 256⟩ :=
  Offset.sub_base _ h

theorem stSub {St : Addr} {d n : Nat} (h : d + n ≤ 80) : Region.Sub ⟨St + BitVec.ofNat 64 d, n⟩ ⟨St, 80⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

theorem bSub {W : Addr} {d n : Nat} (h₁ : 96 ≤ d) (h₂ : d + n ≤ 2560) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W + BitVec.ofNat 64 96, 2464⟩ :=
  Offset.sub _ h₁ (by omega)

theorem aSub {W : Addr} {d n : Nat} (h : d + n ≤ 16) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 16⟩ :=
  Offset.sub_base _ h

variable {Ctx St W : Addr} (L : Lay Ctx St W)
include L

/-- Parts of the state and of `W` outside `[16, 96)` are disjoint. -/
theorem st_w {a n d k : Nat} (ha : a + n ≤ 80) (hd : (d + k ≤ 16) ∨ (96 ≤ d ∧ d + k ≤ 2560)) :
    (⟨St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ := by
  rcases hd with hd | ⟨h₁, h₂⟩
  · exact (L.sa.sub_left (stSub ha)).sub_right (aSub hd)
  · exact (L.sb.sub_left (stSub ha)).sub_right (bSub h₁ h₂)

theorem ctx_st {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 80) :
    (⟨Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 d, k⟩ :=
  (L.cs.sub_left (ctxSub ha)).sub_right (stSub hd)

theorem ctx_w {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 2560) :
    (⟨Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  (L.cw'.sub_left (ctxSub ha)).sub_right (wSub hd)

/-- Parts of the state are disjoint. -/
theorem st_st {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 80) (hd : d + k ≤ 80) :
    (⟨St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.sw; omega) (by have := L.sw; omega)

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

end Lay

namespace Perm

variable {Ctx St W : Addr} {s : State} (P : Perm Ctx St W s)
include P

theorem ctxR {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 d) n :=
  in_off P.ctx h (by decide)

theorem stW {d n : Nat} (h : d + n ≤ 80) : InRegions s.wr (St + BitVec.ofNat 64 d) n :=
  in_off P.st h (by decide)

theorem stR {d n : Nat} (h : d + n ≤ 80) : InRegions (s.rd ++ s.wr) (St + BitVec.ofNat 64 d) n :=
  in_left (P.stW h)

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem ctxC {d n : Nat} (h : d + n ≤ 256) : Covers [⟨Ctx + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_off P.ctx h (by decide)

theorem stC {d n : Nat} (h : d + n ≤ 80) : Covers [⟨St + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.st h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

/-! ## Arithmetic on lengths -/

theorem ofNat_add_ofNat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem ofNat_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := a) ha, Nat.mod_eq_of_lt (a := a - b) (by omega)]
  omega

theorem lsr_ofNat (n k : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]

theorem lsl4_ofNat (n : Nat) : BitVec.ofNat 64 n <<< 4 = BitVec.ofNat 64 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  rw [Nat.mod_mul_mod, Nat.mul_comm]

theorem lsl3_eq (x : BitVec 64) : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [Nat.reducePow, Nat.mul_comm]

theorem and15 (x : BitVec 64) : x &&& BitVec.ofNat 64 15 = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 15) (by decide),
    show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat_beq_zero {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a == 0) = decide (a = 0) := by
  by_cases h : a = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 a ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat_of_lt ha] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem ofNat_bne_zero {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a != 0) = !decide (a = 0) := by
  rw [bne, ofNat_beq_zero ha]

/-- `cbz` on a register holding `a`. -/
theorem eval_zero {s : State} {r : Reg} {a : Nat} (h : s.gpr r = BitVec.ofNat 64 a) (ha : a < 2 ^ 64) :
    isa.eval (.zero .x r) s = some (decide (a = 0)) := by
  show some (s.read .x r == 0) = _
  rw [State.read, h, BitVec.setWidth_eq, ofNat_beq_zero ha]

/-- `cbnz` on a register holding `a`. -/
theorem eval_nonzero {s : State} {r : Reg} {a : Nat} (h : s.gpr r = BitVec.ofNat 64 a) (ha : a < 2 ^ 64) :
    isa.eval (.nonzero .x r) s = some (!decide (a = 0)) := by
  show some (s.read .x r != 0) = _
  rw [State.read, h, BitVec.setWidth_eq, ofNat_bne_zero ha]

theorem ofNat_lit (n : Nat) : (OfNat.ofNat n : Addr) = BitVec.ofNat 64 n := rfl

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ofNat_add_ofNat]

theorem movz_ofNat {k : Nat} (hk : k < 2 ^ 16) :
    BitVec.setWidth 64 (BitVec.ofNat 16 k) <<< (16 * 0) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- A running block, with what is known of its result. -/
theorem WP.run {is : List Instr} {s : State} {Q R : State → Prop}
    (h : ∃ s', runBlock isa is s = some s' ∧ Q s') (hq : ∀ s', Q s' → R s') : WP isa (.block is) s R := by
  obtain ⟨s', h₁, h₂⟩ := h; exact WP.of_runBlock ⟨s', h₁, hq _ h₂⟩

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

/-- The registers the pieces keep for the function running them: the rounds
and the function's own values. -/
abbrev keptRegs : List Reg := [.x22, .x26, .x27, .x28]

/-- The kept registers hold the values `k` gives them. -/
def Kept (k : Reg → BitVec 64) (s : State) : Prop := ∀ r ∈ keptRegs, s.gpr r = k r

theorem Kept.of_eq {k : Reg → BitVec 64} {s s' : State} (h : Kept k s) (hg : ∀ r ∈ keptRegs, s'.gpr r = s.gpr r) :
    Kept k s' := fun r hr => (hg r hr).trans (h r hr)

theorem Kept.of_saved {k : Reg → BitVec 64} {s s' : State} (h : Kept k s)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) : Kept k s' :=
  h.of_eq fun r hr => hg r (by
    simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
    simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)

/-- Registers outside `rs` are unchanged. -/
def Others (rs : List Reg) (s s' : State) : Prop := ∀ r, r ∉ rs → s'.gpr r = s.gpr r

theorem Kept.of_others {k : Reg → BitVec 64} {s s' : State} {rs : List Reg} (h : Kept k s) (hg : Others rs s s')
    (hd : ∀ r ∈ keptRegs, r ∉ rs := by decide) : Kept k s' :=
  h.of_eq fun r hr => hg r (hd r hr)

/-- What a block that changes only registers leaves. -/
structure Regs (rs : List Reg) (s s' : State) : Prop where
  others : Others rs s s'
  mem : s'.mem = s.mem
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Env.of_regs {Ctx St W SP : Addr} {s s' : State} {rs : List Reg} (h : Env Ctx St W SP s) (hr : Regs rs s s')
    (hd : ∀ r ∈ [Reg.x19, .x20, .x21], r ∉ rs := by decide) : Env Ctx St W SP s' :=
  h.keep (fun r h' => hr.others r (hd r h')) hr.sp hr.rd hr.wr

theorem Regs.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Regs rs s₁ s₂) (h₂ : Regs rs' s₂ s₃)
    (hs : ∀ r ∈ rs', r ∈ rs := by decide) : Regs rs s₁ s₃ :=
  ⟨fun r hr => (h₂.others r fun h => hr (hs r h)).trans (h₁.others r hr), h₂.mem.trans h₁.mem,
    h₂.sp.trans h₁.sp, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Regs.comp {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Regs rs s₁ s₂) (h₂ : Regs rs' s₂ s₃) :
    Regs (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => (h₂.others r fun h => hr (List.mem_append_right _ h)).trans
    (h₁.others r fun h => hr (List.mem_append_left _ h)), h₂.mem.trans h₁.mem,
    h₂.sp.trans h₁.sp, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Regs.mono {rs rs' : List Reg} {s s' : State} (h : Regs rs s s') (hs : ∀ r ∈ rs, r ∈ rs' := by decide) :
    Regs rs' s s' :=
  ⟨fun r hr => h.others r fun h' => hr (hs r h'), h.mem, h.sp, h.rd, h.wr⟩

theorem Regs.refl (rs : List Reg) (s : State) : Regs rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

/-- Proves `Others rs s s'` for a chain of register writes. -/
macro "others_tac" : tactic => `(tactic| (
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [gpr_write, hr]))

end VG.Proof.AesGcm.AArch64
