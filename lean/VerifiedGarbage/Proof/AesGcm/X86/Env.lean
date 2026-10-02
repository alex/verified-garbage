import VerifiedGarbage.Proof.AesGcm.X86.Callee
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Wp

/-!
# AES-GCM on x86: where everything is

Untrusted: everything here is checked by Lean. The key context (256 bytes at
`Ctx`), the streaming state (80 bytes at `St`), the working space (2560
bytes at `W`) and the `K` bytes of stack below `SP` used by the calls
(`Lay`): the state is disjoint from the parts of `W` other than `[16, 96)`
(where `seal` and `open` keep it), and the context from both. `Env` says
which registers hold `W`, the state and `SP`, that the context may be read
and the state and `W` written, and that `W + ctxO` holds `Ctx`. `xrun`
runs a straight-line block symbolically.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Spec.Aes (bytesAt)

/-! ## Covering regions -/

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

theorem covers_one {r : Region} {ts : List Region} (h : Covers [r] ts) : Covers [r] ts := h

/-! ## The layout -/

/-- The regions: the context, the state and `W`, and the `K` bytes of stack
below `SP` that the calls use (24 for `vg_ghash`, 28 for `vg_aes_ctr32`). -/
structure Lay (Ctx St W SP : BitVec 32) (K : Nat) : Prop where
  fc : Ctx.toNat + 256 ≤ 2 ^ 32
  fs : St.toNat + 80 ≤ 2 ^ 32
  fw : W.toNat + 2560 ≤ 2 ^ 32
  k24 : 24 ≤ K
  k28 : K ≤ 28
  sp : K ≤ SP.toNat
  cs : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 St, 80⟩
  cw : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 W, 2560⟩
  sa : (⟨w64 St, 80⟩ : Region).Disjoint ⟨w64 W, 16⟩
  sb : (⟨w64 St, 80⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 96, 2464⟩
  kc : (below SP K).Disjoint ⟨w64 Ctx, 256⟩
  ks : (below SP K).Disjoint ⟨w64 St, 80⟩
  kw : (below SP K).Disjoint ⟨w64 W, 2560⟩

/-- The registers holding `W`, the state and the stack pointer, what may be
accessed, and the context kept at `W + ctxO`. -/
structure Env (Ctx St W SP : BitVec 32) (s : State) : Prop where
  ebp : s.gpr .ebp = W
  esi : s.gpr .esi = St
  esp : s.gpr .esp = SP
  ctxR : Covers [⟨w64 Ctx, 256⟩] (s.rd ++ s.wr)
  stW : Covers [⟨w64 St, 80⟩] s.wr
  wW : Covers [⟨w64 W, 2560⟩] s.wr
  ctx : s.mem.readW (w64 W + BitVec.ofNat 64 ctxO) 32 = Ctx

namespace Lay

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

variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K)
include L

theorem st_w {a n d k : Nat} (ha : a + n ≤ 80) (hd : (d + k ≤ 16) ∨ (96 ≤ d ∧ d + k ≤ 2560)) :
    (⟨w64 St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ := by
  rcases hd with hd | ⟨h₁, h₂⟩
  · exact (L.sa.sub_left (stSub ha)).sub_right (aSub hd)
  · exact (L.sb.sub_left (stSub ha)).sub_right (bSub h₁ h₂)

theorem ctx_st {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 80) :
    (⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 St + BitVec.ofNat 64 d, k⟩ :=
  (L.cs.sub_left (ctxSub ha)).sub_right (stSub hd)

theorem ctx_w {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 2560) :
    (⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  (L.cw.sub_left (ctxSub ha)).sub_right (wSub hd)

theorem stk_ctx {a n : Nat} (ha : a + n ≤ 256) :
    (below SP K).Disjoint ⟨w64 Ctx + BitVec.ofNat 64 a, n⟩ := L.kc.sub_right (ctxSub ha)

theorem stk_st {a n : Nat} (ha : a + n ≤ 80) :
    (below SP K).Disjoint ⟨w64 St + BitVec.ofNat 64 a, n⟩ := L.ks.sub_right (stSub ha)

theorem stk_w {a n : Nat} (ha : a + n ≤ 2560) :
    (below SP K).Disjoint ⟨w64 W + BitVec.ofNat 64 a, n⟩ := L.kw.sub_right (wSub ha)

omit L in
theorem st_st {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 80) (hd : d + k ≤ 80) :
    (⟨w64 St + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 St + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

omit L in
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨w64 W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

/-- The stack the calls use, at `esp = SP`. -/
theorem below_sub {k : Nat} (hk : k ≤ K) : Region.Sub (below SP k) (below SP K) :=
  VG.X86.below_sub hk L.sp

/-! ### Pointers into the regions, as the code computes them -/

theorem aW {o : Nat} (ho : o < 2560) : w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o :=
  w64_add (by have := L.fw; omega)

theorem aS {o : Nat} (ho : o < 80) : w64 (St + BitVec.ofNat 32 o) = w64 St + BitVec.ofNat 64 o :=
  w64_add (by have := L.fs; omega)

theorem aC {o : Nat} (ho : o < 256) : w64 (Ctx + BitVec.ofNat 32 o) = w64 Ctx + BitVec.ofNat 64 o :=
  w64_add (by have := L.fc; omega)

theorem nW {o : Nat} (ho : o < 2560) : (W + BitVec.ofNat 32 o).toNat = W.toNat + o :=
  toNat_add32 (by have := L.fw; omega)

theorem nS {o : Nat} (ho : o < 80) : (St + BitVec.ofNat 32 o).toNat = St.toNat + o :=
  toNat_add32 (by have := L.fs; omega)

theorem nC {o : Nat} (ho : o < 256) : (Ctx + BitVec.ofNat 32 o).toNat = Ctx.toNat + o :=
  toNat_add32 (by have := L.fc; omega)

end Lay

namespace Env

variable {Ctx St W SP : BitVec 32} {s : State} (E : Env Ctx St W SP s)
include E

theorem ctxIn {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (w64 Ctx + BitVec.ofNat 64 d) n :=
  in_off E.ctxR h (by decide)

theorem stIn {d n : Nat} (h : d + n ≤ 80) : InRegions s.wr (w64 St + BitVec.ofNat 64 d) n :=
  in_off E.stW h (by decide)

theorem stIn' {d n : Nat} (h : d + n ≤ 80) : InRegions (s.rd ++ s.wr) (w64 St + BitVec.ofNat 64 d) n :=
  in_left (E.stIn h)

theorem wIn {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (w64 W + BitVec.ofNat 64 d) n :=
  in_off E.wW h (by decide)

theorem wIn' {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 d) n :=
  in_left (E.wIn h)

theorem ctxC {d n : Nat} (h : d + n ≤ 256) : Covers [⟨w64 Ctx + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_off E.ctxR h (by decide)

theorem stC {d n : Nat} (h : d + n ≤ 80) : Covers [⟨w64 St + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off E.stW h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨w64 W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off E.wW h (by decide)

end Env

/-- An environment, after code that keeps `ebp`, `esi`, `esp`, the
permissions and the context's slot. -/
theorem Env.keep {Ctx St W SP : BitVec 32} {s s' : State} (h : Env Ctx St W SP s)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hc : s'.mem.readW (w64 W + BitVec.ofNat 64 ctxO) 32 = s.mem.readW (w64 W + BitVec.ofNat 64 ctxO) 32) :
    Env Ctx St W SP s' :=
  ⟨by rw [hbp, h.ebp], by rw [hsi, h.esi], by rw [hsp, h.esp], by rw [hrd, hwr]; exact h.ctxR,
    by rw [hwr]; exact h.stW, by rw [hwr]; exact h.wW, by rw [hc, h.ctx]⟩

/-- The context's slot outside a frame that does not touch it. -/
theorem slot_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {W : BitVec 32} {o : Nat}
    (hd : ∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r) :
    m'.readW (w64 W + BitVec.ofNat 64 o) 32 = m.readW (w64 W + BitVec.ofNat 64 o) 32 :=
  hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) hd (by decide)

/-! ## Words written at offsets -/

/-- A word at `p + a`, after a word written at `p + b` elsewhere. -/
theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 32) {a b : Nat} (h : a + 4 ≤ b ∨ b + 4 ≤ a)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (m.writeW (p + BitVec.ofNat 64 b) v).readW (p + BitVec.ofNat 64 a) 32 = m.readW (p + BitVec.ofNat 64 a) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

/-- A word at `p + a`, after a byte written at `q` elsewhere. -/
theorem readW_writeB_sep (m : Mem) {p q : Addr} (v : BitVec 8) (h : Mem.Sep p 4 q 1) :
    (m.writeW q v).readW p 32 = m.readW p 32 :=
  Mem.readW_writeW_sep h (by decide)

/-! ## Arithmetic -/

theorem ofNat_add_ofNat32 (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem ofNat_sub32 {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := a) ha, Nat.mod_eq_of_lt (a := a - b) (by omega)]
  omega

theorem sub_beq32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := VG.X86.Wp.sub_beq ha hb

theorem and_self_beq32 {a : Nat} (ha : a < 2 ^ 32) :
    (BitVec.ofNat 32 a &&& BitVec.ofNat 32 a == 0) = decide (a = 0) := by
  rw [BitVec.and_self]
  by_cases h : a = 0
  · subst h; rfl
  · have : BitVec.ofNat 32 a ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat32 ha] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem and15 (x : BitVec 32) : x &&& BitVec.ofNat 32 15 = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 15) (by decide),
    show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shr4 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 4 = BitVec.ofNat 32 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- `16 k`, by four doublings. -/
theorem times16 (x : BitVec 32) :
    x + x + (x + x) + (x + x + (x + x)) + (x + x + (x + x) + (x + x + (x + x))) =
      BitVec.ofNat 32 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `CF` after `a - b`, as natural numbers. -/
theorem lt_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    ((BitVec.ofNat 32 a).toNat < (BitVec.ofNat 32 b).toNat) = (a < b) := by
  rw [toNat_ofNat32 ha, toNat_ofNat32 hb]

/-! ## Running a block -/

theorem runBlock_app (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (isa.exec i s).bind (runBlock isa (is ++ b)) =
      ((isa.exec i s).bind (runBlock isa is)).bind (runBlock isa b)
    cases isa.exec i s with
    | none => rfl
    | some t => exact ih t

theorem runBlock_app_of {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [runBlock_app, h₁]; exact h₂

theorem blocksAt_one (m : Mem) (p : Addr) : Spec.Gcm.blocksAt m p 1 = [Spec.Gcm.blockAt m p] := by
  simp [Spec.Gcm.blocksAt]


/-- A state with its memory replaced, kept folded (as `State.setReg` is) so
that a store does not copy the state into every field of a structure. -/
def setMem (s : State) (m : Mem) : State := { s with mem := m }

theorem store32_eq (s : State) (a : Addr) (v : BitVec 32) :
    s.store32 a v = if InRegions s.wr a 4 then some (setMem s (s.mem.writeW a v)) else none := rfl

theorem store8_eq (s : State) (a : Addr) (v : Byte) :
    s.store8 a v = if InRegions s.wr a 1 then some (setMem s (s.mem.writeW a v)) else none := rfl

theorem gpr_setMem (s : State) (m : Mem) : (setMem s m).gpr = s.gpr := rfl
theorem mem_setMem (s : State) (m : Mem) : (setMem s m).mem = m := rfl
theorem rd_setMem (s : State) (m : Mem) : (setMem s m).rd = s.rd := rfl
theorem wr_setMem (s : State) (m : Mem) : (setMem s m).wr = s.wr := rfl
theorem cf_setMem (s : State) (m : Mem) : (setMem s m).cf = s.cf := rfl
theorem zf_setMem (s : State) (m : Mem) : (setMem s m).zf = s.zf := rfl

/-- Runs a block of the instructions the AES-GCM code uses. The facts given
rewrite the addresses and discharge the permissions. -/
macro "xrun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (config := {decide := true}) (disch := first | decide | omega) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, execAlu, execShift, State.load32, store32_eq, State.load8, store8_eq,
    State.ea, at_, imm, slot, argOp, stO, tO, uO, ctxO, roundsO, alO, ahO, xlO, xhO, dataO, lenO, aadO, tglO,
    auxO, zO, nlO, vO, rO, dO, nO, bO, scrO, List.cons_append, List.nil_append, List.append_assoc,
    Option.bind_some, Option.map_some, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, mem_setReg,
    mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags,
    wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags, gpr_setMem, mem_setMem, rd_setMem,
    wr_setMem, cf_setMem, zf_setMem, ite_true, ite_false, reduceCtorEq, Nat.reduceAdd, $ts,*]) <;>
  try rfl)

/-- Reads registers through the writes of a block. -/
macro "regs" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := decide) only [gpr_setMem, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags,
    $ts,*]))

/-- Reads the memory, flags and permissions through the writes of a block. -/
macro "mems" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [mem_setMem, mem_setReg, mem_arithFlags, mem_setFlags,
    rd_setMem, rd_setReg, rd_arithFlags, rd_setFlags, wr_setMem, wr_setReg, wr_arithFlags, wr_setFlags,
    zf_setMem, zf_setReg, zf_arithFlags, cf_setMem, cf_setReg, cf_arithFlags, gpr_setMem, gpr_setReg_self,
    gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, Mem.readW_writeW_self32, readW_writeW_off, stO, tO, uO,
    ctxO, roundsO, alO, ahO, xlO, xhO, dataO, lenO, aadO, tglO, auxO, zO, nlO, vO, rO, dO, nO, bO, scrO,
    Nat.reduceAdd, $ts,*]))

end VG.Proof.AesGcm.X86
