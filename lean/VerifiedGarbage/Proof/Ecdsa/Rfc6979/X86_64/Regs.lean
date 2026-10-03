import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Layout
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-!
# Deterministic ECDSA on x86-64: addresses and registers

The effective addresses of the code's memory operands, the immediates it
sign- or zero-extends, the stack below `rsp` the calls use, and the bytes of
a region a frame of writes misses.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_stk (t : State) (d : Nat) : t.ea (stk d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  show t.gpr .rsp + BitVec.ofInt 64 (d : Int) = _
  rw [ofInt_nat]

theorem ea_at (t : State) (r : Reg) (d : Nat) : t.ea (at_ r d) = t.gpr r + BitVec.ofNat 64 d := by
  show t.gpr r + BitVec.ofInt 64 (d : Int) = _
  rw [ofInt_nat]

theorem sx32 {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem zx32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The 24 bytes below the frame, which the calls use. -/
theorem below24 (B : Addr) : below (B + BitVec.ofNat 64 24) 24 = ⟨B, 24⟩ := by
  show (⟨B + BitVec.ofNat 64 24 - BitVec.ofNat 64 24, 24⟩ : Region) = _
  rw [BitVec.add_sub_cancel]

/-- Callee-saved registers, through writes of others. -/
macro "cs_tac" : tactic => `(tactic| (
  intro r hr
  revert hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
  rintro (h | h | h | h | h | h | h) <;> subst h <;>
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, reduceCtorEq, ite_false]))

/-- A fact `simp` has reduced to `True`, or an equation of definitionally equal sides. -/
macro "triv" : tactic => `(tactic| first | trivial | rfl)

theorem ne_cs {r d : Reg} (hr : r ∈ calleeSaved) (hd : d ∉ calleeSaved) : r ≠ d :=
  fun e => hd (e ▸ hr)

/-- The bytes of a region a frame of writes misses. -/
theorem bytesAt_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m p n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => Frame.bytes (R := ⟨p, n⟩) hf hd hn (List.mem_range.mp hi)

/-- Memory that changed only within `ws` changed only within `ws'`, if each
of `ws` lies within one of `ws'`. -/
theorem Frame.widen {ws ws' : List Region} {m m' : Mem} (hf : Frame ws m m')
    (h : ∀ r ∈ ws, ∃ r' ∈ ws', Region.Sub r r') : Frame ws' m m' := hf.sub h

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

theorem _root_.VG.Region.Sub.trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

/-- `p + d` does not wrap. -/
theorem toNat_add_of {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt h]

/-- The stack below `rsp` a call nested `n / 8 - 1` deep uses, within the 24 bytes below the frame. -/
theorem Ctx.below_sub {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem} {u : State} (hc : Ctx L g m₀ u) {n : Nat}
    (hn : n ≤ 24) : Region.Sub (below (u.gpr .rsp) n) ⟨L.B, 24⟩ := by
  rw [hc.rsp, ← below24]; exact VG.X86_64.below_sub hn (by omega)

theorem Lay.Ok.low_scr {L : Lay} (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, 24⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ h₂)

/-- Code that writes no callee-saved register keeps them (`hc` is checked
by evaluating the code). -/
theorem WP.keepCs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hc : (instrs c).all (fun i => calleeSaved.all fun r => !Taint.clobbers i r) = true) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he⟩
  have h₁ := List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  simpa using h₁

/-- Code that keeps the permissions and the callee-saved registers, and
writes only safe regions, keeps `Ctx`. -/
theorem Ctx.of_keep {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem} (hL : L.Ok) {t : State}
    (hc : Ctx L g m₀ t) {is : List Instr} {ws : List Region} {Q : State → Prop}
    (h : WP isa (.block is) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧ Frame ws t.mem t'.mem ∧ Q t')
    (hk : (instrs (.block is : Prog isa)).all (fun i => calleeSaved.all fun r => !Taint.clobbers i r) = true)
    (hs : ∀ r ∈ ws, Safe L r) :
    WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Frame ws t.mem t'.mem ∧ Q t' :=
  WP.mono (WP.keepCs h hk) fun _ ⟨⟨hrd, hwr, hf, hq⟩, hcs⟩ =>
    ⟨hc.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf hs, hf, hq⟩

/-! ## Code that sets one register -/

/-- `u'` is `u` with only the caller-saved register `d` (and the flags)
changed, to `v`. -/
structure Upd (L : Lay) (g : Reg → BitVec 64) (m₀ : Mem) (u : State) (d : Reg) (v : BitVec 64)
    (u' : State) : Prop where
  ctx : Ctx L g m₀ u'
  mem : u'.mem = u.mem
  val : u'.gpr d = v
  keep : ∀ r, r ≠ d → u'.gpr r = u.gpr r

variable {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

theorem Ctx.set (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved)
    (hrd : u'.rd = u.rd) (hwr : u'.wr = u.wr) (hm : u'.mem = u.mem) (hk : ∀ r, r ≠ d → u'.gpr r = u.gpr r) :
    Ctx L g m₀ u' :=
  hc.regs hL hrd hwr hm fun r hr => hk r (ne_cs hr hd)

/-- `d ← scratch + a`. -/
theorem scr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) {a : Nat}
    (ha : a < 2 ^ 31) :
    WP isa (.block (Cfg.scr d a)) u (Upd L g m₀ u d (L.scr + BitVec.ofNat 64 a)) := by
  have h128 := hc.inFr (d := 128) (by omega) (by omega)
  have hrsp : d ≠ .rsp := fun h => hd (h ▸ by decide)
  apply WP.of_runBlock
  simp only [Cfg.scr, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.load64, ea_stk, hc.rsp, Offset.add_add, Nat.reduceAdd, h128, ite_true, Option.map_some,
    Option.bind_some, RegUpd.gpr_setReg_self, hc.pScr, sx32 ha, Option.some.injEq, exists_eq_left']
  refine ⟨hc.set hL hd rfl rfl rfl fun r hr => ?_, rfl, RegUpd.gpr_setReg_self _ _ _, fun r hr => ?_⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr]
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `d ← rsp + o`, an address in the frame. -/
theorem fr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) {o : Nat}
    (ho : o < 2 ^ 31) :
    WP isa (.block (Cfg.fr d o)) u (Upd L g m₀ u d (L.B + BitVec.ofNat 64 (24 + o))) := by
  apply WP.of_runBlock
  simp only [Cfg.fr, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg_self, hc.rsp, sx32 ho, Offset.add_add,
    Option.some.injEq, exists_eq_left']
  refine ⟨hc.set hL hd rfl rfl rfl fun r hr => ?_, rfl, RegUpd.gpr_setReg_self _ _ _, fun r hr => ?_⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr]
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `d ← n`, zero-extended from 32 bits. -/
theorem mov32_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ∉ calleeSaved) {n : Nat}
    (hn : n < 2 ^ 32) :
    WP isa (.block [.mov32 d (.imm (BitVec.ofNat 32 n))]) u (Upd L g m₀ u d (BitVec.ofNat 64 n)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, zx32 hn, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL hd rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, RegUpd.gpr_setReg_self _ _ _,
    fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩

/-- Two pieces of code, each setting one register. -/
theorem upd_append {is js : List Instr} {u : State} {d e : Reg} {v w : BitVec 64}
    (h₁ : WP isa (.block is) u (Upd L g m₀ u d v))
    (h₂ : ∀ u', Ctx L g m₀ u' → WP isa (.block js) u' (Upd L g m₀ u' e w)) {Q : State → Prop}
    (hQ : ∀ u'', Ctx L g m₀ u'' → u''.mem = u.mem → u''.gpr e = w →
      (∀ r, r ≠ e → r ≠ d → u''.gpr r = u.gpr r) → (e ≠ d → u''.gpr d = v) → Q u'') :
    WP isa (.block (is ++ js)) u Q := by
  rw [WP.block_append_iff]
  refine WP.mono h₁ fun u' h => WP.mono (h₂ u' h.ctx) fun u'' h' => hQ u'' h'.ctx (h'.mem.trans h.mem) h'.val
    (fun r hre hrd => (h'.keep r hre).trans (h.keep r hrd)) fun hne => (h'.keep d hne.symm).trans h.val

end VG.Proof.Ecdsa.Rfc6979.X86_64
