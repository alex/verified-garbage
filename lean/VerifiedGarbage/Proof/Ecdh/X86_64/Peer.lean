import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
import VerifiedGarbage.Impl.Ecdh.X86_64
import VerifiedGarbage.Proof.Ecdsa.X86_64.Finish
import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed

/-!
# ECDH on x86-64: reading and checking the peer's key

## The checks

Each check ands a mask into the flag, as the signature's checks do
(`Proof/Weierstrass/X86_64/Flags.lean`): the peer's first byte is `04`
(`checkLead_ok`), a number is below `p` (`checkLtP_ok`) and a number is
zero (`checkZero_ok`).
-/

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem ea_base (s : State) (r : Reg) : s.ea { base := r } = s.gpr r := by
  show s.gpr r + BitVec.ofInt 64 0 = _
  exact BitVec.add_zero _

/-- `rdx = -CF`. -/
theorem sbbRdx_ok (s : State) {b : Bool} (hb : s.cf = some b) :
    WP isa (.block [.alu .sbb .rdx (.reg .rdx)]) s fun s' =>
      s'.gpr .rdx = (if b then BitVec.allOnes 64 else 0) ∧ Keeps [.rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, hb, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨by cases b <;> simp, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `cmp rdx, 1` sets `CF` iff `rdx = 0`. -/
theorem cmpOne_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm 1)]) s fun s' =>
      s'.cf = some (decide (s.gpr .rdx = 0)) ∧ Keeps [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.cf_arithFlags, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r _ => by simp only [RegUpd.gpr_arithFlags], rfl, rfl, rfl⟩
  have : (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 := by decide
  rw [this]
  congr 1
  simp only [Nat.lt_one_iff]
  exact propext ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => by rw [h]; rfl⟩

/-- The mask `rdx` of the byte at `q` being `04`. -/
theorem lead_ok {s : State} {q : Addr} (hq : s.gpr .r9 = q) (hin : InRegions (s.rd ++ s.wr) q 1) :
    WP isa (.block ([.movzx8 .rdx { base := .r9 }, .alu .xor .rdx (.imm 4), .alu .cmp .rdx (.imm 1),
      .alu .sbb .rdx (.reg .rdx)] : List Instr)) s fun s' =>
      s'.gpr .rdx = mask (s.mem q = 4) ∧ Keeps [.rdx] s s' := by
  rw [show ([.movzx8 .rdx { base := .r9 }, .alu .xor .rdx (.imm 4), .alu .cmp .rdx (.imm 1),
      .alu .sbb .rdx (.reg .rdx)] : List Instr) = [.movzx8 .rdx { base := .r9 }, .alu .xor .rdx (.imm 4)] ++
      ([.alu .cmp .rdx (.imm 1)] ++ [.alu .sbb .rdx (.reg .rdx)]) from rfl, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.movzx8 .rdx { base := .r9 }, .alu .xor .rdx (.imm 4)]) s
      (fun s₁ => s₁.gpr .rdx = (s.mem q).setWidth 64 ^^^ BitVec.signExtend 64 (4 : BitVec 32) ∧
        Keeps [.rdx] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
      Option.map_some, State.load8, ea_base, hq, hin, ite_true, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cmpOne_ok s₁) fun s₂ ⟨c₂, k₂⟩ => ?_
  refine WP.mono (sbbRdx_ok s₂ c₂) fun s₃ ⟨e₃, k₃⟩ =>
    ⟨?_, (k₁.trans (k₂.mono (fun _ h => absurd h List.not_mem_nil))).trans k₃⟩
  rw [e₃, e₁]
  have key : ∀ b : Byte, (b.setWidth 64 ^^^ BitVec.signExtend 64 (4 : BitVec 32) = 0) = (b = 4) := by
    decide
  simp only [mask, key, decide_eq_true_eq]

/-! ## Below `p` -/

theorem ltP_eq (c : Cfg) (a : Nat) :
    Impl.Ecdh.X86_64.Cfg.ltP c a =
      (List.range c.n).flatMap (ltStep a (c.sl MP)) ++ ([.alu .sbb .rax (.reg .rax)] : List Instr) := rfl

/-- The mask `rax` of `[a] < p`. -/
theorem ltP_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hm : c.sl MP + 8 * c.n ≤ size) :
    WP isa (.block (Impl.Ecdh.X86_64.Cfg.ltP c a)) s fun s' =>
      s'.gpr .rax = mask (wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MP) c.n) ∧
      Keeps [.rax, .rdx] s s' := by
  obtain ⟨k, hk⟩ : ∃ k, c.n = k + 1 := ⟨c.n - 1, by omega⟩
  rw [ltP_eq, WP.block_append_iff, hk]
  rw [hk] at ha hm
  refine WP.mono (ltSteps_ok hs k ha hm) fun s₁ ⟨c₁, k₁⟩ => ?_
  refine WP.mono (sbbMask_ok s₁ c₁) fun s₂ ⟨e₂, k₂⟩ => ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  rw [e₂]
  simp only [mask, decide_eq_true_eq]

/-- `checkLtP a`: the flag `&=` the mask of `[a] < [MP]`. -/
theorem checkLtP_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hm : c.sl MP + 8 * c.n ≤ size) (hf : c.sl FLAG + 8 ≤ size) :
    WP isa (.block (Impl.Ecdh.X86_64.Cfg.checkLtP c a)) s fun s' =>
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&&
        mask (wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MP) c.n) ∧
      KeepRegs [.rax, .rdx] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  rw [Impl.Ecdh.X86_64.Cfg.checkLtP, List.append_assoc, WP.block_append_iff]
  refine WP.mono (ltP_ok c hs hn ha hm) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rdx (.reg .rax)]) s₁ (fun s₂ =>
      s₂.gpr .rdx = s₁.gpr .rax ∧ Keeps [.rdx] s₁ s₂) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (andFlag_ok' c hs₂ hf) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  refine ⟨by rw [e₃, hm₂, e₂, e₁], (((Keeps.regs k₁).mono (by sub_regs)).trans
    ((Keeps.regs k₂).mono (by sub_regs))).trans (k₃.mono (by sub_regs)), by rw [← hm₂]; exact O₃⟩

/-- `checkLead`: the flag `&=` the mask of the byte at `q = r9` being `04`. -/
theorem checkLead_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {q : Addr} (hq : s.gpr .r9 = q) (hin : InRegions (s.rd ++ s.wr) q 1) (hf : c.sl FLAG + 8 ≤ size) :
    WP isa (.block (Impl.Ecdh.X86_64.Cfg.checkLead c)) s fun s' =>
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&& mask (s.mem q = 4) ∧
      KeepRegs [.rax, .rdx] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  rw [Impl.Ecdh.X86_64.Cfg.checkLead, WP.block_append_iff]
  refine WP.mono (lead_ok hq hin) fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (andFlag_ok' c (hs.of_keeps k₁ (by decide)) hf) fun s₂ ⟨e₂, k₂, O₂⟩ =>
    ⟨by rw [e₂, e₁, k₁.2.1], ((Keeps.regs k₁).mono (by sub_regs)).trans (k₂.mono (by sub_regs)),
      by rw [← k₁.2.1]; exact O₂⟩

/-! ## Zero -/

/-- The mask `rdx` of `[a] = 0`. -/
theorem zero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) :
    WP isa (.block (Impl.Ecdh.X86_64.Cfg.zero c a)) s fun s' =>
      s'.gpr .rdx = mask (wordsVal s.mem base a c.n = 0) ∧ Keeps [.rdx] s s' := by
  rw [Impl.Ecdh.X86_64.Cfg.zero, List.append_assoc, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rdx (.mem (sc a))]) s (fun s₁ =>
      s₁.gpr .rdx = word s.mem base a ∧ Keeps [.rdx] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs (d := a) (by omega),
      Option.map_some, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ors_ok hs₁ (a := a) (c.n - 1) (by omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [e₁, k₁.2.1] at e₂
  have hz : s₂.gpr .rdx = 0 ↔ wordsVal s.mem base a c.n = 0 := by
    rw [e₂, wordsVal_eq_zero_iff]
    constructor
    · intro ⟨h₀, h⟩ j hj
      rcases j with _ | j
      · simpa using h₀
      · exact h j (by omega)
    · intro h
      exact ⟨by simpa using h 0 hn, fun j hj => h (j + 1) (by omega)⟩
  rw [show ([.alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx)] : List Instr) =
    [.alu .cmp .rdx (.imm 1)] ++ [.alu .sbb .rdx (.reg .rdx)] from rfl, WP.block_append_iff]
  refine WP.mono (cmpOne_ok s₂) fun s₃ ⟨c₃, k₃⟩ => ?_
  refine WP.mono (sbbRdx_ok s₃ c₃) fun s₄ ⟨e₄, k₄⟩ =>
    ⟨?_, ((k₁.trans k₂).trans (k₃.mono (fun _ h => absurd h List.not_mem_nil))).trans k₄⟩
  rw [e₄]
  simp only [mask, decide_eq_true_eq, hz]

/-- `checkZero a`: the flag `&=` the mask of `[a] = 0`. -/
theorem checkZero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hf : c.sl FLAG + 8 ≤ size) :
    WP isa (.block (Impl.Ecdh.X86_64.Cfg.checkZero c a)) s fun s' =>
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&& mask (wordsVal s.mem base a c.n = 0) ∧
      KeepRegs [.rax, .rdx] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  rw [Impl.Ecdh.X86_64.Cfg.checkZero, WP.block_append_iff]
  refine WP.mono (zero_ok c hs hn ha) fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (andFlag_ok' c (hs.of_keeps k₁ (by decide)) hf) fun s₂ ⟨e₂, k₂, O₂⟩ =>
    ⟨by rw [e₂, e₁, k₁.2.1], ((Keeps.regs k₁).mono (by sub_regs)).trans (k₂.mono (by sub_regs)),
      by rw [← k₁.2.1]; exact O₂⟩

end VG.Proof.Ecdh.X86_64

/-!
## Reading the peer's key

`peer` stores `R² mod p` and `b R mod p`, reads the peer's `y` into its
slot, and ands into the flag the masks of the peer's first byte being `04`,
`x < p` and `y < p` (`peer_ok`). It writes only those slots and the flag,
in the working space, which the peer's key is apart from.
-/

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.X25519.X86_64 (Keeps)
open VG.Impl.Ecdh.X86_64 (QY R2P BP)

variable {c : Cfg}

theorem signExtend_ofNat : ∀ k < 64, (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by
  decide

/-- `rdx = r9 + k`. -/
theorem ptr_ok (s : State) {k : Nat} (hk : k < 64) :
    WP isa (.block ([.mov .rdx (.reg .r9), .alu .add .rdx (.imm (BitVec.ofNat 32 k))] : List Instr)) s
      fun s' => s'.gpr .rdx = s.gpr .r9 + BitVec.ofNat 64 k ∧ Keeps [.rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
    Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, Option.some.injEq,
    exists_eq_left', signExtend_ofNat k hk]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem peer_eq (c : Cfg) : Impl.Ecdh.X86_64.Cfg.peer c =
    setConst c.n (c.sl R2P) (c.R * c.R % c.C.p) ++ (setConst c.n (c.sl BP) (c.mont c.C.b) ++
    (([.mov .rdx (.reg .r9), .alu .add .rdx (.imm (BitVec.ofNat 32 (1 + 8 * c.n)))] : List Instr) ++
    (loadBE c.n (c.sl QY) .rdx ++ (Impl.Ecdh.X86_64.Cfg.checkLead c ++
    (Impl.Ecdh.X86_64.Cfg.checkLtP c (c.sl E) ++ Impl.Ecdh.X86_64.Cfg.checkLtP c (c.sl QY)))))) := by
  simp only [Impl.Ecdh.X86_64.Cfg.peer, Impl.Ecdh.X86_64.Cfg.consts, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

/-- A slot apart from the one an operation wrote keeps its number. -/
theorem sv_out {base : Addr} {m m' : Mem} {j : Nat} (h : Outside base (c.sl j) (8 * c.n) m m')
    (h7 : c.n < 7) (hn : base.toNat + size ≤ 2 ^ 64) {i : Nat} (hi : i < 45) (hij : i ≠ j) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n := by
  have := sl_le c h7 hi
  exact h.wordsVal (sl_apart c hij) (by omega)

/-- The constants, the peer's `y` and the checks of its first byte, `x` and `y`. -/
theorem peer_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {q : Addr}
    (hq : s.gpr .r9 = q) (hin : (⟨q, 1 + 16 * c.n⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨q, 1 + 16 * c.n⟩ ⟨base, size⟩) (hmp : sv c base s MP = c.C.p) :
    WP isa (.block (Impl.Ecdh.X86_64.Cfg.peer c)) s fun s' =>
      Scr s' base size ∧ KeepRegs [.rax, .rdx] s s' ∧
      Unch base (slW c [R2P, BP, QY] ++ [(c.sl FLAG, 8)]) s.mem s'.mem ∧
      sv c base s' R2P = c.R * c.R % c.C.p ∧ sv c base s' BP = c.mont c.C.b ∧
      sv c base s' QY = ofBytes (Spec.Ecdsa.bytesAt s.mem (q + BitVec.ofNat 64 (1 + 8 * c.n)) (8 * c.n)) ∧
      word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&& mask (s.mem q = 4) &&&
        mask (sv c base s E < c.C.p) &&& mask (sv c base s' QY < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n7
  have hn := hs.nowrap
  have hpl := hc.p_lt
  have hp3 := hc.p_ge
  have hsz : size = 8192 := rfl
  have hF : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  have hR2 := sl_le c h7 (i := R2P) (by decide)
  have hB := sl_le c h7 (i := BP) (by decide)
  have hY := sl_le c h7 (i := QY) (by decide)
  have hE := sl_le c h7 (i := E) (by decide)
  have hM := sl_le c h7 (i := MP) (by decide)
  rw [peer_eq, WP.block_append_iff]
  refine WP.mono (setConst_ok hs hR2 (show c.R * c.R % c.C.p < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega)) hpl)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₁ hB (show c.mont c.C.b < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega)) hpl)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ptr_ok s₂ (k := 1 + 8 * c.n) (by omega)) fun s₃ ⟨e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have hq₂ : s₂.gpr .r9 = q := by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hq]
  have hq₃ : s₃.gpr .r9 = q := by rw [k₃.1 _ (by decide), hq₂]
  have hrw₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by
    rw [k₃.2.2.1, k₃.2.2.2, k₂.rd, k₂.wr, k₁.rd, k₁.wr]
  rw [hq₂] at e₃
  -- `y`
  rw [WP.block_append_iff]
  refine WP.mono (loadBE_ok hs₃ (src := .rdx) (by decide) hY (fun e he => ⟨_, by rw [hrw₃]; exact hin, by
      rw [e₃, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact Offset.contains_base q (by omega) (by omega)⟩)
    (by rw [e₃]; exact (hd.sub_left (Offset.sub_base q (by omega))).sub_right (Offset.sub_base base hY)))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have O₄' : Outside base (c.sl QY) (8 * c.n) s₂.mem s₄.mem := k₃.2.1 ▸ O₄
  have hq₄ : s₄.gpr .r9 = q := by rw [k₄.gpr _ (by decide), hq₃]
  have hrw₄ : s₄.rd ++ s₄.wr = s.rd ++ s.wr := by rw [k₄.rd, k₄.wr, hrw₃]
  -- What the stores so far keep: everything apart from the working space.
  have W₄ : Outside base 0 size s.mem s₄.mem :=
    ((O₁.mono (Nat.zero_le _) (by omega)).trans (O₂.mono (Nat.zero_le _) (by omega))).trans
      (O₄'.mono (Nat.zero_le _) (by omega))
  have hq0 : s₄.mem q = s.mem q := by
    have := keep_of_disjoint' W₄ hd (by omega) (i := 0) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  -- the first byte
  rw [WP.block_append_iff]
  refine WP.mono (checkLead_ok c hs₄ hq₄ ⟨_, by rw [hrw₄]; exact hin, by
      have := Offset.contains_base q (d := 0) (n := 1) (k := 1 + 16 * c.n) (by omega) (by omega)
      rwa [BitVec.add_zero] at this⟩ hF) fun s₅ ⟨f₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  -- `x < p`
  rw [WP.block_append_iff]
  refine WP.mono (checkLtP_ok c hs₅ h0 hE hM hF) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  -- `y < p`
  refine WP.mono (checkLtP_ok c hs₆ h0 hY hM hF) fun s₇ ⟨f₇, k₇, O₇⟩ => ?_
  -- The slots.
  have v₄ : ∀ {i}, i < 45 → i ≠ R2P → i ≠ BP → i ≠ QY →
      wordsVal s₄.mem base (c.sl i) c.n = wordsVal s.mem base (c.sl i) c.n :=
    fun hi h₁ h₂ h₃ => by
      rw [sv_out O₄' h7 hn hi h₃, sv_out O₂ h7 hn hi h₂, sv_out O₁ h7 hn hi h₁]
  have v₇ : ∀ {i}, i < 45 → i ≠ FLAG →
      wordsVal s₇.mem base (c.sl i) c.n = wordsVal s₄.mem base (c.sl i) c.n := fun hi hf =>
    ((sv_flag O₇ h0 h7 hn hi hf).trans (sv_flag O₆ h0 h7 hn hi hf)).trans (sv_flag O₅ h0 h7 hn hi hf)
  have flag₄ : word s₄.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) := by
    have hap : ∀ {j}, j < 45 → j ≠ FLAG → c.sl FLAG + 8 ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl FLAG :=
      fun hj hjf => by have := sl_apart c (Ne.symm hjf) (i := FLAG); omega
    rw [O₄'.word (hap (j := QY) (by decide) (by decide)) (by omega),
      O₂.word (hap (j := BP) (by decide) (by decide)) (by omega),
      O₁.word (hap (j := R2P) (by decide) (by decide)) (by omega)]
  refine ⟨hs₆.of_keepRegs k₇ (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((k₁.trans k₂).mono (by sub_regs)).trans ((Keeps.regs k₃).mono (by sub_regs))).trans
      ((k₄.mono (by sub_regs)).trans (k₅.trans (k₆.trans k₇))))
  · have U := ((((O₁.unch.trans O₂.unch).trans O₄'.unch).trans O₅.unch).trans
      O₆.unch).trans O₇.unch
    refine U.mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.map_cons, List.map_nil, slW] at hw ⊢
    grind
  · show wordsVal s₇.mem _ _ _ = _
    rw [v₇ (i := R2P) (by decide) (by decide), sv_out O₄' h7 hn (by decide) (by decide),
      sv_out O₂ h7 hn (by decide) (by decide), e₁]
  · show wordsVal s₇.mem _ _ _ = _
    rw [v₇ (i := BP) (by decide) (by decide), sv_out O₄' h7 hn (by decide) (by decide), e₂]
  · show wordsVal s₇.mem _ _ _ = _
    rw [v₇ (i := QY) (by decide) (by decide), e₄, e₃, k₃.2.1]
    congr 1
    exact bytesAt_keep (O₁.mono (Nat.zero_le _) (by omega) |>.trans (O₂.mono (Nat.zero_le _) (by omega)))
      (hd.sub_left (Offset.sub_base q (by omega))) (by omega) (by omega)
  · have mp₅ : wordsVal s₅.mem base (c.sl MP) c.n = c.C.p := by
      rw [sv_flag O₅ h0 h7 hn (i := MP) (by decide) (by decide)]
      exact (v₄ (i := MP) (by decide) (by decide) (by decide) (by decide)).trans hmp
    have mp₆ : wordsVal s₆.mem base (c.sl MP) c.n = c.C.p := by
      rw [sv_flag O₆ h0 h7 hn (i := MP) (by decide) (by decide)]; exact mp₅
    have e₅ : wordsVal s₅.mem base (c.sl E) c.n = sv c base s E := by
      rw [sv_flag O₅ h0 h7 hn (i := E) (by decide) (by decide)]
      exact v₄ (by decide) (by decide) (by decide) (by decide)
    have y₆ : wordsVal s₆.mem base (c.sl QY) c.n = wordsVal s₇.mem base (c.sl QY) c.n :=
      (sv_flag O₇ h0 h7 hn (i := QY) (by decide) (by decide)).symm
    show _ = _ &&& _ &&& mask (wordsVal s.mem base (c.sl E) c.n < c.C.p) &&&
      mask (wordsVal s₇.mem base (c.sl QY) c.n < c.C.p)
    rw [f₇, f₆, f₅, flag₄, hq0, e₅, mp₅, y₆, mp₆]

end VG.Proof.Ecdh.X86_64
