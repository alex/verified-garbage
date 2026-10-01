import VerifiedGarbage.Proof.X25519.X86_64.Env
import VerifiedGarbage.Proof.X25519.Ladder

/-!
# X25519 on x86-64: an iteration of the ladder

Untrusted: everything here is checked by Lean. The start of an iteration
(`stepPre`): the counter `rbx` counts down to the bit `t`, whose byte of the
array `BITS` is `k_t`; `swap ^ k_t` becomes the mask in `rcx`, and `k_t` the
new `swap` (a word at `SWAP`).
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- The start of `step`. -/
def stepPre : List Instr :=
  [.alu .sub .rbx (.imm 1), .movzx8 .rax { base := .rdi, index := some .rbx, disp := BITS },
    .mov .rdx (.mem (sc SWAP)), .alu .xor .rdx (.reg .rax), .store (sc SWAP) .rax,
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)]

theorem ea_bits {s : State} {base : Addr} (hr : s.gpr .rdi = base) {t : Nat}
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) :
    s.ea { base := .rdi, index := some .rbx, disp := BITS } = off base (BITS + t) := by
  simp only [State.ea, hr, hb, off, BITS, BitVec.ofInt_natCast]
  rw [BitVec.mul_one, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm t 768]

theorem mask_xor : ∀ a < 2, ∀ b < 2,
    (0 : BitVec 64) - (BitVec.ofNat 64 a ^^^ (BitVec.ofNat 8 b).setWidth 64) =
      mask (decide (a ^^^ b = 1)) := by decide

theorem stepPre_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 255)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 1)) {kt sw0 : Nat} (hk : kt < 2) (hsw : sw0 < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 kt)
    (hswap : word s.mem base SWAP = BitVec.ofNat 64 sw0) :
    WP isa (.block stepPre) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 t ∧ s'.gpr .rcx = mask (decide (sw0 ^^^ kt = 1)) ∧
      (∀ r, r ∉ [.rbx, .rax, .rdx, .rcx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (off base SWAP) (BitVec.ofNat 64 kt) ∧ s'.xmm = s.xmm ∧
      s'.ymmHi = s.ymmHi := by
  have hb' : s.gpr .rbx - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 t := by
    have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
    rw [hb, e1, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hin : InRegions (s.rd ++ s.wr) (off base (BITS + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  have hw : InRegions s.wr (off base SWAP) 8 := ⟨_, hs.wr, contains_sc (by simp only [SWAP]; omega)⟩
  have hr : InRegions (s.rd ++ s.wr) (off base SWAP) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [SWAP]; omega)⟩
  apply WP.of_runBlock
  simp only [stepPre, runBlock_cons, runStep_some, exec, readSrc, execAlu, State.load8,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hb', Option.bind_some]
  rw [ea_bits (base := base) (t := t) (by simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg,
    ite_false, reduceCtorEq, hs.rdi]) (by simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg,
    ite_true])]
  have hswap' : s.mem.readW (off base SWAP) 64 = BitVec.ofNat 64 sw0 := hswap
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    State.load64, State.store64, ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hs.rdi, hin, hbit, hr, hw, hswap', ite_true,
    ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', State.setReg32]
  have e0 : BitVec.setWidth 64 (0 : BitVec 32) = 0 := rfl
  have ek : BitVec.setWidth 64 (BitVec.ofNat 8 kt) = BitVec.ofNat 64 kt := by
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  refine ⟨trivial, by rw [e0]; exact mask_xor sw0 hsw kt hk, fun r hr => ?_, trivial, trivial,
    by rw [ek], rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

variable {fld : Field} (hf : FieldOk fld)

def opsList (fld : Field) : List Instr :=
  cswap (32 * (3 : Fin 128).val) (32 * (5 : Fin 128).val) ++
  cswap (32 * (4 : Fin 128).val) (32 * (6 : Fin 128).val) ++
  add (32 * (7 : Fin 128).val) (32 * (3 : Fin 128).val) (32 * (4 : Fin 128).val) ++
  sub (32 * (8 : Fin 128).val) (32 * (3 : Fin 128).val) (32 * (4 : Fin 128).val) ++
  add (32 * (9 : Fin 128).val) (32 * (5 : Fin 128).val) (32 * (6 : Fin 128).val) ++
  sub (32 * (10 : Fin 128).val) (32 * (5 : Fin 128).val) (32 * (6 : Fin 128).val) ++
  fld.sqr (32 * (11 : Fin 128).val) (32 * (7 : Fin 128).val) ++
  fld.sqr (32 * (12 : Fin 128).val) (32 * (8 : Fin 128).val) ++
  fld.mul (32 * (14 : Fin 128).val) (32 * (10 : Fin 128).val) (32 * (7 : Fin 128).val) ++
  fld.mul (32 * (15 : Fin 128).val) (32 * (9 : Fin 128).val) (32 * (8 : Fin 128).val) ++
  sub (32 * (13 : Fin 128).val) (32 * (11 : Fin 128).val) (32 * (12 : Fin 128).val) ++
  sub (32 * (6 : Fin 128).val) (32 * (14 : Fin 128).val) (32 * (15 : Fin 128).val) ++
  add (32 * (5 : Fin 128).val) (32 * (14 : Fin 128).val) (32 * (15 : Fin 128).val) ++
  fld.a24 (32 * (4 : Fin 128).val) (32 * (13 : Fin 128).val) ++
  fld.sqr (32 * (6 : Fin 128).val) (32 * (6 : Fin 128).val) ++
  fld.sqr (32 * (5 : Fin 128).val) (32 * (5 : Fin 128).val) ++
  add (32 * (4 : Fin 128).val) (32 * (11 : Fin 128).val) (32 * (4 : Fin 128).val) ++
  fld.mul (32 * (6 : Fin 128).val) (32 * (2 : Fin 128).val) (32 * (6 : Fin 128).val) ++
  fld.mul (32 * (3 : Fin 128).val) (32 * (11 : Fin 128).val) (32 * (12 : Fin 128).val) ++
  fld.mul (32 * (4 : Fin 128).val) (32 * (13 : Fin 128).val) (32 * (4 : Fin 128).val)

theorem step_eq : step fld = stepPre ++ (opsList fld ++ ([.alu .test .rbx (.reg .rbx)] : List Instr)) := by
  simp only [step, stepPre, opsList, List.append_assoc]
  rfl

/-- The slots after the field operations of an iteration. -/
def stepEnv (sw : Bool) (e : Env) : Env :=
  opMul 4 13 4 (opMul 3 11 12 (opMul 6 2 6 (opAdd 4 11 4 (opMul 5 5 5 (opMul 6 6 6 (opA24 4 13
    (opAdd 5 14 15 (opSub 6 14 15 (opSub 13 11 12 (opMul 15 9 8 (opMul 14 10 7 (opMul 12 8 8
    (opMul 11 7 7 (opSub 10 5 6 (opAdd 9 5 6 (opSub 8 3 4 (opAdd 7 3 4 (opSwap 4 6 sw
    (opSwap 3 5 sw e)))))))))))))))))))

include hf in
/-- The field operations of an iteration, with the mask `rcx` of the swap
bit `sw`. -/
theorem ops_ok {s1 : State} {base : Addr} (hs1 : Scr s1 base) {sw : Bool}
    (hm : s1.gpr .rcx = mask sw) :
    WP isa (.block (opsList fld)) s1 fun s' =>
      Keep base s1 s' ∧ E s'.mem base = stepEnv sw (E s1.mem base) := by
  simp only [opsList, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs1 3 5 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) hm) fun s2 ⟨k2, c2, e2⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs2 4 6 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (c2.trans hm)) fun s3 ⟨k3, c3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  rw [WP.block_append_iff]
  refine WP.mono (addE hs3 7 3 4 ⟨by decide, by decide⟩) fun s4 ⟨k4, e4⟩ => ?_
  have hs4 := k4.scr hs3
  rw [WP.block_append_iff]
  refine WP.mono (subE hs4 8 3 4 ⟨by decide, by decide⟩) fun s5 ⟨k5, e5⟩ => ?_
  have hs5 := k5.scr hs4
  rw [WP.block_append_iff]
  refine WP.mono (addE hs5 9 5 6 ⟨by decide, by decide⟩) fun s6 ⟨k6, e6⟩ => ?_
  have hs6 := k6.scr hs5
  rw [WP.block_append_iff]
  refine WP.mono (subE hs6 10 5 6 ⟨by decide, by decide⟩) fun s7 ⟨k7, e7⟩ => ?_
  have hs7 := k7.scr hs6
  rw [WP.block_append_iff]
  refine WP.mono (sqrE hf hs7 11 7 ⟨by decide, by decide⟩) fun s8 ⟨k8, e8⟩ => ?_
  have hs8 := k8.scr hs7
  rw [WP.block_append_iff]
  refine WP.mono (sqrE hf hs8 12 8 ⟨by decide, by decide⟩) fun s9 ⟨k9, e9⟩ => ?_
  have hs9 := k9.scr hs8
  rw [WP.block_append_iff]
  refine WP.mono (mulE hf hs9 14 10 7 ⟨by decide, by decide⟩) fun s10 ⟨k10, e10⟩ => ?_
  have hs10 := k10.scr hs9
  rw [WP.block_append_iff]
  refine WP.mono (mulE hf hs10 15 9 8 ⟨by decide, by decide⟩) fun s11 ⟨k11, e11⟩ => ?_
  have hs11 := k11.scr hs10
  rw [WP.block_append_iff]
  refine WP.mono (subE hs11 13 11 12 ⟨by decide, by decide⟩) fun s12 ⟨k12, e12⟩ => ?_
  have hs12 := k12.scr hs11
  rw [WP.block_append_iff]
  refine WP.mono (subE hs12 6 14 15 ⟨by decide, by decide⟩) fun s13 ⟨k13, e13⟩ => ?_
  have hs13 := k13.scr hs12
  rw [WP.block_append_iff]
  refine WP.mono (addE hs13 5 14 15 ⟨by decide, by decide⟩) fun s14 ⟨k14, e14⟩ => ?_
  have hs14 := k14.scr hs13
  rw [WP.block_append_iff]
  refine WP.mono (a24E hf hs14 4 13 ⟨by decide, by decide⟩) fun s15 ⟨k15, e15⟩ => ?_
  have hs15 := k15.scr hs14
  rw [WP.block_append_iff]
  refine WP.mono (sqrE hf hs15 6 6 ⟨by decide, by decide⟩) fun s16 ⟨k16, e16⟩ => ?_
  have hs16 := k16.scr hs15
  rw [WP.block_append_iff]
  refine WP.mono (sqrE hf hs16 5 5 ⟨by decide, by decide⟩) fun s17 ⟨k17, e17⟩ => ?_
  have hs17 := k17.scr hs16
  rw [WP.block_append_iff]
  refine WP.mono (addE hs17 4 11 4 ⟨by decide, by decide⟩) fun s18 ⟨k18, e18⟩ => ?_
  have hs18 := k18.scr hs17
  rw [WP.block_append_iff]
  refine WP.mono (mulE hf hs18 6 2 6 ⟨by decide, by decide⟩) fun s19 ⟨k19, e19⟩ => ?_
  have hs19 := k19.scr hs18
  rw [WP.block_append_iff]
  refine WP.mono (mulE hf hs19 3 11 12 ⟨by decide, by decide⟩) fun s20 ⟨k20, e20⟩ => ?_
  have hs20 := k20.scr hs19
  refine WP.mono (mulE hf hs20 4 13 4 ⟨by decide, by decide⟩) fun s21 ⟨k21, e21⟩ => ?_
  refine ⟨(k2.trans (k3.trans (k4.trans (k5.trans (k6.trans (k7.trans (k8.trans (k9.trans (k10.trans (k11.trans (k12.trans (k13.trans (k14.trans (k15.trans (k16.trans (k17.trans (k18.trans (k19.trans (k20.trans k21))))))))))))))))))), ?_⟩
  rw [e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2]
  rfl

/-- The ladder's loop invariant, with the counter `rbx = n`: the slots
`x1, x2, z2, x3, z3` (2–6) and the word `swap` hold the ladder's state after
the bits 254 down to `n`, and since the loop's start (`s₀`) nothing else
changed but the registers `clob` and the bytes `[64, 648)`. -/
structure LInv (base : Addr) (k : Nat) (u : Spec.X25519.Fe) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → s.gpr r = s₀.gpr r
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base 64 584 s₀.mem s.mem
  x1 : E s.mem base 2 = u
  x2 : E s.mem base 3 = (ladderAfter k u n).x2
  z2 : E s.mem base 4 = (ladderAfter k u n).z2
  x3 : E s.mem base 5 = (ladderAfter k u n).x3
  z3 : E s.mem base 6 = (ladderAfter k u n).z3
  swap : word s.mem base SWAP = BitVec.ofNat 64 (ladderAfter k u n).swap

theorem cswap_fst (sw : Nat) (a b : Spec.X25519.Fe) :
    (Spec.X25519.cswap sw a b).1 = if decide (sw = 1) = true then b else a := by
  simp only [Spec.X25519.cswap, decide_eq_true_eq]; split <;> rfl

theorem cswap_snd (sw : Nat) (a b : Spec.X25519.Fe) :
    (Spec.X25519.cswap sw a b).2 = if decide (sw = 1) = true then a else b := by
  simp only [Spec.X25519.cswap, decide_eq_true_eq]; split <;> rfl

/-- The slots of the ladder's variables after an iteration's field operations
are those of `ladderStep`. -/
theorem stepEnv_eval (e : Env) (st : Spec.X25519.Ladder) (k : Nat) (u : Spec.X25519.Fe) (t : Nat)
    (h2 : e 2 = u) (h3 : e 3 = st.x2) (h4 : e 4 = st.z2) (h5 : e 5 = st.x3) (h6 : e 6 = st.z3) :
    stepEnv (decide (st.swap ^^^ bit k t = 1)) e 2 = u ∧
    stepEnv (decide (st.swap ^^^ bit k t = 1)) e 3 = (Spec.X25519.ladderStep k u st t).x2 ∧
    stepEnv (decide (st.swap ^^^ bit k t = 1)) e 4 = (Spec.X25519.ladderStep k u st t).z2 ∧
    stepEnv (decide (st.swap ^^^ bit k t = 1)) e 5 = (Spec.X25519.ladderStep k u st t).x3 ∧
    stepEnv (decide (st.swap ^^^ bit k t = 1)) e 6 = (Spec.X25519.ladderStep k u st t).z3 := by
  rw [ladderStep_eq]
  simp (config := {decide := true}) only [stepEnv, opMul, opAdd, opSub, opA24, opSwap,
    Function.update_apply, cswap_fst, cswap_snd, h2, h3, h4, h5, h6]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

include hf in
/-- One iteration of the ladder: from the state after the bits down to
`n + 1` to the state after the bits down to `n`. -/
theorem step_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X25519.Fe} {n : Nat} (hn : n < 255)
    (hbits : ∀ t < 255, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t))
    (hi : LInv base k u s₀ s (n + 1)) :
    WP isa (.block (step fld)) s fun s' => LInv base k u s₀ s' n ∧ s'.zf = some (decide (n = 0)) := by
  have hs := hi.scr
  have hbit : s.mem (off base (BITS + n)) = BitVec.ofNat 8 (bit k n) := by
    rw [hi.mem _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)]
    exact hbits n hn
  rw [step_eq, WP.block_append_iff]
  refine WP.mono (stepPre_ok hs hn hi.rbx (by have := bit_le k n; omega)
    (by have := ladderAfter_swap_le k u (n := n + 1) (by omega); omega) hbit hi.swap)
    fun s1 ⟨b1, m1, g1, rd1, wr1, mem1, _, _⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  have o8 : Outside base 640 8 s.mem s1.mem := by
    rw [mem1]; exact writeW_outside _ _ _ (by omega)
  have e1 : E s1.mem base = Function.update (E s.mem base) 20 (F s1.mem base (32 * 20)) :=
    E_update (o := 20) (o8.mono (by omega) (by omega))
  rw [WP.block_append_iff]
  refine WP.mono (ops_ok hf hs1 m1) fun s2 ⟨K, e2⟩ => ?_
  have hs2 := K.scr hs1
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  have zf : (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by
    rw [BitVec.and_self]
    rcases Nat.eq_zero_or_pos n with rfl | h
    · rfl
    · rw [decide_eq_false (by omega)]
      apply beq_false_of_ne
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact absurd this (by simp; omega)
  obtain ⟨v2, v3, v4, v5, v6⟩ := stepEnv_eval (E s1.mem base) (ladderAfter k u (n + 1)) k u n
    (by rw [e1]; exact hi.x1) (by rw [e1]; exact hi.x2) (by rw [e1]; exact hi.z2)
    (by rw [e1]; exact hi.x3) (by rw [e1]; exact hi.z3)
  rw [← ladderAfter_step k u hn, ← e2] at v3 v4 v5 v6
  rw [← e2] at v2
  refine ⟨⟨⟨hs2.rdi, hs2.wr, hs2.nowrap⟩, fun r hr hb => ?_, ?_, ?_, ?_, ?_, v2, v3, v4, v5, v6, ?_⟩,
    ?_⟩
  · have h' : r ∉ [Reg.rbx, .rax, .rdx, .rcx] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hb, fun h => hr (h ▸ by decide), fun h => hr (h ▸ by decide),
        fun h => hr (h ▸ by decide)⟩
    rw [RegUpd.gpr_arithFlags, K.gpr r hr, g1 r h', hi.gpr r hr hb]
  · rw [RegUpd.gpr_arithFlags, K.gpr _ (by decide), b1]
  · rw [RegUpd.rd_arithFlags, K.rd, rd1, hi.rd]
  · rw [RegUpd.wr_arithFlags, K.wr, wr1, hi.wr]
  · rw [RegUpd.mem_arithFlags]
    exact hi.mem.trans ((o8.mono (by omega) (by omega)).trans (K.mem.mono (by omega) (by omega)))
  · rw [RegUpd.mem_arithFlags, K.mem.word (by simp only [SWAP]; omega) (by simp only [SWAP]; omega),
      mem1, ladderAfter_step k u hn]
    simp only [X86_64.word, Mem.readW_writeW_self64]
    rfl
  · rw [RegUpd.zf_arithFlags, K.gpr .rbx (by decide), b1, zf]

include hf in
/-- The ladder's loop, from the counter `n ≥ 1` down to 0. -/
theorem loop_ok {s₀ : State} {base : Addr} {k : Nat} {u : Spec.X25519.Fe}
    (hbits : ∀ t < 255, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 255 → LInv base k u s₀ s n →
      WP isa (.loop (.block (step fld)) .ne) s fun s' => LInv base k u s₀ s' 0 := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := .block (step fld)) (c := .ne)
    (Q := fun s' => LInv base k u s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 255 ∧ LInv base k u s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (step_ok hf (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

include hf in
/-- The ladder: the counter set to 255, then the loop. -/
theorem ladder_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X25519.Fe}
    (hbits : ∀ t < 255, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t))
    (hi : ∀ s', s'.gpr .rbx = BitVec.ofNat 64 255 → (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → LInv base k u s₀ s' 255) :
    WP isa (ladder fld) s fun s' => LInv base k u s₀ s' 0 := by
  refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rbx (.imm 255)]) s (fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 255 ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
    exact ⟨rfl, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩)
    fun s' ⟨h1, h2, h3, h4, h5⟩ => loop_ok hf hbits 255 s' (by omega) (by omega) (hi s' h1 h2 h3 h4 h5))

/-- What a ladder leaves (`ladder`'s, or `vg_x25519_ifma`'s): the slots
`x2, z2, x3, z3` (3–6) and the word `swap` hold the ladder's final state,
and since its start (`s₀`) nothing else changed but the registers `clob` and
`rbx`, and the bytes `[64, 2216)`. -/
structure LPost (base : Addr) (k : Nat) (u : Spec.X25519.Fe) (s₀ s : State) : Prop where
  scr : Scr s base
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base 64 2152 s₀.mem s.mem
  x2 : E s.mem base 3 = (ladderAfter k u 0).x2
  z2 : E s.mem base 4 = (ladderAfter k u 0).z2
  x3 : E s.mem base 5 = (ladderAfter k u 0).x3
  z3 : E s.mem base 6 = (ladderAfter k u 0).z3
  swap : word s.mem base SWAP = BitVec.ofNat 64 (ladderAfter k u 0).swap

theorem LInv.post {base : Addr} {k : Nat} {u : Spec.X25519.Fe} {s₀ s : State} (h : LInv base k u s₀ s 0) :
    LPost base k u s₀ s :=
  ⟨h.scr, h.gpr, h.rd, h.wr, h.mem.mono (by decide) (by decide), h.x2, h.z2, h.x3, h.z3, h.swap⟩

/-- What a ladder starts from: the bits of `k` in `BITS`, `x1 = u` and the
ladder's first state in the slots 2–6, and `swap = 0`. -/
structure LPre (base : Addr) (k : Nat) (u : Spec.X25519.Fe) (s : State) : Prop where
  scr : Scr s base
  bits : ∀ t < 255, s.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t)
  x1 : E s.mem base 2 = u
  x2 : E s.mem base 3 = 1
  z2 : E s.mem base 4 = 0
  x3 : E s.mem base 5 = u
  z3 : E s.mem base 6 = 1
  swap : word s.mem base SWAP = 0

include hf in
/-- `ladder`, as a ladder: from `LPre` to `LPost`. -/
theorem ladder_post {s : State} {base : Addr} {k : Nat} {u : Spec.X25519.Fe} (h : LPre base k u s) :
    WP isa (ladder fld) s (LPost base k u s) :=
  WP.mono (ladder_ok hf h.bits fun s' hb g m rd wr => ⟨⟨by rw [g _ (by decide)]; exact h.scr.rdi,
      by rw [wr]; exact h.scr.wr, h.scr.nowrap⟩, fun r _ hr => g r hr, hb, rd, wr,
      by rw [m]; exact Outside.refl _ _ _ _, by rw [m, h.x1], by rw [m, h.x2]; rfl, by rw [m, h.z2]; rfl,
      by rw [m, h.x3]; rfl, by rw [m, h.z3]; rfl, by rw [m, h.swap]; rfl⟩)
    fun _ hl => hl.post

end VG.Proof.X25519.X86_64
