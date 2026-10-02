import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Arith
import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# GHASH with PMULL: the instruction groups

What each group of instructions of `Impl.Gcm.AArch64.Pmull` does to the state,
each proved by one symbolic execution for any registers it is used with, and
what a load and a store of a block are in `Q`.
-/

namespace VG.Proof.Gcm.AArch64.Pmull

open VG VG.AArch64 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)

/-! ## Loads and stores of blocks -/

theorem getLsbD_read (m : Mem) : ∀ (n : Nat) (a : Addr) (i : Nat), i < 8 * n →
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)
  | 0, _, _, h => absurd h (by omega)
  | n + 1, a, i, h => by
    simp only [Mem.read, BitVec.getLsbD_append]
    by_cases hi : i < 8
    · simp [hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · simp only [hi, ite_false]
      rw [getLsbD_read m n (a + 1) (i - 8) (by omega)]
      have e1 : (i - 8) / 8 = i / 8 - 1 := by omega
      have e2 : (i - 8) % 8 = i % 8 := by omega
      rw [e1, e2]
      congr 2
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
      omega

theorem vdword_read16 (m : Mem) (p : Addr) {e : Nat} (he : e < 2) :
    vdword (m.read p 16) e = m.readW (p + BitVec.ofNat 64 (8 * e)) 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, Mem.readW, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and]
  rw [getLsbD_read m 16 p _ (by omega), getLsbD_read m 8 _ i (by omega), Offset.add_add,
    show 8 * e + i / 8 = (64 * e + i) / 8 by omega, show i % 8 = (64 * e + i) % 8 by omega]

/-- A block, loaded and `rev64`ed. -/
theorem ρ_load (m : Mem) (p : Addr) :
    ρ (VRevOp.eval .rev64b (m.read p 16)) = φ (Spec.Gcm.blockAt m p) := by
  rw [ρ, vdword_rev64b _ (by decide), vdword_rev64b _ (by decide), vdword_read16 m p (by decide),
    vdword_read16 m p (by decide), ← blockAt_rev, φ_append]

theorem read_write16 (m : Mem) (p : Addr) (v : BitVec (8 * 16)) : (m.write p 16 v).read p 16 = v :=
  Mem.read_eq_of_bytes fun i hi => by
    simp only [Mem.write, Mem.sub_ofNat_toNat p (show i < 2 ^ 64 by omega), hi, ite_true]

/-- A block as loaded, `rev64`ed and stored. -/
theorem φ_store (m : Mem) (p : Addr) (v : BitVec 128) :
    φ (Spec.Gcm.blockAt (m.write p 16 (VRevOp.eval .rev64b v)) p) = ρ v := by
  rw [← ρ_load, read_write16, rev64b_rev64b]

/-! ## Reading through writes -/

theorem v_setV (s : State) (d : VReg) (x : BitVec 128) (r : VReg) :
    (s.setV d x).v r = if r = d then x else s.v r := rfl

theorem gpr_setV (s : State) (d : VReg) (x : BitVec 128) : (s.setV d x).gpr = s.gpr := rfl
theorem mem_setV (s : State) (d : VReg) (x : BitVec 128) : (s.setV d x).mem = s.mem := rfl
theorem rd_setV (s : State) (d : VReg) (x : BitVec 128) : (s.setV d x).rd = s.rd := rfl
theorem wr_setV (s : State) (d : VReg) (x : BitVec 128) : (s.setV d x).wr = s.wr := rfl
theorem sp_setV (s : State) (d : VReg) (x : BitVec 128) : (s.setV d x).sp = s.sp := rfl

/-- `s'` differs from `s` at most in the vector registers `rs`. -/
structure VOnly (rs : List VReg) (s s' : State) : Prop where
  v : ∀ r, r ∉ rs → s'.v r = s.v r
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem VOnly.trans {rs rs' : List VReg} {s s' s'' : State} (h : VOnly rs s s')
    (h' : VOnly rs' s' s'') : VOnly (rs ++ rs') s s'' :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    exact (h'.v r hr.2).trans (h.v r hr.1),
   h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem VOnly.weaken {rs rs' : List VReg} {s s' : State} (h : VOnly rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : VOnly rs' s s' :=
  ⟨fun r hr => h.v r fun h' => hr (hs r h'), h.gpr, h.mem, h.rd, h.wr, h.sp⟩

theorem VOnly.refl (rs : List VReg) (s : State) : VOnly rs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The groups -/

/-- The product registers. -/
def prod (s : State) : Prod := ⟨s.v LO, s.v MID, s.v HI⟩

theorem VOnly.prod {rs : List VReg} {s s' : State} (h : VOnly rs s s') (h3 : VReg.v3 ∉ rs)
    (h4 : VReg.v4 ∉ rs) (h5 : VReg.v5 ∉ rs) : Pmull.prod s' = Pmull.prod s := by
  simp only [Pmull.prod, h.v _ h3, h.v _ h4, h.v _ h5]

/-- A register `acc` only reads. -/
def Free (r : VReg) : Prop := r ≠ .v3 ∧ r ≠ .v4 ∧ r ≠ .v5 ∧ r ≠ .v7

theorem exec_pmull0 (d n m : VReg) (s : State) :
    exec (.vop (.pmull false d n m)) s =
      some (s.setV d (polyMul (vdword (s.v n) 0) (vdword (s.v m) 0))) := rfl

theorem exec_pmull1 (d n m : VReg) (s : State) :
    exec (.vop (.pmull true d n m)) s =
      some (s.setV d (polyMul (vdword (s.v n) 1) (vdword (s.v m) 1))) := rfl

theorem exec_eor (d n m : VReg) (s : State) :
    exec (.vop (.logic .eor d n m)) s = some (s.setV d (s.v n ^^^ s.v m)) := rfl

theorem exec_ext8 (d n m : VReg) (s : State) :
    exec (.vop (.ext d n m 8)) s = some (s.setV d (ext8 (s.v n) (s.v m))) := rfl

theorem exec_movi0 (d : VReg) (s : State) : exec (.vop (.movi0 d)) s = some (s.setV d 0) := rfl

theorem exec_rev64b (d n : VReg) (s : State) :
    exec (.vop (.rev .rev64b d n)) s = some (s.setV d (VRevOp.eval .rev64b (s.v n))) := rfl

theorem exec_ldrq {t : VReg} {n : Reg} {off : Nat} {s : State} (ho : off % 16 = 0)
    (ho' : off < 4096 * 16) (hin : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec, addr, ho, ho', and_self, ite_true, Option.bind_some, State.load, hin,
    Option.map_some]

theorem zero_ok (s : State) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.zero) s fun s' =>
      prod s' = Prod.zero ∧ VOnly [LO, MID, HI] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.zero, runBlock_cons, runStep_some, runBlock_nil, exec_movi0,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [prod, v_setV, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2, ite_false]

theorem acc_ok (a sk t : VReg) (s : State) (ha : Free a) (hs : Free sk) (ht : Free t) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.acc a sk t)) s fun s' =>
      prod s' = (prod s).acc (s.v a) (s.v sk) (s.v t) ∧ VOnly [LO, MID, HI, T] s s' := by
  obtain ⟨ha3, ha4, ha5, ha7⟩ := ha
  obtain ⟨-, -, hs5, hs7⟩ := hs
  obtain ⟨ht3, ht4, ht5, ht7⟩ := ht
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.acc, runBlock_cons, runStep_some, runBlock_nil, exec_pmull0,
    exec_pmull1, exec_eor, Option.some.injEq, exists_eq_left', v_setV, ite_true, ite_false,
    reduceCtorEq, ha3, ha4, ha5, ha7, hs5, hs7, ht3, ht4, ht5, ht7]
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [prod, Prod.acc, v_setV, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem reduce_ok (d : VReg) (s : State) (hc : s.v C = ofVDwords poly poly) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.reduce d)) s fun s' =>
      s'.v d = reduce (prod s) ∧ VOnly [LO, MID, HI, T, d] s s' := by
  have hc0 : vdword (ofVDwords poly poly) 0 = poly := vdword_append_0 _ _
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.reduce, runBlock_cons, runStep_some, runBlock_nil,
    exec_pmull0, exec_eor, exec_ext8, Option.some.injEq, exists_eq_left', v_setV, ite_true,
    ite_false, reduceCtorEq, hc]
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [hc0]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- `d ← mul(a, t)` with its halves swapped, a block of class `x · a · t` (`a` as loaded). -/
theorem mul_ok (d a sk t : VReg) (s : State) (ha : Free a) (hs : Free sk) (ht : Free t)
    (hst : s.v sk = ext8 (s.v t) (s.v t)) (hc : s.v C = ofVDwords poly poly) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.mul d a sk t)) s fun s' =>
      ρ (s'.v d) = x * ρ (s.v a) * φ (s.v t) ∧ VOnly [LO, MID, HI, T, d] s s' := by
  rw [Impl.Gcm.AArch64.Pmull.mul, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨p₁, o₁⟩ => ?_
  refine WP.mono (acc_ok a sk t s₁ ha hs ht) fun s₂ ⟨p₂, o₂⟩ => ?_
  have k : ∀ r, r ≠ .v3 → r ≠ .v4 → r ≠ .v5 → r ≠ .v7 → s₂.v r = s.v r := fun r h3 h4 h5 h7 => by
    rw [o₂.v r (by simp [h3, h4, h5, h7]), o₁.v r (by simp [h3, h4, h5])]
  refine WP.mono (reduce_ok d s₂ (by rw [k C (by decide) (by decide) (by decide) (by decide), hc]))
    fun s₃ ⟨p₃, o₃⟩ => ⟨?_, ?_⟩
  · rw [p₃, ρ_reduce, p₂, p₁, o₁.v a (by simp [ha.1, ha.2.1, ha.2.2.1]),
      o₁.v sk (by simp [hs.1, hs.2.1, hs.2.2.1]), o₁.v t (by simp [ht.1, ht.2.1, ht.2.2.1]), hst,
      Prod.val_acc, Prod.val_zero, zero_add]
  · exact (o₁.trans (o₂.trans o₃)).weaken fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h | h) | (h | h | h | h) | (h | h | h | h | h) <;> simp [h]

/-- `ext d, n, n, #8`: the halves of `n`, swapped. -/
theorem swap_ok (d n : VReg) (s : State) :
    WP isa (.block [.vop (.ext d n n 8)]) s fun s' =>
      s'.v d = ext8 (s.v n) (s.v n) ∧ VOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ext8, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [v_setV, ite_true]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [v_setV, hr, ite_false]

/-- A 16-byte load at `[n, #off]`, and `rev64`. -/
theorem ldrev_ok (d : VReg) (n : Reg) (off : Nat) (s : State) (ho : off % 16 = 0)
    (ho' : off < 4096 * 16) (hin : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.loadRev d n off)) s fun s' =>
      ρ (s'.v d) = φ (Spec.Gcm.blockAt s.mem (s.gpr n + BitVec.ofNat 64 off)) ∧ VOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.loadRev, runBlock_cons, runStep_some, runBlock_nil,
    exec_ldrq ho ho' hin, exec_rev64b,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [v_setV, ite_true, ρ_load]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [v_setV, hr, ite_false]

theorem exec_strq {t : VReg} {n : Reg} {off : Nat} {s : State} (ho : off % 16 = 0)
    (ho' : off < 4096 * 16) (hout : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, ho, ho', and_self, ite_true, Option.bind_some, State.store, hout]

/-- `eor d, n, m`. -/
theorem eor_ok (d n m : VReg) (s : State) :
    WP isa (.block [.vop (.logic .eor d n m)]) s fun s' =>
      s'.v d = s.v n ^^^ s.v m ∧ VOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_eor, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [v_setV, ite_true]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [v_setV, hr, ite_false]

/-! ## General-purpose registers and constants -/

theorem v_write (s : State) (sz : Size) (r : Reg) (w : BitVec sz.bits) : (s.write sz r w).v = s.v := rfl
theorem mem_write (s : State) (sz : Size) (r : Reg) (w : BitVec sz.bits) :
    (s.write sz r w).mem = s.mem := rfl
theorem rd_write (s : State) (sz : Size) (r : Reg) (w : BitVec sz.bits) :
    (s.write sz r w).rd = s.rd := rfl
theorem wr_write (s : State) (sz : Size) (r : Reg) (w : BitVec sz.bits) :
    (s.write sz r w).wr = s.wr := rfl

theorem exec_movz_x {d : Reg} {imm : BitVec 16} {hw : Nat} (h : 16 * hw < 64) (s : State) :
    exec (.movz .x d imm hw) s = some (s.write .x d (imm.setWidth 64 <<< (16 * hw))) := by
  simp only [exec, Size.bits, h, ite_true]

theorem exec_dup_d2 (d : VReg) (n : Reg) (s : State) :
    exec (.vop (.dup .d2 d n)) s = some (s.setV d (ofVDwords (s.gpr n) (s.gpr n))) := rfl

theorem exec_ins_d2 {d : VReg} {i : Nat} {n : Reg} (h : i < 2) (s : State) :
    exec (.vop (.ins .d2 d i n)) s = some (s.setV d (setLane (s.v d) 64 i (s.gpr n))) := by
  simp only [exec, VOp.eval, h, ite_true, Option.map_some]

theorem setLane_pair (v : BitVec 128) (a b : BitVec 64) :
    setLane (setLane v 64 0 a) 64 1 b = b ++ a := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [setLane, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_append,
    hj, decide_true, Bool.true_and, Nat.mul_zero, Nat.mul_one, Nat.sub_zero]
  by_cases h : j < 64
  · simp only [h, decide_true, ite_true]
    simp
  · simp only [h, decide_false, ite_false, show j - 64 < 64 by omega, show j - 64 < 128 by omega]
    simp [show 64 ≤ j by omega]

theorem gpr_write_x (s : State) (d : Reg) (w : BitVec 64) (r : Reg) :
    (s.write .x d w).gpr r = if r = d then w else s.gpr r := by
  simp only [RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq]

/-- The reduction constant, zero, and `x⁻²` in both orders. -/
theorem consts_ok (s : State) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.consts) s fun s' =>
      s'.v C = ofVDwords poly poly ∧ s'.v (tReg 2) = xInv2 ∧
      s'.v (sReg 2) = ext8 xInv2 xInv2 ∧
      (∀ r, r ≠ C → r ≠ tReg 2 → r ≠ sReg 2 → s'.v r = s.v r) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.consts, tReg, sReg, runBlock_cons, runStep_some, runBlock_nil,
    exec_movz_x (show 16 * 3 < 64 by decide), exec_movz_x (show 16 * 0 < 64 by decide),
    exec_dup_d2, exec_ins_d2 (show 0 < 2 by decide), exec_ins_d2 (show 1 < 2 by decide),
    v_setV, gpr_setV, v_write, gpr_write_x, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left', setLane_pair, mem_setV, rd_setV, wr_setV, mem_write,
    rd_write, wr_write, and_true]
  refine ⟨by decide, by decide, by rw [ext8_eq]; decide, fun r hc ht hs => ?_,
    fun r h5 h6 h7 => ?_⟩
  · simp only [hc, ht, hs, ite_false]
  · simp only [h5, h6, h7, ite_false]

theorem exec_addImm {d n : Reg} {imm : Nat} (h : imm < 4096) (s : State) :
    exec (.addImm .x d n imm) s = some (s.write .x d (s.gpr n + BitVec.ofNat 64 imm)) := by
  simp only [exec, h, ite_true, State.read, Size.bits, BitVec.setWidth_eq]

theorem exec_subImm {d n : Reg} {imm : Nat} (h : imm < 4096) (s : State) :
    exec (.subImm .x d n imm) s = some (s.write .x d (s.gpr n - BitVec.ofNat 64 imm)) := by
  simp only [exec, h, ite_true, State.read, Size.bits, BitVec.setWidth_eq]

theorem exec_lsr {d n : Reg} {sh : Nat} (h : sh < 64) (s : State) :
    exec (.lsr .x d n sh) s = some (s.write .x d (s.gpr n >>> sh)) := by
  simp only [exec, Size.bits, h, ite_true, State.read, BitVec.setWidth_eq]

/-- Past `k` blocks. -/
theorem advance_ok (k : Nat) (hk : 16 * k < 4096) (s : State) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.advance k)) s fun s' =>
      s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 (16 * k) ∧
      s'.gpr .x3 = s.gpr .x3 - BitVec.ofNat 64 k ∧ s'.gpr .x5 = s'.gpr .x3 >>> 3 ∧
      (∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧ s'.v = s.v ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.advance, runBlock_cons, runStep_some, runBlock_nil,
    exec_addImm hk, exec_subImm (show k < 4096 by omega), exec_lsr (show 3 < 64 by decide),
    gpr_write_x, ite_true,
    ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, fun r h2 h3 h5 => by simp only [h2, h3, h5, ite_false], rfl, rfl, rfl, rfl⟩

/-- `lsr d, n, #sh`. -/
theorem lsr_ok (d n : Reg) (sh : Nat) (hsh : sh < 64) (s : State) :
    WP isa (.block [.lsr .x d n sh]) s fun s' =>
      s'.gpr d = s.gpr n >>> sh ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.v = s.v ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_lsr hsh, gpr_write_x, ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r h => by simp only [h, ite_false], rfl, rfl, rfl, rfl⟩

/-! ## The registers of the powers -/

theorem tReg_free (k : Nat) : Free (tReg k) := by
  unfold tReg Free; split <;> decide

theorem sReg_free (k : Nat) : Free (sReg k) := by
  unfold sReg Free; split <;> decide

/-- The registers of the powers are not those of a block's arithmetic or the constants. -/
theorem tReg_nmem (k : Nat) : tReg k ∉ [LO, MID, HI, A, T, Y, C] := by
  unfold tReg; split <;> decide

theorem sReg_nmem (k : Nat) : sReg k ∉ [LO, MID, HI, A, T, Y, C] := by
  unfold sReg; split <;> decide

theorem tReg_nmem' {rs : List VReg} (k : Nat)
    (hs : ∀ r ∈ rs, r ∈ [LO, MID, HI, A, T, Y, C] := by decide) : tReg k ∉ rs :=
  fun h => tReg_nmem k (hs _ h)

theorem sReg_nmem' {rs : List VReg} (k : Nat)
    (hs : ∀ r ∈ rs, r ∈ [LO, MID, HI, A, T, Y, C] := by decide) : sReg k ∉ rs :=
  fun h => sReg_nmem k (hs _ h)

theorem ne_tReg {r : VReg} (k : Nat) (h : r ∈ [LO, MID, HI, A, T, Y, C] := by decide) :
    r ≠ tReg k :=
  fun e => tReg_nmem k (e ▸ h)

theorem ne_sReg {r : VReg} (k : Nat) (h : r ∈ [LO, MID, HI, A, T, Y, C] := by decide) :
    r ≠ sReg k :=
  fun e => sReg_nmem k (e ▸ h)

theorem tReg_ne_sReg (i j : Nat) : tReg i ≠ sReg j := by
  unfold tReg sReg; split <;> split <;> decide

theorem tReg_inj : ∀ i < 9, ∀ j < 9, 1 ≤ i → 1 ≤ j → tReg i = tReg j → i = j := by decide

theorem sReg_inj : ∀ i < 9, ∀ j < 9, 1 ≤ i → 1 ≤ j → sReg i = sReg j → i = j := by decide

end VG.Proof.Gcm.AArch64.Pmull
