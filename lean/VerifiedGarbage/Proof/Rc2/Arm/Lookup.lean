import VerifiedGarbage.Impl.Rc2.Arm.Lookup
import VerifiedGarbage.Proof.Rc2.Select32
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-! # Correctness of baseline Arm RC2 lookup steps -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

/-- A register-only block preserves memory, regions, and other GPRs. -/
structure Keep (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.trans {rs : List Reg} {s s' s'' : State}
    (h : Keep rs s s') (h' : Keep rs s' s'') : Keep rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem byte_imm (b : Byte) : (BitVec.ofNat 16 b.toNat).setWidth 32 = b.setWidth 32 := by
  simp

theorem index_imm (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 16 i).setWidth 32 = (BitVec.ofNat 8 i).setWidth 32 := by
  have h : BitVec.ofNat 16 i = (BitVec.ofNat 8 i).setWidth 16 := by bv_omega
  rw [h]; simp

theorem piStep_ok (s : State) (x : Byte) (hx : s.gpr .r12 = x.setWidth 32)
    (i : Nat) (hi : i < 256) :
    ∃ s', runBlock isa (piStep i) s = some s' ∧
      s'.gpr .r3 = s.gpr .r3 |||
        (if x.toNat = i then (Spec.Rc2.piTable.getD i 0).setWidth 32 else 0) ∧
      Keep [.r3, .r10, .r11] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [piStep, selectMask, imm, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some, gpr_setReg,
      ite_true, ite_false]
    rfl, ?_⟩
  have he : x = BitVec.ofNat 8 i ↔ x.toNat = i := by
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
    · intro h; rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  constructor
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    rw [hx, index_imm i hi, byte_imm]
    simp only [BitVec.setWidth_zero]
    change s.gpr .r3 |||
      ((0 - (((x.setWidth 32 ^^^ (BitVec.ofNat 8 i).setWidth 32) - 1) >>> 31)) &&&
        (Spec.Rc2.piTable.getD i 0).setWidth 32) = _
    rw [selectMask_eq]
    by_cases h : x.toNat = i
    · rw [ite_eq_left (he.mpr h), ite_eq_left h, BitVec.allOnes_and]
    · simp [h, mt he.mp h]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]
    · simp only [mem_setReg]
    · simp only [rd_setReg]
    · simp only [wr_setReg]


theorem piSteps_ok (is : List Nat) (hi : ∀ i ∈ is, i < 256)
    (s : State) (x : Byte) (hx : s.gpr .r12 = x.setWidth 32) :
    WP isa (.block (is.flatMap piStep)) s (fun s' =>
      s'.gpr .r3 = s.gpr .r3 |||
        (if x.toNat ∈ is then (Spec.Rc2.piTable.getD x.toNat 0).setWidth 32 else 0) ∧
      Keep [.r3, .r10, .r11] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := piStep_ok s x hx i (hi i (by simp))
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have hx₁ := (keep₁.reg .r12 (by decide)).trans hx
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ hx₁)
    intro s₂ h₂
    refine ⟨?_, keep₁.trans h₂.2⟩
    rw [h₂.1, out₁]
    by_cases h : x.toNat = i
    · subst i
      by_cases hm : x.toNat ∈ is <;> simp [hm, BitVec.or_assoc]
    · by_cases hm : x.toNat ∈ is <;> simp [h, hm]

theorem Keep.weaken {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hsub : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.reg r (fun hm => hr (hsub r hm)), h.mem, h.rd, h.wr⟩

theorem maskBits (x : BitVec 32) (n : Nat) (hn : n ≤ 32) :
    x <<< (32 - n) >>> (32 - n) = (x.setWidth n).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  have ha : 32 - n + i < 32 ↔ i < n := by omega
  have hb : ¬32 - n + i < 32 - n := by omega
  simp only [ha, hb, hi, decide_true, decide_false, Bool.not_false,
    Bool.and_true, Bool.true_and, Nat.add_sub_cancel_left]

theorem piStart_ok (s : State) :
    ∃ s', runBlock isa (mask .r12 8 ++ [imm .r3 0]) s = some s' ∧
      s'.gpr .r12 = ((s.gpr .r12).setWidth 8).setWidth 32 ∧ s'.gpr .r3 = 0 ∧
      Keep [.r12, .r3, .r10, .r11] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [mask, imm, List.cons_append, List.nil_append, runBlock_cons,
      exec, Op2.eval]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
    exact maskBits _ 8 (by decide)
  · rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2.1, ite_false]
    · rfl
    · rfl
    · rfl

theorem piLookup_ok (s : State) :
    WP isa (.block piLookup) s (fun s' =>
      s'.gpr .r12 = (Spec.Rc2.pi ((s.gpr .r12).setWidth 8)).setWidth 32 ∧
      Keep [.r12, .r3, .r10, .r11] s s') := by
  rw [piLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, keep₁⟩ := piStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  apply WP.mono (piSteps_ok (List.range 256) (fun i hi => List.mem_range.mp hi)
    s₁ ((s.gpr .r12).setWidth 8) input₁)
  intro s₂ h₂
  have out₂ : s₂.gpr .r3 = (Spec.Rc2.pi ((s.gpr .r12).setWidth 8)).setWidth 32 := by
    rw [h₂.1, zero₁]
    simp only [List.mem_range]
    rw [ite_eq_left ((s.gpr .r12).setWidth 8).isLt]
    exact BitVec.zero_or
  refine WP.of_runBlock ⟨s₂.setReg .r12 (s₂.gpr .r3), ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some, ]
  · constructor
    · rw [gpr_setReg_self, out₂]
    · have k₂ : Keep [.r12, .r3, .r10, .r11] s₁ s₂ := h₂.2.weaken (by
        intro r hr; exact List.mem_cons_of_mem _ hr)
      apply (keep₁.trans k₂).trans
      constructor
      · intro r hr
        exact gpr_setReg_of_ne _ _ (fun h => hr (h ▸ List.mem_cons_self))
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _



theorem keyStep_ok (s : State) (x : Byte) (hx : s.gpr .r12 = x.setWidth 32)
    (i : Nat) (hi : i < 64)
    (hlo : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (2 * i))) 1)
    (hhi : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (2 * i + 1))) 1) :
    ∃ s', runBlock isa (keyStep i) s = some s' ∧
      s'.gpr .r3 = s.gpr .r3 |||
        (if x.toNat = i then
          ((s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 (2 * i)))).setWidth 16 |||
            (s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 (2 * i + 1)))).setWidth 16 <<< 8).setWidth 32
          else 0) ∧
      Keep [.r3, .r8, .r9, .r10, .r11] s s' := by
  have hloOff : 2 * i < 4096 := by omega
  have hhiOff : 2 * i + 1 < 4096 := by omega
  refine ⟨_, by
    simp (config := {decide := true}) only [keyStep, selectMask, loadKey, imm,
      List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, Op2.eval, State.load8,
      Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg,
      wr_setReg,  hloOff, hhiOff, hlo, hhi, ite_true, ite_false]
    rfl, ?_⟩
  have he : x = BitVec.ofNat 8 i ↔ x.toNat = i := by
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · intro h; rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  constructor
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    rw [hx, index_imm i (by omega)]
    change s.gpr .r3 |||
      (((s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 (2 * i)))).setWidth 32 |||
        ((s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 (2 * i + 1)))).setWidth 32).rotateRight 24) &&&
        (0 - (((x.setWidth 32 ^^^ (BitVec.ofNat 8 i).setWidth 32) - 1) >>> 31))) = _
    rw [selectMask_eq, joinBytes]
    by_cases h : x.toNat = i
    · rw [ite_eq_left (he.mpr h), ite_eq_left h, BitVec.and_allOnes]
    · simp [h, mt he.mp h]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
    · simp only [mem_setReg]
    · simp only [rd_setReg]
    · simp only [wr_setReg]

theorem keySteps_ok (is : List Nat) (hi : ∀ i ∈ is, i < 64)
    (s : State) (x : Byte) (hx : s.gpr .r12 = x.setWidth 32)
    (readable : ∀ i < 128,
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 i)) 1) :
    WP isa (.block (is.flatMap keyStep)) s (fun s' =>
      s'.gpr .r3 = s.gpr .r3 |||
        (if x.toNat ∈ is then
          ((s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 (2 * x.toNat)))).setWidth 16 |||
            (s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 (2 * x.toNat + 1)))).setWidth 16 <<< 8).setWidth 32
          else 0) ∧ Keep [.r3, .r8, .r9, .r10, .r11] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    have bound := hi i (by simp)
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := keyStep_ok s x hx i bound
      (readable (2 * i) (by omega)) (readable (2 * i + 1) (by omega))
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have hx₁ := (keep₁.reg .r12 (by decide)).trans hx
    have ptr₁ := keep₁.reg .r0 (by decide)
    have read₁ : ∀ j < 128,
        InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r0 + BitVec.ofNat 32 j)) 1 := by
      rw [keep₁.rd, keep₁.wr, ptr₁]
      exact readable
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ hx₁ read₁)
    intro s₂ h₂
    refine ⟨?_, keep₁.trans h₂.2⟩
    rw [h₂.1, out₁, keep₁.mem, ptr₁]
    by_cases h : x.toNat = i
    · subst i
      by_cases hm : x.toNat ∈ is <;> simp [hm, BitVec.or_assoc]
    · by_cases hm : x.toNat ∈ is <;> simp [h, hm]


theorem keyStart_ok (s : State) :
    ∃ s', runBlock isa (mask .r12 6 ++ [imm .r3 0]) s = some s' ∧
      s'.gpr .r12 = ((s.gpr .r12).setWidth 6).setWidth 32 ∧ s'.gpr .r3 = 0 ∧
      Keep [.r12, .r3, .r8, .r9, .r10, .r11] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [mask, imm, List.cons_append, List.nil_append, runBlock_cons,
      exec, Op2.eval]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
    exact maskBits _ 6 (by decide)
  · rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2.1, ite_false]
    · rfl
    · rfl
    · rfl

theorem scheduleAt_getD (m : Mem) (p : Addr) (i : Nat) (hi : i < 64) :
    (Spec.Rc2.scheduleAt m p).getD i 0 =
      (m (p + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (p + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  simp [Spec.Rc2.scheduleAt, Vector.getD, hi]

theorem keyLookup_ok (s : State) (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ i < 128,
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 i)) 1) :
    WP isa (.block keyLookup) s (fun s' =>
      s'.gpr .r12 = ((Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))).getD
        ((s.gpr .r12).setWidth 6).toNat 0).setWidth 32 ∧
      Keep [.r12, .r3, .r8, .r9, .r10, .r11] s s') := by
  rw [keyLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, keep₁⟩ := keyStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have ptr₁ := keep₁.reg .r0 (by decide)
  have read₁ : ∀ i < 128,
      InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r0 + BitVec.ofNat 32 i)) 1 := by
    rw [keep₁.rd, keep₁.wr, ptr₁]
    exact readable
  have inputByte : s₁.gpr .r12 = (((s.gpr .r12).setWidth 6).setWidth 8).setWidth 32 := by
    rw [input₁]; simp
  apply WP.mono (keySteps_ok (List.range 64) (fun i hi => List.mem_range.mp hi)
    s₁ (((s.gpr .r12).setWidth 6).setWidth 8) inputByte read₁)
  intro s₂ h₂
  have out₂ : s₂.gpr .r3 = ((Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))).getD
      ((s.gpr .r12).setWidth 6).toNat 0).setWidth 32 := by
    rw [h₂.1, zero₁, keep₁.mem, ptr₁]
    simp only [List.mem_range, BitVec.toNat_setWidth]
    have bound := ((s.gpr .r12).setWidth 6).isLt
    simp only [BitVec.toNat_setWidth] at bound
    rw [Nat.mod_eq_of_lt (show (s.gpr .r12).toNat % 64 < 256 by omega),
      ite_eq_left bound, scheduleAt_getD _ _ _ bound]
    rw [addr_add (by omega_using [fit, bound]), addr_add (by omega_using [fit, bound])]
    exact BitVec.zero_or
  refine WP.of_runBlock ⟨s₂.setReg .r12 (s₂.gpr .r3), ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some]
  · constructor
    · rw [gpr_setReg_self, out₂]
    · have k₂ : Keep [.r12, .r3, .r8, .r9, .r10, .r11] s₁ s₂ := h₂.2.weaken (by
        intro r hr; exact List.mem_cons_of_mem _ hr)
      apply (keep₁.trans k₂).trans
      constructor
      · intro r hr
        exact gpr_setReg_of_ne _ _ (fun h => hr (h ▸ List.mem_cons_self))
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _

end VG.Proof.Rc2.Arm
