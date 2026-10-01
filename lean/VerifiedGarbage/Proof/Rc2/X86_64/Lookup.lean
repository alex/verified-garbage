import VerifiedGarbage.Impl.Rc2.X86_64.Lookup
import VerifiedGarbage.Proof.Rc2.Select
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! # Correctness of baseline x86-64 RC2 lookup steps -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

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

theorem byte_imm (b : Byte) : (b.setWidth 32).signExtend 64 = b.setWidth 64 := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · simp
  · simp [BitVec.msb_setWidth]

theorem index_imm (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 32 i).signExtend 64 = (BitVec.ofNat 8 i).setWidth 64 := by
  have h : BitVec.ofNat 32 i = (BitVec.ofNat 8 i).setWidth 32 := by bv_omega
  rw [h, byte_imm]

/-- SUB followed by SBB of a register from itself selects equality. -/
theorem borrowMask_eq (x y : BitVec 8) :
    (0 - (BitVec.ofBool ((x.setWidth 64 ^^^ y.setWidth 64).toNat < 1)).setWidth 64 : BitVec 64) =
      if x = y then BitVec.allOnes 64 else 0 := by
  have he : ((x.setWidth 64 ^^^ y.setWidth 64).toNat < 1) ↔ x = y := by
    rw [Nat.lt_one_iff]
    have hz : (x.setWidth 64 ^^^ y.setWidth 64).toNat = 0 ↔
        x.setWidth 64 ^^^ y.setWidth 64 = 0#64 := by
      constructor
      · intro h
        apply BitVec.eq_of_toNat_eq
        exact h
      · intro h; rw [h]; rfl
    rw [hz, BitVec.xor_eq_zero_iff]
    constructor
    · intro h
      have h' := congrArg (BitVec.setWidth 8) h
      simpa using h'
    · exact congrArg (BitVec.setWidth 64)
  by_cases h : x = y
  · rw [ite_eq_left h]
    have hb : decide ((x.setWidth 64 ^^^ y.setWidth 64).toNat < 1) = true := by
      exact decide_eq_true (he.mpr h)
    rw [hb]
    decide
  · rw [ite_eq_right h]
    have hb : decide ((x.setWidth 64 ^^^ y.setWidth 64).toNat < 1) = false := by
      exact decide_eq_false (mt he.mp h)
    rw [hb]
    decide

theorem piStep_ok (s : State) (x : Byte) (hx : s.gpr .rax = x.setWidth 64)
    (i : Nat) (hi : i < 256) :
    ∃ s', runBlock isa (piStep i) s = some s' ∧
      s'.gpr .rcx = s.gpr .rcx |||
        (if x.toNat = i then (Spec.Rc2.piTable.getD i 0).setWidth 64 else 0) ∧
      Keep [.rcx, .r10, .r11] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [piStep, selectMask, rr, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, cf_setReg, cf_arithFlags,
      ite_true, ite_false]
    rfl, ?_⟩
  have he : x = BitVec.ofNat 8 i ↔ x.toNat = i := by
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
    · intro h; rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    simp only [BitVec.sub_self]
    rw [hx, index_imm i hi, byte_imm]
    change s.gpr .rcx |||
      ((0 - (BitVec.ofBool ((x.setWidth 64 ^^^ (BitVec.ofNat 8 i).setWidth 64).toNat < 1)).setWidth 64) &&&
        (Spec.Rc2.piTable.getD i 0).setWidth 64) = _
    rw [borrowMask_eq]
    by_cases h : x.toNat = i
    · rw [ite_eq_left (he.mpr h), ite_eq_left h, BitVec.allOnes_and]
    · simp [h, mt he.mp h]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem piSteps_ok (is : List Nat) (hi : ∀ i ∈ is, i < 256)
    (s : State) (x : Byte) (hx : s.gpr .rax = x.setWidth 64) :
    WP isa (.block (is.flatMap piStep)) s (fun s' =>
      s'.gpr .rcx = s.gpr .rcx |||
        (if x.toNat ∈ is then (Spec.Rc2.piTable.getD x.toNat 0).setWidth 64 else 0) ∧
      Keep [.rcx, .r10, .r11] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := piStep_ok s x hx i (hi i (by simp))
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have hx₁ := (keep₁.reg .rax (by decide)).trans hx
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

theorem piStart_ok (s : State) :
    ∃ s', runBlock isa [.alu .and .rax (.imm 255), imm .rcx 0] s = some s' ∧
      s'.gpr .rax = ((s.gpr .rax).setWidth 8).setWidth 64 ∧ s'.gpr .rcx = 0 ∧
      Keep [.rax, .rcx, .r10, .r11] s s' := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    exact maskByte _
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, ite_false]
    · exact mem_setReg _ _ _
    · exact rd_setReg _ _ _
    · exact wr_setReg _ _ _

theorem piLookup_ok (s : State) :
    WP isa (.block piLookup) s (fun s' =>
      s'.gpr .rax = (Spec.Rc2.pi ((s.gpr .rax).setWidth 8)).setWidth 64 ∧
      Keep [.rax, .rcx, .r10, .r11] s s') := by
  rw [piLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, keep₁⟩ := piStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  apply WP.mono (piSteps_ok (List.range 256) (fun i hi => List.mem_range.mp hi)
    s₁ ((s.gpr .rax).setWidth 8) input₁)
  intro s₂ h₂
  have out₂ : s₂.gpr .rcx = (Spec.Rc2.pi ((s.gpr .rax).setWidth 8)).setWidth 64 := by
    rw [h₂.1, zero₁]
    simp only [List.mem_range]
    rw [ite_eq_left ((s.gpr .rax).setWidth 8).isLt]
    exact BitVec.zero_or
  refine WP.of_runBlock ⟨s₂.setReg .rax (s₂.gpr .rcx), ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
  · constructor
    · rw [gpr_setReg_self, out₂]
    · have k₂ : Keep [.rax, .rcx, .r10, .r11] s₁ s₂ := h₂.2.weaken (by
        intro r hr; exact List.mem_cons_of_mem _ hr)
      apply (keep₁.trans k₂).trans
      constructor
      · intro r hr
        exact gpr_setReg_of_ne _ _ (fun h => hr (h ▸ List.mem_cons_self))
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _

theorem offset_nat (i : Nat) : BitVec.ofInt 64 (Int.ofNat i) = BitVec.ofNat 64 i := by
  rfl

theorem keyStep_ok (s : State) (x : Byte) (hx : s.gpr .rax = x.setWidth 64)
    (i : Nat) (hi : i < 64)
    (hlo : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (2 * i)) 1)
    (hhi : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (2 * i + 1)) 1) :
    ∃ s', runBlock isa (keyStep i) s = some s' ∧
      s'.gpr .rcx = s.gpr .rcx |||
        (if x.toNat = i then
          ((s.mem (s.gpr .rdi + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
            (s.mem (s.gpr .rdi + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8).setWidth 64
          else 0) ∧
      Keep [.rcx, .r8, .r9, .r10, .r11] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [keyStep, selectMask, loadKey, rr, memOp,
      List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, execShift, readSrc, State.load8, State.ea, offset_nat,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, cf_setReg, cf_arithFlags, gpr_setFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags,
      wr_setReg, wr_arithFlags, hlo, hhi, ite_true, ite_false]
    rfl, ?_⟩
  have he : x = BitVec.ofNat 8 i ↔ x.toNat = i := by
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · intro h; rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    simp only [BitVec.sub_self]
    rw [hx, index_imm i (by omega)]
    change s.gpr .rcx |||
      (((s.mem (s.gpr .rdi + BitVec.ofNat 64 (2 * i))).setWidth 64 |||
        ((s.mem (s.gpr .rdi + BitVec.ofNat 64 (2 * i + 1))).setWidth 64).rotateRight 56) &&&
        (0 - (BitVec.ofBool ((x.setWidth 64 ^^^ (BitVec.ofNat 8 i).setWidth 64).toNat < 1)).setWidth 64)) = _
    rw [borrowMask_eq, joinBytes]
    by_cases h : x.toNat = i
    · rw [ite_eq_left (he.mpr h), ite_eq_left h, BitVec.and_allOnes]
    · simp [h, mt he.mp h]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem keySteps_ok (is : List Nat) (hi : ∀ i ∈ is, i < 64)
    (s : State) (x : Byte) (hx : s.gpr .rax = x.setWidth 64)
    (readable : ∀ i < 128,
      InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 i) 1) :
    WP isa (.block (is.flatMap keyStep)) s (fun s' =>
      s'.gpr .rcx = s.gpr .rcx |||
        (if x.toNat ∈ is then
          ((s.mem (s.gpr .rdi + BitVec.ofNat 64 (2 * x.toNat))).setWidth 16 |||
            (s.mem (s.gpr .rdi + BitVec.ofNat 64 (2 * x.toNat + 1))).setWidth 16 <<< 8).setWidth 64
          else 0) ∧ Keep [.rcx, .r8, .r9, .r10, .r11] s s') := by
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
    have hx₁ := (keep₁.reg .rax (by decide)).trans hx
    have ptr₁ := keep₁.reg .rdi (by decide)
    have read₁ : ∀ j < 128,
        InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 j) 1 := by
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

theorem maskIndex (x : BitVec 64) :
    x &&& 63 = (x.setWidth 6).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 6 - 1) = x.toNat % 64 % 18446744073709551616
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem keyStart_ok (s : State) :
    ∃ s', runBlock isa [.alu .and .rax (.imm 63), imm .rcx 0] s = some s' ∧
      s'.gpr .rax = ((s.gpr .rax).setWidth 6).setWidth 64 ∧ s'.gpr .rcx = 0 ∧
      Keep [.rax, .rcx, .r8, .r9, .r10, .r11] s s' := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    exact maskIndex _
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, ite_false]
    · exact mem_setReg _ _ _
    · exact rd_setReg _ _ _
    · exact wr_setReg _ _ _

theorem scheduleAt_getD (m : Mem) (p : Addr) (i : Nat) (hi : i < 64) :
    (Spec.Rc2.scheduleAt m p).getD i 0 =
      (m (p + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (p + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  simp [Spec.Rc2.scheduleAt, Vector.getD, hi]

theorem keyLookup_ok (s : State)
    (readable : ∀ i < 128,
      InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 i) 1) :
    WP isa (.block keyLookup) s (fun s' =>
      s'.gpr .rax = ((Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)).getD
        ((s.gpr .rax).setWidth 6).toNat 0).setWidth 64 ∧
      Keep [.rax, .rcx, .r8, .r9, .r10, .r11] s s') := by
  rw [keyLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, keep₁⟩ := keyStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have ptr₁ := keep₁.reg .rdi (by decide)
  have read₁ : ∀ i < 128,
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 i) 1 := by
    rw [keep₁.rd, keep₁.wr, ptr₁]
    exact readable
  have inputByte : s₁.gpr .rax = (((s.gpr .rax).setWidth 6).setWidth 8).setWidth 64 := by
    rw [input₁]; simp
  apply WP.mono (keySteps_ok (List.range 64) (fun i hi => List.mem_range.mp hi)
    s₁ (((s.gpr .rax).setWidth 6).setWidth 8) inputByte read₁)
  intro s₂ h₂
  have out₂ : s₂.gpr .rcx = ((Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)).getD
      ((s.gpr .rax).setWidth 6).toNat 0).setWidth 64 := by
    rw [h₂.1, zero₁, keep₁.mem, ptr₁]
    simp only [List.mem_range, BitVec.toNat_setWidth]
    have bound := ((s.gpr .rax).setWidth 6).isLt
    simp only [BitVec.toNat_setWidth] at bound
    rw [Nat.mod_eq_of_lt (show (s.gpr .rax).toNat % 64 < 256 by omega),
      ite_eq_left bound, scheduleAt_getD _ _ _ bound]
    exact BitVec.zero_or
  refine WP.of_runBlock ⟨s₂.setReg .rax (s₂.gpr .rcx), ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
  · constructor
    · rw [gpr_setReg_self, out₂]
    · have k₂ : Keep [.rax, .rcx, .r8, .r9, .r10, .r11] s₁ s₂ := h₂.2.weaken (by
        intro r hr; exact List.mem_cons_of_mem _ hr)
      apply (keep₁.trans k₂).trans
      constructor
      · intro r hr
        exact gpr_setReg_of_ne _ _ (fun h => hr (h ▸ List.mem_cons_self))
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _

end VG.Proof.Rc2.X86_64
