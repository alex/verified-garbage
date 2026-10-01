import VerifiedGarbage.Proof.Rc2.X86.KeySteps

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86 VG.Proof.Rc2.Word32

theorem addr_eq_def (x : BitVec 32) : addr32 x = x.setWidth 64 := rfl

theorem keyStep_ok (s : State) (x : Byte) (hx : s.gpr .eax = x.setWidth 32)
    (i : Nat) (hi : i < 64)
    (fit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (hlo : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * i)) 1)
    (hhi : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * i + 1)) 1) :
    ∃ s', runBlock isa (keyStep i) s = some s' ∧
      s'.gpr .ebx = s.gpr .ebx |||
        (if x.toNat = i then
          ((s.mem (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
            (s.mem (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8).setWidth 32
          else 0) ∧
      Keep [.ebx, .ecx, .esi, .edx] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [keyStep, selectMask, loadKey, rr, memOp,
      List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, execShift, readSrc, State.load8, State.ea, ← addr_eq_def, addr_add (by omega : (s.gpr .edi).toNat + 2 * i < 2 ^ 32),
      addr_add (by omega : (s.gpr .edi).toNat + (2 * i + 1) < 2 ^ 32),
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, gpr_setFlags,
      mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags,
      wr_setReg, wr_arithFlags, wr_setFlags, hlo, hhi, ite_true, ite_false]
    rfl, ?_⟩
  have he : x = BitVec.ofNat 8 i ↔ x.toNat = i := by
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · intro h; rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
    rw [hx, index_imm i (by omega)]
    rw [mask_neg]
    change s.gpr .ebx |||
      (((s.mem (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * i))).setWidth 32 |||
        ((s.mem (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * i + 1))).setWidth 32).rotateRight 24) &&&
        (0 - (((x.setWidth 32 ^^^ (BitVec.ofNat 8 i).setWidth 32) - 1) >>> 31))) = _
    rw [Word32.selectMask_eq, Word32.joinBytes]
    by_cases h : x.toNat = i
    · rw [ite_eq_left (he.mpr h), ite_eq_left h, BitVec.and_allOnes]
    · simp [h, mt he.mp h]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

theorem keySteps_ok (is : List Nat) (hi : ∀ i ∈ is, i < 64)
    (s : State) (x : Byte) (hx : s.gpr .eax = x.setWidth 32)
    (fit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ i < 128,
      InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1) :
    WP isa (.block (is.flatMap keyStep)) s (fun s' =>
      s'.gpr .ebx = s.gpr .ebx |||
        (if x.toNat ∈ is then
          ((s.mem (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * x.toNat))).setWidth 16 |||
            (s.mem (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * x.toNat + 1))).setWidth 16 <<< 8).setWidth 32
          else 0) ∧ Keep [.ebx, .ecx, .esi, .edx] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    have bound := hi i (by simp)
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := keyStep_ok s x hx i bound fit
      (readable (2 * i) (by omega)) (readable (2 * i + 1) (by omega))
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have hx₁ := (keep₁.reg .eax (by decide)).trans hx
    have ptr₁ := keep₁.reg .edi (by decide)
    have read₁ : ∀ j < 128,
        InRegions (s₁.rd ++ s₁.wr) (addr32 (s₁.gpr .edi) + BitVec.ofNat 64 j) 1 := by
      rw [keep₁.rd, keep₁.wr, ptr₁]
      exact readable
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ hx₁ (by rw [ptr₁]; exact fit) read₁)
    intro s₂ h₂
    refine ⟨?_, keep₁.trans h₂.2⟩
    rw [h₂.1, out₁, keep₁.mem, ptr₁]
    by_cases h : x.toNat = i
    · subst i
      by_cases hm : x.toNat ∈ is <;> simp [hm, BitVec.or_assoc]
    · by_cases hm : x.toNat ∈ is <;> simp [h, hm]

theorem maskIndex (x : BitVec 32) :
    x &&& 63 = (x.setWidth 6).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 6 - 1) = x.toNat % 64 % 4294967296
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem keyStart_ok (s : State) :
    ∃ s', runBlock isa [.alu .and .eax (.imm 63), imm .ebx 0] s = some s' ∧
      s'.gpr .eax = ((s.gpr .eax).setWidth 6).setWidth 32 ∧ s'.gpr .ebx = 0 ∧
      Keep [.eax, .ebx, .ecx, .esi, .edx] s s' := by
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
    (fit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ i < 128,
      InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 i) 1) :
    WP isa (.block keyLookup) s (fun s' =>
      s'.gpr .eax = ((Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .edi))).getD
        ((s.gpr .eax).setWidth 6).toNat 0).setWidth 32 ∧
      Keep [.eax, .ebx, .ecx, .esi, .edx] s s') := by
  rw [keyLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, keep₁⟩ := keyStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have ptr₁ := keep₁.reg .edi (by decide)
  have read₁ : ∀ i < 128,
      InRegions (s₁.rd ++ s₁.wr) (addr32 (s₁.gpr .edi) + BitVec.ofNat 64 i) 1 := by
    rw [keep₁.rd, keep₁.wr, ptr₁]
    exact readable
  have inputByte : s₁.gpr .eax = (((s.gpr .eax).setWidth 6).setWidth 8).setWidth 32 := by
    rw [input₁]; simp
  apply WP.mono (keySteps_ok (List.range 64) (fun i hi => List.mem_range.mp hi)
    s₁ (((s.gpr .eax).setWidth 6).setWidth 8) inputByte (by rw [ptr₁]; exact fit) read₁)
  intro s₂ h₂
  have out₂ : s₂.gpr .ebx = ((Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .edi))).getD
      ((s.gpr .eax).setWidth 6).toNat 0).setWidth 32 := by
    rw [h₂.1, zero₁, keep₁.mem, ptr₁]
    simp only [List.mem_range, BitVec.toNat_setWidth]
    have bound := ((s.gpr .eax).setWidth 6).isLt
    simp only [BitVec.toNat_setWidth] at bound
    rw [Nat.mod_eq_of_lt (show (s.gpr .eax).toNat % 64 < 256 by omega),
      ite_eq_left bound, scheduleAt_getD _ _ _ bound]
    exact BitVec.zero_or
  refine WP.of_runBlock ⟨s₂.setReg .eax (s₂.gpr .ebx), ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
  · constructor
    · rw [gpr_setReg_self, out₂]
    · have k₂ : Keep [.eax, .ebx, .ecx, .esi, .edx] s₁ s₂ := h₂.2.weaken (by
        intro r hr; exact List.mem_cons_of_mem _ hr)
      apply (keep₁.trans k₂).trans
      constructor
      · intro r hr
        exact gpr_setReg_of_ne _ _ (fun h => hr (h ▸ List.mem_cons_self))
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _


end VG.Proof.Rc2.X86
