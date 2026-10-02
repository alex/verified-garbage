import VerifiedGarbage.Proof.Aes.Arm.Ctr32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Impl.CmacAes.Arm

/-!
# AES-CMAC on ARMv7: calling `vg_aes_ctr32` on one block

`ctr_call`: the frame that pushes `vg_aes_ctr32`'s stack arguments (`n = 1`
in `ra` and the working space `S` in `rb`) around its call, with the counter
block `C` and one data block `D` holding zeros: `D` then holds `CIPH_K(C)`, as
bytes (`Cmac.aesWith`), and only `C`, `D`, `S` and the 8 bytes below the stack
pointer change in memory.
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm

theorem ofBytes_zeros : Spec.Gcm.ofBytes (Spec.Cmac.zeros 16) = 0 := by decide

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 32 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem storeWords_two (m : Mem) (a : BitVec 32) (x y : BitVec 32) :
    storeWords m a [x, y] = (m.writeW (State.addr a) x).writeW (State.addr (a + 4)) y := rfl

/-- Addresses below a pointer do not wrap. -/
theorem addr_sub {a : BitVec 32} {k : Nat} (h : k ≤ a.toNat) :
    State.addr (a - BitVec.ofNat 32 k) = State.addr a - BitVec.ofNat 64 k := by
  simp only [State.addr]
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt (a := a.toNat) (by omega)]
  omega

/-- The 8 bytes below the stack pointer, where the frame pushes the stack arguments. -/
abbrev below (s : State) : Region := ⟨State.addr s.sp - 8, 8⟩

/-- What a call of `vg_aes_ctr32` on one block needs. -/
structure CallPre (s : State) (W C D S : BitVec 32) (R : Nat) (ra rb : Reg) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = C
  r3 : s.gpr .r3 = D
  hra : s.gpr ra = 1
  hrb : s.gpr rb = S
  regs : regList [ra, rb] = true
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hsp : 8 ≤ s.sp.toNat
  wc : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  wd : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr D, 16⟩
  ws : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  cd : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr D, 16⟩
  cs : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  ds : (⟨State.addr D, 16⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  bw : (below s).Disjoint ⟨State.addr W, 240⟩
  bc : (below s).Disjoint ⟨State.addr C, 16⟩
  bd : (below s).Disjoint ⟨State.addr D, 16⟩
  bs : (below s).Disjoint ⟨State.addr S, 2048⟩
  hW : W.toNat + 240 ≤ 2 ^ 32
  hC : C.toNat + 16 ≤ 2 ^ 32
  hD : D.toNat + 16 ≤ 2 ^ 32
  hS : S.toNat + 2048 ≤ 2 ^ 32
  reads : Covers [⟨State.addr W, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 16⟩, ⟨State.addr D, 16⟩, ⟨State.addr S, 2048⟩] s.wr
  zero : Spec.Aes.bytesAt s.mem (State.addr D) 16 = Spec.Cmac.zeros 16

/-- What a call of `vg_aes_ctr32` on one block leaves. -/
structure CallPost (s : State) (W C D S : BitVec 32) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 16⟩, ⟨State.addr D, 16⟩, ⟨State.addr S, 2048⟩, below s] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (State.addr D) 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (State.addr W) (16 * (R + 1)))
      (Spec.Aes.bytesAt s.mem (State.addr C) 16)

theorem e8 (ra rb : Reg) : BitVec.ofNat 32 (4 * [ra, rb].length) = 8 := rfl

/-- The regions `vg_aes_ctr32` is called with. -/
abbrev ctrRd (s : State) (W : BitVec 32) : List Region := [⟨State.addr W, 240⟩, below s]
abbrev ctrWr (C D S : BitVec 32) : List Region :=
  [⟨State.addr C, 16⟩, ⟨State.addr D, 16⟩, ⟨State.addr S, 2048⟩]

/-- The state `vg_aes_ctr32` runs from, with the permissions it is given. -/
abbrev ctrView (s : State) (ra rb : Reg) (W C D S : BitVec 32) : State :=
  (pushed [ra, rb] s).callEntry.withRegions (ctrRd s W) (ctrWr C D S)

namespace CallPre
variable {s : State} {W C D S : BitVec 32} {R : Nat} {ra rb : Reg} (h : CallPre s W C D S R ra rb)
include h

theorem hA : State.addr (s.sp - 8) = State.addr s.sp - 8 := addr_sub h.hsp

theorem hspA : (s.sp - 8).toNat = s.sp.toNat - 8 :=
  BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact h.hsp)

theorem hA4 : State.addr (s.sp - 8 + BitVec.ofNat 32 4) = State.addr s.sp - 8 + 4 := by
  have := s.sp.isLt
  rw [addr_add (by rw [h.hspA]; omega), h.hA]; rfl

theorem amem : (pushed [ra, rb] s).mem =
    (s.mem.writeW (State.addr s.sp - 8) (1 : BitVec 32)).writeW (State.addr s.sp - 8 + 4) S := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [ra, rb].length)) [s.gpr ra, s.gpr rb] = _
  rw [e8, storeWords_two, h.hA, show (s.sp - 8 + 4 : BitVec 32) = s.sp - 8 + BitVec.ofNat 32 4 from rfl, h.hA4,
    h.hra, h.hrb]

theorem fA : Frame [below s] s.mem (pushed [ra, rb] s).mem := by
  rw [h.amem]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left]; decide

omit h in
theorem sp_view : (ctrView s ra rb W C D S).sp = s.sp - 8 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, e8]

theorem arg0 : stackArg (ctrView s ra rb W C D S) 0 = 1 := by
  have := h.hsp
  rw [stackArg, show stackArgAddr (ctrView s ra rb W C D S) 0 = State.addr s.sp - 8 by
      unfold stackArgAddr; rw [sp_view, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from
        BitVec.add_zero _, h.hA],
    State.withRegions_mem, State.callEntry_mem, h.amem, Mem.readW_writeW_sep
    (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem arg1 : stackArg (ctrView s ra rb W C D S) 1 = S := by
  rw [stackArg, show stackArgAddr (ctrView s ra rb W C D S) 1 = State.addr s.sp - 8 + 4 by
      unfold stackArgAddr; rw [sp_view]; exact h.hA4,
    State.withRegions_mem, State.callEntry_mem, h.amem, Mem.readW_writeW_self32]

omit h in
theorem view_gpr (r : Reg) (hr : r ∉ linkRegs) : (ctrView s ra rb W C D S).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

theorem pre : Proof.Aes.ctr32Arm.pre (ctrView s ra rb W C D S) := by
  have hR := toNat_rounds h.rounds
  have hsa : stackArgAddr (ctrView s ra rb W C D S) 0 = State.addr s.sp - 8 := by
    unfold stackArgAddr; rw [sp_view, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from
      BitVec.add_zero _, h.hA]
  simp only [Proof.Aes.ctr32Arm, h.arg0, h.arg1, hsa, view_gpr .r0 (by decide), view_gpr .r1 (by decide),
    view_gpr .r2 (by decide), view_gpr .r3 (by decide), h.r0, h.r1, h.r2, h.r3, hR, State.withRegions_rd,
    State.withRegions_wr, sp_view, h.hspA, show (1 : BitVec 32).toNat = 1 from rfl, Nat.mul_one]
  refine ⟨trivial, trivial, h.wc, ?_, h.ws, ?_, h.cs, ?_, h.bc.symm, ?_, h.bs.symm, h.hW, h.hC, ?_, h.hS, ?_,
    h.rounds⟩
  · simpa using h.wd
  · simpa using h.cd
  · simpa using h.ds
  · simpa [below] using h.bd.symm
  · simpa using h.hD
  · have := s.sp.isLt; omega

/-- The stack arguments are the frame. -/
theorem cov : Covers (ctrRd s W ++ ctrWr C D S) ((pushed [ra, rb] s).rd ++ (pushed [ra, rb] s).wr) := by
  intro x n' ⟨r, hr, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨r', hr', hc'⟩ := h.reads x n' ⟨_, List.mem_singleton_self _, hc⟩
    refine ⟨r', ?_, hc'⟩
    rcases List.mem_append.mp hr' with h' | h'
    · exact List.mem_append_left _ h'
    · exact List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ h')
  · refine ⟨_, List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_self ..), ?_⟩
    rwa [e8, h.hA]
  all_goals
    obtain ⟨r', hr', hc'⟩ := h.writes x n' ⟨_, by simp, hc⟩
    exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr'), hc'⟩

theorem covW : Covers (ctrWr C D S) (pushed [ra, rb] s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

end CallPre

theorem ctr_noCalls : Impl.Aes.Arm.ctr32.noCalls = true := by decide +kernel

theorem ctr_call {s : State} {W C D S : BitVec 32} {R : Nat} {ra rb : Reg} (h : CallPre s W C D S R ra rb) :
    WP isa (ctrCall ra rb) s (CallPost s W C D S R) := by
  refine WP.frame (rs := [ra, rb]) (r := ra) h.regs (by simpa using h.hsp) (by simp) ?_
  refine WP.call (k := Proof.Aes.ctr32Arm) Proof.Aes.Arm.ctr32_correct
    (rd := ctrRd s W) (wr := ctrWr C D S) h.pre h.cov h.covW ?_ ctr_noCalls
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  have hR := toNat_rounds h.rounds
  have hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  -- The memory of the frame.
  have fBelow : Frame [⟨State.addr C, 16⟩, ⟨State.addr D, 16⟩, ⟨State.addr S, 2048⟩]
      (pushed [ra, rb] s).mem s₂.mem := hf
  have bytesW : Spec.Aes.bytesAt (pushed [ra, rb] s).mem (State.addr W) (16 * (R + 1)) =
      Spec.Aes.bytesAt s.mem (State.addr W) (16 * (R + 1)) :=
    Proof.Cmac.bytesAt_frame h.fA (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bw.symm.sub_left (Region.sub_prefix hR')).symm.symm) (by omega)
  have bytesC : Spec.Aes.bytesAt (pushed [ra, rb] s).mem (State.addr C) 16 =
      Spec.Aes.bytesAt s.mem (State.addr C) 16 :=
    Proof.Cmac.bytesAt_frame16 h.fA (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bc.symm)
  have bytesD : Spec.Aes.bytesAt (pushed [ra, rb] s).mem (State.addr D) 16 =
      Spec.Aes.bytesAt s.mem (State.addr D) 16 :=
    Proof.Cmac.bytesAt_frame16 h.fA (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bd.symm)
  obtain ⟨hdata, -⟩ := hpost
  simp only [State.withRegions_mem, State.callEntry_mem, CallPre.view_gpr .r0 (by decide),
    CallPre.view_gpr .r1 (by decide), CallPre.view_gpr .r2 (by decide), CallPre.view_gpr .r3 (by decide), h.r0, h.r1, h.r2,
    h.r3, hR, h.arg0, show (1 : BitVec 32).toNat = 1 from rfl] at hdata
  have one : ∀ m : Mem, Spec.Gcm.blocksAt m (State.addr D) 1 = [Spec.Gcm.blockAt m (State.addr D)] :=
    fun m => by simp [Spec.Gcm.blocksAt]
  have bD : Spec.Gcm.blockAt (pushed [ra, rb] s).mem (State.addr D) = 0 := by
    rw [Spec.Gcm.blockAt, bytesD, h.zero, ofBytes_zeros]
  rw [one, one, bD, Proof.Cmac.ctr32_one, List.cons.injEq] at hdata
  -- The register the pop loads is the one pushed.
  have slot : s₂.mem.readW (State.addr (pushed [ra, rb] s).sp) 32 = 1 := by
    rw [pushed_sp, e8, h.hA]
    have := fBelow.readW (r := ⟨State.addr s.sp - 8, 4⟩) (a := State.addr s.sp - 8) (w := 32)
      (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (h.bc.sub_left (Region.sub_prefix (by decide))).symm.symm
      · exact (h.bd.sub_left (Region.sub_prefix (by decide)))
      · exact (h.bs.sub_left (Region.sub_prefix (by decide)))) (by decide)
    rw [this, h.amem, Mem.readW_writeW_sep
      (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, pushed_sp, e8]; exact BitVec.sub_add_cancel _ _
  · by_cases hra : r = ra
    · subst hra
      show (s₂.setReg r (s₂.mem.readW (State.addr s₂.sp) 32)).gpr r = _
      rw [VG.Arm.RegUpd.gpr_setReg_self, hsp₂, slot, h.hra]
    · rw [popped_gpr hra, hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    refine (h.fA.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (fBelow.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem, Proof.Cmac.bytesAt_blockAt, hdata.1, Spec.Gcm.blockAt, bytesW, bytesC,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _)]

/-- Calls of `vg_aes_ctr32` on one block, with the same arguments and stack
pointer in both runs, are constant time. -/
theorem ctr_rel {W C D S sp₀ : BitVec 32} {R : Nat} {ra rb : Reg} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → CallPre s₁ W C D S R ra rb ∧ CallPre s₂ W C D S R ra rb ∧ s₁.sp = sp₀ ∧
      s₂.sp = sp₀) :
    RelCT isa P (ctrCall ra rb) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, h₁, h₂⟩ := h _ _ hp; rw [h₁, h₂]) ?_
  refine RelCT.call Proof.Aes.Arm.ctr32_correct Proof.Aes.Arm.ctr32_ct
    [⟨State.addr W, 240⟩, ⟨State.addr sp₀ - 8, 8⟩] (ctrWr C D S) fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_
  obtain ⟨h₁, h₂, sp₁, sp₂⟩ := h _ _ hp
  rw [push_pushed h₁.regs (by simpa using h₁.hsp), Option.some.injEq] at pa
  rw [push_pushed h₂.regs (by simpa using h₂.hsp), Option.some.injEq] at pb
  subst pa pb
  have e₁ : ctrRd s₁ W = [⟨State.addr W, 240⟩, ⟨State.addr sp₀ - 8, 8⟩] := by rw [ctrRd, below, sp₁]
  have e₂ : ctrRd s₂ W = [⟨State.addr W, 240⟩, ⟨State.addr sp₀ - 8, 8⟩] := by rw [ctrRd, below, sp₂]
  have p₁ := h₁.pre (C := C) (D := D) (S := S)
  have p₂ := h₂.pre (C := C) (D := D) (S := S)
  rw [ctrView, e₁] at p₁
  rw [ctrView, e₂] at p₂
  refine ⟨p₁, p₂, ?_, e₁ ▸ h₁.cov, h₁.covW, e₂ ▸ h₂.cov, h₂.covW⟩
  have a₁ := h₁.arg0 (C := C) (D := D) (S := S)
  have b₁ := h₁.arg1 (C := C) (D := D) (S := S)
  have a₂ := h₂.arg0 (C := C) (D := D) (S := S)
  have b₂ := h₂.arg1 (C := C) (D := D) (S := S)
  rw [ctrView, e₁] at a₁ b₁
  rw [ctrView, e₂] at a₂ b₂
  simp only [Proof.Aes.ctr32Arm, a₁, b₁, a₂, b₂, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, pushed_sp, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), pushed_gpr, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1,
    h₂.r2, h₂.r3, sp₁, sp₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.CmacAes.Arm
