import VerifiedGarbage.Proof.Blake2.X86.CompressS.Body
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.TCB.X86.Target

/-!
# BLAKE2s on x86 (32-bit): the compression function

`correct`: the prologue, the final block flag, the loop over the blocks
(`body_ok`) and the epilogue meet `compressX86 Spec.Blake2.s`; `τ₀`, `agree₀`:
the start of its taint analysis.
-/

namespace VG.Proof.Blake2.X86.CompressS

open VG VG.X86 VG.X86.Wp
open VG.Spec.Blake2 (HashValue stateAt compressBlocks)
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.CompressS
open VG.Proof.MdStream.X86 (contains_addr readW_writeW_addr)

/-! ## Prologue and epilogue -/

theorem prologue_eq : prologue = [.mov .eax (.mem (at_ .esp 28)), .store (at_ .eax 80) .ebx,
    .store (at_ .eax 84) .esi, .store (at_ .eax 88) .edi, .mov .esi (.reg .eax),
    .mov .edi (.mem (at_ .esp 8)), .mov .eax (.mem (at_ .esp 16)), .store (at_ .esi tloOff) .eax,
    .mov .eax (.mem (at_ .esp 20)), .store (at_ .esi thiOff) .eax, .mov .ecx (.imm 0),
    .mov .eax (.mem (at_ .esp 24)), .alu .test .eax (.reg .eax)] := rfl

/-- Reading an argument after writing `scratch`. -/
theorem readW_writeW_scr_arg {s₀ : State} (hp : Pre s₀) (m : Mem) (v : BitVec 32) {d e : Nat}
    (hd : d + 4 ≤ 512) (he : 4 ≤ e) (he' : e + 4 ≤ 32) :
    (m.writeW (addr (scr s₀) d) v).readW (addr (esp₀ s₀) e) 32 = m.readW (addr (esp₀ s₀) e) 32 :=
  Mem.readW_writeW_sep (hp.arg_scr.sep (hp.arg_contains he he') (hp.scr_contains hd)) (by decide)

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem :=
  ((((s₀.mem.writeW (addr (scr s₀) 80) (s₀.gpr .ebx)).writeW (addr (scr s₀) 84) (s₀.gpr .esi)).writeW
    (addr (scr s₀) 88) (s₀.gpr .edi)).writeW (addr (scr s₀) tloOff) (arg s₀ 3)).writeW
    (addr (scr s₀) thiOff) (arg s₀ 4)

theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ fun s₁ =>
      s₁.gpr .esi = scr s₀ ∧ s₁.gpr .edi = bp s₀ ∧ s₁.gpr .esp = esp₀ s₀ ∧
      s₁.gpr .ebp = s₀.gpr .ebp ∧ s₁.gpr .ecx = 0 ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧
      s₁.mem = saveMem s₀ ∧ s₁.zf = some (arg s₀ 5 &&& arg s₀ 5 == 0) := by
  have hsa := readW_writeW_scr_arg hp
  have i8 := hp.in_arg (s := s₀) rfl (d := 8) (by omega) (by omega)
  have i16 := hp.in_arg (s := s₀) rfl (d := 16) (by omega) (by omega)
  have i20 := hp.in_arg (s := s₀) rfl (d := 20) (by omega) (by omega)
  have i24 := hp.in_arg (s := s₀) rfl (d := 24) (by omega) (by omega)
  have i28 := hp.in_arg (s := s₀) rfl (d := 28) (by omega) (by omega)
  have a8 : s₀.mem.readW (addr (esp₀ s₀) 8) 32 = bp s₀ := rfl
  have a16 : s₀.mem.readW (addr (esp₀ s₀) 16) 32 = arg s₀ 3 := rfl
  have a20 : s₀.mem.readW (addr (esp₀ s₀) 20) 32 = arg s₀ 4 := rfl
  have a24 : s₀.mem.readW (addr (esp₀ s₀) 24) 32 = arg s₀ 5 := rfl
  have a28 : s₀.mem.readW (addr (esp₀ s₀) 28) 32 = scr s₀ := rfl
  have hout : ∀ d, d + 4 ≤ 512 → InRegions s₀.wr (addr (scr s₀) d) 4 := fun d hd => hp.in_scr rfl hd
  apply WP.of_runBlock
  rw [prologue_eq]
  simp (config := {decide := true}) (disch := decide) only [at_, runBlock_cons,
    runBlock_nil, runStep_some, exec, execAlu, readSrc, ea_mk, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags,
    RegUpd.rd_setFlags, RegUpd.wr_setFlags, State.load32, State.store32, i8, i16, i20, i24, i28, a8,
    a16, a20, a24, a28, hout, hsa, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial

theorem epilogue_eq : epilogue = [.mov .ebx (.mem (at_ .esi 80)), .mov .edi (.mem (at_ .esi 88)),
    .mov .esi (.mem (at_ .esi 84))] := rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block epilogue) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  have hin : ∀ d, d + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
    fun d hd => mem_rd (hp.in_scr hc.wr hd)
  obtain ⟨g0, g1, g2⟩ := hc.saved
  have hesi := hc.esi
  have hesp := hc.esp
  have hebp := hc.ebp
  apply WP.of_runBlock
  rw [epilogue_eq]
  simp (config := {decide := true}) (disch := decide) only [at_, runBlock_cons,
    runBlock_nil, runStep_some, exec, readSrc, ea_mk, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, State.load32, hesi, hin, g0, g1, g2, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hesp, hebp]

/-! ## The final block flag and the count -/

/-- The memory after the flag and the count are stored. -/
def flagMem (s₀ : State) : Mem :=
  ((saveMem s₀).writeW (addr (scr s₀) fOff) (flagW (fl s₀))).writeW (addr (scr s₀) nOff) (arg s₀ 2)

theorem flag_ok {s₀ : State} (hp : Pre s₀) {s : State} (hesi : s.gpr .esi = scr s₀)
    (hesp : s.gpr .esp = esp₀ s₀) (hecx : s.gpr .ecx = 0) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hm : s.mem = saveMem s₀) (hz : s.zf = some (arg s₀ 5 &&& arg s₀ 5 == 0)) :
    WP isa flag s fun s' =>
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .edi = s.gpr .edi ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = flagMem s₀ ∧
      s'.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  have h12 : s₀.mem.readW (addr (esp₀ s₀) 12) 32 = arg s₀ 2 := rfl
  have a12 : (saveMem s₀).readW (addr (esp₀ s₀) 12) 32 = arg s₀ 2 := by
    simp (disch := decide) only [saveMem, readW_writeW_scr_arg hp, h12]
  -- After the flag's `ite`: `ecx` holds it.
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => s₁.gpr .ecx = flagW (fl s₀) ∧ s₁.gpr .esi = s.gpr .esi ∧
      s₁.gpr .edi = s.gpr .edi ∧ s₁.gpr .esp = s.gpr .esp ∧ s₁.gpr .ebp = s.gpr .ebp ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr ∧ s₁.mem = s.mem) ?_ fun s₁ ⟨c₁, e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ => ?_)
  · refine WP.ite (arg s₀ 5 &&& arg s₀ 5 == 0) (by exact hz) (fun h => ?_)
      (fun h => ?_)
    · refine WP.block_nil ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have h0 : arg s₀ 5 = 0 := by simpa using h
      rw [hecx]; simp [flagW, fl, h0]
    · refine wp_movi fun s₁ u₁ => WP.block_nil ⟨?_, u₁.other .esi (by decide), u₁.other .edi (by decide),
        u₁.other .esp (by decide), u₁.other .ebp (by decide), u₁.rd, u₁.wr, u₁.mem⟩
      have h0 : arg s₀ 5 ≠ 0 := by simpa using h
      have hf : (arg s₀ 5 != 0) = true := by simpa using h0
      rw [u₁.gpr]; simp only [flagW, fl, hf, ite_true]; rfl
  · have hin : ∀ d, d + 4 ≤ 512 → InRegions s₁.wr (addr (scr s₀) d) 4 := fun d hd =>
      hp.in_scr (by rw [e₆, hwr]) hd
    refine wp_stm (by rw [e₁, hesi]) (hin fOff (by decide)) fun s₂ u₂ => ?_
    refine wp_ldm (by rw [u₂.gpr, e₃, hesp]) (hp.in_arg (by rw [u₂.rd, e₅, hrd]) (by omega) (by omega))
      fun s₃ u₃ => ?_
    refine wp_stm (by rw [u₃.other _ (by decide), u₂.gpr, e₁, hesi])
      (by rw [u₃.wr, u₂.wr]; exact hin nOff (by decide)) fun s₄ u₄ => ?_
    refine wp_test fun s₅ u₅ hz₅ => WP.block_nil ?_
    have e12 : s₂.mem.readW (addr (esp₀ s₀) 12) 32 = arg s₀ 2 := by
      rw [u₂.mem, e₇, hm, readW_writeW_scr_arg hp _ _ (by decide) (by omega) (by omega), a12]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, e₁]
    · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, e₂]
    · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, e₃]
    · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, e₄]
    · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, e₅]
    · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, e₆]
    · rw [u₅.mem, u₄.mem, u₃.gpr, u₃.mem, e12, u₂.mem, c₁, e₇, hm]; rfl
    · rw [hz₅, u₄.gpr, u₃.gpr, e12]

/-! ## Before the first block -/

theorem flagMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scrR s₀] s₀.mem (flagMem s₀) := by
  have m := List.mem_singleton_self (scrR s₀)
  have c : ∀ d, d + 4 ≤ 512 → (scrR s₀).Contains (addr (scr s₀) d) (32 / 8) := fun d hd =>
    hp.scr_contains hd
  simp only [flagMem, saveMem]
  exact ((((((Frame.refl _ _).writeW m _ (c 80 (by omega))).writeW m _ (c 84 (by omega))).writeW m _
    (c 88 (by omega))).writeW m _ (c tloOff (by decide))).writeW m _ (c thiOff (by decide))).writeW m _
    (c fOff (by decide)) |>.writeW m _ (c nOff (by decide))

theorem common_zero {s₀ : State} (hp : Pre s₀) {s : State} (hesi : s.gpr .esi = scr s₀)
    (hesp : s.gpr .esp = esp₀ s₀) (hebp : s.gpr .ebp = s₀.gpr .ebp) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = flagMem s₀) : Common s₀ 0 s := by
  have fV := hp.scr_fits
  have hr := rw_scr fV
  refine ⟨hesi, hesp, hebp, hrd, hwr, ?_, ?_, ?_⟩
  · rw [hm]; exact (flagMem_frame hp).mono (by simp)
  · rw [hm]
    refine hp.stateAt_ext fun k hk => ?_
    rw [(flagMem_frame hp).readW (r := stR s₀) (hp.st_contains (by omega)) (by
        simp only [List.mem_singleton, forall_eq]; exact hp.st_scr) (by decide),
      ← hp.stateAt_get _ hk]
    rfl
  · rw [hm]
    simp only [Saved, flagMem, saveMem]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (config := {decide := true}) (disch := decide) only [Mem.readW_writeW_self32, hr]

theorem linv_zero {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ 0 s) (hedi : s.gpr .edi = bp s₀)
    (hm : s.mem = flagMem s₀) : LInv s₀ 0 s := by
  have hr := rw_scr hp.scr_fits
  refine ⟨hc, by rw [hedi]; simp [blkAddr], ?_, ?_, ?_, ?_⟩ <;> rw [hm] <;>
    simp (config := {decide := true}) (disch := decide) only [flagMem, saveMem, Mem.readW_writeW_self32, hr]
  · simp only [Nat.zero_mul, Nat.add_zero, t₀]; exact (Proof.Blake2.X86.Stream.lo_append _ _).symm
  · simp only [Nat.zero_mul, Nat.add_zero, t₀]; exact (Proof.Blake2.X86.Stream.hi_append _ _).symm
  · simp [nb]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Blake2.compressX86 Spec.Blake2.s).post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ ⟨hesi, hedi, hesp, hebp, hecx, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (flag_ok hp hesi hesp hecx hrd hwr hm hz)
    fun s₂ ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, hz₂⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₃ hc =>
    WP.mono (restore_ok hp hc) fun s' ⟨hr, hm'⟩ => ⟨⟨hr, ?_⟩, ?_⟩)
  rotate_left
  · rw [hm']
    refine hc.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simpa using ⟨hp.ret_st, hp.ret_scr⟩
  · show stateAt 32 s'.mem _ = _
    rw [hm']; exact hc.state
  have hc₀ := common_zero hp (by rw [e₁, hesi]) (by rw [e₃, hesp]) (by rw [e₄, hebp]) (by rw [e₅, hrd])
    (by rw [e₆, hwr]) e₇
  refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by exact hz₂) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp only [BitVec.and_self, beq_iff_eq] at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₂
      ⟨0, rfl, hpos, linv_zero hp hc₀ (by rw [e₂, hedi]) e₇⟩

/-! ## Constant time -/

/-- The taint analysis starts with the stack arguments public, and the words
holding `state` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [32, 512], argLen := 32, argBases := [(4, 0), (28, 1)] }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hst := hp.st_fits; have hsc := hp.scr_fits; have hs := hp.esp_fits
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 28) (by omega) hp.ret_st hp.arg_st
    · exact VG.X86.Taint.frame_disjoint (n := 28) (by omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : (Proof.Blake2.compressX86 Spec.Blake2.s).pre s₁)
    (h₂ : (Proof.Blake2.compressX86 Spec.Blake2.s).pre s₂)
    (hpub : (Proof.Blake2.compressX86 Spec.Blake2.s).pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scrR, st, scr, ha 0 (by omega), ha 6 (by omega)]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.esp_fits h4 hk, VG.X86.Taint.argByte_eq hp₂.esp_fits h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

end VG.Proof.Blake2.X86.CompressS
