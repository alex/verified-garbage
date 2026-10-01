import VerifiedGarbage.Proof.Blake2.X86.CompressB.Compress
import VerifiedGarbage.Proof.Blake2.X86.CompressB.Lit
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# BLAKE2b compression function on x86 (32-bit): the whole function

Untrusted: everything here is checked by Lean. The prologue and epilogue,
`correct` (the loop over the blocks), constant time, and `compress_verified`
against `compressX86 b` (`Proof/Blake2/X86/Contract.lean`), moved to the shared contract of
`Spec/Blake2/Contract.lean` (`compressB_verified`).
-/

namespace VG.Proof.Blake2.X86.CompressB

open VG VG.X86 VG.Impl.Blake2.X86.CompressB
open VG.Spec.Blake2 (HashValue stateAt compressBlocks)
open VG.Proof.Sha512.X86 (Acc rd64 rd64_frame)
open VG.Proof.Sha256.X86.Stream (contains_addr)

/-! ## The prologue -/

theorem pro_eq : prologue = ([.mov .eax (.mem ⟨.esp, 28⟩), .store ⟨.eax, 288⟩ .ebx,
      .store ⟨.eax, 292⟩ .esi, .store ⟨.eax, 296⟩ .edi, .store ⟨.eax, 300⟩ .ebp,
      .mov .esi (.reg .eax)] : List Instr) ++
    (([.mov .eax (.mem ⟨.esp, 8⟩), .store ⟨.esi, 256⟩ .eax,
      .mov .eax (.mem ⟨.esp, 16⟩), .store ⟨.esi, 264⟩ .eax,
      .mov .eax (.mem ⟨.esp, 20⟩), .store ⟨.esi, 268⟩ .eax,
      .mov .eax (.imm 0), .store ⟨.esi, 272⟩ .eax, .store ⟨.esi, 276⟩ .eax] : List Instr) ++
    (([.mov .eax (.mem ⟨.esp, 24⟩), .mov .ecx (.imm 0), .alu .cmp .ecx (.reg .eax),
      .alu .sbb .ecx (.reg .ecx), .store ⟨.esi, 280⟩ .ecx, .store ⟨.esi, 284⟩ .ecx] : List Instr) ++
    ([.mov .eax (.mem ⟨.esp, 12⟩), .store ⟨.esi, 260⟩ .eax, .alu .test .eax (.reg .eax)] :
      List Instr))) := rfl

/-- The final block flag as the prologue computes it: `0 - 0 - (0 < x)`. -/
def flag32 (x : BitVec 32) : BitVec 32 :=
  0 - 0 - (BitVec.ofBool (decide ((0 : BitVec 32).toNat < x.toNat))).setWidth 32

theorem flag32_eq (x : BitVec 32) : flag32 x ++ flag32 x = flagW (x != 0) := by
  by_cases h : x = 0
  · subst h; decide
  · have : 0 < x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h' | h'
      · exact absurd (BitVec.eq_of_toNat_eq h') h
      · exact h'
    have h' : decide ((0 : BitVec 32).toNat < x.toNat) = true := decide_eq_true this
    simp only [flag32, h', flagW, bne_iff_ne, ne_eq, h, not_false_eq_true, ite_true]
    decide

/-- The memory after saving the callee-saved registers. -/
def proMem₁ (s₀ : State) : Mem :=
  (((s₀.mem.writeW (addr (scr s₀) 288) (s₀.gpr .ebx)).writeW (addr (scr s₀) 292)
    (s₀.gpr .esi)).writeW (addr (scr s₀) 296) (s₀.gpr .edi)).writeW (addr (scr s₀) 300) (s₀.gpr .ebp)

/-- And the block's address and the counter. -/
def proMem₂ (s₀ : State) : Mem :=
  (((((proMem₁ s₀).writeW (addr (scr s₀) 256) (bp s₀)).writeW (addr (scr s₀) 264)
    (arg s₀ 3)).writeW (addr (scr s₀) 268) (arg s₀ 4)).writeW (addr (scr s₀) 272)
    (0 : BitVec 32)).writeW (addr (scr s₀) 276) (0 : BitVec 32)

/-- And the flag. -/
def proMem₃ (s₀ : State) : Mem :=
  ((proMem₂ s₀).writeW (addr (scr s₀) 280) (flag32 (arg s₀ 5))).writeW (addr (scr s₀) 284)
    (flag32 (arg s₀ 5))

/-- The memory after the prologue. -/
def proMem (s₀ : State) : Mem := (proMem₃ s₀).writeW (addr (scr s₀) 260) (arg s₀ 2)

theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ fun s₁ =>
      s₁.gpr .esi = scr s₀ ∧ s₁.gpr .esp = esp₀ s₀ ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧
      s₁.mem = proMem s₀ ∧ s₁.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  have hsa : ∀ (m : Mem) (v : BitVec 32) {d e : Nat}, d + 4 ≤ 512 → 4 ≤ e → e + 4 ≤ 32 →
      (m.writeW (addr (scr s₀) d) v).readW (addr (esp₀ s₀) e) 32 = m.readW (addr (esp₀ s₀) e) 32 :=
    fun m v d e hd he he' => Mem.readW_writeW_sep (hp.arg_scr.sep (hp.arg_contains he he')
      (contains_addr hd (by omega) hp.scr_fits)) (by decide)
  have i8 := hp.in_arg (s := s₀) rfl (d := 8) (by omega) (by omega)
  have i12 := hp.in_arg (s := s₀) rfl (d := 12) (by omega) (by omega)
  have i16 := hp.in_arg (s := s₀) rfl (d := 16) (by omega) (by omega)
  have i20 := hp.in_arg (s := s₀) rfl (d := 20) (by omega) (by omega)
  have i24 := hp.in_arg (s := s₀) rfl (d := 24) (by omega) (by omega)
  have i28 := hp.in_arg (s := s₀) rfl (d := 28) (by omega) (by omega)
  have a8 : s₀.mem.readW (addr (esp₀ s₀) 8) 32 = bp s₀ := rfl
  have a12 : s₀.mem.readW (addr (esp₀ s₀) 12) 32 = arg s₀ 2 := rfl
  have a16 : s₀.mem.readW (addr (esp₀ s₀) 16) 32 = arg s₀ 3 := rfl
  have a20 : s₀.mem.readW (addr (esp₀ s₀) 20) 32 = arg s₀ 4 := rfl
  have a24 : s₀.mem.readW (addr (esp₀ s₀) 24) 32 = arg s₀ 5 := rfl
  have a28 : s₀.mem.readW (addr (esp₀ s₀) 28) 32 = scr s₀ := rfl
  have hout : ∀ d, d + 4 ≤ 512 → InRegions s₀.wr (addr (scr s₀) d) 4 := hp.acc (s := s₀) rfl
  -- The arguments, read after writes to `scratch`.
  have r₁ : ∀ e, 4 ≤ e → e + 4 ≤ 32 →
      (proMem₁ s₀).readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 := by
    intro e h1 h2; simp (disch := omega) only [proMem₁, hsa]
  have r₂ : ∀ e, 4 ≤ e → e + 4 ≤ 32 →
      (proMem₂ s₀).readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 := by
    intro e h1 h2; simp (disch := omega) only [proMem₂, hsa, r₁]
  have r₃ : ∀ e, 4 ≤ e → e + 4 ≤ 32 →
      (proMem₃ s₀).readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 := by
    intro e h1 h2; simp (disch := omega) only [proMem₃, hsa, r₂]
  rw [pro_eq, WP.block_append_iff]
  refine WP.mono (Q := fun (s : State) => s.gpr .esi = scr s₀ ∧ s.gpr .esp = esp₀ s₀ ∧ s.rd = s₀.rd ∧
    s.wr = s₀.wr ∧ s.mem = proMem₁ s₀) ?_ fun s₁ ⟨e₁, p₁, d₁, w₁, m₁⟩ => ?_
  · apply WP.of_runBlock
    simp (config := {decide := true}) (disch := decide) only [runBlock_cons, runBlock_nil,
      runStep_some, exec, readSrc, ea_mk, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
      RegUpd.wr_setReg, State.load32, State.store32, i28, a28, hout, ite_true, ite_false,
      Option.map_some, Option.some.injEq, exists_eq_left', proMem₁]
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s : State) => s.gpr .esi = scr s₀ ∧ s.gpr .esp = esp₀ s₀ ∧ s.rd = s₀.rd ∧
    s.wr = s₀.wr ∧ s.mem = proMem₂ s₀) ?_ fun s₂ ⟨e₂, p₂, d₂, w₂, m₂⟩ => ?_
  · apply WP.of_runBlock
    simp (config := {decide := true}) (disch := decide) only [runBlock_cons, runBlock_nil,
      runStep_some, exec, readSrc, ea_mk, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
      RegUpd.wr_setReg, State.load32, State.store32, e₁, p₁, d₁, w₁, m₁, i8, i16, i20, a8, a16, a20,
      hout, r₁, hsa, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left', proMem₂]
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s : State) => s.gpr .esi = scr s₀ ∧ s.gpr .esp = esp₀ s₀ ∧ s.rd = s₀.rd ∧
    s.wr = s₀.wr ∧ s.mem = proMem₃ s₀) ?_ fun s₃ ⟨e₃, p₃, d₃, w₃, m₃⟩ => ?_
  · apply WP.of_runBlock
    simp (config := {decide := true}) (disch := decide) only [runBlock_cons, runBlock_nil,
      runStep_some, exec, execAlu, readSrc, ea_mk, RegUpd.gpr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.cf_arithFlags, RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, State.load32,
      State.store32, e₂, p₂, d₂, w₂, m₂, i24, a24, hout, r₂, ite_true, ite_false, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left', proMem₃, flag32]
  · apply WP.of_runBlock
    simp (config := {decide := true}) (disch := decide) only [runBlock_cons, runBlock_nil,
      runStep_some, exec, execAlu, readSrc, ea_mk, RegUpd.gpr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_arithFlags, RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, State.load32,
      State.store32, e₃, p₃, d₃, w₃, m₃, i12, a12, hout, r₃, ite_true, ite_false, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left', proMem]

theorem proMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scrR s₀] s₀.mem (proMem s₀) := by
  have c : ∀ d : Nat, d + 4 ≤ 512 → (scrR s₀).Contains (addr (scr s₀) d) (32 / 8) :=
    fun d hd => contains_addr hd (by omega) hp.scr_fits
  have m := List.mem_singleton_self (scrR s₀)
  simp only [proMem, proMem₃, proMem₂, proMem₁]
  exact (((((((((((((Frame.refl _ _).writeW m _ (c 288 (by omega))).writeW m _ (c 292 (by omega))).writeW
    m _ (c 296 (by omega))).writeW m _ (c 300 (by omega))).writeW m _ (c 256 (by omega))).writeW m _
    (c 264 (by omega))).writeW m _ (c 268 (by omega))).writeW m _ (c 272 (by omega))).writeW m _
    (c 276 (by omega))).writeW m _ (c 280 (by omega))).writeW m _ (c 284 (by omega))).writeW m _
    (c 260 (by omega)))

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hesi : s₁.gpr .esi = scr s₀)
    (hesp : s₁.gpr .esp = esp₀ s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr)
    (hm : s₁.mem = proMem s₀) : Common s₀ 0 s₁ := by
  have r32 := rw32_ne hp.scr_fits
  have hF : Frame [scrR s₀] s₀.mem s₁.mem := hm ▸ proMem_frame hp
  have rd : ∀ d, s₁.mem.readW (addr (scr s₀) d) 32 = (proMem s₀).readW (addr (scr s₀) d) 32 := by
    intro d; rw [hm]
  refine ⟨hesi, hesp, hrd, hwr, hF.mono (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Proof.Blake2.compressBlocks_zero]
    apply Vector.ext; intro j hj
    rw [stateAt_rd64 hp.st_fits _ hj, stateAt_rd64 hp.st_fits _ hj]
    exact rd64_frame hF (by simpa using hp.st_scr) hp.st_fits (by omega)
  · intro p hp'
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [rd, proMem, proMem₃, proMem₂, proMem₁, r32, Mem.readW_writeW_self32]
  · simp (disch := decide) only [rd, proMem, proMem₃, proMem₂, proMem₁, r32, Mem.readW_writeW_self32, blOff, blkAddr,
      Nat.mul_zero]
    exact (BitVec.add_zero _).symm
  · simp (disch := decide) only [rd, proMem, proMem₃, proMem₂, proMem₁, Mem.readW_writeW_self32, nOff, Nat.sub_zero,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp (disch := decide) only [rd64, rd, proMem, proMem₃, proMem₂, proMem₁, r32, Mem.readW_writeW_self32, tOff,
      Nat.zero_mul, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp (disch := decide) only [rd64, rd, proMem, proMem₃, proMem₂, proMem₁, r32, Mem.readW_writeW_self32, tOff,
      Nat.zero_mul, Nat.add_zero, Nat.reduceAdd]
    rw [Nat.div_eq_of_lt (BitVec.isLt _)]
    rfl
  · simp (disch := decide) only [rd64, rd, proMem, proMem₃, proMem₂, proMem₁, r32, Mem.readW_writeW_self32, fOff,
      Nat.reduceAdd]
    exact flag32_eq _

/-! ## The epilogue -/

theorem epilogue_eq : epilogue = [.mov .ebx (.mem ⟨.esi, 288⟩), .mov .edi (.mem ⟨.esi, 296⟩),
    .mov .ebp (.mem ⟨.esi, 300⟩), .mov .esi (.mem ⟨.esi, 292⟩)] := rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block epilogue) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  have hin : ∀ d, d + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
    fun d hd => hp.in_scr hc.wr hd
  have g0 := hc.saved (.ebx, 288) (by decide)
  have g1 := hc.saved (.esi, 292) (by decide)
  have g2 := hc.saved (.edi, 296) (by decide)
  have g3 := hc.saved (.ebp, 300) (by decide)
  simp only at g0 g1 g2 g3
  have hesi := hc.esi
  have hesp := hc.esp
  apply WP.of_runBlock
  rw [epilogue_eq]
  simp (config := {decide := true}) (disch := decide) only [runBlock_cons,
    runBlock_nil, runStep_some, exec, readSrc, ea_mk, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, State.load32, hesi, hin, g0, g1, g2, g3, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hesp]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => abiPreserved s₀ s' ∧ (compressX86 Spec.Blake2.b).post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ ⟨hesi, hesp, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc =>
    WP.mono (restore_ok hp hc) fun s' ⟨hr, hm'⟩ => ⟨⟨hr, ?_⟩, ?_⟩)
  rotate_left
  · rw [hm']
    refine hc.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simpa using ⟨hp.ret_st, hp.ret_scr⟩
  · show stateAt 64 s'.mem _ = _
    rw [hm']; exact hc.state
  have hc₀ := common_zero hp hesi hesp hrd hwr hm
  refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp only [BitVec.and_self, beq_iff_eq] at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ Common s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hc⟩
      refine WP.mono (body_ok hp hi hc) fun s' ⟨hc', hz'⟩ => ?_
      have hnb : nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
      by_cases hlast : i + 1 = nb s₀
      · left
        refine ⟨?_, hlast ▸ hc'⟩
        rw [Proof.Sha256.X86.Stream.eval_ne, hz', ← hlast, Nat.sub_self]; rfl
      · right
        have hne : nb s₀ - (i + 1) ≠ 0 := by omega
        have h0 : (BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0) = false := by
          rw [beq_eq_false_iff_ne]
          intro h'
          have h'' := congrArg BitVec.toNat h'
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h''
          exact hne h''
        refine ⟨?_, nb s₀ - (i + 1), by omega, i + 1, rfl, by omega, hc'⟩
        rw [Proof.Sha256.X86.Stream.eval_ne, hz', h0]; rfl
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hc₀⟩

/-! ## Constant time -/

/-- The taint analysis starts with the stack arguments public, and the words
holding `state` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [64, 512], argLen := 32,
    argBases := [(4, 0), (28, 1)] }

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

theorem agree₀ {s₁ s₂ : State} (h₁ : (compressX86 Spec.Blake2.b).pre s₁)
    (h₂ : (compressX86 Spec.Blake2.b).pre s₂) (hpub : (compressX86 Spec.Blake2.b).pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scrR, st, scr, ha 0 (by decide), ha 6 (by decide)]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := hp₁.esp_fits; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := hp₂.esp_fits; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

/-! ## Results -/

/-- Memory holding the arguments `0x1000, 0x2000, 0, 0, 0, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x401D then 0x30 else 0

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 0⟩, ⟨0x4004, 28⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x3000, 512⟩]

theorem sat_pre : (compressX86 Spec.Blake2.b).pre satState := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 0x2000 := by decide
  have a2 : arg satState 2 = 0 := by decide
  have a6 : arg satState 6 = 0x3000 := by decide
  have e : argAddr satState 0 = 0x4004 := by decide
  simp only [compressX86, Spec.Blake2.blockBytes, a0, a1, a2, a6, e]
  refine ⟨by decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

theorem compress_verified : Verified X86.target compress (compressX86 Spec.Blake2.b) :=
  ⟨fun s hs => correct (pre_of s hs),
    VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub) (by taint_decide),
    ⟨satState, sat_pre⟩⟩

theorem compressB_verified :
    Verified X86.target compress (Spec.Blake2.compressBContract X86.abi) :=
  compress_verified.of_implies (by
    sig_implies [Spec.Blake2.compressBContract, Spec.Blake2.compressBSig, Proof.Blake2.compressX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Spec.Blake2.blockBytes]
      [satState, satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using satState)

end VG.Proof.Blake2.X86.CompressB
