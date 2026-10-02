import VerifiedGarbage.Proof.Scrypt.Arm.Whole.Steps
import VerifiedGarbage.Proof.Scrypt.Arm.Whole.Pbkdf2
import VerifiedGarbage.Proof.Scrypt.Arm.RoMixCT
import VerifiedGarbage.Proof.Scrypt.Arm.Lit
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls

/-!
# scrypt on 32-bit ARM: the calls

Each call passes its stack arguments in a frame of its own: four words for
`vg_pbkdf2_hmac_sha256` (`frame4_ok`, as `frame2_ok` of PBKDF2's proof, whose
callee uses at most 24 bytes below it), two for `vg_scrypt_romix`
(`frame2_ok`). What such a call does from `Ctx` and its arguments (`PbkArgs`,
`RomixArgs`): it keeps `Ctx`, and changes memory only in what it writes and
the 40 bytes of stack below the stack pointer (`pbk_call`, `romix_call`).
`pbk_pre'` and `romix_pre` are their preconditions, which the proof of
constant time uses too.
-/

namespace VG.Proof.Scrypt.Arm.Whole

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Arm.FrameStack
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)
open VG.Proof.Pbkdf2.Whole.Arm (After frame2_ok frame2_rel p2_arg0 p2_arg1 p2_argAddr stk)

/-! ## A frame of four words around a call -/

/-- The registers `pbkdf2`'s stack arguments are pushed from. -/
abbrev fr4 : List Reg := [.r10, .r11, .r12, .lr]

/-- What a call in a frame of four words leaves: the regions, the stack
pointer, the callee-saved registers but `lr`, and memory outside what it
may write and the 40 bytes below the stack pointer. -/
structure After4 (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame (ws ++ [belowA s.sp 40]) s.mem s'.mem

section
variable {s : State}

theorem p4_sp : (pushed fr4 s).sp = s.sp - BitVec.ofNat 32 16 := rfl

theorem p4_mem (h : 16 ≤ s.sp.toNat) :
    (pushed fr4 s).mem =
      ((((s.mem.writeW (State.addr (s.sp - BitVec.ofNat 32 16) + BitVec.ofNat 64 0) (s.gpr .r10)).writeW
        (State.addr (s.sp - BitVec.ofNat 32 16) + BitVec.ofNat 64 4) (s.gpr .r11)).writeW
        (State.addr (s.sp - BitVec.ofNat 32 16) + BitVec.ofNat 64 8) (s.gpr .r12)).writeW
        (State.addr (s.sp - BitVec.ofNat 32 16) + BitVec.ofNat 64 12) (s.gpr .lr)) := by
  have e : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' h
  show storeWords s.mem (s.sp - BitVec.ofNat 32 16) [s.gpr .r10, s.gpr .r11, s.gpr .r12, s.gpr .lr] = _
  simp only [storeWords]
  rw [BitVec.add_zero, BitVec.add_assoc, BitVec.add_assoc,
    show (4 : BitVec 32) + 4 = BitVec.ofNat 32 8 from rfl,
    show (BitVec.ofNat 32 8 : BitVec 32) + 4 = BitVec.ofNat 32 12 from rfl,
    show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
    addr_add (by omega), addr_add (by omega), addr_add (by omega)]

theorem p4_arg (h : 16 ≤ s.sp.toNat) {rd wr : List Region} {i : Nat} (hi : i < 4) :
    stackArg ((pushed fr4 s).callEntry.withRegions rd wr) i = s.gpr fr4[i] := by
  have hn := s.sp.isLt
  have e : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' h
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp, State.callEntry_mem,
    State.callEntry_sp, p4_sp]
  rw [p4_mem h, addr_add (by omega)]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [rd_off, Mem.readW_writeW_self32, Nat.mul_zero, Nat.mul_one,
      Nat.reduceMul] <;> rfl

theorem p4_a0 (h : 16 ≤ s.sp.toNat) {rd wr : List Region} :
    stackArg ((pushed fr4 s).callEntry.withRegions rd wr) 0 = s.gpr .r10 := p4_arg h (by decide)
theorem p4_a1 (h : 16 ≤ s.sp.toNat) {rd wr : List Region} :
    stackArg ((pushed fr4 s).callEntry.withRegions rd wr) 1 = s.gpr .r11 := p4_arg h (by decide)
theorem p4_a2 (h : 16 ≤ s.sp.toNat) {rd wr : List Region} :
    stackArg ((pushed fr4 s).callEntry.withRegions rd wr) 2 = s.gpr .r12 := p4_arg h (by decide)
theorem p4_a3 (h : 16 ≤ s.sp.toNat) {rd wr : List Region} :
    stackArg ((pushed fr4 s).callEntry.withRegions rd wr) 3 = s.gpr .lr := p4_arg h (by decide)

theorem p4_argAddr {rd wr : List Region} :
    stackArgAddr ((pushed fr4 s).callEntry.withRegions rd wr) 0 = State.addr (s.sp - BitVec.ofNat 32 16) := by
  simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, p4_sp, Nat.mul_zero]
  rw [BitVec.add_zero]

end

/-- A frame of four words, popped into `r12`, around a call of verified code
that uses at most 24 bytes of stack: the callee runs from the state after
the push, and the frame leaves `After4`. -/
theorem frame4_ok {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hst : armStack c ≤ 24) {s : State} (h40 : 40 ≤ s.sp.toNat) {rd wr : List Region}
    (hpre : k.pre ((pushed fr4 s).callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) ((pushed fr4 s).rd ++ (pushed fr4 s).wr))
    (hw : Covers wr (pushed fr4 s).wr) {Q : State → Prop}
    (hQ : ∀ s₂ : State, After4 s wr (popped .r12 16 s₂) →
      k.post ((pushed fr4 s).callEntry.withRegions rd wr) (s₂.withRegions rd wr) → Q (popped .r12 16 s₂)) :
    WP isa (.frame (.push fr4) (.call n c) (.pop .r12 16)) s Q := by
  have h16 : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' (by omega)
  refine WP.frame (rs := fr4) (r := .r12) (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
    (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine WP.callF hv hpre hc hw (by rw [p4_sp, h16]; omega) fun s₂ hrd hwr hsp hf hcs hpost => ?_
  refine hQ s₂ ⟨?_, ?_, ?_, fun r hr hl => ?_, ?_⟩ hpost
  · rw [popped_rd, hrd, pushed_rd]
  · rw [popped_wr, hwr, pushed_wr]; rfl
  · rw [popped_sp, hsp, p4_sp]; exact BitVec.sub_add_cancel _ _
  · have : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr this, hcs r hr hl, pushed_gpr]
  · rw [popped_mem]
    have f₀ := pushed_frameA (rs := fr4) (s := s) (by simp only [List.length_cons, List.length_nil]; omega)
    refine Frame.trans (Frame.sub f₀ fun r hr => ?_) (Frame.sub hf fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      have := belowA_inner (sp := s.sp) (a := 16) (b := 40) (k := 0) (by omega) h40
      simpa using this
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        rw [p4_sp]
        exact belowA_inner (k := 16) (by omega) h40

/-- Two runs of such a frame leak the same, if their stack pointers are the
same and the callee's preconditions and public data hold. -/
theorem frame4_rel {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (h : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧
      k.pre ((pushed fr4 s₁).callEntry.withRegions rd wr) ∧
      k.pre ((pushed fr4 s₂).callEntry.withRegions rd wr) ∧
      k.pub ((pushed fr4 s₁).callEntry.withRegions rd wr) ((pushed fr4 s₂).callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) ((pushed fr4 s₁).rd ++ (pushed fr4 s₁).wr) ∧ Covers wr (pushed fr4 s₁).wr ∧
      Covers (rd ++ wr) ((pushed fr4 s₂).rd ++ (pushed fr4 s₂).wr) ∧ Covers wr (pushed fr4 s₂).wr) :
    RelCT isa P (.frame (.push fr4) (.call n c) (.pop .r12 16)) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => (h s₁ s₂ hp).1) (RelCT.call hv hct rd wr fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_)
  rw [Hmac.Generic.Arm.push_eq (by decide) pa, Hmac.Generic.Arm.push_eq (by decide) pb]
  exact (h s₁ s₂ hp).2

/-! ## The stack below the stack pointer -/

section
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

/-- The 40 bytes below the stack pointer, as `belowA` has them. -/
theorem stk_eq (hL : L.Ok) : belowA L.sp 40 = L.STK := by
  simp only [belowA, addr_sub' hL.nS]

theorem a16 (hL : L.Ok) :
    State.addr (L.sp - BitVec.ofNat 32 16) = State.addr L.sp - BitVec.ofNat 64 40 + BitVec.ofNat 64 24 := by
  rw [addr_sub' (by have := hL.nS; omega), Offset.sub_ofNat_eq _ (by omega : 16 ≤ 40)]

theorem a40 (hL : L.Ok) :
    State.addr (L.sp - BitVec.ofNat 32 16) - BitVec.ofNat 64 24 = State.addr L.sp - BitVec.ofNat 64 40 := by
  rw [addr_sub' (by have := hL.nS; omega), BitVec.sub_sub, BitVec.ofNat_add_ofNat]

theorem toNat_Q (hL : L.Ok) : (State.addr L.sp - BitVec.ofNat 64 40).toNat = L.sp.toNat - 40 := by
  rw [← addr_sub' hL.nS, toNat_addr, sub_toNat' hL.nS]

/-- Our frames' words and the callee's stack are in `STK`, apart. -/
theorem args16_sub (hL : L.Ok) : Region.Sub ⟨State.addr (L.sp - BitVec.ofNat 32 16), 16⟩ L.STK := by
  rw [a16 hL]; exact Offset.sub_base _ (by omega)

theorem cstk_sub (hL : L.Ok) :
    Region.Sub ⟨State.addr (L.sp - BitVec.ofNat 32 16) - BitVec.ofNat 64 24, 24⟩ L.STK := by
  rw [a40 hL]; exact Region.sub_prefix (by omega)

theorem cstk_args (hL : L.Ok) :
    Region.Disjoint ⟨State.addr (L.sp - BitVec.ofNat 32 16) - BitVec.ofNat 64 24, 24⟩
      ⟨State.addr (L.sp - BitVec.ofNat 32 16), 16⟩ := by
  rw [a40 hL, a16 hL]
  exact (Offset.disjoint_base _ (by omega) (by omega)).symm

/-- `STK` is apart from our stack arguments. -/
theorem stk_args (hL : L.Ok) : L.STK.Disjoint L.ARGS := by
  have := hL.nA; have := hL.nS
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have e : x - State.addr L.sp = (x - (State.addr L.sp - BitVec.ofNat 64 40)) - BitVec.ofNat 64 40 := by
    rw [BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [e, Offset.toNat_sub_ofNat] at h₂
  have := (x - (State.addr L.sp - BitVec.ofNat 64 40)).isLt
  omega

/-- `STK` is apart from the save area. -/
theorem stk_sv (hL : L.Ok) : L.STK.Disjoint L.SV := hL.kc.sub_right hL.sv_sc

end

/-! ## PBKDF2 -/

section
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `scratch`'s first 1600 bytes, PBKDF2's working space. -/
abbrev scr1600 (L : Lay) : Region := ⟨State.addr L.scr, 200 * 8⟩

theorem scr_in (hL : L.Ok) : InBuf L (scr1600 L) :=
  .inr (.inr (.inl (within_base _ (by have := hL.slen17; omega))))

theorem scr_sv (hL : L.Ok) : (scr1600 L).Disjoint L.SV :=
  (Offset.disjoint_base _ (by omega) (by have := hL.nc; have := hL.slen; omega)).symm

/-- The regions a call of PBKDF2 reads and writes. -/
abbrev pbkRd (L : Lay) (salt sl : BitVec 32) : List Region :=
  [L.PW, ⟨State.addr salt, sl.toNat⟩, ⟨State.addr (L.sp - BitVec.ofNat 32 16), 16⟩]
abbrev pbkWr (L : Lay) (out ol : BitVec 32) : List Region := [⟨State.addr out, ol.toNat⟩, scr1600 L]

/-- What a call of PBKDF2 needs of its salt and its output, beyond being in our buffers. -/
structure PbkRegions (L : Lay) (salt sl out ol : BitVec 32) : Prop where
  sw : ∃ R ∈ L.regions, Within ⟨State.addr salt, sl.toNat⟩ R
  ow : InBuf L ⟨State.addr out, ol.toNat⟩
  osv : Region.Disjoint ⟨State.addr out, ol.toNat⟩ L.SV
  so : Region.Disjoint ⟨State.addr salt, sl.toNat⟩ ⟨State.addr out, ol.toNat⟩
  sc : Region.Disjoint ⟨State.addr salt, sl.toNat⟩ (scr1600 L)
  oc : Region.Disjoint ⟨State.addr out, ol.toNat⟩ (scr1600 L)
  ks : L.STK.Disjoint ⟨State.addr salt, sl.toNat⟩
  ns : salt.toNat + sl.toNat ≤ 2 ^ 32
  no : out.toNat + ol.toNat ≤ 2 ^ 32
  ol : ol.toNat ≤ (2 ^ 32 - 1) * 32

theorem pbk_pre' (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {salt sl out ol : BitVec 32}
    (ha : PbkArgs L salt sl out ol t) (hr : PbkRegions L salt sl out ol) :
    pbkA.pre ((pushed fr4 t).callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) := by
  have hS := hL.nS
  have hA := hL.nA
  have h16 : (L.sp - BitVec.ofNat 32 16).toNat = L.sp.toNat - 16 := sub_toNat' (by omega)
  have sp16 : 16 ≤ t.sp.toNat := by rw [hc.sp]; omega
  simp only [pbkA, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.withRegions_gpr,
    State.callEntry_sp, p4_sp, p4_argAddr, p4_a0 sp16, p4_a1 sp16, p4_a2 sp16, p4_a3 sp16,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    pushed_gpr, hc.sp, ha.r0, ha.r1, ha.r2, ha.r3, ha.r10, ha.r11, ha.r12, ha.lr, h16]
  have sw := scr_in hL
  exact ⟨by omega, by omega, trivial, trivial, hL.pw_in hr.ow, hL.pw_in sw, hr.so, hr.sc, hr.oc,
    ((hL.stk_in hr.ow).sub_left (args16_sub hL)).symm, ((hL.stk_in sw).sub_left (args16_sub hL)).symm,
    hL.kp.sub_left (cstk_sub hL), hr.ks.sub_left (cstk_sub hL), (hL.stk_in hr.ow).sub_left (cstk_sub hL),
    (hL.stk_in sw).sub_left (cstk_sub hL), cstk_args hL, hL.np, hr.ns, hr.no,
    by have := hL.nc; have := hL.slen17; omega, by decide, hr.ol⟩

/-- A region within a writable buffer is within `wr`. -/
theorem InBuf.wr {r : Region} (h : InBuf L r) {t : State} (hc : Ctx L g m₀ t) :
    ∃ R ∈ t.wr, Within r R := by
  rw [hc.wr]
  rcases h with h | h | h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, h⟩

theorem pbk_cov (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {salt sl out ol : BitVec 32}
    (hr : PbkRegions L salt sl out ol) :
    Covers (pbkRd L salt sl ++ pbkWr L out ol) ((pushed fr4 t).rd ++ (pushed fr4 t).wr) ∧
      Covers (pbkWr L out ol) (pushed fr4 t).wr := by
  have up : ∀ {r : Region}, (∃ R ∈ t.wr, Within r R) → ∃ R ∈ (pushed fr4 t).rd ++ (pushed fr4 t).wr,
      Within r R := fun ⟨R, hR, hw⟩ => ⟨R, by rw [pushed_wr]; simp [hR], hw⟩
  have upw : ∀ {r : Region}, (∃ R ∈ t.wr, Within r R) → ∃ R ∈ (pushed fr4 t).wr, Within r R :=
    fun ⟨R, hR, hw⟩ => ⟨R, by rw [pushed_wr]; simp [hR], hw⟩
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [pbkRd, pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.PW, by rw [pushed_rd, hc.rd]; simp, within_base _ (Nat.le_refl _)⟩
    · obtain ⟨R, hR, hw⟩ := hr.sw
      refine ⟨R, ?_, hw⟩
      rw [pushed_rd, pushed_wr, hc.rd, hc.wr]
      simp only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · refine ⟨⟨State.addr (t.sp - BitVec.ofNat 32 (4 * fr4.length)), 4 * fr4.length⟩,
        by rw [pushed_wr]; simp, 0, ?_, by simp⟩
      simp only [hc.sp, BitVec.add_zero]; rfl
    · exact up (hr.ow.wr hc)
    · exact up ((scr_in hL).wr hc)
  · simp only [pbkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact upw (hr.ow.wr hc)
    · exact upw ((scr_in hL).wr hc)

/-- The regions a call of PBKDF2 writes miss our stack arguments and the save area. -/
theorem pbk_apart (hL : L.Ok) {salt sl out ol : BitVec 32} (hr : PbkRegions L salt sl out ol) :
    ∀ R ∈ pbkWr L out ol ++ [L.STK], L.ARGS.Disjoint R ∧ L.SV.Disjoint R := by
  simp only [pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro R (rfl | rfl | rfl)
  · exact ⟨hL.args_in hr.ow, hr.osv.symm⟩
  · exact ⟨hL.args_in (scr_in hL), (scr_sv hL).symm⟩
  · exact ⟨(stk_args hL).symm, (stk_sv hL).symm⟩

theorem pbk_call {pbk : Prog isa}
    (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24))
    (hst : armStack pbk ≤ 24) (name : String) (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t)
    {salt sl out ol : BitVec 32} (ha : PbkArgs L salt sl out ol t) (hr : PbkRegions L salt sl out ol) :
    WP isa (pbkCall name pbk) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r4 = t.gpr .r4 ∧
      Frame (pbkWr L out ol ++ [L.STK]) t.mem t'.mem ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt t.mem (State.addr L.pw) L.pwl.toNat)
        (bytesAt t.mem (State.addr salt) sl.toNat) 1 ol.toNat =
        some (bytesAt t'.mem (State.addr out) ol.toNat) := by
  have hS := hL.nS
  obtain ⟨cov, covw⟩ := pbk_cov hL hc hr
  refine frame4_ok (pbk_correct hv) hst (by rw [hc.sp]; exact hS) (pbk_pre' hL hc ha hr) cov covw
    fun s₂ h4 hpost => ?_
  have hf : Frame (pbkWr L out ol ++ [L.STK]) t.mem (popped .r12 16 s₂).mem := by
    have := h4.frame; rwa [hc.sp, stk_eq hL] at this
  have ap := pbk_apart hL hr
  refine ⟨⟨h4.rd.trans hc.rd, h4.wr.trans hc.wr, h4.sp.trans hc.sp,
    (h4.cs .r5 (by decide) (by decide)).trans hc.r5, (h4.cs .r6 (by decide) (by decide)).trans hc.r6,
    (h4.cs .r7 (by decide) (by decide)).trans hc.r7, (h4.cs .r8 (by decide) (by decide)).trans hc.r8,
    (h4.cs .r9 (by decide) (by decide)).trans hc.r9, hc.args.frame hf fun R hR => (ap R hR).1,
    hc.saved.frame hf fun R hR => (ap R hR).2, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩,
    h4.cs .r4 (by decide) (by decide), hf, ?_⟩
  · simp only [pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨R, hR, hs⟩ := hr.ow.sub
      rcases hR with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
    · exact ⟨L.SC, by simp, Within.sub (within_base _ (by have := hL.slen17; omega))⟩
    · exact ⟨L.STK, by simp, fun _ h => h⟩
  · have h := hpost
    have sp16 : 16 ≤ t.sp.toNat := by rw [hc.sp]; omega
    simp only [pbkA, Spec.Hmac.sha256S, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
      pushed_gpr, p4_a0 sp16, p4_a1 sp16, p4_a2 sp16, ha.r0, ha.r1, ha.r2, ha.r3, ha.r10, ha.r11, ha.r12] at h
    have f₀ := pushed_frameA (rs := fr4) (s := t) (by simp only [List.length_cons, List.length_nil]; omega)
    have d16 : ∀ {r : Region}, L.STK.Disjoint r →
        ∀ R ∈ [(⟨State.addr (t.sp - BitVec.ofNat 32 (4 * fr4.length)), 4 * fr4.length⟩ : Region)],
        r.Disjoint R := fun hd R hR => by
      simp only [List.mem_singleton] at hR; subst hR
      rw [hc.sp]; exact (hd.sub_left (args16_sub hL)).symm
    have e₁ : Spec.Sha256.bytesAt (pushed fr4 t).mem (State.addr L.pw) L.pwl.toNat =
        bytesAt t.mem (State.addr L.pw) L.pwl.toNat :=
      Memory.frame_bytesAt f₀ (d16 hL.kp) (by have := L.pwl.isLt; omega)
    have e₂ : Spec.Sha256.bytesAt (pushed fr4 t).mem (State.addr salt) sl.toNat =
        bytesAt t.mem (State.addr salt) sl.toNat :=
      Memory.frame_bytesAt f₀ (d16 hr.ks) (by have := sl.isLt; omega)
    rw [e₁, e₂] at h
    exact h

end

/-! ## ROMix -/

section
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

/-- Block `i` of `b`, as the code computes it, and its address. -/
abbrev blkAt (L : Lay) (i : Nat) : BitVec 32 := L.b + BitVec.ofNat 32 (128 * L.r.toNat * i)
abbrev blkA (L : Lay) (i : Nat) : Addr := State.addr L.b + BitVec.ofNat 64 (128 * L.r.toNat * i)

theorem blk_le (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + L.r.toNat * 128 ≤ L.blen.toNat * 128 := by
  rw [← hL.len_b, Nat.mul_comm L.r.toNat 128, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

theorem addr_blk (hL : L.Ok) {i : Nat} (hi : i < L.pp) : State.addr (blkAt L i) = blkA L i := by
  have := blk_le hL hi; have := hL.nb; have := hL.rpos
  exact addr_add (by omega)

theorem blk_in (hL : L.Ok) {i : Nat} (hi : i < L.pp) : InBuf L ⟨blkA L i, L.r.toNat * 128⟩ :=
  .inl (within_off _ (blk_le hL hi))

/-- The regions a call of ROMix on block `i` writes. -/
abbrev romixWr (L : Lay) (i : Nat) : List Region :=
  [⟨blkA L i, L.r.toNat * 128⟩, ⟨State.addr L.v, L.vlen.toNat * 128⟩, ⟨State.addr L.scr, (L.r.toNat + 2) * 128⟩]

/-- ROMix's stack arguments. -/
abbrev romixRd (L : Lay) : List Region := [⟨State.addr (L.sp - BitVec.ofNat 32 8), 8⟩]

theorem r2 (hL : L.Ok) : (L.r + 2).toNat = L.r.toNat + 2 := by
  have := hL.r_lt
  rw [BitVec.toNat_add, show (2 : BitVec 32).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]

theorem args8_sub (hL : L.Ok) : Region.Sub ⟨State.addr (L.sp - BitVec.ofNat 32 8), 8⟩ L.STK := by
  rw [addr_sub' (by have := hL.nS; omega), Offset.sub_ofNat_eq _ (by omega : 8 ≤ 40)]
  exact Offset.sub_base _ (by omega)

theorem romix_wsub (hL : L.Ok) {i : Nat} (hi : i < L.pp) : ∀ r ∈ romixWr L i, InBuf L r := by
  simp only [romixWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact blk_in hL hi
  · exact .inr (.inl (within_base _ (Nat.le_refl _)))
  · exact .inr (.inr (.inl (within_base _ (by have := hL.slen; omega))))

theorem romix_pre (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (blkAt L i) t) :
    Proof.Scrypt.roMixArm.pre ((pushed [.r12, .lr] t).callEntry.withRegions (romixRd L) (romixWr L i)) := by
  have hS := hL.nS
  have hA := hL.nA
  have s8 : 8 ≤ t.sp.toNat := by rw [hc.sp]; omega
  have hb := blk_in hL hi
  have hv : InBuf L ⟨State.addr L.v, L.vlen.toNat * 128⟩ := .inr (.inl (within_base _ (Nat.le_refl _)))
  have hs : InBuf L ⟨State.addr L.scr, (L.r.toNat + 2) * 128⟩ :=
    .inr (.inr (.inl (within_base _ (by have := hL.slen; omega))))
  have h8 : (L.sp - BitVec.ofNat 32 8).toNat = L.sp.toNat - 8 := sub_toNat' (by omega)
  simp only [Proof.Scrypt.roMixArm, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.withRegions_gpr, State.callEntry_sp, pushed_sp, p2_argAddr, p2_arg0 s8, p2_arg1,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    pushed_gpr, hc.sp, ha.r0, ha.r1, ha.r2, ha.r3, ha.r12, ha.lr, r2 hL, addr_blk hL hi]
  have kb := Within.sub (within_off (State.addr L.b) (blk_le hL hi))
  have ks := Within.sub (within_base (State.addr L.scr) (n := (L.r.toNat + 2) * 128) (k := L.slen.toNat * 128)
    (by have := hL.slen; omega))
  have := blk_le hL hi; have := hL.nb; have := hL.nv; have := hL.nc; have := hL.slen; have := hL.blen_lt; have := hL.rpos
  have tb : (blkAt L i).toNat = L.b.toNat + 128 * L.r.toNat * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 128 * L.r.toNat * i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  exact ⟨trivial, trivial, hL.bv.sub_left kb, (hL.bc.sub_left kb).sub_right ks, hL.vc.sub_right ks,
    (hL.stk_in hb).sub_left (args8_sub hL), (hL.stk_in hv).sub_left (args8_sub hL),
    (hL.stk_in hs).sub_left (args8_sub hL), by rw [tb]; omega, by omega, by omega,
    by simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, h8]; omega, hL.rpos,
    hL.vmod, Whole.valid_pow hL.valid, trivial⟩

theorem romix_cov (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp) :
    Covers (romixRd L ++ romixWr L i) ((pushed [.r12, .lr] t).rd ++ (pushed [.r12, .lr] t).wr) ∧
      Covers (romixWr L i) (pushed [.r12, .lr] t).wr := by
  have upw : ∀ {r : Region}, (∃ R ∈ t.wr, Within r R) → ∃ R ∈ (pushed [.r12, .lr] t).wr, Within r R :=
    fun ⟨R, hR, hw⟩ => ⟨R, by rw [pushed_wr]; simp [hR], hw⟩
  have hw := romix_wsub hL hi
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => upw ((hw r hr).wr hc)⟩
  rcases List.mem_append.mp hr with hr | hr
  · simp only [romixRd, List.mem_singleton] at hr; subst hr
    refine ⟨⟨State.addr (t.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)), 4 * [Reg.r12, Reg.lr].length⟩,
      by rw [pushed_wr]; simp, 0, ?_, by simp⟩
    simp only [hc.sp, BitVec.add_zero]; rfl
  · obtain ⟨R, hR, hw'⟩ := upw ((hw r hr).wr hc)
    exact ⟨R, List.mem_append_right _ hR, hw'⟩

theorem roMix_stack : armStack Impl.Scrypt.Arm.roMix ≤ 16 := by lit_decide

/-- The stack `frame2_ok` lets a call change is in `STK`. -/
theorem stk_sub {t : State} (hc : Ctx L g m₀ t) : Region.Sub (stk t) L.STK := by
  simp only [stk, hc.sp]
  show Region.Sub ⟨State.addr L.sp - BitVec.ofNat 64 24, 24⟩ ⟨State.addr L.sp - BitVec.ofNat 64 40, 40⟩
  rw [Offset.sub_ofNat_eq _ (by omega : 24 ≤ 40)]
  exact Offset.sub_base _ (by omega)

/-- The regions a call of ROMix writes miss our stack arguments and the save area. -/
theorem romix_apart (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    ∀ R ∈ romixWr L i ++ [L.STK], L.ARGS.Disjoint R ∧ L.SV.Disjoint R := by
  have hw := romix_wsub hL hi
  intro R hR
  rcases List.mem_append.mp hR with hR | hR
  · refine ⟨hL.args_in (hw R hR), ?_⟩
    simp only [romixWr, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact (hL.bc.symm.sub_left hL.sv_sc).sub_right (Within.sub (within_off _ (blk_le hL hi)))
    · exact hL.vc.symm.sub_left hL.sv_sc
    · exact (Offset.disjoint_base _ (by have := hL.slen; omega) (by have := hL.nc; have := hL.slen; omega))
  · simp only [List.mem_singleton] at hR; subst hR
    exact ⟨(stk_args hL).symm, (stk_sv hL).symm⟩

theorem romix_call (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.frame (.push [.r12, .lr]) (.call "vg_scrypt_romix" Impl.Scrypt.Arm.roMix) (.pop .r12 8)) t
      fun t' => Ctx L g m₀ t' ∧ t'.gpr .r4 = t.gpr .r4 ∧
        Frame (romixWr L i ++ [L.STK]) t.mem t'.mem ∧
        bytesAt t'.mem (blkA L i) (128 * L.r.toNat) =
          Spec.Scrypt.roMix L.r.toNat L.NN (bytesAt t.mem (blkA L i) (128 * L.r.toNat)) := by
  have hS := hL.nS
  obtain ⟨cov, covw⟩ := romix_cov hL hc hi
  refine frame2_ok (by decide) (by decide) RoMix.roMix_correct roMix_stack (by rw [hc.sp]; omega)
    (romix_pre hL hc hi ha) cov covw fun s₂ h2 hpost => ?_
  have hf : Frame (romixWr L i ++ [L.STK]) t.mem (popped .r12 8 s₂).mem :=
    Frame.sub h2.frame fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.STK, by simp, stk_sub hc⟩
  have ap := romix_apart hL hi
  refine ⟨⟨h2.rd.trans hc.rd, h2.wr.trans hc.wr, h2.sp.trans hc.sp,
    (h2.cs .r5 (by decide) (by decide)).trans hc.r5, (h2.cs .r6 (by decide) (by decide)).trans hc.r6,
    (h2.cs .r7 (by decide) (by decide)).trans hc.r7, (h2.cs .r8 (by decide) (by decide)).trans hc.r8,
    (h2.cs .r9 (by decide) (by decide)).trans hc.r9, hc.args.frame hf fun R hR => (ap R hR).1,
    hc.saved.frame hf fun R hR => (ap R hR).2, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩,
    h2.cs .r4 (by decide) (by decide), hf, ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨R, hR, hs⟩ := (romix_wsub hL hi r hr).sub
      rcases hR with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
      · exact ⟨_, by simp, hs⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.STK, by simp, fun _ h => h⟩
  · have h := hpost
    simp only [Proof.Scrypt.roMixArm, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), pushed_gpr, ha.r0, ha.r1, ha.r3,
      addr_blk hL hi] at h
    have f₀ := pushed_frameA (rs := [Reg.r12, Reg.lr]) (s := t)
      (by simp only [List.length_cons, List.length_nil]; rw [hc.sp]; omega)
    have e : Spec.Scrypt.bytesAt (pushed [.r12, .lr] t).mem (blkA L i) (128 * L.r.toNat) =
        bytesAt t.mem (blkA L i) (128 * L.r.toNat) :=
      Memory.frame_bytesAt f₀ (fun R hR => by
        simp only [List.mem_singleton] at hR; subst hR
        have hs : Region.Sub ⟨State.addr (t.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)),
            4 * [Reg.r12, Reg.lr].length⟩ L.STK := by
          rw [hc.sp]; exact args8_sub hL
        rw [Nat.mul_comm]
        exact ((hL.stk_in (blk_in hL hi)).sub_left hs).symm) (by have := hL.r_lt; omega)
    rw [e] at h
    exact h

end

end VG.Proof.Scrypt.Arm.Whole
