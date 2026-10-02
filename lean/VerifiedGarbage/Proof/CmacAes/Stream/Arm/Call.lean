import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Contract
import VerifiedGarbage.Proof.MlKem.Arm.CallF
import VerifiedGarbage.Proof.Framework.OffsetBelow

/-!
# Streaming AES-CMAC on ARMv7: the calls

A call of each function the streaming functions call (`vg_aes_expand_key`,
`vg_cmac_aes_subkeys`, and `vg_cmac_aes_update` and `vg_cmac_aes_finalize` in
the frame that pushes their two stack arguments), from its contract: what it
needs (`…Args`), what it leaves (`…Post`, in terms of the memory before the
call), and that two calls with the same arguments leak the same (`…_rel`).

`vg_cmac_aes_subkeys`, `vg_cmac_aes_update` and `vg_cmac_aes_finalize` have
frames of their own (`WP.callF`), 8 bytes below their stack pointer; with
the pushed stack arguments, a call of the last two uses the 16 bytes below
ours (`blw16`).
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm
open VG.Proof.CmacAes.Arm (addr_sub storeWords_two e8 toNat_rounds)

theorem sub8_8 (p : Addr) : p - 8 - 8 = p - 16 := Offset.sub_sub_ofNat p 8 8

/-- The 16 bytes below the stack pointer. -/
abbrev blw16 (s : State) : Region := ⟨State.addr s.sp - 16, 16⟩

/-- The state a function called in a frame pushing `ra` and `rb` runs from,
with the permissions it is given. -/
abbrev view (ra rb : Reg) (s : State) (rd wr : List Region) : State :=
  (pushed [ra, rb] s).callEntry.withRegions rd wr

theorem view_gpr {ra rb : Reg} {s : State} {rd wr : List Region} (r : Reg) (hr : r ∉ linkRegs) :
    (view ra rb s rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

theorem view_sp {ra rb : Reg} {s : State} {rd wr : List Region} : (view ra rb s rd wr).sp = s.sp - 8 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, e8]

section
variable {s : State} (hsp : 16 ≤ s.sp.toNat)
include hsp

theorem hA : State.addr (s.sp - 8) = State.addr s.sp - 8 := addr_sub (k := 8) (by omega)

theorem spA : (s.sp - 8).toNat = s.sp.toNat - 8 :=
  BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact Nat.le_trans (by decide) hsp)

theorem hA4 : State.addr (s.sp - 8 + BitVec.ofNat 32 4) = State.addr s.sp - 8 + 4 := by
  have := s.sp.isLt
  rw [addr_add (by rw [spA hsp]; omega), hA hsp]; rfl

theorem amem (ra rb : Reg) : (pushed [ra, rb] s).mem =
    (s.mem.writeW (State.addr s.sp - 8) (s.gpr ra)).writeW (State.addr s.sp - 8 + 4) (s.gpr rb) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [ra, rb].length)) [s.gpr ra, s.gpr rb] = _
  rw [e8, storeWords_two, hA hsp, show (s.sp - 8 + 4 : BitVec 32) = s.sp - 8 + BitVec.ofNat 32 4 from rfl,
    hA4 hsp]

theorem push_frame (ra rb : Reg) : Frame [⟨State.addr s.sp - 8, 8⟩] s.mem (pushed [ra, rb] s).mem := by
  rw [amem hsp]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left]; decide

theorem push_slot (ra rb : Reg) : (pushed [ra, rb] s).mem.readW (State.addr s.sp - 8) 32 = s.gpr ra := by
  rw [amem hsp, Mem.readW_writeW_sep
    (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem push_slot1 (ra rb : Reg) : (pushed [ra, rb] s).mem.readW (State.addr s.sp - 8 + 4) 32 = s.gpr rb := by
  rw [amem hsp, Mem.readW_writeW_self32]

/-- The stack arguments, as the callee reads them. -/
theorem view_arg0 {ra rb : Reg} {rd wr : List Region} : stackArg (view ra rb s rd wr) 0 = s.gpr ra := by
  rw [stackArg, show stackArgAddr (view ra rb s rd wr) 0 = State.addr s.sp - 8 by
      unfold stackArgAddr; rw [view_sp, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from
        BitVec.add_zero _, hA hsp],
    State.withRegions_mem, State.callEntry_mem, push_slot hsp]

theorem view_arg1 {ra rb : Reg} {rd wr : List Region} : stackArg (view ra rb s rd wr) 1 = s.gpr rb := by
  rw [stackArg, show stackArgAddr (view ra rb s rd wr) 1 = State.addr s.sp - 8 + 4 by
      unfold stackArgAddr; rw [view_sp]; exact hA4 hsp,
    State.withRegions_mem, State.callEntry_mem, push_slot1 hsp]

theorem view_argAddr {ra rb : Reg} {rd wr : List Region} :
    stackArgAddr (view ra rb s rd wr) 0 = State.addr s.sp - 8 := by
  unfold stackArgAddr; rw [view_sp, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from
    BitVec.add_zero _, hA hsp]

theorem view_below {ra rb : Reg} {rd wr : List Region} :
    State.addr (view ra rb s rd wr).sp - 8 = State.addr s.sp - 16 := by
  rw [view_sp, hA hsp, sub8_8]

omit hsp in
theorem slot_sub : Region.Sub ⟨State.addr s.sp - 8, 8⟩ (blw16 s) :=
  Offset.sub_below (State.addr s.sp) (a := 8) (b := 16) (by decide) (by decide)

omit hsp in
theorem lo_sub : Region.Sub ⟨State.addr s.sp - 16, 8⟩ (blw16 s) := Region.sub_prefix (by decide)

end

/-- A call of `c` (with frames using 8 bytes of stack) in the frame that
pushes its two stack arguments `ra` and `rb`, from its contract `k`: it
runs from `view`, and changes memory only within the regions it may write
and the 16 bytes below the stack pointer; the pop loads `ra` back, so it
changes no callee-saved register but `lr`. -/
theorem WP.frameCallF {ra rb : Reg} {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsu : stackUse c = 8) (hregs : regList [ra, rb] = true) {s : State} (hsp : 16 ≤ s.sp.toNat)
    {rd wr : List Region} (hpre : k.pre (view ra rb s rd wr))
    (hc : Covers (rd ++ wr) ((pushed [ra, rb] s).rd ++ (pushed [ra, rb] s).wr))
    (hw : Covers wr (pushed [ra, rb] s).wr) (hb : ∀ r ∈ wr, (blw16 s).Disjoint r) {Q : State → Prop}
    (hQ : ∀ s' s₂ : State, s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame (wr ++ [blw16 s]) s.mem s'.mem → (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.mem = s₂.mem → k.post (view ra rb s rd wr) (s₂.withRegions rd wr) → Q s') :
    WP isa (.frame (.push [ra, rb]) (.call name c) (.pop ra 8)) s Q := by
  have hspA := spA hsp
  refine WP.frame (rs := [ra, rb]) (r := ra) hregs (by simp only [List.length_cons, List.length_nil]; omega)
    (by simp) ?_
  refine WP.callF hv hpre hc hw (by rw [hsu, pushed_sp, e8, hspA]; omega)
    fun s₂ hrd₂ hwr₂ hsp₂ hf hcs hpost => ?_
  rw [pushed_sp, e8, hsu] at hf
  rw [pushed_sp, e8] at hsp₂
  have hbA : belowA (s.sp - 8) 8 = ⟨State.addr s.sp - 16, 8⟩ := by
    simp only [belowA, hA hsp]; exact congrArg (fun b => (⟨b, 8⟩ : Region)) (sub8_8 _)
  rw [hbA] at hf
  -- The slot the pop loads.
  have slot : s₂.mem.readW (State.addr s₂.sp) 32 = s.gpr ra := by
    rw [hsp₂, hA hsp]
    rw [hf.readW (r := ⟨State.addr s.sp - 8, 4⟩) (Region.contains_self _ _) (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact ((hb r hr).sub_left (slot_sub (s := s))).sub_left (Region.sub_prefix (by decide))
      · rw [List.mem_singleton] at hr; subst hr
        have := Offset.below_disjoint (State.addr s.sp - 8) (m := 8) (l := 4) (by decide)
        exact (Offset.sub_sub_ofNat (State.addr s.sp) 8 8 ▸ this).symm) (by decide), push_slot hsp]
  refine hQ _ s₂ ?_ ?_ ?_ ?_ (fun r hr hlr => ?_) (popped_mem _ _ _) hpost
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂]; exact BitVec.sub_add_cancel _ _
  · rw [popped_mem]
    refine ((push_frame hsp ra rb).sub fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), slot_sub⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), lo_sub⟩
  · by_cases hra : r = ra
    · subst hra
      show (s₂.setReg r (s₂.mem.readW (State.addr s₂.sp) 32)).gpr r = _
      rw [VG.Arm.RegUpd.gpr_setReg_self, slot]
    · rw [popped_gpr hra, hcs r hr hlr, pushed_gpr]

/-- Two runs of such a call leak the same if the callee's contract holds
in both, its public data agree, and the stack pointers are the same. -/
theorem RelCT.frameCall {ra rb : Reg} {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hregs : regList [ra, rb] = true) {rd wr : List Region}
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧ 8 ≤ s₁.sp.toNat ∧ 8 ≤ s₂.sp.toNat ∧
      k.pre (view ra rb s₁ rd wr) ∧ k.pre (view ra rb s₂ rd wr) ∧
      k.pub (view ra rb s₁ rd wr) (view ra rb s₂ rd wr) ∧
      Covers (rd ++ wr) ((pushed [ra, rb] s₁).rd ++ (pushed [ra, rb] s₁).wr) ∧
      Covers wr (pushed [ra, rb] s₁).wr ∧
      Covers (rd ++ wr) ((pushed [ra, rb] s₂).rd ++ (pushed [ra, rb] s₂).wr) ∧
      Covers wr (pushed [ra, rb] s₂).wr) :
    RelCT isa P (.frame (.push [ra, rb]) (.call name c) (.pop ra 8)) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => (h _ _ hp).1) ?_
  refine RelCT.call hv hct rd wr fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_
  obtain ⟨-, h₁, h₂, p₁, p₂, q, c₁, w₁, c₂, w₂⟩ := h _ _ hp
  rw [push_pushed hregs (by simpa using h₁), Option.some.injEq] at pa
  rw [push_pushed hregs (by simpa using h₂), Option.some.injEq] at pb
  subst pa pb
  exact ⟨p₁, p₂, q, c₁, w₁, c₂, w₂⟩


/-- The 8 bytes below a callee's stack pointer, for a call in the frame. -/
theorem view_blw {ra rb : Reg} {s : State} {rd wr : List Region} (hsp : 16 ≤ s.sp.toNat) :
    Region.Sub ⟨State.addr (view ra rb s rd wr).sp - BitVec.ofNat 64 8, 8⟩ (blw16 s) := by
  show Region.Sub ⟨State.addr (view ra rb s rd wr).sp - 8, 8⟩ (blw16 s)
  rw [view_below hsp]; exact lo_sub

/-- The covering of a call's regions, from those of the caller. -/
theorem cov_push {ra rb : Reg} {s : State} (hsp : 16 ≤ s.sp.toNat) {rd₀ wr : List Region}
    (hr : Covers rd₀ (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers ((rd₀ ++ [⟨State.addr s.sp - 8, 8⟩]) ++ wr) ((pushed [ra, rb] s).rd ++ (pushed [ra, rb] s).wr) := by
  intro x n ⟨r, hr', hc⟩
  rcases List.mem_append.mp hr' with hr' | hr'
  · rcases List.mem_append.mp hr' with hr' | hr'
    · obtain ⟨r', hr'', hc'⟩ := hr x n ⟨r, hr', hc⟩
      refine ⟨r', ?_, hc'⟩
      rcases List.mem_append.mp hr'' with h' | h'
      · exact List.mem_append_left _ h'
      · exact List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ h')
    · rw [List.mem_singleton] at hr'; subst hr'
      refine ⟨_, List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_self ..), ?_⟩
      rwa [e8, hA hsp]
  · obtain ⟨r', hr'', hc'⟩ := hw x n ⟨r, hr', hc⟩
    exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr''), hc'⟩

theorem covW_push {ra rb : Reg} {s : State} {wr : List Region} (hw : Covers wr s.wr) :
    Covers wr (pushed [ra, rb] s).wr := by
  intro x n hi
  obtain ⟨r', hr', hc'⟩ := hw x n hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

/-! ## `vg_cmac_aes_update` -/

theorem stackUse_update : stackUse Impl.CmacAes.Arm.update = 8 := by decide +kernel

/-- The regions `vg_cmac_aes_update` is called with. -/
abbrev uRd (s : State) (W D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr s.sp - 8, 8⟩]
abbrev uWr (C S : BitVec 32) : List Region := [⟨State.addr C, 16⟩, ⟨State.addr S, 2176⟩]

/-- What a call of `vg_cmac_aes_update` needs: the key schedule `W`, the
chaining value `C`, `n` blocks at `D`, the working space `S` and the rounds
`R`. -/
structure UArgs (s : State) (W C D S : BitVec 32) (R n : Nat) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = C
  r3 : s.gpr .r3 = D
  r9 : s.gpr .r9 = BitVec.ofNat 32 n
  r10 : s.gpr .r10 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hn : 16 * n < 2 ^ 32
  hsp : 16 ≤ s.sp.toNat
  wc : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  ws : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  dc : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  cs : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  bw : (blw16 s).Disjoint ⟨State.addr W, 240⟩
  bd : (blw16 s).Disjoint ⟨State.addr D, 16 * n⟩
  bc : (blw16 s).Disjoint ⟨State.addr C, 16⟩
  bs : (blw16 s).Disjoint ⟨State.addr S, 2176⟩
  fW : W.toNat + 240 ≤ 2 ^ 32
  fC : C.toNat + 16 ≤ 2 ^ 32
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 16⟩, ⟨State.addr S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_update` leaves. -/
structure UPost (s : State) (W C D S : BitVec 32) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 16⟩, ⟨State.addr S, 2176⟩, blw16 s] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (State.addr C) 16 =
    Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (State.addr W) (16 * (R + 1))))
      (Spec.Aes.bytesAt s.mem (State.addr C) 16) (Spec.Cmac.blocksAt s.mem (State.addr D) 16 n)

theorem UArgs.pre {s : State} {W C D S : BitVec 32} {R n : Nat} (h : UArgs s W C D S R n) :
    Proof.CmacAes.Arm.updateArm.pre (view .r9 .r10 s (uRd s W D n) (uWr C S)) := by
  have hR := toNat_rounds h.rounds
  have hN : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.hn; omega)
  have hb := view_blw (ra := .r9) (rb := .r10) (rd := uRd s W D n) (wr := uWr C S) h.hsp
  have hslot : Region.Sub ⟨stackArgAddr (view .r9 .r10 s (uRd s W D n) (uWr C S)) 0, 8⟩ (blw16 s) := by
    rw [view_argAddr h.hsp]; exact slot_sub
  simp only [Proof.CmacAes.Arm.updateArm, view_arg0 h.hsp, view_arg1 h.hsp, view_argAddr h.hsp,
    view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide), view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r9, h.r10, hR, hN, State.withRegions_rd, State.withRegions_wr]
  rw [view_argAddr h.hsp] at hslot
  have hspv := spA h.hsp
  have := h.hsp
  refine ⟨rfl, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, (h.bc.sub_left slot_sub).symm,
    (h.bs.sub_left slot_sub).symm, h.bw.sub_left hb, h.bd.sub_left hb, h.bc.sub_left hb, h.bs.sub_left hb,
    h.fW, h.fC, h.fD, h.fS, ?_, ?_, h.rounds⟩
  · rw [view_sp, hspv]; omega
  · rw [view_sp, hspv]; have := s.sp.isLt; omega

theorem upd_call {s : State} {W C D S : BitVec 32} {R n : Nat} (h : UArgs s W C D S R n) :
    WP isa Impl.CmacAes.Stream.Arm.updCall s (UPost s W C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hN : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.hn; omega)
  refine WP.frameCallF (k := Proof.CmacAes.Arm.updateArm) (fun _ hs => Proof.CmacAes.Arm.update_wp hs)
    stackUse_update rfl h.hsp h.pre (cov_push h.hsp h.reads h.writes) (covW_push h.writes) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.bc
      · exact h.bs) fun s' s₂ hrd hwr hsp hf hcs hm hpost => ?_
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  have fP := push_frame h.hsp .r9 .r10
  have keep : ∀ {p : Addr} {k : Nat}, (blw16 s).Disjoint ⟨p, k⟩ → k ≤ 2 ^ 64 →
      Spec.Aes.bytesAt (pushed [.r9, .r10] s).mem p k = Spec.Aes.bytesAt s.mem p k := fun hd hk =>
    Proof.Cmac.bytesAt_frame fP (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact (hd.sub_left slot_sub).symm) hk
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  simp only [Proof.CmacAes.Arm.updateArm, Proof.CmacAes.Arm.ciphAt, view_arg0 h.hsp,
    view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide), view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r9, hR, hN, State.withRegions_mem, State.callEntry_mem] at hpost
  rw [hm, hpost, keep (h.bw.sub_right (Region.sub_prefix hRb)) (by omega), keep h.bc (by decide)]
  congr 1
  simp only [Spec.Cmac.blocksAt]
  refine List.map_congr_left fun i hi => keep (h.bd.sub_right (Offset.sub_base _ ?_)) (by decide)
  rw [List.mem_range] at hi; omega

theorem upd_rel {W C D S sp₀ : BitVec 32} {R n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → UArgs s₁ W C D S R n ∧ UArgs s₂ W C D S R n ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa P Impl.CmacAes.Stream.Arm.updCall fun _ _ => True := by
  refine RelCT.frameCall (k := Proof.CmacAes.Arm.updateArm) (rd := [⟨State.addr W, 240⟩,
    ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr sp₀ - 8, 8⟩]) (wr := uWr C S)
    (fun _ hs => Proof.CmacAes.Arm.update_wp hs) Proof.CmacAes.Arm.update_ct rfl fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have r₁ : uRd s₁ W D n = [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [uRd, e₁]
  have r₂ : uRd s₂ W D n = [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [uRd, e₂]
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [r₁] at p₁
  rw [r₂] at p₂
  have c₁ := cov_push (ra := .r9) (rb := .r10) h₁.hsp h₁.reads h₁.writes
  have c₂ := cov_push (ra := .r9) (rb := .r10) h₂.hsp h₂.reads h₂.writes
  rw [e₁] at c₁
  rw [e₂] at c₂
  have := h₁.hsp
  refine ⟨e₁.trans e₂.symm, by omega, by have := h₂.hsp; omega, p₁, p₂, ?_, c₁, covW_push h₁.writes, c₂,
    covW_push h₂.writes⟩
  simp only [Proof.CmacAes.Arm.updateArm, view_sp, view_arg0 h₁.hsp, view_arg1 h₁.hsp, view_arg0 h₂.hsp,
    view_arg1 h₂.hsp, view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide),
    view_gpr .r3 (by decide), h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r9, h₁.r10, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.r9,
    h₂.r10, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩


/-! ## `vg_cmac_aes_finalize` -/

theorem stackUse_finalize : stackUse Impl.CmacAes.Arm.finalize = 8 := by decide +kernel

/-- The regions `vg_cmac_aes_finalize` is called with. -/
abbrev fRd (s : State) (K P : BitVec 32) (L : Nat) : List Region :=
  [⟨State.addr K, 272⟩, ⟨State.addr P, L⟩] ++ [⟨State.addr s.sp - 8, 8⟩]
abbrev fWr (St S : BitVec 32) : List Region := [⟨State.addr St, 16⟩, ⟨State.addr S, 2176⟩]

/-- What a call of `vg_cmac_aes_finalize` needs: the key schedule and
subkeys `K`, the state `St`, the `L` last bytes at `P`, the working space
`S` and the rounds `R`. -/
structure FArgs (s : State) (K St P S : BitVec 32) (L R : Nat) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = St
  r3 : s.gpr .r3 = P
  r4 : s.gpr .r4 = BitVec.ofNat 32 L
  r5 : s.gpr .r5 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16
  hsp : 16 ≤ s.sp.toNat
  kst : (⟨State.addr K, 272⟩ : Region).Disjoint ⟨State.addr St, 16⟩
  ks : (⟨State.addr K, 272⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  pst : (⟨State.addr P, L⟩ : Region).Disjoint ⟨State.addr St, 16⟩
  ps : (⟨State.addr P, L⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  sts : (⟨State.addr St, 16⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  bk : (blw16 s).Disjoint ⟨State.addr K, 272⟩
  bp : (blw16 s).Disjoint ⟨State.addr P, L⟩
  bst : (blw16 s).Disjoint ⟨State.addr St, 16⟩
  bs : (blw16 s).Disjoint ⟨State.addr S, 2176⟩
  fK : K.toNat + 272 ≤ 2 ^ 32
  fSt : St.toNat + 16 ≤ 2 ^ 32
  fP : P.toNat + L ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨State.addr K, 272⟩, ⟨State.addr P, L⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr St, 16⟩, ⟨State.addr S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_finalize` leaves. -/
structure FPost (s : State) (K St P S : BitVec 32) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr St, 16⟩, ⟨State.addr S, 2176⟩, blw16 s] s.mem s'.mem
  out : let ciph := Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (State.addr K) (16 * (R + 1)))
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (State.addr K + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem (State.addr St) 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem (State.addr St) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem (State.addr P) L)

theorem FArgs.pre {s : State} {K St P S : BitVec 32} {L R : Nat} (h : FArgs s K St P S L R) :
    Proof.CmacAes.Arm.finalizeArm.pre (view .r4 .r5 s (fRd s K P L) (fWr St S)) := by
  have hR := toNat_rounds h.rounds
  have hL : (BitVec.ofNat 32 L).toNat = L := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.len; omega)
  have hb := view_blw (ra := .r4) (rb := .r5) (rd := fRd s K P L) (wr := fWr St S) h.hsp
  simp only [Proof.CmacAes.Arm.finalizeArm, view_arg0 h.hsp, view_arg1 h.hsp, view_argAddr h.hsp,
    view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide), view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r4, h.r5, hR, hL, State.withRegions_rd, State.withRegions_wr]
  have hspv := spA h.hsp
  have := h.hsp
  refine ⟨rfl, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, (h.bst.sub_left slot_sub).symm,
    (h.bs.sub_left slot_sub).symm, h.bk.sub_left hb, h.bp.sub_left hb, h.bst.sub_left hb, h.bs.sub_left hb,
    h.fK, h.fSt, h.fP, h.fS, ?_, ?_, h.rounds, h.len⟩
  · rw [view_sp, hspv]; omega
  · rw [view_sp, hspv]; have := s.sp.isLt; omega

theorem fin_call {s : State} {K St P S : BitVec 32} {L R : Nat} (h : FArgs s K St P S L R) :
    WP isa Impl.CmacAes.Stream.Arm.finCall s (FPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL : (BitVec.ofNat 32 L).toNat = L := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.len; omega)
  refine WP.frameCallF (k := Proof.CmacAes.Arm.finalizeArm) (fun _ hs => Proof.CmacAes.Arm.finalize_wp hs)
    stackUse_finalize rfl h.hsp h.pre (cov_push h.hsp h.reads h.writes) (covW_push h.writes) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.bst
      · exact h.bs) fun s' s₂ hrd hwr hsp hf hcs hm hpost => ?_
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  have fP := push_frame h.hsp .r4 .r5
  have keep : ∀ {p : Addr} {k : Nat}, (blw16 s).Disjoint ⟨p, k⟩ → k ≤ 2 ^ 64 →
      Spec.Aes.bytesAt (pushed [.r4, .r5] s).mem p k = Spec.Aes.bytesAt s.mem p k := fun hd hk =>
    Proof.Cmac.bytesAt_frame fP (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact (hd.sub_left slot_sub).symm) hk
  have hRb : 16 * (R + 1) ≤ 272 := by rcases h.rounds with h' | h' | h' <;> omega
  simp only [Proof.CmacAes.Arm.finalizeArm, Proof.CmacAes.Arm.ciphAt, view_arg0 h.hsp,
    view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide), view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r4, hR, hL, State.withRegions_mem, State.callEntry_mem] at hpost
  have eK := keep (h.bk.sub_right (Region.sub_prefix hRb)) (by omega)
  have eK2 : Spec.Aes.bytesAt (pushed [.r4, .r5] s).mem (State.addr K + 240) 32 =
      Spec.Aes.bytesAt s.mem (State.addr K + 240) 32 :=
    keep (h.bk.sub_right (Offset.sub_base (State.addr K) (d := 240) (n := 32) (by decide))) (by decide)
  have eSt := keep h.bst (by decide)
  have eP := keep h.bp (by have := h.len; omega)
  intro _ _ hk msg hmod hne hst
  rw [eK, eK2, eSt, eP] at hpost
  rw [hm]
  exact hpost hk msg hmod hne hst

theorem fin_rel {K St P S sp₀ : BitVec 32} {L R : Nat} {Pr : State → State → Prop}
    (h : ∀ s₁ s₂, Pr s₁ s₂ → FArgs s₁ K St P S L R ∧ FArgs s₂ K St P S L R ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa Pr Impl.CmacAes.Stream.Arm.finCall fun _ _ => True := by
  refine RelCT.frameCall (k := Proof.CmacAes.Arm.finalizeArm) (rd := [⟨State.addr K, 272⟩,
    ⟨State.addr P, L⟩] ++ [⟨State.addr sp₀ - 8, 8⟩]) (wr := fWr St S)
    (fun _ hs => Proof.CmacAes.Arm.finalize_wp hs) Proof.CmacAes.Arm.finalize_ct rfl fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have r₁ : fRd s₁ K P L = [⟨State.addr K, 272⟩, ⟨State.addr P, L⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [fRd, e₁]
  have r₂ : fRd s₂ K P L = [⟨State.addr K, 272⟩, ⟨State.addr P, L⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [fRd, e₂]
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [r₁] at p₁
  rw [r₂] at p₂
  have c₁ := cov_push (ra := .r4) (rb := .r5) h₁.hsp h₁.reads h₁.writes
  have c₂ := cov_push (ra := .r4) (rb := .r5) h₂.hsp h₂.reads h₂.writes
  rw [e₁] at c₁
  rw [e₂] at c₂
  have := h₁.hsp
  refine ⟨e₁.trans e₂.symm, by omega, by have := h₂.hsp; omega, p₁, p₂, ?_, c₁, covW_push h₁.writes, c₂,
    covW_push h₂.writes⟩
  simp only [Proof.CmacAes.Arm.finalizeArm, view_sp, view_arg0 h₁.hsp, view_arg1 h₁.hsp, view_arg0 h₂.hsp,
    view_arg1 h₂.hsp, view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide),
    view_gpr .r3 (by decide), h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r4, h₁.r5, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.r4,
    h₂.r5, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_subkeys` -/

theorem stackUse_subkeys : stackUse Impl.CmacAes.Arm.subkeys = 8 := by decide +kernel

theorem cov_app {s : State} {rd wr : List Region} (hr : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers (rd ++ wr) (s.rd ++ s.wr) := by
  intro x n ⟨r, hr', hc⟩
  rcases List.mem_append.mp hr' with hr' | hr'
  · exact hr x n ⟨r, hr', hc⟩
  · obtain ⟨r', hr'', hc'⟩ := hw x n ⟨r, hr', hc⟩
    exact ⟨r', List.mem_append_right _ hr'', hc'⟩

/-- The 8 bytes below the stack pointer. -/
abbrev blw8 (s : State) : Region := ⟨State.addr s.sp - 8, 8⟩

/-- What a call of `vg_cmac_aes_subkeys` needs: the key schedule `W`, the
subkeys `K`, the working space `S` and the rounds `R`. -/
structure SArgs (s : State) (W K S : BitVec 32) (R : Nat) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = K
  r3 : s.gpr .r3 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hsp : 8 ≤ s.sp.toNat
  wk : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr K, 32⟩
  ws : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  ks : (⟨State.addr K, 32⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  bw : (blw8 s).Disjoint ⟨State.addr W, 240⟩
  bk : (blw8 s).Disjoint ⟨State.addr K, 32⟩
  bs : (blw8 s).Disjoint ⟨State.addr S, 2176⟩
  fW : W.toNat + 240 ≤ 2 ^ 32
  fK : K.toNat + 32 ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨State.addr W, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr K, 32⟩, ⟨State.addr S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_subkeys` leaves. -/
structure SPost (s : State) (W K S : BitVec 32) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr K, 32⟩, ⟨State.addr S, 2176⟩, blw8 s] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (State.addr K) 32 =
    (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (State.addr W) (16 * (R + 1)))) 16).1 ++
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (State.addr W) (16 * (R + 1)))) 16).2

theorem SArgs.pre {s : State} {W K S : BitVec 32} {R : Nat} (h : SArgs s W K S R) :
    Proof.CmacAes.Arm.subkeysArm.pre
      (s.callEntry.withRegions [⟨State.addr W, 240⟩] [⟨State.addr K, 32⟩, ⟨State.addr S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [Proof.CmacAes.Arm.subkeysArm, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    h.r0, h.r1, h.r2, h.r3, hR, State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial, h.wk, h.ws, h.ks, h.bw, h.bk, h.bs, h.fW, h.fK, h.fS, h.hsp, h.rounds⟩

theorem sub_call {s : State} {W K S : BitVec 32} {R : Nat} (h : SArgs s W K S R) :
    WP isa (.call "vg_cmac_aes_subkeys" Impl.CmacAes.Arm.subkeys) s (SPost s W K S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.callF (k := Proof.CmacAes.Arm.subkeysArm) (fun _ hs => Proof.CmacAes.Arm.subkeys_wp hs) h.pre
    (cov_app h.reads h.writes) h.writes (by rw [stackUse_subkeys]; exact h.hsp)
    fun s' hrd hwr hsp hf hcs hpost => ?_
  rw [stackUse_subkeys] at hf
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  simp only [Proof.CmacAes.Arm.subkeysArm, Proof.CmacAes.Arm.ciphAt, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    h.r0, h.r1, h.r2, hR] at hpost
  exact hpost

theorem sub_rel {W K S sp₀ : BitVec 32} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → SArgs s₁ W K S R ∧ SArgs s₂ W K S R ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa P (.call "vg_cmac_aes_subkeys" Impl.CmacAes.Arm.subkeys) fun _ _ => True := by
  refine RelCT.call (fun _ hs => Proof.CmacAes.Arm.subkeys_wp hs) Proof.CmacAes.Arm.subkeys_ct
    [⟨State.addr W, 240⟩] [⟨State.addr K, 32⟩, ⟨State.addr S, 2176⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, cov_app h₁.reads h₁.writes, h₁.writes, cov_app h₂.reads h₂.writes, h₂.writes⟩
  simp only [Proof.CmacAes.Arm.subkeysArm, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1, h₂.r2, h₂.r3, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key` -/

/-- What a call of `vg_aes_expand_key` needs: the key `Kp` of `KL` bytes,
the schedule `W` and the working space `S`. -/
structure EArgs (s : State) (Kp W S : BitVec 32) (KL : Nat) : Prop where
  r0 : s.gpr .r0 = Kp
  r1 : s.gpr .r1 = BitVec.ofNat 32 KL
  r2 : s.gpr .r2 = W
  r3 : s.gpr .r3 = S
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32
  kw : (⟨State.addr Kp, KL⟩ : Region).Disjoint ⟨State.addr W, 240⟩
  ks : (⟨State.addr Kp, KL⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  ws : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  fK : Kp.toNat + KL ≤ 2 ^ 32
  fW : W.toNat + 240 ≤ 2 ^ 32
  fS : S.toNat + 512 ≤ 2 ^ 32
  reads : Covers [⟨State.addr Kp, KL⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr W, 240⟩, ⟨State.addr S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key` leaves. -/
structure EPost (s : State) (Kp W S : BitVec 32) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr W, 240⟩, ⟨State.addr S, 512⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (State.addr W) (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (State.addr Kp) KL)

theorem toNat_klen {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) : (BitVec.ofNat 32 KL).toNat = KL := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem EArgs.pre {s : State} {Kp W S : BitVec 32} {KL : Nat} (h : EArgs s Kp W S KL) :
    Proof.Aes.expandKeyArm.pre
      (s.callEntry.withRegions [⟨State.addr Kp, KL⟩] [⟨State.addr W, 240⟩, ⟨State.addr S, 512⟩]) := by
  simp only [Proof.Aes.expandKeyArm, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    h.r0, h.r1, h.r2, h.r3, toNat_klen h.klen, State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial, h.kw, h.ks, h.ws, h.fK, h.fW, h.fS, h.klen⟩

theorem ek_call {s : State} {Kp W S : BitVec 32} {KL : Nat} (h : EArgs s Kp W S KL) :
    WP isa (.call "vg_aes_expand_key" Impl.Aes.Arm.expandKey) s (EPost s Kp W S KL) := by
  refine WP.call (k := Proof.Aes.expandKeyArm) Proof.Aes.Arm.expandKey_correct h.pre
    (cov_app h.reads h.writes) h.writes fun s' hrd hwr hsp hf hcs _ hpost => ?_
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  simp only [Proof.Aes.expandKeyArm, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    h.r0, h.r1, h.r2, toNat_klen h.klen] at hpost
  exact hpost

theorem ek_rel {Kp W S : BitVec 32} {KL : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → EArgs s₁ Kp W S KL ∧ EArgs s₂ Kp W S KL) :
    RelCT isa P (.call "vg_aes_expand_key" Impl.Aes.Arm.expandKey) fun _ _ => True := by
  refine RelCT.call Proof.Aes.Arm.expandKey_correct Proof.Aes.Arm.expandKey_ct
    [⟨State.addr Kp, KL⟩] [⟨State.addr W, 240⟩, ⟨State.addr S, 512⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, cov_app h₁.reads h₁.writes, h₁.writes, cov_app h₂.reads h₂.writes, h₂.writes⟩
  simp only [Proof.Aes.expandKeyArm, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1, h₂.r2, h₂.r3]
  exact ⟨trivial, trivial, trivial, trivial⟩

end VG.Proof.CmacAes.Stream.Arm
