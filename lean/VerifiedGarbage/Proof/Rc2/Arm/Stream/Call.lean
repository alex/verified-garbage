import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Verified
import VerifiedGarbage.Proof.Rc2.Arm.Key
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Impl.Rc2.Arm.Stream
import VerifiedGarbage.Proof.Rc2.Stream

/-!
# Streaming RC2-CBC on ARMv7: the calls

Untrusted: everything here is checked by Lean.

The callees take their scratch buffer `S` on the stack: a frame pushes it
(`push {r12, lr}`, with `S` in `r12` at `[sp]`) around the call. `key_call`
and `cbc_call` run the frame around the call of `vg_rc2_expand_key` and of
the CBC function: memory changes only in the callee's writable buffers and
the 8 bytes below the stack pointer. `key_rel` and `cbc_rel`: the frames, with
the same arguments and stack pointer in two runs, are constant time.
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Impl.Rc2.Arm

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

theorem storeWords_two (m : Mem) (a : BitVec 32) (x y : BitVec 32) :
    storeWords m a [x, y] = (m.writeW (State.addr a) x).writeW (State.addr (a + 4)) y := rfl

/-- The 8 bytes below the stack pointer, where the frame pushes `S` and `lr`. -/
abbrev below (s : State) : Region := ⟨State.addr s.sp - 8, 8⟩

/-- The callee's stack argument. -/
abbrev argR (s : State) : Region := ⟨State.addr s.sp - 8, 4⟩

/-- The state the callee runs from, with the permissions it is given. -/
abbrev view (s : State) (rd wr : List Region) : State :=
  (pushed [.r12, .lr] s).callEntry.withRegions rd wr

theorem e8 : BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length) = 8 := rfl

section
variable {s : State} (hsp : 8 ≤ s.sp.toNat)
include hsp

theorem hA : State.addr (s.sp - 8) = State.addr s.sp - 8 := addr_sub hsp

theorem hA4 : State.addr (s.sp - 8 + BitVec.ofNat 32 4) = State.addr s.sp - 8 + 4 := by
  have := s.sp.isLt
  have e : (s.sp - 8).toNat = s.sp.toNat - 8 := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hsp)
  rw [addr_add (by rw [e]; omega), hA hsp]; rfl

theorem amem : (pushed [.r12, .lr] s).mem =
    (s.mem.writeW (State.addr s.sp - 8) (s.gpr .r12)).writeW (State.addr s.sp - 8 + 4) (s.gpr .lr) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)) [s.gpr .r12, s.gpr .lr] = _
  rw [e8, storeWords_two, hA hsp, show (s.sp - 8 + 4 : BitVec 32) = s.sp - 8 + BitVec.ofNat 32 4 from rfl,
    hA4 hsp]

theorem fA : Frame [below s] s.mem (pushed [.r12, .lr] s).mem := by
  rw [amem hsp]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left]; decide

theorem sa0 (rd wr : List Region) : stackArgAddr (view s rd wr) 0 = State.addr s.sp - 8 := by
  unfold stackArgAddr
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, e8]
  rw [show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from BitVec.add_zero _, hA hsp]

theorem arg0 (rd wr : List Region) : stackArg (view s rd wr) 0 = s.gpr .r12 := by
  rw [stackArg, sa0 hsp, State.withRegions_mem, State.callEntry_mem, amem hsp, Mem.readW_writeW_sep
    (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem view_sp (rd wr : List Region) : (view s rd wr).sp.toNat = s.sp.toNat - 8 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, e8]
  exact BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hsp)

/-- The callee's regions, which the frame covers with `s`'s. -/
theorem cov {rd wr : List Region} (hr : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers (rd ++ argR s :: wr) ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  intro x n' ⟨r, hr', hc⟩
  rcases List.mem_append.mp hr' with h' | h'
  · obtain ⟨r', hr'', hc'⟩ := hr x n' ⟨r, h', hc⟩
    refine ⟨r', ?_, hc'⟩
    rcases List.mem_append.mp hr'' with h'' | h''
    · exact List.mem_append_left _ h''
    · exact List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ h'')
  · rcases List.mem_cons.mp h' with rfl | h'
    · have eb : (⟨State.addr (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)),
          4 * [Reg.r12, Reg.lr].length⟩ : Region) = below s := by rw [e8, hA hsp]; rfl
      refine ⟨below s, List.mem_append_right _ (by rw [pushed_wr, eb]; exact List.mem_cons_self ..), ?_⟩
      simp only [Region.Contains] at hc ⊢; omega
    · obtain ⟨r', hr'', hc'⟩ := hw x n' ⟨r, h', hc⟩
      exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr''), hc'⟩

end

theorem covW {s : State} {wr : List Region} (hw : Covers wr s.wr) : Covers wr (pushed [.r12, .lr] s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := hw x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

theorem view_gpr (s : State) (rd wr : List Region) (r : Reg) (hr : r ∉ linkRegs) :
    (view s rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

/-! ## `vg_rc2_expand_key` -/

/-- What the call of `vg_rc2_expand_key` needs. -/
structure KeyPre (s : State) (K KL E O S : BitVec 32) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = KL
  r2 : s.gpr .r2 = E
  r3 : s.gpr .r3 = O
  r12 : s.gpr .r12 = S
  hsp : 8 ≤ s.sp.toNat
  valid : Spec.Rc2.validKey KL.toNat E.toNat
  ko : (⟨State.addr K, KL.toNat⟩ : Region).Disjoint ⟨State.addr O, 128⟩
  ks : (⟨State.addr K, KL.toNat⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  os : (⟨State.addr O, 128⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  bk : (below s).Disjoint ⟨State.addr K, KL.toNat⟩
  bo : (below s).Disjoint ⟨State.addr O, 128⟩
  bs : (below s).Disjoint ⟨State.addr S, 512⟩
  hK : K.toNat + KL.toNat ≤ 2 ^ 32
  hO : O.toNat + 128 ≤ 2 ^ 32
  hS : S.toNat + 512 ≤ 2 ^ 32
  reads : Covers [⟨State.addr K, KL.toNat⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr O, 128⟩, ⟨State.addr S, 512⟩] s.wr

/-- What the call of `vg_rc2_expand_key` leaves. -/
structure KeyPost (s : State) (K KL E O S : BitVec 32) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr O, 128⟩, ⟨State.addr S, 512⟩, below s] s.mem s'.mem
  sched : Spec.Rc2.scheduleAt s'.mem (State.addr O) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (State.addr K) KL.toNat) E.toNat

abbrev keyRd (s : State) (K KL : BitVec 32) : List Region := [⟨State.addr K, KL.toNat⟩, argR s]
abbrev keyWr (O S : BitVec 32) : List Region := [⟨State.addr O, 128⟩, ⟨State.addr S, 512⟩]

theorem KeyPre.pre {s : State} {K KL E O S : BitVec 32} (h : KeyPre s K KL E O S) :
    keyContract.pre (view s (keyRd s K KL) (keyWr O S)) := by
  have hv := view_sp h.hsp (keyRd s K KL) (keyWr O S)
  simp only [keyContract, arg0 h.hsp, sa0 h.hsp, view_gpr _ _ _ .r0 (by decide), view_gpr _ _ _ .r1 (by decide),
    view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide), h.r0, h.r1, h.r2, h.r3, h.r12,
    State.withRegions_rd, State.withRegions_wr, hv]
  refine ⟨trivial, trivial, h.ko, h.ks, h.os, ?_, ?_, h.hK, h.hO, h.hS, by have := s.sp.isLt; omega, h.valid⟩
  · exact (h.bo.sub_left (Region.sub_prefix (by decide)))
  · exact (h.bs.sub_left (Region.sub_prefix (by decide)))

theorem key_noCalls : expandKey.noCalls = true := by decide +kernel

theorem key_call {s : State} {K KL E O S : BitVec 32} (h : KeyPre s K KL E O S) :
    WP isa Stream.keyCall s (KeyPost s K KL E O S) := by
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h.hsp) (by simp) ?_
  refine WP.call (k := keyContract) key_correct (rd := keyRd s K KL) (wr := keyWr O S) h.pre
    (cov h.hsp h.reads h.writes) (covW h.writes) ?_ key_noCalls
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  have bytesK : Spec.Rc2.bytesAt (pushed [.r12, .lr] s).mem (State.addr K) KL.toNat =
      Spec.Rc2.bytesAt s.mem (State.addr K) KL.toNat :=
    VG.Proof.Rc2.bytesAt_frame (fA h.hsp) _ _ (by omega) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bk.symm)
  change Spec.Rc2.scheduleAt s₂.mem _ = _ at hpost
  simp only [State.withRegions_mem, State.callEntry_mem, view_gpr _ _ _ .r0 (by decide),
    view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, bytesK] at hpost
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, pushed_sp, e8]; exact BitVec.sub_add_cancel _ _
  · have : r ≠ .r12 := by intro e; subst e; simp [preserved] at hr
    rw [popped_gpr this, hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    refine ((fA h.hsp).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (hf.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]; exact hpost

theorem key_rel {K KL E O S sp₀ : BitVec 32} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → KeyPre s₁ K KL E O S ∧ KeyPre s₂ K KL E O S ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa P Stream.keyCall fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, h₁, h₂⟩ := h _ _ hp; rw [h₁, h₂]) ?_
  refine RelCT.call key_correct expandKey_constantTime
    [⟨State.addr K, KL.toNat⟩, ⟨State.addr sp₀ - 8, 4⟩] (keyWr O S) fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_
  obtain ⟨h₁, h₂, sp₁, sp₂⟩ := h _ _ hp
  rw [push_pushed rfl (by simpa using h₁.hsp), Option.some.injEq] at pa
  rw [push_pushed rfl (by simpa using h₂.hsp), Option.some.injEq] at pb
  subst pa pb
  have e₁ : keyRd s₁ K KL = [⟨State.addr K, KL.toNat⟩, ⟨State.addr sp₀ - 8, 4⟩] := by rw [← sp₁]
  have e₂ : keyRd s₂ K KL = [⟨State.addr K, KL.toNat⟩, ⟨State.addr sp₀ - 8, 4⟩] := by rw [← sp₂]
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  have c₁ := cov h₁.hsp h₁.reads h₁.writes
  have c₂ := cov h₂.hsp h₂.reads h₂.writes
  rw [show argR s₁ = ⟨State.addr sp₀ - 8, 4⟩ by rw [← sp₁]] at c₁
  rw [show argR s₂ = ⟨State.addr sp₀ - 8, 4⟩ by rw [← sp₂]] at c₂
  have a₁ := arg0 h₁.hsp (keyRd s₁ K KL) (keyWr O S)
  have a₂ := arg0 h₂.hsp (keyRd s₂ K KL) (keyWr O S)
  rw [view, e₁] at p₁ a₁
  rw [view, e₂] at p₂ a₂
  refine ⟨p₁, p₂, ?_, c₁, covW h₁.writes, c₂, covW h₂.writes⟩
  simp only [keyContract, a₁, a₂, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, pushed_sp, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), pushed_gpr, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1,
    h₂.r2, h₂.r3, h₁.r12, h₂.r12, sp₁, sp₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## The CBC functions -/

theorem cbc_correct' (d : Spec.Rc2.Direction) (s : State) (hs : (Cbc.contract d).pre s) :
    ∃ t s', Exec isa (Impl.Rc2.Arm.Cbc.cbc d) s t s' ∧ abiPreserved s s' ∧ (Cbc.contract d).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := Cbc.cbc_body_correct d s hs
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem cbc_noFrames (d : Spec.Rc2.Direction) : (Impl.Rc2.Arm.Cbc.cbc d).noFrames = true := by
  cases d <;> decide +kernel

/-- The name of the CBC function. -/
def cbcName : Spec.Rc2.Direction → String
  | .encrypt => "vg_rc2_cbc_encrypt"
  | .decrypt => "vg_rc2_cbc_decrypt"

theorem cbcCall_eq (d : Spec.Rc2.Direction) : Stream.cbcCall d =
    .frame (.push [.r12, .lr]) (.call (cbcName d) (Impl.Rc2.Arm.Cbc.cbc d)) (.pop .r12 8) := by
  cases d <;> rfl

/-- What the call of the CBC function needs. -/
structure CbcPre (s : State) (K I D N S : BitVec 32) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = I
  r2 : s.gpr .r2 = D
  r3 : s.gpr .r3 = N
  r12 : s.gpr .r12 = S
  hsp : 8 ≤ s.sp.toNat
  ki : (⟨State.addr K, 128⟩ : Region).Disjoint ⟨State.addr I, 8⟩
  kd : (⟨State.addr K, 128⟩ : Region).Disjoint ⟨State.addr D, 8 * N.toNat⟩
  ks : (⟨State.addr K, 128⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  id : (⟨State.addr I, 8⟩ : Region).Disjoint ⟨State.addr D, 8 * N.toNat⟩
  is : (⟨State.addr I, 8⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  ds : (⟨State.addr D, 8 * N.toNat⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  bk : (below s).Disjoint ⟨State.addr K, 128⟩
  bi : (below s).Disjoint ⟨State.addr I, 8⟩
  bd : (below s).Disjoint ⟨State.addr D, 8 * N.toNat⟩
  bs : (below s).Disjoint ⟨State.addr S, 512⟩
  hK : K.toNat + 128 ≤ 2 ^ 32
  hI : I.toNat + 8 ≤ 2 ^ 32
  hD : D.toNat + 8 * N.toNat ≤ 2 ^ 32
  hS : S.toNat + 512 ≤ 2 ^ 32
  reads : Covers [⟨State.addr K, 128⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr I, 8⟩, ⟨State.addr D, 8 * N.toNat⟩, ⟨State.addr S, 512⟩] s.wr

/-- What the call of the CBC function leaves. -/
structure CbcPost (d : Spec.Rc2.Direction) (s : State) (K I D N S : BitVec 32) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr I, 8⟩, ⟨State.addr D, 8 * N.toNat⟩, ⟨State.addr S, 512⟩, below s] s.mem s'.mem
  data : Spec.Rc2.blocksAt s'.mem (State.addr D) N.toNat =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (State.addr K)) d (Spec.Rc2.blockAt s.mem (State.addr I))
      (Spec.Rc2.blocksAt s.mem (State.addr D) N.toNat)).1
  iv : Spec.Rc2.blockAt s'.mem (State.addr I) =
    (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (State.addr K)) d (Spec.Rc2.blockAt s.mem (State.addr I))
      (Spec.Rc2.blocksAt s.mem (State.addr D) N.toNat)).2

abbrev cbcRd (s : State) (K : BitVec 32) : List Region := [⟨State.addr K, 128⟩, argR s]
abbrev cbcWr (I D N S : BitVec 32) : List Region :=
  [⟨State.addr I, 8⟩, ⟨State.addr D, 8 * N.toNat⟩, ⟨State.addr S, 512⟩]

theorem CbcPre.pre {d : Spec.Rc2.Direction} {s : State} {K I D N S : BitVec 32} (h : CbcPre s K I D N S) :
    (Cbc.contract d).pre (view s (cbcRd s K) (cbcWr I D N S)) := by
  have hv := view_sp h.hsp (cbcRd s K) (cbcWr I D N S)
  simp only [Cbc.contract, arg0 h.hsp, sa0 h.hsp, view_gpr _ _ _ .r0 (by decide), view_gpr _ _ _ .r1 (by decide),
    view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide), h.r0, h.r1, h.r2, h.r3, h.r12,
    State.withRegions_rd, State.withRegions_wr, hv]
  refine ⟨trivial, trivial, h.ki, h.kd, h.ks, h.id, h.is, h.ds, ?_, ?_, ?_, h.hK, h.hI, h.hS,
    by have := s.sp.isLt; omega, h.hD⟩
  · exact (h.bi.sub_left (Region.sub_prefix (by decide))).symm
  · exact (h.bd.sub_left (Region.sub_prefix (by decide))).symm
  · exact (h.bs.sub_left (Region.sub_prefix (by decide))).symm

theorem cbc_call {d : Spec.Rc2.Direction} {s : State} {K I D N S : BitVec 32} (h : CbcPre s K I D N S) :
    WP isa (Stream.cbcCall d) s (CbcPost d s K I D N S) := by
  rw [cbcCall_eq]
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h.hsp) (by simp) ?_
  refine WP.callCalls (k := Cbc.contract d) (cbc_correct' d) (rd := cbcRd s K) (wr := cbcWr I D N S) h.pre
    (cov h.hsp h.reads h.writes) (covW h.writes) ?_ (cbc_noFrames d)
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  have fK := Proof.Rc2.scheduleAt_frame (fA h.hsp) (State.addr K) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bk.symm)
  have fI := Proof.Rc2.blockAt_frame (fA h.hsp) (State.addr I) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bi.symm)
  have fD := Proof.Rc2.blocksAt_frame (fA h.hsp) (State.addr D) N.toNat (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bd.symm)
  obtain ⟨p₁, p₂⟩ := hpost
  simp only [State.withRegions_mem, State.callEntry_mem, view_gpr _ _ _ .r0 (by decide),
    view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, fK, fI, fD] at p₁ p₂
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, pushed_sp, e8]; exact BitVec.sub_add_cancel _ _
  · have : r ≠ .r12 := by intro e; subst e; simp [preserved] at hr
    rw [popped_gpr this, hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    refine ((fA h.hsp).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (hf.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]; exact p₁
  · rw [popped_mem]; exact p₂

theorem cbc_rel {d : Spec.Rc2.Direction} {K I D N S sp₀ : BitVec 32} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → CbcPre s₁ K I D N S ∧ CbcPre s₂ K I D N S ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa P (Stream.cbcCall d) fun _ _ => True := by
  rw [cbcCall_eq]
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, h₁, h₂⟩ := h _ _ hp; rw [h₁, h₂]) ?_
  refine RelCT.call (cbc_correct' d) (Cbc.cbc_constantTime d)
    [⟨State.addr K, 128⟩, ⟨State.addr sp₀ - 8, 4⟩] (cbcWr I D N S) fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_
  obtain ⟨h₁, h₂, sp₁, sp₂⟩ := h _ _ hp
  rw [push_pushed rfl (by simpa using h₁.hsp), Option.some.injEq] at pa
  rw [push_pushed rfl (by simpa using h₂.hsp), Option.some.injEq] at pb
  subst pa pb
  have e₁ : cbcRd s₁ K = [⟨State.addr K, 128⟩, ⟨State.addr sp₀ - 8, 4⟩] := by rw [← sp₁]
  have e₂ : cbcRd s₂ K = [⟨State.addr K, 128⟩, ⟨State.addr sp₀ - 8, 4⟩] := by rw [← sp₂]
  have p₁ := h₁.pre (d := d)
  have p₂ := h₂.pre (d := d)
  have c₁ := cov h₁.hsp h₁.reads h₁.writes
  have c₂ := cov h₂.hsp h₂.reads h₂.writes
  rw [show argR s₁ = ⟨State.addr sp₀ - 8, 4⟩ by rw [← sp₁]] at c₁
  rw [show argR s₂ = ⟨State.addr sp₀ - 8, 4⟩ by rw [← sp₂]] at c₂
  have a₁ := arg0 h₁.hsp (cbcRd s₁ K) (cbcWr I D N S)
  have a₂ := arg0 h₂.hsp (cbcRd s₂ K) (cbcWr I D N S)
  rw [view, e₁] at p₁ a₁
  rw [view, e₂] at p₂ a₂
  refine ⟨p₁, p₂, ?_, c₁, covW h₁.writes, c₂, covW h₂.writes⟩
  simp only [Cbc.contract, a₁, a₂, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, pushed_sp, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), pushed_gpr, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1,
    h₂.r2, h₂.r3, h₁.r12, h₂.r12, sp₁, sp₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.Rc2.Arm.Stream
