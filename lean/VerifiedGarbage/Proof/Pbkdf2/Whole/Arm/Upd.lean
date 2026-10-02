import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: `update`, in its frame, of any length

`VG.Proof.Pbkdf2.Stream.Arm.UpdArgs` and `upd_frame`, for data of any length
that fits the address space (HMAC's functions only absorb constants of fewer
than 2¹⁶ bytes, which `movw` sets; we absorb the password and the salt).
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (Hash)
open VG.Proof.Pbkdf2.Stream.Arm (HashOK updK below count ce0 ce1 ce2 ce3 addr_sub addr_sub_add sep_off
  contains_off frame_app after_frame push_eq)
open Spec.Sha256 (bytesAt)

variable {H : Hash} (hH : HashOK H)

/-- What a framed call of `update` needs of the state before its push: the
state at `st` in `r0`, the count in `r2:r3`, and `len` bytes of data at `d`
and the scratch space at `sc` in `r1`, `r7` and `r10`; the regions the
callee may read and write; that they are disjoint as it needs, and from the
16 bytes below the stack pointer; and that none of them wraps around. -/
structure UpdL (s : State) (st d sc : BitVec 32) (len : Nat) : Prop where
  r0 : s.gpr .r0 = st
  r1 : s.gpr .r1 = d
  r7 : s.gpr .r7 = BitVec.ofNat 32 len
  r10 : s.gpr .r10 = sc
  hlen : len < 2 ^ 32
  sp16 : 16 ≤ s.sp.toNat
  cd : Covers [⟨State.addr d, len⟩] (s.rd ++ s.wr)
  cw : Covers [⟨State.addr st, H.S⟩, ⟨State.addr sc, hH.Wb⟩] s.wr
  st_sc : Region.Disjoint ⟨State.addr st, H.S⟩ ⟨State.addr sc, hH.Wb⟩
  d_st : Region.Disjoint ⟨State.addr d, len⟩ ⟨State.addr st, H.S⟩
  d_sc : Region.Disjoint ⟨State.addr d, len⟩ ⟨State.addr sc, hH.Wb⟩
  b_st : (below s).Disjoint ⟨State.addr st, H.S⟩
  b_d : (below s).Disjoint ⟨State.addr d, len⟩
  b_sc : (below s).Disjoint ⟨State.addr sc, hH.Wb⟩
  nst : st.toNat + H.S ≤ 2 ^ 32
  nd : d.toNat + len ≤ 2 ^ 32
  nsc : sc.toNat + hH.Wb ≤ 2 ^ 32

/-- The four words `update`'s frame pushes. -/
abbrev upd4 : List Reg := [.r1, .r7, .r10, .r12]

theorem e16 : BitVec.ofNat 32 (4 * upd4.length) = 16 := rfl

/-- The regions `update` is given: the data and its stack arguments, the state and the scratch space. -/
abbrev UpdL.rd (sp : BitVec 32) (d : BitVec 32) (len : Nat) : List Region :=
  [⟨State.addr d, len⟩, ⟨State.addr sp - 16, 12⟩]
abbrev UpdL.wr (st sc : BitVec 32) : List Region := [⟨State.addr st, H.S⟩, ⟨State.addr sc, hH.Wb⟩]

namespace UpdL
variable {hH} {s : State} {st d sc : BitVec 32} {len : Nat} (h : UpdL hH s st d sc len)
include h

theorem a0 : State.addr (s.sp - 16) = State.addr s.sp - 16 := addr_sub h.sp16
theorem a4 : State.addr (s.sp - 16 + 4) = State.addr s.sp - 16 + BitVec.ofNat 64 4 := addr_sub_add h.sp16 (by decide)
theorem a8 : State.addr (s.sp - 16 + 4 + 4) = State.addr s.sp - 16 + BitVec.ofNat 64 8 := by
  rw [BitVec.add_assoc]; exact addr_sub_add (k := 16) (i := 8) h.sp16 (by decide)
theorem a12 : State.addr (s.sp - 16 + 4 + 4 + 4) = State.addr s.sp - 16 + BitVec.ofNat 64 12 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; exact addr_sub_add (k := 16) (i := 12) h.sp16 (by decide)

/-- The memory after the push. -/
theorem pmem : (pushed upd4 s).mem =
    (((s.mem.writeW (State.addr s.sp - 16) d).writeW (State.addr s.sp - 16 + BitVec.ofNat 64 4)
      (BitVec.ofNat 32 len)).writeW (State.addr s.sp - 16 + BitVec.ofNat 64 8) sc).writeW
      (State.addr s.sp - 16 + BitVec.ofNat 64 12) (s.gpr .r12) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * upd4.length)) [s.gpr .r1, s.gpr .r7, s.gpr .r10, s.gpr .r12] = _
  rw [e16]
  show (((s.mem.writeW (State.addr (s.sp - 16)) _).writeW (State.addr (s.sp - 16 + 4)) _).writeW
    (State.addr (s.sp - 16 + 4 + 4)) _).writeW (State.addr (s.sp - 16 + 4 + 4 + 4)) _ = _
  rw [h.a0, h.a4, h.a8, h.a12, h.r1, h.r7, h.r10]

omit h in
theorem psp : (pushed upd4 s).sp = s.sp - 16 := by rw [pushed_sp, e16]

/-- The stack arguments, in a state whose memory and stack pointer are those after the push. -/
theorem sa (T : State) (ht : T.sp = s.sp - 16) (i : Nat) (hi : i < 4) :
    stackArgAddr T i = State.addr s.sp - 16 + BitVec.ofNat 64 (4 * i) := by
  simp only [stackArgAddr, ht]
  exact addr_sub_add (k := 16) h.sp16 (by omega_nat)

theorem sa0 (T : State) (ht : T.sp = s.sp - 16) : stackArgAddr T 0 = State.addr s.sp - 16 := by
  rw [h.sa T ht 0 (by decide)]; exact BitVec.add_zero _

theorem arg0 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed upd4 s).mem) : stackArg T 0 = d := by
  rw [stackArg, h.sa T ht 0 (by decide), hm, h.pmem, Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide), show 4 * 0 = 0 from rfl, BitVec.add_zero,
    Mem.readW_writeW_self32]

theorem arg1 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed upd4 s).mem) :
    stackArg T 1 = BitVec.ofNat 32 len := by
  rw [stackArg, h.sa T ht 1 (by decide), hm, h.pmem, Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide), show 4 * 1 = 4 from rfl,
    Mem.readW_writeW_self32]

theorem arg2 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed upd4 s).mem) : stackArg T 2 = sc := by
  rw [stackArg, h.sa T ht 2 (by decide), hm, h.pmem, Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide),
    show 4 * 2 = 8 from rfl, Mem.readW_writeW_self32]

/-- The push writes only below the stack pointer. -/
theorem fP : Frame [below s] s.mem (pushed upd4 s).mem := by
  rw [h.pmem]
  have hc : ∀ k, k + 4 ≤ 16 → (below s).Contains (State.addr s.sp - 16 + BitVec.ofNat 64 k) (32 / 8) := by
    intro k hk; exact contains_off _ (by omega_nat) (by decide)
  refine ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_).writeW
    (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simpa using hc 0 (by decide)
  · exact hc 4 (by decide)
  · exact hc 8 (by decide)
  · exact hc 12 (by decide)

omit h in
theorem vsp : ((pushed upd4 s).callEntry.withRegions (rd s.sp d len) (wr hH st sc)).sp = s.sp - 16 := psp
omit h in
theorem vmem : ((pushed upd4 s).callEntry.withRegions (rd s.sp d len) (wr hH st sc)).mem = (pushed upd4 s).mem := rfl

theorem hlen' : (BitVec.ofNat 32 len).toNat = len := by rw [BitVec.toNat_ofNat]; have := h.hlen; omega_nat

omit h in
theorem argsSub : Region.Sub ⟨State.addr s.sp - 16, 12⟩ (below s) := by
  intro x hx; simp only [Region.Contains] at hx ⊢; omega_nat

theorem pre : (updK H.S hH.Wb hH.SH.Repr).pre ((pushed upd4 s).callEntry.withRegions (rd s.sp d len) (wr hH st sc)) := by
  simp only [updK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, ce0, pushed_gpr,
    h.arg0 _ vsp vmem, h.arg1 _ vsp vmem, h.arg2 _ vsp vmem, h.sa0 _ vsp, h.r0, h.hlen']
  refine ⟨trivial, trivial, h.st_sc, h.d_st, h.d_sc, (h.b_st.sub_left argsSub), (h.b_sc.sub_left argsSub),
    h.nst, h.nd, h.nsc, ?_⟩
  rw [vsp, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, Offset.toNat_sub_ofNat]
  have := h.sp16; have := s.sp.isLt; omega_nat

theorem cov : Covers (rd s.sp d len ++ wr hH st sc) ((pushed upd4 s).rd ++ (pushed upd4 s).wr) := by
  intro x n' ⟨r, hr, hcn⟩
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rw [pushed_rd, pushed_wr, e16]
  rcases hr with (rfl | rfl) | (rfl | rfl)
  · obtain ⟨r', hr', hc'⟩ := h.cd x n' ⟨_, List.mem_singleton_self _, hcn⟩
    rcases List.mem_append.mp hr' with hr' | hr'
    · exact ⟨r', List.mem_append_left _ hr', hc'⟩
    · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
  · refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
    rw [h.a0]; simp only [Region.Contains, upd4, List.length_cons, List.length_nil] at hcn ⊢; omega_nat
  all_goals
    obtain ⟨r', hr', hc'⟩ := h.cw x n' ⟨_, by simp, hcn⟩
    exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩

theorem covW : Covers (wr hH st sc) (pushed upd4 s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h.cw x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

end UpdL

theorem upd_frame {s : State} {st d sc : BitVec 32} {len : Nat} (h : UpdL hH s st d sc len)
    {Q : State → Prop}
    (hQ : ∀ s', Pbkdf2.Stream.Arm.After s [⟨State.addr st, H.S⟩, ⟨State.addr sc, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem (State.addr st) m → count s = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem (State.addr st) (m ++ bytesAt s.mem (State.addr d) len)) → Q s') :
    WP isa (.frame (.push upd4) (.call H.updN H.updC) (.pop .r1 16)) s Q := by
  have h16 := h.sp16
  refine WP.frame (rs := upd4) (r := .r1) rfl (by show 16 ≤ s.sp.toNat; exact h16) (by decide) ?_
  refine WP.callCalls (k := updK H.S hH.Wb hH.SH.Repr) hH.upd.1 h.pre h.cov h.covW ?_ hH.updNF
  intro s₂ hrd hwr hsp hf hcs _ hpost
  have vc : count ((pushed upd4 s).callEntry.withRegions (UpdL.rd s.sp d len) (UpdL.wr hH st sc)) = count s := by
    simp only [count, State.withRegions_gpr, ce2, ce3, pushed_gpr]
  simp only [updK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, pushed_gpr, h.r0,
    h.arg0 _ UpdL.vsp UpdL.vmem, h.arg1 _ UpdL.vsp UpdL.vmem, h.hlen', vc] at hpost
  refine hQ _ (after_frame h.fP hrd hwr hsp hf hcs) fun m hr hcm => ?_
  have hs : ∀ r ∈ [below s], (⟨State.addr st, H.S⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact h.b_st.symm
  have hr' : hH.SH.Repr (pushed upd4 s).mem (State.addr st) m :=
    hH.repr _ _ _ _ _ (fun i hi => h.fP.bytes (R := ⟨State.addr st, H.S⟩) hs
      (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega_nat) hi) hr
  have hd : bytesAt (pushed upd4 s).mem (State.addr d) len = bytesAt s.mem (State.addr d) len := by
    simp only [bytesAt]
    apply List.map_congr_left
    intro i hi
    exact h.fP.bytes (R := ⟨State.addr d, len⟩)
      (by simp only [List.mem_singleton]; rintro r rfl; exact h.b_d.symm) (by show len ≤ 2 ^ 64; have := h.hlen; omega_nat)
      (List.mem_range.mp hi)
  rw [popped_mem, ← hd]
  exact hpost m hr' hcm


theorem upd_rel {P : State → State → Prop} {sp : BitVec 32} {st d sc : BitVec 32} {len : Nat}
    (h : ∀ s s', P s s' → UpdL hH s st d sc len ∧ UpdL hH s' st d sc len ∧ count s = count s' ∧
      s.sp = sp ∧ s'.sp = sp) :
    RelCT isa P (.frame (.push upd4) (.call H.updN H.updC) (.pop .r1 16)) fun _ _ => True := by
  refine RelCT.frame (fun s s' hp => by obtain ⟨-, -, -, e, e'⟩ := h s s' hp; rw [e, e']) ?_
  refine RelCT.call hH.upd.1 hH.upd.2.1 (UpdL.rd sp d len) (UpdL.wr hH st sc)
    fun a b ⟨s, s', hp, pa, pb⟩ => ?_
  obtain ⟨u, u', hc, e, e'⟩ := h s s' hp
  rw [push_eq rfl pa, push_eq rfl pb]
  subst e
  have v : s'.sp = s.sp := e'
  have hv' : UpdL.rd s.sp d len = UpdL.rd s'.sp d len := by rw [v]
  have t1 : ((pushed upd4 s).callEntry.withRegions (UpdL.rd s.sp d len) (UpdL.wr hH st sc)).sp =
    s.sp - 16 := UpdL.psp
  have t2 : ((pushed upd4 s').callEntry.withRegions (UpdL.rd s.sp d len) (UpdL.wr hH st sc)).sp =
    s'.sp - 16 := UpdL.psp
  refine ⟨u.pre, hv' ▸ u'.pre, ?_, u.cov, u.covW, hv' ▸ u'.cov, u'.covW⟩
  obtain ⟨c3, c2⟩ := BitVec.append_32_inj hc
  simp only [updK]
  refine ⟨by rw [t1, t2, v], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.withRegions_gpr, ce0, pushed_gpr, u.r0, u'.r0]
  · simp only [State.withRegions_gpr, ce2, pushed_gpr, c2]
  · simp only [State.withRegions_gpr, ce3, pushed_gpr, c3]
  · rw [u.arg0 _ t1 rfl, u'.arg0 _ t2 rfl]
  · rw [u.arg1 _ t1 rfl, u'.arg1 _ t2 rfl]
  · rw [u.arg2 _ t1 rfl, u'.arg2 _ t2 rfl]


end VG.Proof.Pbkdf2.Whole.Arm
