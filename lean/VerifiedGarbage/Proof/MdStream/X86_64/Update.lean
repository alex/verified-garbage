import VerifiedGarbage.Proof.MdStream.X86_64.Common

/-!
# Streaming Merkle–Damgård hash functions on x86-64: `update`

Untrusted: everything here is checked by Lean. The functional correctness of
`update`, for any hash function (`Md`) and any correct compression function
(`CalleeOk`).
-/

namespace VG.Proof.MdStream.X86_64.Update

open VG VG.X86_64 VG.Impl.MdStream.X86_64
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.MdStream.Md (add_mod_of_eq add_mod_of_lt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame)

/-! ## The precondition -/

section
variable (P : Params) (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev cnt : Nat := (s₀.gpr .rsi).toNat
abbrev dp : Addr := s₀.gpr .rdx
abbrev len : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev stR : Region := ⟨st s₀, P.N + P.B⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
/-- Where the call of the compression function stores its return address. -/
abbrev stkR : Region := below (s₀.gpr .rsp) 8
abbrev scR : Region := ⟨scr s₀, P.so + 48⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- The data. -/
abbrev D : List Byte := bytesAt s₀.mem (dp s₀) (len s₀)

end

/-- The messages the initial state represents, from `iv`. -/
def R₀ {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (st s₀) m ∧ s₀.gpr .rsi = BitVec.ofNat 64 m.length

structure Pre (P : Params) (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR P s₀, scR P s₀]
  st_scr : (stR P s₀).Disjoint (scR P s₀)
  d_st : (dR s₀).Disjoint (stR P s₀)
  d_scr : (dR s₀).Disjoint (scR P s₀)
  ret_st : (retR s₀).Disjoint (stR P s₀)
  ret_scr : (retR s₀).Disjoint (scR P s₀)
  stk_st : (stkR s₀).Disjoint (stR P s₀)
  stk_d : (stkR s₀).Disjoint (dR s₀)
  stk_scr : (stkR s₀).Disjoint (scR P s₀)

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem pre_of {s₀ : State} (h : (updK H).pre s₀) : Pre P s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- The return address and the 8 bytes below it. -/
theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

theorem R₀.length (hd : Dims P) {s₀ : State} {iv : H.HV} {m : List Byte} (h : R₀ H s₀ iv m) :
    cnt s₀ % P.B = m.length % P.B := by
  rw [cnt, h.2, BitVec.toNat_ofNat, hd.mod]

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .rcx).isLt

theorem D_length (s₀ : State) : (D s₀).length = len s₀ := by simp [bytesAt]

end

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (P : Params) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = st s₀
  r15 : s.gpr .r15 = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbp : s.gpr .rbp = dp s₀ + BitVec.ofNat 64 c
  r12 : s.gpr .r12 = BitVec.ofNat 64 (len s₀ - c)
  frame : Frame [stR P s₀, scR P s₀, stkR s₀] s₀.mem s.mem
  saved : Saved P s₀ .r8 s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (c : Nat) (s : State) : Prop
    extends Common P s₀ c s where
  r13 : s.gpr .r13 = BitVec.ofNat 64 ((cnt s₀ + c) % P.B)
  repr : ∀ iv m, R₀ H s₀ iv m → H.Repr iv s.mem (st s₀) (m ++ (D s₀).take c)

section
variable {P : Params} {H : Md P.B P.N P.L}

/-! ## Prologue and epilogue -/

theorem inv_zero (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {s : State} (hm : s.mem = saveMem P s₀ .r8)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hrbx : s.gpr .rbx = st s₀) (hr15 : s.gpr .r15 = scr s₀)
    (hrsp : s.gpr .rsp = s₀.gpr .rsp) (hrbp : s.gpr .rbp = dp s₀) (hr12 : s.gpr .r12 = s₀.gpr .rcx)
    (hr13 : s.gpr .r13 = BitVec.ofNat 64 (cnt s₀ % P.B)) : Inv H s₀ 0 s where
  c_le := Nat.zero_le _
  rd := hrd
  wr := hwr
  rbx := hrbx
  r15 := hr15
  rsp := hrsp
  rbp := by rw [hrbp]; simp
  r12 := by rw [hr12]; simp
  frame := by rw [hm]; exact (saveMem_frame hd).mono fun r hr => by simp at hr; simp [hr]
  saved := by rw [hm]; exact saveMem_saved hd
  r13 := by rw [hr13, Nat.add_zero]
  repr iv m hm₀ := by
    rw [List.take_zero, List.append_nil, hm]
    exact H.repr_congr hd.pos (fun i hi => (saveMem_frame hd).bytes (R := stR P s₀)
      (by simpa using hp.st_scr) (by show P.N + P.B ≤ 2 ^ 64; have := hd.N; have := hd.B; omega) hi) hm₀.1

set_option simprocs false in
theorem prologue_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) :
    WP isa (.block (updateStart P)) s₀ (Inv H s₀ 0) := by
  have := hd.so
  have o : ∀ d : Nat, d + 8 ≤ P.so + 48 → InRegions s₀.wr (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨scR P s₀, by simp [hp.wr], contains_offset' hd (by omega)⟩
  have o0 := o P.so (by omega); have o1 := o (P.so + 8) (by omega); have o2 := o (P.so + 16) (by omega)
  have o3 := o (P.so + 24) (by omega); have o4 := o (P.so + 32) (by omega); have o5 := o (P.so + 40) (by omega)
  apply WP.of_runBlock
  rw [updateStart, save_eq]
  simp only [List.cons_append, List.nil_append]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, ea_at,
    State.store64, o0, o1, o2, o3, o4, o5, ite_true, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine inv_zero hd hp rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := {decide := true}) [State.setReg, arithFlags, State.setFlags, and_mask hd.B]

set_option simprocs false in
theorem epilogue_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {s : State} (hI : Inv H s₀ (len s₀) s) :
    WP isa (.block (restore P)) s fun s' => gprPreserved s₀ s' ∧ (updK H).post s₀ s' := by
  have := hd.so
  have i : ∀ d : Nat, d + 8 ≤ P.so + 48 →
      InRegions (s.rd ++ s.wr) (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨scR P s₀, by simp [hI.rd, hI.wr, hp.wr], contains_offset' hd (by omega)⟩
  have i0 := i P.so (by omega); have i1 := i (P.so + 8) (by omega); have i2 := i (P.so + 16) (by omega)
  have i3 := i (P.so + 24) (by omega); have i4 := i (P.so + 32) (by omega); have i5 := i (P.so + 40) (by omega)
  have g0 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((P.so : Nat) : Int)) 64 = s₀.gpr .rbx :=
    hI.saved (.rbx, P.so) (by simp [saved])
  have g1 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((P.so + 8 : Nat) : Int)) 64 = s₀.gpr .rbp :=
    hI.saved (.rbp, P.so + 8) (by simp [saved])
  have g2 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((P.so + 16 : Nat) : Int)) 64 = s₀.gpr .r12 :=
    hI.saved (.r12, P.so + 16) (by simp [saved])
  have g3 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((P.so + 24 : Nat) : Int)) 64 = s₀.gpr .r13 :=
    hI.saved (.r13, P.so + 24) (by simp [saved])
  have g4 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((P.so + 32 : Nat) : Int)) 64 = s₀.gpr .r14 :=
    hI.saved (.r14, P.so + 32) (by simp [saved])
  have g5 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((P.so + 40 : Nat) : Int)) 64 = s₀.gpr .r15 :=
    hI.saved (.r15, P.so + 40) (by simp [saved])
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hI.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr, ret_stk s₀⟩)
      (by decide)
  have hrsp := hI.rsp
  have hr15 := hI.r15
  have hrepr := hI.repr
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at, State.load64,
    State.setReg, hr15, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, hret⟩, fun iv m hm hc => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hrsp]
  · have := hrepr iv m ⟨hm, hc⟩
    rwa [List.take_of_length_le (Nat.le_of_eq (D_length _))] at this

end

/-! ## One iteration -/

/-- A whole block is ready at `rsi`, and compressing it absorbs the first `c`
bytes of data. -/
structure Pending {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (c : Nat) (s : State) : Prop
    extends Common P s₀ c s where
  r13 : s.gpr .r13 = 0
  r14 : s.gpr .r14 = 1
  mod : (cnt s₀ + c) % P.B = 0
  src : s.gpr .rsi = st s₀ + BitVec.ofNat 64 P.N ∨
    ∃ c₀, s.gpr .rsi = dp s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + P.B ≤ len s₀
  repr : ∀ iv m, R₀ H s₀ iv m → ∀ mem', H.stateAt mem' (st s₀) =
      H.compress (H.stateAt s.mem (st s₀)) (H.blockAt s.mem (s.gpr .rsi)) →
    H.Repr iv mem' (st s₀) (m ++ (D s₀).take c)

/-- All the data is absorbed. -/
def Done {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (s : State) : Prop :=
  Inv H s₀ (len s₀) s ∧ s.gpr .r14 = 0

/-- The loop's postcondition for one iteration from `c` bytes. -/
def Step {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (c : Nat) (s : State) : Prop :=
  (eval .ne s = some false ∧ Inv H s₀ (len s₀) s) ∨
    (eval .ne s = some true ∧ ∃ c', c < c' ∧ Inv H s₀ c' s)

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem Common.congr {s₀ : State} {c : Nat} {s s' : State} (h : Common P s₀ c s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common P s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg]; exact h.rbx
  r15 := by rw [hg]; exact h.r15
  rsp := by rw [hg]; exact h.rsp
  rbp := by rw [hg]; exact h.rbp
  r12 := by rw [hg]; exact h.r12
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.congr {s₀ : State} {c : Nat} {s s' : State} (h : Inv H s₀ c s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv H s₀ c s' :=
  { h.toCommon.congr hg hm hrd hwr with
    r13 := by rw [hg]; exact h.r13
    repr := by rw [hm]; exact h.repr }

/-- The call of the compression function's requirements. -/
theorem Pending.callOk (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {s : State}
    (h : Pending H s₀ c s) : CallOk P s (st s₀) (scr s₀) (s.gpr .rsi) := by
  have := hd.N; have := hd.so; have := hd.B
  have eN : Region.Sub ⟨st s₀, P.N⟩ (stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨scr s₀, P.so⟩ (scR P s₀) := Region.sub_prefix (by omega)
  have eSrc : Region.Sub ⟨s.gpr .rsi, P.B⟩ (stR P s₀) ∨ Region.Sub ⟨s.gpr .rsi, P.B⟩ (dR s₀) := by
    rcases h.src with h' | ⟨c₀, h', hc₀⟩
    · exact .inl (h' ▸ sub_offset (off := P.N) (by omega) (by omega))
    · exact .inr (h' ▸ sub_offset (by omega) (by have := len_lt s₀; omega))
  have hsp := h.rsp
  refine ⟨h.rbx, h.r15, rfl, (hp.st_scr.sub_left eN).sub_right eso, ?_, ?_,
    by rw [hsp]; exact hp.stk_st.sub_right eN, by rw [hsp]; exact hp.stk_scr.sub_right eso, ?_, ?_, ?_⟩
  · rcases h.src with h' | ⟨c₀, h', hc₀⟩
    · rw [h']; intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
    · exact (hp.d_st.sub_left (h' ▸ sub_offset (by omega) (by have := len_lt s₀; omega))).sub_right eN
  · rcases eSrc with e | e
    · exact (hp.st_scr.sub_left e).sub_right eso
    · exact (hp.d_scr.sub_left e).sub_right eso
  · rw [hsp]
    rcases eSrc with e | e
    · exact hp.stk_st.sub_right e
    · exact hp.stk_d.sub_right e
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rcases h.src with h' | ⟨c₀, h', hc₀⟩
      · exact ⟨stR P s₀, by simp, P.N, h', by simp⟩
      · exact ⟨dR s₀, by simp, c₀, h', hc₀⟩
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR P s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR P s₀, by simp, 0, by simp, by simp⟩

theorem Pending.compress_ok (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : Pre P s₀) {c : Nat} {s : State} (h : Pending H s₀ c s) :
    WP isa (compressAt name code) s fun s' => Inv H s₀ c s' ∧ s'.gpr .r14 = 1 := by
  have := hd.N; have := hd.so; have := hd.B
  have eN : Region.Sub ⟨st s₀, P.N⟩ (stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨scr s₀, P.so⟩ (scR P s₀) := Region.sub_prefix (by omega)
  have hsp := h.rsp
  refine compressAt_ok H hf (h.callOk hd hp) (by omega) (by omega) ?_
  intro s' hrd hwr hcs hf hstate _ _
  have cs : ∀ r, r ∈ calleeSaved → s'.gpr r = s.gpr r := hcs
  refine ⟨⟨⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, by rw [cs _ (by decide)]; exact h.rbx,
    by rw [cs _ (by decide)]; exact h.r15, by rw [cs _ (by decide)]; exact h.rsp,
    by rw [cs _ (by decide)]; exact h.rbp, by rw [cs _ (by decide)]; exact h.r12,
    h.frame.trans (hf.sub ?_), fun p hp' => ?_⟩, ?_, fun iv m hm => h.repr iv m hm _ hstate⟩,
    by rw [cs _ (by decide)]; exact h.r14⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR P s₀, by simp, eN⟩
    · exact ⟨scR P s₀, by simp, eso⟩
    · exact ⟨stkR s₀, by simp, by rw [hsp]; exact fun _ h => h⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    have hd' : ∀ d : Nat, P.so ≤ d → d + 8 ≤ P.so + 48 →
        s'.mem.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 =
          s.mem.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 := by
      intro d hd₁ hd₂
      refine hf.readW (r := ⟨scr s₀ + BitVec.ofInt 64 (d : Int), 8⟩) (Region.contains_self _ _) ?_
        (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl
      · exact (hp.st_scr.symm.sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega) (by omega))).sub_right eN
      · intro a h₁ h₂; simp only [Region.Contains, ofInt_natCast] at h₁ h₂; bv_omega
      · rw [hsp]
        exact hp.stk_scr.symm.sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega) (by omega))
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · rw [hd' _ (by omega) (by omega)]; exact h.saved _ (by simp [saved])
  · rw [cs _ (by decide), h.r13, h.mod]; rfl

theorem Pending.congr {s₀ : State} {c : Nat} {s s' : State} (h : Pending H s₀ c s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Pending H s₀ c s' :=
  { h.toCommon.congr hg hm hrd hwr with
    r13 := by rw [hg]; exact h.r13
    r14 := by rw [hg]; exact h.r14
    mod := h.mod
    src := by rw [hg]; exact h.src
    repr := by rw [hm, hg]; exact h.repr }

/-- The second half of the loop body: compress if a block is ready, and loop
back if so. -/
theorem tail_ok (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P s₀) {c : Nat} {s : State} (h : (∃ c', c < c' ∧ Pending H s₀ c' s) ∨ Done H s₀ s) :
    WP isa (updateTail name code) s (Step H s₀ c) := by
  unfold updateTail
  refine WP.seq (WP.mono (test_ok .r14) fun s₁ ⟨hg, hm, hrd, hwr, hz⟩ => ?_)
  rcases h with ⟨c', hc, hP⟩ | ⟨hI, h14⟩
  · have hP₁ := hP.congr hg hm hrd hwr
    refine WP.seq (WP.ite true (by simp [eval, hz, hP.r14]) (fun _ => ?_) (fun h => by cases h))
    refine WP.mono (hP₁.compress_ok hd hf hp) fun s₂ ⟨hI₂, h14⟩ => ?_
    refine WP.mono (test_ok .r14) fun s₃ ⟨hg₃, hm₃, hrd₃, hwr₃, hz₃⟩ => ?_
    exact .inr ⟨by simp [eval, hz₃, h14], c', hc, hI₂.congr hg₃ hm₃ hrd₃ hwr₃⟩
  · refine WP.seq (WP.ite false (by simp [eval, hz, h14]) (fun h => by cases h) fun _ => ?_)
    refine WP.block_nil ?_
    refine WP.mono (test_ok .r14) fun s₃ ⟨hg₃, hm₃, hrd₃, hwr₃, hz₃⟩ => ?_
    exact .inl ⟨by simp [eval, hz₃, hg, h14], (hI.congr hg hm hrd hwr).congr hg₃ hm₃ hrd₃ hwr₃⟩

/-! ## Consuming data -/

theorem D_getD (s₀ : State) {i : Nat} (hi : i < len s₀) :
    (D s₀).getD i 0 = s₀.mem (dp s₀ + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre P s₀) {c : Nat} {s : State} (h : Common P s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = (D s₀).getD i 0 := by
  rw [D_getD s₀ hi]
  exact h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩) (Nat.le_of_lt (len_lt s₀)) hi

theorem length_mid (hd : Dims P) (s₀ : State) {iv : H.HV} {m : List Byte} (hm : R₀ H s₀ iv m) {c : Nat}
    (hc : c ≤ len s₀) : (m ++ (D s₀).take c).length % P.B = (cnt s₀ + c) % P.B := by
  simp only [List.length_append, List.length_take, D_length, Nat.min_eq_left hc]
  rw [Nat.add_mod, ← hm.length hd, ← Nat.add_mod]

theorem take_add_data (s₀ : State) (c t : Nat) (m : List Byte) :
    m ++ (D s₀).take c ++ ((D s₀).drop c).take t = m ++ (D s₀).take (c + t) := by
  rw [List.take_add, List.append_assoc]

/-- A list whose length is a multiple of `B` has nothing past its last block. -/
theorem drop_full {B : Nat} {l : List Byte} (h : l.length % B = 0) : l.drop (B * (l.length / B)) = [] := by
  rw [List.drop_eq_nil_iff]
  have := Nat.div_add_mod l.length B
  omega

set_option simprocs false in
/-- A whole block straight from the data. -/
theorem direct_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {s : State} (hI : Inv H s₀ c s)
    (hr : (cnt s₀ + c) % P.B = 0) (hl : P.B ≤ len s₀ - c) :
    WP isa (.block (direct P)) s fun s' =>
      Pending H s₀ (c + P.B) s' ∧ s'.gpr .rsi = dp s₀ + BitVec.ofNat 64 c := by
  have hrbp := hI.rbp; have hr12 := hI.r12; have hr13 := hI.r13
  have := hd.B
  have sB := sx_ofNat (n := P.B) (by omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [direct, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, isa,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  have hlen := len_lt s₀
  refine ⟨⟨⟨by omega, hI.rd, hI.wr, ?_, ?_, ?_, ?_, ?_, hI.frame, hI.saved⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    try simp (config := {decide := true}) only [State.setReg, State.setReg32, arithFlags, State.setFlags,
      ite_false, ite_true, sB, hrbp, hr12, hr13, hr]
  · exact hI.rbx
  · exact hI.r15
  · exact hI.rsp
  · bv_omega
  · bv_omega
  · rw [← Nat.add_assoc, Nat.add_mod_right]; exact hr
  · exact .inr ⟨c, rfl, by omega⟩
  · intro iv m hm mem' hs
    have hmod := length_mid hd s₀ hm (c := c) (by omega)
    rw [← take_add_data]
    refine H.repr_append_block hd.pos (hI.repr iv m hm)
      (by rw [hmod, hr, List.length_take, List.length_drop, D_length]; omega) ?_
    rw [hs]
    refine congrArg (H.compress _) ?_
    rw [drop_full (by rw [hmod]; exact hr), List.nil_append]
    apply H.parse_congr
    intro k hk
    rw [add_ofNat, hI.data hp (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hk]

/-! ## Buffering data -/

section
variable (P) (s₀ : State) (c : Nat)
/-- Bytes in the buffer before this iteration. -/
abbrev rr : Nat := (cnt s₀ + c) % P.B
/-- Bytes copied into the buffer in this iteration. -/
abbrev tt : Nat := min (P.B - rr P s₀ c) (len s₀ - c)
/-- Where they go. -/
abbrev q : Addr := st s₀ + BitVec.ofNat 64 P.N + BitVec.ofNat 64 (rr P s₀ c)
/-- The data copied. -/
abbrev xs : List Byte := ((D s₀).drop c).take (tt P s₀ c)
end

theorem rr_lt (hd : Dims P) (s₀ : State) (c : Nat) : rr P s₀ c < P.B := Nat.mod_lt _ hd.pos
theorem rr_eq (s₀ : State) (c : Nat) : rr P s₀ c = (cnt s₀ + c) % P.B := rfl
theorem tt_eq (s₀ : State) (c : Nat) : tt P s₀ c = min (P.B - rr P s₀ c) (len s₀ - c) := rfl
theorem tt_le (s₀ : State) (c : Nat) : tt P s₀ c ≤ len s₀ - c := Nat.min_le_right _ _
theorem tt_le' (s₀ : State) (c : Nat) : tt P s₀ c ≤ P.B - rr P s₀ c := Nat.min_le_left _ _

theorem q_eq (s₀ : State) (c : Nat) : q P s₀ c = st s₀ + BitVec.ofNat 64 (P.N + rr P s₀ c) := by
  rw [q, add_ofNat]

/-- The state while copying: `j` bytes copied, into memory `M` otherwise as in `mI`. -/
structure Copy (P : Params) (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ tt P s₀ c
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = st s₀
  r15 : s.gpr .r15 = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbp : s.gpr .rbp = dp s₀ + BitVec.ofNat 64 (c + j)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (len s₀ - c - tt P s₀ c)
  r13 : s.gpr .r13 = BitVec.ofNat 64 (rr P s₀ c + j)
  rax : s.gpr .rax = BitVec.ofNat 64 (tt P s₀ c - j)
  mem : s.mem = writeBytes mI (q P s₀ c) ((xs P s₀ c).take j)

theorem xs_length (s₀ : State) (c : Nat) : (xs P s₀ c).length = tt P s₀ c := by
  have := tt_le (P := P) s₀ c
  simp only [xs, List.length_take, List.length_drop, D_length]; omega

theorem write_frame (hd : Dims P) (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (hj : j ≤ tt P s₀ c) :
    Frame [stR P s₀] mI (writeBytes mI (q P s₀ c) ((xs P s₀ c).take j)) := by
  have := tt_le' (P := P) s₀ c; have := rr_lt hd s₀ c; have := hd.N; have := hd.B
  refine writeBytes_frame _ _ _ ?_
  rw [q_eq]
  exact contains_offset (by simp only [List.length_take]; omega) (by omega)

set_option simprocs false in
theorem copy_step (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {j : Nat} (hj : j < tt P s₀ c) {s : State} (h : Copy P s₀ c sI.mem j s) :
    WP isa (.block [.movzx8 .r9 { base := .rbp }, .store8 (bufByte P) .r9, .alu .add .rbp (.imm 1),
      .alu .add .r13 (.imm 1), .alu .sub .rax (.imm 1)]) s fun s' =>
      Copy P s₀ c sI.mem (j + 1) s' ∧ s'.zf = some (decide (tt P s₀ c - (j + 1) = 0)) := by
  have hlen := len_lt s₀
  have hc := hI.c_le
  have hr := rr_lt hd s₀ c
  have ht := tt_le (P := P) s₀ c; have ht' := tt_le' (P := P) s₀ c
  have := hd.N; have := hd.B
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 (c + j)) 1 :=
    ⟨dR s₀, by simp [h.rd, hp.rd], contains_offset (by omega) (by omega)⟩
  have hbyte : s.mem (dp s₀ + BitVec.ofNat 64 (c + j)) = (D s₀).getD (c + j) 0 := by
    rw [h.mem, ← hI.data hp (by omega)]
    exact (write_frame hd s₀ c sI.mem j h.j_le).bytes (R := dR s₀) (by simpa using hp.d_st)
      (by show len s₀ ≤ 2 ^ 64; omega) (by show c + j < len s₀; omega)
  -- The byte written.
  have hout : InRegions s.wr (q P s₀ c + BitVec.ofNat 64 j) 1 :=
    ⟨stR P s₀, by simp [h.wr, hp.wr], by
      rw [q_eq, add_ofNat]; exact contains_offset (by omega) (by omega)⟩
  have hrbp := h.rbp; have hr13 := h.r13; have hrbx := h.rbx
  have hxs := xs_length (P := P) s₀ c
  refine wp_movzx8 (d := .r9) (a := dp s₀ + BitVec.ofNat 64 (c + j)) (by simp [State.ea, hrbp]) hin
    fun s₁ u₁ => ?_
  refine wp_store8 (r := .r9) (a := q P s₀ c + BitVec.ofNat 64 j) ?_ (by rw [u₁.wr]; exact hout)
    fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  · simp only [State.ea, bufByte, u₁.other .rbx (by decide), u₁.other .r13 (by decide), hrbx, hr13, q,
      BitVec.ofNat_add, BitVec.mul_one, ofInt_natCast]
    ac_rfl
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ hz₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rax → r ≠ .r13 → r ≠ .rbp → r ≠ .r9 → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, g₂, u₁.other r h4]
  have hrax : s₅.gpr .rax = BitVec.ofNat 64 (tt P s₀ c - (j + 1)) := by
    rw [u₅.gpr, u₄.other .rax (by decide), u₃.other .rax (by decide), g₂, u₁.other .rax (by decide), h.rax,
      sx1, ofNat_pred (by omega), Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrax, ?_⟩, ?_⟩
  · rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, h.wr]
  · rw [g .rbx (by decide) (by decide) (by decide) (by decide), hrbx]
  · rw [g .r15 (by decide) (by decide) (by decide) (by decide), h.r15]
  · rw [g .rsp (by decide) (by decide) (by decide) (by decide), h.rsp]
  · rw [u₅.other .rbp (by decide), u₄.other .rbp (by decide), u₃.gpr, g₂, u₁.other .rbp (by decide), hrbp,
      sx1, ← Nat.add_assoc, ofNat_succ, BitVec.add_assoc]
  · rw [g .r12 (by decide) (by decide) (by decide) (by decide), h.r12]
  · rw [u₅.other .r13 (by decide), u₄.gpr, u₃.other .r13 (by decide), g₂, u₁.other .r13 (by decide), hr13,
      sx1, ← Nat.add_assoc, ofNat_succ]
  · have hj' : j < (xs P s₀ c).length := by omega
    rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem, u₁.gpr, hbyte, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj', Option.toList_some,
      writeBytes_snoc _ _ _ _ (by simp only [List.length_take]; omega)]
    have hl : (List.take j (xs P s₀ c)).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [hl, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]
    congr 1
    simp only [xs, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show c + j < (D s₀).length by rw [D_length]; omega), Option.getD_some]
  · rw [hz₅, u₄.other .rax (by decide), u₃.other .rax (by decide), g₂, u₁.other .rax (by decide), h.rax, sx1,
      ofNat_pred (by omega), ofNat_beq_zero (by omega), show tt P s₀ c - j - 1 = tt P s₀ c - (j + 1) by omega]

theorem Inv.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Inv H s₀ c s)
    (hg : ∀ r ∈ [Reg.rbx, .r15, .rsp, .rbp, .r12, .r13], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv H s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg _ (by simp)]; exact h.rbx
  r15 := by rw [hg _ (by simp)]; exact h.r15
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  rbp := by rw [hg _ (by simp)]; exact h.rbp
  r12 := by rw [hg _ (by simp)]; exact h.r12
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  r13 := by rw [hg _ (by simp)]; exact h.r13
  repr := by rw [hm]; exact h.repr

/-- The memory after copying `tt` bytes. -/
theorem copied_facts (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI) :
    let mem := writeBytes sI.mem (q P s₀ c) (xs P s₀ c)
    Frame [stR P s₀, scR P s₀, stkR s₀] s₀.mem mem ∧ Saved P s₀ .r8 mem ∧
      H.stateAt mem (st s₀) = H.stateAt sI.mem (st s₀) ∧
      bytesAt mem (st s₀ + BitVec.ofNat 64 P.N) (rr P s₀ c + tt P s₀ c) =
        bytesAt sI.mem (st s₀ + BitVec.ofNat 64 P.N) (rr P s₀ c) ++ xs P s₀ c := by
  intro mem
  have hr := rr_lt hd s₀ c; have ht' := tt_le' (P := P) s₀ c
  have hxs := xs_length (P := P) s₀ c
  have := hd.N; have := hd.B; have := hd.so
  have hf : Frame [stR P s₀] sI.mem mem := by
    have := write_frame hd s₀ c sI.mem (tt P s₀ c) (Nat.le_refl _)
    rwa [List.take_of_length_le (by omega)] at this
  refine ⟨hI.frame.trans (hf.mono (by simp)), fun p hp' => ?_, ?_, ?_⟩
  · rw [← hI.saved p hp']
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    have hd' : P.so ≤ p.2 ∧ p.2 + 8 ≤ P.so + 48 := by
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega
    refine hf.readW (r := ⟨scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact (hp.st_scr.symm.sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega) (by omega)))
  · apply H.stateAt_congr
    intro i hi
    simp only [mem, q_eq]
    exact writeBytes_before _ _ _ (by omega) (by omega)
  · rw [← hxs]
    exact bytesAt_writeBytes _ _ _ _ (by omega)

set_option simprocs false in
/-- A full buffer: compress it. -/
theorem fill_pending (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {s : State} (h : Copy P s₀ c sI.mem (tt P s₀ c) s) (hfull : rr P s₀ c + tt P s₀ c = P.B) :
    WP isa (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 P.N)), .mov32 .r13 (.imm 0),
      .mov32 .r14 (.imm 1)]) s fun s' =>
      Pending H s₀ (c + tt P s₀ c) s' ∧ s'.gpr .rsi = st s₀ + BitVec.ofNat 64 P.N := by
  have hr := rr_lt hd s₀ c; have ht := tt_le (P := P) s₀ c; have ht' := tt_le' (P := P) s₀ c
  have hrr := rr_eq (P := P) s₀ c
  have hxs := xs_length (P := P) s₀ c
  have hc := hI.c_le
  have := hd.N
  obtain ⟨hfr, hsv, hst, hby⟩ := copied_facts hd hp hI
  have hmem : s.mem = writeBytes sI.mem (q P s₀ c) (xs P s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega)]
  refine wp_mov fun s₁ u₁ _ _ => wp_addi fun s₂ u₂ => wp_mov32i fun s₃ u₃ _ _ =>
    wp_mov32i fun s₄ u₄ _ _ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rsi → r ≠ .r13 → r ≠ .r14 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₄.other r h3, u₃.other r h2, u₂.other r h1, u₁.other r h1]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hsi : s₄.gpr .rsi = st s₀ + BitVec.ofNat 64 P.N := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, h.rbx, sx_ofNat (by omega)]
  refine ⟨⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [m₄, hmem]; exact hfr, by rw [m₄, hmem]; exact hsv⟩,
    by rw [u₄.other _ (by decide), u₃.gpr]; rfl, by rw [u₄.gpr]; rfl, ?_, .inl hsi, ?_⟩, hsi⟩
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .rbx (by decide) (by decide) (by decide), h.rbx]
  · rw [g .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [g .rsp (by decide) (by decide) (by decide), h.rsp]
  · rw [g .rbp (by decide) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by decide) (by decide) (by decide), h.r12, Nat.sub_sub]
  · rw [← Nat.add_assoc, add_mod_of_eq (B := P.B) hfull]
  · intro iv m hm mem' hs
    rw [← take_add_data]
    have hmod := length_mid hd s₀ hm hc
    refine H.repr_append_block hd.pos (hI.repr iv m hm) (by rw [hmod, hxs]; exact hfull) ?_
    rw [hs, m₄, hmem, hst, hsi]
    refine congrArg (H.compress _) (H.parse_congr fun k hk => ?_)
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb, show rr P s₀ c + tt P s₀ c = P.B from hfull] at hby
    exact bytesAt_getD hby hk

set_option simprocs false in
/-- All the data fits in the buffer. -/
theorem fill_done (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {s : State} (h : Copy P s₀ c sI.mem (tt P s₀ c) s) (h14 : s.gpr .r14 = 0)
    (hnf : rr P s₀ c + tt P s₀ c ≠ P.B) : Done H s₀ s := by
  have hr := rr_lt hd s₀ c; have ht := tt_le (P := P) s₀ c; have ht' := tt_le' (P := P) s₀ c
  have hrr := rr_eq (P := P) s₀ c
  have htt := tt_eq (P := P) s₀ c
  have hxs := xs_length (P := P) s₀ c
  have hc := hI.c_le
  have htl : tt P s₀ c = len s₀ - c := by omega
  obtain ⟨hfr, hsv, hst, hby⟩ := copied_facts hd hp hI
  have hmem : s.mem = writeBytes sI.mem (q P s₀ c) (xs P s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega)]
  refine ⟨⟨⟨(Nat.le_refl _), h.rd, h.wr, h.rbx, h.r15, h.rsp, ?_, ?_, by rw [hmem]; exact hfr,
    by rw [hmem]; exact hsv⟩, ?_, fun iv m hm => ?_⟩, h14⟩
  · rw [h.rbp, show c + tt P s₀ c = len s₀ by omega]
  · rw [h.r12, show len s₀ - c - tt P s₀ c = len s₀ - len s₀ by omega]
  · rw [h.r13, show cnt s₀ + len s₀ = cnt s₀ + c + tt P s₀ c by omega,
      add_mod_of_lt (B := P.B) (by omega)]
  · have hmod := length_mid hd s₀ hm hc
    rw [show len s₀ = c + tt P s₀ c by omega, ← take_add_data]
    refine H.repr_append_buf (hI.repr iv m hm) (by rw [hmod, hxs]; omega) (by rw [hmem, hst]) ?_
    rw [hmod, hxs, hmem, hby]
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb]

theorem Copy.of_gpr {s₀ : State} {c : Nat} {mI : Mem} {j : Nat} {s s' : State} (h : Copy P s₀ c mI j s)
    (hg : ∀ r ∈ [Reg.rbx, .r15, .rsp, .rbp, .r12, .r13, .rax], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Copy P s₀ c mI j s' where
  j_le := h.j_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg _ (by simp)]; exact h.rbx
  r15 := by rw [hg _ (by simp)]; exact h.r15
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  rbp := by rw [hg _ (by simp)]; exact h.rbp
  r12 := by rw [hg _ (by simp)]; exact h.r12
  r13 := by rw [hg _ (by simp)]; exact h.r13
  rax := by rw [hg _ (by simp)]; exact h.rax
  mem := by rw [hm]; exact h.mem

theorem copy_loop_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {s : State} (h : Copy P s₀ c sI.mem 0 s) (ht : 0 < tt P s₀ c) :
    WP isa (copyLoop P) s (Copy P s₀ c sI.mem (tt P s₀ c)) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = tt P s₀ c - j ∧ j < tt P s₀ c ∧ Copy P s₀ c sI.mem j s)
    ?_ (tt P s₀ c) s ⟨0, rfl, ht, h⟩
  rintro n s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hd hp hI hj hc) fun s' ⟨hc', hz⟩ => ?_
  by_cases hl : tt P s₀ c - (j + 1) = 0
  · refine .inl ⟨by simp [eval, hz, hl], ?_⟩
    rwa [show j + 1 = tt P s₀ c by omega] at hc'
  · exact .inr ⟨by simp [eval, hz, hl], _, by omega, j + 1, rfl, by omega, hc'⟩

theorem fill_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {s : State} (hI : Inv H s₀ c s) :
    WP isa (fill P) s fun s' =>
      (∃ c', c < c' ∧ Pending H s₀ c' s' ∧ s'.gpr .rsi = st s₀ + BitVec.ofNat 64 P.N) ∨ Done H s₀ s' := by
  have hr := rr_lt hd s₀ c; have ht := tt_le (P := P) s₀ c; have ht' := tt_le' (P := P) s₀ c
  have hrr := rr_eq (P := P) s₀ c; have htt := tt_eq (P := P) s₀ c
  have hc := hI.c_le; have hlen := len_lt s₀
  have := hd.B
  unfold fill
  -- `rax := B - r13; cmp r12, rax`
  refine WP.seq (wp_mov32i fun s₁ u₁ _ _ => wp_sub fun s₂ u₂ _ => wp_cmp fun s₃ g₃ m₃ rd₃ wr₃ cf₃ _ =>
    WP.block_nil ?_)
  have e₃ : ∀ r, r ≠ .rax → s₃.gpr r = s.gpr r := fun r h => by rw [g₃, u₂.other r h, u₁.other r h]
  have hne : ∀ r ∈ [Reg.rbx, .r15, .rsp, .rbp, .r12, .r13], r ≠ .rax := by decide
  have hI₃ : Inv H s₀ c s₃ := hI.of_gpr (fun r hr => e₃ r (hne r hr)) (by rw [m₃, u₂.mem, u₁.mem])
    (by rw [rd₃, u₂.rd, u₁.rd]) (by rw [wr₃, u₂.wr, u₁.wr])
  have hrax₂ : s₂.gpr .rax = BitVec.ofNat 64 (P.B - rr P s₀ c) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.r13, ← rr_eq, zx_ofNat (by omega), sub_ofNat (by omega)]
  have hcf : s₃.cf = some (decide (len s₀ - c < P.B - rr P s₀ c)) := by
    rw [cf₃, hrax₂, u₂.other _ (by decide), u₁.other _ (by decide), hI.r12, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  -- `rax := min(rax, r12)`
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => Inv H s₀ c s₄ ∧ s₄.gpr .rax = BitVec.ofNat 64 (tt P s₀ c) ∧
    s₄.mem = s.mem) ?_ fun s₄ ⟨hI₄, hrax₄, hm₄⟩ => ?_)
  · refine WP.ite (decide (len s₀ - c < P.B - rr P s₀ c)) (by simp [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
    · refine wp_mov fun s₄ u₄ _ _ => WP.block_nil
        ⟨hI₃.of_gpr (fun r hr => u₄.other r (hne r hr)) u₄.mem u₄.rd u₄.wr, ?_,
          by rw [u₄.mem, m₃, u₂.mem, u₁.mem]⟩
      rw [u₄.gpr, hI₃.r12]; congr 1; simp at hb; omega
    · refine WP.block_nil ⟨hI₃, ?_, by rw [m₃, u₂.mem, u₁.mem]⟩
      rw [g₃, hrax₂]; congr 1; simp at hb; omega
  -- `r12 -= rax; test rax, rax`
  refine WP.seq (wp_sub fun s₅ u₅ _ => wp_test fun s₆ g₆ m₆ rd₆ wr₆ z₆ => WP.block_nil ?_)
  have hC₀ : Copy P s₀ c s.mem 0 s₆ := by
    have e : ∀ r, r ≠ .r12 → s₆.gpr r = s₄.gpr r := fun r h => by rw [g₆, u₅.other r h]
    refine ⟨Nat.zero_le _, by rw [rd₆, u₅.rd, hI₄.rd], by rw [wr₆, u₅.wr, hI₄.wr],
      by rw [e _ (by decide), hI₄.rbx], by rw [e _ (by decide), hI₄.r15], by rw [e _ (by decide), hI₄.rsp],
      by rw [e _ (by decide), hI₄.rbp, Nat.add_zero], ?_, by rw [e _ (by decide), hI₄.r13, Nat.add_zero],
      by rw [e _ (by decide), hrax₄, Nat.sub_zero], ?_⟩
    · rw [g₆, u₅.gpr, hI₄.r12, hrax₄, sub_ofNat (by omega), Nat.sub_sub]
    · rw [m₆, u₅.mem, hm₄, List.take_zero, writeBytes_nil]
  have hz₆ : s₆.zf = some (decide (tt P s₀ c = 0)) := by
    rw [z₆, u₅.other _ (by decide), hrax₄, BitVec.and_self, ofNat_beq_zero (by omega)]
  -- Copy the bytes.
  refine WP.seq (WP.mono (Q := Copy P s₀ c s.mem (tt P s₀ c)) ?_ fun s₇ hC => ?_)
  · refine WP.ite (decide (tt P s₀ c = 0)) (by simp [eval, hz₆]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil (hb ▸ hC₀)
    · simp only [decide_eq_false_iff_not] at hb
      rw [← hm₄]
      exact copy_loop_ok hd hp hI₄ (by rw [hm₄]; exact hC₀) (by omega)
  -- Is the buffer full?
  refine WP.seq (wp_mov32i fun s₈ u₈ _ _ => wp_cmpi fun s₉ g₉ m₉ rd₉ wr₉ _ z₉ => WP.block_nil ?_)
  have hne14 : ∀ r ∈ [Reg.rbx, .r15, .rsp, .rbp, .r12, .r13, .rax], r ≠ .r14 := by decide
  have hC₉ : Copy P s₀ c s.mem (tt P s₀ c) s₉ :=
    hC.of_gpr (fun r hr => by rw [g₉, u₈.other r (hne14 r hr)]) (by rw [m₉, u₈.mem])
      (by rw [rd₉, u₈.rd]) (by rw [wr₉, u₈.wr])
  have hz₉ : s₉.zf = some (decide (rr P s₀ c + tt P s₀ c = P.B)) := by
    rw [z₉, u₈.other _ (by decide), hC.r13, sx_ofNat (by omega), sub_beq (by omega) (by omega)]
  have h14 : s₉.gpr .r14 = 0 := by rw [g₉, u₈.gpr]; rfl
  refine WP.ite (decide (rr P s₀ c + tt P s₀ c = P.B)) (by simp [eval, hz₉]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.mono (fill_pending hd hp hI hC₉ hb) fun s' h => .inl ⟨c + tt P s₀ c, by omega, h.1, h.2⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (.inr (fill_done hd hp hI hC₉ h14 hb))

/-- Where the block compressed after absorbing `c` bytes is: in the data if
the buffer is empty and a whole block remains, otherwise in the buffer. -/
def srcOf (P : Params) (s₀ : State) (c : Nat) : Addr :=
  if rr P s₀ c = 0 ∧ P.B ≤ len s₀ - c then dp s₀ + BitVec.ofNat 64 c else st s₀ + BitVec.ofNat 64 P.N

/-- The first half of an iteration. -/
theorem head_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {s : State} (hI : Inv H s₀ c s) :
    WP isa (updateHead P) s fun s' =>
      (∃ c', c < c' ∧ Pending H s₀ c' s' ∧ s'.gpr .rsi = srcOf P s₀ c) ∨ Done H s₀ s' := by
  have hlen := len_lt s₀; have hc := hI.c_le; have hr := rr_lt hd s₀ c
  have := hd.B
  have hr' : (cnt s₀ + c) % P.B < P.B := Nat.mod_lt _ hd.pos
  unfold updateHead
  refine WP.seq (wp_test fun s₁ g₁ m₁ rd₁ wr₁ z₁ => WP.block_nil ?_)
  have hI₁ := hI.of_gpr (fun r _ => by rw [g₁]) m₁ rd₁ wr₁
  refine WP.ite (decide (rr P s₀ c = 0))
    (by rw [show isa.eval .e s₁ = s₁.zf from rfl, z₁, hI.r13, BitVec.and_self, ofNat_beq_zero (by omega)])
    (fun hb => ?_) (fun hb => WP.mono (fill_ok hd hp hI₁) fun _ h => h.imp
      (fun ⟨c', hc', hP, hs⟩ => ⟨c', hc', hP, by
        rw [hs, srcOf]; exact (ite_eq_right_iff.mpr fun h => absurd h.1 (by simpa using hb)).symm⟩) id)
  simp only [decide_eq_true_eq] at hb
  refine WP.seq (wp_cmpi fun s₂ g₂ m₂ rd₂ wr₂ cf₂ _ => WP.block_nil ?_)
  have hI₂ := hI₁.of_gpr (fun r _ => by rw [g₂]) m₂ rd₂ wr₂
  have hcf : s₂.cf = some (decide (len s₀ - c < P.B)) := by
    rw [cf₂, hI₁.r12, sx_ofNat (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  refine WP.ite (!decide (len s₀ - c < P.B)) (by simp [eval, hcf]) (fun hb' => ?_) (fun hb' =>
    WP.mono (fill_ok hd hp hI₂) fun _ h => h.imp
      (fun ⟨c', hc', hP, hs⟩ => ⟨c', hc', hP, by
        rw [hs, srcOf]; exact (ite_eq_right_iff.mpr fun h => absurd h.2 (by simp at hb'; omega)).symm⟩) id)
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hb'
  exact WP.mono (direct_ok hd hp hI₂ hb hb') fun s' h => .inl ⟨c + P.B, by omega, h.1, by
    rw [h.2, srcOf]; exact (ite_eq_left_iff.mpr fun h => absurd ⟨hb, hb'⟩ h).symm⟩

theorem body_ok (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P s₀) {c : Nat} {s : State} (hI : Inv H s₀ c s) :
    WP isa (updateBody P name code) s (Step H s₀ c) :=
  WP.seq (WP.mono (head_ok hd hp hI) fun _ h =>
    tail_ok hd hf hp (h.imp (fun ⟨c', hc, hP, _⟩ => ⟨c', hc, hP⟩) id))

theorem correct (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P s₀) :
    WP isa (update P name code) s₀ fun s' => gprPreserved s₀ s' ∧ (updK H).post s₀ s' := by
  unfold update
  refine WP.seq (WP.mono (prologue_ok (H := H) hd hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := Inv H s₀ (len s₀)) ?_ fun s₂ hI₂ => epilogue_ok hd hp hI₂)
  refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ Inv H s₀ c s) ?_ (len s₀) s₁ ⟨0, rfl, hI⟩
  rintro n s ⟨c, rfl, hI⟩
  refine WP.mono (body_ok hd hf hp hI) fun s' h => ?_
  rcases h with ⟨he, hI'⟩ | ⟨he, c', hc, hI'⟩
  · exact .inl ⟨he, hI'⟩
  · exact .inr ⟨he, len s₀ - c', by have := hI'.c_le; omega, c', rfl, hI'⟩

end

end VG.Proof.MdStream.X86_64.Update
