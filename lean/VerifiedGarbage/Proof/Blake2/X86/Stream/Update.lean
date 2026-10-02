import VerifiedGarbage.Proof.Blake2.X86.Stream.Common

/-!
# Streaming BLAKE2 on x86 (32-bit): `update`

The functional correctness of `update`, for either word size and any correct
compression function (`CalleeOk`).
-/

namespace VG.Proof.Blake2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Spec.Blake2
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.Stream
open VG.Proof.Blake2 (compressX86 updateX86 countX86 ReprR bufLen_le repr_iff reprR_append reprR_flush
  reprR_blocks repr_of_reprR stateAt_congr bytesAt_congr bytesAt_add compressBlocks_congr compressBlocks_succ
  compressBlocks_zero)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)
open VG.Proof.MdStream.X86 (contains_addr addr_add_ofNat sub_offset contains_offset)

variable {w : Nat} {P : Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev cnt : Nat := (countX86 s₀).toNat
abbrev dp : BitVec 32 := arg s₀ 3
abbrev len : Nat := (arg s₀ 4).toNat
abbrev scr : BitVec 32 := arg s₀ 5
abbrev stA : Addr := (st s₀).setWidth 64
abbrev dA : Addr := (dp s₀).setWidth 64
abbrev scA : Addr := (scr s₀).setWidth 64
abbrev stR (w : Nat) : Region := ⟨stA s₀, bufOff w + blockBytes w⟩
abbrev dR : Region := ⟨dA s₀, len s₀⟩
abbrev scR : Region := ⟨scA s₀, 576⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 24⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
/-- Where the calls of the compression function push its arguments and store
the return address. -/
abbrev stkR : Region := below (esp₀ s₀) 32
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dA s₀) c

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀, argR s₀]
  wr : s₀.wr = [stR s₀ w, scR s₀]
  st_scr : (stR s₀ w).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀ w)
  d_scr : (dR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀ w)
  a_scr : (argR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀ w)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀ w)
  stk_scr : (stkR s₀).Disjoint (scR s₀)
  stk_d : (stkR s₀).Disjoint (dR s₀)
  st_fit : (st s₀).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + len s₀ ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 576 ≤ 2 ^ 32
  sp_lo : 32 ≤ (esp₀ s₀).toNat
  sp_fit : (esp₀ s₀).toNat + 28 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : (updateX86 P).pre s₀) : Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  have e := stk_eq h16
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, by show (below _ _).Disjoint _; rw [e]; exact h10,
    by show (below _ _).Disjoint _; rw [e]; exact h11, by show (below _ _).Disjoint _; rw [e]; exact h12,
    h13, h14, h15, h16, h17⟩

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 32 := (arg s₀ 4).isLt

theorem D_length (s₀ : State) (c : Nat) : (D s₀ c).length = c := by simp [bytesAt]

namespace Pre
variable {s₀ : State} (hp : Pre w s₀)
include hp

theorem scr_in {d : Nat} (hd : d + 4 ≤ 576) : (scR s₀).Contains (addr (scr s₀) d) 4 :=
  contains_addr hd (by omega) hp.scr_fit

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  show (⟨addr (esp₀ s₀) 4, 24⟩ : Region).Contains _ _
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ hd₁ (by omega) (by omega)

/-- An argument word, as a region. -/
theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  show Region.Sub _ ⟨addr (esp₀ s₀) 4, 24⟩
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sub _ hd₁ (by omega)

theorem a_stk : (argR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨addr (esp₀ s₀) 4, 24⟩ ⟨(esp₀ s₀ - BitVec.ofNat 32 32).setWidth 64, 32⟩
  rw [addr_eq (by omega), Taint.sub_setWidth (by omega)]
  exact Offset.disjoint_below _ (by omega)

theorem ret_stk : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨(esp₀ s₀).setWidth 64, 4⟩ ⟨(esp₀ s₀ - BitVec.ofNat 32 32).setWidth 64, 32⟩
  rw [Taint.sub_setWidth (by omega)]
  exact Offset.base_disjoint_below _ (by omega)

theorem rin {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 28) :
    InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [hrd, hp.rd], hp.arg_in h₁ h₂⟩

theorem sin {s : State} (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 576) :
    InRegions s.wr (addr (scr s₀) d) 4 :=
  ⟨scR s₀, by simp [hwr, hp.wr], hp.scr_in hd⟩

theorem sinr {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 576) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
  ⟨scR s₀, by simp [hrd, hwr, hp.wr], hp.scr_in hd⟩

/-- The scratch space is disjoint from the other regions the code writes. -/
theorem scr_disj : ∀ r ∈ [stR s₀ w, stkR s₀], Region.Disjoint ⟨(scr s₀).setWidth 64, 576⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.st_scr.symm, hp.stk_scr.symm⟩

end Pre

/-- The data the initial state represents, from `h0`. -/
def R₀ (P : Params w) (s₀ : State) (h0 : HashValue w) (d : List Byte) : Prop :=
  Spec.Blake2.Repr P h0 s₀.mem (stA s₀) d ∧ countX86 s₀ = BitVec.ofNat 64 d.length ∧
    d.length + len s₀ < 2 ^ 64

theorem R₀.cnt_eq {s₀ : State} {h0 : HashValue w} {d : List Byte} (h : R₀ P s₀ h0 d) :
    cnt s₀ = d.length := by
  rw [cnt, h.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.2.2; omega)]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (w : Nat) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  ebp : s.gpr .ebp = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  frame : Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved (scr s₀) s₀ s.mem

/-- The state represents the data followed by the first `c` bytes of data,
the last `r` of them in the buffer. -/
structure Inv (P : Params w) (s₀ : State) (c r : Nat) (s : State) : Prop extends Common w s₀ c s where
  repr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (stA s₀) (d ++ D s₀ c) r

/-- The data pointer and the bytes left. -/
structure Ptr (s₀ : State) (c : Nat) (s : State) : Prop where
  esi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 c
  edi : s.gpr .edi = BitVec.ofNat 32 (len s₀ - c)

/-- The byte count. -/
structure Cnt (s₀ : State) (c : Nat) (m : Mem) : Prop where
  lo : m.readW (addr (scr s₀) cloOff) 32 = BitVec.ofNat 32 (cnt s₀ + c)
  hi : m.readW (addr (scr s₀) chiOff) 32 = BitVec.ofNat 32 ((cnt s₀ + c) / 2 ^ 32)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common w s₀ c s)
    (hg : ∀ r ∈ [Reg.ebx, .ebp, .esp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common w s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hg _ (by simp)]; exact h.ebx
  ebp := by rw [hg _ (by simp)]; exact h.ebp
  esp := by rw [hg _ (by simp)]; exact h.esp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c r : Nat} {s s' : State} (h : Inv P s₀ c r s)
    (hg : ∀ r ∈ [Reg.ebx, .ebp, .esp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv P s₀ c r s' :=
  { h.toCommon.of_gpr hg hm hrd hwr with repr := by rw [hm]; exact h.repr }

theorem Ptr.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Ptr s₀ c s)
    (h₁ : s'.gpr .esi = s.gpr .esi) (h₂ : s'.gpr .edi = s.gpr .edi) : Ptr s₀ c s' :=
  ⟨h₁.trans h.esi, h₂.trans h.edi⟩

/-- The argument words are never written. -/
theorem Common.arg {s₀ : State} (hp : Pre w s₀) {c : Nat} {s : State} (h : Common w s₀ c s) {d : Nat}
    (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 28) :
    s.mem.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 := by
  refine h.frame.readW (r := ⟨addr (esp₀ s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.a_st.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_scr.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_stk.sub_left (hp.arg_sub h₁ h₂)

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre w s₀) {c : Nat} {s : State} (h : Common w s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dA s₀ + BitVec.ofNat 64 i) = s₀.mem (dA s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩)
    (by have := len_lt s₀; simp only; omega) hi

/-- Writes to the scratch space keep the state's bytes. -/
theorem st_keep (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {m m' : Mem} (hf : Frame [scR s₀] m m') :
    ∀ i < bufOff w + blockBytes w, m' (stA s₀ + BitVec.ofNat 64 i) = m (stA s₀ + BitVec.ofNat 64 i) :=
  fun i hi => hf.bytes (R := stR s₀ w) (by simpa using hp.st_scr) (by have := hP.len; simp only; omega) hi

/-! ## Prologue -/

/-- The memory after the prologue. -/
def proMem (s₀ : State) : Mem :=
  ((saveMem (scr s₀) s₀).writeW (addr (scr s₀) cloOff) (arg s₀ 1)).writeW (addr (scr s₀) chiOff) (arg s₀ 2)

theorem proMem_frame {s₀ : State} (hp : Pre w s₀) : Frame [scR s₀] s₀.mem (proMem s₀) :=
  ((saveMem_frame hp.scr_fit s₀).writeW (List.mem_singleton_self _) _ (hp.scr_in (by decide))).writeW
    (List.mem_singleton_self _) _ (hp.scr_in (by decide))

theorem cnt_lo (s₀ : State) : BitVec.ofNat 32 (cnt s₀) = arg s₀ 1 := lo_append _ _
theorem cnt_hi (s₀ : State) : BitVec.ofNat 32 (cnt s₀ / 2 ^ 32) = arg s₀ 2 := hi_append _ _

theorem proMem_cnt {s₀ : State} (hp : Pre w s₀) : Cnt s₀ 0 (proMem s₀) := by
  refine ⟨?_, ?_⟩ <;> simp only [proMem, Nat.add_zero]
  · rw [rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, cnt_lo]
  · rw [Mem.readW_writeW_self32, cnt_hi]

theorem proMem_saved {s₀ : State} (hp : Pre w s₀) : Saved (scr s₀) s₀ (proMem s₀) :=
  (saveMem_saved hp.scr_fit s₀).of_readW fun p hp' => by
    have := saved_bound p hp'
    simp only [proMem]
    rw [rw_scr hp.scr_fit _ _ (by omega) (by decide) (by simp only [chiOff]; omega),
      rw_scr hp.scr_fit _ _ (by omega) (by decide) (by simp only [cloOff]; omega)]

theorem prologue_ok {s₀ : State} (hp : Pre w s₀) :
    WP isa (.block updateStart) s₀ fun s =>
      Common w s₀ 0 s ∧ Ptr s₀ 0 s ∧ s.mem = proMem s₀ ∧ s.gpr .eax = arg s₀ 1 ∧ s.gpr .ecx = arg s₀ 2 := by
  have rin : ∀ {d}, 4 ≤ d → d + 4 ≤ 28 → InRegions (s₀.rd ++ s₀.wr) (addr (esp₀ s₀) d) 4 :=
    fun h₁ h₂ => hp.rin rfl h₁ h₂
  have sin : ∀ {d}, d + 4 ≤ 576 → InRegions s₀.wr (addr (scr s₀) d) 4 := fun h => hp.sin rfl h
  -- The saves only touch the scratch space, so the arguments stay readable.
  have sepA : ∀ d e, 512 ≤ d → d + 4 ≤ 576 → 4 ≤ e → e + 4 ≤ 28 →
      Mem.Sep (addr (esp₀ s₀) e) 4 (addr (scr s₀) d) 4 := by
    intro d e h₁ h₂ h₃ h₄
    exact hp.a_scr.sep (hp.arg_in h₃ h₄) (hp.scr_in h₂)
  have argSave : ∀ e, 4 ≤ e → e + 4 ≤ 28 →
      (saveMem (scr s₀) s₀).readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 := by
    intro e h₁ h₂
    exact Spill.saveMem_readW_of_sep _ _ (by decide) _ _ fun p h =>
      have := saved_bound p h; sepA _ e this.1 (by omega) h₁ h₂
  rw [show updateStart = .mov .eax (.mem (at_ .esp 24)) :: (Spill.saveCode .eax saved ++
    ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .esi (.mem (at_ .esp 16)),
      .mov .edi (.mem (at_ .esp 20)), .mov .eax (.mem (at_ .esp 8)), .store (at_ .ebp cloOff) .eax,
      .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp chiOff) .ecx] : List Instr)) from rfl]
  refine wp_ldm (B := esp₀ s₀) rfl (rin (d := 24) (by omega) (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine Spill.save_ok saved (fun p h => by
    rw [e₁, u₁.wr]; exact sin (by have := saved_bound p h; omega)) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := u₅.gpr
  have m₅ : s₅.mem = saveMem (scr s₀) s₀ := by
    rw [u₅.mem, e₁, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₁.wr]
  have sp₅ : s₅.gpr .esp = esp₀ s₀ := by rw [g₅, u₁.other _ (by decide)]
  have ld : ∀ e, 4 ≤ e → e + 4 ≤ 28 → s₅.mem.readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 :=
    fun e h₁ h₂ => by rw [m₅]; exact argSave e h₁ h₂
  refine wp_mov fun s₆ u₆ => ?_
  have ebp₆ : s₆.gpr .ebp = scr s₀ := by rw [u₆.gpr, g₅, e₁]
  have sp₆ : s₆.gpr .esp = esp₀ s₀ := by rw [u₆.other _ (by decide), sp₅]
  have rd' : ∀ d, 4 ≤ d → d + 4 ≤ 28 → InRegions (s₆.rd ++ s₆.wr) (addr (esp₀ s₀) d) 4 :=
    fun d h₁ h₂ => by rw [u₆.rd, u₆.wr, rd₅, wr₅]; exact rin h₁ h₂
  refine wp_ldm sp₆ (rd' 4 (by omega) (by omega)) fun s₇ u₇ => ?_
  refine wp_ldm (by rw [u₇.other _ (by decide), sp₆]) (by rw [u₇.rd, u₇.wr]; exact rd' 16 (by omega) (by omega))
    fun s₈ u₈ => ?_
  refine wp_ldm (by rw [u₈.other _ (by decide), u₇.other _ (by decide), sp₆])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr]; exact rd' 20 (by omega) (by omega)) fun s₉ u₉ => ?_
  refine wp_ldm (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), sp₆])
    (by rw [u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr]; exact rd' 8 (by omega) (by omega)) fun s₁₀ u₁₀ => ?_
  have g₁₀ : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .esi → r ≠ .ebx → s₁₀.gpr r = s₆.gpr r := fun r a b c d => by
    rw [u₁₀.other r a, u₉.other r b, u₈.other r c, u₇.other r d]
  have m₁₀ : s₁₀.mem = saveMem (scr s₀) s₀ := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]
  have rd₁₀ : s₁₀.rd = s₀.rd := by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅]
  have wr₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]
  refine wp_stm (by rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), ebp₆])
    (hp.sin wr₁₀ (d := cloOff) (by decide)) fun s₁₁ u₁₁ => ?_
  refine wp_ldm (by rw [u₁₁.gpr, g₁₀ _ (by decide) (by decide) (by decide) (by decide), sp₆])
    (by rw [u₁₁.rd, u₁₁.wr]; exact hp.rin rd₁₀ (d := 12) (by omega) (by omega)) fun s₁₂ u₁₂ => ?_
  refine wp_stm (by rw [u₁₂.other _ (by decide), u₁₁.gpr, g₁₀ _ (by decide) (by decide) (by decide) (by decide),
    ebp₆]) (by rw [u₁₂.wr, u₁₁.wr]; exact hp.sin wr₁₀ (d := chiOff) (by decide)) fun s₁₃ u₁₃ => WP.block_nil ?_
  -- The argument words the loads read.
  have a8 : s₁₀.gpr .eax = arg s₀ 1 := by
    rw [u₁₀.gpr, u₉.mem, u₈.mem, u₇.mem, u₆.mem, ld 8 (by omega) (by omega)]; rfl
  have a12 : s₁₂.gpr .ecx = arg s₀ 2 := by
    rw [u₁₂.gpr, u₁₁.mem, m₁₀, Mem.readW_writeW_sep (sepA cloOff 12 (by decide) (by decide) (by omega)
      (by omega)) (by decide), argSave 12 (by omega) (by omega)]; rfl
  have g₁₃ : ∀ r, r ≠ .ecx → s₁₃.gpr r = s₁₀.gpr r := fun r h => by
    rw [u₁₃.gpr, u₁₂.other r h, u₁₁.gpr]
  have m₁₃ : s₁₃.mem = proMem s₀ := by
    rw [u₁₃.mem, a12, u₁₂.mem, u₁₁.mem, a8, m₁₀]; rfl
  have rd₁₃ : s₁₃.rd = s₀.rd := by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, rd₁₀]
  have wr₁₃ : s₁₃.wr = s₀.wr := by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, wr₁₀]
  have l4 : s₆.mem.readW (addr (esp₀ s₀) 4) 32 = arg s₀ 0 := by rw [u₆.mem, ld 4 (by omega) (by omega)]; rfl
  have l16 : s₆.mem.readW (addr (esp₀ s₀) 16) 32 = arg s₀ 3 := by
    rw [u₆.mem, ld 16 (by omega) (by omega)]; rfl
  have l20 : s₆.mem.readW (addr (esp₀ s₀) 20) 32 = arg s₀ 4 := by
    rw [u₆.mem, ld 20 (by omega) (by omega)]; rfl
  refine ⟨⟨Nat.zero_le _, rd₁₃, wr₁₃, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, m₁₃, ?_, ?_⟩
  · rw [g₁₃ _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, l4]
  · rw [g₁₃ _ (by decide), g₁₀ _ (by decide) (by decide) (by decide) (by decide), ebp₆]
  · rw [g₁₃ _ (by decide), g₁₀ _ (by decide) (by decide) (by decide) (by decide), sp₆]
  · rw [m₁₃]; exact (proMem_frame hp).mono (by simp)
  · rw [m₁₃]; exact proMem_saved hp
  · rw [g₁₃ _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.mem, l16]; simp
  · rw [g₁₃ _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.mem, u₇.mem, l20]; simp
  · rw [g₁₃ _ (by decide), a8]
  · rw [u₁₃.gpr, a12]

/-! ## The bytes in the buffer -/

theorem bufLen_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (hC : Common w s₀ 0 s)
    (hptr : Ptr s₀ 0 s) (hm : s.mem = proMem s₀) (hax : s.gpr .eax = arg s₀ 1) (hcx : s.gpr .ecx = arg s₀ 2) :
    WP isa (Impl.Blake2.X86.Stream.bufLen w) s fun s' =>
      Inv P s₀ 0 (Proof.Blake2.bufLen w (cnt s₀)) s' ∧ Ptr s₀ 0 s' ∧ Cnt s₀ 0 s'.mem ∧
        s'.gpr .eax = BitVec.ofNat 32 (Proof.Blake2.bufLen w (cnt s₀)) := by
  -- The representation.
  have hrepr : ∀ h0 d, R₀ P s₀ h0 d →
      ReprR P h0 s.mem (stA s₀) (d ++ D s₀ 0) (Proof.Blake2.bufLen w (cnt s₀)) := by
    intro h0 d hd
    have e : D s₀ 0 = [] := by simp [bytesAt]
    rw [e, List.append_nil, hd.cnt_eq, ← repr_iff P hP.pos, hm]
    exact repr_congr hP (st_keep hP hp (proMem_frame hp)) hd.1
  have hcnt := proMem_cnt hp
  rw [← hm] at hcnt
  unfold Impl.Blake2.X86.Stream.bufLen
  refine WP.seq (wp_orZ fun s₁ u₁ z₁ => WP.block_nil ?_)
  have hz : isa.eval .e s₁ = some (decide (cnt s₀ = 0)) := by
    show s₁.zf = _
    rw [z₁, hcx, hax, or_beq_zero]; rfl
  have hC₁ : Common w s₀ 0 s₁ := hC.of_gpr (fun r hr => u₁.other r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    u₁.mem u₁.rd u₁.wr
  have hptr₁ : Ptr s₀ 0 s₁ := hptr.of_gpr (u₁.other _ (by decide)) (u₁.other _ (by decide))
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_movi fun s₂ u₂ => WP.block_nil ?_
    have e : Proof.Blake2.bufLen w (cnt s₀) = 0 := by simp [Proof.Blake2.bufLen, hb]
    refine ⟨{ hC₁.of_gpr (fun r hr => u₂.other r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
      u₂.mem u₂.rd u₂.wr with repr := ?_ }, hptr₁.of_gpr (u₂.other _ (by decide)) (u₂.other _ (by decide)),
      by rw [u₂.mem, u₁.mem]; exact hcnt, by rw [u₂.gpr, e]; rfl⟩
    rw [u₂.mem, u₁.mem]; exact hrepr
  · simp only [decide_eq_false_iff_not] at hb
    refine wp_subi fun s₂ u₂ _ _ => wp_andi fun s₃ u₃ => wp_addi fun s₄ u₄ => WP.block_nil ?_
    have g : ∀ r, r ≠ .eax → s₄.gpr r = s₁.gpr r := fun r h => by
      rw [u₄.other r h, u₃.other r h, u₂.other r h]
    have hm₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    refine ⟨{ hC₁.of_gpr (fun r hr => g r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
      (by rw [hm₄, u₁.mem]) (by rw [u₄.rd, u₃.rd, u₂.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr]) with repr := ?_ },
      hptr₁.of_gpr (g _ (by decide)) (g _ (by decide)), by rw [hm₄]; exact hcnt, ?_⟩
    · rw [hm₄]; exact hrepr
    · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hax, ← cnt_lo, mask_ofNat hP hb]
      simp [Proof.Blake2.bufLen, hb]

/-! ## Copying data into the buffer -/

theorem dp_add {s₀ : State} (hp : Pre w s₀) {c : Nat} (hc : c < len s₀) :
    (dp s₀ + BitVec.ofNat 32 c).setWidth 64 = dA s₀ + BitVec.ofNat 64 c :=
  sw_add (by have := hp.d_fit; omega)

/-- Copying `k` bytes of data, from byte `c` on, into the buffer, from byte
`r` on: only the buffer changes. -/
theorem copy_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c r k : Nat} (hk : 1 ≤ k)
    (hrk : r + k ≤ blockBytes w) (hck : c + k ≤ len s₀) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hesi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 c)
    (hedx : s.gpr .edx = st s₀ + BitVec.ofNat 32 r) (hecx : s.gpr .ecx = BitVec.ofNat 32 k)
    (hf : Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem s.mem)
    (hrepr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (stA s₀) (d ++ D s₀ c) r) :
    WP isa (copyLoop w .esi .edx .ecx .al) s fun s' =>
      (∀ x, x ≠ .esi → x ≠ .edx → x ≠ .ecx → x ≠ .eax → s'.gpr x = s.gpr x) ∧
      s'.gpr .esi = dp s₀ + BitVec.ofNat 32 (c + k) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      Frame [stR s₀ w] s.mem s'.mem ∧
      ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s'.mem (stA s₀) (d ++ D s₀ (c + k)) (r + k) := by
  have hl := hP.len
  have hL := len_lt s₀
  have fS := hp.st_fit
  have fD := hp.d_fit
  have hN : bufOff w = blockBytes w / 2 := hP.N
  have eD : addr (st s₀ + BitVec.ofNat 32 r) (bufOff w) = stA s₀ + BitVec.ofNat 64 (bufOff w + r) := by
    rw [MdStream.X86.addr_add_ofNat (by omega), Nat.add_comm]
  have eS : (dp s₀ + BitVec.ofNat 32 c).setWidth 64 = dA s₀ + BitVec.ofNat 64 c := dp_add hp (by omega)
  have hsrc : ∀ i < k, InRegions (s.rd ++ s.wr) ((dp s₀ + BitVec.ofNat 32 c).setWidth 64 + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨dR s₀, by simp [hrd, hp.rd], by
      rw [eS, Offset.add_add]; exact contains_offset (by omega) (by omega)⟩
  have hdst : ∀ i < k, InRegions s.wr (addr (st s₀ + BitVec.ofNat 32 r) (bufOff w) + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨stR s₀ w, by simp [hwr, hp.wr], by
      rw [eD, Offset.add_add]; exact contains_offset (by omega) (by omega)⟩
  have hd : Region.Disjoint ⟨(dp s₀ + BitVec.ofNat 32 c).setWidth 64, k⟩
      ⟨addr (st s₀ + BitVec.ofNat 32 r) (bufOff w), k⟩ := by
    rw [eS, eD]
    exact (hp.d_st.sub_left (sub_offset (by omega) (by omega))).sub_right (sub_offset (by omega) (by omega))
  refine copyLoop_ok (w := w) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hk
    (by omega) (by rw [toNat_add_ofNat (by omega)]; omega) (by rw [toNat_add_ofNat (by omega)]; omega)
    hesi hedx hecx hsrc hdst hd fun s' h => ?_
  -- The bytes copied.
  have hx : bytesAt s.mem ((dp s₀ + BitVec.ofNat 32 c).setWidth 64) k =
      bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k := by
    rw [eS]
    refine bytesAt_congr fun i hi => ?_
    rw [Offset.add_add]
    exact hf.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩)
      (by simp only; omega) (show c + i < len s₀ by omega)
  have hm : s'.mem = writeBytes s.mem (stA s₀ + BitVec.ofNat 64 (bufOff w + r))
      (bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k) := by
    rw [h.mem, List.take_of_length_le (by rw [bytesAt_length]), hx, eD]
  have hfw : Frame [stR s₀ w] s.mem s'.mem := by
    rw [hm]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact contains_offset (by omega) (by omega))
  refine ⟨fun x a b c d => h.other x a b c d, ?_, h.rd.trans hrd, h.wr.trans hwr, hfw, fun h0 d hd => ?_⟩
  · rw [h.srcV, BitVec.add_assoc, BitVec.ofNat_add]
  have e : d ++ D s₀ (c + k) = d ++ D s₀ c ++ bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k := by
    rw [D, bytesAt_add, List.append_assoc]
  rw [e]
  have := reprR_append P (hrepr h0 d hd) (x := bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k)
    (mem' := s'.mem) (by rw [bytesAt_length]; exact hrk) ?_ ?_
  · rwa [bytesAt_length] at this
  · rw [hm]
    exact stateAt_congr fun i hi => VG.WriteBytes.writeBytes_before _ _ _ (by omega)
      (by rw [bytesAt_length]; omega)
  · rw [hm, ← Offset.add_add, bytesAt_writeBytes _ _ _ _ (by rw [bytesAt_length]; omega)]

/-! ## Writes to the scratch space and the buffer -/

theorem Saved.write {s₀ : State} (hp : Pre w s₀) {m : Mem} (h : Saved (scr s₀) s₀ m) {d : Nat} (hd : 528 ≤ d)
    (hd' : d + 4 ≤ 576) (v : BitVec 32) : Saved (scr s₀) s₀ (m.writeW (addr (scr s₀) d) v) :=
  h.of_readW fun p hp' => have := saved_bound p hp'; rw_scr hp.scr_fit _ _ (by omega) hd' (by omega)

theorem Saved.st {s₀ : State} (hp : Pre w s₀) {m m' : Mem} (h : Saved (scr s₀) s₀ m)
    (hf : Frame [stR s₀ w] m m') : Saved (scr s₀) s₀ m' :=
  Saved.keep hp.scr_fit h (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
    (by simpa using hp.st_scr.symm)

theorem frame_scr {s₀ : State} (hp : Pre w s₀) {m : Mem} (hf : Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem m)
    {d : Nat} (hd : d + 4 ≤ 576) (v : BitVec 32) :
    Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem (m.writeW (addr (scr s₀) d) v) :=
  hf.writeW (by simp) _ (hp.scr_in hd)

theorem frame_st {s₀ : State} {m m' : Mem} (hf : Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem m)
    (hf' : Frame [stR s₀ w] m m') : Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem m' :=
  hf.trans (hf'.mono (by simp))

/-- The byte count is kept by writes to the buffer. -/
theorem Cnt.st {s₀ : State} (hp : Pre w s₀) {c : Nat} {m m' : Mem} (h : Cnt s₀ c m)
    (hf : Frame [stR s₀ w] m m') : Cnt s₀ c m' := by
  have k := fun d (h₁ : 512 ≤ d) (h₂ : d + 4 ≤ 576) =>
    keep_hi hp.scr_fit (m := m) (m' := m') (rs := [stR s₀ w]) (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
      (by simpa using hp.st_scr.symm) h₁ h₂
  exact ⟨(k cloOff (by decide) (by decide)).trans h.lo, (k chiOff (by decide) (by decide)).trans h.hi⟩

/-! ## `fill` -/

theorem fill_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c r : Nat} (hr : r ≤ blockBytes w) {s : State}
    (hI : Inv P s₀ c r s) (hptr : Ptr s₀ c s) (hcnt : Cnt s₀ c s.mem) (hax : s.gpr .eax = BitVec.ofNat 32 r) :
    WP isa (fill w) s fun s' =>
      Inv P s₀ (c + min (blockBytes w - r) (len s₀ - c)) (r + min (blockBytes w - r) (len s₀ - c)) s' ∧
      Ptr s₀ (c + min (blockBytes w - r) (len s₀ - c)) s' ∧
      Cnt s₀ (c + min (blockBytes w - r) (len s₀ - c)) s'.mem := by
  have hl := hP.len
  have hL := len_lt s₀
  have hc := hI.c_le
  obtain ⟨a, ha⟩ : ∃ a, a = min (blockBytes w - r) (len s₀ - c) := ⟨_, rfl⟩
  rw [← ha]
  have ha₁ : a ≤ blockBytes w - r := ha ▸ Nat.min_le_left _ _
  have ha₂ : a ≤ len s₀ - c := ha ▸ Nat.min_le_right _ _
  unfold fill
  refine WP.seq (wp_movi fun s₁ u₁ => wp_sub fun s₂ u₂ _ => wp_cmp fun s₃ f₃ cf₃ _ => WP.block_nil ?_)
  have hcx₂ : s₂.gpr .ecx = BitVec.ofNat 32 (blockBytes w - r) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hax, B_eq, sub_ofNat hr]
  have hdi₂ : s₂.gpr .edi = BitVec.ofNat 32 (len s₀ - c) := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), hptr.edi]
  have g₃ : ∀ x, x ≠ .ecx → s₃.gpr x = s.gpr x := fun x h => by rw [f₃.gpr, u₂.other x h, u₁.other x h]
  -- `ecx` := `a`.
  refine WP.seq (WP.mono (Q := fun (t : State) => t.gpr .ecx = BitVec.ofNat 32 a ∧
      (∀ x, x ≠ .ecx → t.gpr x = s.gpr x) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ fun t ht => ?_)
  · have hm : s₃.mem = s.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
    have hrd : s₃.rd = s.rd := by rw [f₃.rd, u₂.rd, u₁.rd]
    have hwr : s₃.wr = s.wr := by rw [f₃.wr, u₂.wr, u₁.wr]
    have hcf : isa.eval .b s₃ = some (decide (len s₀ - c < blockBytes w - r)) := by
      show s₃.cf = _
      rw [cf₃, hdi₂, hcx₂, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
    refine WP.ite _ hcf (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine wp_mov fun s₄ u₄ => WP.block_nil ⟨?_, fun x h => by rw [u₄.other x h, g₃ x h],
        by rw [u₄.mem, hm], by rw [u₄.rd, hrd], by rw [u₄.wr, hwr]⟩
      rw [u₄.gpr, f₃.gpr, hdi₂, ha, Nat.min_eq_right (by omega)]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨?_, g₃, hm, hrd, hwr⟩
      rw [f₃.gpr, hcx₂, ha, Nat.min_eq_left (by omega)]
  obtain ⟨tcx, tg, tm, trd, twr⟩ := ht
  have tbp : t.gpr .ebp = scr s₀ := by rw [tg _ (by decide), hI.ebp]
  have trd' : t.rd = s₀.rd := trd.trans hI.rd
  have twr' : t.wr = s₀.wr := twr.trans hI.wr
  refine WP.seq (wp_sub fun s₅ u₅ _ => wp_mov fun s₆ u₆ => wp_add fun s₇ u₇ _ => ?_)
  have g₇ : ∀ x, x ≠ .edx → x ≠ .edi → s₇.gpr x = t.gpr x := fun x h1 h2 => by
    rw [u₇.other x h1, u₆.other x h1, u₅.other x h2]
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, tm]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, trd']
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, twr']
  have bp₇ : s₇.gpr .ebp = scr s₀ := by rw [g₇ _ (by decide) (by decide), tbp]
  have cx₇ : s₇.gpr .ecx = BitVec.ofNat 32 a := by rw [g₇ _ (by decide) (by decide), tcx]
  -- The byte count.
  refine wp_ldmF bp₇ (hp.sinr rd₇ wr₇ (d := cloOff) (by decide)) fun s₈ u₈ _ _ => ?_
  refine wp_add fun s₉ u₉ cf₉ => ?_
  refine wp_stm (o := cloOff) (by rw [u₉.other _ (by decide), u₈.other _ (by decide), bp₇])
    (by rw [u₉.wr, u₈.wr, wr₇]; exact hp.sin rfl (by decide)) fun s₁₀ u₁₀ => ?_
  have bp₁₀ : s₁₀.gpr .ebp = scr s₀ := by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), bp₇]
  have ichi := hp.sinr rd₇ wr₇ (d := chiOff) (by decide)
  refine wp_ldmF bp₁₀ (by rw [u₁₀.rd, u₁₀.wr, u₉.rd, u₉.wr, u₈.rd, u₈.wr]; exact ichi)
    fun s₁₁ u₁₁ cf₁₁ _ => ?_
  refine wp_adc0 (by rw [cf₁₁, u₁₀.cf, cf₉]) fun s₁₂ u₁₂ => ?_
  refine wp_stm (o := chiOff) (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), bp₁₀])
    (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇]; exact hp.sin rfl (by decide)) fun s₁₃ u₁₃ => ?_
  refine wp_test fun s₁₄ f₁₄ z₁₄ => WP.block_nil ?_
  -- The state after the block.
  have g₁₄ : ∀ x, x ≠ .eax → s₁₄.gpr x = s₇.gpr x := fun x h => by
    rw [f₁₄.gpr, u₁₃.gpr, u₁₂.other x h, u₁₁.other x h, u₁₀.gpr, u₉.other x h, u₈.other x h]
  have rd₁₄ : s₁₄.rd = s₀.rd := by rw [f₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, rd₇]
  have wr₁₄ : s₁₄.wr = s₀.wr := by rw [f₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇]
  have lo₉ : s₉.gpr .eax = BitVec.ofNat 32 (cnt s₀ + (c + a)) := by
    rw [u₉.gpr, u₈.gpr, u₈.other _ (by decide), cx₇, m₇, hcnt.lo, ← BitVec.ofNat_add, Nat.add_assoc]
  have m₁₀ : s₁₀.mem = s.mem.writeW (addr (scr s₀) cloOff) (BitVec.ofNat 32 (cnt s₀ + (c + a))) := by
    rw [u₁₀.mem, lo₉, u₉.mem, u₈.mem, m₇]
  have hi₁₂ : s₁₂.gpr .eax = BitVec.ofNat 32 ((cnt s₀ + (c + a)) / 2 ^ 32) := by
    rw [u₁₂.gpr, u₁₁.gpr, m₁₀, rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), hcnt.hi,
      u₈.gpr, u₈.other _ (by decide), cx₇, m₇, hcnt.lo, carry_ofNat _ _ (by omega), Nat.add_assoc]
  have m₁₄ : s₁₄.mem = (s.mem.writeW (addr (scr s₀) cloOff) (BitVec.ofNat 32 (cnt s₀ + (c + a)))).writeW
      (addr (scr s₀) chiOff) (BitVec.ofNat 32 ((cnt s₀ + (c + a)) / 2 ^ 32)) := by
    rw [f₁₄.mem, u₁₃.mem, hi₁₂, u₁₂.mem, u₁₁.mem, m₁₀]
  have hcnt₁₄ : Cnt s₀ (c + a) s₁₄.mem :=
    ⟨by rw [m₁₄, rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32],
      by rw [m₁₄, Mem.readW_writeW_self32]⟩
  have hfr₁₄ : Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem s₁₄.mem := by
    rw [m₁₄]; exact frame_scr hp (frame_scr hp hI.frame (by decide) _) (by decide) _
  have hsv₁₄ : Saved (scr s₀) s₀ s₁₄.mem := by
    rw [m₁₄]; exact Saved.write hp (Saved.write hp hI.saved (by decide) (by decide) _) (by decide) (by decide) _
  have hst₁₄ : ∀ i < bufOff w + blockBytes w,
      s₁₄.mem (stA s₀ + BitVec.ofNat 64 i) = s.mem (stA s₀ + BitVec.ofNat 64 i) := by
    refine st_keep hP hp ?_
    rw [m₁₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hp.scr_in (by decide))).writeW
      (List.mem_singleton_self _) _ (hp.scr_in (by decide))
  have di₁₄ : s₁₄.gpr .edi = BitVec.ofNat 32 (len s₀ - (c + a)) := by
    rw [g₁₄ _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, tg _ (by decide), tcx,
      hptr.edi, sub_ofNat (by omega), Nat.sub_sub]
  have dx₁₄ : s₁₄.gpr .edx = st s₀ + BitVec.ofNat 32 r := by
    rw [g₁₄ _ (by decide), u₇.gpr, u₆.gpr, u₆.other _ (by decide), u₅.other .ebx (by decide),
      u₅.other .eax (by decide), tg .ebx (by decide), tg .eax (by decide), hI.ebx, hax]
  have hz : isa.eval .e s₁₄ = some (decide (a = 0)) := by
    show s₁₄.zf = _
    rw [z₁₄, u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      u₈.other _ (by decide), cx₇, BitVec.and_self, ofNat_beq_zero (by omega)]
  have hC₁₄ : Common w s₀ c s₁₄ :=
    ⟨hc, rd₁₄, wr₁₄, by rw [g₁₄ _ (by decide), g₇ _ (by decide) (by decide), tg _ (by decide), hI.ebx],
      by rw [g₁₄ _ (by decide), bp₇], by rw [g₁₄ _ (by decide), g₇ _ (by decide) (by decide),
        tg _ (by decide), hI.esp], hfr₁₄, hsv₁₄⟩
  have si₁₄ : s₁₄.gpr .esi = dp s₀ + BitVec.ofNat 32 c := by
    rw [g₁₄ _ (by decide), g₇ _ (by decide) (by decide), tg _ (by decide), hptr.esi]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    refine WP.block_nil ⟨{ hC₁₄ with c_le := by omega, repr := fun h0 d hd => ?_ }, ⟨si₁₄, di₁₄⟩, hcnt₁₄⟩
    exact reprR_congr hP hst₁₄ (hI.repr h0 d hd)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (copy_ok hP hp (c := c) (r := r) (k := a) (by omega) (by omega) (by omega) rd₁₄ wr₁₄
      si₁₄ dx₁₄ (by rw [f₁₄.gpr, u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr,
        u₉.other _ (by decide), u₈.other _ (by decide), cx₇]) hfr₁₄
      (fun h0 d hd => reprR_congr hP hst₁₄ (hI.repr h0 d hd)))
      fun s₁₅ ⟨g₁₅, si₁₅, rd₁₅, wr₁₅, f₁₅, rp₁₅⟩ => ?_
    refine ⟨⟨⟨by omega, rd₁₅, wr₁₅, ?_, ?_, ?_, frame_st hfr₁₄ f₁₅, Saved.st hp hsv₁₄ f₁₅⟩, rp₁₅⟩,
      ⟨si₁₅, ?_⟩, Cnt.st hp hcnt₁₄ f₁₅⟩
    · rw [g₁₅ _ (by decide) (by decide) (by decide) (by decide)]; exact hC₁₄.ebx
    · rw [g₁₅ _ (by decide) (by decide) (by decide) (by decide)]; exact hC₁₄.ebp
    · rw [g₁₅ _ (by decide) (by decide) (by decide) (by decide)]; exact hC₁₄.esp
    · rw [g₁₅ _ (by decide) (by decide) (by decide) (by decide)]; exact di₁₄

/-! ## Calling the compression function -/

/-- A call of the compression function on the (full) buffer or on blocks of
data, without the final block flag. -/
theorem call_upd (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) {s : State} {blk tlo thi : BitVec 32} {k : Nat}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hesp : s.gpr .esp = esp₀ s₀) (hS : s.gpr .ebx = st s₀)
    (hC : s.gpr .ebp = scr s₀) (hB : s.gpr .esi = blk) (hk : (s.gpr .edi).toNat = k)
    (hlo : s.gpr .ecx = tlo) (hhi : s.gpr .edx = thi) (hl : s.gpr .eax = 0)
    (hsrc : (blk = st s₀ + BitVec.ofNat 32 (bufOff w) ∧ k = 1) ∨
      ∃ c₀, blk = dp s₀ + BitVec.ofNat 32 c₀ ∧ c₀ + blockBytes w * k ≤ len s₀ ∧ 0 < k)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨stA s₀, bufOff w⟩, ⟨scA s₀, 512⟩, stkR s₀] s.mem s'.mem →
      stateAt w s'.mem (stA s₀) =
        compressBlocks P (stateAt w s.mem (stA s₀)) s.mem (blk.setWidth 64) k (thi ++ tlo).toNat false →
      Q s') :
    WP isa (compressCall name code) s Q := by
  have hl' := hP.len
  have fS := hp.st_fit; have fD := hp.d_fit; have fC := hp.scr_fit
  have hN := hP.N
  have eN : Region.Sub ⟨stA s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨scA s₀, 512⟩ (scR s₀) := Region.sub_prefix (by omega)
  -- Where the blocks are.
  have hblk : blk.toNat + blockBytes w * k ≤ 2 ^ 32 ∧
      (Region.Sub ⟨blk.setWidth 64, blockBytes w * k⟩ (stR s₀ w) ∧
        Region.Disjoint ⟨blk.setWidth 64, blockBytes w * k⟩ ⟨stA s₀, bufOff w⟩ ∨
       Region.Sub ⟨blk.setWidth 64, blockBytes w * k⟩ (dR s₀)) ∧
      ∃ r ∈ s₀.rd ++ s₀.wr, ∃ o, (blk.setWidth 64) = r.base + BitVec.ofNat 64 o ∧
        o + blockBytes w * k ≤ r.len := by
    rcases hsrc with ⟨rfl, rfl⟩ | ⟨c₀, rfl, hc₀, hk0⟩
    · have e := sw_add (x := st s₀) (c := bufOff w) (by omega)
      refine ⟨by rw [toNat_add_ofNat (by omega)]; omega, .inl ⟨by rw [e]; exact sub_offset (by omega) (by omega),
        by rw [e]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)⟩, stR s₀ w, by simp [hp.wr],
        bufOff w, e, by simp only; omega⟩
    · have hB1 : blockBytes w ≤ blockBytes w * k := Nat.le_mul_of_pos_right _ hk0
      have e := sw_add (x := dp s₀) (c := c₀) (by have := hP.pos; omega)
      refine ⟨by rw [toNat_add_ofNat (by have := hP.pos; omega)]; omega,
        .inr (by rw [e]; exact sub_offset (by omega) (by omega)), dR s₀, by simp [hp.rd], c₀, e, hc₀⟩
  obtain ⟨f₁, hsub, r₀, hr₀, o₀, ho₀, hl₀⟩ := hblk
  have dS : (stkR s₀).Disjoint ⟨stA s₀, bufOff w⟩ := hp.stk_st.sub_right eN
  have dC : (stkR s₀).Disjoint ⟨scA s₀, 512⟩ := hp.stk_scr.sub_right eso
  refine call_ok (P := P) hf hesp hS hC hB hk hlo hhi hl hp.sp_lo (by omega) f₁ (by omega)
    ((hp.st_scr.sub_left eN).sub_right eso) ?_ ?_ dS dC ?_ ?_ ?_
    fun s' rd' wr' cs' f' post => hQ s' rd' wr' cs' f' (by rw [post]; rfl)
  · rcases hsub with ⟨_, h⟩ | h
    · exact h
    · exact (hp.d_st.sub_left h).sub_right eN
  · rcases hsub with ⟨h, _⟩ | h
    · exact (hp.st_scr.sub_left h).sub_right eso
    · exact (hp.d_scr.sub_left h).sub_right eso
  · rcases hsub with ⟨h, _⟩ | h
    · exact hp.stk_st.sub_right h
    · exact hp.stk_d.sub_right h
  · rw [hrd, hwr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨r₀, hr₀, o₀, ho₀, hl₀⟩
  · rw [hwr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩

/-- A call keeps what holds throughout. -/
theorem Common.after_call (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} {s s' : State}
    (h : Common w s₀ c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame [⟨stA s₀, bufOff w⟩, ⟨scA s₀, 512⟩, stkR s₀] s.mem s'.mem) :
    Common w s₀ c s' := by
  have hl := hP.len
  have hf' : Frame (⟨scA s₀, 512⟩ :: [stR s₀ w, stkR s₀]) s.mem s'.mem := hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀ w, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨scA s₀, 512⟩, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  exact ⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, by rw [hcs _ (by decide)]; exact h.ebx,
    by rw [hcs _ (by decide)]; exact h.ebp, by rw [hcs _ (by decide)]; exact h.esp,
    h.frame.trans (hf'.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨stR s₀ w, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩),
    Saved.keep hp.scr_fit h.saved hf' hp.scr_disj⟩

/-- A word of the scratch space from offset 512 on is kept by a call. -/
theorem keep_call {s₀ : State} (hp : Pre w s₀) {m m' : Mem}
    (hf : Frame [⟨stA s₀, bufOff w⟩, ⟨scA s₀, 512⟩, stkR s₀] m m') {d : Nat} (h₁ : 512 ≤ d) (h₂ : d + 4 ≤ 576) :
    m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
  refine keep_hi hp.scr_fit (rs := [stR s₀ w, stkR s₀]) (hf.sub fun r hr => ?_) hp.scr_disj h₁ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨stR s₀ w, by simp, Region.sub_prefix (by have := hp.st_fit; omega)⟩
  · exact ⟨⟨scA s₀, 512⟩, by simp, fun _ h => h⟩
  · exact ⟨stkR s₀, by simp, fun _ h => h⟩

theorem compressBlocks_one (h : HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    compressBlocks P h m p 1 t f = F P h (blockAt w m p) t f := by
  rw [compressBlocks_succ, compressBlocks_zero]; simp

/-! ## Compressing the full buffer -/

theorem compressBuf_ok (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) {c : Nat} {s : State} (hI : Inv P s₀ c (blockBytes w) s) (hptr : Ptr s₀ c s)
    (hcnt : Cnt s₀ c s.mem) :
    WP isa (compressBuf w name code) s fun s' => Inv P s₀ c 0 s' ∧ Ptr s₀ c s' ∧ Cnt s₀ c s'.mem := by
  have hl := hP.len
  unfold compressBuf
  have bp := hI.ebp
  refine WP.seq (wp_stm (o := dataOff) bp (hp.sin hI.wr (by decide)) fun s₁ u₁ => ?_)
  refine wp_stm (o := lenOff) (by rw [u₁.gpr, bp]) (by rw [u₁.wr]; exact hp.sin hI.wr (by decide))
    fun s₂ u₂ => ?_
  refine wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_movi fun s₅ u₅ => ?_
  have g₅ : ∀ x, x ≠ .esi → x ≠ .edi → s₅.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₅.other x h2, u₄.other x h1, u₃.other x h1, u₂.gpr, u₁.gpr]
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  have m₂ : s₂.mem = (s.mem.writeW (addr (scr s₀) dataOff) (s.gpr .esi)).writeW (addr (scr s₀) lenOff)
      (s.gpr .edi) := by rw [u₂.mem, u₁.mem, u₁.gpr]
  have m₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have bp₅ : s₅.gpr .ebp = scr s₀ := by rw [g₅ _ (by decide) (by decide), bp]
  refine wp_ldm bp₅ (hp.sinr rd₅ wr₅ (d := cloOff) (by decide)) fun s₆ u₆ => ?_
  have ichi := hp.sinr rd₅ wr₅ (d := chiOff) (by decide)
  refine wp_ldm (by rw [u₆.other _ (by decide), bp₅]) (by rw [u₆.rd, u₆.wr]; exact ichi) fun s₇ u₇ => ?_
  refine wp_movi fun s₈ u₈ => WP.block_nil ?_
  have g₈ : ∀ x, x ≠ .esi → x ≠ .edi → x ≠ .ecx → x ≠ .edx → x ≠ .eax → s₈.gpr x = s.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [u₈.other x h5, u₇.other x h4, u₆.other x h3, g₅ x h1 h2]
  have m₈ : s₈.mem = s₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, m₅]
  -- The memory before the call: only the two words of the scratch space differ.
  have fr₂ : Frame [scR s₀] s.mem s₂.mem := by
    rw [m₂]; exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hp.scr_in (by decide))).writeW
      (List.mem_singleton_self _) _ (hp.scr_in (by decide))
  have rd₂ : s₂.mem.readW (addr (scr s₀) cloOff) 32 = s.mem.readW (addr (scr s₀) cloOff) 32 := by
    rw [m₂, rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide),
      rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide)]
  have rd₂' : s₂.mem.readW (addr (scr s₀) chiOff) 32 = s.mem.readW (addr (scr s₀) chiOff) 32 := by
    rw [m₂, rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide),
      rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide)]
  refine WP.seq (call_upd hP hf hp (blk := st s₀ + BitVec.ofNat 32 (bufOff w)) (k := 1)
    (tlo := BitVec.ofNat 32 (cnt s₀ + c)) (thi := BitVec.ofNat 32 ((cnt s₀ + c) / 2 ^ 32))
    (by rw [u₈.rd, u₇.rd, u₆.rd, rd₅]) (by rw [u₈.wr, u₇.wr, u₆.wr, wr₅])
    (by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.esp])
    (by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.ebx])
    (by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), bp])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hI.ebx, N_eq])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]; rfl)
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, m₅, rd₂, hcnt.lo])
    (by rw [u₈.other _ (by decide), u₇.gpr, u₆.mem, m₅, rd₂', hcnt.hi]) u₈.gpr (.inl ⟨rfl, rfl⟩)
    fun s' rd' wr' cs' f' post => ?_)
  have sv₂ := Saved.write hp (Saved.write hp hI.saved (d := dataOff) (by decide) (by decide) (s.gpr .esi))
    (d := lenOff) (by decide) (by decide) (s.gpr .edi)
  have hC₈ : Common w s₀ c s₈ :=
    ⟨hI.c_le, by rw [u₈.rd, u₇.rd, u₆.rd, rd₅], by rw [u₈.wr, u₇.wr, u₆.wr, wr₅],
      by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.ebx],
      by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), bp],
      by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.esp],
      by rw [m₈, m₂]; exact frame_scr hp (frame_scr hp hI.frame (by decide) _) (by decide) _,
      by rw [m₈, m₂]; exact sv₂⟩
  have hC' : Common w s₀ c s' := hC₈.after_call hP hp rd' wr' cs' f'
  have kc : ∀ d, 512 ≤ d → d + 4 ≤ 576 → s'.mem.readW (addr (scr s₀) d) 32 = s₈.mem.readW (addr (scr s₀) d) 32 :=
    fun _ h₁ h₂ => keep_call hp f' h₁ h₂
  refine wp_ldm (b := .ebp) hC'.ebp (hp.sinr hC'.rd hC'.wr (d := dataOff) (by decide)) fun s₉ u₉ => ?_
  have ilen := hp.sinr hC'.rd hC'.wr (d := lenOff) (by decide)
  refine wp_ldm (b := .ebp) (by rw [u₉.other _ (by decide), hC'.ebp]) (by rw [u₉.rd, u₉.wr]; exact ilen)
    fun s₁₀ u₁₀ => WP.block_nil ?_
  have g₁₀ : ∀ x, x ≠ .esi → x ≠ .edi → s₁₀.gpr x = s'.gpr x := fun x h1 h2 => by
    rw [u₁₀.other x h2, u₉.other x h1]
  have m₁₀ : s₁₀.mem = s'.mem := by rw [u₁₀.mem, u₉.mem]
  have hC₁₀ : Common w s₀ c s₁₀ := hC'.of_gpr (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁₀ _ (by decide) (by decide)) m₁₀
    (by rw [u₁₀.rd, u₉.rd]) (by rw [u₁₀.wr, u₉.wr])
  refine ⟨{ hC₁₀ with repr := fun h0 d hd => ?_ }, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have hcn := hd.cnt_eq
    have hlt := hd.2.2
    have hc := hI.c_le
    rw [m₁₀]
    refine reprR_flush P hP.pos (mem := s₂.mem) (reprR_congr hP (st_keep hP hp fr₂) (hI.repr h0 d hd)) ?_
    rw [post, m₈, compressBlocks_one, sw_add (by have := hp.st_fit; have := hP.pos; omega), append_ofNat (by omega),
      List.length_append, D_length, ← hcn]
  · rw [u₁₀.other _ (by decide), u₉.gpr, kc dataOff (by decide) (by decide), m₈, m₂,
      rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, hptr.esi]
  · rw [u₁₀.gpr, u₉.mem, kc lenOff (by decide) (by decide), m₈, m₂, Mem.readW_writeW_self32, hptr.edi]
  · rw [m₁₀, kc cloOff (by decide) (by decide), m₈, rd₂, hcnt.lo]
  · rw [m₁₀, kc chiOff (by decide) (by decide), m₈, rd₂', hcnt.hi]

/-! ## `head`: filling the buffer -/

/-- After `head`: all the data is in, with the buffer not empty, or the
buffer is empty and data is left. -/
def HeadPost (P : Params w) (s₀ : State) (s : State) : Prop :=
  ∃ c r, Inv P s₀ c r s ∧ Ptr s₀ c s ∧ Cnt s₀ c s.mem ∧ ((c = len s₀ ∧ 1 ≤ r) ∨ (c < len s₀ ∧ r = 0))

theorem head_ok (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) {r : Nat} (hr : r ≤ blockBytes w) (hl : 0 < len s₀) {s : State} (hI : Inv P s₀ 0 r s)
    (hptr : Ptr s₀ 0 s) (hcnt : Cnt s₀ 0 s.mem) (hax : s.gpr .eax = BitVec.ofNat 32 r) :
    WP isa (head w name code) s (HeadPost P s₀) := by
  have hL := len_lt s₀
  have hl' := hP.len
  unfold head
  refine WP.seq (wp_test fun s₁ f₁ z₁ => WP.block_nil ?_)
  have hI₁ := hI.of_gpr (fun r _ => by rw [f₁.gpr]) f₁.mem f₁.rd f₁.wr
  have hptr₁ := hptr.of_gpr (by rw [f₁.gpr]) (by rw [f₁.gpr])
  have hz : isa.eval .e s₁ = some (decide (r = 0)) := by
    show s₁.zf = _
    rw [z₁, hax, BitVec.and_self, ofNat_beq_zero (by omega)]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact WP.block_nil ⟨0, 0, hI₁, hptr₁, by rw [f₁.mem]; exact hcnt, .inr ⟨hl, rfl⟩⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (WP.mono (fill_ok hP hp hr hI₁ hptr₁ (by rw [f₁.mem]; exact hcnt) (by rw [f₁.gpr]; exact hax))
      fun s₂ ⟨hI₂, hptr₂, hcnt₂⟩ => ?_)
    rw [Nat.zero_add, Nat.sub_zero] at hI₂ hptr₂ hcnt₂
    refine WP.seq (wp_test fun s₃ f₃ z₃ => WP.block_nil ?_)
    have hI₃ := hI₂.of_gpr (fun r _ => by rw [f₃.gpr]) f₃.mem f₃.rd f₃.wr
    have hptr₃ := hptr₂.of_gpr (by rw [f₃.gpr]) (by rw [f₃.gpr])
    have hcnt₃ : Cnt s₀ (min (blockBytes w - r) (len s₀)) s₃.mem := by rw [f₃.mem]; exact hcnt₂
    have hz₃ : isa.eval .e s₃ = some (decide (len s₀ - min (blockBytes w - r) (len s₀) = 0)) := by
      show s₃.zf = _
      rw [z₃, hptr₂.edi, BitVec.and_self, ofNat_beq_zero (by omega)]
    refine WP.ite _ hz₃ (fun hb' => ?_) (fun hb' => ?_)
    · simp only [decide_eq_true_eq] at hb'
      exact WP.block_nil ⟨_, _, hI₃, hptr₃, hcnt₃, .inl ⟨by omega, by omega⟩⟩
    · simp only [decide_eq_false_iff_not] at hb'
      have e : r + min (blockBytes w - r) (len s₀) = blockBytes w := by omega
      rw [e] at hI₃
      exact WP.mono (compressBuf_ok hP hf hp hI₃ hptr₃ hcnt₃) fun s₄ ⟨hI₄, hptr₄, hcnt₄⟩ =>
        ⟨_, _, hI₄, hptr₄, hcnt₄, .inr ⟨by omega, rfl⟩⟩

/-! ## `rest`: whole blocks straight from the data, and the last block -/

theorem ok_lg (hP : Ok P) : 1 ≤ Nat.log2 (B w) ∧ Nat.log2 (B w) ≤ 31 ∧ 2 ^ Nat.log2 (B w) = blockBytes w := by
  rw [B_eq]
  rcases hP.bb with h | h <;> rw [h]
  · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
  · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide

theorem shr_ofNat (hP : Ok P) {m : Nat} (h : m < 2 ^ 32) :
    BitVec.ofNat 32 m >>> Nat.log2 (B w) = BitVec.ofNat 32 (m / blockBytes w) := by
  obtain ⟨-, -, lgB⟩ := ok_lg hP
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow, lgB]

/-- The blocks of data but the last, straight from the data. -/
theorem direct_ok (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) {c : Nat} (hc : c < len s₀) {s : State} (hI : Inv P s₀ c 0 s) (hptr : Ptr s₀ c s)
    (hcnt : Cnt s₀ c s.mem) :
    WP isa (direct w name code) s fun s' =>
      Inv P s₀ (c + blockBytes w * ((len s₀ - c - 1) / blockBytes w)) 0 s' ∧
      Ptr s₀ (c + blockBytes w * ((len s₀ - c - 1) / blockBytes w)) s' := by
  have hl := hP.len
  have hL := len_lt s₀
  have hpos := hP.pos
  obtain ⟨lg₁, lg₂, -⟩ := ok_lg hP
  obtain ⟨k, hk⟩ : ∃ k, k = (len s₀ - c - 1) / blockBytes w := ⟨_, rfl⟩
  rw [← hk]
  have hdm := Nat.div_add_mod (len s₀ - c - 1) (blockBytes w)
  have hmod := Nat.mod_lt (len s₀ - c - 1) hpos
  rw [← hk] at hdm
  have hBk : blockBytes w * k ≤ len s₀ - c - 1 := by omega
  have hkle : k ≤ len s₀ - c - 1 := hk ▸ Nat.div_le_self _ _
  unfold direct
  refine WP.seq (wp_mov fun s₁ u₁ => wp_subi fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ => wp_andi fun s₄ u₄ =>
    wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_)
  have hL1 : s₂.gpr .eax = BitVec.ofNat 32 (len s₀ - c - 1) := by
    rw [u₂.gpr, u₁.gpr, hptr.edi, ofNat_pred (by omega)]
  have hcx₄ : s₄.gpr .ecx = BitVec.ofNat 32 ((len s₀ - c - 1) % blockBytes w) := by
    rw [u₄.gpr, u₃.gpr, hL1, and_mask hP, toNat_ofNat_lt (by omega)]
  have hax₅ : s₅.gpr .eax = BitVec.ofNat 32 (blockBytes w * k) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), hL1, hcx₄, sub_ofNat (by omega)]
    exact congrArg _ (by omega)
  have g₅ : ∀ x, x ≠ .eax → x ≠ .ecx → s₅.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₅.other x h1, u₄.other x h2, u₃.other x h2, u₂.other x h1, u₁.other x h1]
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  have hz : isa.eval .e s₅ = some (decide (k = 0)) := by
    show s₅.zf = _
    rw [z₅, u₄.other _ (by decide), u₃.other _ (by decide), hL1, hcx₄, sub_ofNat (by omega),
      ofNat_beq_zero (by omega)]
    have : len s₀ - c - 1 - (len s₀ - c - 1) % blockBytes w = blockBytes w * k := by omega
    rw [this]
    simp only [Nat.mul_eq_zero, Nat.ne_of_gt hpos, false_or]
  have hcom : ∀ r ∈ [Reg.ebx, .ebp, .esp], s₅.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide)
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    rw [Nat.mul_zero, Nat.add_zero]
    exact WP.block_nil ⟨hI.of_gpr hcom m₅ (by rw [rd₅, hI.rd]) (by rw [wr₅, hI.wr]),
      hptr.of_gpr (g₅ _ (by decide) (by decide)) (g₅ _ (by decide) (by decide))⟩
  simp only [decide_eq_false_iff_not] at hb
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hb
  have hB1 : blockBytes w ≤ blockBytes w * k := Nat.le_mul_of_pos_right _ hk1
  have bp₅ : s₅.gpr .ebp = scr s₀ := by rw [g₅ _ (by decide) (by decide), hI.ebp]
  refine WP.seq (wp_stm (o := lenOff) bp₅ (hp.sin wr₅ (by decide)) fun s₆ u₆ => ?_)
  refine wp_stm (o := bytesOff) (by rw [u₆.gpr, bp₅]) (by rw [u₆.wr]; exact hp.sin wr₅ (by decide))
    fun s₇ u₇ => ?_
  refine wp_mov fun s₈ u₈ => wp_shr ⟨lg₁, lg₂⟩ fun s₉ u₉ _ => ?_
  have bp₉ : s₉.gpr .ebp = scr s₀ := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, bp₅]
  have rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅]
  have wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]
  have m₉ : s₉.mem = (s.mem.writeW (addr (scr s₀) lenOff) (s₅.gpr .edi)).writeW (addr (scr s₀) bytesOff)
      (BitVec.ofNat 32 (blockBytes w * k)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.gpr, u₆.mem, hax₅, m₅]
  have rdlo : s₉.mem.readW (addr (scr s₀) cloOff) 32 = BitVec.ofNat 32 (cnt s₀ + c) := by
    rw [m₉, rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide),
      rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), hcnt.lo]
  have rdhi : s₉.mem.readW (addr (scr s₀) chiOff) 32 = BitVec.ofNat 32 ((cnt s₀ + c) / 2 ^ 32) := by
    rw [m₉, rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide),
      rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), hcnt.hi]
  refine wp_ldmF bp₉ (hp.sinr rd₉ wr₉ (d := cloOff) (by decide)) fun s₁₀ u₁₀ _ _ => ?_
  refine wp_addiC fun s₁₁ u₁₁ cf₁₁ => ?_
  have ichi := hp.sinr rd₉ wr₉ (d := chiOff) (by decide)
  refine wp_ldmF (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), bp₉])
    (by rw [u₁₁.rd, u₁₁.wr, u₁₀.rd, u₁₀.wr]; exact ichi) fun s₁₂ u₁₂ cf₁₂ _ => ?_
  refine wp_adc0 (by rw [cf₁₂, cf₁₁]) fun s₁₃ u₁₃ => wp_movi fun s₁₄ u₁₄ => WP.block_nil ?_
  have g₁₄ : ∀ x, x ≠ .eax → x ≠ .ecx → x ≠ .edx → x ≠ .edi → s₁₄.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [u₁₄.other x h1, u₁₃.other x h3, u₁₂.other x h3, u₁₁.other x h2, u₁₀.other x h2, u₉.other x h4,
      u₈.other x h4, u₇.gpr, u₆.gpr, g₅ x h1 h2]
  have m₁₄ : s₁₄.mem = s₉.mem := by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem]
  have lo₁₁ : s₁₁.gpr .ecx = BitVec.ofNat 32 (cnt s₀ + c + blockBytes w) := by
    rw [u₁₁.gpr, u₁₀.gpr, rdlo, B_eq, ← BitVec.ofNat_add]
  have sv₉ := Saved.write hp (Saved.write hp hI.saved (d := lenOff) (by decide) (by decide) (s₅.gpr .edi))
    (d := bytesOff) (by decide) (by decide) (BitVec.ofNat 32 (blockBytes w * k))
  have hC₁₄ : Common w s₀ c s₁₄ :=
    ⟨hI.c_le, by rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, rd₉],
      by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, wr₉],
      by rw [g₁₄ _ (by decide) (by decide) (by decide) (by decide), hI.ebx],
      by rw [g₁₄ _ (by decide) (by decide) (by decide) (by decide), hI.ebp],
      by rw [g₁₄ _ (by decide) (by decide) (by decide) (by decide), hI.esp],
      by rw [m₁₄, m₉]; exact frame_scr hp (frame_scr hp hI.frame (by decide) _) (by decide) _,
      by rw [m₁₄, m₉]; exact sv₉⟩
  have hdi₁₄ : s₁₄.gpr .edi = BitVec.ofNat 32 k := by
    rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.gpr, u₆.gpr, hax₅, shr_ofNat hP (by omega),
      Nat.mul_div_cancel_left _ hpos]
  have hdx₁₄ : s₁₄.gpr .edx = BitVec.ofNat 32 ((cnt s₀ + c + blockBytes w) / 2 ^ 32) := by
    rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.gpr, u₁₁.mem, u₁₀.mem, rdhi, u₁₀.gpr, rdlo, B_eq,
      carry_ofNat _ _ (by omega)]
  refine WP.seq (call_upd hP hf hp (blk := dp s₀ + BitVec.ofNat 32 c) (k := k)
    (tlo := BitVec.ofNat 32 (cnt s₀ + c + blockBytes w))
    (thi := BitVec.ofNat 32 ((cnt s₀ + c + blockBytes w) / 2 ^ 32)) hC₁₄.rd hC₁₄.wr hC₁₄.esp hC₁₄.ebx hC₁₄.ebp
    (by rw [g₁₄ _ (by decide) (by decide) (by decide) (by decide), hptr.esi])
    (by rw [hdi₁₄, toNat_ofNat_lt (by omega)])
    (by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), lo₁₁]) hdx₁₄
    u₁₄.gpr (.inr ⟨c, rfl, by omega, hk1⟩) fun s' rd' wr' cs' f' post => ?_)
  have hC' : Common w s₀ c s' := hC₁₄.after_call hP hp rd' wr' cs' f'
  have kc : ∀ d, 512 ≤ d → d + 4 ≤ 576 → s'.mem.readW (addr (scr s₀) d) 32 = s₁₄.mem.readW (addr (scr s₀) d) 32 :=
    fun _ h₁ h₂ => keep_call hp f' h₁ h₂
  refine wp_ldm (b := .ebp) hC'.ebp (hp.sinr hC'.rd hC'.wr (d := bytesOff) (by decide)) fun s₁₅ u₁₅ => ?_
  refine wp_add fun s₁₆ u₁₆ _ => ?_
  have ilen := hp.sinr hC'.rd hC'.wr (d := lenOff) (by decide)
  refine wp_ldm (b := .ebp) (by rw [u₁₆.other _ (by decide), u₁₅.other _ (by decide), hC'.ebp])
    (by rw [u₁₆.rd, u₁₆.wr, u₁₅.rd, u₁₅.wr]; exact ilen) fun s₁₇ u₁₇ => ?_
  refine wp_sub fun s₁₈ u₁₈ _ => WP.block_nil ?_
  have ax₁₅ : s₁₅.gpr .eax = BitVec.ofNat 32 (blockBytes w * k) := by
    rw [u₁₅.gpr, kc bytesOff (by decide) (by decide), m₁₄, m₉, Mem.readW_writeW_self32]
  have g₁₈ : ∀ x, x ≠ .eax → x ≠ .esi → x ≠ .edi → s₁₈.gpr x = s'.gpr x := fun x h1 h2 h3 => by
    rw [u₁₈.other x h3, u₁₇.other x h3, u₁₆.other x h2, u₁₅.other x h1]
  have m₁₈ : s₁₈.mem = s'.mem := by rw [u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem]
  have hC₁₈ : Common w s₀ c s₁₈ := hC'.of_gpr (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁₈ _ (by decide) (by decide) (by decide)) m₁₈
    (by rw [u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd]) (by rw [u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr])
  refine ⟨⟨{ hC₁₈ with c_le := by omega }, fun h0 d hd => ?_⟩, ⟨?_, ?_⟩⟩
  · have hcn := hd.cnt_eq
    have hlt := hd.2.2
    have hst : ∀ i < bufOff w + blockBytes w,
        s₁₄.mem (stA s₀ + BitVec.ofNat 64 i) = s.mem (stA s₀ + BitVec.ofNat 64 i) := by
      refine st_keep hP hp ?_
      rw [m₁₄, m₉]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hp.scr_in (by decide))).writeW
        (List.mem_singleton_self _) _ (hp.scr_in (by decide))
    have e : d ++ D s₀ (c + blockBytes w * k) =
        d ++ D s₀ c ++ bytesAt s₁₄.mem (dA s₀ + BitVec.ofNat 64 c) (blockBytes w * k) := by
      rw [D, bytesAt_add, List.append_assoc]
      refine congrArg (fun l => d ++ (bytesAt s₀.mem (dA s₀) c ++ l)) (bytesAt_congr fun i hi => ?_)
      rw [Offset.add_add]
      exact (hC₁₄.data hp (by omega)).symm
    rw [m₁₈, e]
    refine reprR_blocks P hpos (reprR_congr hP hst (hI.repr h0 d hd)) ?_
    rw [post, dp_add hp hc, append_ofNat (by omega), List.length_append, D_length, ← hcn]
  · rw [u₁₈.other _ (by decide), u₁₇.other _ (by decide), u₁₆.gpr, u₁₅.other _ (by decide), ax₁₅,
      cs' _ (by decide), g₁₄ _ (by decide) (by decide) (by decide) (by decide), hptr.esi, BitVec.add_assoc,
      BitVec.ofNat_add]
  · rw [u₁₈.gpr, u₁₇.gpr, u₁₇.other .eax (by decide), u₁₆.other .eax (by decide), ax₁₅, u₁₆.mem, u₁₅.mem,
      kc lenOff (by decide) (by decide),
      m₁₄, m₉, rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32,
      g₅ _ (by decide) (by decide), hptr.edi, sub_ofNat (by omega)]
    exact congrArg _ (by omega)

/-- The last `1` to `B` bytes of data, into the empty buffer. -/
theorem tail_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} (hc₁ : c < len s₀)
    (hc₂ : len s₀ - c ≤ blockBytes w) {s : State} (hI : Inv P s₀ c 0 s) (hptr : Ptr s₀ c s) :
    WP isa (tail w) s (Inv P s₀ (len s₀) (len s₀ - c)) := by
  have hL := len_lt s₀
  unfold tail
  refine WP.seq (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil ?_)
  have hg : ∀ x, x ≠ .ecx → x ≠ .edx → s₂.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₂.other x h2, u₁.other x h1]
  have hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine WP.mono (copy_ok hP hp (c := c) (r := 0) (k := len s₀ - c) (by omega) (by omega) (by omega)
      (by rw [u₂.rd, u₁.rd, hI.rd]) (by rw [u₂.wr, u₁.wr, hI.wr])
      (by rw [hg _ (by decide) (by decide)]; exact hptr.esi)
      (by rw [u₂.gpr, u₁.other _ (by decide), hI.ebx]; simp)
      (by rw [u₂.other _ (by decide), u₁.gpr, hptr.edi])
      (by rw [hm₂]; exact hI.frame) (by rw [hm₂]; exact hI.repr))
    fun s₃ ⟨g₃, _, rd₃, wr₃, f₃, rp₃⟩ => ?_
  have e : c + (len s₀ - c) = len s₀ := by omega
  rw [e, Nat.zero_add] at rp₃
  have g : ∀ x, x ≠ .esi → x ≠ .edx → x ≠ .ecx → x ≠ .eax → s₃.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [g₃ x h1 h2 h3 h4, hg x h3 h2]
  refine ⟨⟨Nat.le_refl _, rd₃, wr₃, ?_, ?_, ?_, ?_, ?_⟩, rp₃⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact hI.ebx
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact hI.ebp
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact hI.esp
  · exact frame_st hI.frame (by rw [← hm₂]; exact f₃)
  · exact Saved.st hp hI.saved (by rw [← hm₂]; exact f₃)

/-- All the data is in, and the buffer is not empty. -/
def Full (P : Params w) (s₀ : State) (s : State) : Prop := ∃ r, Inv P s₀ (len s₀) r s ∧ 1 ≤ r

theorem rest_ok (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) {s : State} (h : HeadPost P s₀ s) : WP isa (rest w name code) s (Full P s₀) := by
  have hL := len_lt s₀
  have hpos := hP.pos
  obtain ⟨c, r, hI, hptr, hcnt, hcr⟩ := h
  unfold rest
  refine WP.seq (wp_test fun s₁ f₁ z₁ => WP.block_nil ?_)
  have hI₁ := hI.of_gpr (fun r _ => by rw [f₁.gpr]) f₁.mem f₁.rd f₁.wr
  have hptr₁ := hptr.of_gpr (by rw [f₁.gpr]) (by rw [f₁.gpr])
  have hz : isa.eval .e s₁ = some (decide (len s₀ - c = 0)) := by
    show s₁.zf = _
    rw [z₁, hptr.edi, BitVec.and_self, ofNat_beq_zero (by omega)]
  have hc := hI.c_le
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', _⟩
    · exact WP.block_nil ⟨r, hI₁, hr⟩
    · omega
  · simp only [decide_eq_false_iff_not] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', rfl⟩
    · omega
    refine WP.seq (WP.mono (direct_ok hP hf hp hc' hI₁ hptr₁ (by rw [f₁.mem]; exact hcnt))
      fun s₂ ⟨hI₂, hptr₂⟩ => ?_)
    have hdm := Nat.div_add_mod (len s₀ - c - 1) (blockBytes w)
    have hmod := Nat.mod_lt (len s₀ - c - 1) hpos
    exact WP.mono (tail_ok hP hp (by omega) (by omega) hI₂ hptr₂) fun s₃ hI₃ => ⟨_, hI₃, by omega⟩

/-! ## Epilogue and the whole function -/

/-- All the data is in. -/
def Done (P : Params w) (s₀ : State) (s : State) : Prop :=
  Common w s₀ (len s₀) s ∧
    ∀ h0 d, R₀ P s₀ h0 d → Spec.Blake2.Repr P h0 s.mem (stA s₀) (d ++ D s₀ (len s₀))

theorem Full.done (hP : Ok P) {s₀ : State} {s : State} (h : Full P s₀ s) : Done P s₀ s := by
  obtain ⟨r, hI, hr⟩ := h
  exact ⟨hI.toCommon, fun h0 d hd => repr_of_reprR P hP.pos (hI.repr h0 d hd) hr⟩

theorem epilogue_ok {s₀ : State} (hp : Pre w s₀) {s : State} (hD : Done P s₀ s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ (updateX86 P).post s₀ s' := by
  obtain ⟨hC, hrepr⟩ := hD
  refine WP.mono (restore_saved hC.ebp (fun d _ hd => hp.sinr hC.rd hC.wr (by omega)) hC.saved)
    fun s₅ ⟨hg, hsp, hm₅⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun h0 d hd hc hl => ?_⟩
  · by_cases h : r = .esp
    · subst h; rw [hsp, hC.esp]
    · exact hg r hr h
  · rw [hm₅]
    refine hC.frame.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.ret_st, hp.ret_scr, hp.ret_stk]
  · rw [hm₅]; exact hrepr h0 d ⟨hd, hc, hl⟩

theorem correct (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) :
    WP isa (update w name code) s₀ fun s' => abiPreserved s₀ s' ∧ (updateX86 P).post s₀ s' := by
  have hL := len_lt s₀
  unfold update
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hC, hptr, hm, hax, hcx⟩ => ?_)
  refine WP.seq (WP.mono (bufLen_ok hP hp hC hptr hm hax hcx) fun s₂ ⟨hI, hptr₂, hcnt₂, hax₂⟩ => ?_)
  refine WP.seq (wp_test fun s₃ f₃ z₃ => WP.block_nil ?_)
  have hI₃ := hI.of_gpr (fun r _ => by rw [f₃.gpr]) f₃.mem f₃.rd f₃.wr
  have hptr₃ := hptr₂.of_gpr (by rw [f₃.gpr]) (by rw [f₃.gpr])
  refine WP.seq (WP.mono (Q := Done P s₀) ?_ fun s₄ h => epilogue_ok hp h)
  have hz : isa.eval .e s₃ = some (decide (len s₀ = 0)) := by
    show s₃.zf = _
    rw [z₃, hptr₂.edi, BitVec.and_self, Nat.sub_zero, ofNat_beq_zero (by omega)]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.block_nil ⟨{ hI₃.toCommon with c_le := by omega }, fun h0 d hd => ?_⟩
    have := hI₃.repr h0 d hd
    have e0 : ∀ n, n = 0 → D s₀ n = [] := by rintro _ rfl; simp [bytesAt]
    rw [e0 0 rfl, List.append_nil] at this
    rw [e0 _ hb, List.append_nil, repr_iff P hP.pos, ← hd.cnt_eq]; exact this
  · simp only [decide_eq_false_iff_not] at hb
    have hr := bufLen_le (w := w) hP.pos (cnt s₀)
    exact WP.seq (WP.mono (head_ok hP hf hp hr (by omega) hI₃ hptr₃ (by rw [f₃.mem]; exact hcnt₂)
      (by rw [f₃.gpr]; exact hax₂)) fun s₄ h => WP.mono (rest_ok hP hf hp h) fun s₅ h => h.done hP)

end VG.Proof.Blake2.X86.Stream.Update
