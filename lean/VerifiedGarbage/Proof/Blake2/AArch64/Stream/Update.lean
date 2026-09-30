import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Common

/-!
# Streaming BLAKE2 on AArch64: `update`

Untrusted: everything here is checked by Lean. The functional correctness of
`update`, for either word size and any correct compression function
(`CalleeOk`). The same structure as the x86-64 proof
(`VG.Proof.Blake2.X86_64.Stream.Update`), inside the frame saving `x30`
(`WP.frameReg`).
-/

namespace VG.Proof.Blake2.AArch64.Stream.Update

open VG VG.AArch64 VG.Spec.Blake2
open VG.Impl.Blake2.AArch64.Stream (N B mov copyLoop fill compressBuf head direct tail rest updateStart
  updateMain update saved save restore)
open VG.Impl.Blake2.AArch64 (lbb compress)
open VG.Proof.MdStream.AArch64 (Upd Mupd toNat_ofNat_lt wp_mov wp_addImm wp_subImm wp_movz wp_add wp_sub
  wp_and wp_lsr ofNat_beq_zero)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)
open VG.Proof.Blake2 (ReprR bufLen_le repr_iff reprR_append reprR_flush reprR_blocks repr_of_reprR
  stateAt_congr bytesAt_congr bytesAt_add updateAArch64)

variable {w : Nat} {P : Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev cnt : Nat := (s₀.gpr .x1).toNat
abbrev dp : Addr := s₀.gpr .x2
abbrev len : Nat := (s₀.gpr .x3).toNat
abbrev scr : Addr := s₀.gpr .x4
abbrev stR (w : Nat) : Region := ⟨st s₀, bufOff w + blockBytes w⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
abbrev scR : Region := ⟨scr s₀, 576⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c
/-- The frame saving `x30`, below the stack pointer. -/
abbrev stkR : Region := ⟨s₀.sp - 16, 16⟩

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀ w, scR s₀]
  st_scr : (stR s₀ w).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀ w)
  d_scr : (dR s₀).Disjoint (scR s₀)

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (w : Nat) (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  st : (stkR s₀).Disjoint (stR s₀ w)
  d : (stkR s₀).Disjoint (dR s₀)
  scr : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : (updateAArch64 P).pre s₀) : Pre w s₀ ∧ Stack w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩⟩

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
theorem cnt_lt (s₀ : State) : cnt s₀ < 2 ^ 64 := (s₀.gpr .x1).isLt

/-- The data the initial state represents, from `h0`. -/
def R₀ (P : Params w) (s₀ : State) (h0 : HashValue w) (d : List Byte) : Prop :=
  Spec.Blake2.Repr P h0 s₀.mem (st s₀) d ∧ s₀.gpr .x1 = BitVec.ofNat 64 d.length ∧
    d.length + len s₀ < 2 ^ 64

theorem R₀.cnt_eq {s₀ : State} {h0 : HashValue w} {d : List Byte} (h : R₀ P s₀ h0 d) :
    cnt s₀ = d.length := by
  rw [Update.cnt, h.2.1, toNat_ofNat_lt (by have := h.2.2; omega)]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by simp [bytesAt]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (w : Nat) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = st s₀
  x20 : s.gpr .x20 = scr s₀
  x21 : s.gpr .x21 = dp s₀ + BitVec.ofNat 64 c
  x22 : s.gpr .x22 = BitVec.ofNat 64 (len s₀ - c)
  x24 : s.gpr .x24 = BitVec.ofNat 64 (cnt s₀ + c)
  keep : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  frame : Frame [stR s₀ w, scR s₀] s₀.mem s.mem
  saved : Saved (scr s₀) s₀.gpr s.mem

/-- The state represents the data followed by the first `c` bytes of data,
the last `r` of them in the buffer. -/
structure Inv (P : Params w) (s₀ : State) (c r : Nat) (s : State) : Prop extends Common w s₀ c s where
  x23 : s.gpr .x23 = BitVec.ofNat 64 r
  repr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (st s₀) (d ++ D s₀ c) r

/-- The registers `Common` is about. -/
abbrev commonRegs : List Reg := [.x19, .x20, .x21, .x22, .x24, .x25, .x26, .x27, .x28]

theorem notC {r : Reg} (hr : r ∈ commonRegs) (x : Reg) (hx : x ∉ commonRegs := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common w s₀ c s)
    (hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common w s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  x19 := by rw [hg _ (by simp)]; exact h.x19
  x20 := by rw [hg _ (by simp)]; exact h.x20
  x21 := by rw [hg _ (by simp)]; exact h.x21
  x22 := by rw [hg _ (by simp)]; exact h.x22
  x24 := by rw [hg _ (by simp)]; exact h.x24
  keep := fun r hr => by rw [hg r (by simp only [untouched] at hr; simp [hr])]; exact h.keep r hr
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c r : Nat} {s s' : State} (h : Inv P s₀ c r s)
    (hg : ∀ r ∈ .x23 :: commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Inv P s₀ c r s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (List.mem_cons_of_mem _ hr)) hm hrd hwr hsp with
    x23 := by rw [hg _ (by simp)]; exact h.x23
    repr := by rw [hm]; exact h.repr }

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre w s₀) {c : Nat} {s : State} (h : Common w s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩) (Nat.le_of_lt (len_lt s₀)) hi

/-- Writes to the state and the compression function's scratch space keep the
saved registers. -/
theorem saved_frame {s₀ : State} (hp : Pre w s₀) {m m' : Mem} (h : Saved (scr s₀) s₀.gpr m)
    (hf : Frame [stR s₀ w, ⟨scr s₀, 512⟩] m m') : Saved (scr s₀) s₀.gpr m' := by
  intro p hp'
  have hoff : 512 ≤ p.2 ∧ p.2 + 8 ≤ 560 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [← h p hp']
  refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  have e : Region.Sub ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := Offset.sub_base _ (by omega)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · exact hp.st_scr.symm.sub_left e
  · exact Offset.disjoint_base _ (by omega) (by omega)

/-! ## Prologue -/

theorem prologue_ok {s₀ : State} (hp : Pre w s₀) :
    WP isa (.block updateStart) s₀ fun s => Common w s₀ 0 s ∧ s.mem = saveMem s₀.mem (scr s₀) s₀.gpr := by
  refine save_ok (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => WP.block_nil ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, g₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
    simp
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
    simp
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
    simp
  · have : r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x24 := by
      simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [u₆.other _ this.2.2.2.2, u₅.other _ this.2.2.2.1, u₄.other _ this.2.2.1, u₃.other _ this.2.1,
      u₂.other _ this.1, g₁]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
    exact (saveMem_frame _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, Offset.sub_base _ (by omega)⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]; exact saveMem_saved _ _ _
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]

/-! ## The bytes in the buffer -/

theorem bufLen_ok' (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (hC : Common w s₀ 0 s)
    (hm : s.mem = saveMem s₀.mem (scr s₀) s₀.gpr) :
    WP isa (Impl.Blake2.AArch64.Stream.bufLen (w := w)) s (Inv P s₀ 0 (Blake2.bufLen w (cnt s₀))) := by
  have hN := hP.len
  have hrepr : ∀ h0 d, R₀ P s₀ h0 d →
      ReprR P h0 s.mem (st s₀) (d ++ D s₀ 0) (Blake2.bufLen w (cnt s₀)) := by
    intro h0 d hd
    have e : D s₀ 0 = [] := by simp [bytesAt]
    rw [e, List.append_nil, hd.cnt_eq, ← repr_iff P hP.pos]
    refine repr_congr hP (fun i hi => ?_) hd.1
    rw [hm]
    exact (saveMem_frame _ _ _).bytes (R := stR s₀ w)
      (by simpa using hp.st_scr.sub_right (Offset.sub_base _ (by omega))) (by simp only; omega) hi
  refine WP.mono (bufLen_ok hP) fun s' ⟨h23, g, m, rd, wr, sp⟩ => ?_
  rw [hC.x24, Nat.add_zero, toNat_ofNat_lt (cnt_lt s₀)] at h23
  exact { hC.of_gpr (fun r hr => g r (notC hr .x9) (notC hr .x23)) m rd wr sp with
    x23 := h23, repr := by rw [m]; exact hrepr }

/-! ## Copying data into the buffer -/

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = bytesAt m p r ++ xs := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, writeBytes]
    have hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j from
      Offset.add_ofNat_add_sub p r j, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]

/-- Copying `k` bytes of data, from byte `c` on, into the buffer, from byte
`r` on. -/
theorem copy_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c r k : Nat} (hk : 1 ≤ k)
    (hrk : r + k ≤ blockBytes w) (hck : c + k ≤ len s₀) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hx19 : s.gpr .x19 = st s₀)
    (hx21 : s.gpr .x21 = dp s₀ + BitVec.ofNat 64 c) (hx23 : s.gpr .x23 = BitVec.ofNat 64 r)
    (hx11 : s.gpr .x11 = BitVec.ofNat 64 k) (hf : Frame [stR s₀ w, scR s₀] s₀.mem s.mem)
    (hs : Saved (scr s₀) s₀.gpr s.mem)
    (hrepr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (st s₀) (d ++ D s₀ c) r) :
    WP isa (copyLoop (w := w)) s fun s' =>
      (∀ x, x ≠ .x9 → x ≠ .x12 → x ≠ .x21 → x ≠ .x23 → x ≠ .x11 → s'.gpr x = s.gpr x) ∧
      s'.gpr .x21 = dp s₀ + BitVec.ofNat 64 (c + k) ∧ s'.gpr .x23 = BitVec.ofNat 64 (r + k) ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s.sp ∧ Frame [stR s₀ w, scR s₀] s₀.mem s'.mem ∧
      Saved (scr s₀) s₀.gpr s'.mem ∧
      ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s'.mem (st s₀) (d ++ D s₀ (c + k)) (r + k) := by
  have hl := hP.len
  have hL := len_lt s₀
  have hsrc : ∀ i < k, InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨dR s₀, by simp [hrd, hp.rd], by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have hdst : ∀ i < k, InRegions s.wr (st s₀ + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨stR s₀ w, by simp [hwr, hp.wr], by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have hd : Region.Disjoint ⟨dp s₀ + BitVec.ofNat 64 c, k⟩ ⟨st s₀ + BitVec.ofNat 64 (bufOff w + r), k⟩ :=
    (hp.d_st.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
  refine copyLoop_ok (w := w) hP.N64 hk (by omega) hx19 hx21 hx23 hx11 hsrc hdst hd fun s' h => ?_
  -- The bytes copied.
  have hx : bytesAt s.mem (dp s₀ + BitVec.ofNat 64 c) k = bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k :=
    bytesAt_congr fun i hi => by
      rw [Offset.add_add]
      exact hf.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩)
        (Nat.le_of_lt hL) (show c + i < len s₀ by omega)
  have hm : s'.mem = writeBytes s.mem (st s₀ + BitVec.ofNat 64 (bufOff w + r))
      (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k) := by
    rw [h.mem, List.take_of_length_le (by rw [bytesAt_length]), hx]
  have hfw : Frame [stR s₀ w] s.mem s'.mem := by
    rw [hm]
    exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Offset.contains_base _ (by omega) (by omega))
  refine ⟨h.other, h.x21.trans (Offset.add_add _ _ _), h.x23, h.rd.trans hrd, h.wr.trans hwr, h.sp,
    hf.trans (hfw.mono (by simp)), saved_frame hp hs (hfw.mono (by simp)), fun h0 d hd => ?_⟩
  have e : d ++ D s₀ (c + k) = d ++ D s₀ c ++ bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k := by
    rw [D, bytesAt_add, List.append_assoc]
  rw [e]
  have := reprR_append P (hrepr h0 d hd) (x := bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k)
    (mem' := s'.mem) (by rw [bytesAt_length]; exact hrk) ?_ ?_
  · rwa [bytesAt_length] at this
  · rw [hm]
    exact stateAt_congr fun i hi => writeBytes_before _ _ _ (by omega) (by rw [bytesAt_length]; omega)
  · rw [hm, ← Offset.add_add, bytesAt_writeBytes _ _ _ _ (by rw [bytesAt_length]; omega)]

/-! ## Calling the compression function -/

/-- The blocks compressed are the (full) buffer or blocks of data. -/
def Src (w : Nat) (s₀ : State) (src : Addr) (n : Nat) : Prop :=
  (src = st s₀ + BitVec.ofNat 64 (bufOff w) ∧ n = blockBytes w) ∨
    ∃ c₀, src = dp s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + n ≤ len s₀

theorem callOk (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} {s : State} (h : Common w s₀ c s)
    {src : Addr} {n : Nat} (hsrc : Src w s₀ src n) : CallOk (w := w) s (st s₀) (scr s₀) src n := by
  have hl := hP.len; have := len_lt s₀
  have eN : Region.Sub ⟨st s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨scr s₀, 512⟩ (scR s₀) := Region.sub_prefix (by omega)
  have eSrc : Region.Sub ⟨src, n⟩ (stR s₀ w) ∨ Region.Sub ⟨src, n⟩ (dR s₀) := by
    rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · exact .inl (h' ▸ Offset.sub_base _ (by omega))
    · exact .inr (h' ▸ Offset.sub_base _ (by omega))
  refine ⟨h.x19, h.x20, (hp.st_scr.sub_left eN).sub_right eso, ?_, ?_, ?_, ?_⟩
  · rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · rw [h']; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
    · exact (hp.d_st.sub_left (h' ▸ Offset.sub_base _ (by omega))).sub_right eN
  · rcases eSrc with e | e
    · exact (hp.st_scr.sub_left e).sub_right eso
    · exact (hp.d_scr.sub_left e).sub_right eso
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
      · exact ⟨stR s₀ w, by simp, bufOff w, h', by simp⟩
      · exact ⟨dR s₀, by simp, c₀, h', hc₀⟩
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩

theorem commonRegs_preserved : ∀ r ∈ commonRegs, r ∈ preserved ∧ r ≠ .x30 := by decide

/-- A call keeps what holds throughout. -/
theorem Common.after_call (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} {s s' : State}
    (h : Common w s₀ c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r)
    (hf : Frame [⟨st s₀, bufOff w⟩, ⟨scr s₀, 512⟩] s.mem s'.mem) :
    Common w s₀ c s' := by
  have hl := hP.len
  have hf' : Frame [stR s₀ w, ⟨scr s₀, 512⟩] s.mem s'.mem := hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨scr s₀, 512⟩, by simp, fun _ h => h⟩
  have hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r := fun r hr =>
    hcs r (commonRegs_preserved r hr).1 (commonRegs_preserved r hr).2
  refine ⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, by rw [hg _ (by simp)]; exact h.x19,
    by rw [hg _ (by simp)]; exact h.x20, by rw [hg _ (by simp)]; exact h.x21,
    by rw [hg _ (by simp)]; exact h.x22, by rw [hg _ (by simp)]; exact h.x24,
    fun r hr => by rw [hg r (by simp only [untouched] at hr; simp [hr])]; exact h.keep r hr,
    h.frame.trans (hf'.sub fun r hr => ?_), saved_frame hp h.saved hf'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨stR s₀ w, by simp, fun _ h => h⟩
  · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩

theorem compressBlocks_one (h : HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    compressBlocks P h m p 1 t f = F P h (blockAt w m p) t f := by
  rw [compressBlocks_succ, compressBlocks_zero]; simp

theorem one_toNat : (BitVec.setWidth 64 (1 : BitVec 16)).toNat = 1 := rfl

/-- Compressing the full buffer. -/
theorem compressBuf_ok (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀)
    {c : Nat} {s : State} (hI : Inv P s₀ c (blockBytes w) s) :
    WP isa (compressBuf P) s (Inv P s₀ c 0) := by
  have hl := hP.len
  have hN := hP.N64
  have hc := hI.c_le
  unfold compressBuf
  refine WP.seq (compressWith_ok hf (bufArgs_ok (by omega))
    (by rw [one_toNat, Nat.mul_one]; exact callOk hP hp hI.toCommon (.inl ⟨by rw [hI.x19], rfl⟩))
    fun s' hrd hwr hsp hcs hfr hst => ?_)
  refine wp_movz fun s₂ u₂ => WP.block_nil ?_
  have hC := hI.toCommon.after_call hP hp hrd hwr hsp hcs hfr
  refine { hC.of_gpr (fun r hr => u₂.other r (notC hr .x23)) u₂.mem u₂.rd u₂.wr u₂.sp with
    x23 := by rw [u₂.gpr]; rfl, repr := fun h0 d hd => ?_ }
  rw [u₂.mem]
  refine reprR_flush P hP.pos (hI.repr h0 d hd) ?_
  have hlt := hd.2.2
  rw [hst, one_toNat, compressBlocks_one, hI.x19, hI.x24, List.length_append, D, bytesAt_length,
    ← hd.cnt_eq, toNat_ofNat_lt (by rw [← hd.cnt_eq] at hlt; omega)]
  rfl

/-! ## `head`: filling the buffer -/

theorem lt_of_div_zero {x b : Nat} (hb : 0 < b) (h : x / b = 0) : x < b := by
  refine Nat.lt_of_not_le fun hc => ?_
  have := Nat.div_pos hc hb
  omega

theorem le_of_div_ne {x b : Nat} (h : x / b ≠ 0) : b ≤ x := by
  refine Nat.le_of_not_lt fun hc => h (Nat.div_eq_of_lt hc)

/-- Copying `min(B - r, len - c)` bytes of data into the buffer. -/
theorem fill_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c r : Nat} (hr : r ≤ blockBytes w) {s : State}
    (hI : Inv P s₀ c r s) :
    WP isa (fill (w := w)) s (Inv P s₀ (c + min (blockBytes w - r) (len s₀ - c))
      (r + min (blockBytes w - r) (len s₀ - c))) := by
  have hl := hP.len
  have hL := len_lt s₀
  have hcn := cnt_lt s₀
  have hc := hI.c_le
  have hpos := hP.pos
  obtain ⟨a, ha⟩ : ∃ a, a = min (blockBytes w - r) (len s₀ - c) := ⟨_, rfl⟩
  rw [← ha]
  have ha₁ : a ≤ blockBytes w - r := ha ▸ Nat.min_le_left _ _
  have ha₂ : a ≤ len s₀ - c := ha ▸ Nat.min_le_right _ _
  unfold fill
  refine WP.seq (wp_movz fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_lsr hP.lbb.1 fun s₃ u₃ => WP.block_nil ?_)
  have h11 : s₃.gpr .x11 = BitVec.ofNat 64 (blockBytes w - r) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.x23, movz_B hP, sub_ofNat hr]
  have h9 : s₃.gpr .x9 = BitVec.ofNat 64 ((len s₀ - c) / blockBytes w) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.x22, shr_ofNat hP (by omega)]
  have g₃ : ∀ x, x ≠ .x9 → x ≠ .x11 → s₃.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₃.other x h1, u₂.other x h2, u₁.other x h2]
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hrd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have hwr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have hsp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  -- `x11` := `a`.
  refine WP.seq (WP.mono (Q := fun (t : State) => t.gpr .x11 = BitVec.ofNat 64 a ∧
      (∀ x, x ≠ .x9 → x ≠ .x11 → t.gpr x = s.gpr x) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp) ?_ fun t ht => ?_)
  · refine WP.ite _ (zero_iff s₃ h9 (by have := Nat.div_le_self (len s₀ - c) (blockBytes w); omega))
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      have hlt := lt_of_div_zero hpos hb
      refine WP.seq (wp_add fun s₄ u₄ => wp_lsr hP.lbb.1 fun s₅ u₅ => WP.block_nil ?_)
      have h9' : s₅.gpr .x9 = BitVec.ofNat 64 ((len s₀ - c + r) / blockBytes w) := by
        rw [u₅.gpr, u₄.gpr, g₃ _ (by decide) (by decide), g₃ _ (by decide) (by decide), hI.x22, hI.x23,
          ← BitVec.ofNat_add, shr_ofNat hP (by omega)]
      have g₅ : ∀ x, x ≠ .x9 → x ≠ .x11 → s₅.gpr x = s.gpr x := fun x h1 h2 => by
        rw [u₅.other x h1, u₄.other x h1, g₃ x h1 h2]
      have hm₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, hm₃]
      have hrd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, hrd₃]
      have hwr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, hwr₃]
      have hsp₅ : s₅.sp = s.sp := by rw [u₅.sp, u₄.sp, hsp₃]
      refine WP.ite _ (zero_iff s₅ h9' (by have := Nat.div_le_self (len s₀ - c + r) (blockBytes w); omega))
        (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq] at hb'
        have hlt' := lt_of_div_zero hpos hb'
        refine wp_mov fun s₆ u₆ => WP.block_nil ⟨?_, fun x h1 h2 => by rw [u₆.other x h2, g₅ x h1 h2],
          by rw [u₆.mem, hm₅], by rw [u₆.rd, hrd₅], by rw [u₆.wr, hwr₅], by rw [u₆.sp, hsp₅]⟩
        rw [u₆.gpr, g₅ _ (by decide) (by decide), hI.x22, ha, Nat.min_eq_right (by omega)]
      · simp only [decide_eq_false_iff_not] at hb'
        have hle := le_of_div_ne hb'
        refine WP.block_nil ⟨?_, g₅, hm₅, hrd₅, hwr₅, hsp₅⟩
        rw [u₅.other _ (by decide), u₄.other _ (by decide), h11, ha, Nat.min_eq_left (by omega)]
    · simp only [decide_eq_false_iff_not] at hb
      have hle := le_of_div_ne hb
      refine WP.block_nil ⟨?_, g₃, hm₃, hrd₃, hwr₃, hsp₃⟩
      rw [h11, ha, Nat.min_eq_left (by omega)]
  obtain ⟨tx11, tg, tm, trd, twr, tsp⟩ := ht
  refine WP.seq (wp_sub fun s₅ u₅ => wp_add fun s₆ u₆ => WP.block_nil ?_)
  have g₆ : ∀ x, x ≠ .x9 → x ≠ .x11 → x ≠ .x22 → x ≠ .x24 → s₆.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [u₆.other x h4, u₅.other x h3, tg x h1 h2]
  have h611 : s₆.gpr .x11 = BitVec.ofNat 64 a := by rw [u₆.other _ (by decide), u₅.other _ (by decide), tx11]
  have h622 : s₆.gpr .x22 = BitVec.ofNat 64 (len s₀ - (c + a)) := by
    rw [u₆.other _ (by decide), u₅.gpr, tx11, tg _ (by decide) (by decide), hI.x22, sub_ofNat (by omega)]
    exact congrArg _ (by omega)
  have h624 : s₆.gpr .x24 = BitVec.ofNat 64 (cnt s₀ + (c + a)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₅.other _ (by decide), tx11, tg _ (by decide) (by decide), hI.x24,
      ← BitVec.ofNat_add, Nat.add_assoc]
  have hm₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, tm]
  have hrd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, trd]
  have hwr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, twr]
  have hsp₆ : s₆.sp = s.sp := by rw [u₆.sp, u₅.sp, tsp]
  have hkeep₆ : ∀ r ∈ untouched, s₆.gpr r = s₀.gpr r := fun r hr => by
    rw [g₆ r (notU hr .x9) (notU hr .x11) (notU hr .x22) (notU hr .x24), hI.keep r hr]
  refine WP.ite _ (zero_iff s₆ h611 (by omega)) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    refine WP.block_nil ⟨⟨by omega, hrd₆.trans hI.rd, hwr₆.trans hI.wr, hsp₆.trans hI.sp, ?_, ?_, ?_, h622,
      h624, hkeep₆, by rw [hm₆]; exact hI.frame, by rw [hm₆]; exact hI.saved⟩, ?_, ?_⟩
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x19
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x20
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide), Nat.add_zero]; exact hI.x21
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide), Nat.add_zero]; exact hI.x23
    · rw [hm₆, Nat.add_zero]; exact hI.repr
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (copy_ok hP hp (c := c) (r := r) (k := a) (by omega) (by omega) (by omega)
      (hrd₆.trans hI.rd) (hwr₆.trans hI.wr)
      (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x19)
      (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x21)
      (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x23) h611
      (by rw [hm₆]; exact hI.frame) (by rw [hm₆]; exact hI.saved) (by rw [hm₆]; exact hI.repr))
      fun s₈ ⟨g₈, h821, h823, rd₈, wr₈, sp₈, f₈, sv₈, rp₈⟩ => ?_
    refine ⟨⟨by omega, rd₈, wr₈, sp₈.trans (hsp₆.trans hI.sp), ?_, ?_, h821, ?_, ?_, fun r hr => ?_, f₈, sv₈⟩,
      h823, rp₈⟩
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x19
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x20
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h622
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h624
    · rw [g₈ r (notU hr .x9) (notU hr .x12) (notU hr .x21) (notU hr .x23) (notU hr .x11)]
      exact hkeep₆ r hr

/-- After `head`: all the data is in, with the buffer not empty, or the
buffer is empty and data is left. -/
def HeadPost (P : Params w) (s₀ : State) (s : State) : Prop :=
  ∃ c r, Inv P s₀ c r s ∧ ((c = len s₀ ∧ 1 ≤ r) ∨ (c < len s₀ ∧ r = 0))

theorem head_ok (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀) {r : Nat}
    (hr : r ≤ blockBytes w) (hl : 0 < len s₀) {s : State} (hI : Inv P s₀ 0 r s) :
    WP isa (head P) s (HeadPost P s₀) := by
  have hL := len_lt s₀
  have hl' := hP.len
  unfold head
  refine WP.ite _ (zero_iff s hI.x23 (by omega)) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact WP.block_nil ⟨0, 0, hI, .inr ⟨hl, rfl⟩⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (WP.mono (fill_ok hP hp hr hI) fun s₂ hI₂ => ?_)
    rw [Nat.zero_add, Nat.sub_zero] at hI₂
    refine WP.ite _ (zero_iff s₂ hI₂.x22 (by omega)) (fun hb' => ?_) (fun hb' => ?_)
    · simp only [decide_eq_true_eq] at hb'
      exact WP.block_nil ⟨_, _, hI₂, .inl ⟨by omega, by omega⟩⟩
    · simp only [decide_eq_false_iff_not] at hb'
      have e : r + min (blockBytes w - r) (len s₀) = blockBytes w := by omega
      rw [e] at hI₂
      exact WP.mono (compressBuf_ok hP hf hp hI₂) fun s₄ hI₄ => ⟨_, _, hI₄, .inr ⟨by omega, rfl⟩⟩

/-! ## `rest`: whole blocks straight from the data, and the last block -/

/-- The arguments for compressing blocks of data. -/
theorem directArgs_ok {σ : State} (hB : B w < 4096) :
    WP isa (.block (([mov .x0 .x19] : List Instr) ++ ([mov .x1 .x21, mov .x2 .x10,
      .addImm .x .x3 .x24 (B w), .movz .x .x4 0 0] : List Instr) ++ ([mov .x5 .x20] : List Instr))) σ
      fun s => Setup σ s (σ.gpr .x21) (σ.gpr .x10) (σ.gpr .x24 + BitVec.ofNat 64 (B w)) false := by
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_addImm hB fun s₄ u₄ =>
    wp_movz fun s₅ u₅ => wp_mov fun s₆ u₆ => WP.block_nil ?_
  have hcs : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr]; rfl
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hcs r hr
    rw [u₆.other _ h5, u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

/-- The blocks of data but the last, straight from the data. -/
theorem direct_ok (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀) {c : Nat}
    (hc : c < len s₀) {s : State} (hI : Inv P s₀ c 0 s) :
    WP isa (direct P) s (Inv P s₀ (c + blockBytes w * ((len s₀ - c - 1) / blockBytes w)) 0) := by
  have hl := hP.len
  have hL := len_lt s₀
  have hcn := cnt_lt s₀
  have hpos := hP.pos
  obtain ⟨k, hk⟩ : ∃ k, k = (len s₀ - c - 1) / blockBytes w := ⟨_, rfl⟩
  rw [← hk]
  have hdm := Nat.div_add_mod (len s₀ - c - 1) (blockBytes w)
  have hmod := Nat.mod_lt (len s₀ - c - 1) hpos
  rw [← hk] at hdm
  have hkle : k ≤ len s₀ - c - 1 := hk ▸ Nat.div_le_self _ _
  unfold direct
  refine WP.seq (wp_subImm (by decide) fun s₁ u₁ => wp_lsr hP.lbb.1 fun s₂ u₂ => WP.block_nil ?_)
  have h10 : s₂.gpr .x10 = BitVec.ofNat 64 k := by
    rw [u₂.gpr, u₁.gpr, hI.x22, sub_ofNat (by omega), shr_ofNat hP (by omega), hk]
  have hC₂ : Common w s₀ c s₂ := hI.toCommon.of_gpr
    (fun r hr => by rw [u₂.other r (notC hr .x10), u₁.other r (notC hr .x9)])
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (by rw [u₂.sp, u₁.sp])
  have h23 : s₂.gpr .x23 = BitVec.ofNat 64 0 := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hI.x23
  have hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine WP.ite _ (zero_iff s₂ h10 (by omega)) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    rw [Nat.mul_zero, Nat.add_zero]
    exact WP.block_nil ⟨hC₂, h23, by rw [hm₂]; exact hI.repr⟩
  simp only [decide_eq_false_iff_not] at hb
  have hBk : blockBytes w * k + 1 ≤ len s₀ - c := by omega
  have hBk' : blockBytes w ≤ blockBytes w * k := Nat.le_mul_of_pos_right _ (by omega)
  have hsrc : Src w s₀ (s₂.gpr .x21) (blockBytes w * (s₂.gpr .x10).toNat) :=
    .inr ⟨c, hC₂.x21, by rw [h10, toNat_ofNat_lt (by omega)]; omega⟩
  refine WP.seq (compressWith_ok hf (directArgs_ok (by rw [B_eq]; omega)) (callOk hP hp hC₂ hsrc)
    fun s' hrd hwr hsp hcs hfr hst => ?_)
  have hC' := hC₂.after_call hP hp hrd hwr hsp hcs hfr
  refine wp_subImm (by decide) fun s₁ u₁ => wp_movz fun s₃ u₃ => wp_and fun s₄ u₄ =>
    wp_addImm (by decide) fun s₅ u₅ => wp_sub fun s₆ u₆ => wp_add fun s₇ u₇ => wp_add fun s₈ u₈ =>
    wp_mov fun s₉ u₉ => WP.block_nil ?_
  have hm : (len s₀ - c - 1) % blockBytes w + 1 = len s₀ - (c + blockBytes w * k) := by omega
  have hx9 : s₅.gpr .x9 = BitVec.ofNat 64 (len s₀ - (c + blockBytes w * k)) := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₁.gpr, hC'.x22, sub_ofNat (by omega), mask_mod hP,
      toNat_ofNat_lt (by omega), ← BitVec.ofNat_add, hm]
  have h10₆ : s₆.gpr .x10 = BitVec.ofNat 64 (blockBytes w * k) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₁.other _ (by decide), hC'.x22, hx9, sub_ofNat (by omega)]
    exact congrArg _ (by omega)
  have hg : ∀ x, x ≠ .x9 → x ≠ .x10 → x ≠ .x21 → x ≠ .x22 → x ≠ .x24 → s₉.gpr x = s'.gpr x :=
    fun x h1 h2 h3 h4 h5 => by
      rw [u₉.other x h4, u₈.other x h5, u₇.other x h3, u₆.other x h2, u₅.other x h1, u₄.other x h1,
        u₃.other x h2, u₁.other x h1]
  have hm₉ : s₉.mem = s'.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₁.mem]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, by rw [hm₉]; exact hC'.frame,
    by rw [hm₉]; exact hC'.saved⟩, ?_, fun h0 d hd => ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₁.rd, hC'.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₁.wr, hC'.wr]
  · rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₁.sp, hC'.sp]
  · rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC'.x19
  · rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC'.x20
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), h10₆,
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₁.other _ (by decide),
      hC'.x21, Offset.add_add]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), hx9]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other .x24 (by decide), u₇.other .x10 (by decide), h10₆,
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₁.other _ (by decide), hC'.x24, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [hg r (notU hr .x9) (notU hr .x10) (notU hr .x21) (notU hr .x22) (notU hr .x24)]; exact hC'.keep r hr
  · rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide), hcs _ (by decide) (by decide), h23]
  · have hcnt := hd.cnt_eq
    have hlt := hd.2.2
    have e : d ++ D s₀ (c + blockBytes w * k) =
        d ++ D s₀ c ++ bytesAt s₂.mem (dp s₀ + BitVec.ofNat 64 c) (blockBytes w * k) := by
      rw [D, bytesAt_add, List.append_assoc]
      refine congrArg (fun l => d ++ (bytesAt s₀.mem (dp s₀) c ++ l)) (bytesAt_congr fun i hi => ?_)
      rw [Offset.add_add]
      exact (hC₂.data hp (by omega)).symm
    rw [hm₉, e]
    refine reprR_blocks P hpos (by rw [hm₂]; exact hI.repr h0 d hd) ?_
    rw [hst, h10, hC₂.x21, hC₂.x24, B_eq, ← BitVec.ofNat_add, toNat_ofNat_lt (by omega),
      toNat_ofNat_lt (by omega), List.length_append, D, bytesAt_length, ← hcnt]

/-- The last `1` to `B` bytes of data, into the empty buffer. -/
theorem tail_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} (hc₁ : c < len s₀)
    (hc₂ : len s₀ - c ≤ blockBytes w) {s : State} (hI : Inv P s₀ c 0 s) :
    WP isa (tail (w := w)) s (Inv P s₀ (len s₀) (len s₀ - c)) := by
  have hL := len_lt s₀
  unfold tail
  refine WP.seq (wp_mov fun s₁ u₁ => wp_add fun s₂ u₂ => wp_movz fun s₃ u₃ => WP.block_nil ?_)
  have hg : ∀ x, x ≠ .x11 → x ≠ .x24 → x ≠ .x22 → s₃.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [u₃.other x h3, u₂.other x h2, u₁.other x h1]
  have h11 : s₃.gpr .x11 = BitVec.ofNat 64 (len s₀ - c) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.x22]
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (copy_ok hP hp (c := c) (r := 0) (k := len s₀ - c) (by omega) (by omega) (by omega)
      (by rw [u₃.rd, u₂.rd, u₁.rd, hI.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr, hI.wr])
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.x19)
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.x21)
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.x23) h11
      (by rw [hm₃]; exact hI.frame) (by rw [hm₃]; exact hI.saved) (by rw [hm₃]; exact hI.repr))
    fun s₄ ⟨g₄, h421, h423, rd₄, wr₄, sp₄, f₄, sv₄, rp₄⟩ => ?_
  have e : c + (len s₀ - c) = len s₀ := by omega
  rw [e] at h421 rp₄
  rw [Nat.zero_add] at h423 rp₄
  have g : ∀ x, x ≠ .x9 → x ≠ .x12 → x ≠ .x21 → x ≠ .x23 → x ≠ .x11 → x ≠ .x24 → x ≠ .x22 →
      s₄.gpr x = s.gpr x := fun x h1 h2 h3 h4 h5 h6 h7 => by rw [g₄ x h1 h2 h3 h4 h5, hg x h5 h6 h7]
  refine ⟨⟨Nat.le_refl _, rd₄, wr₄, by rw [sp₄, u₃.sp, u₂.sp, u₁.sp, hI.sp], ?_, ?_, h421, ?_, ?_,
    fun r hr => ?_, f₄, sv₄⟩, h423, rp₄⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.x19
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.x20
  · rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), u₃.gpr, Nat.sub_self]; rfl
  · rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), u₁.other _ (by decide), hI.x24, hI.x22, ← BitVec.ofNat_add]
    exact congrArg _ (by omega)
  · rw [g r (notU hr .x9) (notU hr .x12) (notU hr .x21) (notU hr .x23) (notU hr .x11) (notU hr .x24)
      (notU hr .x22)]
    exact hI.keep r hr

/-- All the data is in, and the buffer is not empty. -/
def Full (P : Params w) (s₀ : State) (s : State) : Prop := ∃ r, Inv P s₀ (len s₀) r s ∧ 1 ≤ r

theorem rest_ok (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀) {s : State}
    (h : HeadPost P s₀ s) : WP isa (rest P) s (Full P s₀) := by
  have hL := len_lt s₀
  have hpos := hP.pos
  obtain ⟨c, r, hI, hcr⟩ := h
  have hc := hI.c_le
  unfold rest
  refine WP.ite _ (zero_iff s hI.x22 (by omega)) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', _⟩
    · exact WP.block_nil ⟨r, hI, hr⟩
    · omega
  · simp only [decide_eq_false_iff_not] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', rfl⟩
    · omega
    refine WP.seq (WP.mono (direct_ok hP hf hp hc' hI) fun s₂ hI₂ => ?_)
    have hdm := Nat.div_add_mod (len s₀ - c - 1) (blockBytes w)
    have hmod := Nat.mod_lt (len s₀ - c - 1) hpos
    exact WP.mono (tail_ok hP hp (by omega) (by omega) hI₂) fun s₃ hI₃ => ⟨_, hI₃, by omega⟩

/-! ## Epilogue and the whole function -/

/-- All the data is in. -/
def Done (P : Params w) (s₀ : State) (s : State) : Prop :=
  Common w s₀ (len s₀) s ∧
    ∀ h0 d, R₀ P s₀ h0 d → Spec.Blake2.Repr P h0 s.mem (st s₀) (d ++ D s₀ (len s₀))

theorem Full.done (hP : Ok P) {s₀ : State} {s : State} (h : Full P s₀ s) : Done P s₀ s := by
  obtain ⟨r, hI, hr⟩ := h
  exact ⟨hI.toCommon, fun h0 d hd => repr_of_reprR P hP.pos (hI.repr h0 d hd) hr⟩

/-- The epilogue's postcondition. -/
def Post (P : Params w) (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ (updateAArch64 P).post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre w s₀) {s : State} (hI : Done P s₀ s) :
    WP isa (.block restore) s (Post P s₀) := by
  refine restore_ok (scr := scr s₀) hI.1.x20
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hI.1.rd, hI.1.wr, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩)
    s₀.gpr hI.1.saved fun s' hs ho hmem _ _ hsp => ⟨preserved_of hs fun r hr => ?_, by rw [hsp, hI.1.sp],
      fun h0 d hr hc hl => ?_⟩
  · rw [ho r (by simp only [untouched] at hr; simp only [saved, List.map_cons, List.map_nil]; decide +revert),
      hI.1.keep r hr]
  · rw [hmem]; exact hI.2 h0 d ⟨hr, hc, hl⟩

/-- `update` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀) :
    WP isa (updateMain P) s₀ (Post P s₀) := by
  have hL := len_lt s₀
  unfold updateMain
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hC, hm⟩ => ?_)
  refine WP.seq (WP.mono (bufLen_ok' hP hp hC hm) fun s₂ hI => ?_)
  refine WP.seq (WP.mono (Q := Done P s₀) ?_ fun s₄ h => epilogue_ok hp h)
  refine WP.ite _ (zero_iff s₂ hI.x22 (by omega)) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq, Nat.sub_zero] at hb
    refine WP.block_nil ⟨by rw [hb]; exact hI.toCommon, fun h0 d hd => ?_⟩
    have := hI.repr h0 d hd
    have e0 : ∀ n, n = 0 → bytesAt s₀.mem (dp s₀) n = [] := by rintro _ rfl; simp [bytesAt]
    rw [show D s₀ 0 = [] from e0 _ rfl, List.append_nil] at this
    rw [show D s₀ (len s₀) = [] from e0 _ hb, List.append_nil]
    rw [repr_iff P hP.pos, ← hd.cnt_eq]; exact this
  · simp only [decide_eq_false_iff_not, Nat.sub_zero] at hb
    have hr := bufLen_le (w := w) hP.pos (cnt s₀)
    exact WP.seq (WP.mono (head_ok hP hf hp hr (by omega) hI) fun s₄ h =>
      WP.mono (rest_ok hP hf hp h) fun s₅ h => h.done hP)

theorem noFrames_updateMain (hf : CalleeOk P (compress P)) : (updateMain P).noFrames = true := by
  simp only [updateMain, head, rest, fill, compressBuf, direct, tail, Impl.Blake2.AArch64.Stream.compressWith,
    copyLoop, Impl.Blake2.AArch64.Stream.bufLen, Code.noFrames, hf.noFrames, Bool.and_self]

/-- The state `updateMain` starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State}
    (hpre : (updateAArch64 P).pre s₀) :
    WP isa (update P) s₀ fun s' => abiPreserved s₀ s' ∧ (updateAArch64 P).post s₀ s' := by
  obtain ⟨hp, hs⟩ := pre_of hpre
  have hl := hP.len
  have hpi : Pre w (inner s₀) := ⟨hp.rd, hp.wr, hp.st_scr, hp.d_st, hp.d_scr⟩
  refine WP.frameReg hs.sp16 (fun R hR => ?_) (WP.mono (correctMain hP hf hpi) fun s' ⟨hk, hsp, hpost⟩ => ?_)
    (by rw [fdepth_of_noFrames (noFrames_updateMain hf)]; decide)
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.st
    · exact hs.scr
  · refine ⟨⟨fun r hr => ?_, rfl⟩, fun h0 d hm hc hlt => ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · have e : bytesAt (inner s₀).mem (dp s₀) (len s₀) = bytesAt s₀.mem (dp s₀) (len s₀) :=
        bytesAt_congr fun i hi => write_frame_bytes hs.d (len_lt s₀) hi
      have := hpost h0 d (repr_congr hP (fun i hi => write_frame_bytes (R := stR s₀ w) hs.st
        (by show bufOff w + blockBytes w < 2 ^ 64; omega) hi) hm) hc hlt
      rw [e] at this
      exact this

end VG.Proof.Blake2.AArch64.Stream.Update
