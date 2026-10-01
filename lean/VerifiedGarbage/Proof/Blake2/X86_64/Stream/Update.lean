import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Common
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# Streaming BLAKE2 on x86-64: `update`

Untrusted: everything here is checked by Lean. The functional correctness of
`update`, for either word size and any correct compression function
(`CalleeOk`).
-/

namespace VG.Proof.Blake2.X86_64.Stream.Update

open VG VG.X86_64 VG.Spec.Blake2
open VG.Impl.Blake2.X86_64.Stream
open VG.Impl.Blake2.X86_64 (at_ compress)
open VG.Proof.MdStream.X86_64 (Upd ofInt_natCast toNat_ofNat_lt wp_mov wp_movm wp_store
  wp_addi wp_subi wp_sub wp_add wp_cmp wp_test wp_movzx8 wp_store8 wp_mov32i wp_andi wp_shr test_ok
  sx1 ofNat_succ ofNat_pred ofNat_beq_zero sub_ofNat contains_offset contains_offset' sub_offset ea_at
  Saved saveMem saveMem_saved saveMem_frame)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)
open VG.Proof.Blake2 (ReprR bufLen_le repr_iff reprR_append reprR_flush reprR_blocks repr_of_reprR stateAt_congr
  bytesAt_congr bytesAt_add blockAt_congr compressBlocks_congr)

variable {w : Nat} {P : Params w} {callee : Impl.Blake2.X86_64.Stream.Callee}

/-! ## Saving the caller's registers

As the Merkle–Damgård hash functions do, after the compression function's
512 bytes of scratch space. -/

/-- The Merkle–Damgård streaming parameters with the same saved registers. -/
def mdP : Impl.MdStream.X86_64.Params := ⟨1, 64, 1, 512, [], []⟩

theorem mdP_dims : MdStream.X86_64.Dims mdP := ⟨.inl rfl, by decide, by decide, by decide⟩

theorem save_eq (b : Reg) : save b = Impl.MdStream.X86_64.save mdP b := rfl
theorem restore_eq' : restore = Impl.MdStream.X86_64.restore mdP := rfl

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev cnt : Nat := (s₀.gpr .rsi).toNat
abbrev dp : Addr := s₀.gpr .rdx
abbrev len : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev stR (w : Nat) : Region := ⟨st s₀, bufOff w + blockBytes w⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
/-- Where the calls of the compression function store the return address. -/
abbrev stkR : Region := below (s₀.gpr .rsp) 8
abbrev scR : Region := ⟨scr s₀, 576⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀ w, scR s₀]
  st_scr : (stR s₀ w).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀ w)
  d_scr : (dR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀ w)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀ w)
  stk_d : (stkR s₀).Disjoint (dR s₀)
  stk_scr : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : (updateX86_64 P).pre s₀) : Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 8) (d := 8) (n := 8) (k := 8)
    (Nat.le_refl _) (by omega)
  rwa [BitVec.sub_add_cancel] at this

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .rcx).isLt
theorem cnt_lt (s₀ : State) : cnt s₀ < 2 ^ 64 := (s₀.gpr .rsi).isLt

/-- The data the initial state represents, from `h0`. -/
def R₀ (P : Params w) (s₀ : State) (h0 : HashValue w) (d : List Byte) : Prop :=
  Spec.Blake2.Repr P h0 s₀.mem (st s₀) d ∧ s₀.gpr .rsi = BitVec.ofNat 64 d.length ∧
    d.length + len s₀ < 2 ^ 64

theorem R₀.cnt_eq {s₀ : State} {h0 : HashValue w} {d : List Byte} (h : R₀ P s₀ h0 d) :
    cnt s₀ = d.length := by
  rw [Update.cnt, h.2.1, toNat_ofNat_lt (by have := h.2.2; omega)]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (w : Nat) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = st s₀
  r15 : s.gpr .r15 = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbp : s.gpr .rbp = dp s₀ + BitVec.ofNat 64 c
  r12 : s.gpr .r12 = BitVec.ofNat 64 (len s₀ - c)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (cnt s₀ + c)
  frame : Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved mdP s₀ .r8 s.mem

/-- The state represents the data followed by the first `c` bytes of data,
the last `r` of them in the buffer. -/
structure Inv (P : Params w) (s₀ : State) (c r : Nat) (s : State) : Prop extends Common w s₀ c s where
  r13 : s.gpr .r13 = BitVec.ofNat 64 r
  repr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (st s₀) (d ++ D s₀ c) r

theorem Common.congr {s₀ : State} {c : Nat} {s s' : State} (h : Common w s₀ c s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common w s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg]; exact h.rbx
  r15 := by rw [hg]; exact h.r15
  rsp := by rw [hg]; exact h.rsp
  rbp := by rw [hg]; exact h.rbp
  r12 := by rw [hg]; exact h.r12
  r14 := by rw [hg]; exact h.r14
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

/-- The registers `Common` is about. -/
abbrev commonRegs : List Reg := [.rbx, .r15, .rsp, .rbp, .r12, .r14]

theorem ne_rax : ∀ x ∈ commonRegs, x ≠ .rax := by decide
theorem ne_r13 : ∀ x ∈ commonRegs, x ≠ .r13 := by decide

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common w s₀ c s)
    (hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common w s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg _ (by simp)]; exact h.rbx
  r15 := by rw [hg _ (by simp)]; exact h.r15
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  rbp := by rw [hg _ (by simp)]; exact h.rbp
  r12 := by rw [hg _ (by simp)]; exact h.r12
  r14 := by rw [hg _ (by simp)]; exact h.r14
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Common.congr' {s₀ : State} {c : Nat} {s s' : State} (h : Common w s₀ c s)
    (hg : ∀ r, r ≠ .r13 → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common w s₀ c s' :=
  h.of_gpr (fun r hr => hg r (ne_r13 r hr)) hm hrd hwr

theorem Inv.congr {s₀ : State} {c r : Nat} {s s' : State} (h : Inv P s₀ c r s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv P s₀ c r s' :=
  { h.toCommon.congr hg hm hrd hwr with
    r13 := by rw [hg]; exact h.r13
    repr := by rw [hm]; exact h.repr }

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre w s₀) {c : Nat} {s : State} (h : Common w s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩)
    (Nat.le_of_lt (len_lt s₀)) hi

/-! ## Prologue -/

theorem common_zero {s₀ : State} {s : State} (hm : s.mem = saveMem mdP s₀ .r8)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hrbx : s.gpr .rbx = st s₀) (hr15 : s.gpr .r15 = scr s₀)
    (hrsp : s.gpr .rsp = s₀.gpr .rsp) (hrbp : s.gpr .rbp = dp s₀) (hr12 : s.gpr .r12 = s₀.gpr .rcx)
    (hr14 : s.gpr .r14 = s₀.gpr .rsi) : Common w s₀ 0 s where
  c_le := Nat.zero_le _
  rd := hrd
  wr := hwr
  rbx := hrbx
  r15 := hr15
  rsp := hrsp
  rbp := by rw [hrbp]; simp
  r12 := by rw [hr12]; simp
  r14 := by rw [hr14]; simp
  frame := by
    rw [hm]
    exact (saveMem_frame mdP_dims).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, Region.sub_prefix (by decide)⟩
  saved := by rw [hm]; exact saveMem_saved mdP_dims

set_option simprocs false in
theorem prologue_ok {s₀ : State} (hp : Pre w s₀) :
    WP isa (.block updateStart) s₀ fun s => Common w s₀ 0 s ∧ s.mem = saveMem mdP s₀ .r8 := by
  have o : ∀ d : Nat, d + 8 ≤ 512 + 48 → InRegions s₀.wr (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨scR s₀, by simp [hp.wr], contains_offset' (by omega) (by omega)⟩
  have o0 := o 512 (by omega); have o1 := o (512 + 8) (by omega); have o2 := o (512 + 16) (by omega)
  have o3 := o (512 + 24) (by omega); have o4 := o (512 + 32) (by omega); have o5 := o (512 + 40) (by omega)
  apply WP.of_runBlock
  rw [updateStart, save_eq, MdStream.X86_64.save_eq]
  simp only [List.cons_append, List.nil_append]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at, mdP,
    State.store64, o0, o1, o2, o3, o4, o5, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨common_zero rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_, rfl⟩ <;>
    simp (config := {decide := true}) only [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne,
      not_false_eq_true]

/-- `Repr` depends only on the bytes of the streaming state. -/
theorem repr_congr (hP : Ok P) {h0 : HashValue w} {mem mem' : Mem} {p : Addr} {d : List Byte}
    (hm : ∀ i < bufOff w + blockBytes w, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (h : Spec.Blake2.Repr P h0 mem p d) : Spec.Blake2.Repr P h0 mem' p d := by
  have hN : bufOff w + blockBytes w < 2 ^ 64 := by rcases hP.bb with h | h <;> rw [hP.N, h] <;> decide
  rw [repr_iff P hP.pos] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, by rw [← h4]; exact stateAt_congr fun i hi => hm i (by omega), ?_⟩
  rw [← h5]
  refine bytesAt_congr fun i hi => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hm _ (by omega)

/-! ## The bytes in the buffer -/

theorem mask_mod (hP : Ok P) (x : BitVec 64) :
    x &&& (BitVec.ofNat 32 (B w - 1)).signExtend 64 = BitVec.ofNat 64 (x.toNat % blockBytes w) :=
  MdStream.X86_64.and_mask hP.bb x

theorem bufLen_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (hC : Common w s₀ 0 s)
    (hm : s.mem = saveMem mdP s₀ .r8) :
    WP isa (Impl.Blake2.X86_64.Stream.bufLen (w := w)) s (Inv P s₀ 0 (Blake2.bufLen w (cnt s₀))) := by
  have hc := cnt_lt s₀
  have hbb := hP.bb
  have h14 : s.gpr .r14 = BitVec.ofNat 64 (cnt s₀) := by rw [hC.r14, Nat.add_zero]
  -- The representation.
  have hrepr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (st s₀) (d ++ D s₀ 0) (Blake2.bufLen w (cnt s₀)) := by
    intro h0 d hd
    have e : D s₀ 0 = [] := by simp [bytesAt]
    rw [e, List.append_nil, hd.cnt_eq, ← repr_iff P hP.pos]
    refine repr_congr hP (fun i hi => ?_) hd.1
    have hN : bufOff w + blockBytes w ≤ 2 ^ 64 := by
      rcases hbb with h | h <;> rw [hP.N, h] <;> decide
    have hd : (stR s₀ w).Disjoint ⟨scr s₀, mdP.so + 48⟩ :=
      hp.st_scr.sub_right (Region.sub_prefix (by decide))
    rw [hm]
    exact (saveMem_frame mdP_dims).bytes (R := stR s₀ w) (by simpa using hd) hN hi
  unfold Impl.Blake2.X86_64.Stream.bufLen
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => wp_subi fun s₂ u₂ _ => wp_andi fun s₃ u₃ =>
    wp_addi fun s₄ u₄ => wp_test fun s₅ g₅ m₅ rd₅ wr₅ z₅ => WP.block_nil ?_)
  have g : ∀ r, r ≠ .r13 → s₅.gpr r = s.gpr r := fun r h => by
    rw [g₅, u₄.other r h, u₃.other r h, u₂.other r h, u₁.other r h]
  have hm₅ : s₅.mem = s.mem := by rw [m₅, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hrd : s₅.rd = s.rd := by rw [rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hwr : s₅.wr = s.wr := by rw [wr₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hC₅ : Common w s₀ 0 s₅ := hC.congr' g hm₅ hrd hwr
  have hz : isa.eval .e s₅ = some (decide (cnt s₀ = 0)) := by
    have e : s₄.gpr .r14 = BitVec.ofNat 64 (cnt s₀) := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h14]
    simp only [eval, z₅, e, BitVec.and_self, ofNat_beq_zero hc]
  refine WP.ite (decide (cnt s₀ = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_mov32i fun s₆ u₆ _ _ => WP.block_nil ?_
    refine { hC₅.congr' (fun r h => u₆.other r h) u₆.mem u₆.rd u₆.wr with r13 := ?_, repr := ?_ }
    · rw [u₆.gpr, Blake2.bufLen, hb]; rfl
    · rw [u₆.mem, hm₅]; exact hrepr
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil { hC₅ with r13 := ?_, repr := ?_ }
    · rw [g₅, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, h14, sx1, ofNat_pred (by omega), mask_mod hP,
        toNat_ofNat_lt (by omega), Blake2.bufLen, ite_eq_right_of_eq_false _ _ (eq_false hb), ← ofNat_succ]
    · rw [hm₅]; exact hrepr

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

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by simp [bytesAt]

/-- Writes to the state, the compression function's scratch space and below
the stack keep the saved registers. -/
theorem saved_frame {s₀ : State} (hp : Pre w s₀) {m m' : Mem} (h : Saved mdP s₀ .r8 m)
    (hf : Frame [stR s₀ w, ⟨scr s₀, 512⟩, stkR s₀] m m') : Saved mdP s₀ .r8 m' := by
  intro p hp'
  obtain ⟨h₁, h₂⟩ := MdStream.X86_64.saved_offset mdP_dims hp'
  simp only [mdP] at h₁ h₂
  rw [← h p hp']
  refine hf.readW (r := ⟨scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩) (Region.contains_self _ _) ?_ (by decide)
  have e : Region.Sub ⟨scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩ (scR s₀) := by
    rw [ofInt_natCast]; exact sub_offset (by omega) (by omega)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left e
  · rw [ofInt_natCast]; exact Offset.disjoint_base _ (by omega) (by omega)
  · exact hp.stk_scr.symm.sub_left e

theorem ok_len (hP : Ok P) : bufOff w + blockBytes w ≤ 256 := by
  rcases hP.bb with h | h <;> rw [hP.N, h] <;> decide

/-- Copying `k` bytes of data, from byte `c` on, into the buffer, from byte
`r` on. -/
theorem copy_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c r k : Nat} (hk : 1 ≤ k)
    (hrk : r + k ≤ blockBytes w) (hck : c + k ≤ len s₀) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hrbx : s.gpr .rbx = st s₀)
    (hrbp : s.gpr .rbp = dp s₀ + BitVec.ofNat 64 c) (hr13 : s.gpr .r13 = BitVec.ofNat 64 r)
    (hrax : s.gpr .rax = BitVec.ofNat 64 k) (hf : Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem s.mem)
    (hs : Saved mdP s₀ .r8 s.mem)
    (hrepr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (st s₀) (d ++ D s₀ c) r) :
    WP isa (copyLoop (w := w)) s fun s' =>
      (∀ x, x ≠ .r9 → x ≠ .rax → x ≠ .rbp → x ≠ .r13 → s'.gpr x = s.gpr x) ∧
      s'.gpr .rbp = dp s₀ + BitVec.ofNat 64 (c + k) ∧ s'.gpr .r13 = BitVec.ofNat 64 (r + k) ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem s'.mem ∧
      Saved mdP s₀ .r8 s'.mem ∧
      ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s'.mem (st s₀) (d ++ D s₀ (c + k)) (r + k) := by
  have hl := ok_len hP
  have hL := len_lt s₀
  have hsrc : ∀ i < k, InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨dR s₀, by simp [hrd, hp.rd], by
      rw [Offset.add_add]; exact contains_offset (by omega) (by omega)⟩
  have hdst : ∀ i < k, InRegions s.wr (st s₀ + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨stR s₀ w, by simp [hwr, hp.wr], by
      rw [Offset.add_add]; exact contains_offset (by omega) (by omega)⟩
  have hd : Region.Disjoint ⟨dp s₀ + BitVec.ofNat 64 c, k⟩ ⟨st s₀ + BitVec.ofNat 64 (bufOff w + r), k⟩ :=
    (hp.d_st.sub_left (sub_offset (by omega) (by omega))).sub_right (sub_offset (by omega) (by omega))
  refine copyLoop_ok (w := w) hk (by omega) hrbx hrbp hr13 hrax hsrc hdst hd fun s' h => ?_
  -- The bytes copied.
  have hx : bytesAt s.mem (dp s₀ + BitVec.ofNat 64 c) k = bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k :=
    bytesAt_congr fun i hi => by
      rw [Offset.add_add]
      exact hf.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩)
        (Nat.le_of_lt hL) (show c + i < len s₀ by omega)
  have hm : s'.mem = writeBytes s.mem (st s₀ + BitVec.ofNat 64 (bufOff w + r))
      (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k) := by
    rw [h.mem, List.take_of_length_le (by rw [bytesAt_length]), hx]
  have hfw : Frame [stR s₀ w] s.mem s'.mem := by
    rw [hm]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact contains_offset (by omega) (by omega))
  refine ⟨h.other, h.rbp.trans (Offset.add_add _ _ _), h.r13, h.rd.trans hrd, h.wr.trans hwr,
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
  have hl := ok_len hP; have := len_lt s₀
  have eN : Region.Sub ⟨st s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨scr s₀, 512⟩ (scR s₀) := Region.sub_prefix (by omega)
  have eSrc : Region.Sub ⟨src, n⟩ (stR s₀ w) ∨ Region.Sub ⟨src, n⟩ (dR s₀) := by
    rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · exact .inl (h' ▸ sub_offset (by omega) (by omega))
    · exact .inr (h' ▸ sub_offset (by omega) (by omega))
  have hsp := h.rsp
  refine ⟨h.rbx, h.r15, (hp.st_scr.sub_left eN).sub_right eso, ?_, ?_,
    by rw [hsp]; exact hp.stk_st.sub_right eN, by rw [hsp]; exact hp.stk_scr.sub_right eso, ?_, ?_, ?_,
    by omega, by rcases hsrc with ⟨_, rfl⟩ | ⟨c₀, _, hc₀⟩ <;> omega⟩
  · rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · rw [h']; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
    · exact (hp.d_st.sub_left (h' ▸ sub_offset (by omega) (by omega))).sub_right eN
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

/-- A call keeps what holds throughout. -/
theorem Common.after_call (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} {s s' : State}
    (h : Common w s₀ c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame [⟨st s₀, bufOff w⟩, ⟨scr s₀, 512⟩, below (s.gpr .rsp) 8] s.mem s'.mem) :
    Common w s₀ c s' := by
  have hl := ok_len hP
  have hf' : Frame [stR s₀ w, ⟨scr s₀, 512⟩, stkR s₀] s.mem s'.mem := hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀ w, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨scr s₀, 512⟩, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, by rw [h.rsp]; exact fun _ h => h⟩
  exact ⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, by rw [hcs _ (by decide)]; exact h.rbx,
    by rw [hcs _ (by decide)]; exact h.r15, by rw [hcs _ (by decide)]; exact h.rsp,
    by rw [hcs _ (by decide)]; exact h.rbp, by rw [hcs _ (by decide)]; exact h.r12,
    by rw [hcs _ (by decide)]; exact h.r14,
    h.frame.trans (hf'.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀ w, by simp, fun _ h => h⟩
      · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩),
    saved_frame hp h.saved hf'⟩

theorem compressBlocks_one (h : HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    compressBlocks P h m p 1 t f = F P h (blockAt w m p) t f := by
  rw [compressBlocks_succ, compressBlocks_zero]; simp

/-- Compressing the full buffer. -/
theorem compressBuf_ok (hP : Ok P) (hf : CalleeOk P callee.code) {s₀ : State} (hp : Pre w s₀)
    {c : Nat} {s : State} (hI : Inv P s₀ c (blockBytes w) s) :
    WP isa (compressBuf (w := w) callee) s (Inv P s₀ c 0) := by
  have hl := ok_len hP
  have hc := hI.c_le
  unfold compressBuf
  refine WP.seq (compressWith_ok (src := st s₀ + BitVec.ofNat 64 (bufOff w)) (n := 1)
    (t := BitVec.ofNat 64 (cnt s₀ + c)) (last := false) hf ?_
    (by simpa using callOk hP hp hI.toCommon (.inl ⟨rfl, rfl⟩)) fun s' hrd hwr hcs hfr hst => ?_)
  · simp only [List.cons_append, List.nil_append]
    refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_addi fun s₃ u₃ => wp_mov32i fun s₄ u₄ _ _ =>
      wp_mov fun s₅ u₅ _ _ => wp_mov32i fun s₆ u₆ _ _ => wp_mov fun s₇ u₇ _ _ => WP.block_nil ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, u₂.gpr, u₁.other _ (by decide), hI.rbx, N_eq, MdStream.X86_64.sx_ofNat (by omega)]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.r14]
    · rw [u₇.other _ (by decide), u₆.gpr]; rfl
    · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
    · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine wp_mov32i fun s₂ u₂ _ _ => WP.block_nil ?_
  have hC := hI.toCommon.after_call hP hp hrd hwr hcs hfr
  have hC₂ := hC.congr' (fun r h => u₂.other r h) u₂.mem u₂.rd u₂.wr
  refine { hC₂ with r13 := ?_, repr := fun h0 d hd => ?_ }
  · rw [u₂.gpr]; rfl
  rw [u₂.mem]
  refine reprR_flush P hP.pos (hI.repr h0 d hd) ?_
  rw [hst, show (1 : BitVec 64).toNat = 1 from rfl, compressBlocks_one, List.length_append, D, bytesAt_length, ← hd.cnt_eq,
    toNat_ofNat_lt (by have := hd.2.2; rw [← hd.cnt_eq] at this; omega)]

/-! ## `head`: filling the buffer -/

/-- Copying `min(B - r, len - c)` bytes of data into the buffer. -/
theorem fill_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c r : Nat} (hr : r ≤ blockBytes w) {s : State}
    (hI : Inv P s₀ c r s) :
    WP isa (fill (w := w)) s (Inv P s₀ (c + min (blockBytes w - r) (len s₀ - c))
      (r + min (blockBytes w - r) (len s₀ - c))) := by
  have hl := ok_len hP
  have hL := len_lt s₀
  have hcn := cnt_lt s₀
  have hc := hI.c_le
  obtain ⟨a, ha⟩ : ∃ a, a = min (blockBytes w - r) (len s₀ - c) := ⟨_, rfl⟩
  rw [← ha]
  have ha₁ : a ≤ blockBytes w - r := ha ▸ Nat.min_le_left _ _
  have ha₂ : a ≤ len s₀ - c := ha ▸ Nat.min_le_right _ _
  unfold fill
  refine WP.seq (wp_mov32i fun s₁ u₁ _ _ => wp_sub fun s₂ u₂ _ => wp_cmp fun s₃ g₃ m₃ rd₃ wr₃ cf₃ _ =>
    WP.block_nil ?_)
  have hrax₂ : s₂.gpr .rax = BitVec.ofNat 64 (blockBytes w - r) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.r13, B_eq,
      MdStream.X86_64.zx_ofNat (by omega), sub_ofNat hr]
  have h12₂ : s₂.gpr .r12 = BitVec.ofNat 64 (len s₀ - c) := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), hI.r12]
  have g₂ : ∀ x, x ≠ .rax → s₃.gpr x = s.gpr x := fun x h => by rw [g₃, u₂.other x h, u₁.other x h]
  -- `rax` := `a`.
  refine WP.seq (WP.mono (Q := fun (t : State) => t.gpr .rax = BitVec.ofNat 64 a ∧
      (∀ x, x ≠ .rax → t.gpr x = s.gpr x) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ fun t ht => ?_)
  · have hm : s₃.mem = s.mem := by rw [m₃, u₂.mem, u₁.mem]
    have hrd : s₃.rd = s.rd := by rw [rd₃, u₂.rd, u₁.rd]
    have hwr : s₃.wr = s.wr := by rw [wr₃, u₂.wr, u₁.wr]
    have hcf : isa.eval .b s₃ = some (decide (len s₀ - c < blockBytes w - r)) := by
      simp only [eval, cf₃, h12₂, hrax₂, toNat_ofNat_lt (show len s₀ - c < 2 ^ 64 by omega),
        toNat_ofNat_lt (show blockBytes w - r < 2 ^ 64 by omega)]
    refine WP.ite _ hcf (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine wp_mov fun s₄ u₄ _ _ => WP.block_nil ⟨?_, fun x h => by rw [u₄.other x h, g₂ x h],
        by rw [u₄.mem, hm], by rw [u₄.rd, hrd], by rw [u₄.wr, hwr]⟩
      rw [u₄.gpr, g₃, h12₂, ha, Nat.min_eq_right (by omega)]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨?_, g₂, hm, hrd, hwr⟩
      rw [g₃, hrax₂, ha, Nat.min_eq_left (by omega)]
  obtain ⟨tax, tg, tm, trd, twr⟩ := ht
  refine WP.seq (wp_sub fun s₅ u₅ _ => wp_add fun s₆ u₆ => wp_test fun s₇ g₇ m₇ rd₇ wr₇ z₇ => WP.block_nil ?_)
  have g₇' : ∀ x, x ≠ .rax → x ≠ .r12 → x ≠ .r14 → s₇.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [g₇, u₆.other x h3, u₅.other x h2, tg x h1]
  have h7ax : s₇.gpr .rax = BitVec.ofNat 64 a := by
    rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), tax]
  have h712 : s₇.gpr .r12 = BitVec.ofNat 64 (len s₀ - (c + a)) := by
    rw [g₇, u₆.other _ (by decide), u₅.gpr, tax, tg _ (by decide), hI.r12, sub_ofNat (by omega)]
    exact congrArg _ (by omega)
  have h714 : s₇.gpr .r14 = BitVec.ofNat 64 (cnt s₀ + (c + a)) := by
    rw [g₇, u₆.gpr, u₅.other _ (by decide), u₅.other _ (by decide), tax, tg _ (by decide), hI.r14, ← BitVec.ofNat_add,
      Nat.add_assoc]
  have hm₇ : s₇.mem = s.mem := by rw [m₇, u₆.mem, u₅.mem, tm]
  have hrd₇ : s₇.rd = s.rd := by rw [rd₇, u₆.rd, u₅.rd, trd]
  have hwr₇ : s₇.wr = s.wr := by rw [wr₇, u₆.wr, u₅.wr, twr]
  have hz : isa.eval .e s₇ = some (decide (a = 0)) := by
    have e : s₆.gpr .rax = BitVec.ofNat 64 a := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), tax]
    simp only [eval, z₇, e, BitVec.and_self, ofNat_beq_zero (show a < 2 ^ 64 by omega)]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    have hg : ∀ x, x ≠ .rax → x ≠ .r12 → x ≠ .r14 → s₇.gpr x = s.gpr x := g₇'
    refine WP.block_nil ⟨⟨by omega, hrd₇.trans hI.rd, hwr₇.trans hI.wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hg _ (by decide) (by decide) (by decide)]; exact hI.rbx
    · rw [hg _ (by decide) (by decide) (by decide)]; exact hI.r15
    · rw [hg _ (by decide) (by decide) (by decide)]; exact hI.rsp
    · rw [hg _ (by decide) (by decide) (by decide), Nat.add_zero]; exact hI.rbp
    · exact h712
    · exact h714
    · rw [hm₇]; exact hI.frame
    · rw [hm₇]; exact hI.saved
    · rw [hg _ (by decide) (by decide) (by decide), Nat.add_zero]; exact hI.r13
    · rw [hm₇, Nat.add_zero]; exact hI.repr
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (copy_ok hP hp (c := c) (r := r) (k := a) (by omega) (by omega) (by omega)
      (hrd₇.trans hI.rd) (hwr₇.trans hI.wr)
      (by rw [g₇' _ (by decide) (by decide) (by decide)]; exact hI.rbx)
      (by rw [g₇' _ (by decide) (by decide) (by decide)]; exact hI.rbp)
      (by rw [g₇' _ (by decide) (by decide) (by decide)]; exact hI.r13) h7ax
      (by rw [hm₇]; exact hI.frame) (by rw [hm₇]; exact hI.saved) (by rw [hm₇]; exact hI.repr))
      fun s₈ ⟨g₈, h8bp, h813, rd₈, wr₈, f₈, sv₈, rp₈⟩ => ?_
    have e : ∀ x, x ≠ .r9 → x ≠ .rax → x ≠ .rbp → x ≠ .r13 → x ≠ .r12 → x ≠ .r14 →
        s₈.gpr x = s.gpr x := fun x h1 h2 h3 h4 h5 h6 => by rw [g₈ x h1 h2 h3 h4, g₇' x h2 h5 h6]
    refine ⟨⟨by omega, rd₈, wr₈, ?_, ?_, ?_, h8bp, ?_, ?_, f₈, sv₈⟩, h813, rp₈⟩
    · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.rbx
    · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.r15
    · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.rsp
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide)]; exact h712
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide)]; exact h714

/-- After `head`: all the data is in, with the buffer not empty, or the
buffer is empty and data is left. -/
def HeadPost (P : Params w) (s₀ : State) (s : State) : Prop :=
  ∃ c r, Inv P s₀ c r s ∧ ((c = len s₀ ∧ 1 ≤ r) ∨ (c < len s₀ ∧ r = 0))

theorem head_ok (hP : Ok P) (hf : CalleeOk P callee.code) {s₀ : State} (hp : Pre w s₀) {r : Nat}
    (hr : r ≤ blockBytes w) (hl : 0 < len s₀) {s : State} (hI : Inv P s₀ 0 r s) :
    WP isa (head (w := w) callee) s (HeadPost P s₀) := by
  have hL := len_lt s₀
  have hl' := ok_len hP
  unfold head
  refine WP.seq (WP.mono (test_ok .r13) fun s₁ ⟨g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  have hI₁ := hI.congr g₁ m₁ rd₁ wr₁
  have hz : isa.eval .e s₁ = some (decide (r = 0)) := by
    simp only [eval, z₁, hI.r13, BitVec.and_self, ofNat_beq_zero (show r < 2 ^ 64 by omega)]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact WP.block_nil ⟨0, 0, hI₁, .inr ⟨hl, rfl⟩⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (WP.mono (fill_ok hP hp hr hI₁) fun s₂ hI₂ => ?_)
    rw [Nat.zero_add, Nat.sub_zero] at hI₂
    refine WP.seq (WP.mono (test_ok .r12) fun s₃ ⟨g₃, m₃, rd₃, wr₃, z₃⟩ => ?_)
    have hI₃ := hI₂.congr g₃ m₃ rd₃ wr₃
    have hz₃ : isa.eval .e s₃ = some (decide (len s₀ - min (blockBytes w - r) (len s₀) = 0)) := by
      simp only [eval, z₃, hI₂.r12, BitVec.and_self,
        ofNat_beq_zero (show len s₀ - min (blockBytes w - r) (len s₀) < 2 ^ 64 by omega)]
    refine WP.ite _ hz₃ (fun hb' => ?_) (fun hb' => ?_)
    · simp only [decide_eq_true_eq] at hb'
      exact WP.block_nil ⟨_, _, hI₃, .inl ⟨by omega, by omega⟩⟩
    · simp only [decide_eq_false_iff_not] at hb'
      have e : r + min (blockBytes w - r) (len s₀) = blockBytes w := by omega
      rw [e] at hI₃
      exact WP.mono (compressBuf_ok hP hf hp hI₃) fun s₄ hI₄ => ⟨_, _, hI₄, .inr ⟨by omega, rfl⟩⟩

/-! ## `rest`: whole blocks straight from the data, and the last block -/

theorem ok_lg (hP : Ok P) : 1 ≤ Nat.log2 (B w) ∧ Nat.log2 (B w) ≤ 63 ∧ 2 ^ Nat.log2 (B w) = blockBytes w := by
  rw [B_eq]
  rcases hP.bb with h | h <;> rw [h]
  · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
  · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide

theorem shr_ofNat (hP : Ok P) {m : Nat} (h : m < 2 ^ 64) :
    BitVec.ofNat 64 m >>> Nat.log2 (B w) = BitVec.ofNat 64 (m / blockBytes w) := by
  obtain ⟨-, -, lgB⟩ := ok_lg hP
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow, lgB]

/-- The blocks of data but the last, straight from the data. -/
theorem direct_ok (hP : Ok P) (hf : CalleeOk P callee.code) {s₀ : State} (hp : Pre w s₀) {c : Nat}
    (hc : c < len s₀) {s : State} (hI : Inv P s₀ c 0 s) :
    WP isa (direct (w := w) callee) s (Inv P s₀ (c + blockBytes w * ((len s₀ - c - 1) / blockBytes w)) 0) := by
  have hl := ok_len hP
  have hL := len_lt s₀
  have hcn := cnt_lt s₀
  have hpos := hP.pos
  obtain ⟨lg₁, lg₂, -⟩ := ok_lg hP
  obtain ⟨k, hk⟩ : ∃ k, k = (len s₀ - c - 1) / blockBytes w := ⟨_, rfl⟩
  rw [← hk]
  have hdm := Nat.div_add_mod (len s₀ - c - 1) (blockBytes w)
  have hmod := Nat.mod_lt (len s₀ - c - 1) hpos
  rw [← hk] at hdm
  have hkle : k ≤ len s₀ - c - 1 := hk ▸ Nat.div_le_self _ _
  unfold direct
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => wp_subi fun s₂ u₂ _ => wp_shr ⟨lg₁, lg₂⟩ fun s₃ u₃ =>
    wp_test fun s₄ g₄ m₄ rd₄ wr₄ z₄ => WP.block_nil ?_)
  have hrax : s₄.gpr .rax = BitVec.ofNat 64 k := by
    rw [g₄, u₃.gpr, u₂.gpr, u₁.gpr, hI.r12, sx1, ofNat_pred (by omega), shr_ofNat hP (by omega), hk]
  have g : ∀ x, x ≠ .rax → s₄.gpr x = s.gpr x := fun x h => by
    rw [g₄, u₃.other x h, u₂.other x h, u₁.other x h]
  have hm₄ : s₄.mem = s.mem := by rw [m₄, u₃.mem, u₂.mem, u₁.mem]
  have hrd₄ : s₄.rd = s.rd := by rw [rd₄, u₃.rd, u₂.rd, u₁.rd]
  have hwr₄ : s₄.wr = s.wr := by rw [wr₄, u₃.wr, u₂.wr, u₁.wr]
  have hz : isa.eval .e s₄ = some (decide (k = 0)) := by
    have e : s₃.gpr .rax = BitVec.ofNat 64 k := by rw [← hrax, g₄]
    simp only [eval, z₄, e, BitVec.and_self, ofNat_beq_zero (show k < 2 ^ 64 by omega)]
  have hC₄ : Common w s₀ c s₄ := hI.toCommon.of_gpr (fun x hx => g x (ne_rax x hx)) hm₄ hrd₄ hwr₄
  have h13 : s₄.gpr .r13 = BitVec.ofNat 64 0 := by rw [g _ (by decide)]; exact hI.r13
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    rw [Nat.mul_zero, Nat.add_zero]
    exact WP.block_nil ⟨hC₄, h13, by rw [hm₄]; exact hI.repr⟩
  simp only [decide_eq_false_iff_not] at hb
  have hBk : blockBytes w * k + 1 ≤ len s₀ - c := by omega
  have hBk' : blockBytes w ≤ blockBytes w * k := Nat.le_mul_of_pos_right _ (by omega)
  have hsrc : Src w s₀ (dp s₀ + BitVec.ofNat 64 c) (blockBytes w * (BitVec.ofNat 64 k).toNat) :=
    .inr ⟨c, rfl, by rw [toNat_ofNat_lt (by omega)]; omega⟩
  refine WP.seq (compressWith_ok (src := dp s₀ + BitVec.ofNat 64 c) (n := BitVec.ofNat 64 k)
    (t := BitVec.ofNat 64 (cnt s₀ + c + blockBytes w)) (last := false) hf ?_
    (callOk hP hp hC₄ hsrc) fun s' hrd hwr hcs hfr hst => ?_)
  · simp only [List.cons_append, List.nil_append]
    refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₅ u₅ _ _ =>
      wp_addi fun s₆ u₆ => wp_mov32i fun s₇ u₇ _ _ => wp_mov fun s₈ u₈ _ _ => WP.block_nil ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hC₄.rbp]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hrax]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), hC₄.r14, B_eq, MdStream.X86_64.sx_ofNat (by omega),
        ← BitVec.ofNat_add]
    · rw [u₈.other _ (by decide), u₇.gpr]; rfl
    · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₃.wr, u₂.wr, u₁.wr]
    · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₃.mem, u₂.mem, u₁.mem]
  have hC' := hC₄.after_call hP hp hrd hwr hcs hfr
  refine wp_mov fun s₁ u₁ _ _ => wp_subi fun s₂ u₂ _ => wp_andi fun s₃ u₃ => wp_addi fun s₅ u₅ =>
    wp_sub fun s₆ u₆ _ => wp_add fun s₇ u₇ => wp_add fun s₈ u₈ => wp_mov fun s₉ u₉ _ _ => WP.block_nil ?_
  have hm : (len s₀ - c - 1) % blockBytes w + 1 = len s₀ - (c + blockBytes w * k) := by omega
  have hrax₅ : s₅.gpr .rax = BitVec.ofNat 64 (len s₀ - (c + blockBytes w * k)) := by
    rw [u₅.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hC'.r12, sx1, ofNat_pred (by omega), mask_mod hP,
      toNat_ofNat_lt (by omega), ← ofNat_succ, hm]
  have h12₆ : s₆.gpr .r12 = BitVec.ofNat 64 (blockBytes w * k) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hC'.r12, hrax₅, sub_ofNat (by omega)]
    exact congrArg _ (by omega)
  have hg : ∀ x, x ≠ .rax → x ≠ .r12 → x ≠ .rbp → x ≠ .r14 → s₉.gpr x = s'.gpr x := fun x h1 h2 h3 h4 => by
    rw [u₉.other x h2, u₈.other x h4, u₇.other x h3, u₆.other x h2, u₅.other x h1, u₃.other x h1,
      u₂.other x h1, u₁.other x h1]
  have hm₉ : s₉.mem = s'.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hm₉]; exact hC'.frame,
    by rw [hm₉]; exact hC'.saved⟩, ?_, fun h0 d hd => ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₃.rd, u₂.rd, u₁.rd, hC'.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₃.wr, u₂.wr, u₁.wr, hC'.wr]
  · rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact hC'.rbx
  · rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact hC'.r15
  · rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact hC'.rsp
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), h12₆,
      u₅.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      hC'.rbp, Offset.add_add]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), hrax₅]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other .r14 (by decide), u₇.other .r12 (by decide), h12₆,
      u₆.other _ (by decide), u₅.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hC'.r14, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [hg _ (by decide) (by decide) (by decide) (by decide), hcs _ (by decide), h13]
  · have hcnt := hd.cnt_eq
    have hlt := hd.2.2
    have e : d ++ D s₀ (c + blockBytes w * k) =
        d ++ D s₀ c ++ bytesAt s₄.mem (dp s₀ + BitVec.ofNat 64 c) (blockBytes w * k) := by
      rw [D, bytesAt_add, List.append_assoc]
      refine congrArg (fun l => d ++ (bytesAt s₀.mem (dp s₀) c ++ l)) (bytesAt_congr fun i hi => ?_)
      rw [Offset.add_add]
      exact (hC₄.data hp (by omega)).symm
    rw [hm₉, e]
    refine reprR_blocks P hpos (by rw [hm₄]; exact hI.repr h0 d hd) ?_
    rw [hst, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega), List.length_append, D, bytesAt_length,
      ← hcnt]

/-- The last `1` to `B` bytes of data, into the empty buffer. -/
theorem tail_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} (hc₁ : c < len s₀)
    (hc₂ : len s₀ - c ≤ blockBytes w) {s : State} (hI : Inv P s₀ c 0 s) :
    WP isa (tail (w := w)) s (Inv P s₀ (len s₀) (len s₀ - c)) := by
  have hL := len_lt s₀
  unfold tail
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => wp_add fun s₂ u₂ => wp_mov32i fun s₃ u₃ _ _ => WP.block_nil ?_)
  have hg : ∀ x, x ≠ .rax → x ≠ .r14 → x ≠ .r12 → s₃.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [u₃.other x h3, u₂.other x h2, u₁.other x h1]
  have hax : s₃.gpr .rax = BitVec.ofNat 64 (len s₀ - c) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.r12]
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (copy_ok hP hp (c := c) (r := 0) (k := len s₀ - c) (by omega) (by omega) (by omega)
      (by rw [u₃.rd, u₂.rd, u₁.rd, hI.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr, hI.wr])
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.rbx)
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.rbp)
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.r13) hax
      (by rw [hm₃]; exact hI.frame) (by rw [hm₃]; exact hI.saved) (by rw [hm₃]; exact hI.repr))
    fun s₄ ⟨g₄, h4bp, h413, rd₄, wr₄, f₄, sv₄, rp₄⟩ => ?_
  have e : c + (len s₀ - c) = len s₀ := by omega
  rw [e] at h4bp rp₄
  rw [Nat.zero_add] at h413 rp₄
  have g : ∀ x, x ≠ .r9 → x ≠ .rax → x ≠ .rbp → x ≠ .r13 → x ≠ .r14 → x ≠ .r12 →
      s₄.gpr x = s.gpr x := fun x h1 h2 h3 h4 h5 h6 => by rw [g₄ x h1 h2 h3 h4, hg x h2 h5 h6]
  refine ⟨⟨Nat.le_refl _, rd₄, wr₄, ?_, ?_, ?_, h4bp, ?_, ?_, f₄, sv₄⟩, h413, rp₄⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.rbx
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.r15
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.rsp
  · rw [g₄ _ (by decide) (by decide) (by decide) (by decide), u₃.gpr, Nat.sub_self]; rfl
  · rw [g₄ _ (by decide) (by decide) (by decide) (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), u₁.gpr, hI.r14, hI.r12, ← BitVec.ofNat_add]
    exact congrArg _ (by omega)

/-- All the data is in, and the buffer is not empty. -/
def Full (P : Params w) (s₀ : State) (s : State) : Prop := ∃ r, Inv P s₀ (len s₀) r s ∧ 1 ≤ r

theorem rest_ok (hP : Ok P) (hf : CalleeOk P callee.code) {s₀ : State} (hp : Pre w s₀) {s : State}
    (h : HeadPost P s₀ s) : WP isa (rest (w := w) callee) s (Full P s₀) := by
  have hL := len_lt s₀
  have hpos := hP.pos
  obtain ⟨c, r, hI, hcr⟩ := h
  unfold rest
  refine WP.seq (WP.mono (test_ok .r12) fun s₁ ⟨g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  have hI₁ := hI.congr g₁ m₁ rd₁ wr₁
  have hz : isa.eval .e s₁ = some (decide (len s₀ - c = 0)) := by
    simp only [eval, z₁, hI.r12, BitVec.and_self, ofNat_beq_zero (show len s₀ - c < 2 ^ 64 by omega)]
  have hc := hI.c_le
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', _⟩
    · exact WP.block_nil ⟨r, hI₁, hr⟩
    · omega
  · simp only [decide_eq_false_iff_not] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', rfl⟩
    · omega
    refine WP.seq (WP.mono (direct_ok hP hf hp hc' hI₁) fun s₂ hI₂ => ?_)
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

set_option simprocs false in
theorem epilogue_ok {s₀ : State} (hp : Pre w s₀) {s : State} (hI : Done P s₀ s) :
    WP isa (.block restore) s fun s' => gprPreserved s₀ s' ∧ (updateX86_64 P).post s₀ s' := by
  have i : ∀ d : Nat, d + 8 ≤ 512 + 48 →
      InRegions (s.rd ++ s.wr) (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨scR s₀, by simp [hI.1.rd, hI.1.wr, hp.wr], contains_offset' (by omega) (by omega)⟩
  have i0 := i 512 (by omega); have i1 := i (512 + 8) (by omega); have i2 := i (512 + 16) (by omega)
  have i3 := i (512 + 24) (by omega); have i4 := i (512 + 32) (by omega); have i5 := i (512 + 40) (by omega)
  have sv := hI.1.saved
  have g0 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((512 : Nat) : Int)) 64 = s₀.gpr .rbx :=
    sv (.rbx, 512) (by simp [Impl.MdStream.X86_64.saved, mdP])
  have g1 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((512 + 8 : Nat) : Int)) 64 = s₀.gpr .rbp :=
    sv (.rbp, 512 + 8) (by simp [Impl.MdStream.X86_64.saved, mdP])
  have g2 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((512 + 16 : Nat) : Int)) 64 = s₀.gpr .r12 :=
    sv (.r12, 512 + 16) (by simp [Impl.MdStream.X86_64.saved, mdP])
  have g3 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((512 + 24 : Nat) : Int)) 64 = s₀.gpr .r13 :=
    sv (.r13, 512 + 24) (by simp [Impl.MdStream.X86_64.saved, mdP])
  have g4 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((512 + 32 : Nat) : Int)) 64 = s₀.gpr .r14 :=
    sv (.r14, 512 + 32) (by simp [Impl.MdStream.X86_64.saved, mdP])
  have g5 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((512 + 40 : Nat) : Int)) 64 = s₀.gpr .r15 :=
    sv (.r15, 512 + 40) (by simp [Impl.MdStream.X86_64.saved, mdP])
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hI.1.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr, ret_stk s₀⟩)
      (by decide)
  have hrsp := hI.1.rsp
  have hr15 := hI.1.r15
  have hrepr := hI.2
  apply WP.of_runBlock
  rw [restore_eq', MdStream.X86_64.restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at, State.load64, mdP,
    State.setReg, hr15, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, hret⟩, fun h0 d hd hc hl => hrepr h0 d ⟨hd, hc, hl⟩⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hrsp]

theorem correct (hP : Ok P) (hf : CalleeOk P callee.code) {s₀ : State} (hp : Pre w s₀) :
    WP isa (update P callee) s₀ fun s' => gprPreserved s₀ s' ∧ (updateX86_64 P).post s₀ s' := by
  have hL := len_lt s₀
  unfold update
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hC, hm⟩ => ?_)
  refine WP.seq (WP.mono (bufLen_ok hP hp hC hm) fun s₂ hI => ?_)
  refine WP.seq (WP.mono (test_ok .r12) fun s₃ ⟨g₃, m₃, rd₃, wr₃, z₃⟩ => ?_)
  have hI₃ := hI.congr g₃ m₃ rd₃ wr₃
  refine WP.seq (WP.mono (Q := Done P s₀) ?_ fun s₄ h => epilogue_ok hp h)
  have hz : isa.eval .e s₃ = some (decide (len s₀ = 0)) := by
    simp only [eval, z₃, hI.r12, BitVec.and_self, Nat.sub_zero,
      ofNat_beq_zero (show len s₀ < 2 ^ 64 by omega)]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.block_nil ⟨by rw [hb]; exact hI₃.toCommon, fun h0 d hd => ?_⟩
    have := hI₃.repr h0 d hd
    have e0 : ∀ n, n = 0 → bytesAt s₀.mem (dp s₀) n = [] := by rintro _ rfl; simp [bytesAt]
    rw [show D s₀ 0 = [] from e0 _ rfl, List.append_nil] at this
    rw [show D s₀ (len s₀) = [] from e0 _ hb, List.append_nil]
    rw [repr_iff P hP.pos, ← hd.cnt_eq]; exact this
  · simp only [decide_eq_false_iff_not] at hb
    have hr := bufLen_le (w := w) hP.pos (cnt s₀)
    exact WP.seq (WP.mono (head_ok hP hf hp hr (by omega) hI₃) fun s₄ h =>
      WP.mono (rest_ok hP hf hp h) fun s₅ h => h.done hP)

end VG.Proof.Blake2.X86_64.Stream.Update
