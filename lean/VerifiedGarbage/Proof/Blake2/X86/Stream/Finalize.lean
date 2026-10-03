import VerifiedGarbage.Proof.Blake2.X86.Stream.Common
import VerifiedGarbage.Proof.Framework.Range

/-!
# Streaming BLAKE2 on x86 (32-bit): `finalize`

`finalize` saves the callee-saved registers (`prologue_ok`), computes the
number of buffered bytes (`bufLen_val`), zeroes the rest of the buffer
(`pad_ok`), compresses it as the last block (`call_ok`), copies the hash value
out (`output_ok`) and restores the registers (`epilogue_ok`), for either word
size and any correct compression function (`CalleeOk`).
-/

namespace VG.Proof.Blake2.X86.Stream.Finalize

open VG VG.X86 VG.X86.Wp VG.Spec.Blake2
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.Stream
open VG.Proof.Blake2 (compressX86 finalizeX86 countX86 final_eq stateAt_congr bytesAt_congr bytesAt_add
  bytesAt_state wordBytes_readW bufLen_le compressBlocks_succ compressBlocks_zero)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_append
  writeBytes_before write_eq_writeBytes)
open VG.Proof.MdStream.X86 (contains_addr sub_offset contains_offset)

variable {w : Nat} {P : Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev cnt : Nat := (countX86 s₀).toNat
abbrev op : BitVec 32 := arg s₀ 3
abbrev scr : BitVec 32 := arg s₀ 4
abbrev stA : Addr := (st s₀).setWidth 64
abbrev opA : Addr := (op s₀).setWidth 64
abbrev scA : Addr := (scr s₀).setWidth 64
abbrev stR (w : Nat) : Region := ⟨stA s₀, bufOff w + blockBytes w⟩
abbrev outR (w : Nat) : Region := ⟨opA s₀, bufOff w⟩
abbrev scR : Region := ⟨scA s₀, 576⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
/-- Where the call of the compression function pushes its arguments and
stores the return address. -/
abbrev stkR : Region := below (esp₀ s₀) 32

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [stR s₀ w, outR s₀ w, scR s₀]
  st_out : (stR s₀ w).Disjoint (outR s₀ w)
  st_scr : (stR s₀ w).Disjoint (scR s₀)
  out_scr : (outR s₀ w).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀ w)
  a_out : (argR s₀).Disjoint (outR s₀ w)
  a_scr : (argR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀ w)
  ret_out : (retR s₀).Disjoint (outR s₀ w)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀ w)
  stk_out : (stkR s₀).Disjoint (outR s₀ w)
  stk_scr : (stkR s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32
  out_fit : (op s₀).toNat + bufOff w ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 576 ≤ 2 ^ 32
  sp_lo : 32 ≤ (esp₀ s₀).toNat
  sp_fit : (esp₀ s₀).toNat + 24 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : (finalizeX86 P).pre s₀) : Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  have e := stk_eq h18
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    by show (below _ _).Disjoint _; rw [e]; exact h12, by show (below _ _).Disjoint _; rw [e]; exact h13,
    by show (below _ _).Disjoint _; rw [e]; exact h14, h15, h16, h17, h18, h19⟩

namespace Pre
variable {s₀ : State} (hp : Pre w s₀)
include hp

theorem scr_in {d : Nat} (hd : d + 4 ≤ 576) : (scR s₀).Contains (addr (scr s₀) d) 4 :=
  contains_addr hd (by omega) hp.scr_fit

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  show (⟨addr (esp₀ s₀) 4, 20⟩ : Region).Contains _ _
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ hd₁ (by omega) (by omega)

theorem rin {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 24) :
    InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [hrd, hp.rd], hp.arg_in h₁ h₂⟩

theorem sin {s : State} (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 576) :
    InRegions s.wr (addr (scr s₀) d) 4 :=
  ⟨scR s₀, by simp [hwr, hp.wr], hp.scr_in hd⟩

theorem sinr {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 576) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
  ⟨scR s₀, by simp [hrd, hwr, hp.wr], hp.scr_in hd⟩

theorem ret_stk : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨(esp₀ s₀).setWidth 64, 4⟩ ⟨(esp₀ s₀ - BitVec.ofNat 32 32).setWidth 64, 32⟩
  rw [Taint.sub_setWidth (by omega)]
  exact Offset.base_disjoint_below _ (by omega)

theorem a_stk : (argR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨addr (esp₀ s₀) 4, 20⟩ ⟨(esp₀ s₀ - BitVec.ofNat 32 32).setWidth 64, 32⟩
  rw [addr_eq (by omega), Taint.sub_setWidth (by omega)]
  exact Offset.disjoint_below _ (by omega)

theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  show Region.Sub _ ⟨addr (esp₀ s₀) 4, 20⟩
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sub _ hd₁ (by omega)

end Pre

/-! ## The prologue -/

/-- After the prologue. -/
structure Start (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  ebp : s.gpr .ebp = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  eax : s.gpr .eax = arg s₀ 1
  ecx : s.gpr .ecx = arg s₀ 2
  mem : s.mem = saveMem (scr s₀) s₀

theorem prologue_ok {s₀ : State} (hp : Pre w s₀) : WP isa (.block finalizeStart) s₀ (Start s₀) := by
  have rin : ∀ {d}, 4 ≤ d → d + 4 ≤ 24 → InRegions (s₀.rd ++ s₀.wr) (addr (esp₀ s₀) d) 4 :=
    fun h₁ h₂ => hp.rin rfl h₁ h₂
  have sin : ∀ {d}, d + 4 ≤ 576 → InRegions s₀.wr (addr (scr s₀) d) 4 := fun h => hp.sin rfl h
  have sepA : ∀ d e, 512 ≤ d → d + 4 ≤ 576 → 4 ≤ e → e + 4 ≤ 24 →
      Mem.Sep (addr (esp₀ s₀) e) 4 (addr (scr s₀) d) 4 := by
    intro d e h₁ h₂ h₃ h₄
    exact hp.a_scr.sep (hp.arg_in h₃ h₄) (hp.scr_in h₂)
  have argSave : ∀ e, 4 ≤ e → e + 4 ≤ 24 →
      (saveMem (scr s₀) s₀).readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 := by
    intro e h₁ h₂
    exact Spill.saveMem_readW_of_sep _ _ (by decide) _ _ fun p h =>
      have := saved_bound p h; sepA _ e this.1 (by omega) h₁ h₂
  rw [show finalizeStart = .mov .eax (.mem (at_ .esp 20)) :: (Spill.saveCode .eax saved ++
    ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .eax (.mem (at_ .esp 8)),
      .mov .ecx (.mem (at_ .esp 12))] : List Instr)) from rfl]
  refine wp_ldm (B := esp₀ s₀) rfl (rin (d := 20) (by omega) (by omega)) fun s₁ u₁ => ?_
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
  refine wp_mov fun s₆ u₆ => ?_
  have sp₆ : s₆.gpr .esp = esp₀ s₀ := by rw [u₆.other _ (by decide), sp₅]
  have rd' : ∀ d, 4 ≤ d → d + 4 ≤ 24 → InRegions (s₆.rd ++ s₆.wr) (addr (esp₀ s₀) d) 4 :=
    fun d h₁ h₂ => by rw [u₆.rd, u₆.wr, rd₅, wr₅]; exact rin h₁ h₂
  have l : ∀ e, 4 ≤ e → e + 4 ≤ 24 → s₆.mem.readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 :=
    fun e h₁ h₂ => by rw [u₆.mem, m₅]; exact argSave e h₁ h₂
  refine wp_ldm sp₆ (rd' 4 (by omega) (by omega)) fun s₇ u₇ => ?_
  refine wp_ldm (by rw [u₇.other _ (by decide), sp₆]) (by rw [u₇.rd, u₇.wr]; exact rd' 8 (by omega) (by omega))
    fun s₈ u₈ => ?_
  refine wp_ldm (by rw [u₈.other _ (by decide), u₇.other _ (by decide), sp₆])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr]; exact rd' 12 (by omega) (by omega)) fun s₉ u₉ => WP.block_nil ?_
  refine ⟨by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅], by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅], ?_, ?_, ?_, ?_, ?_,
    by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, l 4 (by omega) (by omega)]; rfl
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅, e₁]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), sp₆]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.mem, l 8 (by omega) (by omega)]; rfl
  · rw [u₉.gpr, u₈.mem, u₇.mem, l 12 (by omega) (by omega)]; rfl

/-! ## The number of buffered bytes -/

theorem bufLen_val (hP : Ok P) {s : State} {lo hi : BitVec 32} (hax : s.gpr .eax = lo)
    (hcx : s.gpr .ecx = hi) :
    WP isa (Impl.Blake2.X86.Stream.bufLen w) s fun s' =>
      s'.gpr .eax = BitVec.ofNat 32 (Proof.Blake2.bufLen w (hi ++ lo).toNat) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold Impl.Blake2.X86.Stream.bufLen
  refine WP.seq (wp_orZ fun s₁ u₁ z₁ => WP.block_nil ?_)
  have hz : isa.eval .e s₁ = some (decide ((hi ++ lo).toNat = 0)) := by
    show s₁.zf = _
    rw [z₁, hcx, hax, or_beq_zero]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_movi fun s₂ u₂ => WP.block_nil ⟨?_, fun r h1 h2 => by rw [u₂.other r h1, u₁.other r h2],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
    rw [u₂.gpr, hb]; rfl
  · simp only [decide_eq_false_iff_not] at hb
    refine wp_subi fun s₂ u₂ _ _ => wp_andi fun s₃ u₃ => wp_addi fun s₄ u₄ => WP.block_nil
      ⟨?_, fun r h1 h2 => by rw [u₄.other r h1, u₃.other r h1, u₂.other r h1, u₁.other r h2],
        by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
        by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
    have e : lo = BitVec.ofNat 32 (hi ++ lo).toNat := (lo_append hi lo).symm
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hax]
    conv_lhs => rw [e]
    rw [mask_ofNat hP hb]
    simp only [Proof.Blake2.bufLen, hb, ite_false]

/-! ## Zeroing the rest of the buffer -/

/-- The zeroing loop's state after `j` of `k` bytes, from `s₀`. -/
structure ZI (s₀ : State) (dA : BitVec 32) (k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  edx : s.gpr .edx = dA + BitVec.ofNat 32 j
  ecx : s.gpr .ecx = BitVec.ofNat 32 (k - j)
  other : ∀ x, x ≠ .edx → x ≠ .ecx → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes s₀.mem (addr dA (bufOff w)) (List.replicate j 0)

/-- The loop zeroing `k ≥ 1` bytes at `dA + N` (at `edx`, `eax = 0`). -/
theorem zeroLoop_ok {s₀ : State} {dA : BitVec 32} {k : Nat} (hk : 1 ≤ k) (hk32 : k < 2 ^ 32)
    (hfd : dA.toNat + bufOff w + k ≤ 2 ^ 32)
    (hdx : s₀.gpr .edx = dA) (hcx : s₀.gpr .ecx = BitVec.ofNat 32 k) (hax : s₀.gpr .eax = 0)
    (hout : ∀ i < k, InRegions s₀.wr (addr dA (bufOff w) + BitVec.ofNat 64 i) 1)
    {Q : State → Prop} (hQ : ∀ s, ZI (w := w) s₀ dA k k s → Q s) :
    WP isa (zeroLoop w) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧ ZI (w := w) s₀ dA k j s) ?_ k s₀
    ⟨0, by omega, by omega, by omega, by simp [hdx], by rw [hcx, Nat.sub_zero], fun _ _ _ => rfl, rfl, rfl,
      by rw [List.replicate_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have eD : addr (s.gpr .edx) (bufOff w) = addr dA (bufOff w) + BitVec.ofNat 64 j := by
    rw [h.edx, MdStream.X86.addr_add_ofNat (by omega), addr_eq (by omega), BitVec.add_assoc,
      BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 j)]
  have hout' : InRegions s.wr (addr dA (bufOff w) + BitVec.ofNat 64 j) 1 := by rw [h.wr]; exact hout j hj
  set m₁ := s.mem.writeW (addr dA (bufOff w) + BitVec.ofNat 64 j) ((s.gpr Reg8.al.reg).setWidth 8) with hm₁
  refine cons (s' := { s with mem := m₁ }) ?_ ?_
  · have e : s.ea (at_ .edx (N w)) = addr dA (bufOff w) + BitVec.ofNat 64 j := eD
    simp only [exec, State.store8, e, hout', ite_true, hm₁]
  refine wp_addi fun s₂ u₂ => wp_subi fun s₃ u₃ _ hz₃ => WP.block_nil ?_
  have e₁ : ∀ r, ({ s with mem := m₁ } : State).gpr r = s.gpr r := fun _ => rfl
  have hcx' : s₃.gpr .ecx = BitVec.ofNat 32 (k - (j + 1)) := by
    rw [u₃.gpr, u₂.other _ (by decide), e₁, h.ecx, ofNat_pred (by omega), Nat.sub_sub]
  have hI : ZI (w := w) s₀ dA k (j + 1) s₃ := by
    refine ⟨by omega, ?_, hcx', fun x h1 h2 => ?_, ?_, ?_, ?_⟩
    · rw [u₃.other _ (by decide), u₂.gpr, e₁, h.edx, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    · rw [u₃.other x h2, u₂.other x h1]; exact h.other x h1 h2
    · rw [u₃.rd, u₂.rd]; exact h.rd
    · rw [u₃.wr, u₂.wr]; exact h.wr
    · rw [u₃.mem, u₂.mem]
      show m₁ = _
      rw [hm₁, show Reg8.al.reg = Reg.eax from rfl, h.other .eax (by decide) (by decide), hax, h.mem,
        List.replicate_succ',
        writeBytes_snoc _ _ _ _ (by simp; omega), List.length_replicate]
      rfl
  have hzf : s₃.zf = some (decide (k - (j + 1) = 0)) := by
    rw [hz₃, u₂.other _ (by decide), e₁, h.ecx, ofNat_pred (show 1 ≤ k - j by omega), ofNat_beq_zero (by omega),
      show k - j - 1 = k - (j + 1) by omega]
  by_cases hjk : j + 1 = k
  · refine .inl ⟨?_, hQ _ (hjk ▸ hI)⟩
    simp only [eval, hzf, show k - (j + 1) = 0 by omega, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩
    simp only [eval, hzf, show k - (j + 1) ≠ 0 by omega, decide_false, Option.map_some, Bool.not_false]

/-- Zeroing the buffer of the state at `ebx` (`st`) from byte `eax` (`r`) on. -/
theorem pad_ok (hP : Ok P) {s : State} {st : BitVec 32} {r : Nat} (hr : r ≤ blockBytes w)
    (hfit : st.toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32)
    (hbx : s.gpr .ebx = st) (hax : s.gpr .eax = BitVec.ofNat 32 r)
    (hdst : ∀ i < blockBytes w - r, InRegions s.wr (addr st (bufOff w + r) + BitVec.ofNat 64 i) 1) :
    WP isa (pad w) s fun s' =>
      (∀ x, x ≠ .eax → x ≠ .ecx → x ≠ .edx → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem (addr st (bufOff w + r)) (List.replicate (blockBytes w - r) 0) := by
  have hl := hP.len
  unfold pad
  refine WP.seq (wp_mov fun s₁ u₁ => wp_add fun s₂ u₂ _ => wp_movi fun s₃ u₃ => wp_sub fun s₄ u₄ z₄ =>
    wp_moviF fun s₅ u₅ _ zf₅ => WP.block_nil ?_)
  have g : ∀ x, x ≠ .eax → x ≠ .ecx → x ≠ .edx → s₅.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [u₅.other x h1, u₄.other x h2, u₃.other x h2, u₂.other x h3, u₁.other x h3]
  have hcx : s₅.gpr .ecx = BitVec.ofNat 32 (blockBytes w - r) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hax, B_eq, sub_ofNat hr]
  have hdx : s₅.gpr .edx = st + BitVec.ofNat 32 r := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr,
      u₁.other _ (by decide), hbx, hax]
  have hz : isa.eval .e s₅ = some (decide (blockBytes w - r = 0)) := by
    show s₅.zf = _
    rw [zf₅, z₄, ← u₄.gpr, ← u₅.other .ecx (by decide), hcx, ofNat_beq_zero (by omega)]
  have hm₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hwr : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hrd : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  refine WP.ite _ hz (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨g, hrd, hwr, ?_⟩
    rw [hb, List.replicate_zero, writeBytes_nil, hm₅]
  · simp only [decide_eq_false_iff_not] at hb
    have e : addr (st + BitVec.ofNat 32 r) (bufOff w) = addr st (bufOff w + r) := by
      rw [MdStream.X86.addr_add_ofNat (by omega), addr_eq (by omega), Nat.add_comm]
    refine zeroLoop_ok (w := w) (dA := st + BitVec.ofNat 32 r) (by omega) (by omega)
      (by rw [toNat_add_ofNat (by omega)]; omega) hdx hcx u₅.gpr
      (fun i hi => by rw [hwr, e]; exact hdst i hi) fun s' h => ?_
    refine ⟨fun x h1 h2 h3 => by rw [h.other x h3 h2, g x h1 h2 h3], by rw [h.rd, hrd], by rw [h.wr, hwr], ?_⟩
    rw [h.mem, hm₅, e]

/-! ## Bytes -/

theorem writeW_eq (m : Mem) (a : Addr) (v : BitVec 32) : m.writeW a v = writeBytes m a (wordBytes v) := by
  rw [Mem.writeW, write_eq_writeBytes]; rfl

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) = if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes]
  rw [show q + BitVec.ofNat 64 i - q = BitVec.ofNat 64 i by rw [BitVec.add_comm]; exact BitVec.add_sub_cancel _ _,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} {n : Nat} (hn : xs.length = n)
    (h : n < 2 ^ 64) : bytesAt (writeBytes m q xs) q n = xs := by
  subst hn
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- The buffer after zeroing it from byte `r` on. -/
theorem pad_bytes {m m' : Mem} {st : Addr} {N r bb : Nat} (hr : r ≤ bb) (hlt : N + bb < 2 ^ 64)
    (hm : m' = writeBytes m (st + BitVec.ofNat 64 (N + r)) (List.replicate (bb - r) 0)) :
    bytesAt m' (st + BitVec.ofNat 64 N) bb =
      bytesAt m (st + BitVec.ofNat 64 N) r ++ List.replicate (bb - r) 0 := by
  conv_lhs => rw [show bb = r + (bb - r) by omega]
  rw [bytesAt_add, Offset.add_ofNat_add_ofNat]
  congr 1
  · refine bytesAt_congr fun i hi => ?_
    rw [hm, Offset.add_ofNat_add_ofNat,
      writeBytes_before m st _ (by omega : N + i < N + r) (by simp; omega)]
  · rw [hm]; exact bytesAt_writeBytes_self _ _ (by simp) (by omega)

/-! ## Copying the hash value out -/

/-- After copying `k` words. -/
def OInv (σ : State) (k : Nat) (s : State) : Prop :=
  (∀ r, r ≠ .ecx → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧
    s.mem = writeBytes σ.mem ((σ.gpr .eax).setWidth 64) (bytesAt σ.mem ((σ.gpr .ebx).setWidth 64) (4 * k))

theorem output_ok {σ : State} (hN4 : bufOff w % 4 = 0)
    (hfs : (σ.gpr .ebx).toNat + bufOff w ≤ 2 ^ 32) (hfo : (σ.gpr .eax).toNat + bufOff w ≤ 2 ^ 32)
    (hin : ∀ a n, (⟨(σ.gpr .ebx).setWidth 64, bufOff w⟩ : Region).Contains a n → InRegions (σ.rd ++ σ.wr) a n)
    (hout : ∀ a n, (⟨(σ.gpr .eax).setWidth 64, bufOff w⟩ : Region).Contains a n → InRegions σ.wr a n)
    (hd : Region.Disjoint ⟨(σ.gpr .ebx).setWidth 64, bufOff w⟩ ⟨(σ.gpr .eax).setWidth 64, bufOff w⟩) :
    WP isa (.block (output w)) σ fun s =>
      (∀ r, r ≠ .ecx → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧
      s.mem = writeBytes σ.mem ((σ.gpr .eax).setWidth 64)
        (bytesAt σ.mem ((σ.gpr .ebx).setWidth 64) (bufOff w)) := by
  have e : 4 * (Impl.Blake2.X86.Stream.N w / 4) = bufOff w := by rw [N_eq]; omega
  unfold output
  rw [← e]
  refine wp_range_flatMap (M := isa) (OInv σ) (fun k s hk ⟨hg, hrd, hwr, hm⟩ => ?_) _ (Nat.le_refl _) σ
    ⟨fun _ _ => rfl, rfl, rfl, by rw [Nat.mul_zero]; simp [bytesAt, writeBytes_nil]⟩
  rw [N_eq] at hk
  have hk4 : 4 * k + 4 ≤ bufOff w := by omega
  have hl : (bytesAt σ.mem ((σ.gpr .ebx).setWidth 64) (4 * k)).length = 4 * k := by simp [bytesAt]
  have eS : addr (σ.gpr .ebx) (4 * k) = (σ.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_eq (by omega)
  have eO : addr (σ.gpr .eax) (4 * k) = (σ.gpr .eax).setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_eq (by omega)
  refine wp_ldm (B := σ.gpr .ebx) (by rw [hg _ (by decide)])
    (by rw [hrd, hwr, eS]; exact hin _ _ (Offset.contains_base _ hk4 (by omega))) fun s₁ u₁ => ?_
  refine wp_stm (B := σ.gpr .eax) (by rw [u₁.other _ (by decide), hg _ (by decide)])
    (by rw [u₁.wr, hwr, eO]; exact hout _ _ (Offset.contains_base _ hk4 (by omega))) fun s₂ u₂ =>
      WP.block_nil ⟨fun r hr => by rw [u₂.gpr, u₁.other r hr, hg r hr], by rw [u₂.rd, u₁.rd, hrd],
        by rw [u₂.wr, u₁.wr, hwr], ?_⟩
  have hv : s.mem.readW (addr (σ.gpr .ebx) (4 * k)) 32 = σ.mem.readW (addr (σ.gpr .ebx) (4 * k)) 32 := by
    rw [hm, eS]
    exact (writeBytes_frame (R := ⟨(σ.gpr .eax).setWidth 64, bufOff w⟩) _ _ _
      (contains_prefix _ (by omega))).readW
      (Offset.contains_base (k := bufOff w) _ hk4 (by omega)) (by simpa using hd) (by decide)
  have e' := writeBytes_append σ.mem ((σ.gpr .eax).setWidth 64) (bytesAt σ.mem ((σ.gpr .ebx).setWidth 64) (4 * k))
    (wordBytes (σ.mem.readW ((σ.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (4 * k)) 32))
    (by rw [hl]; simp [wordBytes]; omega)
  rw [hl] at e'
  rw [u₂.mem, u₁.gpr, u₁.mem, hv, hm, eO, eS, writeW_eq, e', wordBytes_readW _ _ (.inl rfl),
    ← bytesAt_add, Nat.mul_succ]

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre w s₀) {s : State} (hbp : s.gpr .ebp = scr s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsv : Saved (scr s₀) s₀ s.mem) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ calleeSaved, r ≠ .esp → s'.gpr r = s₀.gpr r) ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem :=
  restore_saved hbp (fun d _ hd => hp.sinr hrd hwr (by omega)) hsv

/-! ## The whole function -/

theorem compressBlocks_one (h : HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    compressBlocks P h m p 1 t f = F P h (blockAt w m p) t f := by
  rw [show (1 : Nat) = 0 + 1 from rfl, compressBlocks_succ, compressBlocks_zero]; simp

/-- The arguments are kept by writes to the writable buffers and below the
stack. -/
theorem arg_keep {s₀ : State} (hp : Pre w s₀) {m : Mem}
    (hf : Frame [stR s₀ w, outR s₀ w, scR s₀, stkR s₀] s₀.mem m) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 24) :
    m.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 := by
  refine hf.readW (r := ⟨addr (esp₀ s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.a_st.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_out.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_scr.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_stk.sub_left (hp.arg_sub h₁ h₂)

theorem correct (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) :
    WP isa (finalize w name code) s₀ fun s' => abiPreserved s₀ s' ∧ (finalizeX86 P).post s₀ s' := by
  have hl := hP.len
  have hpos := hP.pos
  have hN := hP.N
  have fS := hp.st_fit; have fO := hp.out_fit; have fC := hp.scr_fit
  have hstN : Region.Sub ⟨stA s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega)
  have hsc : Region.Sub ⟨scA s₀, 512⟩ (scR s₀) := Region.sub_prefix (by omega)
  have eB : (st s₀ + BitVec.ofNat 32 (bufOff w)).setWidth 64 = stA s₀ + BitVec.ofNat 64 (bufOff w) :=
    sw_add (by omega)
  have hbuf : Region.Sub ⟨stA s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩ (stR s₀ w) :=
    Offset.sub_base _ (by omega)
  unfold finalize
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have F₁ : Frame [scR s₀] s₀.mem s₁.mem := by rw [h₁.mem]; exact saveMem_frame hp.scr_fit s₀
  refine WP.seq (WP.mono (bufLen_val hP h₁.eax h₁.ecx) fun s₂ ⟨ax₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  generalize hr : Proof.Blake2.bufLen w (arg s₀ 2 ++ arg s₀ 1).toNat = r at ax₂
  have hrB : r ≤ blockBytes w := hr ▸ bufLen_le hpos _
  have bx₂ : s₂.gpr .ebx = st s₀ := by rw [g₂ _ (by decide) (by decide), h₁.ebx]
  have eP : r < blockBytes w → addr (st s₀) (bufOff w + r) = stA s₀ + BitVec.ofNat 64 (bufOff w + r) :=
    fun h => addr_eq (by omega)
  refine WP.seq (WP.mono (pad_ok hP hrB fS bx₂ ax₂ fun i hi => ?_) fun s₃ ⟨g₃, rd₃, wr₃, m₃⟩ => ?_)
  · rw [wr₂, h₁.wr, hp.wr, eP (by omega), Offset.add_add]
    exact ⟨stR s₀ w, by simp, contains_offset (by omega) (by omega)⟩
  have hm₃ : s₃.mem = writeBytes s₁.mem (stA s₀ + BitVec.ofNat 64 (bufOff w + r))
      (List.replicate (blockBytes w - r) 0) := by
    rw [m₃, m₂]
    by_cases h : r < blockBytes w
    · rw [eP h]
    · rw [show blockBytes w - r = 0 by omega, List.replicate_zero, writeBytes_nil, writeBytes_nil]
  have F₃ : Frame [stR s₀ w] s₁.mem s₃.mem := by
    rw [hm₃]; exact writeBytes_frame _ _ _ (contains_offset (by simp; omega) (by omega))
  have F₀₃ : Frame [stR s₀ w, outR s₀ w, scR s₀, stkR s₀] s₀.mem s₃.mem :=
    (F₁.mono (by simp)).trans (F₃.mono (by simp))
  have g₃' : ∀ x, x ≠ .eax → x ≠ .ecx → x ≠ .edx → s₃.gpr x = s₁.gpr x := fun x h1 h2 h3 => by
    rw [g₃ x h1 h2 h3, g₂ x h1 h2]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, h₁.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, h₁.wr]
  have sp₃ : s₃.gpr .esp = esp₀ s₀ := by rw [g₃' _ (by decide) (by decide) (by decide), h₁.esp]
  -- The call.
  refine WP.seq ?_
  unfold compressLast
  refine WP.seq (wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => wp_movi fun s₆ u₆ => wp_movi fun s₇ u₇ => ?_)
  have g₇ : ∀ x, x ≠ .esi → x ≠ .edi → x ≠ .eax → s₇.gpr x = s₃.gpr x := fun x h1 h2 h3 => by
    rw [u₇.other x h3, u₆.other x h2, u₅.other x h1, u₄.other x h1]
  have m₇ : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃']
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃']
  have sp₇ : s₇.gpr .esp = esp₀ s₀ := by rw [g₇ _ (by decide) (by decide) (by decide), sp₃]
  refine wp_ldm sp₇ (hp.rin rd₇ (d := 8) (by omega) (by omega)) fun s₈ u₈ => ?_
  have i12 := hp.rin rd₇ (d := 12) (by omega) (by omega)
  refine wp_ldm (by rw [u₈.other _ (by decide), sp₇]) (by rw [u₈.rd, u₈.wr]; exact i12) fun s₉ u₉ => WP.block_nil ?_
  have g₉ : ∀ x, x ≠ .esi → x ≠ .edi → x ≠ .eax → x ≠ .ecx → x ≠ .edx → s₉.gpr x = s₁.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [u₉.other x h5, u₈.other x h4, g₇ x h1 h2 h3, g₃' x h3 h4 h5]
  have m₉ : s₉.mem = s₃.mem := by rw [u₉.mem, u₈.mem, m₇]
  have rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, rd₇]
  have wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, wr₇]
  have cx₉ : s₉.gpr .ecx = arg s₀ 1 := by
    rw [u₉.other _ (by decide), u₈.gpr, m₇, arg_keep hp F₀₃ (by omega) (by omega)]; rfl
  have dx₉ : s₉.gpr .edx = arg s₀ 2 := by
    rw [u₉.gpr, u₈.mem, m₇, arg_keep hp F₀₃ (by omega) (by omega)]; rfl
  have esp₉ : s₉.gpr .esp = esp₀ s₀ := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.esp]
  refine call_ok (P := P) hf (k := 1) esp₉
    (by rw [g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.ebx])
    (by rw [g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.ebp])
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.gpr, u₄.gpr, g₃' _ (by decide) (by decide) (by decide), h₁.ebx, N_eq])
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]; rfl)
    cx₉ dx₉ (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]) hp.sp_lo (by omega)
    (by rw [toNat_add_ofNat (by omega)]; omega) (by omega)
    ((hp.st_scr.sub_left hstN).sub_right hsc) (by rw [eB]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega))
    (by rw [eB, Nat.mul_one]; exact (hp.st_scr.sub_left hbuf).sub_right hsc) (hp.stk_st.sub_right hstN)
    (hp.stk_scr.sub_right hsc) (by rw [eB, Nat.mul_one]; exact hp.stk_st.sub_right hbuf) ?_ ?_ fun s₁₀ rd₁₀ wr₁₀ cs₁₀ f₁₀ e₁₀ => ?_
  · rw [rd₉, wr₉, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀ w, by simp, bufOff w, by rw [eB], by simp only; omega⟩
  · rw [wr₉, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp only; omega⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp only; omega⟩
  have sp₁₀ : s₁₀.gpr .esp = esp₀ s₀ := by rw [cs₁₀ _ (by decide), esp₉]
  have bx₁₀ : s₁₀.gpr .ebx = st s₀ := by
    rw [cs₁₀ _ (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.ebx]
  have bp₁₀ : s₁₀.gpr .ebp = scr s₀ := by
    rw [cs₁₀ _ (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.ebp]
  have rd₁₀' : s₁₀.rd = s₀.rd := rd₁₀.trans rd₉
  have wr₁₀' : s₁₀.wr = s₀.wr := wr₁₀.trans wr₉
  have F₃₁₀ : Frame [stR s₀ w, outR s₀ w, scR s₀, stkR s₀] s₃.mem s₁₀.mem := by
    rw [← m₉]
    refine f₁₀.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀ w, by simp, hstN⟩
    · exact ⟨scR s₀, by simp, hsc⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  have F₀₁₀ := F₀₃.trans F₃₁₀
  refine wp_ldm sp₁₀ (hp.rin rd₁₀' (d := 16) (by omega) (by omega)) fun s₁₁ u₁₁ => ?_
  have ax₁₁ : s₁₁.gpr .eax = op s₀ := by rw [u₁₁.gpr, arg_keep hp F₀₁₀ (by omega) (by omega)]; rfl
  have bx₁₁ : s₁₁.gpr .ebx = st s₀ := by rw [u₁₁.other _ (by decide), bx₁₀]
  rw [show (output w).append restore = output w ++ restore from rfl, WP.block_append_iff]
  have hN4 : bufOff w % 4 = 0 := by rcases hP.bb with h | h <;> omega
  refine WP.mono (output_ok (σ := s₁₁) hN4 (by rw [bx₁₁]; omega) (by rw [ax₁₁]; omega)
    (fun a n h => ?_) (fun a n h => ?_) (by rw [bx₁₁, ax₁₁]; exact hp.st_out.sub_left hstN))
    fun s₁₂ ⟨g₁₂, rd₁₂, wr₁₂, m₁₂⟩ => ?_
  · rw [u₁₁.rd, u₁₁.wr, rd₁₀', wr₁₀', hp.rd, hp.wr]
    rw [bx₁₁] at h
    exact ⟨stR s₀ w, by simp, by simp only [Region.Contains, stA] at h ⊢; omega⟩
  · rw [u₁₁.wr, wr₁₀', hp.wr]
    rw [ax₁₁] at h
    exact ⟨outR s₀ w, by simp, h⟩
  have F₁₂ : Frame [outR s₀ w] s₁₁.mem s₁₂.mem := by
    rw [m₁₂, ax₁₁]
    exact writeBytes_frame _ _ _ (contains_prefix _ (by simp [bytesAt]))
  -- The saved registers.
  have sv₁ : Saved (scr s₀) s₀ s₁.mem := by rw [h₁.mem]; exact saveMem_saved hp.scr_fit s₀
  have sv₃ : Saved (scr s₀) s₀ s₃.mem :=
    Saved.keep hp.scr_fit sv₁ (F₃.mono fun r hr => List.mem_cons_of_mem _ hr) (by simpa using hp.st_scr.symm)
  have f₁₀' : Frame [⟨scA s₀, 512⟩, ⟨stA s₀, bufOff w⟩, stkR s₀] s₉.mem s₁₀.mem :=
    f₁₀.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp
  have sv₁₀ : Saved (scr s₀) s₀ s₁₀.mem :=
    Saved.keep hp.scr_fit (by rw [m₉]; exact sv₃) f₁₀' (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨(hp.st_scr.sub_left hstN).symm, hp.stk_scr.symm⟩)
  have sv₁₂ : Saved (scr s₀) s₀ s₁₂.mem :=
    Saved.keep hp.scr_fit (by rw [← u₁₁.mem] at sv₁₀; exact sv₁₀) (F₁₂.mono fun r hr => List.mem_cons_of_mem _ hr)
      (by simpa using hp.out_scr.symm)
  have bp₁₂ : s₁₂.gpr .ebp = scr s₀ := by rw [g₁₂ _ (by decide), u₁₁.other _ (by decide), bp₁₀]
  refine WP.mono (restore_ok hp bp₁₂ (by rw [rd₁₂, u₁₁.rd, rd₁₀']) (by rw [wr₁₂, u₁₁.wr, wr₁₀']) sv₁₂)
    fun s₁₃ ⟨cs₁₃, sp₁₃, m₁₃⟩ => ?_
  have F₀₁₂ : Frame [stR s₀ w, outR s₀ w, scR s₀, stkR s₀] s₀.mem s₁₂.mem :=
    F₀₁₀.trans (by rw [← u₁₁.mem]; exact F₁₂.mono (by simp))
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun h0 d hR hlt hcnt => ?_⟩
  · by_cases h : r = .esp
    · subst h
      rw [sp₁₃, g₁₂ _ (by decide), u₁₁.other _ (by decide), sp₁₀]
    · exact cs₁₃ r hr h
  · rw [m₁₃]
    exact F₀₁₂.readW (Region.contains_self _ _)
      (by simpa using ⟨hp.ret_st, hp.ret_out, hp.ret_scr, hp.ret_stk⟩) (by decide)
  · have hn : (arg s₀ 2 ++ arg s₀ 1).toNat = d.length := by
      show (countX86 s₀).toNat = _
      rw [hcnt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    rw [hn] at hr
    subst hr
    have hst : ∀ i < bufOff w + blockBytes w,
        s₁.mem (stA s₀ + BitVec.ofNat 64 i) = s₀.mem (stA s₀ + BitVec.ofNat 64 i) :=
      fun i hi => F₁.bytes (R := stR s₀ w) (by simpa using hp.st_scr) (by simp only; omega) hi
    show bytesAt s₁₃.mem (opA s₀) (bufOff w) = _
    rw [m₁₃, m₁₂, ax₁₁, bx₁₁, bytesAt_writeBytes_self _ _ (by simp [bytesAt]) (by omega), u₁₁.mem,
      bytesAt_state _ _ (by rcases hP.w with h | h <;> simp [h]), e₁₀,
      show ((1 : BitVec 32) != 0) = true from rfl, compressBlocks_one, hn, eB, m₉]
    refine final_eq P hpos hR ?_ ?_
    · exact stateAt_congr fun i hi => by
        rw [hm₃, writeBytes_before s₁.mem _ _ (by omega : i < bufOff w + Proof.Blake2.bufLen w d.length)
          (by simp; omega), hst i (by omega)]
    · rw [pad_bytes hrB (by omega) hm₃]
      congr 1
      exact bytesAt_congr fun i hi => by rw [Offset.add_ofNat_add_ofNat, hst _ (by omega)]

end VG.Proof.Blake2.X86.Stream.Finalize
