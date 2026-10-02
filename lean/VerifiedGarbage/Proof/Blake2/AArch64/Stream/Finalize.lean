import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Common
import VerifiedGarbage.Proof.Framework.Range

/-!
# Streaming BLAKE2 on AArch64: `finalize`

Inside the frame saving `x30` (`WP.frameReg`), `finalize` saves the
callee-saved registers (`prologue_ok`), computes the number of buffered bytes
(`bufLen_ok`), zeroes the rest of the buffer (`pad_ok`), compresses it as the
last block (`compressWith_ok`), copies the hash value out (`output_ok`) and
restores the registers (`restore_ok`).
-/

namespace VG.Proof.Blake2.AArch64.Stream.Finalize

open VG VG.AArch64 VG.Spec.Blake2
open VG.Impl.Blake2.AArch64.Stream (N B mov zeroLoop pad compressLast output finalizeMain finalize saved save
  restore)
open VG.Impl.Blake2.AArch64 (compress)
open VG.Proof.Blake2 (finalizeAArch64 bufOff final_eq stateAt_congr bytesAt_congr bytesAt_add
  bytesAt_state bufLen_le compressBlocks_succ compressBlocks_zero)
open VG.Proof.MdStream.AArch64 (Upd Mupd toNat_ofNat_lt wp_mov wp_movz wp_sub wp_ldr wp_str)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_frame writeBytes_append writeBytes_before
  write_eq_writeBytes)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev op : Addr := s₀.gpr .x2
abbrev scr : Addr := s₀.gpr .x3
abbrev stR (w : Nat) : Region := ⟨st s₀, bufOff w + blockBytes w⟩
abbrev outR (w : Nat) : Region := ⟨op s₀, bufOff w⟩
abbrev scR : Region := ⟨scr s₀, 576⟩
/-- The frame saving `x30`, below the stack pointer. -/
abbrev stkR : Region := ⟨s₀.sp - 16, 16⟩

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀ w, outR s₀ w, scR s₀]
  st_out : (stR s₀ w).Disjoint (outR s₀ w)
  st_scr : (stR s₀ w).Disjoint (scR s₀)
  out_scr : (outR s₀ w).Disjoint (scR s₀)

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (w : Nat) (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  st : (stkR s₀).Disjoint (stR s₀ w)
  out : (stkR s₀).Disjoint (outR s₀ w)
  scr : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {w : Nat} {P : Params w} {s₀ : State} (h : (finalizeAArch64 P).pre s₀) :
    Pre w s₀ ∧ Stack w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩⟩

/-- The saved registers are outside everything written after the saves. -/
theorem Saved.frame {w : Nat} {s₀ : State} (hp : Pre w s₀) {g : Reg → BitVec 64} {m m' : Mem}
    (h : Saved (scr s₀) g m) (hf : Frame [stR s₀ w, outR s₀ w, ⟨scr s₀, 512⟩] m m') :
    Saved (scr s₀) g m' := by
  intro p hp'
  have hoff : 512 ≤ p.2 ∧ p.2 + 8 ≤ 560 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [← h p hp']
  have hsub : Region.Sub ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := Offset.sub_base _ (by omega)
  refine hf.readW (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left hsub
  · exact hp.out_scr.symm.sub_left hsub
  · exact Offset.disjoint_base _ (by omega) (by omega)

/-! ## The prologue -/

/-- After the prologue. -/
structure Start (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = st s₀
  x20 : s.gpr .x20 = scr s₀
  x21 : s.gpr .x21 = op s₀
  x24 : s.gpr .x24 = s₀.gpr .x1
  keep : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  mem : s.mem = saveMem s₀.mem (scr s₀) s₀.gpr

theorem prologue_ok {w : Nat} {s₀ : State} (hp : Pre w s₀) :
    WP isa (.block (save .x3 ++ ([mov .x19 .x0, mov .x20 .x3, mov .x21 .x2, mov .x24 .x1] : List Instr)))
      s₀ (Start s₀) := by
  refine save_ok (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [u₅.other _ (notU hr .x24), u₄.other _ (notU hr .x21), u₃.other _ (notU hr .x20),
      u₂.other _ (notU hr .x19), g₁]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]

/-! ## Zeroing the rest of the buffer -/

section
variable {w : Nat}

/-- Zeroing the buffer from byte `r` (in `x23`) on. -/
theorem pad_ok {s : State} {st : Addr} {r : Nat} (hN : bufOff w ≤ 64) (hr : r ≤ blockBytes w)
    (hbb : blockBytes w < 2 ^ 16) (hx19 : s.gpr .x19 = st) (hx23 : s.gpr .x23 = BitVec.ofNat 64 r)
    (hdst : ∀ i < blockBytes w - r,
      InRegions s.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1) :
    WP isa (pad (w := w)) s fun s' =>
      (∀ x, x ≠ .x9 → x ≠ .x11 → x ≠ .x12 → x ≠ .x23 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (st + BitVec.ofNat 64 (bufOff w + r))
        (List.replicate (blockBytes w - r) 0) := by
  unfold pad
  refine WP.seq (wp_movz fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_sub fun s₃ u₃ => WP.block_nil ?_)
  have g : ∀ x, x ≠ .x9 → x ≠ .x11 → s₃.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₃.other x h2, u₂.other x h2, u₁.other x h1]
  have h11 : s₃.gpr .x11 = BitVec.ofNat 64 (blockBytes w - r) := by
    rw [u₃.gpr, u₂.other .x23 (by decide), u₂.gpr, u₁.other .x23 (by decide), hx23,
      movz_ofNat (n := B w) hbb, B_eq, sub_ofNat hr]
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hrd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have hwr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have hsp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  refine WP.ite _ (zero_iff s₃ h11 (by omega)) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨fun x h1 h2 _ _ => g x h1 h2, hrd₃, hwr₃, hsp₃, ?_⟩
    rw [hb, List.replicate_zero, writeBytes_nil, hm₃]
  · simp only [decide_eq_false_iff_not] at hb
    refine zeroLoop_ok (st := st) (r := r) hN (by omega) (by omega)
      (by rw [g _ (by decide) (by decide), hx19])
      (by rw [g _ (by decide) (by decide), hx23]) h11
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl)
      (fun i hi => by rw [hwr₃]; exact hdst i hi) fun s' h => ?_
    refine ⟨fun x h1 h2 h3 h4 => by rw [h.other x h3 h4 h2, g x h1 h2], by rw [h.rd, hrd₃],
      by rw [h.wr, hwr₃], by rw [h.sp, hsp₃], ?_⟩
    rw [h.mem, hm₃]

end

/-! ## Bytes -/

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem writeW_eq (m : Mem) (a : Addr) (v : BitVec 64) : m.writeW a v = writeBytes m a (wordBytes v) := by
  rw [Mem.writeW, write_eq_writeBytes]; rfl

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

section
variable {w : Nat}

theorem output_eq : output (w := w) = (List.range (N w / 8)).flatMap fun k =>
    [.ldr .x .x9 .x19 (8 * k), .str .x .x9 .x21 (8 * k)] := rfl

/-- After copying `k` words. -/
def OInv (σ : State) (k : Nat) (s : State) : Prop :=
  (∀ r, r ≠ .x9 → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧ s.sp = σ.sp ∧
    s.mem = writeBytes σ.mem (σ.gpr .x21) (bytesAt σ.mem (σ.gpr .x19) (8 * k))

theorem output_ok {σ : State} (hN : bufOff w ≤ 64) (hN8 : bufOff w % 8 = 0)
    (hin : ∀ a n, (⟨σ.gpr .x19, bufOff w⟩ : Region).Contains a n → InRegions (σ.rd ++ σ.wr) a n)
    (hout : ∀ a n, (⟨σ.gpr .x21, bufOff w⟩ : Region).Contains a n → InRegions σ.wr a n)
    (hd : Region.Disjoint ⟨σ.gpr .x19, bufOff w⟩ ⟨σ.gpr .x21, bufOff w⟩) :
    WP isa (.block (output (w := w))) σ fun s =>
      (∀ r, r ≠ .x9 → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧ s.sp = σ.sp ∧
      s.mem = writeBytes σ.mem (σ.gpr .x21) (bytesAt σ.mem (σ.gpr .x19) (bufOff w)) := by
  have e : 8 * (N w / 8) = bufOff w := by rw [N_eq]; omega
  rw [output_eq, ← e]
  refine wp_range_flatMap (M := isa) (OInv σ) (fun k s hk ⟨hg, hrd, hwr, hsp, hm⟩ => ?_) _ (Nat.le_refl _) σ
    ⟨fun _ _ => rfl, rfl, rfl, rfl, by rw [Nat.mul_zero]; simp [bytesAt, writeBytes_nil]⟩
  rw [N_eq] at hk
  have hk8 : 8 * k + 8 ≤ bufOff w := by omega
  have hl : (bytesAt σ.mem (σ.gpr .x19) (8 * k)).length = 8 * k := by simp [bytesAt]
  refine wp_ldr (a := σ.gpr .x19 + BitVec.ofNat 64 (8 * k)) ⟨by omega, by omega⟩
    (by rw [hg _ (by decide)]) (by rw [hrd, hwr]; exact hin _ _ (Offset.contains_base _ hk8 (by omega)))
    fun s₁ u₁ => wp_str (a := σ.gpr .x21 + BitVec.ofNat 64 (8 * k)) ⟨by omega, by omega⟩ ?_ ?_ fun s₂ g₂ =>
      WP.block_nil ⟨fun r hr => by rw [g₂.gpr, u₁.other r hr, hg r hr], by rw [g₂.rd, u₁.rd, hrd],
        by rw [g₂.wr, u₁.wr, hwr], by rw [g₂.sp, u₁.sp, hsp], ?_⟩
  · rw [u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₁.wr, hwr]; exact hout _ _ (Offset.contains_base _ hk8 (by omega))
  · have hv : s.mem.readW (σ.gpr .x19 + BitVec.ofNat 64 (8 * k)) 64 =
        σ.mem.readW (σ.gpr .x19 + BitVec.ofNat 64 (8 * k)) 64 := by
      rw [hm]
      exact (writeBytes_frame (R := ⟨σ.gpr .x21, bufOff w⟩) _ _ _
        (contains_prefix _ (by omega))).readW
        (Offset.contains_base (k := bufOff w) _ hk8 (by omega)) (by simpa using hd) (by decide)
    have e := writeBytes_append σ.mem (σ.gpr .x21) (bytesAt σ.mem (σ.gpr .x19) (8 * k))
      (wordBytes (σ.mem.readW (σ.gpr .x19 + BitVec.ofNat 64 (8 * k)) 64))
      (by rw [hl]; simp [wordBytes]; omega)
    rw [hl] at e
    rw [g₂.mem, u₁.gpr, u₁.mem, hv, hm, writeW_eq, e,
      VG.Proof.Blake2.wordBytes_readW _ _ (.inr rfl), ← bytesAt_add, Nat.mul_succ]

end

/-! ## The whole function -/

section
variable {w : Nat} {P : Params w}

theorem noFrames_finalizeMain (hf : CalleeOk P (compress P)) : (finalizeMain P).noFrames = true := by
  simp only [finalizeMain, pad, compressLast, Impl.Blake2.AArch64.Stream.compressWith, zeroLoop,
    Impl.Blake2.AArch64.Stream.bufLen, Code.noFrames, hf.noFrames, Bool.and_self]

/-- The registers kept from the prologue to the epilogue. -/
abbrev commonKeep : List Reg := [.x19, .x20, .x21, .x24, .x25, .x26, .x27, .x28]

theorem commonKeep_ok : ∀ r ∈ commonKeep,
    r ∈ preserved ∧ r ≠ .x30 ∧ r ≠ .x9 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x23 := by decide

/-- The epilogue's postcondition. -/
def Post (P : Params w) (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ (finalizeAArch64 P).post s₀ s'

/-- `finalize` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀) :
    WP isa (finalizeMain P) s₀ (Post P s₀) := by
  have hl := hP.len
  have hN := hP.N64
  have hbb := hP.bb
  have hN8 : bufOff w % 8 = 0 := by simp only [bufOff]; omega
  have hstN : Region.Sub ⟨st s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega)
  have hsave_st : ∀ r ∈ [(⟨scr s₀ + BitVec.ofNat 64 512, 48⟩ : Region)], (stR s₀ w).Disjoint r := by
    simpa using hp.st_scr.sub_right (Offset.sub_base _ (by omega))
  unfold finalizeMain
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have hkeep : ∀ i < bufOff w + blockBytes w,
      s₁.mem (st s₀ + BitVec.ofNat 64 i) = s₀.mem (st s₀ + BitVec.ofNat 64 i) := fun i hi => by
    rw [h₁.mem]; exact (saveMem_frame _ _ _).bytes (R := stR s₀ w) hsave_st (by simp only; omega) hi
  refine WP.seq (WP.mono (bufLen_ok hP) fun s₂ ⟨r23₂, g₂, m₂, rd₂, wr₂, sp₂⟩ => ?_)
  rw [h₁.x24] at r23₂
  generalize hn : (s₀.gpr .x1).toNat = n at r23₂
  have hr : Blake2.bufLen w n ≤ blockBytes w := bufLen_le (by omega) n
  have hx19₂ : s₂.gpr .x19 = st s₀ := by rw [g₂ _ (by decide) (by decide), h₁.x19]
  refine WP.seq (WP.mono (pad_ok (st := st s₀) hN hr (by omega) hx19₂ r23₂ fun i hi => ?_)
    fun s₃ ⟨g₃, rd₃, wr₃, sp₃, m₃⟩ => ?_)
  · rw [wr₂, h₁.wr, hp.wr, Offset.add_ofNat_add_ofNat]
    exact ⟨stR s₀ w, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have g₃' : ∀ r, r ≠ .x9 → r ≠ .x11 → r ≠ .x12 → r ≠ .x23 → s₃.gpr r = s₁.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₃ r h1 h2 h3 h4, g₂ r h1 h4]
  have hrd₃ : s₃.rd = s₀.rd := by rw [rd₃, rd₂, h₁.rd]
  have hwr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, h₁.wr]
  have hsp₃ : s₃.sp = s₀.sp := by rw [sp₃, sp₂, h₁.sp]
  have hx19₃ : s₃.gpr .x19 = st s₀ := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), h₁.x19]
  have hx20₃ : s₃.gpr .x20 = scr s₀ := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), h₁.x20]
  have hm₃ : s₃.mem = writeBytes s₁.mem (st s₀ + BitVec.ofNat 64 (bufOff w + Blake2.bufLen w n))
      (List.replicate (blockBytes w - Blake2.bufLen w n) 0) := by rw [m₃, m₂]
  -- The call.
  have hbuf : Region.Sub ⟨st s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩ (stR s₀ w) :=
    Offset.sub_base _ (by omega)
  have hscr : Region.Sub ⟨scr s₀, 512⟩ (scR s₀) := Region.sub_prefix (by omega)
  have hcall : CallOk (w := w) s₃ (st s₀) (scr s₀) (s₃.gpr .x19 + BitVec.ofNat 64 (bufOff w))
      (blockBytes w * (BitVec.setWidth 64 (1 : BitVec 16)).toNat) := by
    rw [show (BitVec.setWidth 64 (1 : BitVec 16)).toNat = 1 from rfl, Nat.mul_one, hx19₃]
    refine ⟨hx19₃, hx20₃, (hp.st_scr.sub_left hstN).sub_right hscr,
      Offset.disjoint_base _ (Nat.le_refl _) (by omega), (hp.st_scr.sub_left hbuf).sub_right hscr, ?_, ?_⟩
    · rw [hrd₃, hwr₃, hp.rd, hp.wr, List.nil_append]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀ w, by simp, bufOff w, rfl, by simp only; omega⟩
      · exact ⟨stR s₀ w, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
      · exact ⟨scR s₀, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · rw [hwr₃, hp.wr]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀ w, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
      · exact ⟨scR s₀, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
  unfold compressLast
  refine WP.seq (compressWith_ok hf (bufArgs_ok (by omega)) hcall fun s₄ rd₄ wr₄ sp₄ cs₄ f₄ e₄ => ?_)
  have cs : ∀ r ∈ commonKeep, s₄.gpr r = s₁.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := commonKeep_ok r hr
    rw [cs₄ r h1 h2, g₃' r h3 h4 h5 h6]
  have hx19₄ : s₄.gpr .x19 = st s₀ := by rw [cs _ (by simp), h₁.x19]
  have hx21₄ : s₄.gpr .x21 = op s₀ := by rw [cs _ (by simp), h₁.x21]
  have hwr₄ : s₄.wr = s₀.wr := by rw [wr₄, hwr₃]
  rw [WP.block_append_iff]
  refine WP.mono (output_ok (σ := s₄) hN hN8 (fun a k h => ?_) (fun a k h => ?_) ?_)
    fun s₅ ⟨g₅, rd₅, wr₅, sp₅, m₅⟩ => ?_
  · rw [rd₄, hrd₃, hwr₄, hp.rd, hp.wr, List.nil_append]
    rw [hx19₄] at h
    exact ⟨stR s₀ w, by simp, by simp only [Region.Contains] at h ⊢; omega⟩
  · rw [hwr₄, hp.wr]
    rw [hx21₄] at h
    exact ⟨outR s₀ w, by simp, h⟩
  · rw [hx19₄, hx21₄]; exact hp.st_out.sub_left hstN
  -- What the call and the stores wrote.
  have F₁ : Frame [stR s₀ w, outR s₀ w, ⟨scr s₀, 512⟩] s₁.mem s₅.mem := by
    have f₃ : Frame [stR s₀ w] s₁.mem s₃.mem := by
      rw [hm₃]; exact writeBytes_frame _ _ _ (Offset.contains_base _ (by simp; omega) (by omega))
    have f₅ : Frame [outR s₀ w] s₄.mem s₅.mem := by
      rw [m₅, hx21₄]
      exact writeBytes_frame _ _ _ (contains_prefix _ (by simp [bytesAt]))
    refine ((f₃.mono (by simp)).trans (f₄.sub fun r hr => ?_)).trans (f₅.mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, hstN⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have hsv : Saved (scr s₀) s₀.gpr s₅.mem := Saved.frame hp (h₁.mem ▸ saveMem_saved _ _ _) F₁
  refine restore_ok (scr := scr s₀) (by rw [g₅ _ (by decide), cs _ (by simp), h₁.x20])
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [rd₅, wr₅, rd₄, wr₄, hrd₃, hwr₃, hp.wr],
      Offset.contains_base _ (by omega) (by omega)⟩) s₀.gpr hsv
    fun s₆ hs ho m₆ _ _ sp₆ => ⟨preserved_of hs fun r hr => ?_, by rw [sp₆, sp₅, sp₄, hsp₃], ?_⟩
  · rw [ho r (by simp only [untouched] at hr; simp only [saved, List.map_cons, List.map_nil]; decide +revert),
      g₅ r (notU hr .x9), cs r (by simp only [untouched] at hr; simp [hr]), h₁.keep r hr]
  · intro h0 d hR hlt hcnt
    have hnd : n = d.length := by rw [← hn, hcnt, toNat_ofNat_lt hlt]
    subst hnd
    have hx24₃ : (s₃.gpr .x24).toNat = d.length := by
      rw [g₃' _ (by decide) (by decide) (by decide) (by decide), h₁.x24, hn]
    rw [m₆, m₅, hx21₄, hx19₄, bytesAt_writeBytes_self _ _ (by simp [bytesAt]) (by omega),
      bytesAt_state _ _ hP.w.symm, e₄, show (BitVec.setWidth 64 (1 : BitVec 16)).toNat = 0 + 1 from rfl,
      compressBlocks_succ, compressBlocks_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, BitVec.add_zero,
      hx24₃, hx19₃, show (((1 : BitVec 16).setWidth 64).setWidth 32 != 0) = true from rfl]
    refine final_eq P (by omega) hR ?_ ?_
    · exact stateAt_congr fun i hi => by
        rw [hm₃, writeBytes_before s₁.mem _ _ (by omega : i < bufOff w + Blake2.bufLen w d.length)
          (by simp; omega), hkeep i (by omega)]
    · rw [pad_bytes hr (by omega) hm₃]
      congr 1
      exact bytesAt_congr fun i hi => by rw [Offset.add_ofNat_add_ofNat, hkeep _ (by omega)]

/-- The state `finalizeMain` starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State}
    (hpre : (finalizeAArch64 P).pre s₀) :
    WP isa (finalize P) s₀ fun s' => GprAbi s₀ s' ∧ (finalizeAArch64 P).post s₀ s' := by
  obtain ⟨hp, hs⟩ := pre_of hpre
  have hl := hP.len
  have hpi : Pre w (inner s₀) := ⟨hp.rd, hp.wr, hp.st_out, hp.st_scr, hp.out_scr⟩
  refine WP.frameReg hs.sp16 (fun R hR => ?_) (WP.mono (correctMain hP hf hpi) fun s' ⟨hk, hsp, hpost⟩ => ?_)
    (by rw [fdepth_of_noFrames (noFrames_finalizeMain hf)]; decide)
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact hs.st
    · exact hs.out
    · exact hs.scr
  · refine ⟨⟨fun r hr => ?_, rfl⟩, fun h0 d hm hlt hc => ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · exact hpost h0 d (repr_congr hP (fun i hi => write_frame_bytes (R := stR s₀ w) hs.st
        (by show bufOff w + blockBytes w < 2 ^ 64; omega) hi) hm) hlt hc

end

end VG.Proof.Blake2.AArch64.Stream.Finalize
