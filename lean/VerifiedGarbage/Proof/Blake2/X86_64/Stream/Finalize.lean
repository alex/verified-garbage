import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Init

/-!
# Streaming BLAKE2 on x86-64: `finalize`

`finalize` saves the callee-saved registers (`prologue_ok`), computes the
number of buffered bytes (`bufLen_ok`), zeroes the rest of the buffer
(`pad_ok`), compresses it as the last block (`compressWith_ok`), copies the
hash value out (`output_ok`) and restores the registers (`restore_ok`).
-/

namespace VG.Proof.Blake2.X86_64.Stream.Finalize

open VG VG.X86_64 VG.Spec.Blake2
open VG.Impl.Blake2.X86_64.Stream (saved save restore output)
open VG.Impl.Blake2.X86_64 (at_ compress)
open VG.Proof.Blake2 (finalizeX86_64 bufOff final_eq stateAt_congr bytesAt_congr bytesAt_add
  bytesAt_state bufLen_le compressBlocks_succ compressBlocks_zero)
open VG.Proof.Blake2.X86_64.Stream (Ok N_eq B_eq CalleeOk CallOk Setup compressWith_ok)
open VG.Proof.Blake2.X86_64.Stream.Init (ea_at writeBytes_at)
open VG.Proof.MdStream.X86_64 (Upd WP.cons wp_mov wp_movm wp_mov32i wp_store wp_store8 wp_addi wp_subi
  wp_sub wp_andi wp_test ofInt_natCast sx1 sx_ofNat zx_ofNat and_mask sub_ofNat ofNat_succ ofNat_pred
  ofNat_beq_zero toNat_ofNat_lt)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_append
  writeBytes_before write_eq_writeBytes)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev op : Addr := s₀.gpr .rdx
abbrev scr : Addr := s₀.gpr .rcx
abbrev stR (w : Nat) : Region := ⟨st s₀, bufOff w + blockBytes w⟩
abbrev outR (w : Nat) : Region := ⟨op s₀, bufOff w⟩
abbrev scR : Region := ⟨scr s₀, 576⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- Where the call of the compression function stores its return address. -/
abbrev stkR : Region := below (s₀.gpr .rsp) 8

/-- The caller's callee-saved registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ k < 6, m.readW (scr s₀ + BitVec.ofNat 64 (512 + 8 * k)) 64 = s₀.gpr (saved.getD k (.rax, 0)).1

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀ w, outR s₀ w, scR s₀]
  st_out : (stR s₀ w).Disjoint (outR s₀ w)
  st_scr : (stR s₀ w).Disjoint (scR s₀)
  out_scr : (outR s₀ w).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀ w)
  ret_out : (retR s₀).Disjoint (outR s₀ w)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀ w)
  stk_out : (stkR s₀).Disjoint (outR s₀ w)
  stk_scr : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {w : Nat} {P : Params w} {s₀ : State} (h : (finalizeX86_64 P).pre s₀) : Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) :=
  Offset.base_disjoint_below _ (by decide)

/-- The saved registers are outside everything written after the saves. -/
theorem Saved.frame {w : Nat} {s₀ : State} (hp : Pre w s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [stR s₀ w, outR s₀ w, ⟨scr s₀, 512⟩, stkR s₀] m m') : Saved s₀ m' := by
  intro k hk
  rw [← h k hk]
  have hsub : Region.Sub ⟨scr s₀ + BitVec.ofNat 64 (512 + 8 * k), 8⟩ (scR s₀) :=
    Offset.sub_base _ (by omega)
  refine hf.readW (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left hsub
  · exact hp.out_scr.symm.sub_left hsub
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact hp.stk_scr.symm.sub_left hsub

/-! ## The prologue -/

theorem save_eq : save .rcx = (List.range 6).flatMap fun k =>
    [.store (at_ .rcx (512 + 8 * k)) ((saved.getD k (.rax, 0)).1)] := rfl

/-- During the saves. -/
def SaveInv (s₀ : State) (k : Nat) (s : State) : Prop :=
  s.gpr = s₀.gpr ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    Frame [⟨scr s₀ + BitVec.ofNat 64 512, 48⟩] s₀.mem s.mem ∧
    ∀ j < k, s.mem.readW (scr s₀ + BitVec.ofNat 64 (512 + 8 * j)) 64 = s₀.gpr ((saved.getD j (.rax, 0)).1)

theorem saves_ok {w : Nat} {s₀ : State} (hp : Pre w s₀) :
    WP isa (.block ((List.range 6).flatMap fun k =>
      [.store (at_ .rcx (512 + 8 * k)) ((saved.getD k (.rax, 0)).1)])) s₀ (SaveInv s₀ 6) := by
  refine wp_range_flatMap (M := isa) (SaveInv s₀) (fun k s hk ⟨hg, hrd, hwr, hf, hv⟩ => ?_) 6
    (Nat.le_refl _) s₀ ⟨rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  refine wp_store (a := scr s₀ + BitVec.ofNat 64 (512 + 8 * k)) (by rw [ea_at, hg])
    ⟨scR s₀, by simp [hwr, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
    fun s' g' m' r' w' => WP.block_nil ?_
  refine ⟨g'.trans hg, r'.trans hrd, w'.trans hwr, ?_, fun j hj => ?_⟩
  · rw [m']
    exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  · rw [m', hg]
    by_cases e : j = k
    · subst e; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hv j (by omega)

/-- After the prologue. -/
structure Start (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = st s₀
  r15 : s.gpr .r15 = scr s₀
  rbp : s.gpr .rbp = op s₀
  r14 : s.gpr .r14 = s₀.gpr .rsi
  rsp : s.gpr .rsp = s₀.gpr .rsp
  frame : Frame [⟨scr s₀ + BitVec.ofNat 64 512, 48⟩] s₀.mem s.mem
  saved : Saved s₀ s.mem

theorem prologue_ok {w : Nat} {s₀ : State} (hp : Pre w s₀) :
    WP isa (.block (save .rcx ++ ([.mov .rbx (.reg .rdi), .mov .r15 (.reg .rcx), .mov .rbp (.reg .rdx),
      .mov .r14 (.reg .rsi)] : List Instr))) s₀ (Start s₀) := by
  rw [save_eq, WP.block_append_iff]
  refine WP.mono (saves_ok hp) fun s₁ ⟨g₁, rd₁, wr₁, f₁, v₁⟩ => ?_
  refine wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ =>
    wp_mov fun s₅ u₅ _ _ => WP.block_nil ?_
  have hm : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  refine ⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁], ?_, ?_, ?_,
    ?_, ?_, by rw [hm]; exact f₁, by rw [hm]; exact v₁⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]

/-! ## The number of buffered bytes -/

section
variable {w : Nat}

theorem bufLen_ok (hP : blockBytes w = 64 ∨ blockBytes w = 128) {s : State} :
    WP isa (Impl.Blake2.X86_64.Stream.bufLen (w := w)) s fun s' =>
      s'.gpr .r13 = BitVec.ofNat 64 (bufLen w (s.gpr .r14).toNat) ∧
      (∀ r, r ≠ .r13 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold Impl.Blake2.X86_64.Stream.bufLen
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => wp_subi fun s₂ u₂ _ => wp_andi fun s₃ u₃ => wp_addi fun s₄ u₄ =>
    wp_test fun s₅ g₅ m₅ rd₅ wr₅ z₅ => WP.block_nil ?_)
  have hn := (s.gpr .r14).isLt
  generalize hn' : (s.gpr .r14).toNat = n at hn
  have hr14 : s.gpr .r14 = BitVec.ofNat 64 n := by rw [← hn', BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have g : ∀ r, r ≠ .r13 → s₅.gpr r = s.gpr r := fun r h => by
    rw [g₅, u₄.other r h, u₃.other r h, u₂.other r h, u₁.other r h]
  have hm : s₅.mem = s.mem := by rw [m₅, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hrd : s₅.rd = s.rd := by rw [rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hwr : s₅.wr = s.wr := by rw [wr₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hz : s₅.zf = some (decide (n = 0)) := by
    rw [z₅, ← congrFun g₅ .r14, g .r14 (by decide), BitVec.and_self, hr14, ofNat_beq_zero hn]
  refine WP.ite (decide (n = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_mov32i fun s₆ u₆ _ _ => WP.block_nil ⟨?_, fun r h => by rw [u₆.other r h, g r h],
      by rw [u₆.mem, hm], by rw [u₆.rd, hrd], by rw [u₆.wr, hwr]⟩
    rw [u₆.gpr, hb]; rfl
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil ⟨?_, g, hm, hrd, hwr⟩
    rw [g₅, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hr14, sx1, ofNat_pred (by omega), B_eq, and_mask hP,
      toNat_ofNat_lt (by omega), ← ofNat_succ]
    simp only [bufLen, hb, ↓reduceIte]

/-! ## Zeroing the rest of the buffer -/

/-- The zeroing loop's state after `j` of `k` bytes, from `s₀`. -/
structure ZI (s₀ : State) (q : Addr) (r k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  r13 : s.gpr .r13 = BitVec.ofNat 64 (r + j)
  rax : s.gpr .rax = BitVec.ofNat 64 (k - j)
  other : ∀ x, x ≠ .rax → x ≠ .r13 → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes s₀.mem q (List.replicate j 0)

/-- The loop zeroing `k ≥ 1` bytes of the buffer, from byte `r` on (in `r13`). -/
theorem zeroLoop_ok {s₀ : State} {st : Addr} {r k : Nat} (hk : 1 ≤ k) (hk' : r + k < 2 ^ 32)
    (hrbx : s₀.gpr .rbx = st) (hr13 : s₀.gpr .r13 = BitVec.ofNat 64 r)
    (hrax : s₀.gpr .rax = BitVec.ofNat 64 k) (hr9 : s₀.gpr .r9 = 0)
    (hdst : ∀ i < k, InRegions s₀.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1)
    {Q : State → Prop}
    (hQ : ∀ s, ZI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) r k k s → Q s) :
    WP isa (Impl.Blake2.X86_64.Stream.zeroLoop (w := w)) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      ZI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) r k j s) ?_ k s₀
    ⟨0, by omega, by omega, by omega, by rw [hr13, Nat.add_zero], by rw [hrax, Nat.sub_zero],
      fun _ _ _ => rfl, rfl, rfl, by rw [List.replicate_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hrbx' : s.gpr .rbx = st := by rw [h.other .rbx (by decide) (by decide), hrbx]
  refine wp_store8 (r := .r9) (a := st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j) ?_
    (by rw [h.wr]; exact hdst j hj) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  · simp only [State.ea, Impl.Blake2.X86_64.Stream.bufByte, hrbx', h.r13, N_eq, BitVec.ofNat_add,
      BitVec.mul_one, ofInt_natCast]
    ac_rfl
  refine wp_addi fun s₃ u₃ => wp_subi fun s₄ u₄ hz₄ => WP.block_nil ?_
  have hrax' : s₄.gpr .rax = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [u₄.gpr, u₃.other .rax (by decide), g₂, h.rax, sx1, ofNat_pred (by omega), Nat.sub_sub]
  have hI : ZI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) r k (j + 1) s₄ := by
    refine ⟨by omega, ?_, hrax', fun x h1 h2 => ?_, ?_, ?_, ?_⟩
    · rw [u₄.other .r13 (by decide), u₃.gpr, g₂, h.r13, sx1, ← Nat.add_assoc, ofNat_succ]
    · rw [u₄.other x h1, u₃.other x h2, g₂, h.other x h1 h2]
    · rw [u₄.rd, u₃.rd, rd₂, h.rd]
    · rw [u₄.wr, u₃.wr, wr₂, h.wr]
    · rw [u₄.mem, u₃.mem, m₂, h.other .r9 (by decide) (by decide), hr9, h.mem,
        List.replicate_succ', writeBytes_snoc _ _ _ _ (by simp; omega), List.length_replicate]
      rfl
  have hzf : s₄.zf = some (decide (k - (j + 1) = 0)) := by
    rw [hz₄, u₃.other .rax (by decide), g₂, h.rax, sx1, ofNat_pred (show 1 ≤ k - j by omega),
      ofNat_beq_zero (by omega), show k - j - 1 = k - (j + 1) by omega]
  by_cases hjk : j + 1 = k
  · refine .inl ⟨?_, hQ _ (hjk ▸ hI)⟩
    simp only [eval, hzf, show k - (j + 1) = 0 by omega, decide_true, Option.map_some,
      Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩
    simp only [eval, hzf, show k - (j + 1) ≠ 0 by omega, decide_false, Option.map_some,
      Bool.not_false]

/-- Zeroing the buffer from byte `r` (in `r13`) on. -/
theorem pad_ok {s : State} {st : Addr} {r : Nat} (hr : r ≤ blockBytes w)
    (hbb : blockBytes w < 2 ^ 31) (hrbx : s.gpr .rbx = st) (hr13 : s.gpr .r13 = BitVec.ofNat 64 r)
    (hdst : ∀ i < blockBytes w - r,
      InRegions s.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1) :
    WP isa (Impl.Blake2.X86_64.Stream.pad (w := w)) s fun s' =>
      (∀ x, x ≠ .r9 → x ≠ .rax → x ≠ .r13 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem (st + BitVec.ofNat 64 (bufOff w + r))
        (List.replicate (blockBytes w - r) 0) := by
  unfold Impl.Blake2.X86_64.Stream.pad
  refine WP.seq (wp_mov32i fun s₁ u₁ _ _ => wp_mov32i fun s₂ u₂ _ _ => wp_sub fun s₃ u₃ z₃ =>
    WP.block_nil ?_)
  have g : ∀ x, x ≠ .r9 → x ≠ .rax → s₃.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₃.other x h2, u₂.other x h2, u₁.other x h1]
  have hrax : s₃.gpr .rax = BitVec.ofNat 64 (blockBytes w - r) := by
    rw [u₃.gpr, u₂.other .r13 (by decide), u₂.gpr, u₁.other .r13 (by decide), hr13, B_eq,
      zx_ofNat (by omega), sub_ofNat hr]
  have hz : s₃.zf = some (decide (blockBytes w - r = 0)) := by
    rw [z₃, ← u₃.gpr, hrax, ofNat_beq_zero (by omega)]
  refine WP.ite (decide (blockBytes w - r = 0)) hz (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨fun x h1 h2 _ => g x h1 h2, by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], ?_⟩
    rw [hb, List.replicate_zero, writeBytes_nil, u₃.mem, u₂.mem, u₁.mem]
  · simp only [decide_eq_false_iff_not] at hb
    have hwr : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
    refine zeroLoop_ok (st := st) (r := r) (by omega) (by omega)
      (by rw [g _ (by decide) (by decide), hrbx])
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hr13]) hrax
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl)
      (fun i hi => by rw [hwr]; exact hdst i hi) fun s' h => ?_
    refine ⟨fun x h1 h2 h3 => by rw [h.other x h2 h3, g x h1 h2], by rw [h.rd, u₃.rd, u₂.rd, u₁.rd],
      by rw [h.wr, hwr], ?_⟩
    rw [h.mem, u₃.mem, u₂.mem, u₁.mem]

end

/-! ## Bytes -/

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

/-! ## The call -/

section
variable {w : Nat}

theorem args_ok {σ : State} (hN : bufOff w < 2 ^ 31) :
    WP isa (.block (([.mov .rdi (.reg .rbx)] : List Instr) ++
      ([.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (Impl.Blake2.X86_64.Stream.N w))),
        .mov32 .rdx (.imm 1), .mov .rcx (.reg .r14), .mov32 .r8 (.imm 1)] : List Instr) ++
      ([.mov .r9 (.reg .r15)] : List Instr))) σ
      fun s => Setup σ s (σ.gpr .rbx + BitVec.ofNat 64 (bufOff w)) 1 (σ.gpr .r14) true := by
  refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_addi fun s₃ u₃ => wp_mov32i fun s₄ u₄ _ _ =>
    wp_mov fun s₅ u₅ _ _ => wp_mov32i fun s₆ u₆ _ _ => wp_mov fun s₇ u₇ _ _ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → s₇.gpr r = σ.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by
      rw [u₇.other r h6, u₆.other r h5, u₅.other r h4, u₄.other r h3, u₃.other r h2, u₂.other r h2,
        u₁.other r h1]
  have hcs : ∀ r ∈ calleeSaved, r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx ∧ r ≠ .r8 ∧ r ≠ .r9 := by
    decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.gpr, u₁.other _ (by decide), N_eq, sx_ofNat hN]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.gpr]; rfl
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · have h := hcs r hr
    exact g r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem callOk_of {s₀ σ : State} (hp : Pre w s₀) (hs : bufOff w + blockBytes w < 2 ^ 32)
    (hrd : σ.rd = s₀.rd) (hwr : σ.wr = s₀.wr) (hrbx : σ.gpr .rbx = st s₀) (hr15 : σ.gpr .r15 = scr s₀)
    (hsp : σ.gpr .rsp = s₀.gpr .rsp) :
    CallOk (w := w) σ (st s₀) (scr s₀) (st s₀ + BitVec.ofNat 64 (bufOff w))
      (blockBytes w * (1 : BitVec 64).toNat) := by
  rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.mul_one]
  have hstN : Region.Sub ⟨st s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega)
  have hbuf : Region.Sub ⟨st s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩ (stR s₀ w) :=
    Offset.sub_base _ (by omega)
  have hscr : Region.Sub ⟨scr s₀, 512⟩ (scR s₀) := Region.sub_prefix (by omega)
  refine ⟨hrbx, hr15, (hp.st_scr.sub_left hstN).sub_right hscr,
    Offset.disjoint_base _ (Nat.le_refl _) (by omega), (hp.st_scr.sub_left hbuf).sub_right hscr,
    by rw [hsp]; exact hp.stk_st.sub_right hstN, by rw [hsp]; exact hp.stk_scr.sub_right hscr,
    by rw [hsp]; exact hp.stk_st.sub_right hbuf, ?_, ?_, by omega, by omega⟩
  · rw [hrd, hwr, hp.rd, hp.wr, List.nil_append]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀ w, by simp, bufOff w, rfl, by simp only; omega⟩
    · exact ⟨stR s₀ w, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · exact ⟨scR s₀, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
  · rw [hwr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · exact ⟨scR s₀, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩

end

/-! ## Copying the hash value out -/

section
variable {w : Nat}

theorem output_eq : output (w := w) = (List.range (Impl.Blake2.X86_64.Stream.N w / 8)).flatMap fun k =>
    [.mov .rax (.mem (at_ .rbx (8 * k))), .store (at_ .rbp (8 * k)) .rax] := rfl

/-- After copying `k` words. -/
def OInv (σ : State) (k : Nat) (s : State) : Prop :=
  (∀ r, r ≠ .rax → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧
    s.mem = writeBytes σ.mem (σ.gpr .rbp) (bytesAt σ.mem (σ.gpr .rbx) (8 * k))

theorem output_ok {σ : State} (hN : bufOff w < 2 ^ 32) (hN8 : bufOff w % 8 = 0)
    (hin : ∀ a n, (⟨σ.gpr .rbx, bufOff w⟩ : Region).Contains a n → InRegions (σ.rd ++ σ.wr) a n)
    (hout : ∀ a n, (⟨σ.gpr .rbp, bufOff w⟩ : Region).Contains a n → InRegions σ.wr a n)
    (hd : Region.Disjoint ⟨σ.gpr .rbx, bufOff w⟩ ⟨σ.gpr .rbp, bufOff w⟩) :
    WP isa (.block (output (w := w))) σ fun s =>
      (∀ r, r ≠ .rax → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧
      s.mem = writeBytes σ.mem (σ.gpr .rbp) (bytesAt σ.mem (σ.gpr .rbx) (bufOff w)) := by
  have e : 8 * (Impl.Blake2.X86_64.Stream.N w / 8) = bufOff w := by rw [N_eq]; omega
  rw [output_eq, ← e]
  refine wp_range_flatMap (M := isa) (OInv σ) (fun k s hk ⟨hg, hrd, hwr, hm⟩ => ?_) _ (Nat.le_refl _) σ
    ⟨fun _ _ => rfl, rfl, rfl, by rw [Nat.mul_zero]; simp [bytesAt, writeBytes_nil]⟩
  rw [N_eq] at hk
  have hk8 : 8 * k + 8 ≤ bufOff w := by omega
  have hl : (bytesAt σ.mem (σ.gpr .rbx) (8 * k)).length = 8 * k := by simp [bytesAt]
  refine wp_movm (a := σ.gpr .rbx + BitVec.ofNat 64 (8 * k))
    (by rw [ea_at, hg _ (by decide)]) (by rw [hrd, hwr]; exact hin _ _ (Offset.contains_base _ hk8 (by omega)))
    fun s₁ u₁ => wp_store (a := σ.gpr .rbp + BitVec.ofNat 64 (8 * k)) ?_ ?_ fun s₂ g₂ m₂ rd₂ wr₂ =>
      WP.block_nil ⟨fun r hr => by rw [g₂, u₁.other r hr, hg r hr], by rw [rd₂, u₁.rd, hrd],
        by rw [wr₂, u₁.wr, hwr], ?_⟩
  · rw [ea_at, u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₁.wr, hwr]; exact hout _ _ (Offset.contains_base _ hk8 (by omega))
  · have hv : s.mem.readW (σ.gpr .rbx + BitVec.ofNat 64 (8 * k)) 64 =
        σ.mem.readW (σ.gpr .rbx + BitVec.ofNat 64 (8 * k)) 64 := by
      rw [hm]
      exact (writeBytes_frame (R := ⟨σ.gpr .rbp, bufOff w⟩) _ _ _
        (VG.Proof.Blake2.X86_64.Stream.contains_prefix _ (by omega))).readW
        (Offset.contains_base (k := bufOff w) _ hk8 (by omega)) (by simpa using hd) (by decide)
    have e := writeBytes_append σ.mem (σ.gpr .rbp) (bytesAt σ.mem (σ.gpr .rbx) (8 * k))
      (wordBytes (σ.mem.readW (σ.gpr .rbx + BitVec.ofNat 64 (8 * k)) 64))
      (by rw [hl]; simp [wordBytes]; omega)
    rw [hl] at e
    rw [m₂, u₁.gpr, u₁.mem, hv, hm, writeW_eq, e, VG.Proof.Blake2.wordBytes_readW _ _ (.inr rfl),
      ← bytesAt_add, Nat.mul_succ]

end

/-! ## The epilogue -/

theorem restore_eq : restore = (List.range 6).flatMap fun k =>
    [.mov ((saved.getD k (.rax, 0)).1) (.mem (at_ .r15 (512 + 8 * k)))] := rfl

theorem saved_ne : ∀ j < 6, ∀ k < 6, j ≠ k → (saved.getD j (.rax, 0)).1 ≠ (saved.getD k (.rax, 0)).1 := by
  decide

theorem saved_ne' : ∀ k < 6, (saved.getD k (.rax, 0)).1 ≠ .rsp ∧
    (k < 5 → (saved.getD k (.rax, 0)).1 ≠ .r15) := by
  decide

/-- During the restores. -/
def ResInv (s₀ s₁ : State) (k : Nat) (s : State) : Prop :=
  (k < 6 → s.gpr .r15 = scr s₀) ∧ s.gpr .rsp = s₀.gpr .rsp ∧
    s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧
    ∀ j < k, s.gpr ((saved.getD j (.rax, 0)).1) = s₀.gpr ((saved.getD j (.rax, 0)).1)

theorem restore_ok {w : Nat} {s₀ s₁ : State} (hp : Pre w s₀) (hr15 : s₁.gpr .r15 = scr s₀)
    (hsp : s₁.gpr .rsp = s₀.gpr .rsp) (hwr : s₁.wr = s₀.wr) (hsv : Saved s₀ s₁.mem) :
    WP isa (.block restore) s₁ fun s =>
      (∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r) ∧ s.mem = s₁.mem := by
  rw [restore_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (ResInv s₀ s₁)
    (fun k s' hk ⟨r15, sp, m, rd, wr, v⟩ => ?_) 6 (Nat.le_refl _) s₁
    ⟨fun _ => hr15, hsp, rfl, rfl, rfl, fun _ h => absurd h (by omega)⟩) fun s' ⟨_, sp, m, _, _, v⟩ => ?_
  · refine wp_movm (a := scr s₀ + BitVec.ofNat 64 (512 + 8 * k)) (by rw [ea_at, r15 hk])
      ⟨scR s₀, by simp [rd, wr, hwr, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
      fun s'' h => WP.block_nil ?_
    have ne := saved_ne' k hk
    refine ⟨fun hk' => by rw [h.other _ (Ne.symm (ne.2 (by omega))), r15 hk],
      by rw [h.other _ (Ne.symm ne.1), sp], by rw [h.mem, m], by rw [h.rd, rd], by rw [h.wr, wr],
      fun j hj => ?_⟩
    by_cases e : j = k
    · subst e; rw [h.gpr, m]; exact hsv j hk
    · rw [h.other _ (saved_ne j (by omega) k hk e), v j (by omega)]
  · refine ⟨fun r hr => ?_, m⟩
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact v 0 (by omega)
    · exact v 1 (by omega)
    · exact sp
    · exact v 2 (by omega)
    · exact v 3 (by omega)
    · exact v 4 (by omega)
    · exact v 5 (by omega)

/-! ## The whole function -/

theorem correct {callee : Impl.Blake2.X86_64.Stream.Callee} {w : Nat} {P : Params w} {s₀ : State} (hP : Ok P) (hf : CalleeOk P callee.code)
    (hpre : (finalizeX86_64 P).pre s₀) :
    WP isa (Impl.Blake2.X86_64.Stream.finalize P callee) s₀ fun s' =>
      gprPreserved s₀ s' ∧ (finalizeX86_64 P).post s₀ s' := by
  have hp := pre_of hpre
  have hw := hP.w
  obtain ⟨hs, hs16, -, -, -⟩ := Init.sizes hw
  have hbb := hP.bb
  have hNe := hP.N
  have hN8 : bufOff w % 8 = 0 := by simp only [bufOff]; omega
  have hN : bufOff w < 2 ^ 31 := by omega
  have hstN : Region.Sub ⟨st s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega)
  have hsave_st : ∀ r ∈ [(⟨scr s₀ + BitVec.ofNat 64 512, 48⟩ : Region)], (stR s₀ w).Disjoint r := by
    simpa using hp.st_scr.sub_right (Offset.sub_base _ (by omega))
  unfold Impl.Blake2.X86_64.Stream.finalize
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have hkeep : ∀ i < bufOff w + blockBytes w,
      s₁.mem (st s₀ + BitVec.ofNat 64 i) = s₀.mem (st s₀ + BitVec.ofNat 64 i) :=
    fun i hi => h₁.frame.bytes (R := stR s₀ w) hsave_st (by simp only; omega) hi
  refine WP.seq (WP.mono (bufLen_ok hbb) fun s₂ ⟨r13₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  rw [h₁.r14] at r13₂
  generalize hn : (s₀.gpr .rsi).toNat = n at r13₂
  have hr : bufLen w n ≤ blockBytes w := bufLen_le (by omega) n
  have hrbx₂ : s₂.gpr .rbx = st s₀ := by rw [g₂ _ (by decide), h₁.rbx]
  refine WP.seq (WP.mono (pad_ok (st := st s₀) hr (by omega) hrbx₂ r13₂ fun i hi => ?_)
    fun s₃ ⟨g₃, rd₃, wr₃, m₃⟩ => ?_)
  · rw [wr₂, h₁.wr, hp.wr, Offset.add_ofNat_add_ofNat]
    exact ⟨stR s₀ w, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have g₃' : ∀ r, r ≠ .r9 → r ≠ .rax → r ≠ .r13 → s₃.gpr r = s₁.gpr r := fun r h1 h2 h3 => by
    rw [g₃ r h1 h2 h3, g₂ r h3]
  have hrd₃ : s₃.rd = s₀.rd := by rw [rd₃, rd₂, h₁.rd]
  have hwr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, h₁.wr]
  have hsp₃ : s₃.gpr .rsp = s₀.gpr .rsp := by rw [g₃' _ (by decide) (by decide) (by decide), h₁.rsp]
  have hrbx₃ : s₃.gpr .rbx = st s₀ := by rw [g₃' _ (by decide) (by decide) (by decide), h₁.rbx]
  have hm₃ : s₃.mem = writeBytes s₁.mem (st s₀ + BitVec.ofNat 64 (bufOff w + bufLen w n))
      (List.replicate (blockBytes w - bufLen w n) 0) := by rw [m₃, m₂]
  -- The call.
  refine WP.seq (compressWith_ok hf (WP.mono (args_ok (σ := s₃) hN) fun s' h => by rw [hrbx₃] at h; exact h)
    (callOk_of hp hs hrd₃ hwr₃ hrbx₃ (by rw [g₃' _ (by decide) (by decide) (by decide), h₁.r15]) hsp₃)
    fun s₄ rd₄ wr₄ cs₄ f₄ e₄ => ?_)
  have hrbx₄ : s₄.gpr .rbx = st s₀ := by rw [cs₄ _ (by decide), hrbx₃]
  have hrbp₄ : s₄.gpr .rbp = op s₀ := by
    rw [cs₄ _ (by decide), g₃' _ (by decide) (by decide) (by decide), h₁.rbp]
  have hwr₄ : s₄.wr = s₀.wr := by rw [wr₄, hwr₃]
  rw [WP.block_append_iff]
  refine WP.mono (output_ok (σ := s₄) (by omega) hN8 (fun a k h => ?_) (fun a k h => ?_) ?_)
    fun s₅ ⟨g₅, rd₅, wr₅, m₅⟩ => ?_
  · rw [rd₄, hrd₃, hwr₄, hp.rd, hp.wr, List.nil_append]
    rw [hrbx₄] at h
    exact ⟨stR s₀ w, by simp, by simp only [Region.Contains] at h ⊢; omega⟩
  · rw [hwr₄, hp.wr]
    rw [hrbp₄] at h
    exact ⟨outR s₀ w, by simp, h⟩
  · rw [hrbx₄, hrbp₄]; exact hp.st_out.sub_left hstN
  -- What the calls and stores wrote.
  have F₁ : Frame [stR s₀ w, outR s₀ w, ⟨scr s₀, 512⟩, stkR s₀] s₁.mem s₅.mem := by
    have f₃ : Frame [stR s₀ w] s₁.mem s₃.mem := by
      rw [hm₃]; exact writeBytes_frame _ _ _ (Offset.contains_base _ (by simp; omega) (by omega))
    have f₅ : Frame [outR s₀ w] s₄.mem s₅.mem := by
      rw [m₅, hrbp₄]
      exact writeBytes_frame _ _ _ (VG.Proof.Blake2.X86_64.Stream.contains_prefix _ (by simp [bytesAt]))
    rw [hsp₃] at f₄
    refine ((f₃.mono (by simp)).trans (f₄.sub fun r hr => ?_)).trans (f₅.mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀ w, by simp, hstN⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  refine WP.mono (restore_ok hp (by rw [g₅ _ (by decide), cs₄ _ (by decide),
      g₃' _ (by decide) (by decide) (by decide), h₁.r15])
    (by rw [g₅ _ (by decide), cs₄ _ (by decide), hsp₃]) (by rw [wr₅, hwr₄])
    (h₁.saved.frame hp F₁)) fun s₆ ⟨cs₆, m₆⟩ => ?_
  refine ⟨⟨cs₆, ?_⟩, fun h0 d hR hlt hcnt => ?_⟩
  · have F₀ : Frame [stR s₀ w, outR s₀ w, scR s₀, stkR s₀] s₀.mem s₆.mem := by
      rw [m₆]
      refine (h₁.frame.sub fun r hr => ?_).trans (F₁.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨scR s₀, by simp, Offset.sub_base _ (by omega)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
        · exact ⟨_, by simp, fun _ h => h⟩
    exact F₀.readW (Region.contains_self _ _)
      (by simpa using ⟨hp.ret_st, hp.ret_out, hp.ret_scr, ret_stk s₀⟩) (by decide)
  · have hnd : n = d.length := by rw [← hn, hcnt, toNat_ofNat_lt hlt]
    subst hnd
    have hr14 : (s₃.gpr .r14).toNat = d.length := by
      rw [g₃' _ (by decide) (by decide) (by decide), h₁.r14, hn]
    rw [m₆, m₅, hrbp₄, hrbx₄, bytesAt_writeBytes_self _ _ (by simp [bytesAt]) (by omega),
      bytesAt_state _ _ (hw.symm), e₄, show (1 : BitVec 64).toNat = 0 + 1 from rfl, compressBlocks_succ,
      compressBlocks_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, BitVec.add_zero, hr14]
    refine final_eq P (by omega) hR ?_ ?_
    · exact stateAt_congr fun i hi => by
        rw [hm₃, writeBytes_before s₁.mem _ _ (by omega : i < bufOff w + bufLen w d.length)
          (by simp; omega), hkeep i (by omega)]
    · rw [pad_bytes hr (by omega) hm₃]
      congr 1
      exact bytesAt_congr fun i hi => by rw [Offset.add_ofNat_add_ofNat, hkeep _ (by omega)]

end VG.Proof.Blake2.X86_64.Stream.Finalize
