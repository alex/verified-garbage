import VerifiedGarbage.Proof.Hmac.AArch64.Common
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Spec.Hmac.Contract

/-!
# HMAC-SHA-256 on AArch64: `init`

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 proof (`VG.Proof.Hmac.X86_64.Init`).
-/

namespace VG.Proof.Hmac.AArch64.Init


open VG VG.AArch64 VG.Impl.Hmac.AArch64
open VG.Impl.Sha256.AArch64.Stream (mov save restore compressAt saved)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_snoc repr_block)
open VG.Proof.Sha256.Stream (writeBytes repr_congr)
open VG.Proof.Sha256.AArch64 (writeState stateAt_writeState contains_offset sub_offset toNat_ofNat_lt)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_mov wp_movz wp_addImm wp_subImm wp_sub wp_add wp_ldrb
  wp_strb frame_bytes untouched eval_zero eval_nonzero ofNat_beq_zero sub_ofNat ofNat_succ)
open VG.Proof.Sha256.AArch64.Stream (compressAt_ok saveMem saveMem_saved saveMem_frame save_ok
  restore_ok movzk)
open VG.Spec.Sha256 (bytesAt stateAt Repr H0)
open VG.Spec.Hmac (xorPad ipad opad blockKey sha256)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .x0
abbrev out : Addr := s₀.gpr .x1
abbrev kp : Addr := s₀.gpr .x2
abbrev kl : Nat := (s₀.gpr .x3).toNat
abbrev scr : Addr := s₀.gpr .x4
abbrev inR : Region := ⟨inn s₀, 96⟩
abbrev outR : Region := ⟨out s₀, 96⟩
abbrev kR : Region := ⟨kp s₀, kl s₀⟩
abbrev scR : Region := ⟨scr s₀, 160⟩

/-- The key, padded with zeros to a block. -/
def K0 : List Byte := bytesAt s₀.mem (kp s₀) (kl s₀) ++ List.replicate (64 - kl s₀) 0

/-- The caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (scr s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1

end

structure Pre (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ 64
  rd : s₀.rd = [kR s₀]
  wr : s₀.wr = [inR s₀, outR s₀, scR s₀]
  i_o : (inR s₀).Disjoint (outR s₀)
  i_s : (inR s₀).Disjoint (scR s₀)
  o_s : (outR s₀).Disjoint (scR s₀)
  k_i : (kR s₀).Disjoint (inR s₀)
  k_o : (kR s₀).Disjoint (outR s₀)
  k_s : (kR s₀).Disjoint (scR s₀)

/-- The frame saving `x30`, below the stack pointer. -/
abbrev stkR (s₀ : State) : Region := ⟨s₀.sp - 16, 16⟩

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  i : (stkR s₀).Disjoint (inR s₀)
  o : (stkR s₀).Disjoint (outR s₀)
  k : (stkR s₀).Disjoint (kR s₀)
  s : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Hmac.initSha256AArch64.pre s₀) : Pre s₀ ∧ Stack s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13⟩⟩

theorem K0_length (s₀ : State) (hp : Pre s₀) : (K0 s₀).length = 64 := by
  simp [K0, bytesAt_length]; have := hp.kl_le; omega

theorem blockKey_eq {s₀ : State} (hp : Pre s₀) :
    blockKey sha256 (bytesAt s₀.mem (kp s₀) (kl s₀)) = K0 s₀ := by
  have := hp.kl_le
  simp [blockKey, sha256, K0, bytesAt_length, show ¬ (64 < kl s₀) by omega]

/-! ## `H⁽⁰⁾` -/

open VG.Proof.MdStream.AArch64.WP (cons)

/-- The three instructions storing the 32-bit word `x` at `[b + off]`. -/
def word (b : Reg) (x : BitVec 32) (off : Nat) : List Instr :=
  [.movz .w .x9 (x.extractLsb' 0 16) 0, .movk .w .x9 (x.extractLsb' 16 16) 1, .str .w .x9 b off]

theorem h0_eq (b : Reg) : h0 b = word b H0[0] 0 ++ word b H0[1] 4 ++ word b H0[2] 8 ++ word b H0[3] 12 ++
    word b H0[4] 16 ++ word b H0[5] 20 ++ word b H0[6] 24 ++ word b H0[7] 28 := rfl

theorem word_ok {b : Reg} (hb : b ≠ .x9) {x : BitVec 32} {off : Nat} (ho : off % 4 = 0 ∧ off < 16384)
    {rest : List Instr} {s : State} {Q : State → Prop}
    (hout : InRegions s.wr (s.gpr b + BitVec.ofNat 64 off) 4)
    (k : ∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = s.mem.writeW (s.gpr b + BitVec.ofNat 64 off) x → WP isa (.block rest) s' Q) :
    WP isa (.block (word b x off ++ rest)) s Q := by
  simp only [word, List.cons_append, List.nil_append]
  refine cons exec_movz_w (cons exec_movk_w (cons (exec_str_w ho ?_) (k _ ?_ rfl rfl rfl ?_)))
  · simpa [State.write, hb] using hout
  · intro r hr; simp [State.write, hr]
  · simp only [State.write, ite_true, hb, ite_false]
    congr 1
    exact movzk x

/-- `H⁽⁰⁾` stored at `b`. -/
theorem h0_ok {b : Reg} (hb : b ≠ .x9) {s : State} {rest : List Instr} {Q : State → Prop}
    (o : ∀ k < 8, InRegions s.wr (s.gpr b + BitVec.ofNat 64 (4 * k)) 4)
    (k : ∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeState s.mem (s.gpr b) H0 → WP isa (.block rest) s' Q) :
    WP isa (.block (h0 b ++ rest)) s Q := by
  rw [h0_eq]
  simp only [List.append_assoc]
  refine word_ok hb (by decide) (o 0 (by omega)) fun s1 g1 _ wr1 sp1 m1 => ?_
  have k1 : s1.gpr b = s.gpr b := g1 _ hb
  refine word_ok hb (by decide) (by rw [wr1, k1]; exact o 1 (by omega)) fun s2 g2 _ wr2 sp2 m2 => ?_
  have k2 : s2.gpr b = s.gpr b := by rw [g2 _ hb, k1]
  have w2 : s2.wr = s.wr := by rw [wr2, wr1]
  refine word_ok hb (by decide) (by rw [w2, k2]; exact o 2 (by omega)) fun s3 g3 _ wr3 sp3 m3 => ?_
  have k3 : s3.gpr b = s.gpr b := by rw [g3 _ hb, k2]
  have w3 : s3.wr = s.wr := by rw [wr3, w2]
  refine word_ok hb (by decide) (by rw [w3, k3]; exact o 3 (by omega)) fun s4 g4 _ wr4 sp4 m4 => ?_
  have k4 : s4.gpr b = s.gpr b := by rw [g4 _ hb, k3]
  have w4 : s4.wr = s.wr := by rw [wr4, w3]
  refine word_ok hb (by decide) (by rw [w4, k4]; exact o 4 (by omega)) fun s5 g5 _ wr5 sp5 m5 => ?_
  have k5 : s5.gpr b = s.gpr b := by rw [g5 _ hb, k4]
  have w5 : s5.wr = s.wr := by rw [wr5, w4]
  refine word_ok hb (by decide) (by rw [w5, k5]; exact o 5 (by omega)) fun s6 g6 _ wr6 sp6 m6 => ?_
  have k6 : s6.gpr b = s.gpr b := by rw [g6 _ hb, k5]
  have w6 : s6.wr = s.wr := by rw [wr6, w5]
  refine word_ok hb (by decide) (by rw [w6, k6]; exact o 6 (by omega)) fun s7 g7 _ wr7 sp7 m7 => ?_
  have k7 : s7.gpr b = s.gpr b := by rw [g7 _ hb, k6]
  have w7 : s7.wr = s.wr := by rw [wr7, w6]
  refine word_ok hb (by decide) (by rw [w7, k7]; exact o 7 (by omega)) fun s8 g8 rd8 wr8 sp8 m8 => ?_
  rename_i rd1 rd2 rd3 rd4 rd5 rd6 rd7
  refine k s8 (fun r h => by rw [g8 r h, g7 r h, g6 r h, g5 r h, g4 r h, g3 r h, g2 r h, g1 r h])
    (by rw [rd8, rd7, rd6, rd5, rd4, rd3, rd2, rd1]) (by rw [wr8, w7])
    (by rw [sp8, sp7, sp6, sp5, sp4, sp3, sp2, sp1]) ?_
  rw [m8, m7, m6, m5, m4, m3, m2, m1, k7, k6, k5, k4, k3, k2, k1]
  rfl

/-- Writing a hash value stays within its 32 bytes. -/
theorem writeState_frame (m : Mem) (p : Addr) (v : Spec.Sha256.HashValue) :
    Frame [⟨p, 32⟩] m (writeState m p v) := by
  have c : ∀ k, k < 8 → (⟨p, 32⟩ : Region).Contains (p + BitVec.ofNat 64 (4 * k)) (32 / 8) :=
    fun k hk => contains_offset (by omega) (by omega)
  simp only [writeState]
  refine (((((((((Frame.refl _ _).writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _
    (c 2 ?_)).writeW ?_ _ (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _
    (c 6 ?_)).writeW ?_ _ (c 7 ?_)) <;> simp

/-! ## The key block -/

/-- The memory while building the two buffers: `j` bytes of `K₀ ⊕ ipad` and
`K₀ ⊕ opad` are written. -/
structure BufMem (s₀ : State) (j : Nat) (m : Mem) : Prop where
  stI : stateAt m (inn s₀) = H0
  stO : stateAt m (out s₀) = H0
  bufI : bytesAt m (inn s₀ + 32) j = ((K0 s₀).take j).map (· ^^^ ipad)
  bufO : bytesAt m (out s₀ + 32) j = ((K0 s₀).take j).map (· ^^^ opad)
  saved : Saved s₀ m
  frame : Frame [inR s₀, outR s₀, scR s₀] s₀.mem m

/-- The registers while building the two buffers (`x24` = `j`). -/
structure Buf (s₀ : State) (j : Nat) (s : State) : Prop where
  j_le : j ≤ 64
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = inn s₀
  x20 : s.gpr .x20 = scr s₀
  x21 : s.gpr .x21 = out s₀
  x24 : s.gpr .x24 = BitVec.ofNat 64 j
  x14 : s.gpr .x14 = (0x36 : BitVec 16).setWidth 64
  x15 : s.gpr .x15 = (0x5c : BitVec 16).setWidth 64
  mem : BufMem s₀ j s.mem

/-- In the key loop: `x22` points at key byte `j`, and `x23` counts the key bytes left. -/
structure Key (s₀ : State) (j : Nat) (s : State) : Prop extends Buf s₀ j s where
  x22 : s.gpr .x22 = kp s₀ + BitVec.ofNat 64 j
  x23 : s.gpr .x23 = BitVec.ofNat 64 (kl s₀ - j)

/-- In the pad loop: `x11` counts the bytes left. -/
structure Pad (s₀ : State) (j : Nat) (s : State) : Prop extends Buf s₀ j s where
  x11 : s.gpr .x11 = BitVec.ofNat 64 (64 - j)

theorem sub32 (p : Addr) : Region.Sub ⟨p, 32⟩ ⟨p, 96⟩ := Region.sub_prefix (by omega)

theorem save_sub (s₀ : State) : Region.Sub ⟨scr s₀ + BitVec.ofNat 64 112, 48⟩ (scR s₀) :=
  sub_offset (by omega) (by omega)

/-- `Saved` survives a write outside the save area `scratch[112..160)`. -/
theorem saved_frame {s₀ : State} {m m' : Mem} (h : Saved s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 112, 48⟩ r) : Saved s₀ m' := by
  intro p hp'
  rw [← h p hp']
  refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  refine (hd r hr).sub_left ?_
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · intro a ha; simp only [Region.Contains] at *; bv_omega

/-- `Saved` survives a write outside the scratch space. -/
theorem saved_frame' {s₀ : State} {m m' : Mem} (h : Saved s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (scR s₀).Disjoint r) : Saved s₀ m' :=
  saved_frame h hf fun r hr => (hd r hr).sub_left (save_sub s₀)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save .x4 ++ [mov .x19 .x0, mov .x20 .x4, mov .x21 .x1, mov .x22 .x2, mov .x23 .x3] ++
      h0 .x19 ++ h0 .x21 ++ ([.movz .x .x14 0x36 0, .movz .x .x15 0x5c 0, .movz .x .x24 0 0] : List Instr))) s₀
      (Key s₀ 0) := by
  simp only [List.append_assoc]
  refine save_ok (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hp.wr], contains_offset hd₂ (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => ?_
  have h19 : s₆.gpr .x19 = inn s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, g₁]
  have h20 : s₆.gpr .x20 = scr s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁]
  have h21 : s₆.gpr .x21 = out s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  have h22 : s₆.gpr .x22 = kp s₀ := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  have h23 : s₆.gpr .x23 = s₀.gpr .x3 := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  have m₆ : s₆.mem = saveMem s₀.mem (scr s₀) s₀.gpr := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  have sp₆ : s₆.sp = s₀.sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  refine h0_ok (by decide) (fun k hk => ⟨inR s₀, by simp [wr₆, hp.wr], by
    rw [h19]; exact contains_offset (by omega) (by omega)⟩) fun s₇ g₇ rd₇ wr₇ sp₇ m₇ => ?_
  refine h0_ok (by decide) (fun k hk => ⟨outR s₀, by simp [wr₇, wr₆, hp.wr], by
    rw [g₇ _ (by decide), h21]; exact contains_offset (by omega) (by omega)⟩)
    fun s₈ g₈ rd₈ wr₈ sp₈ m₈ => ?_
  refine wp_movz fun s₉ u₉ => wp_movz fun s₁₀ u₁₀ => wp_movz fun s₁₁ u₁₁ => WP.block_nil ?_
  have k : ∀ r, r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → r ≠ .x24 → s₁₁.gpr r = s₆.gpr r :=
    fun r a b c d => by rw [u₁₁.other r d, u₁₀.other r c, u₉.other r b, g₈ r a, g₇ r a]
  rw [h19] at m₇
  rw [g₇ _ (by decide), h21] at m₈
  have hm : s₁₁.mem = writeState (writeState (saveMem s₀.mem (scr s₀) s₀.gpr) (inn s₀) H0) (out s₀) H0 := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, m₈, m₇, m₆]
  have fS := saveMem_frame s₀.mem (scr s₀) s₀.gpr
  have fI := writeState_frame (saveMem s₀.mem (scr s₀) s₀.gpr) (inn s₀) H0
  have fO := writeState_frame (writeState (saveMem s₀.mem (scr s₀) s₀.gpr) (inn s₀) H0) (out s₀) H0
  have ds : ∀ p : Addr, ∀ r : Region, r.Disjoint ⟨p, 96⟩ → r.Disjoint ⟨p, 32⟩ :=
    fun p r h => h.sub_right (sub32 p)
  refine ⟨⟨by omega, by rw [u₁₁.rd, u₁₀.rd, u₉.rd, rd₈, rd₇, rd₆],
    by rw [u₁₁.wr, u₁₀.wr, u₉.wr, wr₈, wr₇, wr₆], by rw [u₁₁.sp, u₁₀.sp, u₉.sp, sp₈, sp₇, sp₆],
    by rw [k _ (by decide) (by decide) (by decide) (by decide), h19],
    by rw [k _ (by decide) (by decide) (by decide) (by decide), h20],
    by rw [k _ (by decide) (by decide) (by decide) (by decide), h21], by rw [u₁₁.gpr]; rfl,
    by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr],
    by rw [u₁₁.other _ (by decide), u₁₀.gpr],
    ⟨?_, ?_, by simp [bytesAt], by simp [bytesAt], ?_, ?_⟩⟩, ?_, ?_⟩
  · rw [hm]
    refine (Proof.Sha256.Stream.stateAt_congr fun i hi => ?_).trans
      (stateAt_writeState (saveMem s₀.mem (scr s₀) s₀.gpr) _ _)
    exact frame_bytes fO (R := ⟨inn s₀, 32⟩) (by simpa using ds _ _ (hp.i_o.sub_left (sub32 _))) (by simp) hi
  · rw [hm, stateAt_writeState]
  · rw [hm]
    refine saved_frame' (saved_frame' (saveMem_saved _ _ _) fI ?_) fO ?_ <;> simp only [List.mem_singleton] <;>
      rintro r rfl
    · exact ds _ _ hp.i_s.symm
    · exact ds _ _ hp.o_s.symm
  · rw [hm]
    refine ((fS.mono ?_).trans (fI.sub ?_)).trans (fO.sub ?_)
    · simp
    · simp only [List.mem_singleton]; rintro r rfl; exact ⟨inR s₀, by simp, sub32 _⟩
    · simp only [List.mem_singleton]; rintro r rfl; exact ⟨outR s₀, by simp, sub32 _⟩
  · rw [k _ (by decide) (by decide) (by decide) (by decide), h22]; simp
  · rw [k _ (by decide) (by decide) (by decide) (by decide), h23]; simp

/-- A byte written right after `j` bytes of a buffer, in both buffers. -/
theorem buf_write {s₀ : State} (hp : Pre s₀) {j : Nat} {m : Mem} (h : BufMem s₀ j m) (hj : j < 64) :
    BufMem s₀ (j + 1) ((m.writeW (inn s₀ + 32 + BitVec.ofNat 64 j)
      ((K0 s₀)[j]'(by rw [K0_length s₀ hp]; omega) ^^^ ipad)).writeW
      (out s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j]'(by rw [K0_length s₀ hp]; omega) ^^^ opad)) := by
  have hl : j < (K0 s₀).length := by rw [K0_length s₀ hp]; omega
  set x := (K0 s₀)[j] ^^^ ipad
  set y := (K0 s₀)[j] ^^^ opad
  let bI : Region := ⟨inn s₀ + 32, 64⟩
  let bO : Region := ⟨out s₀ + 32, 64⟩
  have sI : Region.Sub bI (inR s₀) := sub_offset (off := 32) (by omega) (by omega)
  have sO : Region.Sub bO (outR s₀) := sub_offset (off := 32) (by omega) (by omega)
  have f₁ : Frame [bI] m (m.writeW (inn s₀ + 32 + BitVec.ofNat 64 j) x) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) x (contains_offset (by omega) (by omega))
  have f₂ : Frame [bO] (m.writeW (inn s₀ + 32 + BitVec.ofNat 64 j) x)
      ((m.writeW (inn s₀ + 32 + BitVec.ofNat 64 j) x).writeW (out s₀ + 32 + BitVec.ofNat 64 j) y) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) y (contains_offset (by omega) (by omega))
  have F := (f₁.mono (rs' := [bI, bO]) (by simp)).trans (f₂.mono (by simp))
  have dIO : bI.Disjoint bO := (hp.i_o.sub_left sI).sub_right sO
  have st : ∀ p : Addr, (∀ r ∈ [bI, bO], Region.Disjoint ⟨p, 32⟩ r) →
      stateAt ((m.writeW (inn s₀ + 32 + BitVec.ofNat 64 j) x).writeW (out s₀ + 32 + BitVec.ofNat 64 j) y) p =
        stateAt m p :=
    fun p hd => Proof.Sha256.Stream.stateAt_congr fun i hi => frame_bytes F (R := ⟨p, 32⟩) hd (by simp) hi
  have self : ∀ q : Addr, Region.Disjoint ⟨q, 32⟩ ⟨q + 32, 64⟩ := fun q a h₁ h₂ => by
    simp only [Region.Contains] at h₁ h₂; bv_omega
  refine ⟨?_, ?_, ?_, ?_, saved_frame' h.saved F ?_, h.frame.trans (F.sub ?_)⟩
  · rw [st _ ?_, h.stI]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact self _
    · exact (hp.i_o.sub_left (sub32 _)).sub_right sO
  · rw [st _ ?_, h.stO]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact (hp.i_o.symm.sub_left (sub32 _)).sub_right sI
    · exact self _
  · rw [Proof.Sha256.Stream.bytesAt_congr
        (fun i hi => frame_bytes f₂ (R := ⟨inn s₀ + 32, j + 1⟩) ?_ (by simp; omega) hi),
      bytesAt_snoc _ _ (by omega), h.bufI, List.take_succ_eq_append_getElem hl, List.map_append]
    · rfl
    · simp only [List.mem_singleton]; rintro r rfl
      exact dIO.sub_left (Region.sub_prefix (by omega))
  · rw [bytesAt_snoc _ _ (by omega),
      Proof.Sha256.Stream.bytesAt_congr
        (fun i hi => frame_bytes f₁ (R := ⟨out s₀ + 32, j⟩) ?_ (by simp; omega) hi),
      h.bufO, List.take_succ_eq_append_getElem hl, List.map_append]
    · rfl
    · simp only [List.mem_singleton]; rintro r rfl
      exact dIO.symm.sub_left (Region.sub_prefix (by omega))
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.i_s.symm.sub_right sI
    · exact hp.o_s.symm.sub_right sO
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact ⟨inR s₀, by simp, sI⟩
    · exact ⟨outR s₀, by simp, sO⟩

/-! ## The key and pad loops -/

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  cons (s' := s.write .x d (s.gpr n ^^^ s.gpr m)) (by simp [exec, State.read])
    (k _ (Proof.MdStream.AArch64.Upd.write64 _ _ _))

theorem xor_byte (b : Byte) (v : BitVec 16) :
    (b.setWidth 64 ^^^ v.setWidth 64).setWidth 8 = b ^^^ v.setWidth 8 := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

theorem K0_lt {s₀ : State} {j : Nat} (hj : j < kl s₀) (h : j < (K0 s₀).length) :
    (K0 s₀)[j] = s₀.mem (kp s₀ + BitVec.ofNat 64 j) := by
  simp only [K0]
  rw [List.getElem_append_left (by rw [bytesAt_length]; exact hj)]
  simp [bytesAt]

theorem K0_ge {s₀ : State} {j : Nat} (hj : kl s₀ ≤ j) (h : j < (K0 s₀).length) : (K0 s₀)[j] = 0 := by
  simp only [K0]
  rw [List.getElem_append_right (by rw [bytesAt_length]; exact hj)]
  simp

def keyBody : List Instr :=
  [.ldrb .x9 .x22 0,
    .logic .eor .x .x10 .x9 .x14, .add .x .x12 .x19 .x24, .strb .x10 .x12 32,
    .logic .eor .x .x10 .x9 .x15, .add .x .x12 .x21 .x24, .strb .x10 .x12 32,
    .addImm .x .x22 .x22 1, .addImm .x .x24 .x24 1, .subImm .x .x23 .x23 1]

theorem keyLoop_eq : keyLoop = .loop (.block keyBody) (.nonzero .x .x23) := rfl

theorem buf_in {s₀ : State} (hp : Pre s₀) {s : State} (hwr : s.wr = s₀.wr) {j : Nat} (hj : j < 64)
    {p : Addr} (hpR : p = inn s₀ ∨ p = out s₀) : InRegions s.wr (p + 32 + BitVec.ofNat 64 j) 1 := by
  refine ⟨⟨p, 96⟩, by rcases hpR with rfl | rfl <;> simp [hwr, hp.wr], ?_⟩
  rw [BitVec.add_assoc, show (32 : Addr) + BitVec.ofNat 64 j = BitVec.ofNat 64 (32 + j) by
    rw [BitVec.ofNat_add]; rfl]
  exact contains_offset (by omega) (by omega)

theorem key_step {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : j < kl s₀) {s : State} (h : Key s₀ j s) :
    WP isa (.block keyBody) s (Key s₀ (j + 1)) := by
  have hkl := hp.kl_le
  have hl : j < (K0 s₀).length := by rw [K0_length s₀ hp]; omega
  have hin : InRegions (s.rd ++ s.wr) (kp s₀ + BitVec.ofNat 64 j) 1 :=
    ⟨kR s₀, by simp [h.rd, hp.rd], contains_offset (by omega) (by omega)⟩
  have hbyte : s.mem (kp s₀ + BitVec.ofNat 64 j) = (K0 s₀)[j] := by
    rw [K0_lt hj hl]
    refine frame_bytes h.mem.frame (R := kR s₀) ?_ (by show kl s₀ ≤ 2 ^ 64; omega) hj
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.k_i
    · exact hp.k_o
    · exact hp.k_s
  unfold keyBody
  refine wp_ldrb (a := kp s₀ + BitVec.ofNat 64 j) (by omega) (by rw [h.x22]; simp) hin fun s₁ u₁ => ?_
  refine wp_eor fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  refine wp_strb (a := inn s₀ + 32 + BitVec.ofNat 64 j) (by omega) ?_
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact buf_in hp h.wr (by omega) (.inl rfl)) fun s₄ u₄ => ?_
  · simp (config := {decide := true}) only [u₃.gpr, u₂.other, u₁.other, h.x19, h.x24]; bv_omega
  refine wp_eor fun s₅ u₅ => wp_add fun s₆ u₆ => ?_
  refine wp_strb (a := out s₀ + 32 + BitVec.ofNat 64 j) (by omega) ?_
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact buf_in hp h.wr (by omega) (.inr rfl))
    fun s₇ u₇ => ?_
  · simp (config := {decide := true}) only [u₆.gpr, u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other,
      h.x21, h.x24]
    bv_omega
  refine wp_addImm (by omega) fun s₈ u₈ => wp_addImm (by omega) fun s₉ u₉ =>
    wp_subImm (by omega) fun s₁₀ u₁₀ => WP.block_nil ?_
  have k : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 → s₁₀.gpr r = s.gpr r :=
    fun r a b c d e f => by
      rw [u₁₀.other r e, u₉.other r f, u₈.other r d, u₇.gpr, u₆.other r c, u₅.other r b, u₄.gpr,
        u₃.other r c, u₂.other r b, u₁.other r a]
  have v₁ : (s₃.gpr .x10).setWidth 8 = (K0 s₀)[j] ^^^ ipad := by
    simp (config := {decide := true}) only [u₃.other, u₂.gpr, u₁.gpr, u₁.other, h.x14, xor_byte, hbyte]
    rfl
  have v₂ : (s₆.gpr .x10).setWidth 8 = (K0 s₀)[j] ^^^ opad := by
    simp (config := {decide := true}) only [u₆.other, u₅.gpr, u₄.gpr, u₃.other, u₂.other, u₁.gpr,
      u₁.other, h.x15, xor_byte, hbyte]
    rfl
  have hm : s₁₀.mem = (s.mem.writeW (inn s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j] ^^^ ipad)).writeW
      (out s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j] ^^^ opad) := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, v₂, u₆.mem, u₅.mem, u₄.mem, v₁, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨by omega, by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x19],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x20],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x21], ?_,
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x14],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x15],
    by rw [hm]; exact buf_write hp h.mem (by omega)⟩, ?_, ?_⟩
  · simp (config := {decide := true}) only [u₁₀.other, u₉.gpr, u₈.other, u₇.gpr, u₆.other, u₅.other,
      u₄.gpr, u₃.other, u₂.other, u₁.other, h.x24]
    rw [BitVec.ofNat_add]
  · simp (config := {decide := true}) only [u₁₀.other, u₉.other, u₈.gpr, u₇.gpr, u₆.other, u₅.other,
      u₄.gpr, u₃.other, u₂.other, u₁.other, h.x22]
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  · simp (config := {decide := true}) only [u₁₀.gpr, u₉.other, u₈.other, u₇.gpr, u₆.other, u₅.other,
      u₄.gpr, u₃.other, u₂.other, u₁.other, h.x23]
    rw [show (BitVec.ofNat 64 1 : BitVec 64) = 1 from rfl, ← show kl s₀ - j - 1 = kl s₀ - (j + 1) by omega,
      ← sub_ofNat (a := kl s₀ - j) (b := 1) (by omega)]
    rfl

def padBody : List Instr :=
  [.add .x .x12 .x19 .x24, .strb .x14 .x12 32, .add .x .x12 .x21 .x24, .strb .x15 .x12 32,
    .addImm .x .x24 .x24 1, .subImm .x .x11 .x11 1]

theorem padLoop_eq : padLoop = .loop (.block padBody) (.nonzero .x .x11) := rfl

theorem ipad_byte : ((0x36 : BitVec 16).setWidth 64).setWidth 8 = (0 : Byte) ^^^ ipad := by decide
theorem opad_byte : ((0x5c : BitVec 16).setWidth 64).setWidth 8 = (0 : Byte) ^^^ opad := by decide

theorem pad_step {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : kl s₀ ≤ j) (hj' : j < 64) {s : State}
    (h : Pad s₀ j s) : WP isa (.block padBody) s (Pad s₀ (j + 1)) := by
  have hl : j < (K0 s₀).length := by rw [K0_length s₀ hp]; omega
  unfold padBody
  refine wp_add fun s₁ u₁ => ?_
  refine wp_strb (a := inn s₀ + 32 + BitVec.ofNat 64 j) (by omega) ?_
    (by rw [u₁.wr]; exact buf_in hp h.wr hj' (.inl rfl)) fun s₂ u₂ => ?_
  · rw [u₁.gpr, h.x19, h.x24]; bv_omega
  refine wp_add fun s₃ u₃ => ?_
  refine wp_strb (a := out s₀ + 32 + BitVec.ofNat 64 j) (by omega) ?_
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact buf_in hp h.wr hj' (.inr rfl)) fun s₄ u₄ => ?_
  · simp (config := {decide := true}) only [u₃.gpr, u₂.gpr, u₁.other, h.x21, h.x24]; bv_omega
  refine wp_addImm (by omega) fun s₅ u₅ => wp_subImm (by omega) fun s₆ u₆ => WP.block_nil ?_
  have k : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x24 → s₆.gpr r = s.gpr r := fun r a b c => by
    rw [u₆.other r a, u₅.other r c, u₄.gpr, u₃.other r b, u₂.gpr, u₁.other r b]
  have hm : s₆.mem = (s.mem.writeW (inn s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j] ^^^ ipad)).writeW
      (out s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j] ^^^ opad) := by
    simp (config := {decide := true}) only [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.other,
      u₂.gpr, u₁.other, h.x14, h.x15, K0_ge hj hl, ipad_byte, opad_byte]
  refine ⟨⟨by omega, by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    by rw [k _ (by decide) (by decide) (by decide), h.x19],
    by rw [k _ (by decide) (by decide) (by decide), h.x20],
    by rw [k _ (by decide) (by decide) (by decide), h.x21], ?_,
    by rw [k _ (by decide) (by decide) (by decide), h.x14],
    by rw [k _ (by decide) (by decide) (by decide), h.x15],
    by rw [hm]; exact buf_write hp h.mem hj'⟩, ?_⟩
  · simp (config := {decide := true}) only [u₆.other, u₅.gpr, u₄.gpr, u₃.other, u₂.gpr, u₁.other, h.x24]
    rw [BitVec.ofNat_add]
  · simp (config := {decide := true}) only [u₆.gpr, u₅.other, u₄.gpr, u₃.other, u₂.gpr, u₁.other, h.x11]
    rw [show 64 - (j + 1) = 64 - j - 1 by omega, ← sub_ofNat (a := 64 - j) (b := 1) (by omega)]

theorem key_loop_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Key s₀ 0 s) (hk : 0 < kl s₀) :
    WP isa keyLoop s (Buf s₀ (kl s₀)) := by
  have := hp.kl_le
  rw [keyLoop_eq]
  refine WP.loop (M := isa) (fun n s => ∃ j, n = kl s₀ - j ∧ j < kl s₀ ∧ Key s₀ j s) ?_ (kl s₀) s
    ⟨0, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, hb⟩
  refine WP.mono (key_step hp hj hb) fun s' hb' => ?_
  have hz : isa.eval (.nonzero .x .x23) s' = some (decide (kl s₀ - (j + 1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x .x23) s' = _
    rw [eval_nonzero, hb'.x23, bne, ofNat_beq_zero (by omega)]
    simp
  by_cases hl : kl s₀ - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
    rw [show kl s₀ = j + 1 by omega]; exact hb'.toBuf
  · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega, j + 1, rfl, by omega, hb'⟩

theorem pad_loop_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Pad s₀ (kl s₀) s) (hk : kl s₀ < 64) :
    WP isa padLoop s (Buf s₀ 64) := by
  rw [padLoop_eq]
  refine WP.loop (M := isa) (fun n s => ∃ j, n = 64 - j ∧ kl s₀ ≤ j ∧ j < 64 ∧ Pad s₀ j s) ?_
    (64 - kl s₀) s ⟨kl s₀, rfl, (Nat.le_refl _), hk, h⟩
  rintro n s ⟨j, rfl, hj, hj', hb⟩
  refine WP.mono (pad_step hp hj hj' hb) fun s' hb' => ?_
  have hz : isa.eval (.nonzero .x .x11) s' = some (decide (64 - (j + 1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x .x11) s' = _
    rw [eval_nonzero, hb'.x11, bne, ofNat_beq_zero (by omega)]
    simp
  by_cases hl : 64 - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
    rw [show (64 : Nat) = j + 1 by omega]; exact hb'.toBuf
  · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega, j + 1, rfl, by omega, by omega, hb'⟩

/-! ## The two compressions -/

/-- The inlined compression of the block in the buffer of the state at `p`
(the inner or the outer one). -/
theorem compress_ok {s₀ : State} (hp : Pre s₀) {p : Addr} (hpR : p = inn s₀ ∨ p = out s₀) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (h19 : s.gpr .x19 = p) (h20 : s.gpr .x20 = scr s₀)
    (h1 : s.gpr .x1 = p + 32) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      s'.sp = s.sp →
      Frame [⟨p, 32⟩, ⟨scr s₀, 112⟩] s.mem s'.mem →
      stateAt s'.mem p = Spec.Sha256.compress (stateAt s.mem p) (Spec.Sha256.blockAt s.mem (p + 32)) →
      Q s') :
    WP isa compressAt s Q := by
  have hs : Region.Disjoint ⟨p, 96⟩ (scR s₀) ∧ ⟨p, 96⟩ ∈ s₀.wr := by
    rcases hpR with rfl | rfl
    · exact ⟨hp.i_s, by simp [hp.wr]⟩
    · exact ⟨hp.o_s, by simp [hp.wr]⟩
  obtain ⟨d, hm⟩ := hs
  have e32 : Region.Sub ⟨p, 32⟩ ⟨p, 96⟩ := Region.sub_prefix (by omega)
  have eb : Region.Sub ⟨p + 32, 64⟩ ⟨p, 96⟩ := sub_offset (off := 32) (by omega) (by omega)
  have e112 : Region.Sub ⟨scr s₀, 112⟩ (scR s₀) := Region.sub_prefix (by omega)
  refine compressAt_ok h19 h20 h1 ((d.sub_left e32).sub_right e112) ?_ ((d.sub_left eb).sub_right e112)
    ?_ ?_ hQ
  · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
  · rw [hrd, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨p, 96⟩, by simp [hm], 32, rfl, by simp⟩
    · exact ⟨⟨p, 96⟩, by simp [hm], 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp [hp.wr], 0, by simp, by simp⟩
  · rw [hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨p, 96⟩, hm, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp [hp.wr], 0, by simp, by simp⟩

/-- A state that a write outside it keeps. -/
theorem state_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 96⟩ r) :
    stateAt m' p = stateAt m p ∧ bytesAt m' (p + 32) 64 = bytesAt m (p + 32) 64 := by
  refine ⟨Proof.Sha256.Stream.stateAt_congr fun i hi =>
      frame_bytes hf (R := ⟨p, 32⟩) (fun r hr => (hd r hr).sub_left (sub32 p)) (by simp) hi,
    Proof.Sha256.Stream.bytesAt_congr fun i hi =>
      frame_bytes hf (R := ⟨p + 32, 64⟩)
        (fun r hr => (hd r hr).sub_left (sub_offset (off := 32) (by omega) (by omega))) (by simp) hi⟩

/-! ## Epilogue -/

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop :=
  (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = s₀.sp ∧ Proof.Hmac.initSha256AArch64.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (h20 : s.gpr .x20 = scr s₀) (hsp : s.sp = s₀.sp) (hsv : Saved s₀ s.mem)
    (hI : Repr s.mem (inn s₀) (xorPad (K0 s₀) ipad)) (hO : Repr s.mem (out s₀) (xorPad (K0 s₀) opad)) :
    WP isa (.block restore) s (Post s₀) := by
  refine restore_ok (scr := scr s₀) h20
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hrd, hwr, hp.wr], contains_offset hd₂ (by omega)⟩) s₀.gpr
    hsv fun s' hs _ hmem _ _ hsp' => ⟨hs, by rw [hsp', hsp], ?_⟩
  simp only [Proof.Hmac.initSha256AArch64]
  rw [blockKey_eq hp, hmem]
  exact ⟨hI, hO⟩

/-- No instruction of `init` writes the callee-saved registers it does not save. -/
theorem untouched_ok : ∀ r ∈ untouched, ∀ i ∈ instrs initMain, dstOf i ≠ some r := by
  have : ((instrs initMain).all fun i => untouched.all fun r => dstOf i != some r) = true :=
    instrs_keeps (by decide +kernel)
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr
  simpa using this

/-! ## Correctness -/

theorem buf_full {s₀ : State} (hp : Pre s₀) {m : Mem} (h : BufMem s₀ 64 m) :
    bytesAt m (inn s₀ + 32) 64 = xorPad (K0 s₀) ipad ∧ bytesAt m (out s₀ + 32) 64 = xorPad (K0 s₀) opad := by
  rw [h.bufI, h.bufO, List.take_of_length_le (by rw [K0_length s₀ hp])]
  exact ⟨rfl, rfl⟩

/-- `init` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain {s₀ : State} (hp : Pre s₀) :
    WP isa initMain s₀ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ Proof.Hmac.initSha256AArch64.post s₀ s' := by
  have hkl := hp.kl_le
  refine WP.mono (Proof.MdStream.AArch64.WP.gprs (Q := Post s₀) ?_ untouched_ok) fun s' ⟨⟨hsv, hsp, hpost⟩, hu⟩ =>
    ⟨fun r hr h30 => ?_, hsp, hpost⟩
  · unfold initMain
    refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
    -- The key.
    refine WP.seq (WP.mono (Q := Buf s₀ (kl s₀)) ?_ fun s₂ h₂ => ?_)
    · refine WP.ite (decide (kl s₀ = 0))
        (by show VG.AArch64.eval (.zero .x .x23) s₁ = _
            rw [eval_zero, h₁.x23, Nat.sub_zero, ofNat_beq_zero (by omega)])
        (fun hb => WP.block_nil ?_) (fun hb => key_loop_ok hp h₁ ?_)
      · simp only [decide_eq_true_eq] at hb; rw [hb]; exact h₁.toBuf
      · simp only [decide_eq_false_iff_not] at hb; omega
    -- The padding.
    refine WP.seq (wp_movz fun s₃ u₃ => wp_sub fun s₄ u₄ => WP.block_nil ?_)
    have hP : Pad s₀ (kl s₀) s₄ := by
      refine ⟨⟨h₂.j_le, by rw [u₄.rd, u₃.rd, h₂.rd], by rw [u₄.wr, u₃.wr, h₂.wr],
        by rw [u₄.sp, u₃.sp, h₂.sp], ?_, ?_, ?_, ?_, ?_, ?_, by rw [u₄.mem, u₃.mem]; exact h₂.mem⟩, ?_⟩
      all_goals simp (config := {decide := true}) only [u₄.gpr, u₄.other, u₃.gpr, u₃.other, h₂.x19,
        h₂.x20, h₂.x21, h₂.x24, h₂.x14, h₂.x15]
      rw [← sub_ofNat hkl]; rfl
    refine WP.seq (WP.mono (Q := Buf s₀ 64) ?_ fun s₆ h₆ => ?_)
    · refine WP.ite (decide (64 - kl s₀ = 0))
        (by show VG.AArch64.eval (.zero .x .x11) s₄ = _
            rw [eval_zero, hP.x11, ofNat_beq_zero (by omega)])
        (fun hb => WP.block_nil ?_) (fun hb => pad_loop_ok hp hP ?_)
      · simp only [decide_eq_true_eq] at hb
        exact (show kl s₀ = 64 by omega) ▸ hP.toBuf
      · simp only [decide_eq_false_iff_not] at hb; omega
    obtain ⟨bI, bO⟩ := buf_full hp h₆.mem
    -- The inner block.
    refine WP.seq (wp_addImm (by omega) fun s₇ u₇ => WP.block_nil ?_)
    refine WP.seq (compress_ok hp (.inl rfl) (by rw [u₇.rd, h₆.rd]) (by rw [u₇.wr, h₆.wr])
      (by rw [u₇.other _ (by decide), h₆.x19]) (by rw [u₇.other _ (by decide), h₆.x20])
      (by rw [u₇.gpr, h₆.x19]; rfl) fun s₈ rd₈ wr₈ cs₈ sp₈ fr₈ st₈ => ?_)
    have hI₈ : Repr s₈.mem (inn s₀) (xorPad (K0 s₀) ipad) :=
      repr_block (by rw [u₇.mem]; exact h₆.mem.stI) (by rw [u₇.mem]; exact bI)
        (by simp [xorPad, K0_length s₀ hp]) st₈
    have dO : ∀ r ∈ [(⟨inn s₀, 32⟩ : Region), ⟨scr s₀, 112⟩], Region.Disjoint ⟨out s₀, 96⟩ r := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.i_o.symm.sub_right (sub32 _)
      · exact hp.o_s.sub_right (Region.sub_prefix (by omega))
    obtain ⟨sO₈, bO₈⟩ := state_frame fr₈ dO
    have sv₈ : Saved s₀ s₈.mem := by
      refine saved_frame (by rw [u₇.mem]; exact h₆.mem.saved) fr₈ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact (hp.i_s.symm.sub_left (save_sub s₀)).sub_right (sub32 _)
      · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
    -- The outer block.
    refine WP.seq (wp_mov fun s₉ u₉ => wp_addImm (by omega) fun s₁₀ u₁₀ => WP.block_nil ?_)
    have x21₈ : s₈.gpr .x21 = out s₀ := by
      rw [cs₈ _ (by decide) (by decide), u₇.other _ (by decide), h₆.x21]
    have x20₈ : s₈.gpr .x20 = scr s₀ := by
      rw [cs₈ _ (by decide) (by decide), u₇.other _ (by decide), h₆.x20]
    have m₁₀ : s₁₀.mem = s₈.mem := by rw [u₁₀.mem, u₉.mem]
    refine WP.seq (compress_ok hp (.inr rfl) (by rw [u₁₀.rd, u₉.rd, rd₈, u₇.rd, h₆.rd])
      (by rw [u₁₀.wr, u₉.wr, wr₈, u₇.wr, h₆.wr])
      (by rw [u₁₀.other _ (by decide), u₉.gpr, x21₈])
      (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), x20₈])
      (by rw [u₁₀.gpr, u₉.gpr, x21₈]; rfl)
      fun s₁₁ rd₁₁ wr₁₁ cs₁₁ sp₁₁ fr₁₁ st₁₁ => ?_)
    have hO : Repr s₁₁.mem (out s₀) (xorPad (K0 s₀) opad) :=
      repr_block (by rw [m₁₀, sO₈, u₇.mem]; exact h₆.mem.stO) (by rw [m₁₀, bO₈, u₇.mem]; exact bO)
        (by simp [xorPad, K0_length s₀ hp]) st₁₁
    have hI : Repr s₁₁.mem (inn s₀) (xorPad (K0 s₀) ipad) := by
      refine repr_congr (fun i hi => frame_bytes fr₁₁ (R := inR s₀) ?_ (by simp) hi) (m₁₀ ▸ hI₈)
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.i_o.sub_right (sub32 _)
      · exact hp.i_s.sub_right (Region.sub_prefix (by omega))
    refine epilogue_ok hp (by rw [rd₁₁, u₁₀.rd, u₉.rd, rd₈, u₇.rd, h₆.rd])
      (by rw [wr₁₁, u₁₀.wr, u₉.wr, wr₈, u₇.wr, h₆.wr])
      (by rw [cs₁₁ _ (by decide) (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), x20₈])
      (by rw [sp₁₁, u₁₀.sp, u₉.sp, sp₈, u₇.sp, h₆.sp]) ?_ hI hO
    refine saved_frame (by rw [m₁₀]; exact sv₈) fr₁₁ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact (hp.o_s.symm.sub_left (save_sub s₀)).sub_right (sub32 _)
    · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv (.x19, 112) (by simp [saved])
    · exact hsv (.x20, 120) (by simp [saved])
    · exact hsv (.x21, 128) (by simp [saved])
    · exact hsv (.x22, 136) (by simp [saved])
    · exact hsv (.x23, 144) (by simp [saved])
    · exact hsv (.x24, 152) (by simp [saved])
    all_goals first | exact absurd rfl h30 | exact hu _ (by simp [untouched])

/-- The state `initMain` starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Hmac.initSha256AArch64.post s₀ s' := by
  have hpi : Pre (inner s₀) :=
    ⟨hp.kl_le, hp.rd, hp.wr, hp.i_o, hp.i_s, hp.o_s, hp.k_i, hp.k_o, hp.k_s⟩
  refine WP.frameReg hs.sp16 (fun R hR => ?_) (WP.mono (correctMain hpi) fun s' ⟨hk, hsp, hpost⟩ => ?_)
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact hs.i
    · exact hs.o
    · exact hs.s
  · refine ⟨⟨fun r hr => ?_, rfl⟩, ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · have e : bytesAt (inner s₀).mem (s₀.gpr .x2) (s₀.gpr .x3).toNat =
          bytesAt s₀.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat :=
        Proof.Sha256.Stream.bytesAt_congr fun i hi =>
          Proof.MdStream.AArch64.write_frame_bytes (R := kR s₀) hs.k (s₀.gpr .x3).isLt hi
      simpa only [Proof.Hmac.initSha256AArch64, e, State.write] using hpost

/-! ## `Verified` -/

/-- The initial taint: only the arguments are public. -/
theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Hmac.initSha256AArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition (with an empty key). -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x2000, 96⟩, ⟨0x4000, 160⟩]

theorem init_correct (s : State) (hs : Proof.Hmac.initSha256AArch64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ Proof.Hmac.initSha256AArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs).1 (pre_of hs).2
  exact ⟨t, s', he, h⟩

theorem init_ct : ConstantTime isa Proof.Hmac.initSha256AArch64.pre Proof.Hmac.initSha256AArch64.pub
    init := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ hp => agree₀ hp)
    (by taint_decide)

/-- `initSha256AArch64` with the 608 bytes of scratch of the shared contract
(sized for the x86-64 AVX2 compression function), of which the code uses 160. -/
def initWide : Contract isa :=
  { Proof.Hmac.initSha256AArch64 with
    pre := fun s =>
      let inner : Region := ⟨s.gpr .x0, 96⟩
      let outer : Region := ⟨s.gpr .x1, 96⟩
      let key : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
      let scratch : Region := ⟨s.gpr .x4, 608⟩
      let stack : Region := ⟨s.sp - 16, 16⟩
      (s.gpr .x3).toNat ≤ 64 ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
      inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
      key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
      16 ≤ s.sp.toNat ∧ stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧
      stack.Disjoint scratch }

/-- The regions `initSha256AArch64` lets the code write. -/
def narrowWr (s : State) : List Region := [⟨s.gpr .x0, 96⟩, ⟨s.gpr .x1, 96⟩, ⟨s.gpr .x4, 160⟩]

theorem initWide_pre (s : State) (h : initWide.pre s) :
    Proof.Hmac.initSha256AArch64.pre (s.withRegions s.rd (narrowWr s)) :=
  let ⟨h₁, h₂, _, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄⟩ := h
  ⟨h₁, h₂, rfl, h₄, h₅.sub_right (Region.sub_of_ble rfl), h₆.sub_right (Region.sub_of_ble rfl), h₇,
    h₈, h₉.sub_right (Region.sub_of_ble rfl), h₁₀, h₁₁, h₁₂, h₁₃,
    h₁₄.sub_right (Region.sub_of_ble rfl)⟩

/-- A state satisfying `initWide.pre`. -/
def wideSat : State := { sat with wr := [⟨0x1000, 96⟩, ⟨0x2000, 96⟩, ⟨0x4000, 608⟩] }

theorem initWide_implies : initWide.Implies (Spec.Hmac.initSha256Contract AArch64.abi 16) := by
  sig_implies [Spec.Hmac.initSha256Contract, Spec.Hmac.initSha256Sig, initWide,
    Proof.Hmac.initSha256AArch64, AArch64.abi, AArch64.argRegs] [wideSat, sat] using wideSat

/-- The proof is written against `initSha256AArch64`, widened to the shared
contract's scratch. -/
theorem init_verified :
    Verified AArch64.target Impl.Hmac.AArch64.init (Spec.Hmac.initSha256Contract AArch64.abi 16) :=
  have hsat := initWide_implies.sat_left
  (Verified.widen (Verified.of_correct init_correct init_ct
    (.refl (hsat.elim fun s hs => ⟨_, initWide_pre s hs⟩)))
    narrowWr initWide_pre
    (fun _ h => by
      obtain ⟨_, _, h₃, _⟩ := h
      rw [h₃]
      exact .cons (Region.prefix_of_ble rfl) (.cons (Region.prefix_of_ble rfl)
        (.cons (Region.prefix_of_ble rfl) .nil)))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat).of_implies initWide_implies

end VG.Proof.Hmac.AArch64.Init
