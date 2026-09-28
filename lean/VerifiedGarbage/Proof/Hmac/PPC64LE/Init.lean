import VerifiedGarbage.Proof.Hmac.PPC64LE.Common
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Init
import VerifiedGarbage.Proof.Hmac.PPC64LE.Contract

/-!
# HMAC-SHA-256 on PPC64LE: `init`

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 proof (`VG.Proof.Hmac.Common.Init`).
-/

namespace VG.Proof.Hmac.PPC64LE.Init


open VG VG.PPC64LE VG.Impl.Hmac.PPC64LE
open VG.Impl.Sha256.PPC64LE.Stream (mov save restore compressAt saved)
open VG.Proof.Hmac.Common (bytesAt_length)
open VG.Proof.Hmac.Common (bytesAt_snoc repr_block)
open VG.Proof.Sha256.Stream (writeBytes repr_congr)
open VG.Proof.Sha256.PPC64LE (writeState stateAt_writeState contains_offset sub_offset toNat_ofNat_lt)
open VG.Proof.Sha256.PPC64LE.Stream (Upd Mupd wp_mov wp_li wp_addi wp_subi wp_sub wp_add wp_lbz
  wp_stb compressAt_ok saveMem saveMem_saved saveMem_frame save_ok restore_ok frame_bytes untouched
  eval_zero eval_nonzero ofNat_beq_zero sub_ofNat ofNat_succ nvRegs nv_pres pushMem frame_sub)
open VG.Spec.Sha256 (bytesAt stateAt Repr H0)
open VG.Spec.Hmac (xorPad ipad opad blockKey sha256)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .r3
abbrev out : Addr := s₀.gpr .r4
abbrev kp : Addr := s₀.gpr .r5
abbrev kl : Nat := (s₀.gpr .r6).toNat
abbrev scr : Addr := s₀.gpr .r7
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

/-- The frame saving the link register, below the stack pointer. -/
abbrev stkR (s₀ : State) : Region := ⟨s₀.sp - 48, 48⟩

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (s₀ : State) : Prop where
  sp48 : 48 ≤ s₀.sp.toNat
  i : (stkR s₀).Disjoint (inR s₀)
  o : (stkR s₀).Disjoint (outR s₀)
  k : (stkR s₀).Disjoint (kR s₀)
  s : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Hmac.initSha256PPC64LE.pre s₀) : Pre s₀ ∧ Stack s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13⟩⟩

theorem K0_length (s₀ : State) (hp : Pre s₀) : (K0 s₀).length = 64 := by
  simp [K0, bytesAt_length]; have := hp.kl_le; omega

theorem blockKey_eq {s₀ : State} (hp : Pre s₀) :
    blockKey sha256 (bytesAt s₀.mem (kp s₀) (kl s₀)) = K0 s₀ := by
  have := hp.kl_le
  simp [blockKey, sha256, K0, bytesAt_length, show ¬ (64 < kl s₀) by omega]

/-! ## `H⁽⁰⁾` -/

open VG.Proof.Sha256.PPC64LE.Stream.WP (cons)

/-- The three instructions storing the 32-bit word `x` at `off(b)`. -/
def word (b : Reg) (x : BitVec 32) (off : Nat) : List Instr :=
  [.lis .r8 (x.extractLsb' 16 16), .ori .r8 .r8 (x.extractLsb' 0 16), .store .w .r8 b off]

theorem h0_eq (b : Reg) : h0 b = word b H0[0] 0 ++ word b H0[1] 4 ++ word b H0[2] 8 ++ word b H0[3] 12 ++
    word b H0[4] 16 ++ word b H0[5] 20 ++ word b H0[6] 24 ++ word b H0[7] 28 := rfl

theorem word_ok {b : Reg} (hb : b ≠ .r8) (hb0 : b ≠ .r0) {x : BitVec 32} {off : Nat} (ho : off < 2 ^ 15)
    {rest : List Instr} {s : State} {Q : State → Prop}
    (hout : InRegions s.wr (s.gpr b + BitVec.ofNat 64 off) 4)
    (k : ∀ s', (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = s.mem.writeW (s.gpr b + BitVec.ofNat 64 off) x → WP isa (.block rest) s' Q) :
    WP isa (.block (word b x off ++ rest)) s Q := by
  simp only [word, List.cons_append, List.nil_append]
  refine cons exec_lis (cons exec_ori (cons (exec_store_w hb0 ho ?_) (k _ ?_ rfl rfl rfl ?_)))
  · simpa [State.write, hb] using hout
  · intro r hr; simp [State.write, hr]
  · simp only [State.write, ite_true, hb, ite_false]
    congr 1
    exact lis_ori x

/-- `H⁽⁰⁾` stored at `b`. -/
theorem h0_ok {b : Reg} (hb : b ≠ .r8) (hb0 : b ≠ .r0) {s : State} {rest : List Instr} {Q : State → Prop}
    (o : ∀ k < 8, InRegions s.wr (s.gpr b + BitVec.ofNat 64 (4 * k)) 4)
    (k : ∀ s', (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeState s.mem (s.gpr b) H0 → WP isa (.block rest) s' Q) :
    WP isa (.block (h0 b ++ rest)) s Q := by
  rw [h0_eq]
  simp only [List.append_assoc]
  refine word_ok hb hb0 (by omega) (o 0 (by omega)) fun s1 g1 _ wr1 sp1 m1 => ?_
  have k1 : s1.gpr b = s.gpr b := g1 _ hb
  refine word_ok hb hb0 (by omega) (by rw [wr1, k1]; exact o 1 (by omega)) fun s2 g2 _ wr2 sp2 m2 => ?_
  have k2 : s2.gpr b = s.gpr b := by rw [g2 _ hb, k1]
  have w2 : s2.wr = s.wr := by rw [wr2, wr1]
  refine word_ok hb hb0 (by omega) (by rw [w2, k2]; exact o 2 (by omega)) fun s3 g3 _ wr3 sp3 m3 => ?_
  have k3 : s3.gpr b = s.gpr b := by rw [g3 _ hb, k2]
  have w3 : s3.wr = s.wr := by rw [wr3, w2]
  refine word_ok hb hb0 (by omega) (by rw [w3, k3]; exact o 3 (by omega)) fun s4 g4 _ wr4 sp4 m4 => ?_
  have k4 : s4.gpr b = s.gpr b := by rw [g4 _ hb, k3]
  have w4 : s4.wr = s.wr := by rw [wr4, w3]
  refine word_ok hb hb0 (by omega) (by rw [w4, k4]; exact o 4 (by omega)) fun s5 g5 _ wr5 sp5 m5 => ?_
  have k5 : s5.gpr b = s.gpr b := by rw [g5 _ hb, k4]
  have w5 : s5.wr = s.wr := by rw [wr5, w4]
  refine word_ok hb hb0 (by omega) (by rw [w5, k5]; exact o 5 (by omega)) fun s6 g6 _ wr6 sp6 m6 => ?_
  have k6 : s6.gpr b = s.gpr b := by rw [g6 _ hb, k5]
  have w6 : s6.wr = s.wr := by rw [wr6, w5]
  refine word_ok hb hb0 (by omega) (by rw [w6, k6]; exact o 6 (by omega)) fun s7 g7 _ wr7 sp7 m7 => ?_
  have k7 : s7.gpr b = s.gpr b := by rw [g7 _ hb, k6]
  have w7 : s7.wr = s.wr := by rw [wr7, w6]
  refine word_ok hb hb0 (by omega) (by rw [w7, k7]; exact o 7 (by omega)) fun s8 g8 rd8 wr8 sp8 m8 => ?_
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

/-- The registers while building the two buffers (`r31` = `j`). -/
structure Buf (s₀ : State) (j : Nat) (s : State) : Prop where
  j_le : j ≤ 64
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r26 : s.gpr .r26 = inn s₀
  r27 : s.gpr .r27 = scr s₀
  r28 : s.gpr .r28 = out s₀
  r31 : s.gpr .r31 = BitVec.ofNat 64 j
  r12 : s.gpr .r12 = BitVec.ofNat 64 0x36
  r0 : s.gpr .r0 = BitVec.ofNat 64 0x5c
  mem : BufMem s₀ j s.mem
  nv : ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r

/-- In the key loop: `r29` points at key byte `j`, and `r30` counts the key bytes left. -/
structure Key (s₀ : State) (j : Nat) (s : State) : Prop extends Buf s₀ j s where
  r29 : s.gpr .r29 = kp s₀ + BitVec.ofNat 64 j
  r30 : s.gpr .r30 = BitVec.ofNat 64 (kl s₀ - j)

/-- In the pad loop: `r10` counts the bytes left. -/
structure Pad (s₀ : State) (j : Nat) (s : State) : Prop extends Buf s₀ j s where
  r10 : s.gpr .r10 = BitVec.ofNat 64 (64 - j)

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
    WP isa (.block (save .r7 ++
      ([mov .r26 .r3, mov .r27 .r7, mov .r28 .r4, mov .r29 .r5, mov .r30 .r6] : List Instr) ++
      h0 .r26 ++ h0 .r28 ++ ([.li .r12 0x36, .li .r0 0x5c, .li .r31 0] : List Instr))) s₀
      (Key s₀ 0) := by
  simp only [List.append_assoc]
  refine save_ok (by decide) (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hp.wr], contains_offset hd₂ (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => ?_
  have h19 : s₆.gpr .r26 = inn s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, g₁]
  have h20 : s₆.gpr .r27 = scr s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁]
  have h21 : s₆.gpr .r28 = out s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  have h22 : s₆.gpr .r29 = kp s₀ := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  have h23 : s₆.gpr .r30 = s₀.gpr .r6 := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  have m₆ : s₆.mem = saveMem s₀.mem (scr s₀) s₀.gpr := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  have sp₆ : s₆.sp = s₀.sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  refine h0_ok (by decide) (by decide) (fun k hk => ⟨inR s₀, by simp [wr₆, hp.wr], by
    rw [h19]; exact contains_offset (by omega) (by omega)⟩) fun s₇ g₇ rd₇ wr₇ sp₇ m₇ => ?_
  refine h0_ok (by decide) (by decide) (fun k hk => ⟨outR s₀, by simp [wr₇, wr₆, hp.wr], by
    rw [g₇ _ (by decide), h21]; exact contains_offset (by omega) (by omega)⟩)
    fun s₈ g₈ rd₈ wr₈ sp₈ m₈ => ?_
  refine wp_li (by decide) fun s₉ u₉ => wp_li (by decide) fun s₁₀ u₁₀ => wp_li (by decide) fun s₁₁ u₁₁ => WP.block_nil ?_
  have k : ∀ r, r ≠ .r8 → r ≠ .r12 → r ≠ .r0 → r ≠ .r31 → s₁₁.gpr r = s₆.gpr r :=
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
    by rw [k _ (by decide) (by decide) (by decide) (by decide), h21], by rw [u₁₁.gpr],
    by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr],
    by rw [u₁₁.other _ (by decide), u₁₀.gpr],
    ⟨?_, ?_, by simp [bytesAt], by simp [bytesAt], ?_, ?_⟩, fun r hr => ?_⟩, ?_, ?_⟩
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
  · have ne : r ≠ .r8 ∧ r ≠ .r12 ∧ r ≠ .r0 ∧ r ≠ .r31 ∧ r ≠ .r26 ∧ r ≠ .r27 ∧ r ≠ .r28 ∧ r ≠ .r29 ∧
        r ≠ .r30 := by revert r hr; decide
    rw [k r ne.1 ne.2.1 ne.2.2.1 ne.2.2.2.1, u₆.other r ne.2.2.2.2.2.2.2.2, u₅.other r ne.2.2.2.2.2.2.2.1,
      u₄.other r ne.2.2.2.2.2.2.1, u₃.other r ne.2.2.2.2.2.1, u₂.other r ne.2.2.2.2.1, g₁]
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
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  cons exec_logic (k _ (Proof.Sha256.PPC64LE.Stream.Upd.write _ _ _))

theorem xor_byte (b : Byte) (v : Nat) :
    (b.setWidth 64 ^^^ BitVec.ofNat 64 v).setWidth 8 = b ^^^ BitVec.ofNat 8 v := by
  ext i hi
  simp [BitVec.getElem_xor]

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
  [.lbz .r8 .r29 0,
    .logic .xor .r9 .r8 .r12, .add .r11 .r26 .r31, .stb .r9 .r11 32,
    .logic .xor .r9 .r8 .r0, .add .r11 .r28 .r31, .stb .r9 .r11 32,
    .addi .r29 .r29 1, .addi .r31 .r31 1, .subi .r30 .r30 1]

theorem keyLoop_eq : keyLoop = .loop (.block keyBody) (.nonzero .d .r30) := rfl

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
  refine wp_lbz (a := kp s₀ + BitVec.ofNat 64 j) (by decide) (by omega) (by rw [h.r29]; simp) hin fun s₁ u₁ => ?_
  refine wp_eor fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  refine wp_stb (a := inn s₀ + 32 + BitVec.ofNat 64 j) (by decide) (by omega) ?_
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact buf_in hp h.wr (by omega) (.inl rfl)) fun s₄ u₄ => ?_
  · simp (config := {decide := true}) only [u₃.gpr, u₂.other, u₁.other, h.r26, h.r31]; bv_omega
  refine wp_eor fun s₅ u₅ => wp_add fun s₆ u₆ => ?_
  refine wp_stb (a := out s₀ + 32 + BitVec.ofNat 64 j) (by decide) (by omega) ?_
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact buf_in hp h.wr (by omega) (.inr rfl))
    fun s₇ u₇ => ?_
  · simp (config := {decide := true}) only [u₆.gpr, u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other,
      h.r28, h.r31]
    bv_omega
  refine wp_addi (by decide) (by omega) fun s₈ u₈ => wp_addi (by decide) (by omega) fun s₉ u₉ =>
    wp_subi (by decide) (by omega) fun s₁₀ u₁₀ => WP.block_nil ?_
  have k : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s₁₀.gpr r = s.gpr r :=
    fun r a b c d e f => by
      rw [u₁₀.other r e, u₉.other r f, u₈.other r d, u₇.gpr, u₆.other r c, u₅.other r b, u₄.gpr,
        u₃.other r c, u₂.other r b, u₁.other r a]
  have v₁ : (s₃.gpr .r9).setWidth 8 = (K0 s₀)[j] ^^^ ipad := by
    simp (config := {decide := true}) only [u₃.other, u₂.gpr, u₁.gpr, u₁.other, h.r12, xor_byte, hbyte]
    rfl
  have v₂ : (s₆.gpr .r9).setWidth 8 = (K0 s₀)[j] ^^^ opad := by
    simp (config := {decide := true}) only [u₆.other, u₅.gpr, u₄.gpr, u₃.other, u₂.other, u₁.gpr,
      u₁.other, h.r0, xor_byte, hbyte]
    rfl
  have hm : s₁₀.mem = (s.mem.writeW (inn s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j] ^^^ ipad)).writeW
      (out s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j] ^^^ opad) := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, v₂, u₆.mem, u₅.mem, u₄.mem, v₁, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨by omega, by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r26],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r27],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r28], ?_,
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r12],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r0],
    by rw [hm]; exact buf_write hp h.mem (by omega), fun r hr => by
      rw [k r (by revert r hr; decide) (by revert r hr; decide) (by revert r hr; decide)
        (by revert r hr; decide) (by revert r hr; decide) (by revert r hr; decide)]; exact h.nv r hr⟩,
    ?_, ?_⟩
  · simp (config := {decide := true}) only [u₁₀.other, u₉.gpr, u₈.other, u₇.gpr, u₆.other, u₅.other,
      u₄.gpr, u₃.other, u₂.other, u₁.other, h.r31]
    rw [BitVec.ofNat_add]
  · simp (config := {decide := true}) only [u₁₀.other, u₉.other, u₈.gpr, u₇.gpr, u₆.other, u₅.other,
      u₄.gpr, u₃.other, u₂.other, u₁.other, h.r29]
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  · simp (config := {decide := true}) only [u₁₀.gpr, u₉.other, u₈.other, u₇.gpr, u₆.other, u₅.other,
      u₄.gpr, u₃.other, u₂.other, u₁.other, h.r30]
    rw [show (BitVec.ofNat 64 1 : BitVec 64) = 1 from rfl, ← show kl s₀ - j - 1 = kl s₀ - (j + 1) by omega,
      ← sub_ofNat (a := kl s₀ - j) (b := 1) (by omega)]
    rfl

def padBody : List Instr :=
  [.add .r11 .r26 .r31, .stb .r12 .r11 32, .add .r11 .r28 .r31, .stb .r0 .r11 32,
    .addi .r31 .r31 1, .subi .r10 .r10 1]

theorem padLoop_eq : padLoop = .loop (.block padBody) (.nonzero .d .r10) := rfl

theorem ipad_byte : (BitVec.ofNat 64 0x36).setWidth 8 = (0 : Byte) ^^^ ipad := by decide
theorem opad_byte : (BitVec.ofNat 64 0x5c).setWidth 8 = (0 : Byte) ^^^ opad := by decide

theorem pad_step {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : kl s₀ ≤ j) (hj' : j < 64) {s : State}
    (h : Pad s₀ j s) : WP isa (.block padBody) s (Pad s₀ (j + 1)) := by
  have hl : j < (K0 s₀).length := by rw [K0_length s₀ hp]; omega
  unfold padBody
  refine wp_add fun s₁ u₁ => ?_
  refine wp_stb (a := inn s₀ + 32 + BitVec.ofNat 64 j) (by decide) (by omega) ?_
    (by rw [u₁.wr]; exact buf_in hp h.wr hj' (.inl rfl)) fun s₂ u₂ => ?_
  · rw [u₁.gpr, h.r26, h.r31]; bv_omega
  refine wp_add fun s₃ u₃ => ?_
  refine wp_stb (a := out s₀ + 32 + BitVec.ofNat 64 j) (by decide) (by omega) ?_
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact buf_in hp h.wr hj' (.inr rfl)) fun s₄ u₄ => ?_
  · simp (config := {decide := true}) only [u₃.gpr, u₂.gpr, u₁.other, h.r28, h.r31]; bv_omega
  refine wp_addi (by decide) (by omega) fun s₅ u₅ => wp_subi (by decide) (by omega) fun s₆ u₆ => WP.block_nil ?_
  have k : ∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .r31 → s₆.gpr r = s.gpr r := fun r a b c => by
    rw [u₆.other r a, u₅.other r c, u₄.gpr, u₃.other r b, u₂.gpr, u₁.other r b]
  have hm : s₆.mem = (s.mem.writeW (inn s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j] ^^^ ipad)).writeW
      (out s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j] ^^^ opad) := by
    simp (config := {decide := true}) only [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.other,
      u₂.gpr, u₁.other, h.r12, h.r0, K0_ge hj hl, ipad_byte, opad_byte]
  refine ⟨⟨by omega, by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    by rw [k _ (by decide) (by decide) (by decide), h.r26],
    by rw [k _ (by decide) (by decide) (by decide), h.r27],
    by rw [k _ (by decide) (by decide) (by decide), h.r28], ?_,
    by rw [k _ (by decide) (by decide) (by decide), h.r12],
    by rw [k _ (by decide) (by decide) (by decide), h.r0],
    by rw [hm]; exact buf_write hp h.mem hj', fun r hr => by
      rw [k r (by revert r hr; decide) (by revert r hr; decide) (by revert r hr; decide)]
      exact h.nv r hr⟩, ?_⟩
  · simp (config := {decide := true}) only [u₆.other, u₅.gpr, u₄.gpr, u₃.other, u₂.gpr, u₁.other, h.r31]
    rw [BitVec.ofNat_add]
  · simp (config := {decide := true}) only [u₆.gpr, u₅.other, u₄.gpr, u₃.other, u₂.gpr, u₁.other, h.r10]
    rw [show 64 - (j + 1) = 64 - j - 1 by omega, ← sub_ofNat (a := 64 - j) (b := 1) (by omega)]

theorem key_loop_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Key s₀ 0 s) (hk : 0 < kl s₀) :
    WP isa keyLoop s (Buf s₀ (kl s₀)) := by
  have := hp.kl_le
  rw [keyLoop_eq]
  refine WP.loop (M := isa) (fun n s => ∃ j, n = kl s₀ - j ∧ j < kl s₀ ∧ Key s₀ j s) ?_ (kl s₀) s
    ⟨0, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, hb⟩
  refine WP.mono (key_step hp hj hb) fun s' hb' => ?_
  have hz : isa.eval (.nonzero .d .r30) s' = some (decide (kl s₀ - (j + 1) ≠ 0)) := by
    show VG.PPC64LE.eval (.nonzero .d .r30) s' = _
    rw [eval_nonzero, hb'.r30, bne, ofNat_beq_zero (by omega)]
    simp
  by_cases hl : kl s₀ - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
    rw [show kl s₀ = j + 1 by omega]; exact hb'.toBuf
  · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega, j + 1, rfl, by omega, hb'⟩

theorem pad_loop_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Pad s₀ (kl s₀) s) (hk : kl s₀ < 64) :
    WP isa padLoop s (Buf s₀ 64) := by
  rw [padLoop_eq]
  refine WP.loop (M := isa) (fun n s => ∃ j, n = 64 - j ∧ kl s₀ ≤ j ∧ j < 64 ∧ Pad s₀ j s) ?_
    (64 - kl s₀) s ⟨kl s₀, rfl, le_rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, hj', hb⟩
  refine WP.mono (pad_step hp hj hj' hb) fun s' hb' => ?_
  have hz : isa.eval (.nonzero .d .r10) s' = some (decide (64 - (j + 1) ≠ 0)) := by
    show VG.PPC64LE.eval (.nonzero .d .r10) s' = _
    rw [eval_nonzero, hb'.r10, bne, ofNat_beq_zero (by omega)]
    simp
  by_cases hl : 64 - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
    rw [show (64 : Nat) = j + 1 by omega]; exact hb'.toBuf
  · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega, j + 1, rfl, by omega, by omega, hb'⟩

/-! ## The two compressions -/

/-- The inlined compression of the block in the buffer of the state at `p`
(the inner or the outer one). -/
theorem compress_ok {s₀ : State} (hp : Pre s₀) {p : Addr} (hpR : p = inn s₀ ∨ p = out s₀) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (h19 : s.gpr .r26 = p) (h20 : s.gpr .r27 = scr s₀)
    (h1 : s.gpr .r4 = p + 32) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
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
  (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧ (∀ r ∈ nvRegs, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
    Proof.Hmac.initSha256PPC64LE.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (h20 : s.gpr .r27 = scr s₀) (hsp : s.sp = s₀.sp) (hsv : Saved s₀ s.mem)
    (hnv : ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r)
    (hI : Repr s.mem (inn s₀) (xorPad (K0 s₀) ipad)) (hO : Repr s.mem (out s₀) (xorPad (K0 s₀) opad)) :
    WP isa (.block restore) s (Post s₀) := by
  refine restore_ok (scr := scr s₀) h20
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hrd, hwr, hp.wr], contains_offset hd₂ (by omega)⟩) s₀.gpr
    hsv fun s' hs ho hmem _ _ hsp' => ⟨hs, fun r hr => by
      rw [ho r (by revert r hr; decide)]; exact hnv r hr, by rw [hsp', hsp], ?_⟩
  simp only [Proof.Hmac.initSha256PPC64LE]
  rw [blockKey_eq hp, hmem]
  exact ⟨hI, hO⟩

/-- No instruction of `init` writes the callee-saved registers it does not save. -/
theorem untouched_ok : ∀ r ∈ untouched, ∀ i ∈ instrs initMain, dstOf i ≠ some r := by
  have : ((instrs initMain).all fun i => untouched.all fun r => dstOf i != some r) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr
  simpa using this

/-! ## Correctness -/

theorem buf_full {s₀ : State} (hp : Pre s₀) {m : Mem} (h : BufMem s₀ 64 m) :
    bytesAt m (inn s₀ + 32) 64 = xorPad (K0 s₀) ipad ∧ bytesAt m (out s₀ + 32) 64 = xorPad (K0 s₀) opad := by
  rw [h.bufI, h.bufO, List.take_of_length_le (by rw [K0_length s₀ hp])]
  exact ⟨rfl, rfl⟩

/-- `init` without its frame: the callee-saved registers are kept. -/
theorem correctMain {s₀ : State} (hp : Pre s₀) :
    WP isa initMain s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ Proof.Hmac.initSha256PPC64LE.post s₀ s' := by
  have hkl := hp.kl_le
  refine WP.mono (Proof.Sha256.PPC64LE.Stream.WP.gprs (Q := Post s₀) ?_ untouched_ok)
    fun s' ⟨⟨hsv, hnv, hsp, hpost⟩, hu⟩ => ⟨fun r hr => ?_, hsp, hpost⟩
  · unfold initMain
    refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
    -- The key.
    refine WP.seq (WP.mono (Q := Buf s₀ (kl s₀)) ?_ fun s₂ h₂ => ?_)
    · refine WP.ite (decide (kl s₀ = 0))
        (by show VG.PPC64LE.eval (.zero .d .r30) s₁ = _
            rw [eval_zero, h₁.r30, Nat.sub_zero, ofNat_beq_zero (by omega)])
        (fun hb => WP.block_nil ?_) (fun hb => key_loop_ok hp h₁ ?_)
      · simp only [decide_eq_true_eq] at hb; rw [hb]; exact h₁.toBuf
      · simp only [decide_eq_false_iff_not] at hb; omega
    -- The padding.
    refine WP.seq (wp_li (by decide) fun s₃ u₃ => wp_sub fun s₄ u₄ => WP.block_nil ?_)
    have hP : Pad s₀ (kl s₀) s₄ := by
      refine ⟨⟨h₂.j_le, by rw [u₄.rd, u₃.rd, h₂.rd], by rw [u₄.wr, u₃.wr, h₂.wr],
        by rw [u₄.sp, u₃.sp, h₂.sp], ?_, ?_, ?_, ?_, ?_, ?_, by rw [u₄.mem, u₃.mem]; exact h₂.mem,
        fun r hr => by
          rw [u₄.other r (by revert r hr; decide), u₃.other r (by revert r hr; decide)]
          exact h₂.nv r hr⟩, ?_⟩
      all_goals simp (config := {decide := true}) only [u₄.gpr, u₄.other, u₃.gpr, u₃.other, h₂.r26,
        h₂.r27, h₂.r28, h₂.r31, h₂.r12, h₂.r0]
      rw [← sub_ofNat hkl]
    refine WP.seq (WP.mono (Q := Buf s₀ 64) ?_ fun s₆ h₆ => ?_)
    · refine WP.ite (decide (64 - kl s₀ = 0))
        (by show VG.PPC64LE.eval (.zero .d .r10) s₄ = _
            rw [eval_zero, hP.r10, ofNat_beq_zero (by omega)])
        (fun hb => WP.block_nil ?_) (fun hb => pad_loop_ok hp hP ?_)
      · simp only [decide_eq_true_eq] at hb
        exact (show kl s₀ = 64 by omega) ▸ hP.toBuf
      · simp only [decide_eq_false_iff_not] at hb; omega
    obtain ⟨bI, bO⟩ := buf_full hp h₆.mem
    -- The inner block.
    refine WP.seq (wp_addi (by decide) (by omega) fun s₇ u₇ => WP.block_nil ?_)
    refine WP.seq (compress_ok hp (.inl rfl) (by rw [u₇.rd, h₆.rd]) (by rw [u₇.wr, h₆.wr])
      (by rw [u₇.other _ (by decide), h₆.r26]) (by rw [u₇.other _ (by decide), h₆.r27])
      (by rw [u₇.gpr, h₆.r26]; rfl) fun s₈ rd₈ wr₈ cs₈ sp₈ fr₈ st₈ => ?_)
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
    refine WP.seq (wp_mov fun s₉ u₉ => wp_addi (by decide) (by omega) fun s₁₀ u₁₀ => WP.block_nil ?_)
    have x21₈ : s₈.gpr .r28 = out s₀ := by
      rw [cs₈ _ (by decide), u₇.other _ (by decide), h₆.r28]
    have x20₈ : s₈.gpr .r27 = scr s₀ := by
      rw [cs₈ _ (by decide), u₇.other _ (by decide), h₆.r27]
    have m₁₀ : s₁₀.mem = s₈.mem := by rw [u₁₀.mem, u₉.mem]
    have nv₁₀ : ∀ r ∈ nvRegs, s₁₀.gpr r = s₀.gpr r := fun r hr => by
      rw [u₁₀.other r (by revert r hr; decide), u₉.other r (by revert r hr; decide),
        cs₈ r (nv_pres r hr), u₇.other r (by revert r hr; decide)]
      exact h₆.nv r hr
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
      (by rw [cs₁₁ _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), x20₈])
      (by rw [sp₁₁, u₁₀.sp, u₉.sp, sp₈, u₇.sp, h₆.sp]) ?_
      (fun r hr => by rw [cs₁₁ r (nv_pres r hr)]; exact nv₁₀ r hr) hI hO
    refine saved_frame (by rw [m₁₀]; exact sv₈) fr₁₁ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact (hp.o_s.symm.sub_left (save_sub s₀)).sub_right (sub32 _)
    · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
  · have key : ∀ r ∈ preserved, r ∈ untouched ∨ r ∈ nvRegs ∨ r ∈ saved.map Prod.fst := by decide
    rcases key r hr with hr' | hr' | hr'
    · exact hu r hr'
    · exact hnv r hr'
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr'
      exact hsv p hp'

/-- The state `initMain` starts in: the link register moved to `r0`, then
pushed in a frame. -/
abbrev inner (s₀ : State) : State := framed .r0 (s₀.write .r0 s₀.lr)

theorem correct {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Hmac.initSha256PPC64LE.post s₀ s' := by
  have hpi : Pre (inner s₀) :=
    ⟨hp.kl_le, hp.rd, hp.wr, hp.i_o, hp.i_s, hp.o_s, hp.k_i, hp.k_o, hp.k_s⟩
  refine WP.seq (cons exec_mflr (WP.block_nil (WP.seq ?_)))
  refine WP.frameReg (by exact hs.sp48) (fun R hR => ?_) (WP.mono (correctMain hpi)
    fun s' ⟨hk, hsp, hpost⟩ => ?_)
  · rw [show (s₀.write .r0 s₀.lr).wr = s₀.wr from rfl, hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact hs.i.sub_left (frame_sub _)
    · exact hs.o.sub_left (frame_sub _)
    · exact hs.s.sub_left (frame_sub _)
  · refine cons exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, ?_⟩)
    · have h0 : r ≠ .r0 := by revert r hr; decide
      simp only [State.write, h0, ite_false]
      rw [hk r hr]
      simp only [framed, State.write, h0, ite_false]
    · simp [State.write]
    · have e : bytesAt (inner s₀).mem (s₀.gpr .r5) (s₀.gpr .r6).toNat =
          bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat :=
        Proof.Sha256.Stream.bytesAt_congr fun i hi =>
          Proof.Sha256.PPC64LE.Stream.write_frame_bytes (R := kR s₀) hs.k (s₀.gpr .r6).isLt hi
      change Repr s'.mem (s₀.gpr .r3) (xorPad (blockKey sha256
          (bytesAt (inner s₀).mem (s₀.gpr .r5) (s₀.gpr .r6).toNat)) ipad) ∧
        Repr s'.mem (s₀.gpr .r4) (xorPad (blockKey sha256
          (bytesAt (inner s₀).mem (s₀.gpr .r5) (s₀.gpr .r6).toNat)) opad) at hpost
      rw [e] at hpost
      exact hpost

/-! ## `Verified` -/

/-- The initial taint: only the arguments are public. -/
theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Hmac.initSha256PPC64LE.pub s₁ s₂) :
    VG.PPC64LE.Taint.Agree (VG.PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition (with an empty key). -/
def sat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x2000, 96⟩, ⟨0x4000, 160⟩]

theorem init_verified : Verified PPC64LE.target init Proof.Hmac.initSha256PPC64LE := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs).1 (pre_of hs).2
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) (fun _ _ _ _ hp => agree₀ hp)
      (by taint_decide)
  · refine ⟨sat, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, by decide, ?_, ?_, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, sat] at h₁ h₂
      bv_omega

end VG.Proof.Hmac.PPC64LE.Init
