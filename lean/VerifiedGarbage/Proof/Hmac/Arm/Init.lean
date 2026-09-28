import VerifiedGarbage.Proof.Hmac.Arm.Common
import VerifiedGarbage.Proof.Hmac.X86_64.Init
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Init
import VerifiedGarbage.Proof.Hmac.Arm.Contract

/-!
# HMAC-SHA-256 on ARMv7: `init`

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 and AArch64 proofs (`VG.Proof.Hmac.X86_64.Init`,
`VG.Proof.Hmac.AArch64.Init`), with `inner` in `r0`, `outer` in `r4`, the key
pointer in `r5`, the bytes left in `r6`, the byte index in `r7` and `ipad`,
`opad` in `r8`, `r9`.
-/

namespace VG.Proof.Hmac.Arm.Init

open VG VG.Arm VG.Impl.Hmac.Arm
open VG.Impl.Sha256.Arm.Stream (save restore compressAt saved)
open VG.Proof.Hmac.Arm (add_off)
open VG.Proof.Hmac.X86_64 (bytesAt_length)
open VG.Proof.Hmac.X86_64.Init (bytesAt_snoc repr_block)
open VG.Proof.Sha256.Stream (writeBytes repr_congr)
open VG.Proof.Sha256.AArch64 (writeState stateAt_writeState)
open VG.Proof.Sha256.Arm (contains_offset)
open VG.Proof.Sha256.Arm.Stream (Upd Mupd Fupd wp_mov wp_add wp_subs wp_cmp wp_ldrb wp_strb wp_ldrSp
  wp_str op2_imm op2_reg compressAt_ok saveMem saveMem_saved saveMem_frame save_ok restore_ok frame_bytes
  sub_offset eval_eq eval_ne ofNat_beq_zero sub_ofNat sub_beq)
open VG.Proof.Sha256.Arm.Stream.Update (addr_toNat)
open VG.Spec.Sha256 (bytesAt stateAt Repr H0)
open VG.Spec.Hmac (xorPad ipad opad blockKey sha256)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev inn : BitVec 32 := s₀.gpr .r0
abbrev ou : BitVec 32 := s₀.gpr .r1
abbrev kp : BitVec 32 := s₀.gpr .r2
abbrev kl : Nat := (s₀.gpr .r3).toNat
abbrev scr : BitVec 32 := stackArg s₀ 0
abbrev inA : Addr := State.addr (inn s₀)
abbrev ouA : Addr := State.addr (ou s₀)
abbrev kA : Addr := State.addr (kp s₀)
abbrev scA : Addr := State.addr (scr s₀)
abbrev inR : Region := ⟨inA s₀, 96⟩
abbrev ouR : Region := ⟨ouA s₀, 96⟩
abbrev kR : Region := ⟨kA s₀, kl s₀⟩
abbrev scR : Region := ⟨scA s₀, 160⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩

/-- The key, padded with zeros to a block. -/
def K0 : List Byte := bytesAt s₀.mem (kA s₀) (kl s₀) ++ List.replicate (64 - kl s₀) 0

/-- The caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

end

structure Pre (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ 64
  rd : s₀.rd = [kR s₀, argR s₀]
  wr : s₀.wr = [inR s₀, ouR s₀, scR s₀]
  i_o : (inR s₀).Disjoint (ouR s₀)
  i_s : (inR s₀).Disjoint (scR s₀)
  o_s : (ouR s₀).Disjoint (scR s₀)
  k_i : (kR s₀).Disjoint (inR s₀)
  k_o : (kR s₀).Disjoint (ouR s₀)
  k_s : (kR s₀).Disjoint (scR s₀)
  a_i : (argR s₀).Disjoint (inR s₀)
  a_o : (argR s₀).Disjoint (ouR s₀)
  a_s : (argR s₀).Disjoint (scR s₀)
  in_fit : (inn s₀).toNat + 96 ≤ 2 ^ 32
  ou_fit : (ou s₀).toNat + 96 ≤ 2 ^ 32
  k_fit : (kp s₀).toNat + kl s₀ ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 160 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 4 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : Proof.Hmac.initSha256Arm.pre s₀) : Pre s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem K0_length (s₀ : State) (hp : Pre s₀) : (K0 s₀).length = 64 := by
  simp [K0, bytesAt_length]; have := hp.kl_le; omega

theorem blockKey_eq {s₀ : State} (hp : Pre s₀) :
    blockKey sha256 (bytesAt s₀.mem (kA s₀) (kl s₀)) = K0 s₀ := by
  have := hp.kl_le
  simp [blockKey, sha256, K0, bytesAt_length, show ¬ (64 < kl s₀) by omega]

theorem arg_in {s₀ : State} (hp : Pre s₀) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 4 :=
  ⟨argR s₀, by simp [hp.rd], Region.contains_self _ _⟩

/-! ## `H⁽⁰⁾` -/

open VG.Proof.Sha256.Arm.Stream.WP (cons)

/-- The three instructions storing the 32-bit word `x` at `[b + off]`. -/
def word (b : Reg) (x : BitVec 32) (off : Nat) : List Instr :=
  [.movw .r12 (x.extractLsb' 0 16), .movt .r12 (x.extractLsb' 16 16), .str .r12 b off]

theorem h0_eq (b : Reg) : h0 b = word b H0[0] 0 ++ word b H0[1] 4 ++ word b H0[2] 8 ++ word b H0[3] 12 ++
    word b H0[4] 16 ++ word b H0[5] 20 ++ word b H0[6] 24 ++ word b H0[7] 28 := rfl

theorem word_ok {b : Reg} (hb : b ≠ .r12) {x : BitVec 32} {off : Nat} (ho : off < 4096)
    {rest : List Instr} {s : State} {Q : State → Prop} (hfit : (s.gpr b).toNat + off < 2 ^ 32)
    (hout : InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 off) 4)
    (k : ∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = s.mem.writeW (State.addr (s.gpr b) + BitVec.ofNat 64 off) x → WP isa (.block rest) s' Q) :
    WP isa (.block (word b x off ++ rest)) s Q := by
  simp only [word, List.cons_append, List.nil_append]
  refine cons rfl (cons rfl ?_)
  refine wp_str ho (by simp only [State.setReg, hb, ite_false]; exact addr_add hfit) hout fun s' u => ?_
  refine k s' (fun r hr => by rw [u.gpr]; simp [State.setReg, hr]) u.rd u.wr u.sp ?_
  rw [u.mem]
  simp only [State.setReg, ite_true, movw_movt]

/-- `H⁽⁰⁾` stored at `b`. -/
theorem h0_ok {b : Reg} (hb : b ≠ .r12) {s : State} {rest : List Instr} {Q : State → Prop}
    (hfit : (s.gpr b).toNat + 32 ≤ 2 ^ 32)
    (o : ∀ k < 8, InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 (4 * k)) 4)
    (k : ∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeState s.mem (State.addr (s.gpr b)) H0 → WP isa (.block rest) s' Q) :
    WP isa (.block (h0 b ++ rest)) s Q := by
  rw [h0_eq]
  simp only [List.append_assoc]
  refine word_ok hb (by decide) (by omega) (o 0 (by omega)) fun s1 g1 _ wr1 sp1 m1 => ?_
  have k1 : s1.gpr b = s.gpr b := g1 _ hb
  refine word_ok hb (by decide) (by rw [k1]; omega) (by rw [wr1, k1]; exact o 1 (by omega))
    fun s2 g2 _ wr2 sp2 m2 => ?_
  have k2 : s2.gpr b = s.gpr b := by rw [g2 _ hb, k1]
  have w2 : s2.wr = s.wr := by rw [wr2, wr1]
  refine word_ok hb (by decide) (by rw [k2]; omega) (by rw [w2, k2]; exact o 2 (by omega))
    fun s3 g3 _ wr3 sp3 m3 => ?_
  have k3 : s3.gpr b = s.gpr b := by rw [g3 _ hb, k2]
  have w3 : s3.wr = s.wr := by rw [wr3, w2]
  refine word_ok hb (by decide) (by rw [k3]; omega) (by rw [w3, k3]; exact o 3 (by omega))
    fun s4 g4 _ wr4 sp4 m4 => ?_
  have k4 : s4.gpr b = s.gpr b := by rw [g4 _ hb, k3]
  have w4 : s4.wr = s.wr := by rw [wr4, w3]
  refine word_ok hb (by decide) (by rw [k4]; omega) (by rw [w4, k4]; exact o 4 (by omega))
    fun s5 g5 _ wr5 sp5 m5 => ?_
  have k5 : s5.gpr b = s.gpr b := by rw [g5 _ hb, k4]
  have w5 : s5.wr = s.wr := by rw [wr5, w4]
  refine word_ok hb (by decide) (by rw [k5]; omega) (by rw [w5, k5]; exact o 5 (by omega))
    fun s6 g6 _ wr6 sp6 m6 => ?_
  have k6 : s6.gpr b = s.gpr b := by rw [g6 _ hb, k5]
  have w6 : s6.wr = s.wr := by rw [wr6, w5]
  refine word_ok hb (by decide) (by rw [k6]; omega) (by rw [w6, k6]; exact o 6 (by omega))
    fun s7 g7 _ wr7 sp7 m7 => ?_
  have k7 : s7.gpr b = s.gpr b := by rw [g7 _ hb, k6]
  have w7 : s7.wr = s.wr := by rw [wr7, w6]
  refine word_ok hb (by decide) (by rw [k7]; omega) (by rw [w7, k7]; exact o 7 (by omega))
    fun s8 g8 rd8 wr8 sp8 m8 => ?_
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
  stI : stateAt m (inA s₀) = H0
  stO : stateAt m (ouA s₀) = H0
  bufI : bytesAt m (inA s₀ + 32) j = ((K0 s₀).take j).map (· ^^^ ipad)
  bufO : bytesAt m (ouA s₀ + 32) j = ((K0 s₀).take j).map (· ^^^ opad)
  saved : Saved s₀ m
  frame : Frame [inR s₀, ouR s₀, scR s₀] s₀.mem m

/-- The registers while building the two buffers (`r7` = `j`). -/
structure Buf (s₀ : State) (j : Nat) (s : State) : Prop where
  j_le : j ≤ 64
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r0 : s.gpr .r0 = inn s₀
  r4 : s.gpr .r4 = ou s₀
  r7 : s.gpr .r7 = BitVec.ofNat 32 j
  r8 : s.gpr .r8 = 0x36
  r9 : s.gpr .r9 = 0x5c
  mem : BufMem s₀ j s.mem

/-- In the key loop: `r5` points at key byte `j`, and `r6` counts the key bytes left. -/
structure Key (s₀ : State) (j : Nat) (s : State) : Prop extends Buf s₀ j s where
  r5 : s.gpr .r5 = kp s₀ + BitVec.ofNat 32 j
  r6 : s.gpr .r6 = BitVec.ofNat 32 (kl s₀ - j)

/-- In the pad loop: `r6` counts the bytes left. -/
structure Pad (s₀ : State) (j : Nat) (s : State) : Prop extends Buf s₀ j s where
  r6 : s.gpr .r6 = BitVec.ofNat 32 (64 - j)

theorem sub32 (p : Addr) : Region.Sub ⟨p, 32⟩ ⟨p, 96⟩ := Region.sub_prefix (by omega)

theorem save_sub (s₀ : State) : Region.Sub ⟨scA s₀ + BitVec.ofNat 64 112, 36⟩ (scR s₀) :=
  sub_offset (by omega) (by omega)

/-- `Saved` survives a write outside the save area `scratch[112..148)`. -/
theorem saved_frame {s₀ : State} {m m' : Mem} (h : Saved s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨scA s₀ + BitVec.ofNat 64 112, 36⟩ r) : Saved s₀ m' := by
  intro p hp'
  rw [← h p hp']
  refine hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  refine (hd r hr).sub_left ?_
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · intro a ha; simp only [Region.Contains] at *; bv_omega

/-- `Saved` survives a write outside the scratch space. -/
theorem saved_frame' {s₀ : State} {m m' : Mem} (h : Saved s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (scR s₀).Disjoint r) : Saved s₀ m' :=
  saved_frame h hf fun r hr => (hd r hr).sub_left (save_sub s₀)

theorem beq_zero_toNat (x : BitVec 32) : (x - 0 == 0) = decide (x.toNat = 0) := by
  rw [show x - 0 = x by simp]
  by_cases h : x.toNat = 0
  · simp [BitVec.eq_of_toNat_eq (show x.toNat = (0 : BitVec 32).toNat from h)]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'; exact h (by rw [h']; rfl)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block ([.ldrSp .r12 0] ++ save .r12 ++ [.mov .r4 (.reg .r1), .mov .r5 (.reg .r2),
      .mov .r6 (.reg .r3)] ++ h0 .r0 ++ h0 .r4 ++
      [.mov .r8 (.imm 0x36), .mov .r9 (.imm 0x5c), .mov .r7 (.imm 0), .cmp .r6 (.imm 0)])) s₀
      (fun s => Key s₀ 0 s ∧ s.z = decide (kl s₀ = 0)) := by
  have hsc := hp.scr_fit; have hin := hp.in_fit; have hou := hp.ou_fit
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl (arg_in hp) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine save_ok (b := .r12) (by rw [h12]; omega) (fun d hd₁ hd₂ => ⟨scR s₀, by simp [u₁.wr, hp.wr],
    by rw [h12]; exact contains_offset (by omega) (by omega)⟩) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_mov (op2_reg _ _) fun s₅ u₅ => ?_
  have k₅ : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s₅.gpr r = s₀.gpr r := fun r a b c d => by
    rw [u₅.other r c, u₄.other r b, u₃.other r a, g₂, u₁.other r d]
  have h0₅ : s₅.gpr .r0 = inn s₀ := k₅ _ (by decide) (by decide) (by decide) (by decide)
  have h4₅ : s₅.gpr .r4 = ou s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide)]
  have h5₅ : s₅.gpr .r5 = kp s₀ := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  have h6₅ : s₅.gpr .r6 = s₀.gpr .r3 := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  have m₅ : s₅.mem = saveMem s₀.mem (scA s₀) s₁.gpr saved := by
    rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem, h12]
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  have sp₅ : s₅.sp = s₀.sp := by rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  refine h0_ok (b := .r0) (by decide) (by rw [h0₅]; omega) (fun k hk => ⟨inR s₀, by simp [wr₅, hp.wr], by
    rw [h0₅]; exact contains_offset (by omega) (by omega)⟩) fun s₆ g₆ rd₆ wr₆ sp₆ m₆ => ?_
  have h4₆ : s₆.gpr .r4 = ou s₀ := by rw [g₆ _ (by decide), h4₅]
  refine h0_ok (b := .r4) (by decide) (by rw [h4₆]; omega) (fun k hk => ⟨ouR s₀, by simp [wr₆, wr₅, hp.wr], by
    rw [h4₆]; exact contains_offset (by omega) (by omega)⟩) fun s₇ g₇ rd₇ wr₇ sp₇ m₇ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₈ u₈ => wp_mov (op2_imm (by decide)) fun s₉ u₉ =>
    wp_mov (op2_imm (by decide)) fun s₁₀ u₁₀ => wp_cmp (op2_imm (by decide)) fun s₁₁ f₁₁ z₁₁ =>
    WP.block_nil ?_
  have k : ∀ r, r ≠ .r12 → r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → s₁₁.gpr r = s₅.gpr r := fun r a b c d => by
    rw [f₁₁.gpr, u₁₀.other r b, u₉.other r d, u₈.other r c, g₇ r a, g₆ r a]
  rw [h0₅] at m₆
  rw [h4₆] at m₇
  have hm : s₁₁.mem = writeState (writeState (saveMem s₀.mem (scA s₀) s₁.gpr saved) (inA s₀) H0) (ouA s₀) H0 := by
    rw [f₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, m₇, m₆, m₅]
  have fS : Frame [scR s₀] s₀.mem (saveMem s₀.mem (scA s₀) s₁.gpr saved) :=
    saveMem_frame s₀.mem (scA s₀) s₁.gpr saved fun p hp' =>
      (VG.Proof.Sha256.Arm.Stream.saved_bound p hp').1
  have fI := writeState_frame (saveMem s₀.mem (scA s₀) s₁.gpr saved) (inA s₀) H0
  have fO := writeState_frame (writeState (saveMem s₀.mem (scA s₀) s₁.gpr saved) (inA s₀) H0) (ouA s₀) H0
  have ds : ∀ p : Addr, ∀ r : Region, r.Disjoint ⟨p, 96⟩ → r.Disjoint ⟨p, 32⟩ :=
    fun p r h => h.sub_right (sub32 p)
  refine ⟨⟨⟨by omega, by rw [f₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, rd₇, rd₆, rd₅],
    by rw [f₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇, wr₆, wr₅], by rw [f₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, sp₇, sp₆, sp₅],
    by rw [k _ (by decide) (by decide) (by decide) (by decide), h0₅],
    by rw [k _ (by decide) (by decide) (by decide) (by decide), h4₅],
    by rw [f₁₁.gpr, u₁₀.gpr]; rfl,
    by rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr],
    by rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr],
    ⟨?_, ?_, by simp [bytesAt], by simp [bytesAt], ?_, ?_⟩⟩, ?_, ?_⟩, ?_⟩
  · rw [hm]
    refine (Proof.Sha256.Stream.stateAt_congr fun i hi => ?_).trans
      (stateAt_writeState (saveMem s₀.mem (scA s₀) s₁.gpr saved) _ _)
    exact frame_bytes fO (R := ⟨inA s₀, 32⟩) (by simpa using ds _ _ (hp.i_o.sub_left (sub32 _))) (by simp) hi
  · rw [hm, stateAt_writeState]
  · rw [hm]
    refine saved_frame' (saved_frame' (fun p hp' => ?_) fI ?_) fO ?_
    · rw [saveMem_saved _ _ _ p hp', u₁.other]
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    all_goals simp only [List.mem_singleton]; rintro r rfl
    · exact ds _ _ hp.i_s.symm
    · exact ds _ _ hp.o_s.symm
  · rw [hm]
    refine ((fS.mono ?_).trans (fI.sub ?_)).trans (fO.sub ?_)
    · simp
    · simp only [List.mem_singleton]; rintro r rfl; exact ⟨inR s₀, by simp, sub32 _⟩
    · simp only [List.mem_singleton]; rintro r rfl; exact ⟨ouR s₀, by simp, sub32 _⟩
  · rw [k _ (by decide) (by decide) (by decide) (by decide), h5₅]; simp
  · rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      g₇ _ (by decide), g₆ _ (by decide), h6₅]; simp
  · rw [z₁₁, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      g₇ _ (by decide), g₆ _ (by decide), h6₅, beq_zero_toNat]

/-- A byte written right after `j` bytes of a buffer, in both buffers. -/
theorem buf_write {s₀ : State} (hp : Pre s₀) {j : Nat} {m : Mem} (h : BufMem s₀ j m) (hj : j < 64) :
    BufMem s₀ (j + 1) ((m.writeW (inA s₀ + 32 + BitVec.ofNat 64 j)
      ((K0 s₀)[j]'(by rw [K0_length s₀ hp]; omega) ^^^ ipad)).writeW
      (ouA s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j]'(by rw [K0_length s₀ hp]; omega) ^^^ opad)) := by
  have hl : j < (K0 s₀).length := by rw [K0_length s₀ hp]; omega
  set x := (K0 s₀)[j] ^^^ ipad
  set y := (K0 s₀)[j] ^^^ opad
  let bI : Region := ⟨inA s₀ + 32, 64⟩
  let bO : Region := ⟨ouA s₀ + 32, 64⟩
  have sI : Region.Sub bI (inR s₀) := sub_offset (off := 32) (by omega) (by omega)
  have sO : Region.Sub bO (ouR s₀) := sub_offset (off := 32) (by omega) (by omega)
  have f₁ : Frame [bI] m (m.writeW (inA s₀ + 32 + BitVec.ofNat 64 j) x) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) x (contains_offset (by omega) (by omega))
  have f₂ : Frame [bO] (m.writeW (inA s₀ + 32 + BitVec.ofNat 64 j) x)
      ((m.writeW (inA s₀ + 32 + BitVec.ofNat 64 j) x).writeW (ouA s₀ + 32 + BitVec.ofNat 64 j) y) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) y (contains_offset (by omega) (by omega))
  have F := (f₁.mono (rs' := [bI, bO]) (by simp)).trans (f₂.mono (by simp))
  have dIO : bI.Disjoint bO := (hp.i_o.sub_left sI).sub_right sO
  have st : ∀ p : Addr, (∀ r ∈ [bI, bO], Region.Disjoint ⟨p, 32⟩ r) →
      stateAt ((m.writeW (inA s₀ + 32 + BitVec.ofNat 64 j) x).writeW (ouA s₀ + 32 + BitVec.ofNat 64 j) y) p =
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
        (fun i hi => frame_bytes f₂ (R := ⟨inA s₀ + 32, j + 1⟩) ?_ (by simp; omega) hi),
      bytesAt_snoc _ _ (by omega), h.bufI, List.take_succ_eq_append_getElem hl, List.map_append]
    · rfl
    · simp only [List.mem_singleton]; rintro r rfl
      exact dIO.sub_left (Region.sub_prefix (by omega))
  · rw [bytesAt_snoc _ _ (by omega),
      Proof.Sha256.Stream.bytesAt_congr
        (fun i hi => frame_bytes f₁ (R := ⟨ouA s₀ + 32, j⟩) ?_ (by simp; omega) hi),
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
    · exact ⟨ouR s₀, by simp, sO⟩

/-! ## The key and pad loops -/

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2} {y : BitVec 32}
    (ho : o.eval s = some y) (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem xor_byte (b : Byte) (v : BitVec 32) :
    (b.setWidth 32 ^^^ v).setWidth 8 = b ^^^ v.setWidth 8 := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

theorem K0_lt {s₀ : State} {j : Nat} (hj : j < kl s₀) (h : j < (K0 s₀).length) :
    (K0 s₀)[j] = s₀.mem (kA s₀ + BitVec.ofNat 64 j) := by
  simp only [K0]
  rw [List.getElem_append_left (by rw [bytesAt_length]; exact hj)]
  simp [bytesAt]

theorem K0_ge {s₀ : State} {j : Nat} (hj : kl s₀ ≤ j) (h : j < (K0 s₀).length) : (K0 s₀)[j] = 0 := by
  simp only [K0]
  rw [List.getElem_append_right (by rw [bytesAt_length]; exact hj)]
  simp

/-- Byte `j` of a state's buffer, addressed as `[p + j, #32]`. -/
theorem buf_addr {p : BitVec 32} (hp : p.toNat + 96 ≤ 2 ^ 32) {j : Nat} (hj : j < 64) :
    State.addr (p + BitVec.ofNat 32 j + BitVec.ofNat 32 32) = State.addr p + 32 + BitVec.ofNat 64 j := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by omega), Nat.add_comm, BitVec.ofNat_add,
    ← BitVec.add_assoc]
  rfl

theorem buf_in {s₀ : State} (hp : Pre s₀) {s : State} (hwr : s.wr = s₀.wr) {j : Nat} (hj : j < 64)
    {p : Addr} (hpR : p = inA s₀ ∨ p = ouA s₀) : InRegions s.wr (p + 32 + BitVec.ofNat 64 j) 1 := by
  refine ⟨⟨p, 96⟩, by rcases hpR with rfl | rfl <;> simp [hwr, hp.wr], ?_⟩
  rw [BitVec.add_assoc, show (32 : Addr) + BitVec.ofNat 64 j = BitVec.ofNat 64 (32 + j) by
    rw [BitVec.ofNat_add]; rfl]
  exact contains_offset (by omega) (by omega)

theorem ofNat_succ (j : Nat) : BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) := by
  rw [BitVec.ofNat_add]; rfl

def keyBody : List Instr :=
  [.ldrb .r12 .r5 0,
    .dp .eor .r1 .r12 (.reg .r8), .dp .add .r2 .r0 (.reg .r7), .strb .r1 .r2 32,
    .dp .eor .r1 .r12 (.reg .r9), .dp .add .r2 .r4 (.reg .r7), .strb .r1 .r2 32,
    .dp .add .r5 .r5 (.imm 1), .dp .add .r7 .r7 (.imm 1), .subs .r6 .r6 (.imm 1)]

theorem keyLoop_eq : keyLoop = .loop (.block keyBody) .ne := rfl

theorem key_step {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : j < kl s₀) {s : State} (h : Key s₀ j s) :
    WP isa (.block keyBody) s fun s' => Key s₀ (j + 1) s' ∧ s'.z = decide (kl s₀ - (j + 1) = 0) := by
  have hkl := hp.kl_le; have hkf := hp.k_fit; have hin := hp.in_fit; have hou := hp.ou_fit
  have hl : j < (K0 s₀).length := by rw [K0_length s₀ hp]; omega
  have hinr : InRegions (s.rd ++ s.wr) (kA s₀ + BitVec.ofNat 64 j) 1 :=
    ⟨kR s₀, by simp [h.rd, hp.rd], contains_offset (by omega) (by omega)⟩
  have hbyte : s.mem (kA s₀ + BitVec.ofNat 64 j) = (K0 s₀)[j] := by
    rw [K0_lt hj hl]
    refine frame_bytes h.mem.frame (R := kR s₀) ?_ (by show kl s₀ ≤ 2 ^ 64; omega) hj
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.k_i
    · exact hp.k_o
    · exact hp.k_s
  unfold keyBody
  refine wp_ldrb (a := kA s₀ + BitVec.ofNat 64 j) (by omega)
    (by rw [h.r5, BitVec.add_zero, addr_add (by omega)]) hinr
    fun s₁ u₁ => ?_
  refine wp_eor (op2_reg _ _) fun s₂ u₂ => wp_add (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_strb (a := inA s₀ + 32 + BitVec.ofNat 64 j) (by omega) ?_
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact buf_in hp h.wr (by omega) (.inl rfl)) fun s₄ u₄ => ?_
  · simp (config := {decide := true}) only [u₃.gpr, u₂.other, u₁.other, h.r0, h.r7]
    exact buf_addr hin (by omega)
  refine wp_eor (op2_reg _ _) fun s₅ u₅ => wp_add (op2_reg _ _) fun s₆ u₆ => ?_
  refine wp_strb (a := ouA s₀ + 32 + BitVec.ofNat 64 j) (by omega) ?_
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact buf_in hp h.wr (by omega) (.inr rfl))
    fun s₇ u₇ => ?_
  · simp (config := {decide := true}) only [u₆.gpr, u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other,
      h.r4, h.r7]
    exact buf_addr hou (by omega)
  refine wp_add (op2_imm (by decide)) fun s₈ u₈ => wp_add (op2_imm (by decide)) fun s₉ u₉ =>
    wp_subs (op2_imm (by decide)) fun s₁₀ u₁₀ z₁₀ => WP.block_nil ?_
  have k : ∀ r, r ≠ .r12 → r ≠ .r1 → r ≠ .r2 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₁₀.gpr r = s.gpr r :=
    fun r a b c d e f => by
      rw [u₁₀.other r e, u₉.other r f, u₈.other r d, u₇.gpr, u₆.other r c, u₅.other r b, u₄.gpr,
        u₃.other r c, u₂.other r b, u₁.other r a]
  have v₁ : (s₃.gpr .r1).setWidth 8 = (K0 s₀)[j] ^^^ ipad := by
    simp (config := {decide := true}) only [u₃.other, u₂.gpr, u₁.gpr, u₁.other, h.r8, xor_byte, hbyte]
    rfl
  have v₂ : (s₆.gpr .r1).setWidth 8 = (K0 s₀)[j] ^^^ opad := by
    simp (config := {decide := true}) only [u₆.other, u₅.gpr, u₄.gpr, u₃.other, u₂.other, u₁.gpr,
      u₁.other, h.r9, xor_byte, hbyte]
    rfl
  have hm : s₁₀.mem = (s.mem.writeW (inA s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j] ^^^ ipad)).writeW
      (ouA s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j] ^^^ opad) := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, v₂, u₆.mem, u₅.mem, u₄.mem, v₁, u₃.mem, u₂.mem, u₁.mem]
  have r6 : s₉.gpr .r6 = BitVec.ofNat 32 (kl s₀ - j) := by
    simp (config := {decide := true}) only [u₉.other, u₈.other, u₇.gpr, u₆.other, u₅.other,
      u₄.gpr, u₃.other, u₂.other, u₁.other, h.r6]
  refine ⟨⟨⟨by omega, by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r0],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r4], ?_,
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r8],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r9],
    by rw [hm]; exact buf_write hp h.mem (by omega)⟩, ?_, ?_⟩, ?_⟩
  · simp (config := {decide := true}) only [u₁₀.other, u₉.gpr, u₈.other, u₇.gpr, u₆.other, u₅.other,
      u₄.gpr, u₃.other, u₂.other, u₁.other, h.r7]
    exact ofNat_succ j
  · simp (config := {decide := true}) only [u₁₀.other, u₉.other, u₈.gpr, u₇.gpr, u₆.other, u₅.other,
      u₄.gpr, u₃.other, u₂.other, u₁.other, h.r5]
    rw [BitVec.add_assoc, ofNat_succ]
  · rw [u₁₀.gpr, r6, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  · rw [z₁₀, r6, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega) (by omega)]
    simp only [decide_eq_decide]; omega

def padBody : List Instr :=
  [.dp .add .r2 .r0 (.reg .r7), .strb .r8 .r2 32, .dp .add .r2 .r4 (.reg .r7),
    .strb .r9 .r2 32, .dp .add .r7 .r7 (.imm 1), .subs .r6 .r6 (.imm 1)]

theorem padLoop_eq : padLoop = .loop (.block padBody) .ne := rfl

theorem ipad_byte : (0x36 : BitVec 32).setWidth 8 = (0 : Byte) ^^^ ipad := by decide
theorem opad_byte : (0x5c : BitVec 32).setWidth 8 = (0 : Byte) ^^^ opad := by decide

theorem pad_step {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : kl s₀ ≤ j) (hj' : j < 64) {s : State}
    (h : Pad s₀ j s) : WP isa (.block padBody) s fun s' => Pad s₀ (j + 1) s' ∧ s'.z = decide (64 - (j + 1) = 0) := by
  have hin := hp.in_fit; have hou := hp.ou_fit
  have hl : j < (K0 s₀).length := by rw [K0_length s₀ hp]; omega
  unfold padBody
  refine wp_add (op2_reg _ _) fun s₁ u₁ => ?_
  refine wp_strb (a := inA s₀ + 32 + BitVec.ofNat 64 j) (by omega) ?_
    (by rw [u₁.wr]; exact buf_in hp h.wr hj' (.inl rfl)) fun s₂ u₂ => ?_
  · rw [u₁.gpr, h.r0, h.r7]; exact buf_addr hin hj'
  refine wp_add (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_strb (a := ouA s₀ + 32 + BitVec.ofNat 64 j) (by omega) ?_
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact buf_in hp h.wr hj' (.inr rfl)) fun s₄ u₄ => ?_
  · simp (config := {decide := true}) only [u₃.gpr, u₂.gpr, u₁.other, h.r4, h.r7]
    exact buf_addr hou hj'
  refine wp_add (op2_imm (by decide)) fun s₅ u₅ => wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ =>
    WP.block_nil ?_
  have k : ∀ r, r ≠ .r2 → r ≠ .r6 → r ≠ .r7 → s₆.gpr r = s.gpr r := fun r a b c => by
    rw [u₆.other r b, u₅.other r c, u₄.gpr, u₃.other r a, u₂.gpr, u₁.other r a]
  have hm : s₆.mem = (s.mem.writeW (inA s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j] ^^^ ipad)).writeW
      (ouA s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j] ^^^ opad) := by
    simp (config := {decide := true}) only [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.other,
      u₂.gpr, u₁.other, h.r8, h.r9, K0_ge hj hl, ipad_byte, opad_byte]
  have r6 : s₅.gpr .r6 = BitVec.ofNat 32 (64 - j) := by
    simp (config := {decide := true}) only [u₅.other, u₄.gpr, u₃.other, u₂.gpr, u₁.other, h.r6]
  refine ⟨⟨⟨by omega, by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    by rw [k _ (by decide) (by decide) (by decide), h.r0],
    by rw [k _ (by decide) (by decide) (by decide), h.r4], ?_,
    by rw [k _ (by decide) (by decide) (by decide), h.r8],
    by rw [k _ (by decide) (by decide) (by decide), h.r9],
    by rw [hm]; exact buf_write hp h.mem hj'⟩, ?_⟩, ?_⟩
  · simp (config := {decide := true}) only [u₆.other, u₅.gpr, u₄.gpr, u₃.other, u₂.gpr, u₁.other, h.r7]
    exact ofNat_succ j
  · rw [u₆.gpr, r6, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  · rw [z₆, r6, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega) (by omega)]
    simp only [decide_eq_decide]; omega

theorem key_loop_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Key s₀ 0 s) (hk : 0 < kl s₀) :
    WP isa keyLoop s (Buf s₀ (kl s₀)) := by
  have := hp.kl_le
  rw [keyLoop_eq]
  refine WP.loop (M := isa) (fun n s => ∃ j, n = kl s₀ - j ∧ j < kl s₀ ∧ Key s₀ j s) ?_ (kl s₀) s
    ⟨0, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, hb⟩
  refine WP.mono (key_step hp hj hb) fun s' ⟨hb', hz'⟩ => ?_
  have hz : isa.eval .ne s' = some (decide (kl s₀ - (j + 1) ≠ 0)) := by
    show VG.Arm.eval .ne s' = _
    rw [eval_ne, hz']
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
  refine WP.mono (pad_step hp hj hj' hb) fun s' ⟨hb', hz'⟩ => ?_
  have hz : isa.eval .ne s' = some (decide (64 - (j + 1) ≠ 0)) := by
    show VG.Arm.eval .ne s' = _
    rw [eval_ne, hz']
    simp
  by_cases hl : 64 - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
    rw [show (64 : Nat) = j + 1 by omega]; exact hb'.toBuf
  · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega, j + 1, rfl, by omega, by omega, hb'⟩

/-! ## The two compressions -/

theorem add32 {p : BitVec 32} (h : p.toNat + 96 ≤ 2 ^ 32) :
    State.addr (p + 32) = State.addr p + 32 ∧ (p + 32).toNat = p.toNat + 32 := by
  refine ⟨addr_add (k := 32) (by omega), ?_⟩
  rw [BitVec.toNat_add, show (32 : BitVec 32).toNat = 32 from rfl, Nat.mod_eq_of_lt (by omega)]

/-- The inlined compression of the block in the buffer of the state at `p`
(the inner or the outer one). -/
theorem compress_ok {s₀ : State} (hp : Pre s₀) {p : BitVec 32} (hpR : p = inn s₀ ∨ p = ou s₀) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (h0 : s.gpr .r0 = p) (h3 : s.gpr .r3 = scr s₀)
    (h1 : s.gpr .r1 = p + 32) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.gpr .r0 = p → s'.gpr .r3 = scr s₀ → s'.sp = s.sp →
      Frame [⟨State.addr p, 32⟩, ⟨scA s₀, 112⟩] s.mem s'.mem →
      stateAt s'.mem (State.addr p) =
        Spec.Sha256.compress (stateAt s.mem (State.addr p)) (Spec.Sha256.blockAt s.mem (State.addr p + 32)) →
      Q s') :
    WP isa compressAt s Q := by
  have hs : Region.Disjoint ⟨State.addr p, 96⟩ (scR s₀) ∧ ⟨State.addr p, 96⟩ ∈ s₀.wr ∧
      p.toNat + 96 ≤ 2 ^ 32 := by
    rcases hpR with rfl | rfl
    · exact ⟨hp.i_s, by simp [hp.wr], hp.in_fit⟩
    · exact ⟨hp.o_s, by simp [hp.wr], hp.ou_fit⟩
  obtain ⟨d, hm, hf⟩ := hs
  have hsc := hp.scr_fit
  obtain ⟨ea, et⟩ := add32 hf
  have e32 : Region.Sub ⟨State.addr p, 32⟩ ⟨State.addr p, 96⟩ := Region.sub_prefix (by omega)
  have eb : Region.Sub ⟨State.addr p + 32, 64⟩ ⟨State.addr p, 96⟩ := sub_offset (off := 32) (by omega) (by omega)
  have e112 : Region.Sub ⟨scA s₀, 112⟩ (scR s₀) := Region.sub_prefix (by omega)
  refine compressAt_ok (st := p) (scr := scr s₀) (src := p + 32) h0 h3 h1 (by omega) (by omega) (by omega)
    ((d.sub_left e32).sub_right e112) ?_ (by rw [ea]; exact (d.sub_left eb).sub_right e112) ?_ ?_
    fun s' h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ => hQ s' h₁ h₂ h₃ h₄ h₅ h₆ h₇ (by rw [h₈, ea])
  · rw [ea]; intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
  · rw [hrd, hwr, ea]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨State.addr p, 96⟩, by simp [hm], 32, rfl, by simp⟩
    · exact ⟨⟨State.addr p, 96⟩, by simp [hm], 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp [hp.wr], 0, by simp, by simp⟩
  · rw [hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨State.addr p, 96⟩, hm, 0, by simp, by simp⟩
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
def Post (s₀ s' : State) : Prop := abiPreserved s₀ s' ∧ Proof.Hmac.initSha256Arm.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (h3 : s.gpr .r3 = scr s₀) (hsp : s.sp = s₀.sp) (hsv : Saved s₀ s.mem)
    (hI : Repr s.mem (inA s₀) (xorPad (K0 s₀) ipad)) (hO : Repr s.mem (ouA s₀) (xorPad (K0 s₀) opad)) :
    WP isa (.block restore) s (Post s₀) := by
  refine restore_ok (scr := scr s₀) h3 hp.scr_fit
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hrd, hwr, hp.wr], contains_offset (by omega) (by omega)⟩) s₀.gpr
    hsv fun s' hs ho hmem _ _ hsp' => ⟨⟨fun r hr => ?_, by rw [hsp', hsp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs (.r4, 112) (by simp [saved])
    · exact hs (.r5, 116) (by simp [saved])
    · exact hs (.r6, 120) (by simp [saved])
    · exact hs (.r7, 124) (by simp [saved])
    · exact hs (.r8, 128) (by simp [saved])
    · exact hs (.r9, 132) (by simp [saved])
    · exact hs (.r10, 136) (by simp [saved])
    · exact hs (.r11, 140) (by simp [saved])
    · exact hs (.lr, 144) (by simp [saved])
  · simp only [Proof.Hmac.initSha256Arm]
    rw [blockKey_eq hp, hmem]
    exact ⟨hI, hO⟩

/-! ## Correctness -/

theorem buf_full {s₀ : State} (hp : Pre s₀) {m : Mem} (h : BufMem s₀ 64 m) :
    bytesAt m (inA s₀ + 32) 64 = xorPad (K0 s₀) ipad ∧ bytesAt m (ouA s₀ + 32) 64 = xorPad (K0 s₀) opad := by
  rw [h.bufI, h.bufO, List.take_of_length_le (by rw [K0_length s₀ hp])]
  exact ⟨rfl, rfl⟩

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa init s₀ (Post s₀) := by
  have hkl := hp.kl_le
  unfold init
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, z₁⟩ => ?_)
  -- The key.
  refine WP.seq (WP.mono (Q := Buf s₀ (kl s₀)) ?_ fun s₂ h₂ => ?_)
  · refine WP.ite (decide (kl s₀ = 0)) (by show VG.Arm.eval .eq s₁ = _; rw [eval_eq, z₁])
      (fun hb => WP.block_nil ?_) (fun hb => key_loop_ok hp h₁ ?_)
    · simp only [decide_eq_true_eq] at hb; rw [hb]; exact h₁.toBuf
    · simp only [decide_eq_false_iff_not] at hb; omega
  -- The padding.
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₃ u₃ => wp_subs (op2_reg _ _) fun s₄ u₄ z₄ =>
    WP.block_nil ?_)
  have k₄ : ∀ r, r ≠ .r6 → s₄.gpr r = s₂.gpr r := fun r h => by rw [u₄.other r h, u₃.other r h]
  have hP : Pad s₀ (kl s₀) s₄ := by
    refine ⟨⟨h₂.j_le, by rw [u₄.rd, u₃.rd, h₂.rd], by rw [u₄.wr, u₃.wr, h₂.wr],
      by rw [u₄.sp, u₃.sp, h₂.sp], by rw [k₄ _ (by decide), h₂.r0], by rw [k₄ _ (by decide), h₂.r4],
      by rw [k₄ _ (by decide), h₂.r7], by rw [k₄ _ (by decide), h₂.r8], by rw [k₄ _ (by decide), h₂.r9],
      by rw [u₄.mem, u₃.mem]; exact h₂.mem⟩, ?_⟩
    rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), h₂.r7, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl,
      sub_ofNat hkl]
  have hz₄ : s₄.z = decide (64 - kl s₀ = 0) := by
    rw [z₄, u₃.gpr, u₃.other _ (by decide), h₂.r7, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl,
      sub_beq (by omega) (by omega)]
    simp only [decide_eq_decide]; omega
  refine WP.seq (WP.mono (Q := Buf s₀ 64) ?_ fun s₆ h₆ => ?_)
  · refine WP.ite (decide (64 - kl s₀ = 0)) (by show VG.Arm.eval .eq s₄ = _; rw [eval_eq, hz₄])
      (fun hb => WP.block_nil ?_) (fun hb => pad_loop_ok hp hP ?_)
    · simp only [decide_eq_true_eq] at hb
      exact (show kl s₀ = 64 by omega) ▸ hP.toBuf
    · simp only [decide_eq_false_iff_not] at hb; omega
  obtain ⟨bI, bO⟩ := buf_full hp h₆.mem
  -- The inner block.
  refine WP.seq (wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [h₆.sp]; rfl)
    (by rw [h₆.rd, h₆.wr]; exact arg_in hp) fun s₇ u₇ => wp_add (op2_imm (by decide)) fun s₈ u₈ =>
      WP.block_nil ?_)
  have fW₆ : Frame s₀.wr s₀.mem s₆.mem := by rw [hp.wr]; exact h₆.mem.frame
  have hsa : s₆.mem.readW (stackArgAddr s₀ 0) 32 = scr s₀ := by
    refine fW₆.readW (r := argR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.a_i
    · exact hp.a_o
    · exact hp.a_s
  have m₈ : s₈.mem = s₆.mem := by rw [u₈.mem, u₇.mem]
  refine WP.seq (compress_ok hp (.inl rfl) (by rw [u₈.rd, u₇.rd, h₆.rd]) (by rw [u₈.wr, u₇.wr, h₆.wr])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), h₆.r0])
    (by rw [u₈.other _ (by decide), u₇.gpr, hsa])
    (by rw [u₈.gpr, u₇.other _ (by decide), h₆.r0]) fun s₉ rd₉ wr₉ cs₉ r0₉ r3₉ sp₉ fr₉ st₉ => ?_)
  have hI₉ : Repr s₉.mem (inA s₀) (xorPad (K0 s₀) ipad) :=
    repr_block (by rw [m₈]; exact h₆.mem.stI) (by rw [m₈]; exact bI)
      (by simp [xorPad, K0_length s₀ hp]) st₉
  have dO : ∀ r ∈ [(⟨inA s₀, 32⟩ : Region), ⟨scA s₀, 112⟩], Region.Disjoint ⟨ouA s₀, 96⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.i_o.symm.sub_right (sub32 _)
    · exact hp.o_s.sub_right (Region.sub_prefix (by omega))
  obtain ⟨sO₉, bO₉⟩ := state_frame fr₉ dO
  have sv₉ : Saved s₀ s₉.mem := by
    refine saved_frame (by rw [m₈]; exact h₆.mem.saved) fr₉ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact (hp.i_s.symm.sub_left (save_sub s₀)).sub_right (sub32 _)
    · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
  -- The outer block.
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁₀ u₁₀ => wp_add (op2_imm (by decide)) fun s₁₁ u₁₁ =>
    WP.block_nil ?_)
  have r4₉ : s₉.gpr .r4 = ou s₀ := by
    rw [cs₉ _ (by decide) (by decide), u₈.other _ (by decide), u₇.other _ (by decide), h₆.r4]
  have m₁₁ : s₁₁.mem = s₉.mem := by rw [u₁₁.mem, u₁₀.mem]
  refine WP.seq (compress_ok hp (.inr rfl) (by rw [u₁₁.rd, u₁₀.rd, rd₉, u₈.rd, u₇.rd, h₆.rd])
    (by rw [u₁₁.wr, u₁₀.wr, wr₉, u₈.wr, u₇.wr, h₆.wr])
    (by rw [u₁₁.other _ (by decide), u₁₀.gpr, r4₉])
    (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), r3₉])
    (by rw [u₁₁.gpr, u₁₀.gpr, r4₉])
    fun s₁₂ rd₁₂ wr₁₂ cs₁₂ r0₁₂ r3₁₂ sp₁₂ fr₁₂ st₁₂ => ?_)
  have hO : Repr s₁₂.mem (ouA s₀) (xorPad (K0 s₀) opad) :=
    repr_block (by rw [m₁₁, sO₉, m₈]; exact h₆.mem.stO) (by rw [m₁₁, bO₉, m₈]; exact bO)
      (by simp [xorPad, K0_length s₀ hp]) st₁₂
  have hI : Repr s₁₂.mem (inA s₀) (xorPad (K0 s₀) ipad) := by
    refine repr_congr (fun i hi => frame_bytes fr₁₂ (R := inR s₀) ?_ (by simp) hi) (m₁₁ ▸ hI₉)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.i_o.sub_right (sub32 _)
    · exact hp.i_s.sub_right (Region.sub_prefix (by omega))
  refine epilogue_ok hp (by rw [rd₁₂, u₁₁.rd, u₁₀.rd, rd₉, u₈.rd, u₇.rd, h₆.rd])
    (by rw [wr₁₂, u₁₁.wr, u₁₀.wr, wr₉, u₈.wr, u₇.wr, h₆.wr]) r3₁₂
    (by rw [sp₁₂, u₁₁.sp, u₁₀.sp, sp₉, u₈.sp, u₇.sp, h₆.sp]) ?_ hI hO
  refine saved_frame (by rw [m₁₁]; exact sv₉) fr₁₂ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact (hp.o_s.symm.sub_left (save_sub s₀)).sub_right (sub32 _)
  · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

/-! ## `Verified` -/

/-- The initial taint: `r0`–`r3` (`inner`, `outer`, `key`, `key_len`) are
public, `r0` and `r1` point at the two states, and the 4 bytes of stack
arguments are public, pointing at the scratch space. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [96, 96, 160], bases := [(.r0, 0), (.r1, 1)],
    argLen := 4, argBases := [(0, 2)] }

theorem wf₀ {s : State} (h : Proof.Hmac.initSha256Arm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have hi := hp.in_fit; have ho := hp.ou_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.i_o, hp.i_s⟩, hp.o_s, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 4⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.a_i
    · exact hp.a_o
    · exact hp.a_s
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem argByte_eq (s : State) (k : Nat) :
    VG.Arm.Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
  simp [VG.Arm.Taint.argByte, stackArgAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Hmac.initSha256Arm.pre s₁)
    (h₂ : Proof.Hmac.initSha256Arm.pre s₂) (hpub : Proof.Hmac.initSha256Arm.pub s₁ s₂) :
    VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [inR, ouR, scR, inA, ouA, scA, inn, ou, scr, p0, p1, a0]
  · simp only [τ₀] at hk
    rw [argByte_eq, argByte_eq, Mem.readW_byte s₁.mem _ hk,
      Mem.readW_byte s₂.mem _ hk]
    exact congrArg _ a0

/-- A state satisfying the precondition (with an empty key): `inner` at
`0x1000`, `outer` at `0x2000` and the scratch space at `0x4000`, passed on
the stack at `0x5000`. -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x40 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x5000, 4⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x2000, 96⟩, ⟨0x4000, 160⟩]

theorem init_verified : Verified Arm.target init Proof.Hmac.initSha256Arm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)
  · have e0 : stackArg sat 0 = 0x4000 := by decide
    refine ⟨sat, ?_⟩
    simp only [Proof.Hmac.initSha256Arm, e0]
    refine ⟨by decide, by simp [sat, stackArgAddr]; decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, by decide, by decide⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, sat, stackArgAddr, State.addr] at h₁ h₂
      bv_omega

end VG.Proof.Hmac.Arm.Init
