import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-!
# Streaming AES-CMAC on ARMv7: `vg_cmac_aes_finish`

The code saves `r4`, `r5` and `lr`, copies the chaining value to `out`,
computes the number of bytes held back, and calls `vg_cmac_aes_finalize` with
the state as its key and `out` as its state: its result is the MAC of the
message the state represents (`repr_finish`). The code before the call is
constant time by the taint analysis, and the call by its own proof
(`fin_rel`), its arguments pinned by `HMid`.
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_sub wp_and wp_orr wp_cmp wp_ldr
  wp_str wp_ldrSp saveMem saveList_ok saveMem_frame readW_writeW_save)
open VG.Proof.CmacAes.Arm (restoreB_ok saveMem_congr addr_word in_word in_word0)
open VG.Proof.Cmac.Stream (held held_le held_zero)

/-- The precondition, by name: the state `St`, `out` (`O`), the scratch
buffer `S` and the rounds `R`. -/
structure HPre (s₀ : State) (St O S : BitVec 32) (R : Nat) : Prop where
  r0 : s₀.gpr .r0 = St
  a0 : stackArg s₀ 0 = O
  a1 : stackArg s₀ 1 = S
  r1 : (s₀.gpr .r1).toNat = R
  rd : s₀.rd = [⟨stackArgAddr s₀ 0, 8⟩]
  wr : s₀.wr = [⟨State.addr St, 304⟩, ⟨State.addr O, 16⟩, ⟨State.addr S, 2304⟩]
  st_o : (⟨State.addr St, 304⟩ : Region).Disjoint ⟨State.addr O, 16⟩
  st_s : (⟨State.addr St, 304⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  o_s : (⟨State.addr O, 16⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  a_st : (⟨stackArgAddr s₀ 0, 8⟩ : Region).Disjoint ⟨State.addr St, 304⟩
  a_o : (⟨stackArgAddr s₀ 0, 8⟩ : Region).Disjoint ⟨State.addr O, 16⟩
  a_s : (⟨stackArgAddr s₀ 0, 8⟩ : Region).Disjoint ⟨State.addr S, 2304⟩
  b_st : (blw16 s₀).Disjoint ⟨State.addr St, 304⟩
  b_o : (blw16 s₀).Disjoint ⟨State.addr O, 16⟩
  b_s : (blw16 s₀).Disjoint ⟨State.addr S, 2304⟩
  fSt : St.toNat + 304 ≤ 2 ^ 32
  fO : O.toNat + 16 ≤ 2 ^ 32
  fS : S.toNat + 2304 ≤ 2 ^ 32
  sp : 16 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem HPre.of {s₀ : State} (h : finishArm.pre s₀) :
    HPre s₀ (s₀.gpr .r0) (stackArg s₀ 0) (stackArg s₀ 1) (s₀.gpr .r1).toNat :=
  let ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, o, p, q, r⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, i, j, k, l, m, n, o, p, q, r⟩

/-! ## Arguments on the stack -/

theorem arg1_eq {s : State} (h : s.sp.toNat + 8 ≤ 2 ^ 32) :
    stackArgAddr s 1 = stackArgAddr s 0 + BitVec.ofNat 64 4 := by
  simp only [stackArgAddr]
  rw [addr_add (by omega), addr_add (by omega)]
  simp

theorem arg_in {s : State} (h : s.sp.toNat + 8 ≤ 2 ^ 32) {rs : List Region} (hr : ⟨stackArgAddr s 0, 8⟩ ∈ rs)
    {k : Nat} (hk : k < 2) : InRegions rs (stackArgAddr s k) 4 := by
  refine ⟨_, hr, ?_⟩
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · simpa using Offset.contains_base (stackArgAddr s 0) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  · rw [arg1_eq h]; exact Offset.contains_base _ (by decide) (by decide)

/-! ## Saving the registers, and copying the chaining value -/

def fsaved : List (Reg × Nat) := [(.r4, 2176), (.r5, 2180), (.lr, 2184)]

theorem fsaved_bound : ∀ p ∈ fsaved, 2176 ≤ p.2 ∧ p.2 + 4 ≤ 2188 := by decide

/-- The copy of the chaining value, a word at a time through `lr`. -/
def cvCopy : List Instr :=
  [.ldr .lr .r0 272, .str .lr .r12 0, .ldr .lr .r0 276, .str .lr .r12 4, .ldr .lr .r0 280, .str .lr .r12 8,
   .ldr .lr .r0 284, .str .lr .r12 12]

/-- `count`'s bytes held back, and whether `count` is 0. -/
def heldBlk : List Instr :=
  [.dp .sub .r4 .r2 (.imm 1), .dp .and .r4 .r4 (.imm 15), .dp .add .r4 .r4 (.imm 1),
   .dp .orr .r2 .r2 (.reg .r3), .cmp .r2 (.imm 0)]

theorem finishPre_eq : finishPre = .ldrSp .r12 4 :: (fsaved.map (fun p => Instr.str p.1 .r12 p.2) ++
    (mov .r5 .r12 :: .ldrSp .r12 0 :: (cvCopy ++ heldBlk))) := rfl

/-- The memory after saving the registers. -/
def fsMem (s₀ : State) (S : BitVec 32) : Mem := saveMem s₀.mem (State.addr S) s₀.gpr fsaved

set_option simprocs false in
theorem fsMem_slot (s₀ : State) (S : BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ fsaved) :
    (fsMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
  simp only [fsaved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  simp (disch := decide) only [fsMem, fsaved, saveMem, Mem.readW_writeW_self32, readW_writeW_save]

theorem fsMem_frame (s₀ : State) (S : BitVec 32) : Frame [⟨State.addr S, 2304⟩] s₀.mem (fsMem s₀ S) :=
  saveMem_frame _ _ _ (by decide) fsaved fun p hp => by have := fsaved_bound p hp; omega

/-- The memory after copying the block at `p` to `o`, a word at a time. -/
def cvMem (m : Mem) (o p : Addr) : Mem :=
  Proof.Cmac.store4 m o (m.readW p 32) (m.readW (p + BitVec.ofNat 64 4) 32) (m.readW (p + BitVec.ofNat 64 8) 32)
    (m.readW (p + BitVec.ofNat 64 12) 32)

theorem cvMem_bytes (m : Mem) (o p : Addr) : Spec.Aes.bytesAt (cvMem m o p) o 16 = Spec.Aes.bytesAt m p 16 := by
  rw [cvMem, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, ← Proof.Cmac.bytesAt_split4]

theorem cvMem_frame (m : Mem) (o p : Addr) : Frame [⟨o, 16⟩] m (cvMem m o p) := Proof.Cmac.frame_store4 _ _ _ _ _

theorem cvCopy_ok {is : List Instr} {s : State} {Q : State → Prop} {St O : BitVec 32}
    (h0 : s.gpr .r0 = St) (h12 : s.gpr .r12 = O) (fSt : St.toNat + 288 ≤ 2 ^ 32) (fO : O.toNat + 16 ≤ 2 ^ 32)
    (hr : Covers [⟨State.addr St + BitVec.ofNat 64 272, 16⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr O, 16⟩] s.wr)
    (hd : (⟨State.addr O, 16⟩ : Region).Disjoint ⟨State.addr St + BitVec.ofNat 64 272, 16⟩)
    (k : ∀ s', (∀ r, r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.mem = cvMem s.mem (State.addr O) (State.addr St + BitVec.ofNat 64 272) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (cvCopy ++ is)) s Q := by
  have aP (i : Nat) (hi : i ≤ 12) : State.addr (St + BitVec.ofNat 32 (272 + i)) =
      State.addr St + BitVec.ofNat 64 272 + BitVec.ofNat 64 i := addr_word i (by omega) hi
  have aO (i : Nat) (hi : i ≤ 12) : State.addr (O + BitVec.ofNat 32 (0 + i)) =
      State.addr O + BitVec.ofNat 64 0 + BitVec.ofNat 64 i := addr_word i (by omega) hi
  have o0 : State.addr O + BitVec.ofNat 64 0 = State.addr O := BitVec.add_zero _
  rw [o0] at aO
  have dW (i j : Nat) (hi : i ≤ 12) (hj : j ≤ 12) :
      (⟨State.addr O + BitVec.ofNat 64 i, 4⟩ : Region).Disjoint ⟨State.addr St + BitVec.ofNat 64 272 + BitVec.ofNat 64 j, 4⟩ :=
    (hd.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
  have dW0 (j : Nat) (hj : j ≤ 12) :
      (⟨State.addr O, 4⟩ : Region).Disjoint ⟨State.addr St + BitVec.ofNat 64 272 + BitVec.ofNat 64 j, 4⟩ := by
    have := dW 0 j (by decide) hj; rwa [BitVec.add_zero] at this
  simp only [cvCopy, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr St + BitVec.ofNat 64 272) (by decide) (by rw [h0]; exact addr_add (by omega))
    (in_word0 hr) fun s₁ u₁ => ?_
  refine wp_str (a := State.addr O) (by decide)
    (by rw [u₁.other _ (by decide), h12, BitVec.add_zero]) (by rw [u₁.wr]; exact in_word0 hw) fun s₂ v₂ => ?_
  refine wp_ldr (a := State.addr St + BitVec.ofNat 64 272 + BitVec.ofNat 64 4) (by decide)
    (by rw [v₂.gpr, u₁.other _ (by decide), h0]; exact aP 4 (by decide))
    (by rw [v₂.rd, v₂.wr, u₁.rd, u₁.wr]; exact in_word hr (by decide)) fun s₃ u₃ => ?_
  refine wp_str (a := State.addr O + BitVec.ofNat 64 4) (by decide)
    (by rw [u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), h12]; exact aO 4 (by decide))
    (by rw [u₃.wr, v₂.wr, u₁.wr]; exact in_word hw (by decide)) fun s₄ v₄ => ?_
  refine wp_ldr (a := State.addr St + BitVec.ofNat 64 272 + BitVec.ofNat 64 8) (by decide)
    (by rw [v₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), h0]; exact aP 8 (by decide))
    (by rw [v₄.rd, v₄.wr, u₃.rd, u₃.wr, v₂.rd, v₂.wr, u₁.rd, u₁.wr]; exact in_word hr (by decide))
    fun s₅ u₅ => ?_
  refine wp_str (a := State.addr O + BitVec.ofNat 64 8) (by decide)
    (by rw [u₅.other _ (by decide), v₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), h12]
        exact aO 8 (by decide))
    (by rw [u₅.wr, v₄.wr, u₃.wr, v₂.wr, u₁.wr]; exact in_word hw (by decide)) fun s₆ v₆ => ?_
  refine wp_ldr (a := State.addr St + BitVec.ofNat 64 272 + BitVec.ofNat 64 12) (by decide)
    (by rw [v₆.gpr, u₅.other _ (by decide), v₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), h0]
        exact aP 12 (by decide))
    (by rw [v₆.rd, v₆.wr, u₅.rd, u₅.wr, v₄.rd, v₄.wr, u₃.rd, u₃.wr, v₂.rd, v₂.wr, u₁.rd, u₁.wr]
        exact in_word hr (by decide)) fun s₇ u₇ => ?_
  refine wp_str (a := State.addr O + BitVec.ofNat 64 12) (by decide)
    (by rw [u₇.other _ (by decide), v₆.gpr, u₅.other _ (by decide), v₄.gpr, u₃.other _ (by decide), v₂.gpr,
          u₁.other _ (by decide), h12]
        exact aO 12 (by decide))
    (by rw [u₇.wr, v₆.wr, u₅.wr, v₄.wr, u₃.wr, v₂.wr, u₁.wr]; exact in_word hw (by decide)) fun s₈ v₈ => ?_
  refine k s₈ (fun r hr => ?_) ?_ ?_ ?_ ?_
  · rw [v₈.gpr, u₇.other _ hr, v₆.gpr, u₅.other _ hr, v₄.gpr, u₃.other _ hr, v₂.gpr, u₁.other _ hr]
  · rw [v₈.mem, u₇.gpr, u₇.mem, v₆.mem, u₅.gpr, u₅.mem, v₄.mem, u₃.gpr, u₃.mem, v₂.mem, u₁.gpr, u₁.mem]
    simp only [Proof.Cmac.readW_writeW_disj _ (dW0 4 (by decide)), Proof.Cmac.readW_writeW_disj _ (dW0 8 (by decide)),
      Proof.Cmac.readW_writeW_disj _ (dW0 12 (by decide)),
      Proof.Cmac.readW_writeW_disj _ (dW 4 8 (by decide) (by decide)),
      Proof.Cmac.readW_writeW_disj _ (dW 4 12 (by decide) (by decide)),
      Proof.Cmac.readW_writeW_disj _ (dW 8 12 (by decide) (by decide))]
    rfl
  · rw [v₈.rd, u₇.rd, v₆.rd, u₅.rd, v₄.rd, u₃.rd, v₂.rd, u₁.rd]
  · rw [v₈.wr, u₇.wr, v₆.wr, u₅.wr, v₄.wr, u₃.wr, v₂.wr, u₁.wr]
  · rw [v₈.sp, u₇.sp, v₆.sp, u₅.sp, v₄.sp, u₃.sp, v₂.sp, u₁.sp]

/-! ## Before the call -/

/-- What the block before `lastLen` leaves. -/
structure HBlk (s₀ : State) (St O S : BitVec 32) (s : State) : Prop where
  r0 : s.gpr .r0 = St
  r1 : s.gpr .r1 = s₀.gpr .r1
  r4 : s.gpr .r4 = ((s₀.gpr .r2 - 1) &&& 15) + 1
  r5 : s.gpr .r5 = S
  r12 : s.gpr .r12 = O
  z : s.z = ((s₀.gpr .r2 ||| s₀.gpr .r3) - 0 == 0)
  mem : s.mem = cvMem (fsMem s₀ S) (State.addr O) (State.addr St + BitVec.ofNat 64 272)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .lr → s.gpr r = s₀.gpr r

theorem finishPre_wp {s₀ : State} {St O S : BitVec 32} {R : Nat} (hp : HPre s₀ St O S R) :
    WP isa (.block finishPre) s₀ (HBlk s₀ St O S) := by
  have hS := hp.fS
  have hSt := hp.fSt
  rw [finishPre_eq]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl
    (arg_in hp.spf (by rw [hp.rd]; simp) (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = S := by rw [u₁.gpr]; exact hp.a1
  refine saveList_ok fsaved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have := fsaved_bound p hp'
    rw [h12, u₁.wr, hp.wr]
    exact ⟨by omega, by omega, ⟨⟨State.addr S, 2304⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩⟩
  have hm₂ : s₂.mem = fsMem s₀ S := by
    rw [m₂, u₁.mem, h12, fsMem]
    exact saveMem_congr _ _ _ fun p hp' => u₁.other _ (by
      simp only [fsaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl <;> decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact arg_in hp.spf (by rw [hp.rd]; simp) (by decide))
    fun s₄ u₄ => ?_
  have hO : s₄.gpr .r12 = O := by
    rw [u₄.gpr, u₃.mem, hm₂, ← hp.a0]
    exact (fsMem_frame s₀ S).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.a_s.sub_left (Region.sub_prefix (by decide))) (by decide)
  have rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, rd₂, u₁.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, wr₂, u₁.wr]
  have c272 : Region.Sub ⟨State.addr St + BitVec.ofNat 64 272, 16⟩ ⟨State.addr St, 304⟩ :=
    Offset.sub_base _ (by decide)
  refine cvCopy_ok (St := St) (O := O)
    (by simp (disch := decide) only [u₄.other, u₃.other, g₂, u₁.other, hp.r0]) hO (by omega) hp.fO
    (by
      rw [rd₄, wr₄, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨State.addr St, 304⟩, by simp, 272, rfl, by simp⟩)
    (by
      rw [wr₄, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨State.addr O, 16⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩)
    (hp.st_o.symm.sub_right c272) fun s₅ g₅ m₅ rd₅ wr₅ sp₅ => ?_
  simp only [heldBlk]
  refine wp_sub (op2_imm (by decide)) fun s₆ u₆ => wp_and (op2_imm (by decide)) fun s₇ u₇ =>
    wp_add (op2_imm (by decide)) fun s₈ u₈ => wp_orr (op2_reg _ _) fun s₉ u₉ =>
    wp_cmp (op2_imm (by decide)) fun s₁₀ f₁₀ z₁₀ => WP.block_nil ?_
  have g : ∀ r, r ≠ .lr → r ≠ .r2 → r ≠ .r4 → r ≠ .r12 → r ≠ .r5 → s₁₀.gpr r = s₀.gpr r := fun r a b c d e => by
    rw [f₁₀.gpr, u₉.other _ b, u₈.other _ c, u₇.other _ c, u₆.other _ c, g₅ _ a, u₄.other _ d, u₃.other _ e, g₂,
      u₁.other _ d]
  refine ⟨by rw [g .r0 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hp.r0,
    g .r1 (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₁₀.gpr, u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.gpr, g₅ _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  · rw [f₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      g₅ _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, h12]
  · rw [f₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      g₅ _ (by decide), hO]
  · rw [z₁₀, u₉.gpr]
    simp (disch := decide) only [u₈.other, u₇.other, u₆.other, g₅, u₄.other, u₃.other, g₂, u₁.other]
  · rw [f₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅, u₄.mem, u₃.mem, hm₂]
  · rw [f₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, sp₅, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [f₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅, rd₄]
  · rw [f₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅, wr₄]
  · intro r hr a b c
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl a
    | exact absurd rfl b
    | exact absurd rfl c
    | exact g _ (by decide) (by decide) (by decide) (by decide) (by decide)

/-- What the code before the call leaves. -/
structure HMid (s₀ : State) (St O S : BitVec 32) (R : Nat) (s : State) : Prop where
  args : FArgs s St O (St + BitVec.ofNat 32 288) S (held (countArm s₀).toNat) R
  mem : s.mem = cvMem (fsMem s₀ S) (State.addr O) (State.addr St + BitVec.ofNat 64 272)
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .lr → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem HPre.aL {s₀ : State} {St O S : BitVec 32} {R : Nat} (hp : HPre s₀ St O S R) :
    State.addr (St + BitVec.ofNat 32 288) = State.addr St + BitVec.ofNat 64 288 := addr_add (by have := hp.fSt; omega)

theorem HPre.fargs {s₀ s : State} {St O S : BitVec 32} {R L : Nat} (hp : HPre s₀ St O S R) (hL : L ≤ 16)
    (r0 : s.gpr .r0 = St) (r1 : s.gpr .r1 = s₀.gpr .r1) (r2 : s.gpr .r2 = O)
    (r3 : s.gpr .r3 = St + BitVec.ofNat 32 288) (r4 : s.gpr .r4 = BitVec.ofNat 32 L) (r5 : s.gpr .r5 = S)
    (sp : s.sp = s₀.sp) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    FArgs s St O (St + BitVec.ofNat 32 288) S L R := by
  have hw := hp.fSt
  have pSt : Region.Sub ⟨State.addr (St + BitVec.ofNat 32 288), L⟩ ⟨State.addr St, 304⟩ := by
    rw [hp.aL]; exact Offset.sub_base _ (by omega)
  have hb : blw16 s = blw16 s₀ := by rw [blw16, sp]
  exact
  { r0 := r0, r2 := r2, r3 := r3, r4 := r4, r5 := r5
    r1 := by rw [r1]; exact BitVec.eq_of_toNat_eq (by rw [hp.r1, toNat_ofNat32 (by rcases hp.rounds with h | h | h <;> omega)])
    rounds := hp.rounds, len := hL
    hsp := by rw [sp]; exact hp.sp
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := (hp.st_s.sub_left pSt).sub_right (Region.sub_prefix (by decide))
    sts := hp.o_s.sub_right (Region.sub_prefix (by decide))
    bk := by rw [hb]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bp := by rw [hb]; exact hp.b_st.sub_right pSt
    bst := by rw [hb]; exact hp.b_o
    bs := by rw [hb]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fK := by omega
    fSt := hp.fO
    fP := by rw [toNat_add_ofNat (by omega)]; omega
    fS := by have := hp.fS; omega
    reads := by
      rw [rd, wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr St, 304⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
      · exact ⟨⟨State.addr St, 304⟩, by simp, 288, hp.aL, by simp; omega⟩
    writes := by
      rw [wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr O, 16⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
      · exact ⟨⟨State.addr S, 2304⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩ }

theorem finPre_wp {s₀ : State} {St O S : BitVec 32} {R : Nat} (hp : HPre s₀ St O S R) :
    WP isa finPre s₀ (HMid s₀ St O S R) := by
  refine WP.seq (WP.mono (finishPre_wp hp) fun s₁ h₁ => ?_)
  have hc := (countArm s₀).isLt
  have ev : isa.eval .eq s₁ = some (decide ((countArm s₀).toNat = 0)) := by
    show VG.Arm.eval .eq s₁ = _
    rw [VG.Proof.MdStream.Arm.eval_eq, h₁.z, or_beq_zero (count_eq s₀) hc]
  have tail : ∀ {t : State} {L : Nat}, L ≤ 16 → t.gpr .r4 = BitVec.ofNat 32 L → L = held (countArm s₀).toNat →
      (∀ r, r ≠ .r4 → t.gpr r = s₁.gpr r) → t.mem = s₁.mem → t.sp = s₁.sp → t.rd = s₁.rd → t.wr = s₁.wr →
      WP isa (.block finArgs) t (HMid s₀ St O S R) := fun {t L} hL h4 hLe g m sp rd wr => by
    refine wp_mov (op2_reg _ _) fun t₁ u₁ => wp_add (op2_imm (by decide)) fun t₂ u₂ => WP.block_nil ?_
    have g₂ : ∀ r, r ≠ .r2 → r ≠ .r3 → t₂.gpr r = t.gpr r := fun r a b => by rw [u₂.other _ b, u₁.other _ a]
    refine ⟨hLe ▸ hp.fargs hL (by rw [g₂ _ (by decide) (by decide), g _ (by decide), h₁.r0])
      (by rw [g₂ _ (by decide) (by decide), g _ (by decide), h₁.r1])
      (by rw [u₂.other _ (by decide), u₁.gpr, g _ (by decide), h₁.r12])
      (by rw [u₂.gpr, u₁.other _ (by decide), g _ (by decide), h₁.r0]; rfl)
      (by rw [g₂ _ (by decide) (by decide), h4]) (by rw [g₂ _ (by decide) (by decide), g _ (by decide), h₁.r5])
      (by rw [u₂.sp, u₁.sp, sp, h₁.sp]) (by rw [u₂.rd, u₁.rd, rd, h₁.rd]) (by rw [u₂.wr, u₁.wr, wr, h₁.wr]),
      by rw [u₂.mem, u₁.mem, m, h₁.mem], fun r hr a b c => ?_, by rw [u₂.sp, u₁.sp, sp, h₁.sp],
      by rw [u₂.rd, u₁.rd, rd, h₁.rd], by rw [u₂.wr, u₁.wr, wr, h₁.wr]⟩
    have : r ≠ .r2 ∧ r ≠ .r3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₂ _ this.1 this.2, g _ a, h₁.keep r hr a b c]
  refine WP.seq ?_
  by_cases h0 : (countArm s₀).toNat = 0
  · refine WP.ite true (by rw [ev, h0]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_
    exact tail (L := 0) (by decide) u.gpr (by rw [h0]; rfl) (fun r h => u.other r h) u.mem u.sp u.rd u.wr
  · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => WP.block_nil ?_
    refine tail (held_le _) ?_ rfl (fun _ _ => rfl) rfl rfl rfl rfl
    rw [h₁.r4]
    exact held_lo (count_eq s₀) hc h0

/-! ## The whole function -/

theorem finishPost_eq : finishPost = ([(.r4, 2176), (.lr, 2184)] : List (Reg × Nat)).map
    (fun p => Instr.ldr p.1 .r5 p.2) ++ ([.ldr .r5 .r5 2180] : List Instr) := rfl

theorem finish_wp {s₀ : State} (h0 : finishArm.pre s₀) :
    WP isa finish s₀ fun s' => abiPreserved s₀ s' ∧ finishArm.post s₀ s' := by
  have hp := HPre.of h0
  generalize s₀.gpr .r0 = St at hp
  generalize stackArg s₀ 0 = O at hp
  generalize stackArg s₀ 1 = S at hp
  generalize (s₀.gpr .r1).toNat = R at hp
  have hSt := hp.fSt
  have hS := hp.fS
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (fin_call h₁.args) fun s₂ h₂ => ?_)
  have e5 : s₂.gpr .r5 = S := by rw [h₂.saved _ (by simp [preserved]) (by decide), h₁.args.r5]
  have rdwr : s₂.rd ++ s₂.wr = [⟨stackArgAddr s₀ 0, 8⟩, ⟨State.addr St, 304⟩, ⟨State.addr O, 16⟩,
      ⟨State.addr S, 2304⟩] := by
    rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  have inS (d : Nat) (hd : d + 4 ≤ 2304) : InRegions (s₂.rd ++ s₂.wr) (State.addr S + BitVec.ofNat 64 d) 4 := by
    rw [rdwr]; exact ⟨⟨State.addr S, 2304⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  rw [finishPost_eq]
  refine restoreB_ok [(.r4, 2176), (.lr, 2184)] s₂ _ (by decide) (fun p hp' => ?_)
    fun s₃ ld₃ ho₃ m₃ rd₃ wr₃ sp₃ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rw [e5]
    rcases hp' with rfl | rfl
    · exact ⟨by decide, by decide, by omega, inS _ (by decide)⟩
    · exact ⟨by decide, by decide, by omega, inS _ (by decide)⟩
  refine wp_ldr (a := State.addr S + BitVec.ofNat 64 2180) (by decide)
    (by rw [ho₃ _ (by decide), e5]; exact addr_add (by omega))
    (by rw [rd₃, wr₃]; exact inS _ (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, m₃]
  -- The saved registers.
  have slot (d : Nat) (hd : 2176 ≤ d) (hd' : d + 4 ≤ 2188) :
      s₂.mem.readW (State.addr S + BitVec.ofNat 64 d) 32 = (fsMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 := by
    have sub : Region.Sub ⟨State.addr S + BitVec.ofNat 64 d, 4⟩ ⟨State.addr S, 2304⟩ := Offset.sub_base _ (by omega)
    have c := Region.contains_self (State.addr S + BitVec.ofNat 64 d) 4
    rw [h₂.frame.readW c (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.o_s.symm.sub_left sub
        · exact Offset.disjoint_base _ hd (by omega)
        · rw [blw16, h₁.sp]; exact (hp.b_s.sub_right sub).symm) (by decide), h₁.mem,
      (cvMem_frame _ _ _).readW c (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.o_s.symm.sub_left sub) (by decide)]
  refine ⟨⟨fun r hr => ?_, by rw [u₄.sp, sp₃, h₂.sp, h₁.sp]⟩, ?_⟩
  · have hr' := hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₄.other _ (by decide), ld₃ (.r4, 2176) (by simp), e5, slot 2176 (by decide) (by decide),
        fsMem_slot s₀ S (r := .r4) (d := 2176) (by decide)]
    · rw [u₄.gpr, m₃, slot 2180 (by decide) (by decide), fsMem_slot s₀ S (r := .r5) (d := 2180) (by decide)]
    all_goals first
      | rw [u₄.other _ (by decide), ld₃ (.lr, 2184) (by simp), e5, slot 2184 (by decide) (by decide),
          fsMem_slot s₀ S (r := .lr) (d := 2184) (by decide)]
      | rw [u₄.other _ (by decide), ho₃ _ (by decide), h₂.saved _ hr' (by decide),
          h₁.keep _ hr' (by decide) (by decide) (by decide)]
  · intro key msg hr hR hcnt hlen
    rw [hp.r0] at hr
    rw [hp.a0, m₄]
    have hc : (countArm s₀).toNat = msg.length := by rw [hcnt, toNat_ofNat64 hlen]
    have hR' : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.r1]; exact hR
    -- The state is unchanged before the call.
    have fSt : ∀ {d n : Nat}, d + n ≤ 304 → Spec.Aes.bytesAt s₁.mem (State.addr St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₀.mem (State.addr St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      have sub : Region.Sub ⟨State.addr St + BitVec.ofNat 64 d, n⟩ ⟨State.addr St, 304⟩ := Offset.sub_base _ hd
      rw [h₁.mem, Proof.Cmac.bytesAt_frame (cvMem_frame _ _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hp.st_o.sub_left sub) (by omega),
        Proof.Cmac.bytesAt_frame (fsMem_frame _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hp.st_s.sub_left sub) (by omega)]
    obtain ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩ := (Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr
    have hsch : Spec.Aes.bytesAt s₁.mem (State.addr St) (16 * (R + 1)) = Spec.Aes.expandKey key := by
      have := fSt (d := 0) (n := 16 * (R + 1)) (by rcases hp.rounds with h | h | h <;> omega)
      rw [BitVec.add_zero] at this; rw [this, hR']; exact hks
    have hciph : Spec.Cmac.aesWith R (Spec.Aes.bytesAt s₁.mem (State.addr St) (16 * (R + 1))) = Spec.Cmac.aes key := by
      rw [hsch, hR']; rfl
    have e₁ : Spec.Aes.bytesAt s₁.mem (State.addr St + 240) 32 = Spec.Aes.bytesAt s₀.mem (State.addr St + 240) 32 :=
      fSt (d := 240) (by decide)
    have e₂ : Spec.Aes.bytesAt s₁.mem (State.addr O) 16 = Spec.Aes.bytesAt s₀.mem (State.addr St + 272) 16 := by
      rw [h₁.mem, cvMem_bytes]
      exact Proof.Cmac.bytesAt_frame (fsMem_frame _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_s.sub_left (Offset.sub_base _ (by decide))) (by decide)
    have e₃ : Spec.Aes.bytesAt s₁.mem (State.addr (St + BitVec.ofNat 32 288)) (held (countArm s₀).toNat) =
        Spec.Aes.bytesAt s₀.mem (State.addr St + 288) (held msg.length) := by
      rw [hp.aL, hc]; exact fSt (by have := held_le msg.length; omega)
    obtain ⟨hm, hne, hst, happ⟩ := Proof.Cmac.Stream.repr_finish
      ((Proof.Cmac.Stream.repr_iff _ _ _ _).mpr ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩)
    have out := h₂.out (by rw [hciph, e₁]; exact hsk) _ hm (by rw [hc]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, e₃, happ, Proof.Cmac.Stream.aesCmac_eq]

/-! ## Constant time -/

/-- The stack arguments of a state satisfying the precondition, for the
taint analysis. -/
theorem HPre.wfA {s₀ : State} {St O S : BitVec 32} {R : Nat} (hp : HPre s₀ St O S R) :
    s₀.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ s₀.wr, Region.Disjoint ⟨State.addr s₀.sp, 8⟩ r := by
  have e : (⟨State.addr s₀.sp, 8⟩ : Region) = ⟨stackArgAddr s₀ 0, 8⟩ := by simp [stackArgAddr]
  refine ⟨hp.spf, ?_⟩
  rw [e, hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hp.a_st
  · exact hp.a_o
  · exact hp.a_s

theorem finish_rel {s₀ s₀' : State} (h0 : finishArm.pre s₀) (h0' : finishArm.pre s₀')
    (hq : finishArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finish fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp := HPre.of h0
  have hp' : HPre s₀' (s₀.gpr .r0) (stackArg s₀ 0) (stackArg s₀ 1) (s₀.gpr .r1).toNat := by
    rw [q2, q3, q6, q7]; exact HPre.of h0'
  have hc : (countArm s₀').toNat = (countArm s₀).toNat := by simp only [countArm, q4, q5]
  have wf := hp.wfA
  have wf' := hp'.wfA
  generalize s₀.gpr .r0 = St at hp hp'
  generalize stackArg s₀ 0 = O at hp hp'
  generalize stackArg s₀ 1 = S at hp hp'
  generalize (s₀.gpr .r1).toNat = R at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 8) finPre h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r5]) (.block finishPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := HMid s₀ St O S R)
    (G' := HMid s₀' St O S R) (argTaint [.r0, .r1, .r2, .r3] 8)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) q1 wf wf' (argMem_of (j := 2) q1 hp.spf fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> assumption
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact q6
        · exact q7) ⟨_, hA⟩
    (fun s e => by rw [e]; exact finPre_wp hp) (fun s e => by rw [e]; exact finPre_wp hp')
  have c := rel_wp (F := HMid s₀ St O S R) (F' := HMid s₀' St O S R)
    (G := fun s => s.gpr .r5 = S) (G' := fun s => s.gpr .r5 = S)
    (fin_rel (sp₀ := s₀.sp) fun _ _ h => ⟨h.1.args, by rw [← hc]; exact h.2.args, h.1.sp, h.2.sp.trans q1.symm⟩)
    (fun _ h => WP.mono (fin_call h.args) fun _ h' => by
      rw [h'.saved _ (by simp [preserved]) (by decide)]; exact h.args.r5)
    (fun _ h => WP.mono (fin_call h.args) fun _ h' => by
      rw [h'.saved _ (by simp [preserved]) (by decide)]; exact h.args.r5)
  have p := RelCT.taint (A := taint) (P := fun a b => a.gpr .r5 = S ∧ b.gpr .r5 = S)
    (Taint.ofRegs [.r5]) (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1, h.2]) hB
  exact a.seq (c.seq p)

theorem finish_ct : ConstantTime isa finishArm.pre finishArm.pub finish :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finish_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.Arm
