import VerifiedGarbage.Proof.Sha512.Arm.Rounds
import VerifiedGarbage.Proof.Sha512.Arm.Contract
import Mathlib.Tactic.Set

/-!
# SHA-512 compression function on ARMv7: the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha512.Arm

open VG VG.Arm VG.Impl.Sha512.Arm
open VG.Spec.Sha512 (HashValue Word Block W stateAt blockAt compress compressBlocks parseBlock)
open VG.Proof.MdStream.Arm (contains_offset)
open VG.Proof.MdStream.Arm (sub_offset wp_add wp_subs wp_mov wp_cmp op2_imm op2_reg eval_ne)

/-! ## Memory -/

theorem stateAt_get {st : BitVec 32} (hfit : st.toNat + 64 ≤ 2 ^ 32) (m : Mem) {k : Nat} (hk : k < 8) :
    (stateAt m (State.addr st))[k] = rd64 m st (8 * k) := by
  simp only [stateAt, Vector.getElem_ofFn, rd64]
  rw [readW64, A_eq (by omega), A_eq (by omega),
    show State.addr st + BitVec.ofNat 64 (8 * k) + 4 = State.addr st + BitVec.ofNat 64 (8 * k + 4) by
      bv_omega]

theorem stateAt_ext {st : BitVec 32} (hfit : st.toNat + 64 ≤ 2 ^ 32) {m : Mem} {H : HashValue}
    (h : ∀ k (hk : k < 8), rd64 m st (8 * k) = H[k]) : stateAt m (State.addr st) = H := by
  ext k hk
  rw [stateAt_get hfit m hk, h k hk]

theorem cat44 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((b0 ++ b1 ++ b2 ++ b3 : BitVec 32) ++ (b4 ++ b5 ++ b6 ++ b7 : BitVec 32) : BitVec 64) =
      (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 : BitVec 64) := by
  simp only [BitVec.append_assoc, BitVec.cast_eq]

theorem add_one' (p : Addr) (a : Nat) : p + BitVec.ofNat 64 a + 1 = p + BitVec.ofNat 64 (a + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- `loadW` makes the block's words from its bytes. -/
theorem raw_block {bk : BitVec 32} (hfit : bk.toNat + 128 ≤ 2 ^ 32) (m : Mem) :
    Raw bk (blockAt m (State.addr bk)) m := by
  intro j hj
  rw [W_lt _ hj]
  simp only [blockAt, parseBlock, rd64, lo_append, hi_append]
  rw [A_eq (by omega), A_eq (by omega), rev_readW, rev_readW]
  simp only [add_one', Nat.add_assoc]
  exact cat44 _ _ _ _ _ _ _ _

/-! ## Loading the working variables -/

structure LdInv (st scr : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ∉ [X0, X1] → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vars : ∀ k < n, rd64 s'.mem scr (8 * k) = rd64 s.mem st (8 * k)
  frame : Frame [workR scr] s.mem s'.mem

theorem Ctx.disjW {st scr : BitVec 32} {s : State} (c : Ctx st scr s) : (stR st).Disjoint (workR scr) :=
  c.disj.sub_right (Region.sub_prefix (by omega))

theorem load_ok {st scr : BitVec 32} {s : State} (c : Ctx st scr s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap loadH)) s (LdInv st scr s n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega),
      Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ h₁ => ?_
    have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [loadH, ← List.append_nil (Impl.Sha512.Arm.st X0 X1 .r3 (8 * n))]
    refine wp_ld (by decide) (by decide) (by omega) c₁.r0 (c₁.wS _ (by omega)).1
      (c₁.wS _ (by omega)).2 fun s₂ o₂ p₂ => ?_
    refine wp_st (by omega) (by rw [o₂.gpr _ (by decide), c₁.r3]) p₂
      (by rw [o₂.wr]; exact (c₁.wV _ (by omega)).1) (by rw [o₂.wr]; exact (c₁.wV _ (by omega)).2)
      fun s₃ u₃ => WP.block_nil ⟨fun r hr => ?_, by rw [u₃.rd, o₂.rd, h₁.rd],
        by rw [u₃.wr, o₂.wr, h₁.wr], by rw [u₃.sp, o₂.sp, h₁.sp], fun k hk => ?_, ?_⟩
    · rw [u₃.gpr, o₂.gpr r hr, h₁.gpr r hr]
    · have fitV := c.fitV
      rw [u₃.mem]
      by_cases hkn : k = n
      · subst hkn
        rw [rd64_write64_self _ _ (by omega),
          rd64_frame h₁.frame (fun r hr => by simp at hr; subst hr; exact c.disjW) c.fitS (by omega)]
      · rw [rd64_write64_ne (b := scr) (o := 8 * n) (o' := 8 * k) _ _ (by omega) (by omega)
          (by omega), o₂.mem]
        exact h₁.vars k (by omega)
    · rw [u₃.mem, o₂.mem]
      exact frame_write64 (N := 192) (o := 8 * n) h₁.frame (by simp) (by have := c.fitV; omega) (by omega) _

/-! ## Adding them into the hash value -/

structure UInv (st scr : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ∉ [Z0, Z1, X0, X1] → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  done : ∀ k < n, rd64 s'.mem st (8 * k) = rd64 s.mem scr (8 * k) + rd64 s.mem st (8 * k)
  todo : ∀ k, n ≤ k → k < 8 → rd64 s'.mem st (8 * k) = rd64 s.mem st (8 * k)
  frame : Frame [stR st] s.mem s'.mem

theorem update_ok {st scr : BitVec 32} {s : State} (c : Ctx st scr s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap addH)) s (UInv st scr s n) := by
  intro n hn
  have fitS := c.fitS
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega),
      fun _ _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ h₁ => ?_
    have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [addH, List.append_assoc, List.append_assoc, ← List.append_nil (Impl.Sha512.Arm.st Z0 Z1 .r0 (8 * n))]
    refine wp_ld (by decide) (by decide) (by omega) c₁.r3 (c₁.wV _ (by omega)).1
      (c₁.wV _ (by omega)).2 fun s₂ o₂ p₂ => ?_
    refine wp_ld (by decide) (by decide) (by omega) (by rw [o₂.gpr _ (by decide), c₁.r0])
      (by rw [o₂.wr]; exact (c₁.wS _ (by omega)).1) (by rw [o₂.wr]; exact (c₁.wS _ (by omega)).2)
      fun s₃ o₃ p₃ => ?_
    refine wp_add64 (by decide) (by decide) (p₂.of_only o₃ (by decide) (by decide)) p₃
      fun s₄ o₄ p₄ => ?_
    have O := (o₂.trans o₃).trans o₄
    refine wp_st (by omega) (by rw [O.gpr _ (by decide), c₁.r0]) p₄
      (by rw [O.wr]; exact (c₁.wS _ (by omega)).1) (by rw [O.wr]; exact (c₁.wS _ (by omega)).2)
      fun s₅ u₅ => WP.block_nil ⟨fun r hr => ?_, by rw [u₅.rd, O.rd, h₁.rd],
        by rw [u₅.wr, O.wr, h₁.wr], by rw [u₅.sp, O.sp, h₁.sp], fun k hk => ?_, fun k hk hk' => ?_, ?_⟩
    · rw [u₅.gpr, (O.mono (by decide)).gpr r hr, h₁.gpr r hr]
    · rw [u₅.mem, O.mem, o₂.mem]
      by_cases hkn : k = n
      · subst hkn
        rw [rd64_write64_self _ _ (by omega), h₁.todo k (by omega) (by omega),
          rd64_frame h₁.frame (fun r hr => by simp at hr; subst hr; exact c.disj.symm) c.fitV
            (by omega)]
      · rw [rd64_write64_ne (b := st) (o := 8 * n) (o' := 8 * k) _ _ (by omega) (by omega)
          (by omega)]
        exact h₁.done k (by omega)
    · rw [u₅.mem, O.mem, rd64_write64_ne (b := st) (o := 8 * n) (o' := 8 * k) _ _ (by omega)
        (by omega) (by omega)]
      exact h₁.todo k (by omega) hk'
    · rw [u₅.mem, O.mem]
      exact frame_write64 (N := 64) (o := 8 * n) h₁.frame (by simp) c.fitS (by omega) _


namespace Compress

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev stp : BitVec 32 := s₀.gpr .r0
abbrev bp : BitVec 32 := s₀.gpr .r1
abbrev nb : Nat := (s₀.gpr .r2).toNat
abbrev scp : BitVec 32 := s₀.gpr .r3
abbrev blR : Region := ⟨State.addr (bp s₀), 128 * nb s₀⟩
abbrev H₀ : HashValue := stateAt s₀.mem (State.addr (stp s₀))

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (128 * i)

/-- The address of a saved register. -/
abbrev saveAddr (d : Nat) : Addr := State.addr (scp s₀ + BitVec.ofNat 32 d)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR (stp s₀), scrR (scp s₀)]
  st_scr : (stR (stp s₀)).Disjoint (scrR (scp s₀))
  blk_st : (blR s₀).Disjoint (stR (stp s₀))
  blk_scr : (blR s₀).Disjoint (scrR (scp s₀))
  st_fits : (stp s₀).toNat + 64 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 128 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scp s₀).toNat + 224 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha512.compressArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem ctx {s : State} (h0 : s.gpr .r0 = stp s₀) (h3 : s.gpr .r3 = scp s₀) (hw : s.wr = s₀.wr) :
    Ctx (stp s₀) (scp s₀) s :=
  ⟨h0, h3, h.st_fits, h.scr_fits, h.st_scr,
    Reg64.of_mem (by rw [hw, h.wr]; simp) h.st_fits, Reg64.of_mem (by rw [hw, h.wr]; simp) h.scr_fits⟩

theorem blk_toNat {i : Nat} (hi : i < nb s₀) : (blkAddr s₀ i).toNat = (bp s₀).toNat + 128 * i := by
  have := h.blk_fits
  simp only [blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 128 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem blk_fit {i : Nat} (hi : i < nb s₀) : (blkAddr s₀ i).toNat + 128 ≤ 2 ^ 32 := by
  have := h.blk_fits; rw [h.blk_toNat hi]; omega

theorem blk_addr {i : Nat} (hi : i < nb s₀) :
    State.addr (blkAddr s₀ i) = State.addr (bp s₀) + BitVec.ofNat 64 (128 * i) :=
  addr_add (by have := h.blk_fits; omega)

theorem blk_sub {i : Nat} (hi : i < nb s₀) : Region.Sub ⟨State.addr (blkAddr s₀ i), 128⟩ (blR s₀) := by
  have := h.blk_fits
  rw [h.blk_addr hi]; exact sub_offset (by omega) (by omega)

theorem blk_rd {i : Nat} (hi : i < nb s₀) {o : Nat} (ho : o + 4 ≤ 128) :
    InRegions (s₀.rd ++ s₀.wr) (A (blkAddr s₀ i) o) 4 := by
  refine ⟨blR s₀, by simp [h.rd], ?_⟩
  have := h.blk_fit hi
  have := h.blk_fits
  have e : State.addr (bp s₀) + BitVec.ofNat 64 (128 * i) + BitVec.ofNat 64 o =
      State.addr (bp s₀) + BitVec.ofNat 64 (128 * i + o) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [A_eq (by omega), h.blk_addr hi, e]
  exact contains_offset (by omega) (by omega)

theorem blk_disj {i : Nat} (hi : i < nb s₀) :
    ∀ r ∈ [stR (stp s₀), scrR (scp s₀)], Region.Disjoint ⟨State.addr (blkAddr s₀ i), 128⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.blk_st.sub_left (h.blk_sub hi), h.blk_scr.sub_left (h.blk_sub hi)⟩

theorem saveAddr_eq {d : Nat} (hd : d < 224) :
    saveAddr s₀ d = State.addr (scp s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := h.scr_fits; omega)

theorem in_save {d : Nat} (hd : d + 4 ≤ 224) : InRegions (s₀.rd ++ s₀.wr) (saveAddr s₀ d) 4 := by
  rw [h.saveAddr_eq (by omega)]
  exact ⟨scrR (scp s₀), by simp [h.wr], contains_offset hd (by omega)⟩

theorem out_save {d : Nat} (hd : d + 4 ≤ 224) : InRegions s₀.wr (saveAddr s₀ d) 4 := by
  rw [h.saveAddr_eq (by omega)]
  exact ⟨scrR (scp s₀), by simp [h.wr], contains_offset hd (by omega)⟩

end Pre

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch buffer. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (saveAddr s₀ 192) 32 = s₀.gpr .r4 ∧ m.readW (saveAddr s₀ 196) 32 = s₀.gpr .r5 ∧
  m.readW (saveAddr s₀ 200) 32 = s₀.gpr .r6 ∧ m.readW (saveAddr s₀ 204) 32 = s₀.gpr .r7 ∧
  m.readW (saveAddr s₀ 208) 32 = s₀.gpr .r8 ∧ m.readW (saveAddr s₀ 212) 32 = s₀.gpr .r9 ∧
  m.readW (saveAddr s₀ 216) 32 = s₀.gpr .r10 ∧ m.readW (saveAddr s₀ 220) 32 = s₀.gpr .r11

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = stp s₀
  r3 : s.gpr .r3 = scp s₀
  lr : s.gpr .lr = s₀.gpr .lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR (stp s₀), scrR (scp s₀)] s₀.mem s.mem
  state : stateAt s.mem (State.addr (stp s₀)) =
    compressBlocks (H₀ s₀) s₀.mem (State.addr (bp s₀)) i
  saved : Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  r4 : s.gpr .r4 = blkAddr s₀ i
  r5 : s.gpr .r5 = BitVec.ofNat 32 (nb s₀ - i)

theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [workR (scp s₀)] m m' ∨ Frame [stR (stp s₀)] m m') : Saved s₀ m' := by
  have key : ∀ d : Nat, 192 ≤ d → d + 4 ≤ 224 →
      m'.readW (saveAddr s₀ d) 32 = m.readW (saveAddr s₀ d) 32 := by
    intro d hd hd'
    have hc : (⟨saveAddr s₀ d, 4⟩ : Region).Contains (saveAddr s₀ d) (32 / 8) :=
      Region.contains_self _ _
    have := hp.scr_fits
    rcases hf with hf | hf
    · refine hf.readW hc ?_ (by decide)
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [hp.saveAddr_eq (by omega)] at h₁
      generalize State.addr (scp s₀) = b at *
      bv_omega
    · refine hf.readW hc ?_ (by decide)
      simp only [List.mem_singleton, forall_eq]
      refine Region.Disjoint.sub_left hp.st_scr.symm fun a ha => ?_
      simp only [Region.Contains] at ha ⊢
      rw [hp.saveAddr_eq (by omega)] at ha
      generalize State.addr (scp s₀) = b at *
      bv_omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨(key 192 (by omega) (by omega)).trans h1, (key 196 (by omega) (by omega)).trans h2,
    (key 200 (by omega) (by omega)).trans h3, (key 204 (by omega) (by omega)).trans h4,
    (key 208 (by omega) (by omega)).trans h5, (key 212 (by omega) (by omega)).trans h6,
    (key 216 (by omega) (by omega)).trans h7, (key 220 (by omega) (by omega)).trans h8⟩

/-! ## One block -/

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (128 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem advance_ok {s : State} {Q : State → Prop}
    (k : ∀ s', s'.gpr .r4 = s.gpr .r4 + 128 → s'.gpr .r5 = s.gpr .r5 - 1 →
      s'.z = (s.gpr .r5 - 1 == 0) → (∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block advance) s Q := by
  unfold advance
  refine wp_add (op2_imm (by decide)) fun s₁ u₁ =>
    wp_subs (op2_imm (by decide)) fun s₂ u₂ hz => WP.block_nil ?_
  refine k s₂ ?_ ?_ ?_ (fun r h4 h5 => ?_) ?_ ?_ ?_
  · rw [u₂.other _ (by decide), u₁.gpr]
  · rw [u₂.gpr, u₁.other _ (by decide)]
  · rw [hz, u₁.other _ (by decide)]
  · rw [u₂.other _ h5, u₁.other _ h4]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have c := hp.ctx hL.r0 hL.r3 hL.wr
  have fitS := hp.st_fits
  have fitV := hp.scr_fits
  have fitB := hp.blk_fit hi
  set H := stateAt s.mem (State.addr (stp s₀)) with hH
  set M := blockAt s₀.mem (State.addr (blkAddr s₀ i)) with hMdef
  refine WP.seq (WP.mono (load_ok c 8 (Nat.le_refl _)) fun s₁ h₁ => ?_)
  have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
  have hB : BlkCtx (scp s₀) (blkAddr s₀ i) s₁ :=
    ⟨by rw [h₁.gpr _ (by decide), hL.r4], fitB,
      (hp.blk_scr.sub_left (hp.blk_sub hi)).sub_right (Region.sub_prefix (by omega)),
      fun o ho => by rw [h₁.rd, h₁.wr, hL.rd, hL.wr]; exact hp.blk_rd hi ho⟩
  have hM : Raw (blkAddr s₀ i) M s₁.mem := fun j hj => by
    rw [rd64_frame h₁.frame (fun r hr => by simp at hr; subst hr; exact hB.disj) fitB (by omega),
      rd64_frame hL.frame (hp.blk_disj hi) fitB (by omega)]
    exact raw_block fitB s₀.mem j hj
  have h0 : ∀ k (hk : k < 8), rd64 s₁.mem (scp s₀) (8 * k) = H[k] := fun k hk => by
    rw [h₁.vars k hk, stateAt_get fitS _ hk]
  refine WP.seq (WP.mono (rounds_ok c₁ hB hM h0 80 (Nat.le_refl _)) fun s₂ h₂ => ?_)
  have c₂ := c₁.of_rinv h₂
  rw [WP.block_append_iff]
  refine WP.mono (update_ok c₂ 8 (Nat.le_refl _)) fun s₃ h₃ => advance_ok fun s₄ r4₄ r5₄ z₄ g₄ m₄ rd₄ wr₄ => ?_
  -- Registers
  have g₃ : ∀ r, r ∉ temps → r ≠ .r4 → r ≠ .r5 → s₄.gpr r = s.gpr r := fun r hr h4 h5 => by
    have e₃ : ∀ r ∈ [Z0, Z1, X0, X1], r ∈ temps := by decide
    have e₁ : ∀ r ∈ [X0, X1], r ∈ temps := by decide
    rw [g₄ r h4 h5, h₃.gpr r fun h => hr (e₃ r h), h₂.gpr r hr, h₁.gpr r fun h => hr (e₁ r h)]
  have gT : ∀ r, r ∉ temps → s₃.gpr r = s.gpr r := fun r hr => by
    have e₃ : ∀ r ∈ [Z0, Z1, X0, X1], r ∈ temps := by decide
    have e₁ : ∀ r ∈ [X0, X1], r ∈ temps := by decide
    rw [h₃.gpr r fun h => hr (e₃ r h), h₂.gpr r hr, h₁.gpr r fun h => hr (e₁ r h)]
  have hrd : s₄.rd = s₀.rd := by rw [rd₄, h₃.rd, h₂.rd, h₁.rd, hL.rd]
  have hwr : s₄.wr = s₀.wr := by rw [wr₄, h₃.wr, h₂.wr, h₁.wr, hL.wr]
  -- Memory
  have hframe : Frame [stR (stp s₀), scrR (scp s₀)] s₀.mem s₄.mem := by
    have sw : ∀ r ∈ [workR (scp s₀)], ∃ r' ∈ [stR (stp s₀), scrR (scp s₀)], Region.Sub r r' :=
      fun r hr => ⟨scrR (scp s₀), by simp, by simp at hr; subst hr; exact Region.sub_prefix (by omega)⟩
    rw [m₄]
    exact ((hL.frame.trans (h₁.frame.sub sw)).trans (h₂.frame.sub sw)).trans (h₃.frame.mono (by simp))
  have hstate : stateAt s₄.mem (State.addr (stp s₀)) = compress H M := by
    rw [m₄]
    refine stateAt_ext fitS fun k hk => ?_
    have hd₁ : ∀ r ∈ [workR (scp s₀)], Region.Disjoint (stR (stp s₀)) r := fun r hr => by
      simp at hr; subst hr; exact c.disjW
    rw [h₃.done k hk, show 8 * k = vOff 80 k by simp only [vOff]; omega, h₂.vars k hk,
      show vOff 80 k = 8 * k by simp only [vOff]; omega, h₂.hash k hk,
      rd64_frame h₁.frame hd₁ fitS (by omega), ← stateAt_get fitS _ hk]
    simp only [Spec.Sha512.compress, Vector.getElem_zipWith]
    rfl
  have hsaved : Saved s₀ s₄.mem := by
    rw [m₄]
    refine saved_frame hp ?_ (.inr h₃.frame)
    refine saved_frame hp ?_ (.inl h₂.frame)
    exact saved_frame hp hL.saved (.inl h₁.frame)
  have hnb : nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  have hr5 : s₃.gpr .r5 - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [gT .r5 (by decide), hL.r5]
    bv_omega
  have hcommon : Common s₀ (i + 1) s₄ := by
    refine ⟨by rw [g₃ _ (by decide) (by decide) (by decide), hL.r0],
      by rw [g₃ _ (by decide) (by decide) (by decide), hL.r3],
      by rw [g₃ _ (by decide) (by decide) (by decide), hL.lr], hrd, hwr, hframe, ?_, hsaved⟩
    rw [hstate, compressBlocks_succ, ← hL.state, hMdef, hp.blk_addr hi]
  have hev : eval .ne s₄ = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    rw [eval_ne, z₄, hr5]
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon with r4 := ?_, r5 := ?_ }⟩
    · rw [r4₄, gT .r4 (by decide), hL.r4]
      simp only [blkAddr]
      bv_omega
    · rw [r5₄, hr5]

/-! ## Prologue and epilogue -/

theorem save_eq : save = [
    .str .r4 .r3 192, .str .r5 .r3 196, .str .r6 .r3 200, .str .r7 .r3 204, .str .r8 .r3 208,
    .str .r9 .r3 212, .str .r10 .r3 216, .str .r11 .r3 220] := rfl

theorem restore_eq : restore = [
    .ldr .r4 .r3 192, .ldr .r5 .r3 196, .ldr .r6 .r3 200, .ldr .r7 .r3 204, .ldr .r8 .r3 208,
    .ldr .r9 .r3 212, .ldr .r10 .r3 216, .ldr .r11 .r3 220] := rfl

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem :=
  (((((((s₀.mem.writeW (saveAddr s₀ 192) (s₀.gpr .r4)).writeW (saveAddr s₀ 196) (s₀.gpr .r5)).writeW
    (saveAddr s₀ 200) (s₀.gpr .r6)).writeW (saveAddr s₀ 204) (s₀.gpr .r7)).writeW
    (saveAddr s₀ 208) (s₀.gpr .r8)).writeW (saveAddr s₀ 212) (s₀.gpr .r9)).writeW
    (saveAddr s₀ 216) (s₀.gpr .r10)).writeW (saveAddr s₀ 220) (s₀.gpr .r11)

set_option simprocs false in
theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block save) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ := by
  have o0 := hp.out_save (d := 192) (by omega); have o1 := hp.out_save (d := 196) (by omega)
  have o2 := hp.out_save (d := 200) (by omega); have o3 := hp.out_save (d := 204) (by omega)
  have o4 := hp.out_save (d := 208) (by omega); have o5 := hp.out_save (d := 212) (by omega)
  have o6 := hp.out_save (d := 216) (by omega); have o7 := hp.out_save (d := 220) (by omega)
  apply WP.of_runBlock
  rw [save_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, State.store32,
    o0, o1, o2, o3, o4, o5, o6, o7, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_⟩ <;> trivial

theorem save_sep {s₀ : State} (hp : Pre s₀) {d e : Nat} (hd : d + 4 ≤ 224) (he : e + 4 ≤ 224)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (saveAddr s₀ d) 4 (saveAddr s₀ e) 4 := by
  intro x hx hy
  rw [hp.saveAddr_eq (by omega)] at hx
  rw [hp.saveAddr_eq (by omega)] at hy
  generalize State.addr (scp s₀) = a at *
  bv_omega

theorem readW_writeW_save {s₀ : State} (hp : Pre s₀) (m : Mem) (v : BitVec 32) {d e : Nat}
    (hd : d + 4 ≤ 224) (he : e + 4 ≤ 224) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (saveAddr s₀ e) v).readW (saveAddr s₀ d) 32 = m.readW (saveAddr s₀ d) 32 :=
  Mem.readW_writeW_sep (save_sep hp hd he h) (by decide)

theorem saveMem_saved {s₀ : State} (hp : Pre s₀) : Saved s₀ (saveMem s₀) := by
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_save hp]

theorem saveMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scrR (scp s₀)] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 4 ≤ 224 → (scrR (scp s₀)).Contains (saveAddr s₀ d) (32 / 8) :=
    fun d hd => by rw [hp.saveAddr_eq (by omega)]; exact contains_offset hd (by omega)
  simp only [saveMem]
  have m := List.mem_singleton_self (scrR (scp s₀))
  exact ((((((((Frame.refl _ _).writeW m _ (c 192 (by omega))).writeW m _ (c 196 (by omega))).writeW
    m _ (c 200 (by omega))).writeW m _ (c 204 (by omega))).writeW m _ (c 208 (by omega))).writeW
    m _ (c 212 (by omega))).writeW m _ (c 216 (by omega))).writeW m _ (c 220 (by omega))

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (h0 : s₁.gpr .r0 = s₀.gpr .r0)
    (h3 : s₁.gpr .r3 = s₀.gpr .r3) (hlr : s₁.gpr .lr = s₀.gpr .lr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) : Common s₀ 0 s₁ := by
  refine ⟨h0, h3, hlr, hrd, hwr, ?_, ?_, by rw [hm]; exact saveMem_saved hp⟩
  · rw [hm]; exact (saveMem_frame hp).mono (by simp)
  · rw [hm]
    have hd : ∀ r ∈ [scrR (scp s₀)], Region.Disjoint (stR (stp s₀)) r := fun r hr => by
      simp at hr; subst hr; exact hp.st_scr
    refine stateAt_ext hp.st_fits fun k hk => ?_
    rw [rd64_frame (saveMem_frame hp) hd hp.st_fits (by omega), ← stateAt_get hp.st_fits _ hk]
    simp [compressBlocks]

set_option simprocs false in
theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha512.compressArm.post s₀ s' := by
  have i0 := hp.in_save (d := 192) (by omega); have i1 := hp.in_save (d := 196) (by omega)
  have i2 := hp.in_save (d := 200) (by omega); have i3 := hp.in_save (d := 204) (by omega)
  have i4 := hp.in_save (d := 208) (by omega); have i5 := hp.in_save (d := 212) (by omega)
  have i6 := hp.in_save (d := 216) (by omega); have i7 := hp.in_save (d := 220) (by omega)
  rw [← hc.rd, ← hc.wr] at i0 i1 i2 i3 i4 i5 i6 i7
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := hc.saved
  have hstate := hc.state
  have hr3 := hc.r3
  have hlr := hc.lr
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, State.setReg, State.load32, hr3,
    i0, i1, i2, i3, i4, i5, i6, i7, ite_true, ite_false, g0, g1, g2, g3, g4, g5, g6, g7,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, hstate⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [hlr]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Sha512.Arm.compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha512.compressArm.post s₀ s' := by
  unfold Impl.Sha512.Arm.compress
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok hp) fun s₁ ⟨hg, hrd, hwr, hm⟩ => ?_
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_cmp (op2_imm (by decide)) fun s₄ u₄ hz => WP.block_nil ?_
  have g : ∀ r, r ≠ .r4 → r ≠ .r5 → s₄.gpr r = s₀.gpr r := fun r h4 h5 => by
    rw [u₄.gpr, u₃.other _ h5, u₂.other _ h4, hg]
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₅ hc => restore_ok hp hc)
  have hc₀ := common_zero hp (g _ (by decide) (by decide)) (g _ (by decide) (by decide))
    (g _ (by decide) (by decide)) (by rw [u₄.rd, u₃.rd, u₂.rd, hrd]) (by rw [u₄.wr, u₃.wr, u₂.wr, hwr])
    (by rw [u₄.mem, u₃.mem, u₂.mem, hm])
  have hr2 : s₃.gpr .r2 = s₀.gpr .r2 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), hg]
  rw [hr2] at hz
  refine WP.ite (s₀.gpr .r2 - 0 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₄ :=
      { hc₀ with
        r4 := by rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, hg]; simp [blkAddr]
        r5 := by rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), hg]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₄ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x3000, 224⟩]

theorem compress_verified :
    Verified Arm.target Impl.Sha512.Arm.compress Proof.Sha512.compressArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ?_
      (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, satState, State.addr] at h₁ h₂
      bv_omega

end Compress

end VG.Proof.Sha512.Arm
