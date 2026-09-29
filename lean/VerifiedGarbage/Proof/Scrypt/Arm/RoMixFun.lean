import VerifiedGarbage.Proof.Scrypt.Arm.RoMixLoops
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Set

/-!
# scryptROMix on 32-bit ARM: correctness

Untrusted: everything here is checked by Lean. The prologue loads the
scratch pointer from the stack, saves our caller's registers and our return
address in `scratch` and computes `N`; step 2 and step 3 are loops whose
bodies call `vg_scrypt_blockmix` (through `BlockMixSpec`), with our own
stack argument as its scratch space; the epilogue restores the registers.
As on AArch64 (`Proof/Scrypt/AArch64/RoMixFun.lean`).
-/

namespace VG.Proof.Scrypt.Arm.RoMix

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Spec.Scrypt (bytesAt blockMix roMix)
open VG.Proof.Sha256.Stream (writeBytes)
open VG.Proof.Sha256.Arm.Stream (Upd Mupd wp_mov wp_add wp_sub wp_and wp_subs wp_ldr wp_str wp_ldrSp
  op2_reg op2_imm op2_lsl op2_lsr saveMem saveList_ok readW_writeW_save)
open VG.Proof.Scrypt (vList vList_getD roMix_eq roMixIndices_eq mixLoop_succ_fst mixLoop_succ_snd)
open VG.Proof.Scrypt.X86_64.BlockMix (add_ofNat contains_off sub_off InRegions.of_mem
  InRegions.right frame_bytesAt bytesAt_writeBytes_self bytesAt_writeBytes_sep bytesAt_length
  xorBytes_length)

/-! ## Arithmetic -/

theorem dbl32 (x : BitVec 32) : x + x = BitVec.ofNat 32 (2 * x.toNat) := by
  conv_lhs => rw [ofNat_toNat32 x]
  rw [← BitVec.ofNat_add, Nat.two_mul]

theorem stackArgAddr_eq {s s₀ : State} (h : s.sp = s₀.sp) : stackArgAddr s 0 = stackArgAddr s₀ 0 := by
  rw [stackArgAddr, stackArgAddr, h]

/-! ## The prologue -/

theorem prologue_eq : rmPrologue =
    .ldrSp .r12 0 :: (rmSaved.map (fun p => Instr.str p.1 .r12 p.2) ++
      [.mov .r4 (.reg .r0), .mov .r5 (.reg .r2), .mov .r6 (.reg .r12),
       .mov .r7 (.shifted .r1 .lsl 7), .mov .r0 (.reg .r1), .mov .r1 (.imm 1),
       .dp .add .r2 .r3 (.reg .r3)]) := rfl

set_option simprocs false in
theorem saveMem_saved (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ p ∈ rmSaved, (saveMem m B g rmSaved).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1 := by
  intro p hp
  simp only [rmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [rmSaved, saveMem, Mem.readW_writeW_self32,
    readW_writeW_save]

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, (∀ r, r ≠ .r12 → s₁.gpr r = s₀.gpr r) → s₁.gpr .r12 = sc s₀ → s₁.rd = s₀.rd →
      s₁.wr = s₀.wr → s₁.sp = s₀.sp → Frame [scR s₀] s₀.mem s₁.mem → Saved s₀ s₁.mem →
      WP isa (.block rest) s₁ Q) :
    WP isa (.block (.ldrSp .r12 0 :: (rmSaved.map (fun p => Instr.str p.1 .r12 p.2) ++ rest)))
      s₀ Q := by
  have hs := hp.s_nw
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl ?_ fun s₁ u₁ => ?_
  · rw [hp.rd]
    refine InRegions.of_mem (R := argR s₀) (by simp) ?_
    show (stackArgAddr s₀ 0 - stackArgAddr s₀ 0).toNat + 4 ≤ 8
    rw [BitVec.sub_self, BitVec.toNat_zero]; decide
  have e12 : s₁.gpr .r12 = sc s₀ := u₁.gpr
  refine saveList_ok rmSaved s₁ Q (fun p hp' => ?_) fun s₂ g rd wr sp m => ?_
  · obtain ⟨h1, h2, -⟩ := saved_offs p hp'
    rw [e12, u₁.wr, hp.wr]
    exact ⟨by omega, by omega, InRegions.of_mem (by simp) (in_s s₀ (by omega))⟩
  refine k s₂ (fun r hr => by rw [g, u₁.other r hr]) (by rw [g, e12]) (by rw [rd, u₁.rd])
    (by rw [wr, u₁.wr]) (by rw [sp, u₁.sp]) ?_ ?_
  · rw [m, e12, u₁.mem]
    exact saveMem_frame' _ _ _ fun p hp' => in_s s₀ (by have := saved_offs p hp'; omega)
  · intro p hp'
    rw [m, e12, saveMem_saved, u₁.other _ (saved_offs p hp').2.2]
    exact hp'

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  r4 : s.gpr .r4 = bP s₀
  r5 : s.gpr .r5 = vP s₀
  r6 : s.gpr .r6 = sc s₀
  r7 : s.gpr .r7 = BitVec.ofNat 32 (128 * rr s₀)
  r0 : s.gpr .r0 = BitVec.ofNat 32 (rr s₀)
  r1 : s.gpr .r1 = 1
  r2 : s.gpr .r2 = BitVec.ofNat 32 (2 * vl s₀)

theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : ∀ r, r ≠ .r12 → s₁.gpr r = s₀.gpr r)
    (g12 : s₁.gpr .r12 = sc s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp)
    (hf : Frame [scR s₀] s₀.mem s₁.mem) (hsv : Saved s₀ s₁.mem) :
    WP isa (.block [.mov .r4 (.reg .r0), .mov .r5 (.reg .r2), .mov .r6 (.reg .r12),
       .mov .r7 (.shifted .r1 .lsl 7), .mov .r0 (.reg .r1), .mov .r1 (.imm 1),
       .dp .add .r2 .r3 (.reg .r3)]) s₁ (P1 s₀) := by
  have lt := r_lt hp
  have hr : rr s₀ = (s₀.gpr .r1).toNat := rfl
  refine wp_mov (op2_reg _ _) fun a ua => wp_mov (op2_reg _ _) fun b ub =>
    wp_mov (op2_reg _ _) fun c uc => wp_mov (op2_lsl (by decide)) fun d ud =>
    wp_mov (op2_reg _ _) fun e ue => wp_mov (op2_imm (by decide)) fun f uf =>
    wp_add (op2_reg _ _) fun h uh => WP.block_nil ?_
  have hm : h.mem = s₁.mem := by rw [uh.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
  have x1 : d.gpr .r1 = s₀.gpr .r1 := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g _ (by decide)]
  refine ⟨?_, ?_, ?_, by rw [hm]; exact hf, by rw [hm]; exact hsv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [uh.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd, hrd]
  · rw [uh.wr, uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr, hwr]
  · rw [uh.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp, hsp]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.gpr,
      g _ (by decide)]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.gpr, ua.other _ (by decide),
      g _ (by decide)]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.gpr, ub.other _ (by decide), ua.other _ (by decide), g12]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide), ud.gpr,
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g _ (by decide),
      shl32 (by omega)]
    congr 1; omega
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.gpr, x1]
    exact ofNat_toNat32 _
  · rw [uh.other _ (by decide), uf.gpr]
  · rw [uh.gpr, uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g _ (by decide),
      dbl32]

/-! ## Computing `N` -/

/-- After the loop computing `N`. -/
structure N1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  r4 : s.gpr .r4 = bP s₀
  r5 : s.gpr .r5 = vP s₀
  r6 : s.gpr .r6 = sc s₀
  r7 : s.gpr .r7 = BitVec.ofNat 32 (128 * rr s₀)
  r1 : s.gpr .r1 = BitVec.ofNat 32 (2 * NN s₀)

theorem nloop_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : P1 s₀ s) : WP isa nLoop s (N1 s₀) := by
  obtain ⟨e, he⟩ := hp.pow
  have lt := v_lt hp
  have e2 : rr s₀ * 2 ^ (e + 1) = 2 * vl s₀ := by
    rw [hp.vl_eq, he, Nat.pow_succ, Nat.mul_comm (2 ^ e) 2, Nat.mul_left_comm]
  have hNe : 2 * vl s₀ < 2 ^ 32 := by have := vl_mul hp; omega
  refine WP.mono (nLoop_ok (r := rr s₀) (e := e) hp.pos (by omega) h.r0 h.r1
    (by rw [h.r2, e2])) fun t ⟨rd, wr, sp, mem, oth, r1⟩ => ?_
  exact ⟨by rw [rd, h.rd], by rw [wr, h.wr], by rw [sp, h.sp], by rw [mem]; exact h.frame,
    by rw [mem]; exact h.saved,
    by rw [oth _ (by decide) (by decide), h.r4], by rw [oth _ (by decide) (by decide), h.r5],
    by rw [oth _ (by decide) (by decide), h.r6], by rw [oth _ (by decide) (by decide), h.r7],
    by rw [r1, he, Nat.pow_succ, Nat.mul_comm]⟩

/-! ## Step 2 -/

/-- After `i` iterations of step 2. -/
structure Inv2 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = bP s₀
  r5 : s.gpr .r5 = vP s₀
  r6 : s.gpr .r6 = sc s₀
  r7 : s.gpr .r7 = BitVec.ofNat 32 (128 * rr s₀)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (NN s₀ - i)
  r9 : s.gpr .r9 = vAt32 s₀ i
  frame : Frame [bR s₀, vR s₀, scR s₀] s₀.mem s.mem
  kept : Kept s₀ s.mem
  x : bytesAt s.mem (bA s₀) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀)
  done : ∀ k < i, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)

set_option simprocs false in
theorem setupMem_kept (s₀ : State) {m : Mem} (h : Saved s₀ m) :
    Kept s₀ (m.writeW (scA s₀ + BitVec.ofNat 64 156) (BitVec.ofNat 32 (NN s₀))) := by
  refine ⟨fun p hp => ?_, Mem.readW_writeW_self32 _ _ _⟩
  have ho := saved_offs p hp
  rw [readW_writeW_save _ _ _ (by omega) (by decide) (by omega)]
  exact h p hp

theorem setup2_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : N1 s₀ s) :
    WP isa (.block rmSetup) s (Inv2 s₀ 0) := by
  have lt := v_lt hp
  have n1 := NN_pos hp
  have hs := hp.s_nw
  have : 2 * NN s₀ < 2 ^ 32 := by
    have : 2 * NN s₀ ≤ 128 * rr s₀ * NN s₀ := by
      have := hp.pos
      have : 2 ≤ 128 * rr s₀ := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  unfold rmSetup
  refine wp_mov (op2_lsr (by decide)) fun t1 u1 => ?_
  have hd : t1.gpr .r1 = BitVec.ofNat 32 (NN s₀) := by
    rw [u1.gpr, h.r1, shr_ofNat32 _ (by omega), Nat.pow_one, Nat.mul_div_cancel_left _ (by decide)]
  refine wp_str (a := scA s₀ + BitVec.ofNat 64 156) (by decide)
    (by rw [u1.other _ (by decide), h.r6, addr_add (by omega)])
    (by rw [u1.wr, h.wr, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by omega)))
    fun t2 u2 => wp_mov (op2_reg _ _) fun t3 u3 => wp_mov (op2_reg _ _) fun t4 u4 => WP.block_nil ?_
  have g : ∀ r, r ≠ .r1 → r ≠ .r8 → r ≠ .r9 → t4.gpr r = s.gpr r := fun r b c d => by
    rw [u4.other _ d, u3.other _ c, u2.gpr, u1.other _ b]
  have hm : t4.mem = s.mem.writeW (scA s₀ + BitVec.ofNat 64 156) (BitVec.ofNat 32 (NN s₀)) := by
    rw [u4.mem, u3.mem, u2.mem, hd, u1.mem]
  have fr : Frame [scR s₀] s₀.mem t4.mem := by
    rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (in_s s₀ (by omega))
  refine ⟨Nat.zero_le _, by rw [u4.rd, u3.rd, u2.rd, u1.rd, h.rd],
    by rw [u4.wr, u3.wr, u2.wr, u1.wr, h.wr], by rw [u4.sp, u3.sp, u2.sp, u1.sp, h.sp],
    by rw [g _ (by decide) (by decide) (by decide), h.r4],
    by rw [g _ (by decide) (by decide) (by decide), h.r5],
    by rw [g _ (by decide) (by decide) (by decide), h.r6],
    by rw [g _ (by decide) (by decide) (by decide), h.r7], ?_, ?_,
    fr.mono (by simp), by rw [hm]; exact setupMem_kept s₀ h.saved, ?_,
    fun k hk => absurd hk (by omega)⟩
  · rw [u4.other _ (by decide), u3.gpr, u2.gpr, hd, Nat.sub_zero]
  · rw [u4.gpr, u3.other _ (by decide), u2.gpr, u1.other _ (by decide), h.r5]
    simp
  · refine frame_bytesAt fr (fun r hr => ?_) (by have := r_lt hp; omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub' (s₀ := s₀))

/-! ## A call of `vg_scrypt_blockmix` into `b` -/

/-- The instructions before the call, after `r0` is set. -/
abbrev bmTail : List Instr := [.mov .r1 (.shifted .r7 .lsr 7), .mov .r2 (.reg .r4), .mov .r3 (.reg .r1)]

theorem blockMixTo_eq (c : Prog isa) (src : List Instr) :
    blockMixTo c src = .seq (.block (src ++ bmTail)) (.call "vg_scrypt_blockmix" c) := rfl

theorem b_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (bA s₀) (128 * rr s₀) := by
  rw [hp.wr]
  refine InRegions.of_mem (R := bR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem w_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (scA s₀) 128 := by
  rw [hp.wr]
  refine InRegions.of_mem (R := scR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem arg_in {s₀ : State} (hp : Pre s₀) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 4 := by
  rw [hp.rd]
  refine InRegions.of_mem (R := argR s₀) (by simp) ?_
  show (stackArgAddr s₀ 0 - stackArgAddr s₀ 0).toNat + 4 ≤ 8
  rw [BitVec.sub_self, BitVec.toNat_zero]; decide

theorem arg4_sub (s₀ : State) : Region.Sub ⟨stackArgAddr s₀ 0, 4⟩ (argR s₀) :=
  Region.sub_prefix (by decide)

/-- The registers our loops keep are not the call's arguments. -/
theorem pres_ne : ∀ r ∈ preserved, r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 := by decide

/-- A block that may be the source of a call of `vg_scrypt_blockmix` into `b`. -/
structure SrcOK (s₀ : State) (A : BitVec 32) : Prop where
  b : Region.Disjoint ⟨State.addr A, 128 * rr s₀⟩ ⟨bA s₀, 128 * rr s₀⟩
  w : Region.Disjoint ⟨State.addr A, 128 * rr s₀⟩ ⟨scA s₀, 128⟩
  nw : A.toNat + 128 * rr s₀ ≤ 2 ^ 32
  inr : InRegions (s₀.rd ++ s₀.wr) (State.addr A) (128 * rr s₀)

/-- Making the call with the arguments set: its precondition. -/
theorem bm_call {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    {A : BitVec 32} (hA : SrcOK s₀ A) (h0 : s.gpr .r0 = A)
    (h1 : s.gpr .r1 = BitVec.ofNat 32 (rr s₀)) (h2 : s.gpr .r2 = bP s₀)
    (h3 : s.gpr .r3 = BitVec.ofNat 32 (rr s₀)) (hsp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : Frame [bR s₀, vR s₀, scR s₀] s₀.mem s.mem) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      Frame [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩] s.mem s'.mem →
      bytesAt s'.mem (bA s₀) (128 * rr s₀) =
        blockMix (rr s₀) (bytesAt s.mem (State.addr A) (128 * rr s₀)) → Q s') :
    WP isa (.call "vg_scrypt_blockmix" c) s Q := by
  have lt := r_lt hp
  have ea := stackArgAddr_eq hsp
  exact hS s A (bP s₀) (sc s₀) (rr s₀) h0 h1 h2 h3 (arg_keep hp hm hsp rfl) hp.pos lt
    ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hA.b hA.w
    (by rw [ea]; exact (hp.a_b.sub_left (arg4_sub s₀)).sub_right (b_sub' (s₀ := s₀)))
    (by rw [ea]; exact (hp.a_s.sub_left (arg4_sub s₀)).sub_right (w_sub (s₀ := s₀)))
    hA.nw (by have := hp.b_nw; omega) (by have := hp.s_nw; omega)
    (by rw [hsp]; have := hp.sp_nw; omega)
    (by rw [hrd, hwr]; exact hA.inr) (by rw [ea, hrd, hwr]; exact arg_in hp)
    (by rw [hwr]; exact b_in hp) (by rw [hwr]; exact w_in hp) Q hQ

/-- Setting up and making the call, from `r0 = A`. -/
theorem bm_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    {A : BitVec 32} (hA : SrcOK s₀ A) (h0 : s.gpr .r0 = A) (h4 : s.gpr .r4 = bP s₀)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 (128 * rr s₀)) (hsp : s.sp = s₀.sp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hm : Frame [bR s₀, vR s₀, scR s₀] s₀.mem s.mem)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      Frame [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩] s.mem s'.mem →
      bytesAt s'.mem (bA s₀) (128 * rr s₀) =
        blockMix (rr s₀) (bytesAt s.mem (State.addr A) (128 * rr s₀)) → Q s') :
    WP isa (.block bmTail) s fun s' => WP isa (.call "vg_scrypt_blockmix" c) s' Q := by
  have lt := r_lt hp
  refine wp_mov (op2_lsr (by decide)) fun a ua => wp_mov (op2_reg _ _) fun b ub =>
    wp_mov (op2_reg _ _) fun d ud => WP.block_nil ?_
  have k : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → d.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have h1 : a.gpr .r1 = BitVec.ofNat 32 (rr s₀) := by
    rw [ua.gpr, h7, shr_ofNat32 _ lt]; congr 1; omega
  have em : d.mem = s.mem := by rw [ud.mem, ub.mem, ua.mem]
  refine bm_call hS hp hA (by rw [k _ (by decide) (by decide) (by decide), h0])
    (by rw [ud.other _ (by decide), ub.other _ (by decide), h1])
    (by rw [ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h4])
    (by rw [ud.gpr, ub.other _ (by decide), h1]) (by rw [ud.sp, ub.sp, ua.sp, hsp])
    (by rw [ud.rd, ub.rd, ua.rd, hrd]) (by rw [ud.wr, ub.wr, ua.wr, hwr]) (by rw [em]; exact hm)
    fun s' rd' wr' sp' cs' f' b' => hQ s' (by rw [rd', ud.rd, ub.rd, ua.rd])
      (by rw [wr', ud.wr, ub.wr, ua.wr]) (by rw [sp', ud.sp, ub.sp, ua.sp])
      (fun r hr hlr => by
        obtain ⟨-, n1, n2, n3⟩ := pres_ne r hr
        rw [cs' r hr hlr, k r n1 n2 n3])
      (by rw [em] at f'; exact f') (by rw [b', em])

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem vAt_in {i : Nat} (hi : i < NN s₀) : InRegions s₀.wr (vAt s₀ i) (128 * rr s₀) := by
  rw [hp.wr]
  have e := vl_mul hp
  have := v_le hi
  have lt := v_lt hp
  exact InRegions.of_mem (R := vR s₀) (by simp) (contains_off (by rw [e]; omega) (by omega))

/-- `V[i]` and the parts of `scratch` we use. -/
theorem vAt_b {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (bR s₀) :=
  hp.b_v.symm.sub_left (vAt_sub hp hi)
theorem vAt_s {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (scR s₀) :=
  hp.v_s.sub_left (vAt_sub hp hi)

omit hp in
/-- The frame of a call writing `b`, from the one we keep. -/
theorem call_frame {m m' : Mem} (hf : Frame [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩] m m') :
    Frame [bR s₀, vR s₀, scR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨bR s₀, by simp, b_sub'⟩
    · exact ⟨scR s₀, by simp, w_sub⟩

/-- What a call writing `b` keeps: `V[k]`. -/
theorem call_keeps_v {m m' : Mem} (hf : Frame [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩] m m')
    {k : Nat} (hk : k < NN s₀) :
    bytesAt m' (vAt s₀ k) (128 * rr s₀) = bytesAt m (vAt s₀ k) (128 * rr s₀) := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (vAt_b hp hk).sub_right b_sub'
  · exact (vAt_s hp hk).sub_right w_sub

theorem call_kept {m m' : Mem} (hf : Frame [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩] m m')
    (h : Kept s₀ m) : Kept s₀ m' :=
  h.frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (keep_b hp).sub_right b_sub'
    · exact keep_w

theorem srcOK_v {i : Nat} (hi : i < NN s₀) : SrcOK s₀ (vAt32 s₀ i) := by
  have e := vAt_addr hp hi
  exact ⟨by rw [e]; exact (vAt_b hp hi).sub_right b_sub', by rw [e]; exact (vAt_s hp hi).sub_right w_sub,
    vAt_nw hp hi, by rw [e]; exact InRegions.right (vAt_in hp hi)⟩

theorem t_b : Region.Disjoint ⟨tP s₀, 128 * rr s₀⟩ ⟨bA s₀, 128 * rr s₀⟩ :=
  (hp.b_s.symm.sub_left (t_sub hp)).sub_right b_sub'

theorem t_in : InRegions s₀.wr (tP s₀) (128 * rr s₀) := by
  have := hp.s_nw
  rw [hp.wr]
  exact InRegions.of_mem (R := scR s₀) (by simp) (contains_off (by omega) (by omega))

theorem srcOK_t : SrcOK s₀ (tP32 s₀) := by
  have e := t_addr hp
  exact ⟨by rw [e]; exact t_b hp, by rw [e]; exact t_w hp, t_nw hp,
    by rw [e]; exact InRegions.right (t_in hp)⟩

/-- The memory after iteration `i` of step 2. -/
theorem mem2_ok {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv2 s₀ i s) {m₃ : Mem}
    (f₃ : Frame [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩]
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))) m₃)
    (b₃ : bytesAt m₃ (bA s₀) (128 * rr s₀) = blockMix (rr s₀)
      (bytesAt (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))) (vAt s₀ i)
        (128 * rr s₀))) :
    Frame [bR s₀, vR s₀, scR s₀] s₀.mem m₃ ∧ Kept s₀ m₃ ∧
    bytesAt m₃ (bA s₀) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) (i + 1) (B s₀) ∧
    ∀ k < i + 1, bytesAt m₃ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀) := by
  have lt := r_lt hp
  have hl : (bytesAt s.mem (bA s₀) (128 * rr s₀)).length = 128 * rr s₀ := bytesAt_length _ _ _
  have hself : bytesAt (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))) (vAt s₀ i)
      (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀) := by
    have := bytesAt_writeBytes_self s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))
      (by rw [hl]; omega)
    rw [hl] at this
    rw [this, h.x]
  have f₂ : Frame [⟨vAt s₀ i, 128 * rr s₀⟩] s.mem
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame [bR s₀, vR s₀, scR s₀] s.mem
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨vR s₀, by simp, vAt_sub hp hi⟩
  refine ⟨(h.frame.trans f₂').trans (call_frame f₃), call_kept hp f₃ (h.kept.frame f₂ fun r hr => ?_),
    by rw [b₃, hself]; rfl, fun k hk => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact (keep_v hp).sub_right (vAt_sub hp hi)
  · rw [call_keeps_v hp f₃ (by omega)]
    by_cases hki : k = i
    · subst hki; exact hself
    · rw [bytesAt_writeBytes_sep _ _ (by rw [hl]; exact vAt_disj hp (by omega) hi hki) (by omega)]
      exact h.done k (by omega)

end

theorem vAt_succ (s₀ : State) (i : Nat) :
    vAt32 s₀ i + BitVec.ofNat 32 (128 * rr s₀) = vAt32 s₀ (i + 1) := by
  show _ = vP s₀ + BitVec.ofNat 32 (128 * rr s₀ * (i + 1))
  rw [add32, Nat.mul_succ]

theorem b_word {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 32 * rr s₀) :
    InRegions (s₀.rd ++ s₀.wr) (bA s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
  have := r_lt hp
  rw [hp.rd, hp.wr]
  exact InRegions.of_mem (R := bR s₀) (by simp) (contains_off (by omega) (by omega))

theorem v_word {s₀ : State} (hp : Pre s₀) {i k : Nat} (hi : i < NN s₀) (hk : k < 32 * rr s₀) :
    InRegions s₀.wr (State.addr (vAt32 s₀ i) + BitVec.ofNat 64 (4 * k)) 4 := by
  rw [hp.wr, vAt_addr hp hi]
  have e := vl_mul hp
  have := v_le hi
  have lt := v_lt hp
  show InRegions _ (vA s₀ + BitVec.ofNat 64 (128 * rr s₀ * i) + BitVec.ofNat 64 (4 * k)) 4
  rw [add_ofNat]
  exact InRegions.of_mem (R := vR s₀) (by simp) (contains_off (by rw [e]; omega) (by omega))

theorem t_word {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 32 * rr s₀) :
    InRegions s₀.wr (State.addr (tP32 s₀) + BitVec.ofNat 64 (4 * k)) 4 := by
  have := hp.s_nw
  rw [hp.wr, t_addr hp, add_ofNat]
  exact InRegions.of_mem (R := scR s₀) (by simp) (contains_off (by omega) (by omega))

theorem sh2 {s₀ : State} (hp : Pre s₀) :
    BitVec.ofNat 32 (128 * rr s₀) >>> 2 = BitVec.ofNat 32 (32 * rr s₀) := by
  rw [shr_ofNat32 _ (r_lt hp)]; congr 1; omega

/-- One iteration of step 2. -/
theorem step2_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv2 s₀ i s) :
    WP isa (step2 c) s fun s' => Inv2 s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = NN s₀) := by
  have lt := r_lt hp
  have pos := hp.pos
  have hN := NN_lt hp
  have hb := hp.b_nw
  unfold step2
  refine WP.seq (wp_mov (op2_reg _ _) fun a ua => wp_mov (op2_reg _ _) fun b ub =>
    wp_mov (op2_lsr (by decide)) fun d ud => WP.block_nil ?_)
  have ke : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → d.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have erd : d.rd = s₀.rd := by rw [ud.rd, ub.rd, ua.rd, h.rd]
  have ewr : d.wr = s₀.wr := by rw [ud.wr, ub.wr, ua.wr, h.wr]
  have esp : d.sp = s₀.sp := by rw [ud.sp, ub.sp, ua.sp, h.sp]
  have hme : d.mem = s.mem := by rw [ud.mem, ub.mem, ua.mem]
  have e4 : 4 * (32 * rr s₀) = 128 * rr s₀ := by omega
  refine WP.seq (WP.mono (copyLoop_ok (src := bP s₀) (dst := vAt32 s₀ i) (n := 32 * rr s₀)
    (by omega) (by omega) (by omega) (by rw [e4]; exact vAt_nw hp hi)
    (by rw [ud.other _ (by decide), ub.other _ (by decide), ua.gpr, h.r4])
    (by rw [ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.r9])
    (by rw [ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h.r7, sh2 hp])
    (fun k hk => by rw [erd, ewr]; exact b_word hp hk)
    (fun k hk => by rw [ewr]; exact v_word hp hi hk)
    (by rw [e4, vAt_addr hp hi]; exact (vAt_b hp hi).symm.sub_left b_sub'))
    fun t ⟨rdt, wrt, spt, gt, mt⟩ => ?_)
  rw [hme, e4, vAt_addr hp hi] at mt
  have kt : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h0, h1, h2, h3⟩ := pres_ne r hr
    rw [gt r h0 h1 h2 h3, ke r h0 h1 h2]
  have ft : Frame [bR s₀, vR s₀, scR s₀] s₀.mem t.mem := by
    rw [mt]
    refine h.frame.trans (Proof.Sha256.Stream.writeBytes_frame (R := ⟨vAt s₀ i, 128 * rr s₀⟩)
      _ _ _ ?_ |>.sub fun r hr => ?_)
    · rw [bytesAt_length]; exact Region.contains_self _ _
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨vR s₀, by simp, vAt_sub hp hi⟩
  rw [blockMixTo_eq]
  refine WP.seq (WP.seq (wp_mov (op2_reg _ _) fun f uf => ?_))
  have kf : ∀ r ∈ preserved, f.gpr r = s.gpr r := fun r hr => by
    rw [uf.other _ (pres_ne r hr).1, kt r hr]
  refine bm_ok hS hp (srcOK_v hp hi) (by rw [uf.gpr, kt _ (by decide), h.r9])
    (by rw [kf _ (by decide), h.r4]) (by rw [kf _ (by decide), h.r7]) (by rw [uf.sp, spt, esp])
    (by rw [uf.rd, rdt, erd]) (by rw [uf.wr, wrt, ewr]) (by rw [uf.mem]; exact ft)
    fun s4 rd4 wr4 sp4 cs4 f4 b4 => ?_
  rw [uf.mem, mt] at f4 b4
  rw [vAt_addr hp hi] at b4
  obtain ⟨F, K, X, D⟩ := mem2_ok hp hi h f4 b4
  have k4 : ∀ r ∈ preserved, r ≠ .lr → s4.gpr r = s.gpr r := fun r hr hlr => by
    rw [cs4 r hr hlr, kf r hr]
  refine wp_add (op2_reg _ _) fun s5 u5 => wp_subs (op2_imm (by decide)) fun s6 u6 z6 =>
    WP.block_nil ?_
  have k6 : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r8 → r ≠ .r9 → s6.gpr r = s.gpr r :=
    fun r hr hlr h1 h2 => by rw [u6.other _ h1, u5.other _ h2, k4 r hr hlr]
  have e8 : s5.gpr .r8 = BitVec.ofNat 32 (NN s₀ - i) := by
    rw [u5.other _ (by decide), k4 _ (by decide) (by decide), h.r8]
  refine ⟨⟨by omega, by rw [u6.rd, u5.rd, rd4, uf.rd, rdt, erd], by rw [u6.wr, u5.wr, wr4, uf.wr, wrt, ewr],
    by rw [u6.sp, u5.sp, sp4, uf.sp, spt, esp],
    by rw [k6 _ (by decide) (by decide) (by decide) (by decide), h.r4],
    by rw [k6 _ (by decide) (by decide) (by decide) (by decide), h.r5],
    by rw [k6 _ (by decide) (by decide) (by decide) (by decide), h.r6],
    by rw [k6 _ (by decide) (by decide) (by decide) (by decide), h.r7],
    by rw [u6.gpr, e8, dec_count hi], ?_,
    by rw [u6.mem, u5.mem]; exact F, by rw [u6.mem, u5.mem]; exact K,
    by rw [u6.mem, u5.mem]; exact X, by rw [u6.mem, u5.mem]; exact D⟩, by rw [z6, e8, dec_z hi hN]⟩
  rw [u6.other _ (by decide), u5.gpr, k4 _ (by decide) (by decide), k4 _ (by decide) (by decide),
    h.r9, h.r7, vAt_succ]

theorem loop2_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv2 s₀ 0 s) : WP isa (.loop (step2 c) .ne) s (Inv2 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv2 s₀) (fun _ hi _ h => step2_ok hS hp hi h) h

/-! ## Step 3 -/

/-- After `i` iterations of step 3. -/
structure Inv3 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = bP s₀
  r5 : s.gpr .r5 = vP s₀
  r6 : s.gpr .r6 = sc s₀
  r7 : s.gpr .r7 = BitVec.ofNat 32 (128 * rr s₀)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (NN s₀ - i)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (NN s₀ - 1)
  frame : Frame [bR s₀, vR s₀, scR s₀] s₀.mem s.mem
  kept : Kept s₀ s.mem
  v : ∀ k < NN s₀, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)
  x : (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - i)
    (bytesAt s.mem (bA s₀) (128 * rr s₀))).1 = roMix (rr s₀) (NN s₀) (B s₀)
  /-- The indices still to come. -/
  js : (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - i)
    (bytesAt s.mem (bA s₀) (128 * rr s₀))).2 =
      (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop i

theorem mid_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv2 s₀ (NN s₀) s) :
    WP isa (.block rmMid) s (Inv3 s₀ 0) := by
  have n1 := NN_pos hp
  have hs := hp.s_nw
  unfold rmMid
  refine wp_ldr (a := scA s₀ + BitVec.ofNat 64 156) (by decide) (by rw [h.r6, addr_add (by omega)])
    (by rw [h.rd, h.wr, hp.rd, hp.wr]
        exact InRegions.of_mem (R := scR s₀) (by simp) (in_s s₀ (by omega)))
    fun a ua => wp_sub (op2_imm (by decide)) fun b ub => WP.block_nil ?_
  have ka : a.gpr .r8 = BitVec.ofNat 32 (NN s₀) := by rw [ua.gpr, h.kept.2]
  have k : ∀ r, r ≠ .r8 → r ≠ .r9 → b.gpr r = s.gpr r := fun r h1 h2 => by
    rw [ub.other _ h2, ua.other _ h1]
  have hm : b.mem = s.mem := by rw [ub.mem, ua.mem]
  refine ⟨Nat.zero_le _, by rw [ub.rd, ua.rd, h.rd], by rw [ub.wr, ua.wr, h.wr],
    by rw [ub.sp, ua.sp, h.sp], by rw [k _ (by decide) (by decide), h.r4],
    by rw [k _ (by decide) (by decide), h.r5], by rw [k _ (by decide) (by decide), h.r6],
    by rw [k _ (by decide) (by decide), h.r7], by rw [ub.other _ (by decide), ka]; rfl,
    by rw [ub.gpr, ka, ofNat_pred32 n1],
    by rw [hm]; exact h.frame, by rw [hm]; exact h.kept, fun k hk => by rw [hm]; exact h.done k hk,
    ?_, ?_⟩
  · rw [hm, h.x, Nat.sub_zero]
    exact (roMix_eq _ _ _).symm
  · rw [hm, h.x, Nat.sub_zero, List.drop_zero]
    exact (roMixIndices_eq _ _ _).symm

/-- The index `j`. -/
abbrev jOf (s₀ : State) (m : Mem) : Nat :=
  Spec.Scrypt.integerify (rr s₀) (bytesAt m (bA s₀) (128 * rr s₀)) % NN s₀

theorem jOf_lt {s₀ : State} (hp : Pre s₀) (m : Mem) : jOf s₀ m < NN s₀ :=
  Nat.mod_lt _ (NN_pos hp)

/-- `j` as the code computes it. -/
theorem jOf_eq {s₀ : State} (hp : Pre s₀) (m : Mem) :
    m.readW (bA s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 32 &&& BitVec.ofNat 32 (NN s₀ - 1) =
      BitVec.ofNat 32 (jOf s₀ m) := by
  obtain ⟨e, he⟩ := hp.pow
  have hN := NN_lt hp
  have he' : e ≤ 32 := by
    by_contra hc
    have : 2 ^ 32 < 2 ^ e := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := jOf_lt hp m; omega), he, and_mask32 _ he',
    jOf, he, integerify_mod32 _ _ hp.pos he']

theorem jOf_lt32 {s₀ : State} (hp : Pre s₀) (m : Mem) : jOf s₀ m < 2 ^ 32 := by
  have := jOf_lt hp m; have := NN_lt hp; omega

/-- The memory after iteration `i` of step 3. -/
theorem mem3_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s)
    {m₄ : Mem}
    (f₄ : Frame [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩]
      (writeBytes s.mem (tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (bA s₀) (128 * rr s₀))
        (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)))) m₄)
    (b₄ : bytesAt m₄ (bA s₀) (128 * rr s₀) = blockMix (rr s₀)
      (bytesAt (writeBytes s.mem (tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (bA s₀) (128 * rr s₀))
        (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)))) (tP s₀) (128 * rr s₀))) :
    Frame [bR s₀, vR s₀, scR s₀] s₀.mem m₄ ∧ Kept s₀ m₄ ∧
    (∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)) ∧
    (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - (i + 1))
      (bytesAt m₄ (bA s₀) (128 * rr s₀))).1 = roMix (rr s₀) (NN s₀) (B s₀) ∧
    (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - (i + 1))
      (bytesAt m₄ (bA s₀) (128 * rr s₀))).2 =
        (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop (i + 1) := by
  have lt := r_lt hp
  have hj := jOf_lt hp s.mem
  set T := Spec.Pbkdf2.xorBytes (bytesAt s.mem (bA s₀) (128 * rr s₀))
    (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)) with hT
  have hl : T.length = 128 * rr s₀ := by
    rw [hT, xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  have hself : bytesAt (writeBytes s.mem (tP s₀) T) (tP s₀) (128 * rr s₀) = T := by
    have := bytesAt_writeBytes_self s.mem (tP s₀) T (by rw [hl]; omega)
    rwa [hl] at this
  have f₂ : Frame [⟨tP s₀, 128 * rr s₀⟩] s.mem (writeBytes s.mem (tP s₀) T) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame [bR s₀, vR s₀, scR s₀] s.mem (writeBytes s.mem (tP s₀) T) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, t_sub hp⟩
  have hv : ∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀) :=
    fun k hk => by
      rw [call_keeps_v hp f₄ hk, bytesAt_writeBytes_sep _ _
        (by rw [hl]; exact (vAt_s hp hk).sub_right (t_sub hp)) (by omega)]
      exact h.v k hk
  have e : NN s₀ - i = NN s₀ - (i + 1) + 1 := by omega
  refine ⟨(h.frame.trans f₂').trans (call_frame f₄),
    call_kept hp f₄ (h.kept.frame f₂ fun r hr => ?_), hv, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact keep_t hp
  · rw [← h.x, e, mixLoop_succ_fst, b₄, hself, hT, vList_getD _ hj, h.v _ hj]
  · have hs := h.js
    rw [e, mixLoop_succ_snd, vList_getD _ hj, ← h.v _ hj] at hs
    rw [← List.tail_drop, ← hs, b₄, hself, hT]
    rfl

/-- `jBlock`: `r0 = j`. -/
theorem j_ok {s₀ : State} (hp : Pre s₀) {s : State} (h4 : s.gpr .r4 = bP s₀)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 (128 * rr s₀)) (h9 : s.gpr .r9 = BitVec.ofNat 32 (NN s₀ - 1))
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block jBlock) s fun s' => Upd s s' .r0 (BitVec.ofNat 32 (jOf s₀ s.mem)) := by
  have lt := r_lt hp
  have := hp.pos
  have hb := hp.b_nw
  unfold jBlock
  refine wp_add (op2_reg _ _) fun a ua => wp_sub (op2_imm (by decide)) fun b ub => ?_
  refine wp_ldr (a := bA s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) (by decide)
    (by rw [ub.gpr, ua.gpr, h4, h7, sub32 _ (by omega), add_zero32,
      addr_add (by omega)])
    (by rw [ub.rd, ub.wr, ua.rd, ua.wr, hrd, hwr, hp.rd, hp.wr]
        exact InRegions.of_mem (R := bR s₀) (by simp) (contains_off (by omega) (by omega)))
    fun d ud => wp_and (op2_reg _ _) fun e ue => WP.block_nil ?_
  refine ⟨?_, fun r hr => ?_, by rw [ue.mem, ud.mem, ub.mem, ua.mem], by rw [ue.rd, ud.rd, ub.rd, ua.rd],
    by rw [ue.wr, ud.wr, ub.wr, ua.wr], by rw [ue.sp, ud.sp, ub.sp, ua.sp]⟩
  · rw [ue.gpr, ud.gpr, ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h9,
      ub.mem, ua.mem, jOf_eq hp]
  · rw [ue.other _ hr, ud.other _ hr, ub.other _ hr, ua.other _ hr]

/-- The address of `V[j]`, as `mulLoop` computes it. -/
theorem vAt_mul (s₀ : State) (j : Nat) :
    vP s₀ + BitVec.ofNat 32 (j * (128 * rr s₀)) = vAt32 s₀ j := by
  rw [Nat.mul_comm]

/-- One iteration of step 3. -/
theorem step3_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    WP isa (step3 c) s fun s' => Inv3 s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = NN s₀) := by
  have lt := r_lt hp
  have pos := hp.pos
  have hN := NN_lt hp
  have hj := jOf_lt hp s.mem
  have hb := hp.b_nw
  have e4 : 4 * (32 * rr s₀) = 128 * rr s₀ := by omega
  unfold step3
  refine WP.seq (WP.mono (j_ok hp h.r4 h.r7 h.r9 h.rd h.wr) fun a ua => ?_)
  refine WP.seq (wp_mov (op2_reg _ _) fun b ub => wp_mov (op2_reg _ _) fun b' ub' =>
    WP.block_nil ?_)
  refine WP.seq (WP.mono (mulLoop_ok (j := jOf s₀ s.mem) (c := 128 * rr s₀) (a := vP s₀)
    (jOf_lt32 hp s.mem)
    (by rw [ub'.other _ (by decide), ub.other _ (by decide), ua.gpr])
    (by rw [ub'.other _ (by decide), ub.gpr, ua.other _ (by decide), h.r5])
    (by rw [ub'.gpr, ub.other _ (by decide), ua.other _ (by decide), h.r7]))
    fun m ⟨rdm, wrm, spm, memm, om, m1⟩ => ?_)
  rw [vAt_mul] at m1
  have km : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → m.gpr r = s.gpr r := fun r h0 h1 h2 h3 => by
    rw [om r h0 h1 h2 h3, ub'.other r h2, ub.other r h1, ua.other r h0]
  refine WP.seq (wp_mov (op2_reg _ _) fun d ud => wp_add (op2_imm (by decide)) fun e ue =>
    wp_mov (op2_lsr (by decide)) fun f uf => WP.block_nil ?_)
  have rdf : f.rd = s₀.rd := by rw [uf.rd, ue.rd, ud.rd, rdm, ub'.rd, ub.rd, ua.rd, h.rd]
  have wrf : f.wr = s₀.wr := by rw [uf.wr, ue.wr, ud.wr, wrm, ub'.wr, ub.wr, ua.wr, h.wr]
  have spf : f.sp = s₀.sp := by rw [uf.sp, ue.sp, ud.sp, spm, ub'.sp, ub.sp, ua.sp, h.sp]
  have mf : f.mem = s.mem := by rw [uf.mem, ue.mem, ud.mem, memm, ub'.mem, ub.mem, ua.mem]
  have kf : ∀ r ∈ preserved, f.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h0, h1, h2, h3⟩ := pres_ne r hr
    rw [uf.other _ h3, ue.other _ h2, ud.other _ h0, km r h0 h1 h2 h3]
  refine WP.seq (WP.mono (xorLoop_ok (x := bP s₀) (y := vAt32 s₀ (jOf s₀ s.mem)) (d := tP32 s₀)
    (n := 32 * rr s₀) (by omega) (by omega) (by omega)
    (by rw [e4]; exact vAt_nw hp hj) (by rw [e4]; exact t_nw hp)
    (by rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, km _ (by decide) (by decide)
      (by decide) (by decide), h.r4])
    (by rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), m1])
    (by rw [uf.other _ (by decide), ue.gpr, ud.other _ (by decide), km _ (by decide) (by decide)
      (by decide) (by decide), h.r6]; rfl)
    (by rw [uf.gpr, ue.other _ (by decide), ud.other _ (by decide), km _ (by decide) (by decide)
      (by decide) (by decide), h.r7, sh2 hp])
    (fun k hk => by rw [rdf, wrf]; exact b_word hp hk)
    (fun k hk => by rw [rdf, wrf]; exact InRegions.right (v_word hp hj hk))
    (fun k hk => by rw [wrf]; exact t_word hp hk)
    (by rw [e4, t_addr hp]; exact t_b hp)
    (by rw [e4, t_addr hp, vAt_addr hp hj]; exact (vAt_s hp hj).symm.sub_left (t_sub hp)))
    fun t ⟨rdt, wrt, spt, gt, mt⟩ => ?_)
  rw [mf, e4, t_addr hp, vAt_addr hp hj] at mt
  have kt : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r := fun r hr hlr => by
    obtain ⟨h0, h1, h2, h3⟩ := pres_ne r hr
    rw [gt r h0 h1 h2 h3 (by rintro rfl; simp [preserved] at hr) hlr, kf r hr]
  have ft : Frame [bR s₀, vR s₀, scR s₀] s₀.mem t.mem := by
    rw [mt]
    refine h.frame.trans (Proof.Sha256.Stream.writeBytes_frame (R := ⟨tP s₀, 128 * rr s₀⟩)
      _ _ _ ?_ |>.sub fun r hr => ?_)
    · rw [xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
      exact Region.contains_self _ _
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, t_sub hp⟩
  rw [blockMixTo_eq]
  refine WP.seq (WP.seq (wp_add (op2_imm (by decide)) fun q1 v1 => ?_))
  have kq : ∀ r ∈ preserved, r ≠ .lr → q1.gpr r = s.gpr r := fun r hr hlr => by
    rw [v1.other _ (pres_ne r hr).1, kt r hr hlr]
  refine bm_ok hS hp (srcOK_t hp) (by rw [v1.gpr, kt _ (by decide) (by decide), h.r6]; rfl)
    (by rw [kq _ (by decide) (by decide), h.r4]) (by rw [kq _ (by decide) (by decide), h.r7])
    (by rw [v1.sp, spt, spf]) (by rw [v1.rd, rdt, rdf]) (by rw [v1.wr, wrt, wrf])
    (by rw [v1.mem]; exact ft) fun s4 rd4 wr4 sp4 cs4 f4 b4 => ?_
  rw [v1.mem, mt] at f4 b4
  rw [t_addr hp] at b4
  obtain ⟨F, K, V, X, J⟩ := mem3_ok hp hi h f4 b4
  have k4 : ∀ r ∈ preserved, r ≠ .lr → s4.gpr r = s.gpr r := fun r hr hlr => by
    rw [cs4 r hr hlr, kq r hr hlr]
  refine wp_subs (op2_imm (by decide)) fun s5 u5 z5 => WP.block_nil ?_
  have k5 : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r8 → s5.gpr r = s.gpr r := fun r hr hlr h1 => by
    rw [u5.other _ h1, k4 r hr hlr]
  have e8 : s4.gpr .r8 = BitVec.ofNat 32 (NN s₀ - i) := by
    rw [k4 _ (by decide) (by decide), h.r8]
  refine ⟨⟨by omega, by rw [u5.rd, rd4, v1.rd, rdt, rdf], by rw [u5.wr, wr4, v1.wr, wrt, wrf],
    by rw [u5.sp, sp4, v1.sp, spt, spf],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r4],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r5],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r6],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r7], by rw [u5.gpr, e8, dec_count hi],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r9],
    by rw [u5.mem]; exact F, by rw [u5.mem]; exact K, by rw [u5.mem]; exact V,
    by rw [u5.mem]; exact X, by rw [u5.mem]; exact J⟩, by rw [z5, e8, dec_z hi hN]⟩

theorem loop3_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv3 s₀ 0 s) : WP isa (.loop (step3 c) .ne) s (Inv3 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv3 s₀) (fun _ hi _ h => step3_ok hS hp hi h) h

/-! ## The epilogue -/

theorem epilogue_eq : rmEpilogue =
    (rmSaved.take 6).map (fun p => Instr.ldr p.1 .r6 p.2) ++ [.ldr .r6 .r6 152] := rfl

theorem rmSaved_r6 : ∀ p ∈ rmSaved.take 6, p.1 ≠ .r6 := by decide

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv3 s₀ (NN s₀) s) :
    WP isa (.block rmEpilogue) s fun s' => s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ p ∈ rmSaved, s'.gpr p.1 = s₀.gpr p.1) := by
  have hs := hp.s_nw
  have hin : ∀ d, d + 4 ≤ 256 → ∀ t : State, t.rd = s.rd → t.wr = s.wr →
      InRegions (t.rd ++ t.wr) (scA s₀ + BitVec.ofNat 64 d) 4 := fun d hd t hr hw => by
    rw [hr, hw, h.rd, h.wr, hp.rd, hp.wr]
    exact InRegions.of_mem (R := scR s₀) (by simp) (in_s s₀ hd)
  have sv : ∀ p ∈ rmSaved, s.mem.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1 := h.kept.1
  rw [epilogue_eq]
  refine restoreList_ok _ s _ (by decide) (fun p hp' => ?_) fun s₁ hl ho hm hrd hwr hsp => ?_
  · have hb := saved_offs p (List.mem_of_mem_take hp')
    rw [h.r6]
    exact ⟨rmSaved_r6 p hp', by omega, by omega, hin _ (by omega) _ rfl rfl⟩
  have e6 : s₁.gpr .r6 = sc s₀ := by rw [ho _ (by decide), h.r6]
  refine wp_ldr (a := scA s₀ + BitVec.ofNat 64 152) (by decide) (by rw [e6, addr_add (by omega)])
    (hin _ (by omega) _ hrd hwr) fun s₂ u₂ => WP.block_nil ?_
  refine ⟨by rw [u₂.mem, hm], by rw [u₂.sp, hsp], fun p hp' => ?_⟩
  by_cases h6 : p.1 = .r6
  · have : p = (.r6, 152) := by
      revert h6; revert hp'; revert p; decide
    subst this
    rw [u₂.gpr, hm, sv (.r6, 152) (by decide)]
  · have hp6 : p ∈ rmSaved.take 6 := by
      revert h6; revert hp'; revert p; decide
    rw [u₂.other _ h6, hl p hp6, h.r6]
    exact sv p hp'

/-! ## The whole function -/

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block rmPrologue) s₀ (P1 s₀) := by
  rw [prologue_eq]
  exact save_ok hp fun _ g g12 hrd hwr hsp hf hsv => setup_ok hp g g12 hrd hwr hsp hf hsv

theorem correct {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (roMixWith c) s₀ fun s' => (∀ p ∈ rmSaved, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = s₀.sp ∧
      Proof.Scrypt.roMixArm.post s₀ s' := by
  unfold roMixWith
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (nloop_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (setup2_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (loop2_ok hS hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (mid_ok hp h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (loop3_ok hS hp h₅) fun s₆ h₆ => ?_)
  refine WP.mono (restore_ok hp h₆) fun s' ⟨hm', hsp', hg'⟩ => ⟨hg', hsp'.trans h₆.sp, ?_⟩
  show bytesAt s'.mem (bA s₀) (128 * rr s₀) = roMix (rr s₀) (NN s₀) (B s₀)
  rw [hm', ← h₆.x, Nat.sub_self]
  rfl

end VG.Proof.Scrypt.Arm.RoMix
