import VerifiedGarbage.Proof.Scrypt.AArch64.RoMixLoops

/-!
# scryptROMix on AArch64: correctness

Untrusted: everything here is checked by Lean. The prologue saves our
caller's registers and our return address in `scratch` and computes `N`;
step 2 and step 3 are loops whose bodies call `vg_scrypt_blockmix` (through
`BlockMixSpec`); the epilogue restores the registers.
-/

namespace VG.Proof.Scrypt.AArch64.RoMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blockMix roMix)
open VG.Proof.Sha256.Stream (writeBytes)
open VG.Proof.Md5.AArch64.Stream (Upd Mupd wp_mov wp_add wp_addImm wp_subImm wp_ldr wp_str wp_movz
  wp_lsr wp_and readW_writeW_save)
open VG.Proof.Scrypt.AArch64.BlockMix (wp_lsl)
open VG.Proof.Scrypt.X86_64.BlockMix (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off
  InRegions.of_mem InRegions.right frame_bytesAt bytesAt_writeBytes_self bytesAt_writeBytes_sep
  bytesAt_length xorBytes_length)

/-! ## Instructions -/

theorem wp_madd {is : List Instr} {s : State} {Q : State → Prop} {d n m a : Reg}
    (k : ∀ s', Upd s s' d (s.gpr a + s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.madd .x d n m a :: is)) s Q :=
  Proof.Md5.AArch64.Stream.WP.cons (s' := s.write .x d (s.gpr a + s.gpr n * s.gpr m))
    (by simp [exec, State.read]) (k _ (Proof.Md5.AArch64.Stream.Upd.write64 _ _ _))

theorem ofNat_toNat' (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem shl7 {x : BitVec 64} (h : 128 * x.toNat < 2 ^ 64) : x <<< 7 = BitVec.ofNat 64 (128 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 7 = 128 from rfl, Nat.mul_comm,
    Nat.mod_eq_of_lt h, toNat_ofNat_lt h]

theorem dbl' (x : BitVec 64) : x + x = BitVec.ofNat 64 (2 * x.toNat) := by
  conv_lhs => rw [ofNat_toNat' x]
  rw [← BitVec.ofNat_add, Nat.two_mul]

theorem add_sub64 (a : Addr) {n : Nat} (h : 64 ≤ n) :
    a + BitVec.ofNat 64 n - BitVec.ofNat 64 64 = a + BitVec.ofNat 64 (n - 64) := by
  rw [show n = (n - 64) + 64 by omega, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel,
    BitVec.add_sub_cancel]

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
def saveMem (s₀ : State) : Mem :=
  ((((((s₀.mem.writeW (sc s₀ + BitVec.ofNat 64 128) (s₀.gpr .x19)).writeW
    (sc s₀ + BitVec.ofNat 64 136) (s₀.gpr .x20)).writeW (sc s₀ + BitVec.ofNat 64 144)
    (s₀.gpr .x22)).writeW (sc s₀ + BitVec.ofNat 64 152) (s₀.gpr .x23)).writeW
    (sc s₀ + BitVec.ofNat 64 160) (s₀.gpr .x24)).writeW (sc s₀ + BitVec.ofNat 64 168)
    (s₀.gpr .x30)).writeW (sc s₀ + BitVec.ofNat 64 176) (s₀.gpr .x21)

set_option simprocs false in
theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := by
  intro p hp
  simp only [rmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [saveMem, Mem.readW_writeW_self64, readW_writeW_save]

theorem saveMem_frame (s₀ : State) : Frame [scR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 8 ≤ 256 → (scR s₀).Contains (sc s₀ + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => in_s s₀ hd
  simp only [saveMem]
  exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 128 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 136 (by omega))).writeW (List.mem_singleton_self _) _
    (c 144 (by omega))).writeW (List.mem_singleton_self _) _ (c 152 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 160 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 168 (by omega))).writeW (List.mem_singleton_self _) _ (c 176 (by omega))

theorem prologue_eq : rmPrologue =
    [.str .x .x19 .x4 128, .str .x .x20 .x4 136, .str .x .x22 .x4 144, .str .x .x23 .x4 152,
     .str .x .x24 .x4 160, .str .x .x30 .x4 168, .str .x .x21 .x4 176] ++
    [mov .x19 .x0, mov .x20 .x2, mov .x21 .x4, .lsl .x .x22 .x1 7,
     mov .x9 .x1, .movz .x .x10 1 0, .add .x .x11 .x3 .x3] := rfl

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.sp = s₀.sp →
      s₁.mem = saveMem s₀ → WP isa (.block rest) s₁ Q) :
    WP isa (.block ([.str .x .x19 .x4 128, .str .x .x20 .x4 136, .str .x .x22 .x4 144,
      .str .x .x23 .x4 152, .str .x .x24 .x4 160, .str .x .x30 .x4 168, .str .x .x21 .x4 176] ++
      rest)) s₀ Q := by
  have o : ∀ d, d + 8 ≤ 256 → ∀ s : State, s.wr = s₀.wr →
      InRegions s.wr (sc s₀ + BitVec.ofNat 64 d) 8 := fun d hd s hw => by
    rw [hw, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ hd)
  simp only [List.cons_append, List.nil_append]
  refine wp_str (by decide) rfl (o 128 (by omega) _ rfl) fun s1 u1 => ?_
  refine wp_str (by decide) (by rw [u1.gpr]) (o 136 (by omega) _ u1.wr) fun s2 u2 => ?_
  refine wp_str (by decide) (by rw [u2.gpr, u1.gpr]) (o 144 (by omega) _ (u2.wr.trans u1.wr))
    fun s3 u3 => ?_
  refine wp_str (by decide) (by rw [u3.gpr, u2.gpr, u1.gpr])
    (o 152 (by omega) _ (u3.wr.trans (u2.wr.trans u1.wr))) fun s4 u4 => ?_
  refine wp_str (by decide) (by rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr])
    (o 160 (by omega) _ (u4.wr.trans (u3.wr.trans (u2.wr.trans u1.wr)))) fun s5 u5 => ?_
  refine wp_str (by decide) (by rw [u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr])
    (o 168 (by omega) _ (u5.wr.trans (u4.wr.trans (u3.wr.trans (u2.wr.trans u1.wr)))))
    fun s6 u6 => ?_
  refine wp_str (by decide) (by rw [u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr])
    (o 176 (by omega) _ (u6.wr.trans (u5.wr.trans (u4.wr.trans (u3.wr.trans (u2.wr.trans u1.wr))))))
    fun s7 u7 => ?_
  exact k s7 (by rw [u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr])
    (by rw [u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd])
    (u7.wr.trans (u6.wr.trans (u5.wr.trans (u4.wr.trans (u3.wr.trans (u2.wr.trans u1.wr))))))
    (by rw [u7.sp, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp])
    (by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u6.gpr, u5.gpr, u4.gpr, u3.gpr,
          u2.gpr, u1.gpr]
        rfl)

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = saveMem s₀
  x19 : s.gpr .x19 = bP s₀
  x20 : s.gpr .x20 = vP s₀
  x21 : s.gpr .x21 = sc s₀
  x22 : s.gpr .x22 = BitVec.ofNat 64 (128 * rr s₀)
  x9 : s.gpr .x9 = BitVec.ofNat 64 (rr s₀)
  x10 : s.gpr .x10 = 1
  x11 : s.gpr .x11 = BitVec.ofNat 64 (2 * vl s₀)

theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block [mov .x19 .x0, mov .x20 .x2, mov .x21 .x4, .lsl .x .x22 .x1 7,
     mov .x9 .x1, .movz .x .x10 1 0, .add .x .x11 .x3 .x3]) s₁ (P1 s₀) := by
  have lt : 128 * (s₀.gpr .x1).toNat < 2 ^ 64 := r_lt hp
  refine wp_mov fun a ua => wp_mov fun b ub => wp_mov fun c uc => wp_lsl (by decide) fun d ud =>
    wp_mov fun e ue => wp_movz fun f uf => wp_add fun h uh => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [uh.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd, hrd]
  · rw [uh.wr, uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr, hwr]
  · rw [uh.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp, hsp]
  · rw [uh.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.gpr, g]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.gpr, ua.other _ (by decide), g]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.gpr, ub.other _ (by decide), ua.other _ (by decide), g]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide), ud.gpr,
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g, shl7 lt]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.gpr, ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g]
    exact ofNat_toNat' _
  · rw [uh.other _ (by decide), uf.gpr]; decide
  · rw [uh.gpr, uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g, dbl']

/-! ## Computing `N` -/

/-- After the loop computing `N`. -/
structure N1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = saveMem s₀
  x19 : s.gpr .x19 = bP s₀
  x20 : s.gpr .x20 = vP s₀
  x21 : s.gpr .x21 = sc s₀
  x22 : s.gpr .x22 = BitVec.ofNat 64 (128 * rr s₀)
  x10 : s.gpr .x10 = BitVec.ofNat 64 (2 * NN s₀)

theorem nloop_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : P1 s₀ s) : WP isa nLoop s (N1 s₀) := by
  obtain ⟨e, he⟩ := hp.pow
  have lt := v_lt hp
  have e2 : rr s₀ * 2 ^ (e + 1) = 2 * vl s₀ := by
    rw [hp.vl_eq, he, Nat.pow_succ, Nat.mul_comm (2 ^ e) 2, Nat.mul_left_comm]
  have hNe : 2 * vl s₀ < 2 ^ 64 := by have := vl_mul hp; omega
  refine WP.mono (nLoop_ok (r := rr s₀) (e := e) hp.pos (by omega) h.x9 h.x10
    (by rw [h.x11, e2])) fun t ⟨rd, wr, sp, mem, oth, x10⟩ => ?_
  exact ⟨by rw [rd, h.rd], by rw [wr, h.wr], by rw [sp, h.sp], by rw [mem, h.mem],
    by rw [oth _ (by decide) (by decide) (by decide), h.x19],
    by rw [oth _ (by decide) (by decide) (by decide), h.x20],
    by rw [oth _ (by decide) (by decide) (by decide), h.x21],
    by rw [oth _ (by decide) (by decide) (by decide), h.x22],
    by rw [x10, he, Nat.pow_succ, Nat.mul_comm]⟩

/-! ## Step 2 -/

/-- After `i` iterations of step 2. -/
structure Inv2 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = bP s₀
  x20 : s.gpr .x20 = vP s₀
  x21 : s.gpr .x21 = sc s₀
  x22 : s.gpr .x22 = BitVec.ofNat 64 (128 * rr s₀)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (NN s₀ - i)
  x24 : s.gpr .x24 = vAt s₀ i
  frame : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  kept : Kept s₀ s.mem
  x : bytesAt s.mem (bP s₀) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀)
  done : ∀ k < i, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)

set_option simprocs false in
theorem setupMem_kept (s₀ : State) :
    Kept s₀ ((saveMem s₀).writeW (sc s₀ + BitVec.ofNat 64 184) (BitVec.ofNat 64 (NN s₀))) := by
  refine ⟨fun p hp => ?_, Mem.readW_writeW_self64 _ _ _⟩
  have ho := saved_offs hp
  rw [readW_writeW_save _ _ _ (by omega) (by decide) (by omega)]
  exact saveMem_saved s₀ p hp

theorem setup2_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : N1 s₀ s) :
    WP isa (.block rmSetup) s (Inv2 s₀ 0) := by
  have lt := v_lt hp
  have n1 := NN_pos hp
  have : 2 * NN s₀ < 2 ^ 64 := by
    have : 2 * NN s₀ ≤ 128 * rr s₀ * NN s₀ := by
      have := hp.pos
      have : 2 ≤ 128 * rr s₀ := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  unfold rmSetup
  refine wp_lsr (by decide) fun t1 u1 => ?_
  have hd : t1.gpr .x10 = BitVec.ofNat 64 (NN s₀) := by
    rw [u1.gpr, h.x10, shr_ofNat _ (by omega), Nat.pow_one, Nat.mul_div_cancel_left _ (by decide)]
  refine wp_str (a := sc s₀ + BitVec.ofNat 64 184) (by decide) (by rw [u1.other _ (by decide), h.x21])
    (by rw [u1.wr, h.wr, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by omega)))
    fun t2 u2 => wp_mov fun t3 u3 => wp_mov fun t4 u4 => WP.block_nil ?_
  have g : ∀ r, r ≠ .x10 → r ≠ .x23 → r ≠ .x24 → t4.gpr r = s.gpr r := fun r b c d => by
    rw [u4.other _ d, u3.other _ c, u2.gpr, u1.other _ b]
  have hm : t4.mem = (saveMem s₀).writeW (sc s₀ + BitVec.ofNat 64 184) (BitVec.ofNat 64 (NN s₀)) := by
    rw [u4.mem, u3.mem, u2.mem, hd, u1.mem, h.mem]
  have fr : Frame [scR s₀] s₀.mem t4.mem := by
    rw [hm]; exact (saveMem_frame s₀).writeW (List.mem_singleton_self _) _ (in_s s₀ (by omega))
  refine ⟨Nat.zero_le _, by rw [u4.rd, u3.rd, u2.rd, u1.rd, h.rd],
    by rw [u4.wr, u3.wr, u2.wr, u1.wr, h.wr], by rw [u4.sp, u3.sp, u2.sp, u1.sp, h.sp],
    by rw [g _ (by decide) (by decide) (by decide), h.x19],
    by rw [g _ (by decide) (by decide) (by decide), h.x20],
    by rw [g _ (by decide) (by decide) (by decide), h.x21],
    by rw [g _ (by decide) (by decide) (by decide), h.x22], ?_, ?_,
    fr.mono (by simp), by rw [hm]; exact setupMem_kept s₀, ?_, fun k hk => absurd hk (by omega)⟩
  · rw [u4.other _ (by decide), u3.gpr, u2.gpr, hd]; rfl
  · rw [u4.gpr, u3.other _ (by decide), u2.gpr, u1.other _ (by decide), h.x20]
    simp
  · refine frame_bytesAt fr (fun r hr => ?_) (by have := r_lt hp; omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub' (s₀ := s₀))

/-! ## A call of `vg_scrypt_blockmix` into `b` -/

/-- The instructions before the call, after `x0` is set. -/
abbrev bmTail : List Instr := [.lsr .x .x1 .x22 7, mov .x2 .x19, mov .x3 .x1, mov .x4 .x21]

theorem blockMixTo_eq (c : Prog isa) (src : List Instr) :
    blockMixTo c src = .seq (.block (src ++ bmTail)) (.call "vg_scrypt_blockmix" c) := rfl

theorem b_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (bP s₀) (128 * rr s₀) := by
  rw [hp.wr]
  refine InRegions.of_mem (R := bR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem w_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (sc s₀) 128 := by
  rw [hp.wr]
  refine InRegions.of_mem (R := scR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

/-- The registers our loops keep are not the call's arguments. -/
theorem pres_ne : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x9 ∧
    r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14 := by decide

/-- Setting up and making the call, from `x0 = A`. -/
theorem bm_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State} {A : Addr}
    (hA : s.gpr .x0 = A) (h19 : s.gpr .x19 = bP s₀) (h21 : s.gpr .x21 = sc s₀)
    (h22 : s.gpr .x22 = BitVec.ofNat 64 (128 * rr s₀)) (hsp : s.sp = s₀.sp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hAb : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩)
    (hAw : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨sc s₀, 128⟩)
    (hAs : (stkR s₀).Disjoint ⟨A, 128 * rr s₀⟩) (hAn : A.toNat + 128 * rr s₀ ≤ 2 ^ 64)
    (hAi : InRegions (s₀.rd ++ s₀.wr) A (128 * rr s₀)) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (bP s₀) (128 * rr s₀) = blockMix (rr s₀) (bytesAt s.mem A (128 * rr s₀)) →
      Q s') :
    WP isa (.block bmTail) s fun s' => WP isa (.call "vg_scrypt_blockmix" c) s' Q := by
  have lt := r_lt hp
  refine wp_lsr (by decide) fun a ua => wp_mov fun b ub => wp_mov fun d ud => wp_mov fun e ue =>
    WP.block_nil ?_
  have k : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → e.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [ue.other _ h4, ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have h1 : a.gpr .x1 = BitVec.ofNat 64 (rr s₀) := by
    rw [ua.gpr, h22, shr_ofNat _ lt]; congr 1; omega
  have hm : e.mem = s.mem := by rw [ue.mem, ud.mem, ub.mem, ua.mem]
  have hsp' : e.sp = s₀.sp := by rw [ue.sp, ud.sp, ub.sp, ua.sp, hsp]
  refine hS e A (bP s₀) (sc s₀) (rr s₀)
    (by rw [k _ (by decide) (by decide) (by decide) (by decide), hA])
    (by rw [ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide), h1])
    (by rw [ue.other _ (by decide), ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h19])
    (by rw [ue.other _ (by decide), ud.gpr, ub.other _ (by decide), h1])
    (by rw [ue.gpr, ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h21])
    hp.pos lt ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hAb hAw
    (by rw [hsp']; exact hp.sp16)
    (by rw [hsp']; exact hAs) (by rw [hsp']; exact hp.stk_b.sub_right (b_sub' (s₀ := s₀)))
    (by rw [hsp']; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) hAn (by have := hp.b_nw; omega)
    (by have := hp.s_nw; omega)
    (by rw [ue.rd, ud.rd, ub.rd, ua.rd, ue.wr, ud.wr, ub.wr, ua.wr, hrd, hwr]; exact hAi)
    (by rw [ue.wr, ud.wr, ub.wr, ua.wr, hwr]; exact b_in hp)
    (by rw [ue.wr, ud.wr, ub.wr, ua.wr, hwr]; exact w_in hp) _
    fun s' rd' wr' sp' cs' f' b' => hQ s' (by rw [rd', ue.rd, ud.rd, ub.rd, ua.rd])
      (by rw [wr', ue.wr, ud.wr, ub.wr, ua.wr]) (by rw [sp', ue.sp, ud.sp, ub.sp, ua.sp])
      (fun r hr h30 => by
        obtain ⟨-, n1, n2, n3, n4, -⟩ := pres_ne r hr
        rw [cs' r hr h30, k r n1 n2 n3 n4])
      (by rw [hm, hsp'] at f'; exact f') (by rw [b', hm])

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem vAt_nw {i : Nat} (hi : i < NN s₀) : (vAt s₀ i).toNat + 128 * rr s₀ ≤ 2 ^ 64 := by
  have := v_lt hp
  have hv := hp.v_nw
  have e := vl_mul hp
  have := v_le hi
  have := hp.pos
  rw [toNat_add_ofNat _ (by omega)]
  omega

theorem vAt_in {i : Nat} (hi : i < NN s₀) : InRegions s₀.wr (vAt s₀ i) (128 * rr s₀) := by
  rw [hp.wr]
  have e := vl_mul hp
  have := v_le hi
  have lt := v_lt hp
  exact InRegions.of_mem (R := vR s₀) (by simp) (contains_off (by rw [e]; omega) (by omega))

/-- `V[i]` and the parts of `scratch` and the stack we use. -/
theorem vAt_b {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (bR s₀) :=
  hp.b_v.symm.sub_left (vAt_sub hp hi)
theorem vAt_s {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (scR s₀) :=
  hp.v_s.sub_left (vAt_sub hp hi)
theorem vAt_stk {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (stkR s₀) :=
  hp.stk_v.symm.sub_left (vAt_sub hp hi)

omit hp in
/-- The frame of a call writing `b`, from the one we keep. -/
theorem call_frame {m m' : Mem} (hf : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] m m') :
    Frame [bR s₀, vR s₀, scR s₀, stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨bR s₀, by simp, b_sub'⟩
    · exact ⟨scR s₀, by simp, w_sub⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-- What a call writing `b` keeps: `V[k]`. -/
theorem call_keeps_v {m m' : Mem} (hf : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] m m')
    {k : Nat} (hk : k < NN s₀) :
    bytesAt m' (vAt s₀ k) (128 * rr s₀) = bytesAt m (vAt s₀ k) (128 * rr s₀) := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (vAt_b hp hk).sub_right b_sub'
  · exact (vAt_s hp hk).sub_right w_sub
  · exact vAt_stk hp hk

theorem call_kept {m m' : Mem} (hf : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] m m')
    (h : Kept s₀ m) : Kept s₀ m' :=
  h.frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (keep_b hp).sub_right b_sub'
    · exact keep_w
    · exact keep_stk hp

/-- The memory after iteration `i` of step 2. -/
theorem mem2_ok {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv2 s₀ i s) {m₃ : Mem}
    (f₃ : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀]
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) m₃)
    (b₃ : bytesAt m₃ (bP s₀) (128 * rr s₀) = blockMix (rr s₀)
      (bytesAt (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) (vAt s₀ i)
        (128 * rr s₀))) :
    Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem m₃ ∧ Kept s₀ m₃ ∧
    bytesAt m₃ (bP s₀) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) (i + 1) (B s₀) ∧
    ∀ k < i + 1, bytesAt m₃ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀) := by
  have lt := r_lt hp
  have hl : (bytesAt s.mem (bP s₀) (128 * rr s₀)).length = 128 * rr s₀ := bytesAt_length _ _ _
  have hself : bytesAt (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) (vAt s₀ i)
      (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀) := by
    have := bytesAt_writeBytes_self s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))
      (by rw [hl]; exact lt)
    rw [hl] at this
    rw [this, h.x]
  have f₂ : Frame [⟨vAt s₀ i, 128 * rr s₀⟩] s.mem
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s.mem
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) :=
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
    · rw [bytesAt_writeBytes_sep _ _ (by rw [hl]; exact vAt_disj hp (by omega) hi hki) lt]
      exact h.done k (by omega)

end

theorem vAt_succ (s₀ : State) (i : Nat) :
    vAt s₀ i + BitVec.ofNat 64 (128 * rr s₀) = vAt s₀ (i + 1) := by
  show _ = vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * (i + 1))
  rw [add_ofNat, Nat.mul_succ]

theorem b_word {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 16 * rr s₀) :
    InRegions (s₀.rd ++ s₀.wr) (bP s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
  have := r_lt hp
  rw [hp.rd, hp.wr]
  exact InRegions.of_mem (R := bR s₀) (by simp) (contains_off (by omega) (by omega))

theorem v_word {s₀ : State} (hp : Pre s₀) {i k : Nat} (hi : i < NN s₀) (hk : k < 16 * rr s₀) :
    InRegions s₀.wr (vAt s₀ i + BitVec.ofNat 64 (8 * k)) 8 := by
  rw [hp.wr]
  have e := vl_mul hp
  have := v_le hi
  have lt := v_lt hp
  show InRegions _ (vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * i) + BitVec.ofNat 64 (8 * k)) 8
  rw [add_ofNat]
  exact InRegions.of_mem (R := vR s₀) (by simp) (contains_off (by rw [e]; omega) (by omega))

theorem sh3 {s₀ : State} (hp : Pre s₀) :
    BitVec.ofNat 64 (128 * rr s₀) >>> 3 = BitVec.ofNat 64 (16 * rr s₀) := by
  rw [shr_ofNat _ (r_lt hp)]; congr 1; omega

/-- One iteration of step 2. -/
theorem step2_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv2 s₀ i s) :
    WP isa (step2 c) s fun s' => Inv2 s₀ (i + 1) s' ∧ (s'.gpr .x23 != 0) = decide (i + 1 ≠ NN s₀) := by
  have lt := r_lt hp
  have pos := hp.pos
  have hN := NN_lt hp
  unfold step2
  refine WP.seq (wp_mov fun a ua => wp_mov fun b ub => wp_lsr (by decide) fun d ud => WP.block_nil ?_)
  have ke : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → d.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have erd : d.rd = s₀.rd := by rw [ud.rd, ub.rd, ua.rd, h.rd]
  have ewr : d.wr = s₀.wr := by rw [ud.wr, ub.wr, ua.wr, h.wr]
  have esp : d.sp = s₀.sp := by rw [ud.sp, ub.sp, ua.sp, h.sp]
  have hme : d.mem = s.mem := by rw [ud.mem, ub.mem, ua.mem]
  have e8 : 8 * (16 * rr s₀) = 128 * rr s₀ := by omega
  refine WP.seq (WP.mono (copyLoop_ok (src := bP s₀) (dst := vAt s₀ i) (n := 16 * rr s₀) (by omega)
    (by omega) (by rw [ud.other _ (by decide), ub.other _ (by decide), ua.gpr, h.x19])
    (by rw [ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.x24])
    (by rw [ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h.x22, sh3 hp])
    (fun k hk => by rw [erd, ewr]; exact b_word hp hk)
    (fun k hk => by rw [ewr]; exact v_word hp hi hk)
    (by rw [e8]; exact (vAt_b hp hi).symm.sub_left b_sub'))
    fun t ⟨rdt, wrt, spt, gt, mt⟩ => ?_)
  rw [hme, e8] at mt
  have kt : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => by
    obtain ⟨-, -, -, -, -, h9, h10, h11, h12, -⟩ := pres_ne r hr
    rw [gt r h9 h10 h11 h12, ke r h9 h10 h11]
  rw [blockMixTo_eq]
  refine WP.seq (WP.seq (wp_mov fun f uf => ?_))
  have kf : ∀ r ∈ preserved, f.gpr r = s.gpr r := fun r hr => by
    rw [uf.other _ (pres_ne r hr).1, kt r hr]
  refine bm_ok hS hp (A := vAt s₀ i) (by rw [uf.gpr, kt _ (by decide), h.x24])
    (by rw [kf _ (by decide), h.x19]) (by rw [kf _ (by decide), h.x21])
    (by rw [kf _ (by decide), h.x22]) (by rw [uf.sp, spt, esp])
    (by rw [uf.rd, rdt, erd]) (by rw [uf.wr, wrt, ewr])
    ((vAt_b hp hi).sub_right b_sub') ((vAt_s hp hi).sub_right w_sub) (vAt_stk hp hi).symm
    (vAt_nw hp hi) (InRegions.right (vAt_in hp hi)) fun s4 rd4 wr4 sp4 cs4 f4 b4 => ?_
  rw [uf.mem, mt] at f4 b4
  obtain ⟨F, K, X, D⟩ := mem2_ok hp hi h f4 b4
  have k4 : ∀ r ∈ preserved, r ≠ .x30 → s4.gpr r = s.gpr r := fun r hr h30 => by
    rw [cs4 r hr h30, kf r hr]
  refine wp_add fun s5 u5 => wp_subImm (by decide) fun s6 u6 => WP.block_nil ?_
  have k6 : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x23 → r ≠ .x24 → s6.gpr r = s.gpr r :=
    fun r hr h30 h1 h2 => by rw [u6.other _ h1, u5.other _ h2, k4 r hr h30]
  have e23 : s6.gpr .x23 = BitVec.ofNat 64 (NN s₀ - (i + 1)) := by
    rw [u6.gpr, u5.other _ (by decide), k4 _ (by decide) (by decide), h.x23, dec_count hi]
  refine ⟨⟨by omega, by rw [u6.rd, u5.rd, rd4, uf.rd, rdt, erd], by rw [u6.wr, u5.wr, wr4, uf.wr, wrt, ewr],
    by rw [u6.sp, u5.sp, sp4, uf.sp, spt, esp],
    by rw [k6 _ (by decide) (by decide) (by decide) (by decide), h.x19],
    by rw [k6 _ (by decide) (by decide) (by decide) (by decide), h.x20],
    by rw [k6 _ (by decide) (by decide) (by decide) (by decide), h.x21],
    by rw [k6 _ (by decide) (by decide) (by decide) (by decide), h.x22], e23, ?_,
    by rw [u6.mem, u5.mem]; exact F, by rw [u6.mem, u5.mem]; exact K,
    by rw [u6.mem, u5.mem]; exact X, by rw [u6.mem, u5.mem]; exact D⟩, ?_⟩
  · rw [u6.other _ (by decide), u5.gpr, k4 _ (by decide) (by decide), k4 _ (by decide) (by decide),
      h.x24, h.x22, vAt_succ]
  · rw [e23, dec_ne hi hN]

theorem loop2_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv2 s₀ 0 s) : WP isa (.loop (step2 c) (.nonzero .x .x23)) s (Inv2 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv2 s₀) (fun _ hi _ h => step2_ok hS hp hi h) h

/-! ## Step 3 -/

/-- After `i` iterations of step 3. -/
structure Inv3 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = bP s₀
  x20 : s.gpr .x20 = vP s₀
  x21 : s.gpr .x21 = sc s₀
  x22 : s.gpr .x22 = BitVec.ofNat 64 (128 * rr s₀)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (NN s₀ - i)
  x24 : s.gpr .x24 = BitVec.ofNat 64 (NN s₀ - 1)
  frame : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  kept : Kept s₀ s.mem
  v : ∀ k < NN s₀, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)
  x : (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - i)
    (bytesAt s.mem (bP s₀) (128 * rr s₀))).1 = roMix (rr s₀) (NN s₀) (B s₀)
  /-- The indices still to come. -/
  js : (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - i)
    (bytesAt s.mem (bP s₀) (128 * rr s₀))).2 =
      (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop i

theorem mid_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv2 s₀ (NN s₀) s) :
    WP isa (.block rmMid) s (Inv3 s₀ 0) := by
  have n1 := NN_pos hp
  unfold rmMid
  refine wp_ldr (a := sc s₀ + BitVec.ofNat 64 184) (by decide) (by rw [h.x21])
    (by rw [h.rd, h.wr, hp.rd, hp.wr]
        exact InRegions.of_mem (R := scR s₀) (by simp) (in_s s₀ (by omega)))
    fun a ua => wp_subImm (by decide) fun b ub => WP.block_nil ?_
  have ka : a.gpr .x23 = BitVec.ofNat 64 (NN s₀) := by rw [ua.gpr, h.kept.2]
  have k : ∀ r, r ≠ .x23 → r ≠ .x24 → b.gpr r = s.gpr r := fun r h1 h2 => by
    rw [ub.other _ h2, ua.other _ h1]
  have hm : b.mem = s.mem := by rw [ub.mem, ua.mem]
  refine ⟨Nat.zero_le _, by rw [ub.rd, ua.rd, h.rd], by rw [ub.wr, ua.wr, h.wr],
    by rw [ub.sp, ua.sp, h.sp], by rw [k _ (by decide) (by decide), h.x19],
    by rw [k _ (by decide) (by decide), h.x20], by rw [k _ (by decide) (by decide), h.x21],
    by rw [k _ (by decide) (by decide), h.x22], by rw [ub.other _ (by decide), ka]; rfl, ?_,
    by rw [hm]; exact h.frame, by rw [hm]; exact h.kept, fun k hk => by rw [hm]; exact h.done k hk,
    ?_, ?_⟩
  · rw [ub.gpr, ka]
    have := dec_count (n := NN s₀) (k := 0) n1
    simpa using this
  · rw [hm, h.x, Nat.sub_zero]
    exact (roMix_eq _ _ _).symm
  · rw [hm, h.x, Nat.sub_zero, List.drop_zero]
    exact (roMixIndices_eq _ _ _).symm

/-- The index `j`. -/
abbrev jOf (s₀ : State) (m : Mem) : Nat :=
  Spec.Scrypt.integerify (rr s₀) (bytesAt m (bP s₀) (128 * rr s₀)) % NN s₀

theorem jOf_lt {s₀ : State} (hp : Pre s₀) (m : Mem) : jOf s₀ m < NN s₀ :=
  Nat.mod_lt _ (NN_pos hp)

/-- `j` as the code computes it. -/
theorem jOf_eq {s₀ : State} (hp : Pre s₀) (m : Mem) :
    m.readW (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 &&& BitVec.ofNat 64 (NN s₀ - 1) =
      BitVec.ofNat 64 (jOf s₀ m) := by
  obtain ⟨e, he⟩ := hp.pow
  have hN := NN_lt hp
  have he' : e ≤ 64 := by
    by_contra hc
    have : 2 ^ 64 < 2 ^ e := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ofNat_lt (by have := jOf_lt hp m; omega), he, and_mask _ he', jOf, he,
    integerify_mod _ _ hp.pos he']

/-- The address of the low word of `X`'s last 64-byte block. -/
theorem j_addr {s₀ : State} (hp : Pre s₀) :
    bP s₀ + BitVec.ofNat 64 (128 * rr s₀) - BitVec.ofNat 64 64 =
      bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64) :=
  add_sub64 _ (by have := hp.pos; omega)

theorem t_word {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 16 * rr s₀) :
    InRegions s₀.wr (tP s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
  have := hp.s_nw
  rw [hp.wr, add_ofNat]
  exact InRegions.of_mem (R := scR s₀) (by simp) (contains_off (by omega) (by omega))

theorem t_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (tP s₀) (128 * rr s₀) := by
  have := hp.s_nw
  rw [hp.wr]
  exact InRegions.of_mem (R := scR s₀) (by simp) (contains_off (by omega) (by omega))

theorem t_b {s₀ : State} (hp : Pre s₀) :
    Region.Disjoint ⟨tP s₀, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩ :=
  (hp.b_s.symm.sub_left (t_sub hp)).sub_right b_sub'

theorem t_nw {s₀ : State} (hp : Pre s₀) : (tP s₀).toNat + 128 * rr s₀ ≤ 2 ^ 64 := by
  have := hp.s_nw
  rw [toNat_add_ofNat _ (by omega)]
  omega

/-- The memory after iteration `i` of step 3. -/
theorem mem3_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s)
    {m₄ : Mem}
    (f₄ : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀]
      (writeBytes s.mem (tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (bP s₀) (128 * rr s₀))
        (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)))) m₄)
    (b₄ : bytesAt m₄ (bP s₀) (128 * rr s₀) = blockMix (rr s₀)
      (bytesAt (writeBytes s.mem (tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (bP s₀) (128 * rr s₀))
        (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)))) (tP s₀) (128 * rr s₀))) :
    Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem m₄ ∧ Kept s₀ m₄ ∧
    (∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)) ∧
    (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - (i + 1))
      (bytesAt m₄ (bP s₀) (128 * rr s₀))).1 = roMix (rr s₀) (NN s₀) (B s₀) ∧
    (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - (i + 1))
      (bytesAt m₄ (bP s₀) (128 * rr s₀))).2 =
        (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop (i + 1) := by
  have lt := r_lt hp
  have hj := jOf_lt hp s.mem
  set T := Spec.Pbkdf2.xorBytes (bytesAt s.mem (bP s₀) (128 * rr s₀))
    (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)) with hT
  have hl : T.length = 128 * rr s₀ := by
    rw [hT, xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  have hself : bytesAt (writeBytes s.mem (tP s₀) T) (tP s₀) (128 * rr s₀) = T := by
    have := bytesAt_writeBytes_self s.mem (tP s₀) T (by rw [hl]; exact lt)
    rwa [hl] at this
  have f₂ : Frame [⟨tP s₀, 128 * rr s₀⟩] s.mem (writeBytes s.mem (tP s₀) T) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s.mem (writeBytes s.mem (tP s₀) T) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, t_sub hp⟩
  have hv : ∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀) :=
    fun k hk => by
      rw [call_keeps_v hp f₄ hk, bytesAt_writeBytes_sep _ _
        (by rw [hl]; exact (vAt_s hp hk).sub_right (t_sub hp)) lt]
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

/-- `jBlock`: `x9 = j`. -/
theorem j_ok {s₀ : State} (hp : Pre s₀) {s : State} (h19 : s.gpr .x19 = bP s₀)
    (h22 : s.gpr .x22 = BitVec.ofNat 64 (128 * rr s₀)) (h24 : s.gpr .x24 = BitVec.ofNat 64 (NN s₀ - 1))
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block jBlock) s fun s' => Upd s s' .x9 (BitVec.ofNat 64 (jOf s₀ s.mem)) := by
  have lt := r_lt hp
  have := hp.pos
  unfold jBlock
  refine wp_add fun a ua => wp_subImm (by decide) fun b ub => ?_
  refine wp_ldr (a := bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) (by decide)
    (by rw [ub.gpr, ua.gpr, h19, h22, j_addr hp]; exact BitVec.add_zero _)
    (by rw [ub.rd, ub.wr, ua.rd, ua.wr, hrd, hwr, hp.rd, hp.wr]
        exact InRegions.of_mem (R := bR s₀) (by simp) (contains_off (by omega) (by omega)))
    fun d ud => wp_and fun e ue => WP.block_nil ?_
  refine ⟨?_, fun r hr => ?_, by rw [ue.mem, ud.mem, ub.mem, ua.mem], by rw [ue.rd, ud.rd, ub.rd, ua.rd],
    by rw [ue.wr, ud.wr, ub.wr, ua.wr], by rw [ue.sp, ud.sp, ub.sp, ua.sp]⟩
  · rw [ue.gpr, ud.gpr, ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h24,
      ub.mem, ua.mem, jOf_eq hp]
  · rw [ue.other _ hr, ud.other _ hr, ub.other _ hr, ua.other _ hr]

/-- The address of `V[j]`. -/
theorem vAt_madd (s₀ : State) (j : Nat) :
    vP s₀ + BitVec.ofNat 64 j * BitVec.ofNat 64 (128 * rr s₀) = vAt s₀ j := by
  rw [← BitVec.ofNat_mul, Nat.mul_comm]

/-- One iteration of step 3. -/
theorem step3_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    WP isa (step3 c) s fun s' => Inv3 s₀ (i + 1) s' ∧ (s'.gpr .x23 != 0) = decide (i + 1 ≠ NN s₀) := by
  have lt := r_lt hp
  have pos := hp.pos
  have hN := NN_lt hp
  have hj := jOf_lt hp s.mem
  have e8 : 8 * (16 * rr s₀) = 128 * rr s₀ := by omega
  unfold step3
  refine WP.seq (WP.mono (j_ok hp h.x19 h.x22 h.x24 h.rd h.wr) fun a ua => ?_)
  refine WP.seq (wp_madd fun b ub => wp_mov fun d ud => wp_addImm (by decide) fun e ue =>
    wp_lsr (by decide) fun f uf => WP.block_nil ?_)
  have rdf : f.rd = s₀.rd := by rw [uf.rd, ue.rd, ud.rd, ub.rd, ua.rd, h.rd]
  have wrf : f.wr = s₀.wr := by rw [uf.wr, ue.wr, ud.wr, ub.wr, ua.wr, h.wr]
  have spf : f.sp = s₀.sp := by rw [uf.sp, ue.sp, ud.sp, ub.sp, ua.sp, h.sp]
  have mf : f.mem = s.mem := by rw [uf.mem, ue.mem, ud.mem, ub.mem, ua.mem]
  have kf : ∀ r ∈ preserved, f.gpr r = s.gpr r := fun r hr => by
    obtain ⟨-, -, -, -, -, h9, h10, h11, h12, -⟩ := pres_ne r hr
    rw [uf.other _ h12, ue.other _ h11, ud.other _ h9, ub.other _ h10, ua.other _ h9]
  have h10 : f.gpr .x10 = vAt s₀ (jOf s₀ s.mem) := by
    rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), ub.gpr,
      ua.gpr, ua.other _ (by decide), ua.other _ (by decide), h.x20, h.x22, vAt_madd]
  refine WP.seq (WP.mono (xorLoop_ok (x := bP s₀) (y := vAt s₀ (jOf s₀ s.mem)) (d := tP s₀)
    (n := 16 * rr s₀) (by omega) (by omega)
    (by rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, ub.other _ (by decide),
      ua.other _ (by decide), h.x19])
    h10
    (by rw [uf.other _ (by decide), ue.gpr, ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.x21])
    (by rw [uf.gpr, ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.x22, sh3 hp])
    (fun k hk => by rw [rdf, wrf]; exact b_word hp hk)
    (fun k hk => by rw [rdf, wrf]; exact InRegions.right (v_word hp hj hk))
    (fun k hk => by rw [wrf]; exact t_word hp hk)
    (by rw [e8]; exact t_b hp) (by rw [e8]; exact (vAt_s hp hj).symm.sub_left (t_sub hp)))
    fun t ⟨rdt, wrt, spt, gt, mt⟩ => ?_)
  rw [mf, e8] at mt
  have kt : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => by
    obtain ⟨-, -, -, -, -, h9, h10, h11, h12, h13, h14⟩ := pres_ne r hr
    rw [gt r h9 h10 h11 h12 h13 h14, kf r hr]
  rw [blockMixTo_eq]
  refine WP.seq (WP.seq (wp_addImm (by decide) fun q1 v1 => ?_))
  have kq : ∀ r ∈ preserved, q1.gpr r = s.gpr r := fun r hr => by
    rw [v1.other _ (pres_ne r hr).1, kt r hr]
  refine bm_ok hS hp (A := tP s₀) (by rw [v1.gpr, kt _ (by decide), h.x21])
    (by rw [kq _ (by decide), h.x19]) (by rw [kq _ (by decide), h.x21])
    (by rw [kq _ (by decide), h.x22]) (by rw [v1.sp, spt, spf])
    (by rw [v1.rd, rdt, rdf]) (by rw [v1.wr, wrt, wrf])
    (t_b hp) (t_w hp) (hp.stk_s.sub_right (t_sub hp)) (t_nw hp)
    (InRegions.right (t_in hp)) fun s4 rd4 wr4 sp4 cs4 f4 b4 => ?_
  rw [v1.mem, mt] at f4 b4
  obtain ⟨F, K, V, X, J⟩ := mem3_ok hp hi h f4 b4
  have k4 : ∀ r ∈ preserved, r ≠ .x30 → s4.gpr r = s.gpr r := fun r hr h30 => by
    rw [cs4 r hr h30, kq r hr]
  refine wp_subImm (by decide) fun s5 u5 => WP.block_nil ?_
  have k5 : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x23 → s5.gpr r = s.gpr r := fun r hr h30 h1 => by
    rw [u5.other _ h1, k4 r hr h30]
  have e23 : s5.gpr .x23 = BitVec.ofNat 64 (NN s₀ - (i + 1)) := by
    rw [u5.gpr, k4 _ (by decide) (by decide), h.x23, dec_count hi]
  refine ⟨⟨by omega, by rw [u5.rd, rd4, v1.rd, rdt, rdf], by rw [u5.wr, wr4, v1.wr, wrt, wrf],
    by rw [u5.sp, sp4, v1.sp, spt, spf],
    by rw [k5 _ (by decide) (by decide) (by decide), h.x19],
    by rw [k5 _ (by decide) (by decide) (by decide), h.x20],
    by rw [k5 _ (by decide) (by decide) (by decide), h.x21],
    by rw [k5 _ (by decide) (by decide) (by decide), h.x22], e23,
    by rw [k5 _ (by decide) (by decide) (by decide), h.x24],
    by rw [u5.mem]; exact F, by rw [u5.mem]; exact K, by rw [u5.mem]; exact V,
    by rw [u5.mem]; exact X, by rw [u5.mem]; exact J⟩, by rw [e23, dec_ne hi hN]⟩

theorem loop3_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv3 s₀ 0 s) : WP isa (.loop (step3 c) (.nonzero .x .x23)) s (Inv3 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv3 s₀) (fun _ hi _ h => step3_ok hS hp hi h) h

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv3 s₀ (NN s₀) s) :
    WP isa (.block rmEpilogue) s fun s' => s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ p ∈ rmSaved, s'.gpr p.1 = s₀.gpr p.1) := by
  have hin : ∀ d, d + 8 ≤ 256 → ∀ t : State, t.rd = s.rd → t.wr = s.wr →
      InRegions (t.rd ++ t.wr) (sc s₀ + BitVec.ofNat 64 d) 8 := fun d hd t hr hw => by
    rw [hr, hw, h.rd, h.wr, hp.rd, hp.wr]
    exact InRegions.of_mem (R := scR s₀) (by simp) (in_s s₀ hd)
  have sv : ∀ p ∈ rmSaved, s.mem.readW (sc s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1 := h.kept.1
  simp only [rmEpilogue, rmSaved, List.map_cons, List.map_nil]
  refine wp_ldr (by decide) (by rw [h.x21]) (hin 128 (by omega) _ rfl rfl) fun a ua => ?_
  refine wp_ldr (by decide) (by rw [ua.other _ (by decide), h.x21])
    (hin 136 (by omega) _ ua.rd ua.wr) fun b ub => ?_
  refine wp_ldr (by decide) (by rw [ub.other _ (by decide), ua.other _ (by decide), h.x21])
    (hin 144 (by omega) _ (ub.rd.trans ua.rd) (ub.wr.trans ua.wr)) fun c uc => ?_
  refine wp_ldr (by decide) (by rw [uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.x21])
    (hin 152 (by omega) _ (uc.rd.trans (ub.rd.trans ua.rd)) (uc.wr.trans (ub.wr.trans ua.wr)))
    fun d ud => ?_
  refine wp_ldr (by decide) (by rw [ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), h.x21])
    (hin 160 (by omega) _ (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd)))
      (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr)))) fun e ue => ?_
  refine wp_ldr (by decide) (by rw [ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.x21])
    (hin 168 (by omega) _ (ue.rd.trans (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd))))
      (ue.wr.trans (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr))))) fun f uf => ?_
  refine wp_ldr (by decide) (by rw [uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.x21])
    (hin 176 (by omega) _ (uf.rd.trans (ue.rd.trans (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd)))))
      (uf.wr.trans (ue.wr.trans (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr))))))
    fun g ug => WP.block_nil ?_
  have hm : g.mem = s.mem := by rw [ug.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
  refine ⟨hm, by rw [ug.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp], fun p hp' => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.gpr,
      sv (.x19, 128) (by simp [rmSaved])]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.gpr, ua.mem,
      sv (.x20, 136) (by simp [rmSaved])]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.gpr, ub.mem, ua.mem, sv (.x22, 144) (by simp [rmSaved])]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.mem,
      ub.mem, ua.mem, sv (.x23, 152) (by simp [rmSaved])]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.gpr, ud.mem, uc.mem, ub.mem, ua.mem,
      sv (.x24, 160) (by simp [rmSaved])]
  · rw [ug.other _ (by decide), uf.gpr, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem,
      sv (.x30, 168) (by simp [rmSaved])]
  · rw [ug.gpr, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, sv (.x21, 176) (by simp [rmSaved])]

/-! ## The whole function -/

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block rmPrologue) s₀ (P1 s₀) := by
  rw [prologue_eq]
  exact save_ok hp fun _ g hrd hwr hsp hm => setup_ok hp g hrd hwr hsp hm

theorem correct {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (roMixWith c) s₀ fun s' => (∀ p ∈ rmSaved, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = s₀.sp ∧
      Proof.Scrypt.roMixAArch64.post s₀ s' := by
  unfold roMixWith
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (nloop_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (setup2_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (loop2_ok hS hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (mid_ok hp h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (loop3_ok hS hp h₅) fun s₆ h₆ => ?_)
  refine WP.mono (restore_ok hp h₆) fun s' ⟨hm', hsp', hg'⟩ => ⟨hg', hsp'.trans h₆.sp, ?_⟩
  show bytesAt s'.mem (bP s₀) (128 * rr s₀) = roMix (rr s₀) (NN s₀) (B s₀)
  rw [hm', ← h₆.x, Nat.sub_self]
  rfl

end VG.Proof.Scrypt.AArch64.RoMix
