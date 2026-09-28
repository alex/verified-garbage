import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Scrypt.X86_64.RoMix
import VerifiedGarbage.Proof.Scrypt.X86_64.RoMixLoops

/-!
# scryptROMix on x86-64: correctness

Untrusted: everything here is checked by Lean. The prologue saves our
caller's registers in `scratch` and computes `N`; step 2 and step 3 are
loops whose bodies call `vg_scrypt_blockmix` (through `BlockMixSpec`); the
epilogue restores the registers.
-/

namespace VG.Proof.Scrypt.X86_64.RoMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blockMix roMix)
open VG.Proof.Sha1.X86_64.Stream (wp_mov wp_movm wp_store wp_add wp_addi wp_subi wp_mov32i)
open VG.Proof.Sha256.Stream (writeBytes)

theorem frame_bytesAt' {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  BlockMix.frame_bytesAt hf hd hn

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
def saveMem (s₀ : State) : Mem :=
  (((((s₀.mem.writeW (sc s₀ + BitVec.ofNat 64 128) (s₀.gpr .rbx)).writeW
    (sc s₀ + BitVec.ofNat 64 136) (s₀.gpr .rbp)).writeW (sc s₀ + BitVec.ofNat 64 144)
    (s₀.gpr .r12)).writeW (sc s₀ + BitVec.ofNat 64 152) (s₀.gpr .r14)).writeW
    (sc s₀ + BitVec.ofNat 64 160) (s₀.gpr .r15)).writeW (sc s₀ + BitVec.ofNat 64 168)
    (s₀.gpr .r13)

set_option simprocs false in
theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := by
  intro p hp
  simp only [rmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [saveMem, Mem.readW_writeW_self64,
    BlockMix.readW_writeW_off]

theorem saveMem_frame (s₀ : State) : Frame [scR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 8 ≤ 256 → (scR s₀).Contains (sc s₀ + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => in_s s₀ hd
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 128 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 136 (by omega))).writeW (List.mem_singleton_self _) _
    (c 144 (by omega))).writeW (List.mem_singleton_self _) _ (c 152 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 160 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 168 (by omega))

theorem prologue_eq : rmPrologue =
    [.store (at_ .r8 128) .rbx, .store (at_ .r8 136) .rbp, .store (at_ .r8 144) .r12,
     .store (at_ .r8 152) .r14, .store (at_ .r8 160) .r15, .store (at_ .r8 168) .r13] ++
    [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .r8), .mov .r14 (.reg .rsi),
     .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14),
     .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14),
     .alu .add .r14 (.reg .r14),
     .mov .rax (.reg .rsi), .mov32 .rdx (.imm 1), .alu .add .rcx (.reg .rcx)] := rfl

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.mem = saveMem s₀ →
      WP isa (.block rest) s₁ Q) :
    WP isa (.block ([.store (at_ .r8 128) .rbx, .store (at_ .r8 136) .rbp,
      .store (at_ .r8 144) .r12, .store (at_ .r8 152) .r14, .store (at_ .r8 160) .r15,
      .store (at_ .r8 168) .r13] ++ rest)) s₀ Q := by
  have o : ∀ d, d + 8 ≤ 256 → ∀ s : State, s.wr = s₀.wr →
      InRegions s.wr (sc s₀ + BitVec.ofNat 64 d) 8 := fun d hd s hw => by
    rw [hw, hp.wr]; exact BlockMix.InRegions.of_mem (by simp) (in_s s₀ hd)
  simp only [List.cons_append, List.nil_append]
  refine wp_store (BlockMix.ea_at _ _ _) (o 128 (by omega) _ rfl) fun s1 g1 m1 r1 w1 => ?_
  refine wp_store (by rw [BlockMix.ea_at, g1]) (o 136 (by omega) _ w1) fun s2 g2 m2 r2 w2 => ?_
  refine wp_store (by rw [BlockMix.ea_at, g2, g1]) (o 144 (by omega) _ (w2.trans w1))
    fun s3 g3 m3 r3 w3 => ?_
  refine wp_store (by rw [BlockMix.ea_at, g3, g2, g1]) (o 152 (by omega) _ (w3.trans (w2.trans w1)))
    fun s4 g4 m4 r4 w4 => ?_
  refine wp_store (by rw [BlockMix.ea_at, g4, g3, g2, g1])
    (o 160 (by omega) _ (w4.trans (w3.trans (w2.trans w1)))) fun s5 g5 m5 r5 w5 => ?_
  refine wp_store (by rw [BlockMix.ea_at, g5, g4, g3, g2, g1])
    (o 168 (by omega) _ (w5.trans (w4.trans (w3.trans (w2.trans w1))))) fun s6 g6 m6 r6 w6 => ?_
  exact k s6 (by rw [g6, g5, g4, g3, g2, g1]) (by rw [r6, r5, r4, r3, r2, r1])
    (w6.trans (w5.trans (w4.trans (w3.trans (w2.trans w1)))))
    (by rw [m6, m5, m4, m3, m2, m1, g5, g4, g3, g2, g1]; rfl)

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = saveMem s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bP s₀
  r12 : s.gpr .r12 = vP s₀
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)
  rax : s.gpr .rax = BitVec.ofNat 64 (rr s₀)
  rdx : s.gpr .rdx = 1
  rcx : s.gpr .rcx = BitVec.ofNat 64 (2 * vl s₀)

set_option linter.unusedSimpArgs false in
theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .r8),
     .mov .r14 (.reg .rsi),
     .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14),
     .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14),
     .alu .add .r14 (.reg .r14),
     .mov .rax (.reg .rsi), .mov32 .rdx (.imm 1), .alu .add .rcx (.reg .rcx)]) s₁ (P1 s₀) := by
  have lt := r_lt hp
  refine wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun c uc _ _ => wp_mov fun d ud _ _ =>
    wp_add fun e1 u1 => wp_add fun e2 u2 => wp_add fun e3 u3 => wp_add fun e4 u4 =>
    wp_add fun e5 u5 => wp_add fun e6 u6 => wp_add fun e7 u7 => wp_mov fun f uf _ _ =>
    wp_mov32i fun h uh _ _ => wp_add fun i ui => WP.block_nil ?_
  have x0 : d.gpr .r14 = BitVec.ofNat 64 (rr s₀) := by
    rw [ud.gpr, uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have x1 := u1.gpr.trans (BlockMix.dbl x0)
  have x2 := u2.gpr.trans (BlockMix.dbl x1)
  have x3 := u3.gpr.trans (BlockMix.dbl x2)
  have x4 := u4.gpr.trans (BlockMix.dbl x3)
  have x5 := u5.gpr.trans (BlockMix.dbl x4)
  have x6 := u6.gpr.trans (BlockMix.dbl x5)
  have x7 : e7.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀) := by
    rw [u7.gpr.trans (BlockMix.dbl x6)]; congr 1; omega
  have xc : h.gpr .rcx = BitVec.ofNat 64 (vl s₀) := by
    simp (disch := decide) only [uh.other, uf.other, u7.other, u6.other, u5.other, u4.other,
      u3.other, u2.other, u1.other, ud.other, uc.other, ub.other, ua.other, g,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ui.rd, uh.rd, uf.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, ud.rd,
      uc.rd, ub.rd, ua.rd, hrd]
  · rw [ui.wr, uh.wr, uf.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, ud.wr,
      uc.wr, ub.wr, ua.wr, hwr]
  · rw [ui.mem, uh.mem, uf.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem,
      u1.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  all_goals simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other,
    ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, u7.other, x7,
    uf.gpr, uf.other, uh.gpr, uh.other, ui.gpr, ui.other, g, xc, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  all_goals first | rfl | decide |
    exact BlockMix.dbl (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block rmPrologue) s₀ (P1 s₀) := by
  rw [prologue_eq]
  exact save_ok hp fun _ g hrd hwr hm => setup_ok hp g hrd hwr hm

/-! ## Computing `N` -/

/-- After `i` iterations of step 2. -/
structure Inv2 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bP s₀
  rbp : s.gpr .rbp = vAt s₀ i
  r12 : s.gpr .r12 = vP s₀
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)
  r15 : s.gpr .r15 = BitVec.ofNat 64 (NN s₀ - i)
  frame : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  kept : Kept s₀ s.mem
  x : bytesAt s.mem (bP s₀) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀)
  done : ∀ k < i, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)

set_option simprocs false in
theorem setupMem_kept (s₀ : State) :
    Kept s₀ ((saveMem s₀).writeW (sc s₀ + BitVec.ofNat 64 176) (BitVec.ofNat 64 (NN s₀))) := by
  refine ⟨fun p hp => ?_, Mem.readW_writeW_self64 _ _ _⟩
  have ho := saved_offs hp
  rw [BlockMix.readW_writeW_off _ _ _ (by omega) (by decide) (by omega)]
  exact saveMem_saved s₀ p hp

/-- After the loop computing `N`. -/
structure N1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = saveMem s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bP s₀
  r12 : s.gpr .r12 = vP s₀
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)
  rdx : s.gpr .rdx = BitVec.ofNat 64 (2 * NN s₀)

theorem nloop_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : P1 s₀ s) : WP isa nLoop s (N1 s₀) := by
  obtain ⟨e, he⟩ := hp.pow
  have lt := v_lt hp
  have pos := hp.pos
  have e2 : rr s₀ * 2 ^ (e + 1) = 2 * vl s₀ := by
    rw [hp.vl_eq, he, Nat.pow_succ]; ring_nf
  have hNe : 2 * vl s₀ < 2 ^ 64 := by
    have : 128 * rr s₀ * NN s₀ = 128 * vl s₀ := by rw [hp.vl_eq]; ring_nf
    omega
  refine WP.mono (nLoop_ok (r := rr s₀) (e := e) hp.pos (by omega) h.rax h.rdx
    (by rw [h.rcx, e2])) fun t ⟨rd, wr, mem, oth, rdx⟩ => ?_
  have k : ∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r := oth
  exact ⟨by rw [rd, h.rd], by rw [wr, h.wr], by rw [mem, h.mem],
    by rw [k _ (by decide) (by decide), h.rsp], by rw [k _ (by decide) (by decide), h.rbx],
    by rw [k _ (by decide) (by decide), h.r12], by rw [k _ (by decide) (by decide), h.r13],
    by rw [k _ (by decide) (by decide), h.r14], by rw [rdx, he, Nat.pow_succ, Nat.mul_comm]⟩

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
  refine wp_shr (by decide) (by decide) fun t1 u1 _ => ?_
  have hd : t1.gpr .rdx = BitVec.ofNat 64 (NN s₀) := by
    rw [u1.gpr, h.rdx, shr_ofNat _ (by omega), Nat.pow_one, Nat.mul_div_cancel_left _ (by decide)]
  refine wp_store (a := sc s₀ + BitVec.ofNat 64 176)
    (by rw [BlockMix.ea_at, u1.other _ (by decide), h.r13])
    (by rw [u1.wr, h.wr, hp.wr]; exact BlockMix.InRegions.of_mem (by simp) (in_s s₀ (by omega)))
    fun t2 g2 m2 rd2 wr2 => wp_mov fun t3 u3 _ _ => wp_mov fun t4 u4 _ _ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rdx → r ≠ .r15 → r ≠ .rbp → t4.gpr r = s.gpr r := fun r b c d => by
    rw [u4.other _ d, u3.other _ c, g2, u1.other _ b]
  have hm : t4.mem = (saveMem s₀).writeW (sc s₀ + BitVec.ofNat 64 176) (BitVec.ofNat 64 (NN s₀)) := by
    rw [u4.mem, u3.mem, m2, hd, u1.mem, h.mem]
  have fr : Frame [scR s₀] s₀.mem t4.mem := by
    rw [hm]; exact (saveMem_frame s₀).writeW (List.mem_singleton_self _) _ (in_s s₀ (by omega))
  refine ⟨Nat.zero_le _, by rw [u4.rd, u3.rd, rd2, u1.rd, h.rd],
    by rw [u4.wr, u3.wr, wr2, u1.wr, h.wr], by rw [g _ (by decide) (by decide) (by decide), h.rsp],
    by rw [g _ (by decide) (by decide) (by decide), h.rbx], ?_,
    by rw [g _ (by decide) (by decide) (by decide), h.r12],
    by rw [g _ (by decide) (by decide) (by decide), h.r13],
    by rw [g _ (by decide) (by decide) (by decide), h.r14], ?_,
    fr.mono (by simp), by rw [hm]; exact setupMem_kept s₀, ?_, fun k hk => absurd hk (by omega)⟩
  · rw [u4.gpr, u3.other _ (by decide), g2, u1.other _ (by decide), h.r12]
    simp
  · rw [u4.other _ (by decide), u3.gpr, g2, hd]; rfl
  · refine frame_bytesAt' fr (fun r hr => ?_) (by have := r_lt hp; omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub' (s₀ := s₀))

theorem start_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : P1 s₀ s) {rest : Prog isa}
    {Q : State → Prop} (hk : ∀ s', Inv2 s₀ 0 s' → WP isa rest s' Q) :
    WP isa (.seq nLoop (.seq (.block rmSetup) rest)) s Q :=
  WP.seq (WP.mono (nloop_ok hp h) fun _ h' => WP.seq (WP.mono (setup2_ok hp h') hk))

/-! ## A call of `vg_scrypt_blockmix` into `b` -/

/-- The instructions before the call, after `rdi` is set. -/
abbrev bmTail : List Instr :=
  [.mov .rsi (.reg .r14), .shift .shr .rsi 7, .mov .rcx (.reg .rsi), .mov .rdx (.reg .rbx),
    .mov .r8 (.reg .r13)]

theorem blockMixTo_eq (c : Prog isa) (src : List Instr) :
    blockMixTo c src = .seq (.block (src ++ bmTail)) (.call "vg_scrypt_blockmix" c) := rfl

theorem b_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (bP s₀) (128 * rr s₀) := by
  rw [hp.wr]
  refine BlockMix.InRegions.of_mem (R := bR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem w_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (sc s₀) 128 := by
  rw [hp.wr]
  refine BlockMix.InRegions.of_mem (R := scR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem calleeSaved_tail {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rsi ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r8 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Setting up and making the call, from `rdi = A`. -/
theorem bm_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State} {A : Addr}
    (hA : s.gpr .rdi = A) (hbx : s.gpr .rbx = bP s₀) (h13 : s.gpr .r13 = sc s₀)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)) (hsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hAb : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩)
    (hAw : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨sc s₀, 128⟩)
    (hAs : (stkR s₀).Disjoint ⟨A, 128 * rr s₀⟩) (hAn : A.toNat + 128 * rr s₀ ≤ 2 ^ 64)
    (hAi : InRegions (s₀.rd ++ s₀.wr) A (128 * rr s₀)) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (bP s₀) (128 * rr s₀) = blockMix (rr s₀) (bytesAt s.mem A (128 * rr s₀)) →
      Q s') :
    WP isa (.block bmTail) s fun s' => WP isa (.call "vg_scrypt_blockmix" c) s' Q := by
  have lt := r_lt hp
  refine wp_mov fun a ua _ _ => wp_shr (by decide) (by decide) fun b ub _ =>
    wp_mov fun d ud _ _ => wp_mov fun e ue _ _ => wp_mov fun f uf _ _ => WP.block_nil ?_
  have k : ∀ r, r ≠ .rsi → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → f.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [uf.other _ h4, ue.other _ h3, ud.other _ h2, ub.other _ h1, ua.other _ h1]
  have hsi : b.gpr .rsi = BitVec.ofNat 64 (rr s₀) := by
    rw [ub.gpr, ua.gpr, h14, shr_ofNat _ lt]; congr 1; omega
  have hm : f.mem = s.mem := by rw [uf.mem, ue.mem, ud.mem, ub.mem, ua.mem]
  have hsp' : f.gpr .rsp = s₀.gpr .rsp := by rw [k _ (by decide) (by decide) (by decide) (by decide), hsp]
  refine hS f A (bP s₀) (sc s₀) (rr s₀)
    (by rw [k _ (by decide) (by decide) (by decide) (by decide), hA])
    (by rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), hsi])
    (by rw [uf.other _ (by decide), ue.gpr, ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), hbx])
    (by rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, hsi])
    (by rw [uf.gpr, ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h13])
    hp.pos lt ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hAb hAw
    (by rw [hsp']; exact hAs) (by rw [hsp']; exact hp.stk_b.sub_right (b_sub' (s₀ := s₀)))
    (by rw [hsp']; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) hAn (by have := hp.b_nw; omega)
    (by have := hp.s_nw; omega)
    (by rw [uf.rd, ue.rd, ud.rd, ub.rd, ua.rd, uf.wr, ue.wr, ud.wr, ub.wr, ua.wr, hrd, hwr]; exact hAi)
    (by rw [uf.wr, ue.wr, ud.wr, ub.wr, ua.wr, hwr]; exact b_in hp)
    (by rw [uf.wr, ue.wr, ud.wr, ub.wr, ua.wr, hwr]; exact w_in hp) _
    fun s' rd' wr' cs' f' b' => hQ s' (by rw [rd', uf.rd, ue.rd, ud.rd, ub.rd, ua.rd])
      (by rw [wr', uf.wr, ue.wr, ud.wr, ub.wr, ua.wr])
      (fun r hr => by
        obtain ⟨h1, h2, h3, h4⟩ := calleeSaved_tail hr
        rw [cs' r hr, k r h1 h2 h3 h4])
      (by rw [hm, hsp'] at f'; exact f') (by rw [b', hm])

/-! ## Step 2 -/

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem vAt_nw {i : Nat} (hi : i < NN s₀) : (vAt s₀ i).toNat + 128 * rr s₀ ≤ 2 ^ 64 := by
  have := v_lt hp
  have := hp.pos
  have hv := hp.v_nw
  have e : vl s₀ * 128 = 128 * rr s₀ * NN s₀ := by rw [hp.vl_eq]; ring_nf
  have : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  rw [BlockMix.toNat_add_ofNat _ (by omega)]
  omega

theorem vAt_in {i : Nat} (hi : i < NN s₀) : InRegions s₀.wr (vAt s₀ i) (128 * rr s₀) := by
  rw [hp.wr]
  have e : vl s₀ * 128 = 128 * rr s₀ * NN s₀ := by rw [hp.vl_eq]; ring_nf
  have : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have lt := v_lt hp
  exact BlockMix.InRegions.of_mem (R := vR s₀) (by simp)
    (BlockMix.contains_off (by rw [e]; omega) (by omega))

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
  refine frame_bytesAt' hf (fun r hr => ?_) (by have := r_lt hp; omega)
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
  have hl : (bytesAt s.mem (bP s₀) (128 * rr s₀)).length = 128 * rr s₀ := BlockMix.bytesAt_length _ _ _
  have hself : bytesAt (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) (vAt s₀ i)
      (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀) := by
    have := BlockMix.bytesAt_writeBytes_self s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))
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
    · rw [BlockMix.bytesAt_writeBytes_sep _ _ (by rw [hl]; exact vAt_disj hp (by omega) hi hki) lt]
      exact h.done k (by omega)

end

theorem cs_ne {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rax ∧ r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r8 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem vAt_succ (s₀ : State) (i : Nat) :
    vAt s₀ i + BitVec.ofNat 64 (128 * rr s₀) = vAt s₀ (i + 1) := by
  show _ = vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * (i + 1))
  rw [BlockMix.add_ofNat, Nat.mul_succ]

theorem b_word {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 16 * rr s₀) :
    InRegions (s₀.rd ++ s₀.wr) (bP s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
  have := r_lt hp
  rw [hp.rd, hp.wr]
  exact BlockMix.InRegions.of_mem (R := bR s₀) (by simp) (BlockMix.contains_off (by omega) (by omega))

theorem v_word {s₀ : State} (hp : Pre s₀) {i k : Nat} (hi : i < NN s₀) (hk : k < 16 * rr s₀) :
    InRegions s₀.wr (vAt s₀ i + BitVec.ofNat 64 (8 * k)) 8 := by
  rw [hp.wr]
  have e : vl s₀ * 128 = 128 * rr s₀ * NN s₀ := by rw [hp.vl_eq]; ring_nf
  have : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have lt := v_lt hp
  show InRegions _ (vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * i) + BitVec.ofNat 64 (8 * k)) 8
  rw [BlockMix.add_ofNat]
  exact BlockMix.InRegions.of_mem (R := vR s₀) (by simp)
    (BlockMix.contains_off (by rw [e]; omega) (by omega))

/-- One iteration of step 2. -/
theorem step2_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv2 s₀ i s) :
    WP isa (step2 c) s fun s' => Inv2 s₀ (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀)) := by
  have lt := r_lt hp
  have vlt := v_lt hp
  have pos := hp.pos
  have n1 := NN_pos hp
  have hN : NN s₀ < 2 ^ 64 := by
    have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by omega)
    omega
  unfold step2
  refine WP.seq (wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun d ud _ _ =>
    wp_shr (by decide) (by decide) fun e ue _ => WP.block_nil ?_)
  have ke : ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → e.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [ue.other _ h3, ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have erd : e.rd = s₀.rd := by rw [ue.rd, ud.rd, ub.rd, ua.rd, h.rd]
  have ewr : e.wr = s₀.wr := by rw [ue.wr, ud.wr, ub.wr, ua.wr, h.wr]
  have hme : e.mem = s.mem := by rw [ue.mem, ud.mem, ub.mem, ua.mem]
  have ecx : e.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀) := by
    rw [ue.gpr, ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h.r14, shr_ofNat _ lt]
    congr 1; omega
  have e8 : 8 * (16 * rr s₀) = 128 * rr s₀ := by omega
  refine WP.seq (WP.mono (copyLoop_ok (src := bP s₀) (dst := vAt s₀ i) (n := 16 * rr s₀) (by omega)
    (by omega) (by rw [ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.gpr, h.rbx])
    (by rw [ue.other _ (by decide), ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.rbp])
    ecx (fun k hk => by rw [erd, ewr]; exact b_word hp hk)
    (fun k hk => by rw [ewr]; exact v_word hp hi hk)
    (by rw [e8]; exact (vAt_b hp hi).symm.sub_left b_sub'))
    fun t ⟨rdt, wrt, gt, mt⟩ => ?_)
  rw [hme, e8] at mt
  have kt : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3, h4, -, -⟩ := cs_ne hr
    rw [gt r h1 h2 h3 h4, ke r h2 h3 h4]
  rw [blockMixTo_eq]
  refine WP.seq (WP.seq (wp_mov fun f uf _ _ => ?_))
  have kf : ∀ r ∈ calleeSaved, f.gpr r = s.gpr r := fun r hr => by
    rw [uf.other _ (cs_ne hr).2.1, kt r hr]
  have cs : ∀ r ∈ calleeSaved, r ∈ calleeSaved := fun _ h => h
  refine bm_ok hS hp (A := vAt s₀ i) (by rw [uf.gpr, kt _ (by simp [calleeSaved]), h.rbp])
    (by rw [kf _ (by simp [calleeSaved]), h.rbx]) (by rw [kf _ (by simp [calleeSaved]), h.r13])
    (by rw [kf _ (by simp [calleeSaved]), h.r14]) (by rw [kf _ (by simp [calleeSaved]), h.rsp])
    (by rw [uf.rd, rdt, erd]) (by rw [uf.wr, wrt, ewr])
    ((vAt_b hp hi).sub_right b_sub') ((vAt_s hp hi).sub_right w_sub) (vAt_stk hp hi).symm
    (vAt_nw hp hi) (BlockMix.InRegions.right (vAt_in hp hi)) fun s4 rd4 wr4 cs4 f4 b4 => ?_
  rw [uf.mem, mt] at f4 b4
  obtain ⟨F, K, X, D⟩ := mem2_ok hp hi h f4 b4
  have k4 : ∀ r ∈ calleeSaved, s4.gpr r = s.gpr r := fun r hr => by rw [cs4 r hr, kf r hr]
  refine wp_add fun s5 u5 => wp_subi fun s6 u6 z6 => WP.block_nil ?_
  have k6 : ∀ r ∈ calleeSaved, r ≠ .rbp → r ≠ .r15 → s6.gpr r = s.gpr r := fun r hr h1 h2 => by
    rw [u6.other _ h2, u5.other _ h1, k4 r hr]
  have e15 : s5.gpr .r15 = BitVec.ofNat 64 (NN s₀ - i) := by
    rw [u5.other _ (by decide), k4 _ (by simp [calleeSaved]), h.r15]
  refine ⟨⟨by omega, by rw [u6.rd, u5.rd, rd4, uf.rd, rdt, erd], by rw [u6.wr, u5.wr, wr4, uf.wr, wrt, ewr],
    by rw [k6 _ (by simp [calleeSaved]) (by decide) (by decide), h.rsp],
    by rw [k6 _ (by simp [calleeSaved]) (by decide) (by decide), h.rbx], ?_,
    by rw [k6 _ (by simp [calleeSaved]) (by decide) (by decide), h.r12],
    by rw [k6 _ (by simp [calleeSaved]) (by decide) (by decide), h.r13],
    by rw [k6 _ (by simp [calleeSaved]) (by decide) (by decide), h.r14],
    by rw [u6.gpr, e15, dec_count hi],
    by rw [u6.mem, u5.mem]; exact F, by rw [u6.mem, u5.mem]; exact K,
    by rw [u6.mem, u5.mem]; exact X, by rw [u6.mem, u5.mem]; exact D⟩, ?_⟩
  · rw [u6.other _ (by decide), u5.gpr, k4 _ (by simp [calleeSaved]), k4 _ (by simp [calleeSaved]),
      h.rbp, h.r14, vAt_succ]
  · rw [z6, e15, dec_zf hi hN]

theorem loop2_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv2 s₀ 0 s) : WP isa (.loop (step2 c) .ne) s (Inv2 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv2 s₀) (fun _ hi _ h => step2_ok hS hp hi h) h

/-! ## Step 3 -/

/-- After `i` iterations of step 3. -/
structure Inv3 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bP s₀
  rbp : s.gpr .rbp = BitVec.ofNat 64 (NN s₀ - 1)
  r12 : s.gpr .r12 = vP s₀
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)
  r15 : s.gpr .r15 = BitVec.ofNat 64 (NN s₀ - i)
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
  refine wp_movm (a := sc s₀ + BitVec.ofNat 64 176) (by rw [BlockMix.ea_at, h.r13])
    (by rw [h.rd, h.wr, hp.rd, hp.wr]
        exact BlockMix.InRegions.of_mem (R := scR s₀) (by simp) (in_s s₀ (by omega)))
    fun a ua => wp_mov fun b ub _ _ => wp_subi fun d ud _ => WP.block_nil ?_
  have ka : a.gpr .r15 = BitVec.ofNat 64 (NN s₀) := by rw [ua.gpr, h.kept.2]
  have k : ∀ r, r ≠ .r15 → r ≠ .rbp → d.gpr r = s.gpr r := fun r h1 h2 => by
    rw [ud.other _ h2, ub.other _ h2, ua.other _ h1]
  have hm : d.mem = s.mem := by rw [ud.mem, ub.mem, ua.mem]
  refine ⟨Nat.zero_le _, by rw [ud.rd, ub.rd, ua.rd, h.rd], by rw [ud.wr, ub.wr, ua.wr, h.wr],
    by rw [k _ (by decide) (by decide), h.rsp], by rw [k _ (by decide) (by decide), h.rbx], ?_,
    by rw [k _ (by decide) (by decide), h.r12], by rw [k _ (by decide) (by decide), h.r13],
    by rw [k _ (by decide) (by decide), h.r14], by rw [ud.other _ (by decide), ub.other _ (by decide), ka]; rfl,
    by rw [hm]; exact h.frame, by rw [hm]; exact h.kept, fun k hk => by rw [hm]; exact h.done k hk, ?_,
    ?_⟩
  · rw [ud.gpr, ub.gpr, ka]
    have := dec_count (n := NN s₀) (k := 0) n1
    simpa using this
  · rw [hm, h.x, Nat.sub_zero]
    exact (roMix_eq _ _ _).symm
  · rw [hm, h.x, Nat.sub_zero, List.drop_zero]
    exact (roMixIndices_eq _ _ _).symm

/-- The address of the low word of `X`'s last 64-byte block. -/
theorem ea_j {s₀ : State} (hp : Pre s₀) (s : State) (hbx : s.gpr .rbx = bP s₀)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)) :
    s.ea { base := .rbx, index := some .r14, disp := -64 } =
      bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64) := by
  have := hp.pos
  simp only [State.ea, hbx, h14]
  rw [ofNat_split (a := 64) (b := 128 * rr s₀) (by omega),
    show BitVec.ofInt 64 (-64) = 0 - BitVec.ofNat 64 64 by decide]
  bv_omega

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
  have vlt := v_lt hp
  have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by have := hp.pos; omega)
  have he' : e ≤ 64 := by
    by_contra hc
    have : 2 ^ 64 < 2 ^ e := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BlockMix.toNat_ofNat_lt (by have := jOf_lt hp m; omega), he, and_mask _ he', jOf, he,
    integerify_mod _ _ hp.pos he']

theorem t_word {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 16 * rr s₀) :
    InRegions s₀.wr (tP s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
  have := hp.s_nw
  rw [hp.wr, BlockMix.add_ofNat]
  exact BlockMix.InRegions.of_mem (R := scR s₀) (by simp) (BlockMix.contains_off (by omega) (by omega))

theorem t_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (tP s₀) (128 * rr s₀) := by
  have := hp.s_nw
  rw [hp.wr]
  exact BlockMix.InRegions.of_mem (R := scR s₀) (by simp) (BlockMix.contains_off (by omega) (by omega))

theorem t_b {s₀ : State} (hp : Pre s₀) :
    Region.Disjoint ⟨tP s₀, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩ :=
  (hp.b_s.symm.sub_left (t_sub hp)).sub_right b_sub'

theorem t_nw {s₀ : State} (hp : Pre s₀) : (tP s₀).toNat + 128 * rr s₀ ≤ 2 ^ 64 := by
  have := hp.s_nw
  rw [BlockMix.toNat_add_ofNat _ (by omega)]
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
    rw [hT, BlockMix.xorBytes_length _ _ (by simp [BlockMix.bytesAt_length]), BlockMix.bytesAt_length]
  have hself : bytesAt (writeBytes s.mem (tP s₀) T) (tP s₀) (128 * rr s₀) = T := by
    have := BlockMix.bytesAt_writeBytes_self s.mem (tP s₀) T (by rw [hl]; exact lt)
    rwa [hl] at this
  have f₂ : Frame [⟨tP s₀, 128 * rr s₀⟩] s.mem (writeBytes s.mem (tP s₀) T) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s.mem (writeBytes s.mem (tP s₀) T) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, t_sub hp⟩
  have hv : ∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀) :=
    fun k hk => by
      rw [call_keeps_v hp f₄ hk, BlockMix.bytesAt_writeBytes_sep _ _
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

theorem sx192 : (192 : BitVec 32).signExtend 64 = BitVec.ofNat 64 192 := by decide

/-- One iteration of step 3. -/
theorem step3_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    WP isa (step3 c) s fun s' => Inv3 s₀ (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀)) := by
  have lt := r_lt hp
  have vlt := v_lt hp
  have pos := hp.pos
  have hN : NN s₀ < 2 ^ 64 := by
    have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hj := jOf_lt hp s.mem
  have e8 : 8 * (16 * rr s₀) = 128 * rr s₀ := by omega
  have hrd : s.rd = s₀.rd := h.rd
  have hwr : s.wr = s₀.wr := h.wr
  unfold step3 jBlock
  refine WP.seq (wp_movm (a := bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) (ea_j hp s h.rbx h.r14)
    (by rw [hrd, hwr, hp.rd, hp.wr]
        exact BlockMix.InRegions.of_mem (R := bR s₀) (by simp)
          (BlockMix.contains_off (by omega) (by omega)))
    fun a ua => wp_and fun b ub => WP.block_nil ?_)
  have hax : b.gpr .rax = BitVec.ofNat 64 (jOf s₀ s.mem) := by
    rw [ub.gpr, ua.gpr, ua.other .rbp (by decide), h.rbp]; exact jOf_eq hp s.mem
  refine WP.seq (wp_mov fun d ud _ _ => wp_mov fun e ue _ _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (mulLoop_ok (j := jOf s₀ s.mem) (c := 128 * rr s₀) (a := vP s₀)
    (by omega) (by rw [ue.other _ (by decide), ud.other _ (by decide), hax])
    (by rw [ue.other _ (by decide), ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h.r12])
    (by rw [ue.gpr, ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.r14]))
    fun f ⟨rdf, wrf, mf, gf, dxf⟩ => ?_)
  have hdx : f.gpr .rdx = vAt s₀ (jOf s₀ s.mem) := by rw [dxf, Nat.mul_comm]
  refine WP.seq (wp_mov fun g1 u1 _ _ => wp_mov fun g2 u2 _ _ => wp_mov fun g3 u3 _ _ =>
    wp_addi fun g4 u4 => wp_mov fun g5 u5 _ _ => wp_shr (by decide) (by decide) fun g6 u6 _ =>
    WP.block_nil ?_)
  have rd6 : g6.rd = s₀.rd := by
    rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, rdf, ue.rd, ud.rd, ub.rd, ua.rd, hrd]
  have wr6 : g6.wr = s₀.wr := by
    rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, wrf, ue.wr, ud.wr, ub.wr, ua.wr, hwr]
  have m6 : g6.mem = s.mem := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, mf, ue.mem, ud.mem, ub.mem, ua.mem]
  have k6 : ∀ r ∈ calleeSaved, g6.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := cs_ne hr
    rw [u6.other _ h4, u5.other _ h4, u4.other _ h6, u3.other _ h6, u2.other _ h3, u1.other _ h2,
      gf _ h1 h5 h4, ue.other _ h4, ud.other _ h5, ub.other _ h1, ua.other _ h1]
  have x6 : g6.gpr .r8 = tP s₀ := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.gpr, u2.other _ (by decide),
      u1.other _ (by decide), gf _ (by decide) (by decide) (by decide), ue.other _ (by decide),
      ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.r13, sx192]
  refine WP.seq (WP.mono (xorLoop_ok (x := bP s₀) (y := vAt s₀ (jOf s₀ s.mem)) (d := tP s₀)
    (n := 16 * rr s₀) (by omega) (by omega)
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.other _ (by decide), u1.gpr, gf _ (by decide) (by decide) (by decide),
      ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide),
      h.rbx])
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr, u1.other _ (by decide), hdx])
    x6
    (by rw [u6.gpr, u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), gf _ (by decide) (by decide) (by decide), ue.other _ (by decide),
      ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.r14,
      shr_ofNat _ lt]; congr 1; omega)
    (fun k hk => by rw [rd6, wr6]; exact b_word hp hk)
    (fun k hk => by rw [rd6, wr6]; exact BlockMix.InRegions.right (v_word hp hj hk))
    (fun k hk => by rw [wr6]; exact t_word hp hk)
    (by rw [e8]; exact t_b hp) (by rw [e8]; exact (vAt_s hp hj).symm.sub_left (t_sub hp)))
    fun t ⟨rdt, wrt, gt, mt⟩ => ?_)
  rw [m6, e8] at mt
  have kt : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3, h4, -, h6⟩ := cs_ne hr
    rw [gt r h1 h2 h3 h6 h4, k6 r hr]
  rw [blockMixTo_eq]
  refine WP.seq (WP.seq (wp_mov fun q1 v1 _ _ => wp_addi fun q2 v2 => ?_))
  have kq : ∀ r ∈ calleeSaved, q2.gpr r = s.gpr r := fun r hr => by
    rw [v2.other _ (cs_ne hr).2.1, v1.other _ (cs_ne hr).2.1, kt r hr]
  refine bm_ok hS hp (A := tP s₀)
    (by rw [v2.gpr, v1.gpr, kt _ (by decide), h.r13, sx192])
    (by rw [kq _ (by decide), h.rbx]) (by rw [kq _ (by decide), h.r13])
    (by rw [kq _ (by decide), h.r14]) (by rw [kq _ (by decide), h.rsp])
    (by rw [v2.rd, v1.rd, rdt, rd6]) (by rw [v2.wr, v1.wr, wrt, wr6])
    (t_b hp) (t_w hp) (hp.stk_s.sub_right (t_sub hp)) (t_nw hp)
    (BlockMix.InRegions.right (t_in hp)) fun s4 rd4 wr4 cs4 f4 b4 => ?_
  rw [v2.mem, v1.mem, mt] at f4 b4
  obtain ⟨F, K, V, X, J⟩ := mem3_ok hp hi h f4 b4
  have k4 : ∀ r ∈ calleeSaved, s4.gpr r = s.gpr r := fun r hr => by rw [cs4 r hr, kq r hr]
  refine wp_subi fun s5 u5 z5 => WP.block_nil ?_
  have k5 : ∀ r ∈ calleeSaved, r ≠ .r15 → s5.gpr r = s.gpr r := fun r hr h1 => by
    rw [u5.other _ h1, k4 r hr]
  have e15 : s4.gpr .r15 = BitVec.ofNat 64 (NN s₀ - i) := by rw [k4 _ (by decide), h.r15]
  refine ⟨⟨by omega, by rw [u5.rd, rd4, v2.rd, v1.rd, rdt, rd6],
    by rw [u5.wr, wr4, v2.wr, v1.wr, wrt, wr6],
    by rw [k5 _ (by decide) (by decide), h.rsp], by rw [k5 _ (by decide) (by decide), h.rbx],
    by rw [k5 _ (by decide) (by decide), h.rbp], by rw [k5 _ (by decide) (by decide), h.r12],
    by rw [k5 _ (by decide) (by decide), h.r13], by rw [k5 _ (by decide) (by decide), h.r14],
    by rw [u5.gpr, e15, dec_count hi],
    by rw [u5.mem]; exact F, by rw [u5.mem]; exact K, by rw [u5.mem]; exact V,
    by rw [u5.mem]; exact X, by rw [u5.mem]; exact J⟩, by rw [z5, e15, dec_zf hi hN]⟩

theorem loop3_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv3 s₀ 0 s) : WP isa (.loop (step3 c) .ne) s (Inv3 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv3 s₀) (fun _ hi _ h => step3_ok hS hp hi h) h

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv3 s₀ (NN s₀) s) :
    WP isa (.block rmEpilogue) s fun s' => s'.mem = s.mem ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) := by
  have hin : ∀ d, d + 8 ≤ 256 → ∀ t : State, t.rd = s.rd → t.wr = s.wr →
      InRegions (t.rd ++ t.wr) (sc s₀ + BitVec.ofNat 64 d) 8 := fun d hd t hr hw => by
    rw [hr, hw, h.rd, h.wr, hp.rd, hp.wr]
    exact BlockMix.InRegions.of_mem (R := scR s₀) (by simp) (in_s s₀ hd)
  have sv : ∀ p ∈ rmSaved, s.mem.readW (sc s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1 := h.kept.1
  simp only [rmEpilogue, rmSaved, List.map_cons, List.map_nil]
  refine wp_movm (by rw [BlockMix.ea_at, h.r13]) (hin 128 (by omega) _ rfl rfl) fun a ua => ?_
  refine wp_movm (by rw [BlockMix.ea_at, ua.other _ (by decide), h.r13])
    (hin 136 (by omega) _ ua.rd ua.wr) fun b ub => ?_
  refine wp_movm (by rw [BlockMix.ea_at, ub.other _ (by decide), ua.other _ (by decide), h.r13])
    (hin 144 (by omega) _ (ub.rd.trans ua.rd) (ub.wr.trans ua.wr)) fun c uc => ?_
  refine wp_movm (by rw [BlockMix.ea_at, uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.r13])
    (hin 152 (by omega) _ (uc.rd.trans (ub.rd.trans ua.rd)) (uc.wr.trans (ub.wr.trans ua.wr)))
    fun d ud => ?_
  refine wp_movm (by rw [BlockMix.ea_at, ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), h.r13])
    (hin 160 (by omega) _ (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd)))
      (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr)))) fun e ue => ?_
  refine wp_movm (by rw [BlockMix.ea_at, ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.r13])
    (hin 168 (by omega) _ (ue.rd.trans (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd))))
      (ue.wr.trans (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr))))) fun f uf => WP.block_nil ?_
  have hm : f.mem = s.mem := by rw [uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
  refine ⟨hm, fun r hr => ?_⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.gpr, sv (.rbx, 128) (by simp [rmSaved])]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.gpr, ua.mem, sv (.rbp, 136) (by simp [rmSaved])]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.rsp]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.gpr, ub.mem, ua.mem, sv (.r12, 144) (by simp [rmSaved])]
  · rw [uf.gpr, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, sv (.r13, 168) (by simp [rmSaved])]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.mem, ub.mem, ua.mem,
      sv (.r14, 152) (by simp [rmSaved])]
  · rw [uf.other _ (by decide), ue.gpr, ud.mem, uc.mem, ub.mem, ua.mem,
      sv (.r15, 160) (by simp [rmSaved])]

/-! ## The whole function -/

theorem correct {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (roMixWith c) s₀ fun s' =>
      gprPreserved s₀ s' ∧ Proof.Scrypt.roMixX86_64.post s₀ s' := by
  unfold roMixWith
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine start_ok hp h₁ fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (loop2_ok hS hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (mid_ok hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (loop3_ok hS hp h₄) fun s₅ h₅ => ?_)
  refine WP.mono (restore_ok hp h₅) fun s' ⟨hm', hg'⟩ => ?_
  refine ⟨⟨hg', ?_⟩, ?_⟩
  · rw [hm']
    refine h₅.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_b
    · exact hp.ret_v
    · exact hp.ret_s
    · exact ret_stk s₀
  · show bytesAt s'.mem (bP s₀) (128 * rr s₀) = roMix (rr s₀) (NN s₀) (B s₀)
    rw [hm', ← h₅.x, Nat.sub_self]
    rfl

end VG.Proof.Scrypt.X86_64.RoMix
