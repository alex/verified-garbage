import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.Sample.Signs
import VerifiedGarbage.Impl.MlDsa.X86.Sample.Ball

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_sample_in_ball`, the state of the loop

The body is the SHAKE256 output of `c̃` at `scratch + 840` (`sponge_piece`),
`c` zeroed (`zero_piece`), the setup of the loop (`setup_piece`): `i = 256 -
τ`, and the sign bits `S` (the first 8 bytes of the output, as a little-endian
integer) in the argument slots of `len` and `tau` as two words; then the 264
iterations of the loop (`BallLoop.lean`). Iteration `k` starts from the state
`st B τ k = bFold τ (signs X) (0, 256 - τ) ((X.drop 8).take k)` of
`SampleInBall`'s loop (`Proof/MlDsa/Sample/Ball.lean`): the polynomial at `c`,
`i` in `edi`, and the `t = i + τ - 256` signs used shifted out of the words
(`BI`).
-/

namespace VG.Proof.MlDsa.X86.Sample.Ball

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (argOp bZero bSetup qImm sponge outOff)
open VG.Spec.MlDsa (Zq q H n ofInt coeffAt IPoly ballParams)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86.Sample (cR E1)

/-- The layout: `sampleInBall(ctilde, len, tau, c, scratch)`, `len` bytes of
`c̃`, 272 bytes of SHAKE256. -/
def L : Lay := { nA := 5, iA := 3, iS := 4, rate := 136, outlen := 272, mlen := none }

theorem hL : L.Ok :=
  ⟨by decide, by decide, by decide, by decide, by decide, fun k hk => by simp [L] at hk,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- `τ`. -/
abbrev τ (s₀ : State) : Nat := (arg s₀ 2).toNat

/-- The precondition. -/
def QPre (s₀ : State) : Prop := Pre L s₀ ∧ ((arg s₀ 1).toNat, τ s₀) ∈ ballParams

/-- The pointers, `esp` and `c̃` agree. -/
def QPub (s₀ s₀' : State) : Prop := PubP L s₀ s₀' ∧ L.Msg s₀ = L.Msg s₀'

theorem QPre.τ_le {s₀ : State} (hp : QPre s₀) : τ s₀ ≤ 60 := by
  have h := hp.2
  simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega

theorem QPre.len {s₀ : State} (hp : QPre s₀) : (arg s₀ 1).toNat < 136 := by
  have h := hp.2
  simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega

/-! ## The loop of `SampleInBall`, from the message -/

/-- The output. -/
abbrev Xb (B : List Byte) : List Byte := H B 272

/-- The sign bits, as an integer. -/
abbrev Sg (B : List Byte) : Nat := leNat ((Xb B).take 8)

/-- The state of the loop after `k` iterations. -/
abbrev st (B : List Byte) (τ : Nat) (k : Nat) : IPoly × Nat :=
  bFold τ (signs (Xb B)) (Vector.replicate n 0, 256 - τ) (((Xb B).drop 8).take k)

/-- The byte of iteration `k`. -/
abbrev jb (B : List Byte) (k : Nat) : Byte := (Xb B).getD (8 + k) 0

/-- The signs used after `k` iterations. -/
abbrev tu (B : List Byte) (τ k : Nat) : Nat := (st B τ k).2 + τ - 256

theorem out_eq (s₀ : State) : L.out s₀ = Xb (L.Msg s₀) := (H_eq _ _).symm

theorem Xb_length (B : List Byte) : (Xb B).length = 272 := H_length _ _

theorem st_zero (B : List Byte) (τ : Nat) : st B τ 0 = (Vector.replicate n 0, 256 - τ) := by
  simp [st, bFold]

theorem st_succ (B : List Byte) (τ : Nat) {k : Nat} (hk : k < 264) :
    st B τ (k + 1) = bStep τ (signs (Xb B)) (st B τ k) (jb B k) := by
  have hl : ((Xb B).drop 8).length = 264 := by rw [List.length_drop, Xb_length]
  simp only [st]
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [hl]; exact hk), Option.toList_some, bFold_snoc]
  congr 1
  rw [jb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [Xb_length]; omega), Option.getD_some,
    List.getElem_drop]

theorem st_le (B : List Byte) (τ k : Nat) : (st B τ k).2 ≤ 256 := bFold_le (by simp [n]) _

theorem st_ge (B : List Byte) (τ k : Nat) : 256 - τ ≤ (st B τ k).2 :=
  bFold_ge (Vector.replicate n 0, 256 - τ) _

/-! ## The state of the loop -/

/-- Iteration `k`, with the loop's state `S`. -/
structure BI (s₀ : State) (k : Nat) (S : IPoly × Nat) (s : State) : Prop extends Base L s₀ s where
  out : ∀ p < 272, s.mem (L.sA s₀ + BitVec.ofNat 64 (840 + p)) = (Xb (L.Msg s₀)).getD p 0
  esi : s.gpr .esi = L.sP s₀ + BitVec.ofNat 32 (848 + k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (264 - k)
  ebp : s.gpr .ebp = L.aP s₀
  edi : s.gpr .edi = BitVec.ofNat 32 S.2
  poly : ∀ j < 256, coeffAt s.mem (L.aA s₀) j = zw (ofInt S.1[j]!)
  lo : s.mem.readW (argAddr s₀ 1) 32 = BitVec.ofNat 32 (Sg (L.Msg s₀) / 2 ^ (S.2 + τ s₀ - 256))
  hi : s.mem.readW (argAddr s₀ 2) 32 = BitVec.ofNat 32 (Sg (L.Msg s₀) / 2 ^ (S.2 + τ s₀ - 256 + 32))

/-! ## `c` zeroed -/

/-- After `k` words of `c`. -/
structure ZI (s₀ : State) (k : Nat) (s : State) : Prop extends Out L s₀ s where
  ebp : s.gpr .ebp = L.aP s₀
  eax : s.gpr .eax = 0
  edi : s.gpr .edi = L.aP s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  zero : ∀ j < k, coeffAt s.mem (L.aA s₀) j = 0

theorem zinit_piece : Piece QPre QPub (Out L) (ZI · 0)
    (.block [.mov .ebp (.mem (argOp 3)), .mov .eax (.imm 0), .mov .edi (.reg .ebp), .mov .ecx (.imm 256)]) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · have a₃ := h.argEa (i := 3)
    have i₃ := h.argIn hp.1 (i := 3) (by decide)
    have v₃ := h.args 3 (by decide)
    simp only [Nat.reduceMul, Nat.reduceAdd] at a₃
    apply WP.of_runBlock
    simp (config := {decide := true}) only [argOp, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₃, i₃, v₃, ite_true, ite_false,
      Option.some.injEq, exists_eq_left']
    exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, h.out⟩, by simp; rfl, by simp,
      by simp; rfl, by simp, fun j hj => absurd hj (by omega)⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.1.e1]

theorem zstep {s₀ : State} (hp : QPre s₀) {k : Nat} (hk : k < 256) {s : State} (h : ZI s₀ k s) :
    WP isa (.block [.store (at_ .edi 0) .eax, .alu .add .edi (.imm 4), .alu .sub .ecx (.imm 1)]) s
      fun s' => ZI s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have ha := hp.1.a_fit
  have ea : (L.aP s₀ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (L.aA s₀) k := by
    rw [ea_add (by simp only [L] at ha ⊢; omega)]; rfl
  have hin : InRegions s.wr (coeffAddr (L.aA s₀) k) 4 := hp.1.inA h.wr hk
  have fa : Frame [L.aR s₀] s.mem (s.mem.writeW (coeffAddr (L.aA s₀) k) (0 : BitVec 32)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hk)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.ea, State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some, h.edi, h.eax, ea, hin,
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame.writeW (r := L.aR s₀) (by simp) _ (coeff_contains _ hk)⟩,
    args_frame hp.1 h.args fa (by simp only [List.mem_singleton, forall_eq]; exact hp.1.a_g.symm),
    by simp [h.esi]⟩, fun p hp' => ?_⟩, by simp [h.ebp], by simp [h.eax], ?_, ?_, fun j hj => ?_⟩, ?_⟩
  · refine (fa _ fun r hr hc => ?_).trans (h.out p hp')
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.1.a_s _ hc ((hp.1.sub_s (o := 840 + p) (n := 1) (by simp only [L] at hp' ⊢; omega)) _
      (Region.contains_self _ _))
  · simp only [ite_true]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx]
    exact cnt_next hk
  · rw [coeffAt_writeW _ _ (by omega) hk]
    by_cases e : k = j
    · rw [ifT e]
    · rw [ifF e]; exact h.zero j (by omega)
  · simp only [eval, h.ecx]
    exact cnt_ne hk (by omega)

theorem zero_piece : Piece QPre QPub (Out L) (ZI · 256) bZero :=
  Piece.seq zinit_piece (Piece.countLoop (by decide) (fun k s₀ s => ZI s₀ k s) [.edi]
    (fun k hk s₀ s hp h => zstep hp hk h)
    (fun k _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [h.edi, h'.edi, hq.1.aP hL]) (by taint_decide))

/-! ## The setup of the loop -/

theorem argAddr_eq {s₀ : State} (hp : QPre s₀) {i : Nat} (hi : i < 5) :
    argAddr s₀ i = (E0 s₀).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
  ea_off (by have := hp.1.sp'; simp only [L, E0] at this ⊢; omega)

/-- The two argument slots of the sign bits, apart. -/
theorem slots_sep {s₀ : State} (hp : QPre s₀) : Mem.Sep (argAddr s₀ 1) 4 (argAddr s₀ 2) 4 := by
  rw [argAddr_eq hp (by decide), argAddr_eq hp (by decide)]
  exact Offset.sep _ (by omega) (by omega) (by omega)

theorem setup_piece : Piece QPre QPub (ZI · 256) (fun s₀ s => BI s₀ 0 (st (L.Msg s₀) (τ s₀) 0) s)
    (.block bSetup) := by
  refine Piece.taint [.esp, .esi] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by taint_decide)
  · have hs := hp.1.s_fit
    have a₁ := h.argEa (i := 1)
    have a₂ := h.argEa (i := 2)
    have i₂ := h.argIn hp.1 (i := 2) (by decide)
    have v₂ := h.args 2 (by decide)
    have w₁ := h.argInW hp.1 (i := 1) (by decide)
    have w₂ := h.argInW hp.1 (i := 2) (by decide)
    simp only [Nat.reduceMul, Nat.reduceAdd] at a₁ a₂
    have e0 : (L.sP s₀ + BitVec.ofNat 32 840).setWidth 64 = L.sA s₀ + BitVec.ofNat 64 840 := hp.1.off_eq (by omega)
    have e4 : (L.sP s₀ + BitVec.ofNat 32 844).setWidth 64 = L.sA s₀ + BitVec.ofNat 64 844 := hp.1.off_eq (by omega)
    have r0 := hp.1.inS' h.wr (o := 840) (n := 4) (by omega)
    have r4 := hp.1.inS' h.wr (o := 844) (n := 4) (by omega)
    have hb : ∀ b < 8, s.mem (L.sA s₀ + BitVec.ofNat 64 840 + BitVec.ofNat 64 b) = (Xb (L.Msg s₀)).getD b 0 :=
      fun b hb => by rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.out b (by simp only [L]; omega), out_eq]
    have vlo := readW_lo s.mem _ _ hb
    have vhi := readW_hi s.mem _ _ hb
    rw [BitVec.add_assoc, show BitVec.ofNat 64 840 + (4 : BitVec 64) = BitVec.ofNat 64 844 from rfl] at vhi
    have hτ := hp.τ_le
    have fin : ∀ s' : State, s'.gpr .esp = s.gpr .esp → s'.gpr .esi = L.sP s₀ + BitVec.ofNat 32 848 →
        s'.gpr .ecx = BitVec.ofNat 32 264 → s'.gpr .ebp = s.gpr .ebp → s'.gpr .edi = 256 - arg s₀ 2 →
        s'.rd = s.rd → s'.wr = s.wr →
        s'.mem = (s.mem.writeW (argAddr s₀ 1) (BitVec.ofNat 32 (Sg (L.Msg s₀) / 2 ^ 0))).writeW (argAddr s₀ 2)
          (BitVec.ofNat 32 (Sg (L.Msg s₀) / 2 ^ (0 + 32))) →
        BI s₀ 0 (st (L.Msg s₀) (τ s₀) 0) s' := by
      intro s' e1 e2 e3 e4 e5 e6 e7 e8
      have f₁ : Frame [L.gR s₀] s.mem s'.mem := by
        rw [e8]
        exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (arg_contains (n := 5) (by decide) hp.1.sp')).writeW
          (List.mem_singleton_self _) _ (arg_contains (n := 5) (by decide) hp.1.sp')
      rw [st_zero]
      refine ⟨⟨by rw [e1, h.esp], by rw [e6, h.rd], by rw [e7, h.wr], h.frame.trans (f₁.mono (by simp))⟩,
        fun p hp' => ?_, e2, e3, by rw [e4, h.ebp], ?_, fun j hj => ?_, ?_, ?_⟩
      · rw [f₁.bytes (R := ⟨L.sA s₀, 2048⟩) (by simp only [List.mem_singleton, forall_eq]; exact hp.1.s_g)
          (show (2048 : Nat) ≤ 2 ^ 64 by decide) (show 840 + p < 2048 by omega)]
        rw [h.out p hp', out_eq]
      · rw [e5]
        exact eq_ofNat_of_toNat (by
          rw [BitVec.toNat_sub, show (256 : BitVec 32).toNat = 256 from rfl]
          simp only [τ] at hτ ⊢
          omega)
      · rw [coeffAt_eq, f₁.readW (coeff_contains _ hj) (by simp only [List.mem_singleton, forall_eq]; exact hp.1.a_g)
          (by decide), ← coeffAt_eq, h.zero j hj,
          getElem!_pos (Vector.replicate n (0 : Int)) j (by simp only [n]; omega), Vector.getElem_replicate]
        decide
      · rw [e8, Mem.readW_writeW_sep (slots_sep hp) (by decide), Mem.readW_writeW_self32,
          show 256 - τ s₀ + τ s₀ - 256 = 0 by omega]
      · rw [e8, Mem.readW_writeW_self32, show 256 - τ s₀ + τ s₀ - 256 = 0 by omega]
    apply WP.of_runBlock
    simp (config := {decide := true}) only [bSetup, argOp, outOff, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, h.esi, a₁, a₂, i₂, v₂, w₁, w₂, e0, e4, r0, r4, vlo, vhi, Nat.reduceAdd,
      ite_true, ite_false, Option.some.injEq, exists_eq_left']
    exact fin _ (by simp) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.esp, h'.esp, hq.1.e1]
    · rw [h.esi, h'.esi, hq.1.sP hL]

end VG.Proof.MlDsa.X86.Sample.Ball
