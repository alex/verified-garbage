import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Rounds

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Spec.ChaCha20 (innerBlock)
open VG.Proof.ChaCha20.AArch64 (Words not_words_x1)

variable {sve : Bool}

/-- Arithmetic state during the counted phase; x1 holds its public counter. -/
structure PhaseInv (blocks : Nat → CState) (v : CState) (s₀ s : State) (i : Nat) : Prop where
  vec : N (VG.Proof.ChaCha20.AArch64.Rows6.pack
    (fun b => Nat.repeat innerBlock i (blocks b))) s
  scalar : C (Nat.repeat (fun x => innerBlock (innerBlock x)) i v) s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → r ≠ .x1 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  table : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table

theorem PhaseInv.writeCounter {blocks : Nat → CState} {v : CState} {s₀ s : State} {i : Nat}
    (h : PhaseInv blocks v s₀ s i) (c : BitVec 64) :
    PhaseInv blocks v s₀ (s.write .x .x1 c) i := by
  refine ⟨h.vec,?_,h.mem,h.rd,h.wr,?_,h.sp,h.table⟩
  · intro k hk
    rw [RegUpd.gpr_write_of_ne s .x c (by
      intro he; exact not_words_x1 ⟨k,hk,he.symm⟩)]
    exact h.scalar k hk
  · intro r hr hn
    rw [RegUpd.gpr_write_of_ne s .x c hn]
    exact h.keep r hr hn

theorem phase_loop_ok {blocks : Nat → CState} {v : CState} {s₀ s : State}
    (h : PhaseInv blocks v s₀ s 0) (hx : s.gpr .x1 = 5) :
    WP isa (.loop (.seq (parallelRound sve) (.block [.subImm .x .x1 .x1 1])) (.nonzero .x .x1)) s
      (fun u => PhaseInv blocks v s₀ u 5) := by
  let Inv : Nat → State → Prop := fun n a =>
    ∃ i, i < 5 ∧ n = 5 - i ∧ PhaseInv blocks v s₀ a i ∧
      a.gpr .x1 = BitVec.ofNat 64 (5 - i)
  have hstep : ∀ n a, Inv n a → WP isa
      (.seq (parallelRound sve) (.block [.subImm .x .x1 .x1 1])) a (fun u =>
      (eval (.nonzero .x .x1) u = some false ∧ PhaseInv blocks v s₀ u 5) ∨
      (eval (.nonzero .x .x1) u = some true ∧ ∃ m < n, Inv m u)) := by
    rintro n a ⟨i,hi,rfl,ha,hcount⟩
    apply WP.seq
    refine (parallelRound_ok ha.vec ha.scalar ha.table).mono fun b ⟨hb,hc,hsp,ht⟩ => ?_
    have hnext : PhaseInv blocks v s₀ b (i + 1) :=
      ⟨hb,hc.holds,hc.mem.trans ha.mem,hc.rd.trans ha.rd,hc.wr.trans ha.wr,
        fun r hr hn => (hc.keep r hr).trans (ha.keep r hr hn),hsp.trans ha.sp,ht⟩
    have hbc : b.gpr .x1 = BitVec.ofNat 64 (5 - i) :=
      (hc.keep _ not_words_x1).trans hcount
    let u := b.write .x .x1 (b.gpr .x1 - BitVec.ofNat 64 1)
    have hu := hnext.writeCounter (b.gpr .x1 - BitVec.ofNat 64 1)
    have huc : u.gpr .x1 = BitVec.ofNat 64 (5 - (i + 1)) := by
      rw [RegUpd.gpr_write_self,BitVec.setWidth_eq,hbc,
        Offset.ofNat_sub_ofNat (by omega : 1 ≤ 5 - i)]
      simp only [Nat.sub_sub]
    apply WP.block_cons_iff.mpr
    refine ⟨u,?_,WP.block_nil ?_⟩
    · simpa only [State.read,BitVec.setWidth_eq] using
        exec_subImm_x (s := b) (d := .x1) (n := .x1) (imm := 1) (by decide)
    · have he : eval (.nonzero .x .x1) u = some (BitVec.ofNat 64 (5 - (i + 1)) != 0) := by
        simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,huc]
      by_cases hl : i + 1 = 5
      · exact .inl ⟨by rw [he,hl]; rfl,hl ▸ hu⟩
      · have hn : BitVec.ofNat 64 (5 - (i + 1)) ≠ 0 := by
          intro hz
          have hz' := congrArg BitVec.toNat hz
          rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 5 - (i + 1) < 2 ^ 64)] at hz'
          change 5 - (i + 1) = 0 at hz'
          omega
        exact .inr ⟨by rw [he]; simpa using hn,
          5 - (i + 1),by omega,i + 1,by omega,rfl,hu,huc⟩
  exact WP.loop (M := isa) Inv hstep 5 s ⟨0,by decide,rfl,h,hx⟩

theorem counted_phase_ok {blocks : Nat → CState} {v : CState} {s : State} {restore : Reg}
    (hn : N (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks) s) (hc : C v s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table)
    (hr : ¬ Words restore) (hr1 : restore ≠ .x1)
    (hx : s.gpr .x1 = s.gpr restore) :
    WP isa (phase sve restore) s fun u =>
      N (VG.Proof.ChaCha20.AArch64.Rows6.pack
        (fun b => Nat.repeat innerBlock 5 (blocks b))) u ∧
      RI (Nat.repeat innerBlock 10 v) s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  unfold phase
  apply WP.seq
  have hi : PhaseInv blocks v s s 0 := ⟨hn,hc,rfl,rfl,rfl,fun _ _ _ => rfl,rfl,ht⟩
  apply WP.block_cons_iff.mpr
  refine ⟨s.write .x .x1 5,?_,WP.block_nil ?_⟩
  · rfl
  · apply WP.seq
    refine (phase_loop_ok (hi.writeCounter 5) (by rw [RegUpd.gpr_write_self,BitVec.setWidth_eq])).mono
      fun a ha => ?_
    apply WP.block_cons_iff.mpr
    refine ⟨a.write .x .x1 (a.gpr restore),?_,WP.block_nil ?_⟩
    · simpa only [State.read,BitVec.setWidth_eq,BitVec.add_zero] using
        exec_addImm_x (s := a) (d := .x1) (n := restore) (imm := 0) (by decide)
    · have hu := ha.writeCounter (a.gpr restore)
      have hs := hu.scalar
      have he (f : CState → CState) (x : CState) :
          Nat.repeat (fun x => f (f x)) 5 x = Nat.repeat f 10 x := rfl
      rw [he innerBlock v] at hs
      refine ⟨hu.vec,⟨hs,hu.mem,hu.rd,hu.wr,?_⟩,hu.sp,hu.table⟩
      intro r hnr
      by_cases h1 : r = .x1
      · subst r
        rw [RegUpd.gpr_write_self,BitVec.setWidth_eq,ha.keep restore hr hr1,hx]
      · exact hu.keep r hnr h1

end VG.Proof.ChaCha20.AArch64.Mixed8
