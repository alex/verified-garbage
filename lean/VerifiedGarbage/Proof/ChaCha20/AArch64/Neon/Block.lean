import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.Rounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Block
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem

namespace VG.Proof.ChaCha20.AArch64.Neon

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon
open VG.Spec.ChaCha20 (stateAt innerBlock)

theorem rowReg_inj {i j : Nat} (hi : i < 4) (hj : j < 4) (h : rowReg i = rowReg j) : i = j :=
  (show ∀ i < 4, ∀ j < 4, rowReg i = rowReg j → i = j by decide) i hi j hj h

theorem rowReg_ne_v4 {i : Nat} (hi : i < 4) : rowReg i ≠ .v4 :=
  (show ∀ i < 4, rowReg i ≠ .v4 by decide) i hi

theorem Pre.in_row {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 4) (ws : List Region) :
    InRegions (s₀.rd ++ ws) (st s₀ + BitVec.ofNat 64 (16 * i)) 16 :=
  ⟨stR s₀, by simp [hp.rd], contains_off (by omega) (by omega)⟩

theorem Pre.out_row {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 4) :
    InRegions s₀.wr (buf s₀ + BitVec.ofNat 64 (16 * i)) 16 :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by omega) (by omega)⟩

theorem read_row {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [outR s₀] s₀.mem m)
    {i e : Nat} (hi : i < 4) (he : e < 4) :
    vword (m.read (st s₀ + BitVec.ofNat 64 (16 * i)) 16) e = (V s₀)[4 * i + e]'(by omega) := by
  rw [vword_read16 _ _ he, Offset.add_add, show 16 * i + 4 * e = 4 * (4 * i + e) by omega]
  exact hp.read_st hf (by omega)

structure LI (s₀ : State) (i : Nat) (s : State) : Prop where
  loaded : ∀ j (hj : j < 4), j < i → ∀ e (he : e < 4),
    vword (s.v (rowReg j)) e = (V s₀)[4 * j + e]'(by omega)
  keeps : Keeps s₀ s

theorem load_step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 4) {s : State} (h : LI s₀ i s) :
    WP isa (.block [.ldrq (rowReg i) .x0 (16 * i)]) s (LI s₀ (i + 1)) := by
  have ha : 16 * i % 16 = 0 ∧ 16 * i < 4096 * 16 := by omega
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [h.keeps.rd, h.keeps.wr, h.keeps.gpr]; exact Pre.in_row hp hi _
  apply WP.of_runBlock
  simp only [runBlock_cons, runBlock_nil, exec, addr, ha, and_self, ite_true, State.load, hin,
    Option.bind_some, Option.map_some, isa, runStep_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj hji e he => ?_, h.keeps.gpr, h.keeps.mem, h.keeps.rd, h.keeps.wr, h.keeps.sp⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hji with hji | rfl
  · rw [RegUpd.v_setV_of_ne _ _ (fun eq => absurd (rowReg_inj hj hi eq) (by omega))]
    exact h.loaded j hj hji e he
  · rw [RegUpd.v_setV_self, h.keeps.gpr, h.keeps.mem]
    exact read_row hp (Frame.refl _ _) hi he

theorem load_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block load) s₀ fun s => Holds (V s₀) s ∧ Keeps s₀ s := by
  have h : LI s₀ 0 s₀ := ⟨fun _ _ h => absurd h (by omega), Keeps.refl s₀⟩
  have hl : WP isa (.block load) s₀ (LI s₀ 4) := by
    unfold load
    rw [List.map_eq_flatMap]
    exact wp_range_flatMap (M := isa) (LI s₀) (fun i _ hi h => load_step hp hi h) 4 (by decide) s₀ h
  exact hl.mono fun _ h => ⟨fun r hr e he => h.loaded r hr hr e he, h.keeps⟩

theorem read16_write16 (m : Mem) (p : Addr) (v : BitVec 128) :
    (m.write p 16 v).read p 16 = v := by
  simpa only [Mem.readW, Mem.writeW, BitVec.setWidth_eq] using
    Mem.readW_writeW_self m p 16 v (by decide)

structure FI (s₀ : State) (R : CState) (i : Nat) (s : State) : Prop where
  done : ∀ j (hj : j < 4), j < i → ∀ e (he : e < 4),
    vword (s.mem.read (buf s₀ + BitVec.ofNat 64 (16 * j)) 16) e =
      R[4 * j + e]'(by omega) + (V s₀)[4 * j + e]'(by omega)
  rest : ∀ j (hj : j < 4), i ≤ j → ∀ e (he : e < 4),
    vword (s.v (rowReg j)) e = R[4 * j + e]'(by omega)
  frame : Frame [outR s₀] s₀.mem s.mem
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem finish_step {s₀ : State} (hp : Pre s₀) {R : CState} {i : Nat} (hi : i < 4)
    {s : State} (h : FI s₀ R i s) :
    WP isa (.block (finishRow i)) s (FI s₀ R (i + 1)) := by
  have ha : 16 * i % 16 = 0 ∧ 16 * i < 4096 * 16 := by omega
  have hn := rowReg_ne_v4 hi
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [h.rd, h.wr, h.gpr]; exact Pre.in_row hp hi _
  have hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [h.wr, h.gpr]; exact Pre.out_row hp hi
  apply WP.of_runBlock
  simp only [finishRow, runBlock_cons, runBlock_nil, exec, addr, ha, and_self, ite_true,
    State.load, hin, State.store, hout, Option.bind_some, Option.map_some, isa,
    runStep_some, Option.some.injEq, exists_eq_left', VOp.eval,
    RegUpd.v_setV, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV,
    RegUpd.wr_setV, hn, ite_false]
  refine ⟨fun j hj hji e he => ?_, fun j hj hij e he => ?_, ?_, h.gpr, h.rd, h.wr, h.sp⟩
  · rw [h.gpr]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hji with hji | rfl
    · rw [Mem.read_write_sep (Offset.sep (buf s₀) (by omega) (by omega) (by omega)) (by decide)]
      exact h.done j hj hji e he
    · rw [read16_write16, vword_map2 _ _ _ he, h.rest j hj (by omega) e he,
        read_row hp h.frame hj he]
  · have hne : rowReg j ≠ rowReg i := fun eq => absurd (rowReg_inj hj hi eq) (by omega)
    simp only [RegUpd.v_setV, hne, rowReg_ne_v4 hj, ite_false]
    exact h.rest j hj (by omega) e he
  · rw [h.gpr]
    exact h.frame.write (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa block s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.ChaCha20.blockAArch64.post s₀ s' := by
  refine WP.seq ((load_ok hp).mono fun s₁ ⟨h₁, k₁⟩ => ?_)
  refine WP.seq ((rounds_ok h₁ 10).mono fun s₂ ⟨h₂, k₂⟩ => ?_)
  have k := k₁.trans k₂
  have hf : FI s₀ (Rs s₀) 0 s₂ := ⟨fun _ _ h => absurd h (by omega),
    fun j hj _ e he => h₂ j hj e he, k.mem ▸ Frame.refl _ _, k.gpr, k.rd, k.wr, k.sp⟩
  have hfinish : WP isa (.block finish) s₂ (FI s₀ (Rs s₀) 4) :=
    wp_range_flatMap (M := isa) (FI s₀ (Rs s₀)) (fun i _ hi h => finish_step hp hi h)
      4 (by decide) s₂ hf
  refine hfinish.mono fun s' h' => ⟨fun r _ => congrFun h'.gpr r, ?_⟩
  apply block_post
  intro j hj
  have h := h'.done (j / 4) (by omega) (by omega) (j % 4) (by omega)
  rw [vword_read16 _ _ (by omega), Offset.add_add,
    show 16 * (j / 4) + 4 * (j % 4) = 4 * j by omega] at h
  simpa only [show 4 * (j / 4) + j % 4 = j by omega] using h

theorem block_correct (s : State) (hs : Proof.ChaCha20.blockAArch64.pre s) :
    ∃ t s', Exec isa block s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.blockAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩

theorem block_verified :
    Verified AArch64.target block (Spec.ChaCha20.blockContract AArch64.abi) := by
  refine Verified.of_correct block_correct ?_ (by
    sig_implies [Spec.ChaCha20.blockContract, Spec.ChaCha20.blockSig, AArch64.abi, AArch64.argRegs,
      Proof.ChaCha20.blockAArch64] [satState] using satState)
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> assumption

end VG.Proof.ChaCha20.AArch64.Neon
