import VerifiedGarbage.Impl.CmacAes.AArch64.Aese
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
import VerifiedGarbage.Proof.CmacAes.AArch64.Verified

/-! The register-resident CMAC loop, proven against the existing shared
contract. Memory is unchanged until the final chaining value is stored. -/
namespace VG.Proof.CmacAes.AArch64.Aese
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese (kreg aes)
open VG.Impl.CmacAes.AArch64.Aese

abbrev schedule (s : State) := Spec.Aes.bytesAt s.mem (W s) (16 * (R s + 1))
def bytes (v : BitVec 128) : List Byte := (st v).toList

theorem bytes_read (m : Mem) (p : Addr) : bytes (m.readW p 128) = Spec.Aes.bytesAt m p 16 := by
  apply List.ext_getElem
  · simp [bytes, Spec.Aes.bytesAt]
  · intro i hi hj
    simpa [bytes, st, Spec.Aes.bytesAt] using vbyte_readW m p (i := i) (by simpa [bytes] using hi)

theorem bytes_xor (a b : BitVec 128) : bytes (a ^^^ b) = Spec.Cmac.xor (bytes a) (bytes b) := by
  apply List.ext_getElem
  · simp [bytes, Spec.Cmac.xor]
  · intro i hi hj
    simpa [bytes, st, Spec.Cmac.xor] using vbyte_xor a b i

theorem state_bytes (v : BitVec 128) : (Vector.ofFn fun i : Fin 16 => (bytes v).getD i 0) = st v := by
  apply st_ext
  intro i hi
  simp [bytes, Vector.getD, hi]

structure PlainInv (s₀ : State) (k : Nat) (s : State) : Prop where
  keys : Keys (R s₀) (schedule s₀) s
  x2 : s.gpr .x2 = St s₀
  x3 : s.gpr .x3 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  x4 : s.gpr .x4 = BitVec.ofNat 64 (N s₀ - k)
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : bytes (s.v .v0) = Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem (St s₀) 16) ((blks s₀).take k)

theorem key_in {s₀ : State} (hp : UPre s₀) {o : Nat} (h : o + 16 ≤ 240) :
    InRegions (s₀.rd ++ s₀.wr) (W s₀ + BitVec.ofNat 64 o) 16 :=
  ⟨schR s₀, by rw [hp.rd]; simp, Offset.contains_base _ h (by omega)⟩

theorem setupKeys_ok {s₀ : State} (hp : UPre s₀) : WP isa (.block setupKeys) s₀ (PlainInv s₀ 0) := by
  have hR := hp.rounds
  have hx1 := x1_ofNat s₀
  rw [setupKeys, WP.block_append_iff]
  refine WP.mono (loads_ok s₀ (fun j hj => key_in hp (by omega)) 13 (Nat.le_refl _))
    fun s₁ ⟨e₁, f₁⟩ => ?_
  have g : ∀ r, s₁.gpr r = s₀.gpr r := fun r => f₁.gpr r (by simp)
  have e9 : s₁.gpr .x0 + s₁.gpr .x1 <<< 4 = W s₀ + BitVec.ofNat 64 (16 * R s₀) := by
    rw [g, g, VG.Proof.Aes.AArch64.shl4]
  have e9' : W s₀ + BitVec.ofNat 64 (16 * R s₀) - BitVec.ofNat 64 16 =
      W s₀ + BitVec.ofNat 64 (16 * (R s₀ - 1)) := by
    rw [Offset.add_ofNat_sub _ (by omega), show 16 * R s₀ - 16 = 16 * (R s₀ - 1) by omega]
  have rdwr : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [f₁.rd, f₁.wr]
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsl_x (sh := 4) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_add, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, e9,
      BitVec.add_zero, rdwr]
    exact key_in hp (by omega)), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, e9', BitVec.add_zero, rdwr]
    exact key_in hp (by omega)), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 10) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 12) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.setV, State.write, reduceCtorEq, ite_false, BitVec.add_zero, rdwr, g]
    exact ⟨stR s₀, by rw [hp.wr]; simp, Region.contains_self _ _⟩), WP.block_nil ?_⟩
  have hL : ∀ j, j ≤ R s₀ → 16 * j + 16 ≤ 16 * (R s₀ + 1) := fun j hj => by omega
  refine ⟨⟨hR, fun j hj => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, f₁.rd, f₁.wr, ?_⟩
  · simp only [State.setV, State.write, (kreg_ne j).1, (kreg_ne j).2, ite_false,
      show kreg j ≠ .v0 by unfold kreg; split <;> decide]
    rw [e₁ j (by omega)]
    exact keyIs_readW _ _ (hL j (by omega))
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, e9', BitVec.add_zero, f₁.mem]
    exact keyIs_readW _ _ (hL _ (by omega))
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, BitVec.add_zero, f₁.mem]
    exact keyIs_readW _ _ (hL _ (Nat.le_refl _))
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, g, hx1]; rfl
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, g, hx1]; rfl
  · simp [State.setV, State.write, g]
  · simp [State.setV, State.write, g]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, g]
    exact x4_ofNat s₀
  · exact f₁.mem
  · simp only [State.setV, State.write, ite_true, reduceCtorEq, ite_false, g, BitVec.add_zero, f₁.mem]
    exact bytes_read _ _

structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  keys : Keys (R s₀) (schedule s₀) s
  combo : s.v .v31 = s.v .v16 ^^^ s.v .v30
  x2 : s.gpr .x2 = St s₀
  x3 : s.gpr .x3 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  x4 : s.gpr .x4 = BitVec.ofNat 64 (N s₀ - k)
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : bytes (s.v .v0 ^^^ s.v .v30) = Spec.Cmac.chain (ciph s₀)
    (Spec.Aes.bytesAt s₀.mem (St s₀) 16) ((blks s₀).take k)

theorem setup_ok {s₀ : State} (hp : UPre s₀) : WP isa (.block setup) s₀ (Inv s₀ 0) := by
  rw [setup, WP.block_append_iff]
  refine WP.mono (setupKeys_ok hp) fun s h => ?_
  rw [fold, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  have vf : VFrame [.v0, .v31] s
      ((s.setV .v31 (s.v .v16 ^^^ s.v .v30)).setV .v0 (s.v .v0 ^^^ s.v .v30)) := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro r hr
    simp only [List.mem_cons, not_or] at hr
    simp [State.setV, hr.1, hr.2]
  refine ⟨h.keys.of_frame vf ⟨by decide, by decide⟩, ?_, h.x2, h.x3, h.x4, h.mem, h.rd, h.wr, ?_⟩
  · simp [State.setV]
  · simpa [State.setV, BitVec.xor_assoc] using h.state

theorem folded_xor (a m k l : BitVec 128) :
    a ^^^ (m ^^^ (k ^^^ l)) = ((a ^^^ l) ^^^ m) ^^^ k := by
  ac_rfl

/-- The first full round: the input block, first round key and deferred
last round key are XORed before the chaining register is read. -/
theorem absorb_ok {nr : Nat} {w : List Byte} (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 0) 16)
    (hK : Keys nr w s) (hc : s.v .v31 = s.v .v16 ^^^ s.v .v30) :
    WP isa (.block absorb) s fun s' =>
      RInv [.v0] w (fun _ => st ((s.v .v0 ^^^ s.v .v30) ^^^ s.mem.readW (s.gpr .x3) 128)) 1 s' ∧
      VFrame [.v0, .v1] s s' := by
  rw [absorb, WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by decide) hin, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩⟩
  · intro b hb
    simp only [List.mem_singleton] at hb; subst hb
    simp only [State.setV, ite_true, reduceCtorEq, ite_false, BitVec.add_zero, hc]
    rw [folded_xor]
    exact round_st (hK.full 0 (by have := hK.rounds; omega)) (rnds_zero w _).symm
  · intro r hr
    simp only [List.mem_cons, not_or] at hr
    simp [State.setV, hr.1, hr.2]

theorem rounds_tail_ok {nr : Nat} {w : List Byte} {x : VReg → Spec.Aes.State} {s : State}
    (hK : Keys nr w s) (hI : RInv [.v0] w x 1 s) :
    ∀ k, k + 2 ≤ nr →
    WP isa (.block ((List.range k).flatMap fun j => VG.Impl.Aes.AArch64.Aese.rnd [.v0] (kreg (j + 1)))) s
      fun s' => RInv [.v0] w x (k + 1) s' ∧ VFrame [.v0] s s'
  | 0, _ => WP.block_nil ⟨hI, VFrame.refl _ _⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (rounds_tail_ok hK hI k (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have br : BlockRegs [.v0] := ⟨by decide, by decide⟩
    exact WP.mono (round_ok br (j := k + 1) (by omega) (hK.of_frame hf₁ br) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩

theorem folded_last_ok {nr : Nat} {w : List Byte} {x : VReg → Spec.Aes.State} {s : State}
    (hK : Keys nr w s) (hI : RInv [.v0] w x (nr - 1) s) :
    WP isa (.block [.vop (.aese .v0 .v29)]) s fun s' =>
      st (s'.v .v0 ^^^ s'.v .v30) = Spec.Aes.cipher nr w (x .v0) ∧ VFrame [.v0] s s' := by
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩⟩
  · simp only [State.setV, ite_true, reduceCtorEq, ite_false]
    exact last_st hK.k29 hK.k30 (hI .v0 (by simp))
  · intro r hr; simp only [List.mem_singleton] at hr
    simp [State.setV, hr]

theorem tail_ok {nr middle : Nat} {w : List Byte} {x : VReg → Spec.Aes.State} {s : State}
    (hK : Keys nr w s) (hI : RInv [.v0] w x 1 s) (hm : middle + 2 = nr) :
    WP isa (tail middle) s fun s' => st (s'.v .v0 ^^^ s'.v .v30) = Spec.Aes.cipher nr w (x .v0) ∧ VFrame [.v0] s s' := by
  have br : BlockRegs [.v0] := ⟨by decide, by decide⟩
  refine WP.seq (WP.mono (rounds_tail_ok hK hI middle (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_)
  have hI' : RInv [.v0] w x (nr - 1) s₁ := by
    rwa [show middle + 1 = nr - 1 by omega] at hI₁
  exact WP.mono (folded_last_ok (hK.of_frame hf₁ br) hI')
    fun s' ⟨hv, hf'⟩ => ⟨hv, hf₁.trans hf'⟩

theorem advance_ok (s : State) : WP isa (.block advance) s fun s' =>
    s'.gpr .x3 = s.gpr .x3 + 16 ∧ s'.gpr .x4 = s.gpr .x4 - 1 ∧
    Fr [.x3, .x4] [] s s' := by
  rw [advance, WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  refine ⟨by simp [State.write, State.read], by simp [State.write, State.read],
    ⟨?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, not_or] at hr
  simp [State.write, hr.1, hr.2]

theorem body_ok {s₀ : State} (hp : UPre s₀) {middle : Nat} (hm : middle + 2 = R s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : Inv s₀ k s) : WP isa (body middle) s (Inv s₀ (k + 1)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 0) 16 := by
    rw [h.rd, h.wr, h.x3, BitVec.add_zero, hp.rd]
    exact ⟨dataR s₀, by simp, Offset.contains_base _ (by omega) (by have := hp.data_wrap; omega)⟩
  refine WP.seq (WP.mono (absorb_ok s hin h.keys h.combo) fun s₁ ⟨e₁, f₁⟩ => ?_)
  have br : BlockRegs [.v0, .v1] := ⟨by decide, by decide⟩
  refine WP.seq (WP.mono (tail_ok (h.keys.of_frame f₁ br) e₁ hm) fun s₂ ⟨e₂, f₂⟩ => ?_)
  refine WP.mono (advance_ok s₂) fun s₃ ⟨e3, e4, f₃⟩ => ?_
  have fv := f₁.trans (f₂.mono (by simp))
  have g : ∀ r, s₂.gpr r = s.gpr r := fun r => by rw [f₂.gpr, f₁.gpr]
  refine ⟨(h.keys.of_frame fv br).of_fr f₃ (by decide) (by decide) ⟨List.nodup_nil, by simp⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₃.v _ (by simp), f₃.v _ (by simp), f₃.v _ (by simp), fv.v _ (by decide), fv.v _ (by decide), fv.v _ (by decide)]
    exact h.combo
  · rw [f₃.gpr _ (by decide), g, h.x2]
  · rw [e3, g, h.x3]
    change Dp s₀ + BitVec.ofNat 64 (16 * k) + BitVec.ofNat 64 16 = _
    exact Offset.add_add_eq _ (by omega)
  · rw [e4, g, h.x4]
    change BitVec.ofNat 64 (N s₀ - k) - BitVec.ofNat 64 1 = _
    rw [Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  · rw [f₃.mem, f₂.mem, f₁.mem, h.mem]
  · rw [f₃.rd, f₂.rd, f₁.rd, h.rd]
  · rw [f₃.wr, f₂.wr, f₁.wr, h.wr]
  · rw [show s₃.v .v0 = s₂.v .v0 from f₃.v _ (by simp),
      show s₃.v .v30 = s₂.v .v30 from f₃.v _ (by simp)]
    change (st (s₂.v .v0 ^^^ s₂.v .v30)).toList = _
    rw [e₂]
    rw [← state_bytes, bytes_xor, h.state, h.mem, h.x3, bytes_read,
      take_succ_blks s₀ hk, Proof.Cmac.chain_append, Proof.Cmac.chain_single]
    rfl

theorem eval_count {s : State} {n : Nat} (hn : n < 2 ^ 64)
    (h : s.gpr .x4 = BitVec.ofNat 64 n) :
    isa.eval (.nonzero .x .x4) s = some !decide (n = 0) := by
  show some (s.read .x .x4 != 0) = _
  rw [State.read, h, BitVec.setWidth_eq, ofNat_ne_zero hn]

theorem loop_ok {s₀ : State} (hp : UPre s₀) {middle : Nat} (hm : middle + 2 = R s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : Inv s₀ k s) : WP isa (.loop (body middle) (.nonzero .x .x4)) s (Inv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (fun (n : Nat) (t : State) =>
    ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ Inv s₀ j t) ?_ (N s₀ - k) s ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hm hk h) fun s' h' => ?_
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  have ev := eval_count (n := N s₀ - (k + 1)) (by omega) h'.x4
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    exact ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

theorem loops_ok {s₀ : State} (hp : UPre s₀) {s : State}
    (hn : 0 < N s₀) (h : Inv s₀ 0 s) : WP isa loops s (Inv s₀ (N s₀)) := by
  have hx6 := h.keys.x6
  have hx7 := h.keys.x7
  obtain h10 | h12 | h14 := h.keys.rounds
  · rw [h10] at hx6
    exact WP.ite true (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun _ => loop_ok hp (by omega) hn h) (fun h => absurd h (by decide))
  · rw [h12] at hx6 hx7
    refine WP.ite false (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    exact WP.ite true (by simp only [AArch64.eval, State.read, hx7]; decide)
      (fun _ => loop_ok hp (by omega) hn h) (fun h => absurd h (by decide))
  · rw [h14] at hx6 hx7
    refine WP.ite false (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    exact WP.ite false (by simp only [AArch64.eval, State.read, hx7]; decide)
      (fun h => absurd h (by decide)) (fun _ => loop_ok hp (by omega) hn h)

theorem store_bytes (m : Mem) (p : Addr) (v : BitVec 128) :
    Spec.Aes.bytesAt (m.write p 16 v) p 16 = bytes v := by
  apply List.ext_getElem
  · simp [Spec.Aes.bytesAt, bytes]
  · intro i hi hj
    have hi' : i < 16 := by simpa [Spec.Aes.bytesAt] using hi
    simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, bytes, Vector.getElem_toList, st, Vector.getElem_ofFn, vbyte]
    change (if (p + BitVec.ofNat 64 i - p).toNat < 16 then _ else _) = _
    rw [Mem.sub_ofNat_toNat p (by omega), ite_eq_left hi']

theorem correct_wp {s₀ : State} (hp : UPre s₀) : WP isa update s₀ (updateAArch64.post s₀) := by
  have ev : isa.eval (.zero .x .x4) s₀ = some (decide (N s₀ = 0)) := by
    show some (s₀.read .x .x4 == 0) = _
    rw [State.read, BitVec.setWidth_eq, x4_ofNat]
    have e := ofNat_ne_zero ((s₀.gpr .x4).isLt)
    rw [bne] at e
    cases hb : (BitVec.ofNat 64 (N s₀) == 0) <;> cases hd : decide (N s₀ = 0) <;> simp_all
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    simp [updateAArch64, Spec.Cmac.blocksAt, hn, Spec.Cmac.chain]
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    refine WP.seq (WP.mono (setup_ok hp) fun s₁ h₁ => ?_)
    refine WP.seq (WP.mono (loops_ok hp (by omega) h₁) fun s₂ h₂ => ?_)
    rw [WP.block_cons_iff]
    refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]
    refine ⟨_, exec_strq (off := 0) (by decide) (by
      simp only [State.setV]
      rw [h₂.wr, h₂.x2, BitVec.add_zero, hp.wr]
      exact ⟨stR s₀, by simp, Region.contains_self _ _⟩), WP.block_nil ?_⟩
    change Spec.Aes.bytesAt (s₂.mem.write (s₂.gpr .x2 + 0) 16 (s₂.v .v0 ^^^ s₂.v .v30)) (St s₀) 16 = _
    change Spec.Aes.bytesAt (s₂.mem.write (s₂.gpr .x2 + BitVec.ofNat 64 0) 16 (s₂.v .v0 ^^^ s₂.v .v30)) (St s₀) 16 = _
    rw [h₂.x2, BitVec.add_zero, store_bytes, h₂.state,
      List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem correct (s : State) (hs : updateAArch64.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ updateAArch64.post s s' := by
  obtain ⟨t, s', he, hq, hg⟩ := WP.gprs (rs := preserved) (correct_wp (UPre.of hs))
    (by decide +kernel) (by decide +kernel)
  exact ⟨t, s', he, ⟨hg, Exec.sp he, Exec.preservedV he⟩, hq⟩

theorem ct : ConstantTime isa updateAArch64.pre updateAArch64.pub update := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem verified : Verified AArch64.target update (Spec.Cmac.aesUpdateContract AArch64.abi) :=
  Verified.of_correct correct ct (by
    sig_implies [Spec.Cmac.aesUpdateContract, Spec.Cmac.aesUpdateSig, updateAArch64, AArch64.abi,
      AArch64.argRegs] [updSat] using updSat)
end VG.Proof.CmacAes.AArch64.Aese
