import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Lit
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Setup

namespace VG.Proof.Poly1305.AArch64.Radix64
open VG VG.AArch64 VG.Impl.Poly1305.AArch64.Radix64
open VG.Proof.Poly1305.AArch64 VG.PowLit
open VG.Spec.Poly1305 (P bytesAt leNum clamp accumulate Repr)

structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  keys : Keys (Rn s₀) s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = s₀.mem
  acc : A0 s₀ < P → hval s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ i) % P ∧ Bounds s

structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  x1 : s.gpr .x1 = blkAddr s₀ i
  x2 : s.gpr .x2 = BitVec.ofNat 64 (nb s₀ - i)

def body : Prog isa := .block (absorb true ++ VG.Impl.Poly1305.AArch64.advance)

theorem body_ok {s₀ : State} (hp : BPre s₀) {i : Nat}
    (hi : i < nb s₀) {s : State} (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .x .x2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have hin : ∀ d : Nat, d + 8 ≤ 16 →
      InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [hL.rd, hL.wr, hL.x1, hp.rd]
    exact ⟨blR s₀, List.mem_append_left _ (List.mem_singleton_self _), hp.blk_contains hi hd⟩
  have hab := absorb_key_ok s true hL.keys (hin 0 (by decide)) (hin 8 (by decide))
  change WP isa (.block (absorb true ++ VG.Impl.Poly1305.AArch64.advance)) s _
  refine WP.block_append (WP.mono hab fun s₁ ⟨ha, k₁⟩ => ?_)
  refine WP.mono (VG.Proof.Poly1305.AArch64.advance_ok s₁) fun s₂ ⟨a₁, a₂, k₂⟩ => ?_
  have k₂ : Keeps [.x1, .x2] s₁ s₂ := k₂
  have k := k₁.trans k₂
  have hc : Common s₀ (i + 1) s₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, fun hA => ?_⟩
    · rw [k.gpr' (r := .x0), hL.x0]
    · exact hL.keys.of_regs fun r hr => k.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide)
    · rw [k.2.2.1, hL.rd]
    · rw [k.2.2.2, hL.wr]
    · rw [k.2.1, hL.mem]
    · obtain ⟨hv₀, hb⟩ := hL.acc hA
      obtain ⟨hv', hb'⟩ := ha hb
      obtain ⟨e₂, b₂⟩ := bounds_eq (s := s₁) (s' := s₂) fun r hr => k₂.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl <;> decide)
      refine ⟨?_, b₂ hb'⟩
      have h16 : (blks s₀ i).length % 16 = 0 := by
        simp only [blks, Poly1305.length_bytesAt]; omega_using []
      have hb1 : 0 < (bytesAt s₀.mem (blkAddr s₀ i) 16).length := by
        rw [Poly1305.length_bytesAt]; omega_using []
      have hb2 : (bytesAt s₀.mem (blkAddr s₀ i) 16).length ≤ 16 := by rw [Poly1305.length_bytesAt]
      rw [e₂, hv', hL.x1, hL.mem, show word s₀.mem (blkAddr s₀ i) 0 = w64 s₀.mem (blkAddr s₀ i) 0 from rfl, show word s₀.mem (blkAddr s₀ i) 8 = w64 s₀.mem (blkAddr s₀ i) 8 from rfl, VG.Proof.Poly1305.AArch64.block_value hp (Frame.refl _ _) hi, mod_step hv₀, blks_succ,
        Poly1305.absorbAll_append h16, Poly1305.absorbAll_block hb1 hb2]
  have hx2 : s₂.gpr .x2 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [a₂, k₁.gpr' (r := .x2), hL.x2, Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]
  have hev : eval (.nonzero .x .x2) s₂ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx2]
  have := hp.nb_lt
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp only [Nat.sub_self, BitVec.ofNat_eq_ofNat, bne_self_eq_false], hlast ▸ hc⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega_using [hi, hlast]
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, this, h'])] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega_using [hi, hne], { hc with x1 := ?_, x2 := hx2 }⟩
    rw [a₁, k₁.gpr' (r := .x1), hL.x1, blkAddr, blkAddr, Offset.add_add, Nat.mul_succ]


set_option simprocs false in
theorem storeH_ok (s : State) (hw : sR (s.gpr .x0) ∈ s.wr) :
    WP isa (.block storeH) s fun s' =>
      s'.mem = storeHm s.mem (s.gpr .x0) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .x0) d) 8 :=
    fun d hd => ⟨_, hw, contains_off hd (by omega_using [hd])⟩
  have o0 := o 0 (by decide); have o8 := o 8 (by decide); have o16 := o 16 (by decide)
  simp only [off] at o0 o8 o16
  apply WP.of_runBlock
  simp (config := {decide := true}) only [storeH, runBlock_cons, runStep_some, runBlock_nil,
    exec_str_x (show 0 % 8 = 0 ∧ 0 < 32768 by decide) o0, exec_str_x (show 8 % 8 = 0 ∧ 8 < 32768 by decide),
    exec_str_x (show 16 % 8 = 0 ∧ 16 < 32768 by decide), o8, o16, Option.some.injEq, exists_eq_left']
  trivial

theorem epilogue_ok {s₀ : State} (hp : BPre s₀) {s : State}
    (hc : Common s₀ (nb s₀) s) :
    WP isa (.block (reduce ++ storeH)) s fun s' => Proof.Poly1305.blocksAArch64.post s₀ s' := by
  refine WP.block_append (WP.mono (reduce_ok s) fun s₁ ⟨hr, k₁⟩ => ?_)
  have x0₁ : s₁.gpr .x0 = st s₀ := by rw [k₁.gpr', hc.x0]
  refine WP.mono (storeH_ok s₁ (by
    rw [k₁.2.2.2, hc.wr, hp.wr, x0₁]; exact List.mem_singleton_self _))
    fun s₂ ⟨m₂, _, _, _⟩ => ?_
  intro key msg hrep
  have hA := A0_lt hrep
  obtain ⟨hv₀, hb⟩ := hc.acc hA
  have hN := hr hb
  have mem₁ : s₁.mem = s₀.mem := by rw [k₁.2.1, hc.mem]
  rw [x0₁, mem₁] at m₂
  have hf : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₂.mem := by
    rw [m₂]; exact storeHm_frame (Frame.refl _ _) _ _ _
  have hlen := hrep.1
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_append, Poly1305.length_bytesAt]; omega_using [hlen]
  · rw [← off_24, key_frame hf]; exact repr_key hrep
  · rw [m₂, storeHm_acc, ← repr_key hrep, clamp_key, Poly1305.accumulate_append hlen, repr_acc hrep]
    change hval s₁ = _
    rw [hN, hv₀, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)]

theorem blocks_correct {s₀ : State} (hp : BPre s₀) :
    WP isa blocks s₀ (Proof.Poly1305.blocksAArch64.post s₀) := by
  rw [blocks]
  refine WP.seq (WP.mono (setup_ok s₀ (by rw [hp.wr]; exact List.mem_singleton_self _))
    fun s₁ h₁ => ?_)
  obtain ⟨hk, ha, k⟩ := h₁
  have hc₀ : Common s₀ 0 s₁ := ⟨k.gpr' (r := .x0), hk, k.2.2.1, k.2.2.2, k.2.1,
    fun hA => by
      obtain ⟨e, b⟩ := ha hA
      refine ⟨?_, b⟩
      rw [e, show blks s₀ 0 = [] by simp only [blks, bytesAt, Nat.mul_zero, List.range_zero, List.map_nil], Poly1305.absorbAll_nil]⟩
  have x2₁ : s₁.gpr .x2 = s₀.gpr .x2 := k.gpr' (r := .x2)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc₂ => epilogue_ok hp hc₂)
  refine WP.ite (s₁.read .x .x2 == 0) rfl (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by
      simp only [State.read, Size.bits, BitVec.setWidth_eq, x2₁, beq_iff_eq] at h
      simp only [nb, h, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [State.read, Size.bits, BitVec.setWidth_eq, x2₁, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hi'], i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        x1 := by rw [k.gpr' (r := .x1)]; simp only [blkAddr, Nat.mul_zero, BitVec.add_zero]
        x2 := by rw [x2₁]; simp only [nb, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

theorem blocks_untouched : Untouched Impl.Poly1305.AArch64.Radix64.blocks :=
  Untouched.of_all (by rw [← Code.allInstrs_eq]; lit_decide)

theorem blocks_ok (s : State) (hs : Proof.Poly1305.blocksAArch64.pre s) :
    ∃ t s', Exec isa Impl.Poly1305.AArch64.Radix64.blocks s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.blocksAArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ := blocks_correct (BPre.of s hs)
  exact ⟨t, s', he, ⟨fun r hr => Exec.gpr (blocks_untouched r hr) he, Exec.sp he, Exec.preservedV he⟩, h⟩

theorem blocks_ct : ConstantTime isa Proof.Poly1305.blocksAArch64.pre
    Proof.Poly1305.blocksAArch64.pub Impl.Poly1305.AArch64.Radix64.blocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> assumption

theorem blocks_verified :
    Verified AArch64.target Impl.Poly1305.AArch64.Radix64.blocks (Spec.Poly1305.blocksContract AArch64.abi)
      :=
  Verified.of_correct blocks_ok blocks_ct (by
    sig_implies [Spec.Poly1305.blocksContract, Spec.Poly1305.blocksSig,
      Proof.Poly1305.blocksAArch64, AArch64.abi, AArch64.argRegs] [Proof.Poly1305.AArch64.blocksSat]
      using Proof.Poly1305.AArch64.blocksSat)

end VG.Proof.Poly1305.AArch64.Radix64
