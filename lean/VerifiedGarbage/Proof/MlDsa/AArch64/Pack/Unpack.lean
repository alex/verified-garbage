import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.BitPack

/-!
# ML-DSA on AArch64: `vg_mldsa_bit_unpack` and `vg_mldsa_unpack_t1`

The coefficient of a field `y` is `b - y` in 64 bits, plus `q` times its sign
bit (`subModQ`), which is `b - y` in `ℤ_q` (`Pack/Arith.lean`), or `y · 2¹³`.
The loop is proven once for every width (`unpackLoop_ok`), and
`vg_mldsa_bit_unpack` by its five cases, which the length chooses.
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Only wp_sub wp_lsr wp_lsl wp_madd wp_mov wp_movImm wp_strw wp_nil abi_of agree_of
  toNat_lsl_n)
open VG.Proof.MlDsa.Pack

/-- The word `buFin` stores for the field `y`, for `b = B`. -/
abbrev buWord (B y : Nat) : BitVec 32 := (subModQ (BitVec.ofNat 64 B) (BitVec.ofNat 64 y)).setWidth 32

theorem buFin_ok (B d : Nat) : FinOk buFin d (buWord B) (BitVec.ofNat 64 B) (BitVec.ofNat 64 q) :=
  fun j s h12 h13 hj hout _ =>
  wp_sub fun s₁ o₁ e₁ => wp_lsr (by decide) fun s₂ o₂ e₂ => wp_madd fun s₃ o₃ e₃ =>
    wp_strw ⟨by omega, by omega⟩ (by rw [o₃.get .x4, o₂.get .x4, o₁.get .x4])
      (by rw [o₃.wr, o₂.wr, o₁.wr]; exact hout) fun s₄ h₄ => wp_nil ⟨by
        rw [h₄.mem, o₃.mem, o₂.mem, o₁.mem, e₃, e₂, o₂.get .x10, o₂.get .x13, e₁, o₁.get .x13, h12, h13,
          buWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl,
        (((o₁.keep.trans o₂.keep).trans o₃.keep).trans h₄.keep).mono⟩

/-- The word `t1Fin` stores for the field `y`. -/
abbrev t1Word (y : Nat) : BitVec 32 := (BitVec.ofNat 64 y <<< 13).setWidth 32

theorem t1Fin_ok (K12 K13 : BitVec 64) : FinOk t1Fin 10 t1Word K12 K13 := fun j s _ _ hj hout _ =>
  wp_lsl (by decide) fun s₁ o₁ e₁ =>
    wp_strw ⟨by omega, by omega⟩ (by rw [o₁.get .x4]) (by rw [o₁.wr]; exact hout) fun s₂ h₂ => wp_nil ⟨by
      rw [h₂.mem, o₁.mem, e₁, t1Word, BitVec.ofNat_toNat, BitVec.setWidth_eq], (o₁.keep.trans h₂.keep).mono⟩

/-- A field of `d ≤ 20` bits of the input. -/
theorem field_lt (X d k : Nat) (hd : d ≤ 20) : X / 2 ^ (d * k) % 2 ^ d < 2 ^ 20 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos d)) (Nat.pow_le_pow_right (by decide) hd)

theorem bu_wp {s₀ : State} (hp : bitUnpackK.pre s₀) :
    WP isa Impl.MlDsa.AArch64.Pack.bitUnpack s₀ fun s' => bitUnpackK.post s₀ s' := by
  obtain ⟨hrd, hwr, hsep, hab, hlen⟩ := hp
  have hc := bp_cases hab hlen
  have go : ∀ {d c nb B : Nat}, Shape d c nb → wArg s₀ .x3 = B → bitlen (wArg s₀ .x2 + wArg s₀ .x3) = d →
      ∀ s : State, s.gpr .x0 = s₀.gpr .x0 → s.gpr .x4 = s₀.gpr .x4 → s.gpr .x13 = BitVec.ofNat 64 q →
      s.rd = s₀.rd → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (buWidth B d c nb) s fun s' => bitUnpackK.post s₀ s' := by
    intro d c nb B hs hB hd s h0 h4 h13 h3 h5 h6
    rw [hd] at hlen
    have hq : q = 8380417 := rfl
    have hB19 : B ≤ 2 ^ 19 := by omega
    refine WP.seq ?_
    rw [← List.append_nil (Impl.MlKem.AArch64.movImm _ _)]
    refine wp_movImm fun s₁ o₁ e₁ => wp_nil ?_
    refine WP.mono (unpackLoop_ok (buFin_ok B d) hs (v := s₀.gpr .x0) (p := s₀.gpr .x4) (s₀ := s₀)
      (by rw [hrd, hlen]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hwr]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hsep)
      (by rw [o₁.get .x0, h0]) (by rw [o₁.get .x4, h4]) e₁ (by rw [o₁.get .x13, h13])
      (by rw [o₁.rd, h3]) (by rw [o₁.wr, h5]) (by rw [o₁.mem, h6]))
      fun s' ⟨hc', _, _⟩ => ?_
    show PolyIs s'.mem (s₀.gpr .x4) (toRq (bitUnpack (bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat) _ _))
    refine polyIs_of_toNat fun i hi => ?_
    have hy := field_lt (inNum s₀.mem (s₀.gpr .x0) d) d i hs.d20
    have hy' := hy
    unfold inNum at hy'
    rw [hc' i hi, buWord, BitVec.toNat_setWidth, subModQ_toNat (by omega) (by omega),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (show 0 < q by decide)) (by decide)),
      toRq, Vector.getElem_map, bitUnpack_get _ _ _ hi, hlen, hd, hB, ofInt_sub (by omega)]
  unfold Impl.MlDsa.AArch64.Pack.bitUnpack
  refine WP.seq ?_
  rw [← List.append_nil (Impl.MlKem.AArch64.movImm _ _)]
  refine wp_movImm fun s₂ o₂ e₂ => wp_nil ?_
  have h0 : s₂.gpr .x0 = s₀.gpr .x0 := o₂.get .x0
  have h1 : s₂.gpr .x1 = s₀.gpr .x1 := o₂.get .x1
  have h4 : s₂.gpr .x4 = s₀.gpr .x4 := o₂.get .x4
  have h13 : s₂.gpr .x13 = BitVec.ofNat 64 q := e₂
  refine sel_ok (by decide) (fun s₃ o₃ h => ?_) (fun s₃ o₃ h => ?_)
  · rw [h1] at h
    exact go (d := 3) (c := 8) (nb := 3) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₃ (by rw [o₃.get .x0, h0]) (by rw [o₃.get .x4, h4]) (by rw [o₃.get .x13, h13])
      (by rw [o₃.rd, o₂.rd]) (by rw [o₃.wr, o₂.wr]) (by rw [o₃.mem, o₂.mem])
  have k₃ := o₂.trans o₃
  rw [h1] at h
  refine sel_ok (by decide) (fun s₄ o₄ h' => ?_) (fun s₄ o₄ h' => ?_)
  · rw [o₃.get .x1, h1] at h'
    exact go (d := 4) (c := 2) (nb := 1) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₄ (by rw [o₄.get .x0, k₃.get .x0]) (by rw [o₄.get .x4, k₃.get .x4])
      (by rw [o₄.get .x13, o₃.get .x13, h13]) (by rw [o₄.rd, k₃.rd]) (by rw [o₄.wr, k₃.wr])
      (by rw [o₄.mem, k₃.mem])
  have k₄ := k₃.trans o₄
  rw [o₃.get .x1, h1] at h'
  refine sel_ok (by decide) (fun s₅ o₅ h'' => ?_) (fun s₅ o₅ h'' => ?_)
  · rw [o₄.get .x1, o₃.get .x1, h1] at h''
    exact go (d := 13) (c := 8) (nb := 13) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₅ (by rw [o₅.get .x0, k₄.get .x0]) (by rw [o₅.get .x4, k₄.get .x4])
      (by rw [o₅.get .x13, o₄.get .x13, o₃.get .x13, h13]) (by rw [o₅.rd, k₄.rd]) (by rw [o₅.wr, k₄.wr])
      (by rw [o₅.mem, k₄.mem])
  have k₅ := k₄.trans o₅
  rw [o₄.get .x1, o₃.get .x1, h1] at h''
  refine sel_ok (by decide) (fun s₆ o₆ h''' => ?_) (fun s₆ o₆ h''' => ?_)
  · rw [o₅.get .x1, o₄.get .x1, o₃.get .x1, h1] at h'''
    exact go (d := 18) (c := 4) (nb := 9) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₆ (by rw [o₆.get .x0, k₅.get .x0]) (by rw [o₆.get .x4, k₅.get .x4])
      (by rw [o₆.get .x13, o₅.get .x13, o₄.get .x13, o₃.get .x13, h13]) (by rw [o₆.rd, k₅.rd])
      (by rw [o₆.wr, k₅.wr]) (by rw [o₆.mem, k₅.mem])
  · rw [o₅.get .x1, o₄.get .x1, o₃.get .x1, h1] at h'''
    exact go (d := 20) (c := 2) (nb := 5) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₆ (by rw [o₆.get .x0, k₅.get .x0]) (by rw [o₆.get .x4, k₅.get .x4])
      (by rw [o₆.get .x13, o₅.get .x13, o₄.get .x13, o₃.get .x13, h13]) (by rw [o₆.rd, k₅.rd])
      (by rw [o₆.wr, k₅.wr]) (by rw [o₆.mem, k₅.mem])

theorem bitUnpack_correct (s : State) (hs : bitUnpackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Pack.bitUnpack s t s' ∧ abiPreserved s s' ∧ bitUnpackK.post s s' := by
  obtain ⟨t, s', he, hb⟩ := bu_wp hs
  exact ⟨t, s', he, abi_of rfl (by lit_decide) he, hb⟩

theorem bitUnpack_ct : ConstantTime isa bitUnpackK.pre bitUnpackK.pub Impl.MlDsa.AArch64.Pack.bitUnpack :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x4])
    (fun _ _ _ _ ⟨h0, h1, h4, hsp⟩ => agree_of hsp (by simp [h0, h1, h4])) (by taint_decide)

/-- A state satisfying the precondition. -/
def bitUnpackSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 96 | .x2 => 2 | .x3 => 2 | .x4 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 96⟩]
  wr := [⟨0x2000, 1024⟩]

theorem bitUnpack_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Pack.bitUnpack (bitUnpackContract AArch64.abi) :=
  Verified.of_correct bitUnpack_correct bitUnpack_ct
    { pre := by sig_implies_pre [bitUnpackContract, bitUnpackSig, bitUnpackK, AArch64.abi, AArch64.argRegs]
      post := by sig_implies_post [bitUnpackContract, bitUnpackSig, bitUnpackK, AArch64.abi, AArch64.argRegs]
      pub := by sig_implies_pub [bitUnpackContract, bitUnpackSig, bitUnpackK, AArch64.abi, AArch64.argRegs]
      sat := by
        refine ⟨bitUnpackSat, ?_⟩
        sig_pre [bitUnpackContract, bitUnpackSig, AArch64.abi, AArch64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | (simp only [bitPackParams]; decide)
          | decide }

/-! ## `vg_mldsa_unpack_t1` -/

theorem t1_wp {s₀ : State} (hp : unpackT1K.pre s₀) :
    WP isa Impl.MlDsa.AArch64.Pack.unpackT1 s₀ fun s' => unpackT1K.post s₀ s' := by
  obtain ⟨hrd, hwr, hsep⟩ := hp
  refine WP.seq (wp_mov fun s₁ o₁ e₁ => wp_nil ?_)
  refine WP.mono (unpackLoop_ok (t1Fin_ok (s₁.gpr .x12) (s₁.gpr .x13)) (c := 4) (nb := 5)
    ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ (v := s₀.gpr .x0) (p := s₀.gpr .x1) (s₀ := s₀)
    (by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _))
    (by rw [hwr]; exact List.mem_singleton_self _) hsep (o₁.get .x0) e₁ rfl rfl o₁.rd o₁.wr o₁.mem)
    fun s' ⟨hc, _, _⟩ => ?_
  refine polyIs_of_toNat fun i hi => ?_
  have hy : inNum s₀.mem (s₀.gpr .x0) 10 / 2 ^ (10 * i) % 2 ^ 10 < 2 ^ 10 := Nat.mod_lt _ (by decide)
  rw [hc i hi, t1Word, BitVec.toNat_setWidth, toNat_lsl_n (by rw [BitVec.toNat_ofNat]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show _ < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega),
    Vector.getElem_map, simpleBitUnpack_get _ _ hi, show bitlen t1Max = 10 by decide, ofInt_t1 hy]

theorem unpackT1_correct (s : State) (hs : unpackT1K.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Pack.unpackT1 s t s' ∧ abiPreserved s s' ∧ unpackT1K.post s s' := by
  obtain ⟨t, s', he, hb⟩ := t1_wp hs
  exact ⟨t, s', he, abi_of rfl (by lit_decide) he, hb⟩

theorem unpackT1_ct : ConstantTime isa unpackT1K.pre unpackT1K.pub Impl.MlDsa.AArch64.Pack.unpackT1 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1])
    (fun _ _ _ _ ⟨h0, h1, hsp⟩ => agree_of hsp (by simp [h0, h1])) (by taint_decide)

/-- A state satisfying the precondition. -/
def unpackT1Sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 320⟩]
  wr := [⟨0x2000, 1024⟩]

theorem unpackT1_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Pack.unpackT1 (unpackT1Contract AArch64.abi) :=
  Verified.of_correct unpackT1_correct unpackT1_ct
    { pre := by sig_implies_pre [unpackT1Contract, unpackT1Sig, unpackT1K, AArch64.abi, AArch64.argRegs]
      post := by sig_implies_post [unpackT1Contract, unpackT1Sig, unpackT1K, AArch64.abi, AArch64.argRegs]
      pub := by sig_implies_pub [unpackT1Contract, unpackT1Sig, unpackT1K, AArch64.abi, AArch64.argRegs]
      sat := by
        refine ⟨unpackT1Sat, ?_⟩
        sig_pre [unpackT1Contract, unpackT1Sig, AArch64.abi, AArch64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | decide }

end VG.Proof.MlDsa.AArch64.Pack
