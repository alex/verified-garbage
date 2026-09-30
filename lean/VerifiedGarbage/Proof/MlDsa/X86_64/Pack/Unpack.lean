import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.BitPack

/-!
# ML-DSA on x86-64: `vg_mldsa_bit_unpack` and `vg_mldsa_unpack_t1`

Untrusted: everything here is checked by Lean. The coefficient of a field
`y` is `b - y`, plus `q` if that borrows (`subModQ`), which is `b - y` in
`ℤ_q` (`Pack/Arith.lean`), or `y · 2¹³`. The loop is proven once for every
width (`unpackLoop_ok`), and `vg_mldsa_bit_unpack` by its five cases.
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr WP.keep retR pR dArg regsLo agree_regsLo
  gprPreserved_of rotr_toNat)
open VG.Proof.MlDsa.Pack

/-- The word `buFin B` stores for the field `y`. -/
abbrev buWord (B y : Nat) : BitVec 32 := subModQ (BitVec.ofNat 32 B) (BitVec.ofNat 32 y)

theorem buFin_ok (B d : Nat) : FinOk (buFin B) d (buWord B) := fun j s hout _ => by
  refine WP.keep _ ?_ (by rfl)
  unfold buFin
  xrun [ea_at', hout]
  rw [buWord, BitVec.ofNat_toNat]
  rfl

/-- The word `t1Fin` stores for the field `y`. -/
abbrev t1Word (y : Nat) : BitVec 32 := (BitVec.ofNat 32 y).rotateRight 19

theorem t1Fin_ok : FinOk t1Fin 10 t1Word := fun j s hout _ => by
  refine WP.keep _ ?_ (by rfl)
  unfold t1Fin
  xrun [ea_at', hout]
  rw [t1Word, BitVec.ofNat_toNat]

theorem buPro_ok (s : State) :
    WP isa (.block [.mov32 .rcx (.reg .rcx), .mov .rsi (.reg .r8)]) s fun s' =>
      (dArg s' .rcx = dArg s .rcx ∧ s'.gpr .rsi = s.gpr .r8 ∧ s'.mem = s.mem) ∧ Keep [.rcx, .rsi] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [dArg]

/-- A field of `d ≤ 20` bits of the input. -/
theorem field_lt (X d k : Nat) (hd : d ≤ 20) : X / 2 ^ (d * k) % 2 ^ d < 2 ^ 20 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos d)) (Nat.pow_le_pow_right (by decide) hd)

theorem bu_wp {s₀ : State} (hp : bitUnpackK.pre s₀) :
    WP isa Impl.MlDsa.X86_64.Pack.bitUnpack s₀ fun s' =>
      bitUnpackK.post s₀ s' ∧ Frame [pR (s₀.gpr .r8)] s₀.mem s'.mem := by
  obtain ⟨hrd, hwr, hsep, -, -, hab, hlen⟩ := hp
  have go : ∀ {d c nb B : Nat}, Shape d c nb → dArg s₀ .rcx = B → B ≤ 2 ^ 19 →
      bitlen (dArg s₀ .rdx + B) = d → ∀ s : State,
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .rsi = s₀.gpr .r8 → s.rd = s₀.rd → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (unpackLoop (buFin B) d c nb) s fun s' =>
        bitUnpackK.post s₀ s' ∧ Frame [pR (s₀.gpr .r8)] s₀.mem s'.mem := by
    intro d c nb B hs hB hB19 hd s h1 h2 h3 h4 h5
    rw [hB, hd] at hlen
    have hq : q = 8380417 := rfl
    refine WP.mono (unpackLoop_ok (buFin_ok B d) hs (v := s₀.gpr .rdi) (p := s₀.gpr .r8) (s₀ := s₀)
      (by rw [hrd, hlen]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hwr]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hsep) h1 h2 h3 h4 h5)
      fun s' ⟨hc, hf, _⟩ => ⟨?_, hf⟩
    show PolyIs s'.mem (s₀.gpr .r8) (toRq (bitUnpack (bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat) _ _))
    refine polyIs_of_toNat fun i hi => ?_
    have hy := field_lt (inNum s₀.mem (s₀.gpr .rdi) d) d i hs.d20
    have hy' := hy
    unfold inNum at hy'
    rw [hc i hi, buWord, subModQ_toNat (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show B < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega), toRq, Vector.getElem_map, bitUnpack_get _ _ _ hi,
      hlen, hB, hd, ofInt_sub (by omega)]
  unfold Impl.MlDsa.X86_64.Pack.bitUnpack
  refine WP.seq (WP.mono (buPro_ok s₀) fun s₁ ⟨⟨cx₁, si₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  have cases := mem_bitPackParams hab
  refine sel_ok .rcx 2 _ _ s₁ (fun s₂ ⟨g₂, m₂, rd₂, wr₂⟩ h => ?_) (fun s₂ ⟨g₂, m₂, rd₂, wr₂⟩ h => ?_)
  · have e : dArg s₀ .rcx = 2 := by rw [← cx₁, lo_of_eq h]
    have ea : dArg s₀ .rdx = 2 := by omega
    exact go (d := 3) (c := 8) (nb := 3) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₂ (by rw [g₂, di₁]) (by rw [g₂, si₁]) (by rw [rd₂, k₁.2.1])
      (by rw [wr₂, k₁.2.2]) (by rw [m₂, m₁])
  have n2 : dArg s₀ .rcx ≠ 2 := by rw [← cx₁]; exact lo_ne h
  have ds₂ : dArg s₂ .rcx = dArg s₀ .rcx := by unfold dArg; rw [g₂]; exact cx₁
  refine sel_ok .rcx 4 _ _ s₂ (fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ h => ?_) (fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ h => ?_)
  · have e : dArg s₀ .rcx = 4 := by rw [← ds₂, lo_of_eq h]
    have ea : dArg s₀ .rdx = 4 := by omega
    exact go (d := 4) (c := 2) (nb := 1) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₃ (by rw [g₃, g₂, di₁]) (by rw [g₃, g₂, si₁])
      (by rw [rd₃, rd₂, k₁.2.1]) (by rw [wr₃, wr₂, k₁.2.2]) (by rw [m₃, m₂, m₁])
  have n4 : dArg s₀ .rcx ≠ 4 := by rw [← ds₂]; exact lo_ne h
  have ds₃ : dArg s₃ .rcx = dArg s₀ .rcx := by unfold dArg; rw [g₃]; exact ds₂
  refine sel_ok .rcx 4096 _ _ s₃ (fun s₄ ⟨g₄, m₄, rd₄, wr₄⟩ h => ?_) (fun s₄ ⟨g₄, m₄, rd₄, wr₄⟩ h => ?_)
  · have e : dArg s₀ .rcx = 4096 := by rw [← ds₃, lo_of_eq h]
    have ea : dArg s₀ .rdx = 4095 := by omega
    exact go (d := 13) (c := 8) (nb := 13) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₄ (by rw [g₄, g₃, g₂, di₁]) (by rw [g₄, g₃, g₂, si₁])
      (by rw [rd₄, rd₃, rd₂, k₁.2.1]) (by rw [wr₄, wr₃, wr₂, k₁.2.2]) (by rw [m₄, m₃, m₂, m₁])
  have n4096 : dArg s₀ .rcx ≠ 4096 := by rw [← ds₃]; exact lo_ne h
  have ds₄ : dArg s₄ .rcx = dArg s₀ .rcx := by unfold dArg; rw [g₄]; exact ds₃
  refine sel_ok .rcx 131072 _ _ s₄ (fun s₅ ⟨g₅, m₅, rd₅, wr₅⟩ h => ?_) (fun s₅ ⟨g₅, m₅, rd₅, wr₅⟩ h => ?_)
  · have e : dArg s₀ .rcx = 131072 := by rw [← ds₄, lo_of_eq h]
    have ea : dArg s₀ .rdx = 131071 := by omega
    exact go (d := 18) (c := 4) (nb := 9) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₅ (by rw [g₅, g₄, g₃, g₂, di₁]) (by rw [g₅, g₄, g₃, g₂, si₁])
      (by rw [rd₅, rd₄, rd₃, rd₂, k₁.2.1]) (by rw [wr₅, wr₄, wr₃, wr₂, k₁.2.2]) (by rw [m₅, m₄, m₃, m₂, m₁])
  · have n131072 : dArg s₀ .rcx ≠ 131072 := by rw [← ds₄]; exact lo_ne h
    have e : dArg s₀ .rcx = 524288 := by omega
    have ea : dArg s₀ .rdx = 524287 := by omega
    exact go (d := 20) (c := 2) (nb := 5) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₅ (by rw [g₅, g₄, g₃, g₂, di₁]) (by rw [g₅, g₄, g₃, g₂, si₁])
      (by rw [rd₅, rd₄, rd₃, rd₂, k₁.2.1]) (by rw [wr₅, wr₄, wr₃, wr₂, k₁.2.2]) (by rw [m₅, m₄, m₃, m₂, m₁])

theorem bitUnpack_correct (s : State) (hs : bitUnpackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Pack.bitUnpack s t s' ∧ abiPreserved s s' ∧ bitUnpackK.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := Impl.MlDsa.X86_64.Pack.bitUnpack)
    [.rax, .rcx, .rsi, .rdi, .r10, .r11] (bu_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem bitUnpack_ct : ConstantTime isa bitUnpackK.pre bitUnpackK.pub Impl.MlDsa.X86_64.Pack.bitUnpack :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rsi, .r8, .rsp] [.rdx, .rcx])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [hp.2.2.2.2.1, hp.2.2.2.2.2])
    (by taint_decide)

/-- A state satisfying the precondition. -/
def bitUnpackSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 96 | .rdx => 2 | .rcx => 2 | .r8 => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 96⟩]
  wr := [⟨0x2000, 1024⟩]

theorem bitUnpack_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Pack.bitUnpack (bitUnpackContract X86_64.abi) :=
  Verified.of_correct bitUnpack_correct bitUnpack_ct
    { pre := by sig_implies_pre [bitUnpackContract, bitUnpackSig, bitUnpackK, X86_64.abi, X86_64.argRegs]
      post := by sig_implies_post [bitUnpackContract, bitUnpackSig, bitUnpackK, X86_64.abi, X86_64.argRegs]
      pub := by sig_implies_pub [bitUnpackContract, bitUnpackSig, bitUnpackK, X86_64.abi, X86_64.argRegs]
      sat := by
        refine ⟨bitUnpackSat, ?_⟩
        sig_pre [bitUnpackContract, bitUnpackSig, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | (simp only [bitPackParams]; decide)
          | decide }

/-! ## `vg_mldsa_unpack_t1` -/

theorem t1_wp {s₀ : State} (hp : unpackT1K.pre s₀) :
    WP isa Impl.MlDsa.X86_64.Pack.unpackT1 s₀ fun s' =>
      unpackT1K.post s₀ s' ∧ Frame [pR (s₀.gpr .rsi)] s₀.mem s'.mem := by
  obtain ⟨hrd, hwr, hsep, -, -⟩ := hp
  refine WP.mono (unpackLoop_ok t1Fin_ok (c := 4) (nb := 5) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
    (v := s₀.gpr .rdi) (p := s₀.gpr .rsi) (s₀ := s₀)
    (by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _))
    (by rw [hwr]; exact List.mem_singleton_self _) hsep rfl rfl rfl rfl rfl) fun s' ⟨hc, hf, _⟩ => ⟨?_, hf⟩
  refine polyIs_of_toNat fun i hi => ?_
  have hy : inNum s₀.mem (s₀.gpr .rdi) 10 / 2 ^ (10 * i) % 2 ^ 10 < 2 ^ 10 := Nat.mod_lt _ (by decide)
  rw [hc i hi, t1Word, rotr_toNat _ (by decide) (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega), Vector.getElem_map, simpleBitUnpack_get _ _ hi,
    show bitlen t1Max = 10 by decide, ofInt_t1 hy]

theorem unpackT1_correct (s : State) (hs : unpackT1K.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Pack.unpackT1 s t s' ∧ abiPreserved s s' ∧ unpackT1K.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := Impl.MlDsa.X86_64.Pack.unpackT1)
    [.rax, .rcx, .rsi, .rdi, .r10, .r11] (t1_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2)), hb⟩

theorem unpackT1_ct : ConstantTime isa unpackT1K.pre unpackT1K.pub Impl.MlDsa.X86_64.Pack.unpackT1 :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rsi, .rsp] [])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
      fun r hr => absurd hr List.not_mem_nil)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def unpackT1Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 320⟩]
  wr := [⟨0x2000, 1024⟩]

theorem unpackT1_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Pack.unpackT1 (unpackT1Contract X86_64.abi) :=
  Verified.of_correct unpackT1_correct unpackT1_ct
    { pre := by sig_implies_pre [unpackT1Contract, unpackT1Sig, unpackT1K, X86_64.abi, X86_64.argRegs]
      post := by sig_implies_post [unpackT1Contract, unpackT1Sig, unpackT1K, X86_64.abi, X86_64.argRegs]
      pub := by sig_implies_pub [unpackT1Contract, unpackT1Sig, unpackT1K, X86_64.abi, X86_64.argRegs]
      sat := by
        refine ⟨unpackT1Sat, ?_⟩
        sig_pre [unpackT1Contract, unpackT1Sig, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | decide }

end VG.Proof.MlDsa.X86_64.Pack
