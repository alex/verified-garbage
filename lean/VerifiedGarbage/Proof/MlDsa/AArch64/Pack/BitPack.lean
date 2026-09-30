import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.Pack.Arith

/-!
# ML-DSA on AArch64: `vg_mldsa_bit_pack`

Untrusted: everything here is checked by Lean. The value of a coefficient
`x` is `b - x` in 64 bits, plus `q` times its sign bit (`subModQ`), which is
`b - (x mod± q)` for a reduced `x` (`Pack/Arith.lean`). The loop is proven
once for every width (`packLoop_ok`), and the function by its five cases,
which the length chooses.
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Only wp_ldrw wp_sub wp_lsr wp_madd wp_mov wp_movImm wp_nil abi_of agree_of)
open VG.Proof.MlDsa.Pack

/-- `b - x`, plus `q` if it is negative, as the code computes it in 64 bits. -/
def subModQ (b x : BitVec 64) : BitVec 64 := b - x + ((b - x) >>> 63) * BitVec.ofNat 64 q

theorem subModQ_toNat {b x : Nat} (hb : b < q) (hx : x < q) :
    (subModQ (BitVec.ofNat 64 b) (BitVec.ofNat 64 x)).toNat = (b + q - x) % q := by
  have hq : q = 8380417 := rfl
  have hs : (BitVec.ofNat 64 b - BitVec.ofNat 64 x).toNat = (2 ^ 64 - x + b) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := b) (by omega),
      Nat.mod_eq_of_lt (a := x) (by omega)]
  unfold subModQ
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hs,
    BitVec.toNat_ofNat, hq]
  by_cases h : x ≤ b
  · rw [show (2 ^ 64 - x + b) % 2 ^ 64 = b - x by omega]
    omega
  · rw [show (2 ^ 64 - x + b) % 2 ^ 64 = 2 ^ 64 - x + b by omega]
    omega

/-- The value `bpLd` loads of a word, for `b = B`. -/
abbrev bpVal (B : Nat) (w : BitVec 32) : Nat := (subModQ (BitVec.ofNat 64 B) (w.setWidth 64)).toNat

theorem bpLd_ok (B : Nat) : LdOk bpLd (bpVal B) (BitVec.ofNat 64 B) (BitVec.ofNat 64 q) :=
  fun j s h12 h13 hj hin =>
  wp_ldrw ⟨by omega, by omega⟩ rfl hin fun s₁ o₁ e₁ => wp_sub fun s₂ o₂ e₂ => wp_lsr (by decide) fun s₃ o₃ e₃ =>
    wp_madd fun s₄ o₄ e₄ => wp_nil ⟨by
      rw [e₄, e₃, o₃.get .x10, o₃.get .x13, e₂, o₂.get .x13, o₁.get .x12, o₁.get .x13, h12, h13, e₁]; rfl,
      (((o₁.trans o₂).trans o₃).trans o₄).mono⟩

/-- The arguments and the width, by the length. -/
theorem bp_cases {a b len : Nat} (hab : (a, b) ∈ bitPackParams) (hlen : len = 32 * bitlen (a + b)) :
    (b = 2 ∧ bitlen (a + b) = 3 ∧ len = 96) ∨ (b = 4 ∧ bitlen (a + b) = 4 ∧ len = 128) ∨
      (b = 4096 ∧ bitlen (a + b) = 13 ∧ len = 416) ∨ (b = 131072 ∧ bitlen (a + b) = 18 ∧ len = 576) ∨
      (b = 524288 ∧ bitlen (a + b) = 20 ∧ len = 640) := by
  rcases mem_bitPackParams hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .inl ⟨rfl, rfl, hlen⟩
  · exact .inr (.inl ⟨rfl, rfl, hlen⟩)
  · exact .inr (.inr (.inl ⟨rfl, rfl, hlen⟩))
  · exact .inr (.inr (.inr (.inl ⟨rfl, rfl, hlen⟩)))
  · exact .inr (.inr (.inr (.inr ⟨rfl, rfl, hlen⟩)))

/-- The values the loop packs are those of `BitPack`. -/
theorem bitPack_vals {m : Mem} {f : Addr} (hr : Reduced m f) {b : Nat} (hb : b ≤ q / 2)
    (hle : ∀ i < n, modPm (coeffAt m f i).toNat q ≤ b) :
    ((polyAt m f).map fun c => modPm c.val q).toList.map (fun wi => ((b : Int) - wi).toNat) =
      vals (bpVal b) m f := by
  rw [Vector.toList_map, polyAt, toList_ofFn (fun i => Fin.ofNat q (coeffAt m f i).toNat), List.map_map,
    List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hx := hr i hi
  simp only [Function.comp_apply, Fin.val_ofNat, Nat.mod_eq_of_lt hx]
  rw [bpVal, ← BitVec.ofNat_toNat, subModQ_toNat (by omega) hx, sub_modPm hx hb (hle i hi)]

theorem bp_wp {s₀ : State} (hp : bitPackK.pre s₀) :
    WP isa Impl.MlDsa.AArch64.Pack.bitPack s₀ fun s' => bitPackK.post s₀ s' := by
  obtain ⟨hrd, hwr, hsep, hab, hlen, hred, hbnd⟩ := hp
  have hc := bp_cases hab hlen
  have go : ∀ {d c nb B : Nat}, Shape d c nb → wArg s₀ .x2 = B → bitlen (wArg s₀ .x1 + wArg s₀ .x2) = d →
      ∀ s : State, s.gpr .x0 = s₀.gpr .x0 → s.gpr .x2 = s₀.gpr .x3 → s.gpr .x13 = BitVec.ofNat 64 q →
      s.rd = s₀.rd → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (bpWidth B d c nb) s fun s' => bitPackK.post s₀ s' := by
    intro d c nb B hs hB hd s h0 h2 h13 h3 h4 h5
    rw [hd] at hlen
    have hq : q = 8380417 := rfl
    have hB19 : B ≤ 2 ^ 19 := by omega
    refine WP.seq ?_
    rw [← List.append_nil (Impl.MlKem.AArch64.movImm _ _)]
    refine wp_movImm fun s₁ o₁ e₁ => wp_nil ?_
    refine WP.mono (packLoop_ok (bpLd_ok B) hs (f := s₀.gpr .x0) (o := s₀.gpr .x3) (s₀ := s₀)
      (by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hwr, hlen]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hsep)
      (fun i hi => ?_) (by rw [o₁.get .x0, h0]) (by rw [o₁.get .x2, h2]) e₁ (by rw [o₁.get .x13, h13])
      (by rw [o₁.rd, h3]) (by rw [o₁.wr, h4]) (by rw [o₁.mem, h5]))
      fun s' ⟨hB', _, _⟩ => ?_
    · obtain ⟨h₁, h₂⟩ := hbnd i hi
      rw [hB] at h₂
      have hx := hred i hi
      rw [bpVal, ← BitVec.ofNat_toNat, subModQ_toNat (by omega) hx, ← sub_modPm hx (by omega) h₂, ← hd, hB]
      exact lt_bitlen (sub_modPm_le h₁ h₂)
    · show bytesAt s'.mem (s₀.gpr .x3) (s₀.gpr .x4).toNat = bitPack _ _ _
      rw [hlen, hB', bitPack_eq, bitPack_vals hred (by omega) (fun i hi => (hbnd i hi).2), hd,
        hB]
  unfold Impl.MlDsa.AArch64.Pack.bitPack
  refine WP.seq (wp_mov fun s₁ o₁ e₁ => ?_)
  rw [← List.append_nil (Impl.MlKem.AArch64.movImm _ _)]
  refine wp_movImm fun s₂ o₂ e₂ => wp_nil ?_
  have k₂ := o₁.trans o₂
  have h0 : s₂.gpr .x0 = s₀.gpr .x0 := k₂.get .x0
  have h2 : s₂.gpr .x2 = s₀.gpr .x3 := by rw [o₂.get .x2, e₁]
  have h4 : s₂.gpr .x4 = s₀.gpr .x4 := k₂.get .x4
  have h13 : s₂.gpr .x13 = BitVec.ofNat 64 q := e₂
  refine sel_ok (by decide) (fun s₃ o₃ h => ?_) (fun s₃ o₃ h => ?_)
  · rw [h4] at h
    exact go (d := 3) (c := 8) (nb := 3) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₃ (by rw [o₃.get .x0, h0]) (by rw [o₃.get .x2, h2]) (by rw [o₃.get .x13, h13])
      (by rw [o₃.rd, k₂.rd]) (by rw [o₃.wr, k₂.wr]) (by rw [o₃.mem, k₂.mem])
  have k₃ := k₂.trans o₃
  rw [h4] at h
  refine sel_ok (by decide) (fun s₄ o₄ h' => ?_) (fun s₄ o₄ h' => ?_)
  · rw [o₃.get .x4, h4] at h'
    exact go (d := 4) (c := 2) (nb := 1) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₄ (by rw [o₄.get .x0, k₃.get .x0]) (by rw [o₄.get .x2, o₃.get .x2, h2])
      (by rw [o₄.get .x13, o₃.get .x13, h13]) (by rw [o₄.rd, k₃.rd]) (by rw [o₄.wr, k₃.wr])
      (by rw [o₄.mem, k₃.mem])
  have k₄ := k₃.trans o₄
  rw [o₃.get .x4, h4] at h'
  refine sel_ok (by decide) (fun s₅ o₅ h'' => ?_) (fun s₅ o₅ h'' => ?_)
  · rw [o₄.get .x4, o₃.get .x4, h4] at h''
    exact go (d := 13) (c := 8) (nb := 13) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₅ (by rw [o₅.get .x0, k₄.get .x0]) (by rw [o₅.get .x2, o₄.get .x2, o₃.get .x2, h2])
      (by rw [o₅.get .x13, o₄.get .x13, o₃.get .x13, h13]) (by rw [o₅.rd, k₄.rd]) (by rw [o₅.wr, k₄.wr])
      (by rw [o₅.mem, k₄.mem])
  have k₅ := k₄.trans o₅
  rw [o₄.get .x4, o₃.get .x4, h4] at h''
  refine sel_ok (by decide) (fun s₆ o₆ h''' => ?_) (fun s₆ o₆ h''' => ?_)
  · rw [o₅.get .x4, o₄.get .x4, o₃.get .x4, h4] at h'''
    exact go (d := 18) (c := 4) (nb := 9) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₆ (by rw [o₆.get .x0, k₅.get .x0])
      (by rw [o₆.get .x2, o₅.get .x2, o₄.get .x2, o₃.get .x2, h2])
      (by rw [o₆.get .x13, o₅.get .x13, o₄.get .x13, o₃.get .x13, h13]) (by rw [o₆.rd, k₅.rd])
      (by rw [o₆.wr, k₅.wr]) (by rw [o₆.mem, k₅.mem])
  · rw [o₅.get .x4, o₄.get .x4, o₃.get .x4, h4] at h'''
    exact go (d := 20) (c := 2) (nb := 5) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by omega) (by omega) s₆ (by rw [o₆.get .x0, k₅.get .x0])
      (by rw [o₆.get .x2, o₅.get .x2, o₄.get .x2, o₃.get .x2, h2])
      (by rw [o₆.get .x13, o₅.get .x13, o₄.get .x13, o₃.get .x13, h13]) (by rw [o₆.rd, k₅.rd])
      (by rw [o₆.wr, k₅.wr]) (by rw [o₆.mem, k₅.mem])

theorem bitPack_correct (s : State) (hs : bitPackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Pack.bitPack s t s' ∧ abiPreserved s s' ∧ bitPackK.post s s' := by
  obtain ⟨t, s', he, hb⟩ := bp_wp hs
  exact ⟨t, s', he, abi_of rfl (by lit_decide) he, hb⟩

theorem bitPack_ct : ConstantTime isa bitPackK.pre bitPackK.pub Impl.MlDsa.AArch64.Pack.bitPack :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x3, .x4])
    (fun _ _ _ _ ⟨h0, h3, h4, hsp⟩ => agree_of hsp (by simp [h0, h3, h4])) (by taint_decide)

/-- A state satisfying the precondition. -/
def bitPackSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 2 | .x2 => 2 | .x3 => 0x2000 | .x4 => 96 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 96⟩]

theorem bitPack_verified : Verified AArch64.target Impl.MlDsa.AArch64.Pack.bitPack (bitPackContract AArch64.abi) :=
  Verified.of_correct bitPack_correct bitPack_ct
    { pre := by sig_implies_pre [bitPackContract, bitPackSig, bitPackK, AArch64.abi, AArch64.argRegs]
      post := by sig_implies_post [bitPackContract, bitPackSig, bitPackK, AArch64.abi, AArch64.argRegs]
      pub := by sig_implies_pub [bitPackContract, bitPackSig, bitPackK, AArch64.abi, AArch64.argRegs]
      sat := by
        refine ⟨bitPackSat, ?_⟩
        sig_pre [bitPackContract, bitPackSig, AArch64.abi, AArch64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | exact fun i _ => by rw [coeffAt_zero]; decide
          | (simp only [bitPackParams]; decide)
          | decide }

end VG.Proof.MlDsa.AArch64.Pack
