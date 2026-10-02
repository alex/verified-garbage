import VerifiedGarbage.Proof.MlDsa.X86.Pack.BitPack

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_bit_unpack` and `vg_mldsa_unpack_t1`

`bitUnpack(v, len, a, b, f)` loads `v` into `esi`, `f` into `edi` and `b` into
`eax`, and branches on `b` to the unpack loop for its width
(`unpackLoop_piece`); `unpackT1(v, f)` is the loop for 10-bit fields. The
coefficient of a field `y` is `b - y`, plus `q` if that borrows (`subModQ`),
which is `b - y` in `ℤ_q` (`Pack/Arith.lean`), or `y · 2¹³`.
-/

namespace VG.Proof.MlDsa.X86.Pack.Unpack

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Proof.MlKem.X86 (Piece Piece.seq Piece.leaf Piece.verified P0 E0 LeafEnd LeafPost satState rotr_small)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.X86.Pack
open VG.Proof.MlDsa.X86.Pack.BitPack (subModQ subModQ_toNat mem_bitPackParams sh3 sh4 sh13 sh18 sh20)

/-- The word `buFin B` stores for the field `y`. -/
abbrev buWord (B y : Nat) : BitVec 32 := subModQ (BitVec.ofNat 32 B) (BitVec.ofNat 32 y)

theorem buFin_ok (B d : Nat) : FinOk (buFin B) d (buWord B) := fun j s hout _ => by
  refine WP.keep _ ?_ (by rfl)
  unfold buFin
  xrun [hout]
  rw [buWord, BitVec.ofNat_toNat]
  rfl

/-- The word `t1Fin` stores for the field `y`. -/
abbrev t1Word (y : Nat) : BitVec 32 := (BitVec.ofNat 32 y).rotateRight 19

theorem t1Fin_ok : FinOk t1Fin 10 t1Word := fun j s hout _ => by
  refine WP.keep _ ?_ (by rfl)
  unfold t1Fin
  xrun [hout]
  rw [t1Word, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A field of `d ≤ 20` bits of the input. -/
theorem field_lt (X d k : Nat) (hd : d ≤ 20) : X / 2 ^ (d * k) % 2 ^ d < 2 ^ 20 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos d)) (Nat.pow_le_pow_right (by decide) hd)

/-! ## `vg_mldsa_bit_unpack` -/

namespace BU

section
variable (s₀ : State)
/-- The input pointer `v`. -/
abbrev vP : State → BitVec 32 := (arg · 0)
/-- Its length. -/
abbrev vL : State → Nat := fun s₀ => (arg s₀ 1).toNat
/-- The output pointer `f`. -/
abbrev fP : State → BitVec 32 := (arg · 4)
/-- `a`. -/
abbrev aN : Nat := (arg s₀ 2).toNat
/-- `b`. -/
abbrev bN : Nat := (arg s₀ 3).toNat
end

structure Pre (s₀ : State) : Prop where
  lay : Lay 5 vP fP vL (fun _ => 1024) s₀
  ab : (aN s₀, bN s₀) ∈ bitPackParams
  len_eq : (arg s₀ 1).toNat = 32 * bitlen (aN s₀ + bN s₀)

theorem Pre.of {s₀ : State} (h : (bitUnpackContract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17⟩

def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧
    arg s₀ 3 = arg s₀' 3 ∧ arg s₀ 4 = arg s₀' 4

/-- The end of every branch. -/
def Fin (s₀ s : State) : Prop :=
  LeafEnd s₀ [outR fP (fun _ => 1024) s₀] s ∧
    PolyIs s.mem (oA fP s₀) (toRq (bitUnpack (bytesAt s₀.mem (iA vP s₀) (arg s₀ 1).toNat) (aN s₀) (bN s₀)))

/-- The loop for `b = B`, of width `d = bitlen (a + b)`. -/
theorem branch {d c nb B : Nat} (hs : Shape d c nb) (hB : B ≤ 2 ^ 19) {X : State → Prop}
    (hX : ∀ s₀, Pre s₀ → X s₀ → bN s₀ = B ∧ bitlen (aN s₀ + B) = d) {h₁ : Taint.Hint VG.X86.Taint.T}
    (ht₁ : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 (256 / c)))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (ht₂ : (VG.X86.taint.check (τr loopRegs) (.block (unpackBody (buFin B) d c nb)) h₂).isSome = true) :
    Piece Pre Pub (fun s₀ s => Start vP fP s₀ s ∧ X s₀) Fin (unpackLoop (buFin B) d c nb) := by
  have hq : q = 8380417 := rfl
  have hlen : ∀ s₀, Pre s₀ → X s₀ → (arg s₀ 1).toNat = 32 * d := fun s₀ h₀ hx => by
    rw [h₀.len_eq, (hX s₀ h₀ hx).1, (hX s₀ h₀ hx).2]
  refine (unpackLoop_piece (buFin_ok B d) hs vP fP (X := X) (fun s₀ h₀ hx => ?_)
    (fun _ _ _ _ hq => ⟨hq.1, hq.2.1, hq.2.2.2.2.2⟩) ht₁ ht₂).mono (fun _ _ _ h => h)
    (fun s₀ s h₀ ⟨⟨he, hc⟩, hx⟩ => ?_)
  · have hp := h₀.lay
    have hi : inR vP vL s₀ = ⟨iA vP s₀, 32 * d⟩ := by simp only [inR, vL, hlen s₀ h₀ hx]
    exact ⟨by rw [← hi]; exact hp.inR_mem, hp.outR_mem, by rw [← hi]; exact hp.i_o,
      by have := hp.i_fit; rwa [vL, hlen s₀ h₀ hx] at this, hp.o_fit⟩
  · have hp := h₀.lay
    obtain ⟨e₁, e₂⟩ := hX s₀ h₀ hx
    refine ⟨he, polyIs_of_toNat fun i hi => ?_⟩
    have hy := field_lt (inNum (P0 s₀).mem (iA vP s₀) d) d i hs.d20
    have hy' := hy
    unfold inNum at hy'
    rw [hp.bytes_keep (by simp only [vL]; rw [hlen s₀ h₀ hx])] at hy'
    rw [hc i hi, buWord, subModQ_toNat (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show B < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega), toRq, Vector.getElem_map, bitUnpack_get _ _ _ hi,
      hlen s₀ h₀ hx, e₁, e₂, ofInt_sub (by omega), inNum, hp.bytes_keep (by simp only [vL]; rw [hlen s₀ h₀ hx])]

/-- The branch for `b = B` is the one for `a = A`, of width `d'`. -/
theorem pick {s₀ : State} (h₀ : Pre s₀) {A B d' : Nat} (hd : bitlen (A + B) = d') (e : (arg s₀ 3).toNat = B)
    (hA : ∀ a, (a = 2 ∧ B = 2) ∨ (a = 4 ∧ B = 4) ∨ (a = 4095 ∧ B = 4096) ∨ (a = 131071 ∧ B = 131072) ∨
      (a = 524287 ∧ B = 524288) → a = A) : bN s₀ = B ∧ bitlen (aN s₀ + B) = d' := by
  have := mem_bitPackParams h₀.ab
  rw [show bN s₀ = B from e] at this
  rw [hA _ this]; exact ⟨e, hd⟩

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) Fin
    (.seq (.block (ldArgs 0 4 3))
      (sel 2 (unpackLoop (buFin 2) 3 8 3)
        (sel 4 (unpackLoop (buFin 4) 4 2 1)
          (sel 4096 (unpackLoop (buFin 4096) 13 8 13)
            (sel 131072 (unpackLoop (buFin 131072) 18 4 9) (unpackLoop (buFin 524288) 20 2 5)))))) := by
  have hw : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → arg s₀ 3 = arg s₀' 3 := fun _ _ _ _ hq => hq.2.2.2.2.1
  refine Piece.seq (ldArgs_piece (k := 5) (by decide) (by decide) (by decide) (fun _ h => h.lay)
    (fun _ _ _ _ hq => hq.1) (by taint_decide)) ?_
  refine sel_piece (arg · 3) (by decide) hw (by taint_decide)
    (branch sh3 (by decide) (fun s₀ h₀ ⟨_, e⟩ => pick h₀ (A := 2) (by decide) e fun _ _ => by omega)
      (by taint_decide) (by taint_decide)) ?_
  refine sel_piece (arg · 3) (by decide) hw (by taint_decide)
    (branch sh4 (by decide) (fun s₀ h₀ ⟨_, e⟩ => pick h₀ (A := 4) (by decide) e fun _ _ => by omega)
      (by taint_decide) (by taint_decide)) ?_
  refine sel_piece (arg · 3) (by decide) hw (by taint_decide)
    (branch sh13 (by decide) (fun s₀ h₀ ⟨_, e⟩ => pick h₀ (A := 4095) (by decide) e fun _ _ => by omega)
      (by taint_decide) (by taint_decide)) ?_
  refine sel_piece (arg · 3) (by decide) hw (by taint_decide)
    (branch sh18 (by decide) (fun s₀ h₀ ⟨_, e⟩ => pick h₀ (A := 131071) (by decide) e fun _ _ => by omega)
      (by taint_decide) (by taint_decide)) ?_
  refine (branch sh20 (B := 524288) (by decide) (fun s₀ h₀ ⟨⟨⟨⟨_, e₂⟩, e₄⟩, e₄₀⟩, e₁₃⟩ =>
      pick h₀ (A := 524287) (by decide) (by have := mem_bitPackParams h₀.ab; simp only [aN, bN] at this; omega)
        fun _ _ => by omega)
      (by taint_decide) (by taint_decide)).mono (fun _ _ _ ⟨⟨h, _⟩, hx⟩ => ⟨h, hx⟩) fun _ _ _ h => h

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlDsa.X86.Pack.bitUnpack :=
  Piece.leaf (fun s₀ => [outR fP (fun _ => 1024) s₀]) (NoSp.of_all (by decide +kernel))
    (fun _ h => h.lay.leafE) (fun _ h => h.lay.leafW) (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.1, h⟩)

/-- Memory with the arguments `0`, `96`, `2`, `2` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5008 then 96 else if a = 0x500c then 2 else if a = 0x5010 then 2 else if a = 0x5015 then 4 else 0

theorem verified : Verified X86.target Impl.MlDsa.X86.Pack.bitUnpack (bitUnpackContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact hinv.2
  · let st := satState satMem [⟨0, 96⟩] [⟨0x400, 1024⟩, ⟨0x5004, 20⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 96 := by decide
    have a2 : arg st 2 = 2 := by decide
    have a3 : arg st 3 = 2 := by decide
    have a4 : arg st 4 = 0x400 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, a4, e]
    and_intros
    all_goals first
      | rfl
      | exact Region.disjoint_of_sep (by decide)
      | (simp only [bitPackParams]; decide)
      | decide

end BU

/-! ## `vg_mldsa_unpack_t1` -/

namespace T1

/-- The input pointer `v`. -/
abbrev vP : State → BitVec 32 := (arg · 0)
/-- The output pointer `f`. -/
abbrev fP : State → BitVec 32 := (arg · 1)

abbrev Pre (s₀ : State) : Prop := Lay 2 vP fP (fun _ => 320) (fun _ => 1024) s₀

theorem Pre.of {s₀ : State} (h : (unpackT1Contract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [unpackT1Contract, unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

def Pub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

/-- The end of the loop. -/
def Fin (s₀ s : State) : Prop :=
  LeafEnd s₀ [outR fP (fun _ => 1024) s₀] s ∧
    PolyIs s.mem (oA fP s₀) ((simpleBitUnpack (bytesAt s₀.mem (iA vP s₀) 320) t1Max).map
      fun c => ofInt (c * 2 ^ d : Nat))

theorem sh10 : Shape 10 4 5 := ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) Fin
    (.seq (.block (ldPtrs 0 1)) (unpackLoop t1Fin 10 4 5)) := by
  refine Piece.seq (ldPtrs_piece (k := 2) (by decide) (by decide) (fun _ h => h)
    (fun _ _ _ _ hq => hq.1) (by taint_decide)) ?_
  refine (unpackLoop_piece t1Fin_ok sh10 vP fP (X := fun _ => True) (fun s₀ hp _ => ?_)
    (fun _ _ _ _ hq => hq) (by taint_decide) (by taint_decide)).mono (fun _ _ _ h => h)
    (fun s₀ s hp ⟨⟨he, hc⟩, _⟩ => ⟨he, polyIs_of_toNat fun i hi => ?_⟩)
  · exact ⟨hp.inR_mem, hp.outR_mem, hp.i_o, hp.i_fit, hp.o_fit⟩
  · rw [hc i hi, inNum, hp.bytes_keep (by decide)]
    have hy := Nat.mod_lt (Proof.MlKem.digits 8 ((bytesAt s₀.mem (iA vP s₀) 320).map (·.toNat)) / 2 ^ (10 * i))
      (show 2 ^ 10 > 0 by decide)
    rw [t1Word, rotr_small _ (by decide) (by decide) (by rw [BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega), show 32 - 19 = 13 from rfl,
      Vector.getElem_map, simpleBitUnpack_get _ _ hi, show bitlen t1Max = 10 by decide, ofInt_t1 hy]

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlDsa.X86.Pack.unpackT1 :=
  Piece.leaf (fun s₀ => [outR fP (fun _ => 1024) s₀]) (NoSp.of_all (by decide +kernel))
    (fun _ h => h.leafE) (fun _ h => h.leafW) (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.1, h⟩)

/-- Memory with the arguments `0` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 4 else 0

theorem verified : Verified X86.target Impl.MlDsa.X86.Pack.unpackT1 (unpackT1Contract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [unpackT1Contract, unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [unpackT1Contract, unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact hinv.2
  · refine ⟨satState satMem [⟨0, 320⟩] [⟨0x400, 1024⟩, ⟨0x5004, 8⟩], ?_⟩
    sig_sat_check [unpackT1Contract, unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

end T1

end VG.Proof.MlDsa.X86.Pack.Unpack
