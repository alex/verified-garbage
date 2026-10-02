import VerifiedGarbage.Proof.MlDsa.X86.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.Pack.Arith

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_bit_pack`

`bitPack(f, a, b, out, len)` loads `f` into `esi`, `out` into `edi` and `b`
into `eax`, and branches on `b` to the pack loop for its width
(`packLoop_piece`). The value of a coefficient `x` is `b - x`, plus `q` if
that borrows (`subModQ`), which is `b - (x mod± q)` for a reduced `x`
(`Pack/Arith.lean`).
-/

namespace VG.Proof.MlDsa.X86.Pack.BitPack

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Proof.MlKem.X86 (Piece Piece.seq Piece.leaf Piece.verified P0 E0 LeafEnd LeafPost satState)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.X86.Pack
open VG.Proof.MlDsa.X86.Pack.SimpleBitPack (lt_bitlen)

/-- `b - x`, plus `q` if it borrows, as the code computes it. -/
def subModQ (b x : BitVec 32) : BitVec 32 :=
  b - x + (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (b.toNat < x.toNat))) &&& qImm)

theorem subModQ_toNat {b x : BitVec 32} (hb : b.toNat < q) (hx : x.toNat < q) :
    (subModQ b x).toNat = (b.toNat + q - x.toNat) % q := by
  have hq : q = 8380417 := rfl
  rw [hq] at hb hx ⊢
  unfold subModQ
  by_cases h : b.toNat < x.toNat
  · have e : (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (b.toNat < x.toNat))) &&& qImm) = 8380417#32 := by
      rw [decide_eq_true h]; decide
    rw [e, Nat.mod_eq_of_lt (by omega)]
    bv_omega
  · have e : (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (b.toNat < x.toNat))) &&& qImm) = 0#32 := by
      rw [decide_eq_false h]; decide
    rw [e, show (b.toNat + 8380417 - x.toNat) % 8380417 = b.toNat - x.toNat by omega]
    bv_omega

/-- The value `bpLd B` loads of a word. -/
abbrev bpVal (B : Nat) (w : BitVec 32) : Nat := (subModQ (BitVec.ofNat 32 B) w).toNat

theorem bpLd_ok (B : Nat) : LdOk (bpLd B) (bpVal B) := fun j s hin => by
  refine WP.keep _ ?_ (by rfl)
  unfold bpLd
  xrun [hin]
  rfl

theorem mem_bitPackParams {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    (a = 2 ∧ b = 2) ∨ (a = 4 ∧ b = 4) ∨ (a = 4095 ∧ b = 4096) ∨ (a = 131071 ∧ b = 131072) ∨
      (a = 524287 ∧ b = 524288) := by
  simp only [bitPackParams, d, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

/-- The values the loop packs are those of `BitPack`. -/
theorem bitPack_vals {m : Mem} {f : Addr} (hr : Reduced m f) {b : Nat} (hb : b ≤ q / 2)
    (hle : ∀ i < n, modPm (coeffAt m f i).toNat q ≤ b) :
    ((polyAt m f).map fun c => modPm c.val q).toList.map (fun wi => ((b : Int) - wi).toNat) =
      vals (bpVal b) m f := by
  have hbq : (BitVec.ofNat 32 b).toNat = b := by rw [BitVec.toNat_ofNat]; have : q = 8380417 := rfl; omega
  rw [Vector.toList_map, polyAt, toList_ofFn (fun i => Fin.ofNat q (coeffAt m f i).toNat), List.map_map,
    List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hx := hr i hi
  simp only [Function.comp_apply, Fin.val_ofNat, Nat.mod_eq_of_lt hx]
  rw [bpVal, subModQ_toNat (by omega) hx, hbq, sub_modPm hx hb (hle i hi)]

section
variable (s₀ : State)
/-- The input pointer `f`. -/
abbrev fP : State → BitVec 32 := (arg · 0)
/-- The output pointer `out`. -/
abbrev oP : State → BitVec 32 := (arg · 3)
/-- The length of the output. -/
abbrev oL : State → Nat := fun s₀ => (arg s₀ 4).toNat
/-- `a`. -/
abbrev aN : Nat := (arg s₀ 1).toNat
/-- `b`. -/
abbrev bN : Nat := (arg s₀ 2).toNat
end

structure Pre (s₀ : State) : Prop where
  lay : Lay 5 fP oP (fun _ => 1024) oL s₀
  ab : (aN s₀, bN s₀) ∈ bitPackParams
  len_eq : (arg s₀ 4).toNat = 32 * bitlen (aN s₀ + bN s₀)
  red : Reduced s₀.mem (iA fP s₀)
  bnd : ∀ i < n, -(aN s₀ : Int) ≤ modPm (coeffAt s₀.mem (iA fP s₀) i).toNat q ∧
    modPm (coeffAt s₀.mem (iA fP s₀) i).toNat q ≤ bN s₀

theorem Pre.of {s₀ : State} (h : (bitPackContract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [bitPackContract, bitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18, h19⟩

def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧
    arg s₀ 3 = arg s₀' 3 ∧ arg s₀ 4 = arg s₀' 4

/-- The end of every branch. -/
def Fin (s₀ s : State) : Prop :=
  LeafEnd s₀ [outR oP oL s₀] s ∧
    bytesAt s.mem (oA oP s₀) (arg s₀ 4).toNat =
      bitPack ((polyAt s₀.mem (iA fP s₀)).map fun c => modPm c.val q) (aN s₀) (bN s₀)

/-- The loop for `b = B`, of width `d = bitlen (a + b)`. -/
theorem branch {d c nb B : Nat} (hs : Shape d c nb) (hB : B ≤ 2 ^ 19) {X : State → Prop}
    (hX : ∀ s₀, Pre s₀ → X s₀ → bN s₀ = B ∧ bitlen (aN s₀ + B) = d) {h₁ : Taint.Hint VG.X86.Taint.T}
    (ht₁ : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 (256 / c)))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (ht₂ : (VG.X86.taint.check (τr loopRegs) (.block (packBody (bpLd B) d c nb)) h₂).isSome = true) :
    Piece Pre Pub (fun s₀ s => Start fP oP s₀ s ∧ X s₀) Fin (packLoop (bpLd B) d c nb) := by
  have hq : q = 8380417 := rfl
  have hBq : (BitVec.ofNat 32 B).toNat = B := by rw [BitVec.toNat_ofNat]; omega
  have hlen : ∀ s₀, Pre s₀ → X s₀ → (arg s₀ 4).toNat = 32 * d := fun s₀ h₀ hx => by
    rw [h₀.len_eq, (hX s₀ h₀ hx).1, (hX s₀ h₀ hx).2]
  refine (packLoop_piece (bpLd_ok B) hs fP oP (X := X) (fun s₀ h₀ hx => ?_)
    (fun _ _ _ _ hq => ⟨hq.1, hq.2.1, hq.2.2.2.2.1⟩) ht₁ ht₂).mono (fun _ _ _ h => h)
    (fun s₀ s h₀ ⟨⟨he, hb⟩, hx⟩ => ?_)
  · have hp := h₀.lay
    have ho : outR oP oL s₀ = ⟨oA oP s₀, 32 * d⟩ := by simp only [outR, oL, hlen s₀ h₀ hx]
    refine ⟨hp.inR_mem, by rw [← ho]; exact hp.outR_mem, by rw [← ho]; exact hp.i_o, hp.i_fit,
      by have := hp.o_fit; rwa [oL, hlen s₀ h₀ hx] at this, fun i hi => ?_⟩
    obtain ⟨e₁, e₂⟩ := hX s₀ h₀ hx
    obtain ⟨b₁, b₂⟩ := h₀.bnd i hi
    rw [e₁] at b₂
    have hxq := h₀.red i hi
    rw [hp.coeff_keep rfl hi, bpVal, subModQ_toNat (by omega) hxq, hBq, ← sub_modPm hxq (by omega) b₂, ← e₂]
    exact lt_bitlen (sub_modPm_le b₁ b₂)
  · have hp := h₀.lay
    obtain ⟨e₁, e₂⟩ := hX s₀ h₀ hx
    have ho : outR oP oL s₀ = ⟨oA oP s₀, 32 * d⟩ := by simp only [outR, oL, hlen s₀ h₀ hx]
    refine ⟨⟨by rw [ho]; exact he.frame, he.esp, he.rd, he.wr⟩, ?_⟩
    rw [hlen s₀ h₀ hx, hb, packed, bitPack_eq, e₁, e₂,
      bitPack_vals h₀.red (by omega) (fun i hi => by rw [← e₁]; exact (h₀.bnd i hi).2)]
    refine congrArg (fun L => bitsToBytes (fieldBits d L)) (List.map_congr_left fun i hi => ?_)
    rw [hp.coeff_keep rfl (List.mem_range.mp hi)]

/-- The shapes of the widths. -/
theorem sh3 : Shape 3 8 3 := ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
theorem sh4 : Shape 4 2 1 := ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
theorem sh13 : Shape 13 8 13 := ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
theorem sh18 : Shape 18 4 9 := ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
theorem sh20 : Shape 20 2 5 := ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩

/-- The branch for `b = B` is the one for `a = A`, of width `d'`. -/
theorem pick {s₀ : State} (h₀ : Pre s₀) {A B d' : Nat} (hd : bitlen (A + B) = d') (e : (arg s₀ 2).toNat = B)
    (hA : ∀ a, (a = 2 ∧ B = 2) ∨ (a = 4 ∧ B = 4) ∨ (a = 4095 ∧ B = 4096) ∨ (a = 131071 ∧ B = 131072) ∨
      (a = 524287 ∧ B = 524288) → a = A) : bN s₀ = B ∧ bitlen (aN s₀ + B) = d' := by
  have := mem_bitPackParams h₀.ab
  rw [show bN s₀ = B from e] at this
  rw [hA _ this]; exact ⟨e, hd⟩

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) Fin
    (.seq (.block (ldArgs 0 3 2))
      (sel 2 (packLoop (bpLd 2) 3 8 3)
        (sel 4 (packLoop (bpLd 4) 4 2 1)
          (sel 4096 (packLoop (bpLd 4096) 13 8 13)
            (sel 131072 (packLoop (bpLd 131072) 18 4 9) (packLoop (bpLd 524288) 20 2 5)))))) := by
  have hw : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → arg s₀ 2 = arg s₀' 2 := fun _ _ _ _ hq => hq.2.2.2.1
  refine Piece.seq (ldArgs_piece (k := 5) (by decide) (by decide) (by decide) (fun _ h => h.lay)
    (fun _ _ _ _ hq => hq.1) (by taint_decide)) ?_
  refine sel_piece (arg · 2) (by decide) hw (by taint_decide)
    (branch sh3 (by decide) (fun s₀ h₀ ⟨_, e⟩ => pick h₀ (A := 2) (by decide) e fun _ _ => by omega)
      (by taint_decide) (by taint_decide)) ?_
  refine sel_piece (arg · 2) (by decide) hw (by taint_decide)
    (branch sh4 (by decide) (fun s₀ h₀ ⟨_, e⟩ => pick h₀ (A := 4) (by decide) e fun _ _ => by omega)
      (by taint_decide) (by taint_decide)) ?_
  refine sel_piece (arg · 2) (by decide) hw (by taint_decide)
    (branch sh13 (by decide) (fun s₀ h₀ ⟨_, e⟩ => pick h₀ (A := 4095) (by decide) e fun _ _ => by omega)
      (by taint_decide) (by taint_decide)) ?_
  refine sel_piece (arg · 2) (by decide) hw (by taint_decide)
    (branch sh18 (by decide) (fun s₀ h₀ ⟨_, e⟩ => pick h₀ (A := 131071) (by decide) e fun _ _ => by omega)
      (by taint_decide) (by taint_decide)) ?_
  refine (branch sh20 (B := 524288) (by decide) (fun s₀ h₀ ⟨⟨⟨⟨_, e₂⟩, e₄⟩, e₄₀⟩, e₁₃⟩ =>
      pick h₀ (A := 524287) (by decide) (by have := mem_bitPackParams h₀.ab; simp only [aN, bN] at this; omega)
        fun _ _ => by omega)
      (by taint_decide) (by taint_decide)).mono (fun _ _ _ ⟨⟨h, _⟩, hx⟩ => ⟨h, hx⟩) fun _ _ _ h => h

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlDsa.X86.Pack.bitPack :=
  Piece.leaf (fun s₀ => [outR oP oL s₀]) (NoSp.of_all (by decide +kernel)) (fun _ h => h.lay.leafE)
    (fun _ h => h.lay.leafW) (fun _ _ _ _ hq => hq.1) (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.1, h⟩)

/-- Memory with the arguments `0`, `2`, `2`, `0x400` and `96` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5008 then 2 else if a = 0x500c then 2 else if a = 0x5011 then 4 else if a = 0x5014 then 96 else 0

theorem verified : Verified X86.target Impl.MlDsa.X86.Pack.bitPack (bitPackContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [bitPackContract, bitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [bitPackContract, bitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact hinv.2
  · let st := satState satMem [⟨0, 1024⟩] [⟨0x400, 96⟩, ⟨0x5004, 20⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 2 := by decide
    have a2 : arg st 2 = 2 := by decide
    have a3 : arg st 3 = 0x400 := by decide
    have a4 : arg st 4 = 96 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    have hz : ∀ i < 256, coeffAt satMem (BitVec.setWidth 64 (0 : BitVec 32)) i = 0 := fun i hi =>
      coeffAt_low (fun a ha => by
        show satMem a = 0
        rw [satMem, ite_low ha (b := 0x5008) (by decide), ite_low ha (b := 0x500c) (by decide),
          ite_low ha (b := 0x5011) (by decide), ite_low ha (b := 0x5014) (by decide)]) (by decide) hi
    refine ⟨st, ?_⟩
    sig_pre [bitPackContract, bitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, a4, e]
    and_intros
    all_goals first
      | rfl
      | exact Region.disjoint_of_sep (by decide)
      | (simp only [bitPackParams]; decide)
      | exact fun i hi => by rw [hz i hi]; decide
      | decide

end VG.Proof.MlDsa.X86.Pack.BitPack
