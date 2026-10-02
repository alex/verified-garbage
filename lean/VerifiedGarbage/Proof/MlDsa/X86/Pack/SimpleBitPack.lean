import VerifiedGarbage.Proof.MlDsa.X86.Pack.Top
import VerifiedGarbage.Impl.MlDsa.X86.Pack.Encode
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_simple_bit_pack`

`simpleBitPack(f, b, out, len)` loads `f` into `esi`, `out` into `edi` and `b`
into `eax`, and branches on `b` (15, 43 or 1023) to the pack loop for its
width (`packLoop_piece`), whose value of a coefficient is the coefficient.
-/

namespace VG.Proof.MlDsa.X86.Pack.SimpleBitPack

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Proof.MlKem.X86 (Piece Piece.seq Piece.leaf Piece.verified P0 E0 LeafEnd LeafPost satState)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.X86.Pack

theorem sbpLd_ok : LdOk sbpLd BitVec.toNat := fun j s hin => by
  refine WP.keep _ ?_ (by rfl)
  unfold sbpLd
  xrun [hin]

/-- A value at most `b` is less than `2 ^ bitlen b`. -/
theorem lt_bitlen {x b : Nat} (h : x ≤ b) : x < 2 ^ bitlen b := Nat.lt_of_le_of_lt h Nat.lt_log2_self

section
variable (s₀ : State)
/-- The input pointer `f`. -/
abbrev fP : State → BitVec 32 := (arg · 0)
/-- The output pointer `out`. -/
abbrev oP : State → BitVec 32 := (arg · 2)
/-- The length of the output. -/
abbrev oL : State → Nat := fun s₀ => (arg s₀ 3).toNat
/-- The bound `b`. -/
abbrev bN : Nat := (arg s₀ 1).toNat
end

structure Pre (s₀ : State) : Prop where
  lay : Lay 4 fP oP (fun _ => 1024) oL s₀
  b_mem : bN s₀ ∈ simpleBitPackBounds
  len_eq : (arg s₀ 3).toNat = 32 * bitlen (bN s₀)
  le : ∀ i < n, (coeffAt s₀.mem (iA fP s₀) i).toNat ≤ bN s₀

theorem Pre.of {s₀ : State} (h : (simpleBitPackContract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [simpleBitPackContract, simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18⟩

def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧ arg s₀ 3 = arg s₀' 3

/-- The end of every branch. -/
def Fin (s₀ s : State) : Prop :=
  LeafEnd s₀ [outR oP oL s₀] s ∧
    bytesAt s.mem (oA oP s₀) (arg s₀ 3).toNat = simpleBitPack (natPolyAt s₀.mem (iA fP s₀)) (bN s₀)

/-- The loop for the width `d = bitlen v` of `b = v`. -/
theorem branch {d c nb v : Nat} (hs : Shape d c nb) (hv : bitlen v = d) {X : State → Prop}
    (hX : ∀ s₀, Pre s₀ → X s₀ → bN s₀ = v) {h₁ : Taint.Hint VG.X86.Taint.T}
    (ht₁ : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 (256 / c)))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (ht₂ : (VG.X86.taint.check (τr loopRegs) (.block (packBody sbpLd d c nb)) h₂).isSome = true) :
    Piece Pre Pub (fun s₀ s => Start fP oP s₀ s ∧ X s₀) Fin (packLoop sbpLd d c nb) := by
  have hlen : ∀ s₀, Pre s₀ → X s₀ → (arg s₀ 3).toNat = 32 * d := fun s₀ h₀ hx => by
    rw [h₀.len_eq, hX s₀ h₀ hx, hv]
  refine (packLoop_piece sbpLd_ok hs fP oP (X := X) (fun s₀ h₀ hx => ?_)
    (fun _ _ _ _ hq => ⟨hq.1, hq.2.1, hq.2.2.2.1⟩) ht₁ ht₂).mono (fun _ _ _ h => h)
    (fun s₀ s h₀ ⟨⟨he, hb⟩, hx⟩ => ?_)
  · have hp := h₀.lay
    have ho : outR oP oL s₀ = ⟨oA oP s₀, 32 * d⟩ := by simp only [outR, oL, hlen s₀ h₀ hx]
    refine ⟨hp.inR_mem, by rw [← ho]; exact hp.outR_mem, by rw [← ho]; exact hp.i_o, hp.i_fit,
      by have := hp.o_fit; rwa [oL, hlen s₀ h₀ hx] at this, fun i hi => ?_⟩
    rw [hp.coeff_keep rfl hi, ← hv, ← hX s₀ h₀ hx]
    exact lt_bitlen (h₀.le i hi)
  · have hp := h₀.lay
    have ho : outR oP oL s₀ = ⟨oA oP s₀, 32 * d⟩ := by simp only [outR, oL, hlen s₀ h₀ hx]
    refine ⟨⟨by rw [ho]; exact he.frame, he.esp, he.rd, he.wr⟩, ?_⟩
    rw [hlen s₀ h₀ hx, hb, packed, simpleBitPack_eq, natPolyAt_toList, hX s₀ h₀ hx, hv]
    refine congrArg (fun L => bitsToBytes (fieldBits d L)) (List.map_congr_left fun i hi => ?_)
    rw [hp.coeff_keep rfl (List.mem_range.mp hi)]

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) Fin
    (.seq (.block (ldArgs 0 2 1))
      (sel 15 (packLoop sbpLd 4 2 1) (sel 43 (packLoop sbpLd 6 4 3) (packLoop sbpLd 10 4 5)))) := by
  refine Piece.seq (ldArgs_piece (k := 4) (by decide) (by decide) (by decide) (fun _ h => h.lay)
    (fun _ _ _ _ hq => hq.1) (by taint_decide)) ?_
  refine sel_piece (arg · 1) (by decide) (fun _ _ _ _ hq => hq.2.2.1) (by taint_decide)
    (branch (d := 4) (c := 2) (nb := 1) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by decide) (fun _ _ h => h.2) (by taint_decide) (by taint_decide)) ?_
  refine sel_piece (arg · 1) (by decide) (fun _ _ _ _ hq => hq.2.2.1) (by taint_decide)
    (branch (d := 6) (c := 4) (nb := 3) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by decide) (fun _ _ h => h.2) (by taint_decide) (by taint_decide)) ?_
  refine (branch (d := 10) (c := 4) (nb := 5) (v := 1023) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by decide) (fun s₀ h₀ ⟨⟨_, h15⟩, h43⟩ => ?_) (by taint_decide) (by taint_decide)).mono
    (fun _ _ _ ⟨⟨h, _⟩, hx⟩ => ⟨h, hx⟩) fun _ _ _ h => h
  have := h₀.b_mem
  simp only [bN, simpleBitPackBounds, t1Max_eq, List.mem_cons, List.not_mem_nil, or_false] at this h15 h43 ⊢
  omega

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlDsa.X86.Pack.simpleBitPack :=
  Piece.leaf (fun s₀ => [outR oP oL s₀]) (NoSp.of_all (by decide +kernel)) (fun _ h => h.lay.leafE)
    (fun _ h => h.lay.leafW) (fun _ _ _ _ hq => hq.1) (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.1, h⟩)

/-- Memory with the arguments `0`, `15`, `0x400` and `128` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5008 then 15 else if a = 0x500d then 4 else if a = 0x5010 then 128 else 0

theorem verified :
    Verified X86.target Impl.MlDsa.X86.Pack.simpleBitPack (simpleBitPackContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [simpleBitPackContract, simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [simpleBitPackContract, simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact hinv.2
  · let st := satState satMem [⟨0, 1024⟩] [⟨0x400, 128⟩, ⟨0x5004, 16⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 15 := by decide
    have a2 : arg st 2 = 0x400 := by decide
    have a3 : arg st 3 = 128 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [simpleBitPackContract, simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, e]
    and_intros
    all_goals first
      | rfl
      | exact Region.disjoint_of_sep (by decide)
      | (simp only [simpleBitPackBounds, t1Max_eq]; decide)
      | (intro i hi
         rw [coeffAt_low (fun a ha => by
           show satMem a = 0
           rw [satMem, ite_low ha (b := 0x5008) (by decide), ite_low ha (b := 0x500d) (by decide),
             ite_low ha (b := 0x5010) (by decide)]) (by decide) hi]
         decide)
      | decide

end VG.Proof.MlDsa.X86.Pack.SimpleBitPack
