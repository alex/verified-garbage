import VerifiedGarbage.Proof.MlDsa.X86.Sign.Pre

/-!
# ML-DSA signing on x86 (32-bit): `vg_mldsa{44,65,87}_sign`

The body in the leaf's frame (`piece`), and `Verified` against `signContract`
(`verified`), for any implementations of the primitives that `PrimsOk` says
are verified, and any of the three parameter sets.
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece P0 LeafPost satState)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

/-- A top-level function, from its body, for runs related by `SPub`. -/
theorem topLeafS {body : Prog isa} {B : State → State → Prop} (hsp : NoSp body)
    (hb : SP p (fun s₀ s => s = P0 s₀) (fun s₀ s => Ctx (Y p) s₀ s ∧ B s₀ s) body) :
    SP p (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (B s₀) s₀ s') (Impl.MlKem.X86.leaf body) :=
  Piece.leaf (W (Y p)) hsp (fun _ hp => ⟨hp.E0_big, by have := hp.sp'; omega⟩) (fun _ hp => hp.hW)
    (fun _ _ _ _ hq => hq.1.1) (hb.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h.2⟩)

theorem piece (F : PrimsOk P) (ps : PS p) (hsp : NoSp (body P p)) :
    SP p (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Done p s₀) s₀ s') (sign P p) :=
  topLeafS hsp (body_piece F ps)

/-- Memory with the arguments `0`, `0x2000`, `0x3000`, `0x8000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 0x20 else if a = 0x500d then 0x30 else if a = 0x5011 then 0x80 else if a = 0x5016 then 1 else 0

theorem sat (h3 : Ok3 p) : ∃ s, (signContract p X86.abi 96).pre s := by
  rcases h3 with rfl | rfl | rfl
  · refine ⟨satState satMem [⟨0, 2560⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩] [⟨0x8000, 2420⟩, ⟨0x10000, 77824⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_sat_check [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  · refine ⟨satState satMem [⟨0, 4032⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩] [⟨0x8000, 3309⟩, ⟨0x10000, 103424⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_sat_check [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  · refine ⟨satState satMem [⟨0, 4896⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩] [⟨0x8000, 4627⟩, ⟨0x10000, 144384⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_sat_check [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

/-- `vg_mldsa{44,65,87}_sign`, with the primitives `P`, is verified against `signContract`. -/
theorem verified (F : PrimsOk P) (h3 : Ok3 p) (hsp : NoSp (body P p)) :
    Verified X86.target (sign P p) (signContract p X86.abi 96) := by
  have ps := PS.of h3
  refine Piece.verified (((piece F ps hsp).pre_mono (fun _ h => pre_of h) fun _ _ _ _ h => pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) (sat h3)
  obtain ⟨habi, -, -, s, hd, hm, hax⟩ := hq
  refine ⟨habi, ?_⟩
  sig_post [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  rw [sw32, hax, hm]
  unfold Done at hd
  simp only [skOf, muOf, rndOf, bSk, bMu, bRnd, bSig, addr0] at hd
  exact hd

end VG.Proof.MlDsa.X86.Sign
