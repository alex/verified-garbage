import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.NttLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Lit

/-!
# ML-DSA on AArch64: `vg_mldsa_ntt`

The butterfly's code does what `bfly` does (`bfly_spec`), so each layer is
`nttLayer` (`lay_ok`), and the eight layers are `NTT` (`ntt_eq_layers`).
`Ntt.LI`, `Ntt.pro_ok` and `inPlaceSat` serve `NTT⁻¹` too.
-/

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas ntt)

namespace Ntt

/-- The registers the NTTs write. -/
abbrev clob : List Reg := [.x2, .x3, .x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x15]

/-- Between layers: the polynomial `F` at `fP`, the table `tab` at `zP`, and
entry `k` of the table at `x3`. -/
structure LI (tab : Nat → Nat) (s₀ : State) (fP zP : Addr) (F : Poly) (k : Nat) (s : State) : Prop where
  x2 : s.gpr .x2 = fP
  x3 : s.gpr .x3 = coeffAddr zP k
  consts : Consts s
  poly : PolyIs s.mem fP F
  tab : Tab tab s.mem zP 256
  frame : Frame [pR fP, pR zP] s₀.mem s.mem
  keep : Keep clob s₀ s

theorem LI.step {tab : Nat → Nat} {s₀ : State} {fP zP : Addr} {F F' : Poly} {k k' : Nat} {s s' : State}
    (hI : LI tab s₀ fP zP F k s) (hP : PolyIs s'.mem fP F') (hf : Frame [pR fP] s.mem s'.mem)
    (hx2 : s'.gpr .x2 = fP) (h3 : s'.gpr .x3 = coeffAddr zP k')
    (hk : Keep [.x2, .x3, .x4, .x5, .x6, .x12, .x13, .x14, .x15] s s')
    (hd : (pR zP).Disjoint (pR fP)) : LI tab s₀ fP zP F' k' s' :=
  ⟨hx2, h3, ⟨by rw [hk.get .x9, hI.consts.x9], by rw [hk.get .x10, hI.consts.x10],
      by rw [hk.get .x11, hI.consts.x11]⟩, hP, hI.tab.frame hf (by simpa using hd) (by decide),
    hI.frame.trans (hf.mono (by simp)), (hI.keep.trans hk).mono⟩

/-- The chain of zeta indices of the layers `ls` of `NTT`, from `k`. -/
def Chain : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 128 / len ∧ Chain (256 / len) ls

theorem lens_fwd : ∀ len ∈ nttLens, 2 * (128 / len) ≤ 256 ∧ 128 / len + 128 / len = 256 / len := by decide

theorem zetaTab_of : TabOf zetaTab zetas := fun k _ => zetaNat_eq k

theorem lays_ok {s₀ : State} {fP zP : Addr} (hw : pR fP ∈ s₀.wr) (hz : pR zP ∈ s₀.rd ++ s₀.wr)
    (hd : (pR zP).Disjoint (pR fP)) :
    ∀ (ls : List Nat) (F : Poly) (k : Nat) (s : State), (∀ len ∈ ls, len ∈ nttLens) → Chain k ls →
      LI zetaTab s₀ fP zP F k s →
      WP isa (nttLays ls) s fun s' => ∃ k', LI zetaTab s₀ fP zP (ls.foldl nttLayer F) k' s'
  | [], F, k, s, _, _, hI => WP.block_nil ⟨k, hI⟩
  | len :: ls, F, k, s, hls, ⟨hk, hc⟩, hI => by
    have hlen := hls len (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := lens_fwd len hlen
    refine WP.seq (WP.mono (lay_ok bfly_spec zetaTab_of hlen true (fun c => 128 / len + c)
      (fun c hc => by omega) (fun c _ => by rw [zstep, ite_eq_left rfl, coeffAddr_next]; rfl)
      F s hI.x2 (by rw [hI.x3, hk]; rfl) hI.consts hI.poly (by rw [hI.keep.wr]; exact hw)
      (by rw [hI.keep.rd, hI.keep.wr]; exact hz) hd hI.tab) fun s' ⟨⟨hP, hf, hx2, h3⟩, hk'⟩ => ?_)
    exact lays_ok hw hz hd ls _ (256 / len) s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc
      (hI.step hP hf hx2 (by rw [h3, h2]) hk' hd)

/-- The table `tab` to `scratch`, the constants, `x2` = `f` and `x3` at entry `k`. -/
theorem pro_ok {s₀ : State} {t : Poly → Poly} (hp : (inPlaceK t).pre s₀) (tab : Nat → Nat) (k : Nat)
    (hk : 4 * k < 4096) :
    WP isa (.block (nttPro tab k)) s₀
      (LI tab s₀ (s₀.gpr .x0) (s₀.gpr .x1) (polyAt s₀.mem (s₀.gpr .x0)) k) := by
  unfold nttPro
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (storeTab_ok tab (b := .x1) (by decide) s₀ (by rw [hp.2.1]; simp))
    fun s1 ⟨ht, hf, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s1) fun s2 ⟨⟨hc, hm2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (WP.keep [.x2, .x3] (Q := fun s => s.mem = s2.mem ∧ s.gpr .x2 = s2.gpr .x0 ∧
    s.gpr .x3 = s2.gpr .x1 + BitVec.ofNat 64 (4 * k)) (by arun [Impl.MlKem.AArch64.mov, hk]) (by rfl) (hv := rfl))
    fun s3 ⟨⟨hm3, hx2, hx3⟩, k3⟩ => ?_
  have hd' : (pR (s₀.gpr .x0)).Disjoint (pR (s₀.gpr .x1)) := hp.2.2.1
  refine ⟨by rw [hx2, k12.get .x0], by rw [hx3, k12.get .x1],
    ⟨by rw [k3.get .x9, hc.x9], by rw [k3.get .x10, hc.x10], by rw [k3.get .x11, hc.x11]⟩, ?_,
    by rw [hm3, hm2]; exact ht, by rw [hm3, hm2]; exact hf.mono (by simp), (k12.trans k3).mono⟩
  rw [hm3, hm2]
  exact ⟨reduced_frame hf (by simpa using hd') hp.2.2.2, polyAt_frame hf (by simpa using hd')⟩

end Ntt

theorem chain_fwd : Ntt.Chain 1 nttLens := by
  simp only [nttLens, Ntt.Chain]; decide

theorem ntt_noCalls : Impl.MlDsa.AArch64.Arith.ntt.noCalls = true := by lit_decide

theorem ntt_correct (s : State) (hs : (inPlaceK ntt).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Arith.ntt s t s' ∧ abiPreserved s s' ∧ (inPlaceK ntt).post s s' := by
  have hw : pR (s.gpr .x0) ∈ s.wr := by rw [hs.2.1]; simp
  have hz : pR (s.gpr .x1) ∈ s.rd ++ s.wr := by rw [hs.1, hs.2.1]; simp
  obtain ⟨t, s', he, ⟨k, hI⟩⟩ := WP.seq (M := isa) (WP.mono (Ntt.pro_ok hs zetaTab 1 (by decide))
    fun s1 hI => Ntt.lays_ok hw hz hs.2.2.1.symm nttLens _ 1 s1 (fun _ h => h) chain_fwd hI)
  refine ⟨t, s', he, VG.Proof.MlKem.AArch64.abi_of ntt_noCalls (by lit_decide) he, ?_⟩
  show PolyIs _ _ _
  rw [ntt_eq_layers]
  exact hI.poly

/-- The pointers are public. -/
theorem inPlace_agree {t : Poly → Poly} (s₁ s₂ : State) (_ : (inPlaceK t).pre s₁) (_ : (inPlaceK t).pre s₂)
    (hp : (inPlaceK t).pub s₁ s₂) : VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1]) s₁ s₂ :=
  agree_regs hp.2.2 fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hp.1, hp.2.1]

theorem ntt_ct : ConstantTime isa (inPlaceK ntt).pre (inPlaceK ntt).pub Impl.MlDsa.AArch64.Arith.ntt :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x0, .x1]) inPlace_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def inPlaceSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem ntt_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Arith.ntt (Spec.MlDsa.nttContract AArch64.abi) :=
  Verified.of_correct ntt_correct ntt_ct (by
    mldsa_implies [Spec.MlDsa.nttContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, inPlaceK,
      AArch64.abi, AArch64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlDsa.AArch64.Arith
