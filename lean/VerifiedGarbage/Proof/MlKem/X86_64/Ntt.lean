import VerifiedGarbage.Proof.MlKem.X86_64.NttLoop
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86-64: `vg_mlkem_ntt`

Untrusted: everything here is checked by Lean. The butterfly's code does
what `bfly` does (`bfly_spec`), so each layer is `nttLayer` (`fwdLay_ok`),
and the seven layers are `NTT` (`ntt_eq_layers`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- `vg_mlkem_ntt(f = rdi, scratch = rsi)` and `vg_mlkem_ntt_inv`: `f`
becomes `t f`. -/
def inPlaceK (t : Poly → Poly) : Contract isa where
  pre s :=
    s.rd = [] ∧ s.wr = [pR (s.gpr .rdi), pR (s.gpr .rsi)] ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧ Reduced s.mem (s.gpr .rdi)
  post s s' := PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The value of the product of `z` and a word of value `x`, reduced. -/
theorem mulz_toNat {u : BitVec 32} {z x : Zq} (hu : u.toNat = x.val) :
    (BitVec.setWidth 32 (redV (prodR9 u (BitVec.ofNat 64 z.val)))).toNat = (z * x).val := by
  have hz := val_lt z
  have hx := val_lt x
  have e : (prodR9 u (BitVec.ofNat 64 z.val)).toNat = x.val * z.val := by
    rw [prodR9, BitVec.toNat_ofNat, toNat_setWidth64, hu, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := z.val) (by omega)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (mul_lt_q2 hx hz) (by decide))
  have hl : x.val * z.val < 2 ^ 32 := Nat.lt_of_lt_of_le (mul_lt_q2 hx hz) (by decide)
  have hr := redV_lt (x := prodR9 u (BitVec.ofNat 64 z.val)) (by rw [e]; exact hl)
  have hr' : (redV (prodR9 u (BitVec.ofNat 64 z.val))).toNat < 2 ^ 32 := Nat.lt_of_lt_of_le hr (by decide)
  rw [toNat_setWidth32_64 hr', redV_toNat (by rw [e]; exact hl), e, val_mul,
    Nat.mul_comm]

/-- The words a butterfly reads. -/
theorem bfly_regions {fP : Addr} {len j : Nat} (hj : j + len < 256) {s : State}
    (hsi : s.gpr .rsi = coeffAddr fP j) (hw : pR fP ∈ s.wr) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4 ∧ InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4 ∧
      InRegions s.wr (s.gpr .rsi) 4 ∧ InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4 := by
  rw [hsi, coeffAddr_add]
  exact ⟨⟨_, List.mem_append_right _ hw, coeff_contains _ (show j < 256 by omega)⟩,
    ⟨_, List.mem_append_right _ hw, coeff_contains _ hj⟩, ⟨_, hw, coeff_contains _ (show j < 256 by omega)⟩,
    ⟨_, hw, coeff_contains _ hj⟩⟩

theorem bfly_spec : BflyOk Impl.MlKem.X86_64.bfly MlKem.bfly := by
  intro fP len j hlen hj z F s hsi h9 hF hw
  obtain ⟨r0, r1, w0, w1⟩ := bfly_regions hj hsi hw
  refine WP.mono (bfly_ok len s r0 r1 w0 w1) fun s' ⟨⟨hm, hsi', hcx, hz⟩, hk⟩ => ⟨⟨?_, ?_, hsi', hcx, hz⟩, hk⟩
  · rw [hm, h9, hsi, coeffAddr_add, ← coeffAt_eq, ← coeffAt_eq]
    have hj' : j < 256 := by omega
    have ha := polyIs_toNat hF hj'
    have hu := polyIs_toNat hF hj
    have hT := mulz_toNat (z := z) hu
    have hne : j ≠ j + len := by omega
    show PolyIs _ _ ((F.set! (j + len) (F[j]! - z * F[j + len]!)).set! j
      ((F.set! (j + len) (F[j]! - z * F[j + len]!))[j]! + z * F[j + len]!))
    rw [getElem!_set!_ne _ hj' hne.symm]
    refine polyIs_writeW' (polyIs_writeW' hF hj _ ?_) hj' _ ?_
    · rw [csub32_sub (by rw [ha]; exact val_lt _) (by rw [hT]; exact val_lt _), ha, hT, val_sub]
    · rw [csub32_add (by rw [ha]; exact val_lt _) (by rw [hT]; exact val_lt _), ha, hT, val_add]
  · rw [hm, hsi, coeffAddr_add]
    exact (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ (coeff_contains _ hj)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ (show j < 256 by omega))

namespace Ntt

/-- Between layers: the polynomial `F` at `fP`, the zeta `zeta k` at `r8`. -/
structure LI (s₀ : State) (fP zP : Addr) (F : Poly) (k : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = fP
  r8 : s.gpr .r8 = coeffAddr zP k
  poly : PolyIs s.mem fP F
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  tab : Tab zetaTab s.mem zP 128
  frame : Frame [pR fP, pR zP] s₀.mem s.mem
  keep : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s₀ s

theorem LI.step {s₀ : State} {fP zP : Addr} {F F' : Poly} {k k' : Nat} {s s' : State}
    (hI : LI s₀ fP zP F k s) (hP : PolyIs s'.mem fP F') (hf : Frame [pR fP] s.mem s'.mem)
    (hsi : s'.gpr .rsi = fP) (h8 : s'.gpr .r8 = coeffAddr zP k')
    (hk : Keep [.rdi, .r9, .r8, .rcx, .rax, .rdx, .rsi, .rcx, .r10, .r11, .rsi, .rdi, .rsi] s s')
    (hd : (pR zP).Disjoint (pR fP)) : LI s₀ fP zP F' k' s' :=
  ⟨hsi, h8, hP, hk.2.1.trans hI.rd, hk.2.2.trans hI.wr, hI.tab.frame hf (by simpa using hd) (by decide),
    hI.frame.trans (hf.mono (by simp)), (hI.keep.trans hk).mono (by decide)⟩

/-- The chain of zeta indices of the layers `ls` of `NTT`, from `k`. -/
def Chain : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 128 / len ∧ Chain (256 / len) ls

theorem lens_fwd : ∀ len ∈ nttLens, 2 * (128 / len) ≤ 128 ∧ 128 / len + 128 / len = 256 / len := by decide

theorem lays_ok {s₀ : State} {fP zP : Addr} (hw : pR fP ∈ s₀.wr) (hz : pR zP ∈ s₀.rd ++ s₀.wr)
    (hd : (pR zP).Disjoint (pR fP)) :
    ∀ (ls : List Nat) (F : Poly) (k : Nat) (s : State), (∀ len ∈ ls, len ∈ nttLens) → Chain k ls →
      LI s₀ fP zP F k s → WP isa (nttLays ls) s fun s' => ∃ k', LI s₀ fP zP (ls.foldl nttLayer F) k' s'
  | [], F, k, s, _, _, hI => WP.block_nil ⟨k, hI⟩
  | len :: ls, F, k, s, hls, ⟨hk, hc⟩, hI => by
    have hlen := hls len (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := lens_fwd len hlen
    refine WP.seq (WP.mono (lay_ok bfly_spec hlen 4 (fun c => 128 / len + c) (fun c hc => by omega)
      (fun c _ => by rw [show BitVec.signExtend 64 (4 : BitVec 32) = 4 by decide, coeffAddr_succ]; rfl)
      F s hI.rsi (by rw [hI.r8, hk]; rfl) hI.poly (by rw [hI.wr]; exact hw) (by rw [hI.rd, hI.wr]; exact hz) hd
      hI.tab) fun s' ⟨⟨hP, hf, hsi, h8⟩, hk'⟩ => ?_)
    exact lays_ok hw hz hd ls _ (256 / len) s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc
      (hI.step hP hf hsi (by rw [h8, h2]) hk' hd)

/-- The zetas to `scratch`, `rsi` = `f` and `r8` at `zeta k`. -/
theorem pro_ok {s₀ : State} {t : Poly → Poly} (hp : (inPlaceK t).pre s₀) (d : BitVec 32) (k : Nat)
    (hd : BitVec.signExtend 64 d = BitVec.ofNat 64 (4 * k)) :
    WP isa (.block (nttPro ++ ([.alu .add .r8 (.imm d)] : List Instr))) s₀
      (LI s₀ (s₀.gpr .rdi) (s₀.gpr .rsi) (polyAt s₀.mem (s₀.gpr .rdi)) k) := by
  simp only [nttPro, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r9] (Q := fun s => s.mem = s₀.mem ∧ s.gpr .r9 = s₀.gpr .rsi) (by xrun) (by decide))
    fun s1 ⟨⟨hm1, h9⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeTab_ok zetaTab (by decide) s1 (by rw [k1.2.2, hp.2.1, h9]; simp))
    fun s2 ⟨ht, hf, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (WP.keep [.rsi, .r8] (Q := fun s => s.mem = s2.mem ∧ s.gpr .rsi = s2.gpr .rdi ∧
    s.gpr .r8 = s2.gpr .r9 + BitVec.signExtend 64 d) (by xrun [List.cons_append, List.nil_append]) (by rfl))
    fun s3 ⟨⟨hm3, hsi, h8⟩, k3⟩ => ?_
  have hd' : (pR (s₀.gpr .rdi)).Disjoint (pR (s₀.gpr .rsi)) := hp.2.2.1
  refine ⟨by rw [hsi, k12.gpr (by decide)], by rw [h8, k2.gpr (by decide), h9, hd], ?_, by rw [k3.2.1, k12.2.1],
    by rw [k3.2.2, k12.2.2], by rw [hm3, ← h9]; exact ht,
    by rw [hm3, ← hm1, ← h9]; exact hf.mono (by simp), ((k12.trans k3)).mono (by decide)⟩
  rw [hm3]
  refine ⟨?_, ?_⟩
  · rw [h9] at hf
    exact reduced_frame (by rw [← hm1]; exact hf) (by simpa using hd') hp.2.2.2.2.2
  · rw [h9] at hf
    exact polyAt_frame (by rw [← hm1]; exact hf) (by simpa using hd')

end Ntt

theorem chain_fwd : Ntt.Chain 1 nttLens := by
  simp only [nttLens, Ntt.Chain]; decide

theorem ntt_correct (s : State) (hs : (inPlaceK ntt).pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.ntt s t s' ∧ abiPreserved s s' ∧ (inPlaceK ntt).post s s' := by
  have hw : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hz : pR (s.gpr .rsi) ∈ s.rd ++ s.wr := by rw [hs.1, hs.2.1]; simp
  obtain ⟨t, s', he, ⟨k, hI⟩, hk⟩ := WP.keep (c := Impl.MlKem.X86_64.ntt)
    [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]
    (WP.seq (WP.mono (Ntt.pro_ok hs 4 1 (by decide)) fun s1 hI =>
      Ntt.lays_ok hw hz hs.2.2.1.symm nttLens _ 1 s1 (fun _ h => h) chain_fwd hI)) (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hI.frame
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), ?_⟩
  show PolyIs _ _ _
  rw [ntt_eq_layers]
  exact hI.poly

theorem ntt_ct : ConstantTime isa (inPlaceK ntt).pre (inPlaceK ntt).pub Impl.MlKem.X86_64.ntt :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

/-- A state satisfying the precondition. -/
def inPlaceSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem ntt_verified :
    Verified X86_64.target Impl.MlKem.X86_64.ntt (Spec.MlKem.nttContract X86_64.abi) :=
  Verified.of_correct ntt_correct ntt_ct (by
    mlkem_implies [Spec.MlKem.nttContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlKem.X86_64
