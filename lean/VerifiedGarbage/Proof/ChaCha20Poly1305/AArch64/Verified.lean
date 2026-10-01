import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages
import VerifiedGarbage.Proof.Framework.ContractPost
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
import VerifiedGarbage.Proof.Framework.Omega

section

/-!
# ChaCha20-Poly1305 on AArch64: correctness

Untrusted: everything here is checked by Lean. `seal` and `open`, from their
parts.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

/-- That two of the regions the parts use are disjoint: parts of the context
at different offsets, the additional data and the data. (Matching only
reducibly, so that a lemma that does not apply fails fast.) -/
macro "rdisj" : tactic => `(tactic| first
  | with_reducible exact sub_disj _ (by lit_omega) (by lit_omega) (by lit_omega)
  | with_reducible exact (‹APre _›).c_d.sub_left (sub_ctx _ (by lit_omega))
  | with_reducible exact (‹APre _›).c_d.symm.sub_right (sub_ctx _ (by lit_omega))
  | with_reducible exact (‹APre _›).c_a.symm.sub_right (sub_ctx _ (by lit_omega))
  | with_reducible exact (‹APre _›).a_d)

/-- A region is disjoint from each of a list of regions. -/
macro "rdisj_all" : tactic => `(tactic| (
  simp only [macR, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  repeat' apply And.intro
  all_goals rdisj))

theorem hRDX (s₀ : State) : s₀.gpr .x2 = BitVec.ofNat 64 (AL s₀) := by simp [AL]

theorem srcA {s₀ : State} (hp : APre s₀) : Src s₀ (ad s₀) (AL s₀) :=
  ⟨(s₀.gpr .x2).isLt, hp.wrap_a, hp.c_a, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; simp [hp.rd], hc⟩⟩

theorem srcD {s₀ : State} (hp : APre s₀) : Src s₀ (dp s₀) (L s₀) :=
  ⟨(s₀.gpr .x4).isLt, hp.wrap_d, hp.c_d, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; simp [hp.wr], hc⟩⟩

theorem length_encrypt (key nonce m : List Byte) : (Spec.ChaCha20.encrypt key 1 nonce m).length = m.length := by
  rw [encrypt_eq, List.length_zipWith, VG.Proof.ChaCha20.length_keystream, Nat.min_self]

theorem off48 (s₀ : State) : cx s₀ + 48 = off (cx s₀) 48 := rfl

/-- The callee-saved registers on return: those saved in the context are
restored, and the others were never changed. -/
theorem preserved_split : ∀ r ∈ preserved, r ∉ [Reg.x21, .x22, .x23, .x24, .x25, .x30] →
    r ∈ untouched ∧ r ≠ .x30 := by decide

theorem abi_of {s₀ s s₁ s' : State} (h : Inv s₀ s) (hk : ∀ r ∈ preserved, r ≠ .x30 → s₁.gpr r = s.gpr r)
    (hr : ∀ r ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x30], s'.gpr r = s₀.gpr r)
    (hg : ∀ r, r ∉ [Reg.x21, .x22, .x23, .x24, .x25, .x30] → s'.gpr r = s₁.gpr r) (hsp : s'.sp = s.sp) :
    GprAbi s₀ s' := by
  refine ⟨fun r hr' => ?_, by rw [hsp, h.sp]⟩
  by_cases hm : r ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x30]
  · exact hr r hm
  · have hu := preserved_split r hr' hm
    rw [hg r hm, hk r hr' hu.2, h.un r hu.1]

theorem seal_correct (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre s₀) :
    WP isa (sealWith v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ sealAArch64.post s₀ s' := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x4).isLt)
  unfold sealWith
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x2).isLt)
  refine WP.seq (WP.mono (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.x21
    h₁.inv.rd h₁.inv.wr h₁.inv.x24 (by rw [h₁.inv.x25]; exact hRDX s₀))
    fun s₂ ⟨k₂, r₂⟩ => ?_)
  have i₂ := mac_inv h₁.inv k₂
  refine WP.seq (WP.mono (lengths_ok hp i₂) fun s₃ ⟨i₃, k₃, len₃⟩ => ?_)
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₃.frame (by rdisj_all), stateAt_frame k₂.frame (by rdisj_all), h₁.st]
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₃.frame (by rdisj_all) hL', bytesAt_frame k₂.frame (by rdisj_all) hL',
      bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono (crypt_ok v hp i₃ st₃) fun s₄ ⟨i₄, k₄, ct₄⟩ => ?_)
  rw [D₃] at ct₄
  refine WP.seq (WP.mono (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₄.x21
    i₄.rd i₄.wr i₄.x22 (by rw [i₄.x23]; exact hL s₀))
    fun s₅ ⟨k₅, r₅⟩ => ?_)
  have i₅ := mac_inv i₄ k₅
  refine WP.seq (WP.mono (absorbLengths_ok hp i₅) fun s₆ ⟨i₆, k₆, r₆⟩ => ?_)
  refine WP.seq (WP.mono (finalizeTo_ok hp i₆ (out := 48) (.inl (by lit_omega)))
    fun s₇ ⟨k₇, tag₇⟩ => ?_)
  refine WP.mono (restore_ok hp (by rw [k₇.cs _ (pres .x21) (pres30 .x21), i₆.x21])
    (i₆.saved.frame k₇.frame (by rdisj_all)) (by rw [k₇.rd, i₆.rd]) (by rw [k₇.wr, i₆.wr]))
    fun s₈ ⟨⟨rs₈, g₈, m₈⟩, sp₈⟩ => ?_
  have R₄ := Repr.frame k₄.frame (by rdisj_all) (Repr.frame k₃.frame (by rdisj_all) (r₂ (otk s₀) [] h₁.poly))
  have T₇ := tag₇ _ _ (r₆ _ _ (r₅ _ _ R₄))
  have L₅ : bytesAt s₅.mem (off (cx s₀) 656) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame k₅.frame (by rdisj_all) (by lit_omega), bytesAt_frame k₄.frame (by rdisj_all) (by lit_omega), len₃]
  have C₈ : bytesAt s₈.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₈, bytesAt_frame k₇.frame (by rdisj_all) hL', bytesAt_frame k₆.frame (by rdisj_all) hL',
      bytesAt_frame k₅.frame (by rdisj_all) hL', ct₄]
  have C₄ : bytesAt s₄.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := ct₄
  refine ⟨abi_of i₆ k₇.cs rs₈ g₈ (by rw [sp₈, k₇.sp]), ?_⟩

  show Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) =
    (bytesAt s₈.mem (dp s₀) (L s₀), bytesAt s₈.mem (cx s₀ + 48) 16)
  rw [C₈, off48, m₈, T₇, L₅, C₄, hA]
  simp only [Spec.ChaCha20Poly1305.encrypt, macData, List.nil_append,
    List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]

theorem open_correct (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre s₀) :
    WP isa (openWith v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ openAArch64.post s₀ s' := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x4).isLt)
  unfold openWith
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x2).isLt)
  refine WP.seq (WP.mono (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.x21
    h₁.inv.rd h₁.inv.wr h₁.inv.x24 (by rw [h₁.inv.x25]; exact hRDX s₀))
    fun s₂ ⟨k₂, r₂⟩ => ?_)
  have i₂ := mac_inv h₁.inv k₂
  have D₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₂.frame (by rdisj_all) hL', bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₂.x21
    i₂.rd i₂.wr i₂.x22 (by rw [i₂.x23]; exact hL s₀))
    fun s₃ ⟨k₃, r₃⟩ => ?_)
  have i₃ := mac_inv i₂ k₃
  refine WP.seq (WP.mono (lengths_ok hp i₃) fun s₄ ⟨i₄, k₄, len₄⟩ => ?_)
  refine WP.seq (WP.mono (absorbLengths_ok hp i₄) fun s₅ ⟨i₅, k₅, r₅⟩ => ?_)
  have st₅ : stateAt s₅.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₅.frame (by rdisj_all), stateAt_frame k₄.frame (by rdisj_all),
      stateAt_frame k₃.frame (by rdisj_all), stateAt_frame k₂.frame (by rdisj_all), h₁.st]
  refine WP.seq (WP.mono (crypt_ok v hp i₅ st₅) fun s₆ ⟨i₆, k₆, pt₆⟩ => ?_)
  refine WP.seq (WP.mono (finalizeTo_ok hp i₆ (out := 640) (.inr ⟨by omega, by omega⟩))
    fun s₇ ⟨k₇, tag₇⟩ => ?_)
  have x21₇ : s₇.gpr .x21 = cx s₀ := by rw [k₇.cs _ (pres .x21) (pres30 .x21), i₆.x21]
  refine WP.block_append (WP.mono (compare_ok hp x21₇ (by rw [k₇.rd, i₆.rd]) (by rw [k₇.wr, i₆.wr]))
    fun s₈ ⟨rax₈, g₈, sp₈, m₈, rd₈, wr₈⟩ => ?_)
  refine WP.mono (restore_ok hp (by rw [g₈ _ (pres .x21), x21₇])
    (by rw [m₈]; exact i₆.saved.frame k₇.frame (by rdisj_all))
    (by rw [rd₈, k₇.rd, i₆.rd]) (by rw [wr₈, k₇.wr, i₆.wr])) fun s₉ ⟨⟨rs₉, g₉, m₉⟩, sp₉⟩ => ?_
  -- The tag computed, and the one received.
  have R₃ := r₃ _ _ (r₂ (otk s₀) [] h₁.poly)
  have T₇ := tag₇ _ _ (Repr.frame k₆.frame (by rdisj_all) (r₅ _ _ (Repr.frame k₄.frame (by rdisj_all) R₃)))
  have T0₇ : bytesAt s₇.mem (off (cx s₀) 48) 16 = T0 s₀ := by
    rw [bytesAt_frame k₇.frame (by rdisj_all) (by lit_omega), bytesAt_frame i₆.frame (by rdisj_all) (by lit_omega),
      ← off48]
  have P₉ : bytesAt s₉.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₉, m₈, bytesAt_frame k₇.frame (by rdisj_all) hL', pt₆, bytesAt_frame k₅.frame (by rdisj_all) hL',
      bytesAt_frame k₄.frame (by rdisj_all) hL', bytesAt_frame k₃.frame (by rdisj_all) hL', D₂]
  rw [len₄, D₂, hA] at T₇
  refine ⟨abi_of i₆ (fun r hr h30 => by rw [g₈ r hr, k₇.cs r hr h30]) rs₉ (fun r hr => by rw [g₉ r hr])
    (by rw [sp₉, sp₈, k₇.sp]), ?_⟩
  have hm : mac (otk s₀) (macData (A s₀) (D s₀)) = bytesAt s₇.mem (off (cx s₀) 640) 16 := by
    rw [T₇]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  rw [openAArch64, Contract.post_mk]
  dsimp only
  rw [g₉ .x0 (by decide), rax₈]
  split
  next pt hpt =>
    obtain ⟨hmac, rfl⟩ := decrypt_eq_some hpt
    exact ⟨ite_eq_left (hm.symm.trans (hmac.trans T0₇.symm)), P₉⟩
  next hn => exact ite_eq_right fun he => decrypt_eq_none hn ((hm.trans he).trans T0₇)

end VG.Proof.ChaCha20Poly1305.AArch64

end

/-!
# ChaCha20-Poly1305 on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness (from
`Correct.lean`), constant time, and a state satisfying the precondition.

The taint analysis runs through the callees' code: it knows `x21`–`x25`
(the context, the data, the additional data and their lengths) for public
after each call because no callee writes them (unlike `x19` and `x20`, which
`vg_chacha20_xor` restores from memory, and which the analysis therefore
treats as secret afterwards).
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64

/-- The public registers on entry: the pointers and the lengths. -/
def τ₀ : VG.AArch64.Taint.T := VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]

theorem agree₀ {s₁ s₂ : State} (hpub : pubAArch64 s₁ s₂) : VG.AArch64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [τ₀, VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition (with no additional data and no
data). -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x3000, 0⟩]

theorem seal_ok (v : Proof.ChaCha20.AArch64.XorImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa (Impl.ChaCha20Poly1305.AArch64.sealWith v.callee) s t s' ∧ abiPreserved s s' ∧
      sealAArch64.post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := seal_correct v (APre.of s hs)
  exact ⟨t, s', he, h, hpost⟩

theorem seal_ct (v : Proof.ChaCha20.AArch64.XorImpl) : ConstantTime isa sealAArch64.pre sealAArch64.pub
    (Impl.ChaCha20Poly1305.AArch64.sealWith v.callee) := by
  obtain ⟨h, hh⟩ := v.sealTaint
  exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ _ _ hp => agree₀ hp) hh

theorem open_ok (v : Proof.ChaCha20.AArch64.XorImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa (Impl.ChaCha20Poly1305.AArch64.openWith v.callee) s t s' ∧ abiPreserved s s' ∧
      openAArch64.post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := open_correct v (APre.of s hs)
  exact ⟨t, s', he, h, hpost⟩

theorem open_ct (v : Proof.ChaCha20.AArch64.XorImpl) : ConstantTime isa openAArch64.pre openAArch64.pub
    (Impl.ChaCha20Poly1305.AArch64.openWith v.callee) := by
  obtain ⟨h, hh⟩ := v.openTaint
  exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ _ _ hp => agree₀ hp) hh

theorem seal_verified (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (Impl.ChaCha20Poly1305.AArch64.sealWith v.callee)
      (Spec.ChaCha20Poly1305.sealContract AArch64.abi) :=
  Verified.of_correct (seal_ok v) (seal_ct v) (by
    sig_implies [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
      Proof.ChaCha20Poly1305.sealAArch64, Proof.ChaCha20Poly1305.preAArch64,
      Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.ChaCha20Poly1305.AArch64.sat] using Proof.ChaCha20Poly1305.AArch64.sat)

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem open_verified (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (Impl.ChaCha20Poly1305.AArch64.openWith v.callee)
      (Spec.ChaCha20Poly1305.openContract AArch64.abi) :=
  Verified.of_correct (open_ok v) (open_ct v)
    { pre := by
        sig_implies_pre [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openAArch64, Proof.ChaCha20Poly1305.preAArch64,
          Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig, AArch64.abi,
          AArch64.argRegs]
        simp only [Proof.ChaCha20Poly1305.openAArch64] at h
        -- The two `decrypt` terms are equal only up to unfolding numerals.
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact h
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => exact h
      pub := by
        sig_implies_pub [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openAArch64, Proof.ChaCha20Poly1305.preAArch64,
          Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      sat := by
        sig_implies_sat [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
          Proof.ChaCha20Poly1305.openAArch64, Proof.ChaCha20Poly1305.preAArch64,
          Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
          [Proof.ChaCha20Poly1305.AArch64.sat] using Proof.ChaCha20Poly1305.AArch64.sat }

end VG.Proof.ChaCha20Poly1305.AArch64
