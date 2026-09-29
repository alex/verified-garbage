import VerifiedGarbage.Proof.MlKem1024.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.EncTop
import VerifiedGarbage.Impl.MlKem1024.X86_64.Encrypt

/-!
# ML-KEM-1024 on x86-64: K-PKE.Encrypt, its context and the matrix

Untrusted: everything here is checked by Lean. `encrypt1024` runs in both
`vg_mlkem1024_encaps` and `vg_mlkem1024_decaps`, in their layouts, and
keeps what each of them holds of its state (`Ctx`, as ML-KEM-768's
`encrypt`: a predicate `Out` kept by the pieces whose writes pass `chk`).
Its inputs (`EIn`): the encryption key at `E`, the message at `M`, the
randomness at `G + 32`. The matrix `Â` from `ρ` (the last 32 bytes of the
key), as in `vg_mlkem1024_keygen` (`mat_ok`), and its constant time, for a
given `ρ` (`mat_tr`).
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Enc4

open VG.Impl.MlKem1024.X86_64.Encrypt1024

variable {rbs wbs : List (Reg × Nat)}

/-- `ρ` of the key. -/
abbrev rhoE (ek : List Byte) : List Byte := ekRho mlKem1024 ek

/-- The inputs: `ek` at `E`, `m` at `M` and `r` at `G + 32`. -/
structure EIn (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (s : State) : Prop where
  out : C.Out s
  ek : bytesAt s.mem (pa s E) 1568 = ek
  m : bytesAt s.mem (pa s (sc oM)) 32 = m
  r : bytesAt s.mem (pa s sigP) 32 = r

/-- A piece writing `ws` keeps the inputs. -/
def inKeep (bs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (ws : List (Ptr × Nat)) : Bool :=
  chk ws && keepB bs ws E 1568 && keepB bs ws (sc oM) 32 && keepB bs ws sigP 32

theorem EIn.keep {C : Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {s s' : State} (h : EIn C E ek m r s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hc : inKeep (rbs ++ wbs) C.chk E ws = true) :
    EIn C E ek m r s' := by
  simp only [inKeep, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hc, k1⟩, k2⟩, k3⟩ := hc
  have L := C.lay h.out
  exact ⟨C.step h.out hP hc, by rw [L.keepBytes hP k1]; exact h.ek, by rw [L.keepBytes hP k2]; exact h.m,
    by rw [L.keepBytes hP k3]; exact h.r⟩

theorem EIn.rho {C : Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {s : State} (h : EIn C E ek m r s) :
    bytesAt s.mem (pa s (E.1, E.2 + 1536)) 32 = rhoE ek := by
  rw [← h.ek]
  show _ = ((bytesAt s.mem (pa s E) 1568).drop 1536).take 32
  rw [bytesAt_slice _ _ (show 1536 + 32 ≤ 1568 by decide), pa, pa, off_add]

/-! ## The matrix -/

/-- After the first `e` entries of `Â`. -/
structure EB (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (e : Nat) (s : State) : Prop where
  i : EIn C E ek m r s
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = rhoE ek
  r15 : s.gpr .r15 = if allOk4 (rhoE ek) e then 1 else 0
  mat : ∀ e' < e, ∀ f, sampleNTT minIterations (matSeed (rhoE ek) (e' / 4) (e' % 4)) = some f →
    PolyIs s.mem (pa s (aS4 (e' / 4) (e' % 4))) f

/-- The copy of `ρ`. -/
def matChk (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  copyChk bs wbs (sc oSB) (E.1, E.2 + 1536) 32 && decide (E.1 ≠ .rdi) && inKeep bs chk E [(sc oSB, 32)]

/-- Entry `e` of `Â`. -/
def sampEChk (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (e : Nat) : Bool :=
  ijChk bs wbs (aS4 (e / 4) (e % 4)) && inKeep bs chk E (KeyGen4.ijW4 e) && keepB bs (KeyGen4.ijW4 e) (sc oSB) 32 &&
    (List.range e).all fun e' => keepB bs (KeyGen4.ijW4 e) (aS4 (e' / 4) (e' % 4)) 1024

theorem sampE_step {C : Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {e : Nat} (he : e < 16)
    (hc : sampEChk (rbs ++ wbs) wbs C.chk E e = true) {s : State} (h : EB C E ek m r e s) :
    WP isa (sampleIJ4 (e / 4) (e % 4)) s fun s' => PPostB s s' (KeyGen4.ijW4 e) ∧ EB C E ek m r (e + 1) s' := by
  simp only [sampEChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨hij, hkc⟩, kB⟩, kA⟩ := hc
  have L := C.lay h.i.out
  unfold sampleIJ4
  refine WP.mono (sampP_ok L C.bs (by omega) (by omega) hij) fun s' ⟨hP, h15, hres⟩ => ⟨hP, ?_⟩
  refine ⟨h.i.keep hP hkc, by rw [L.keepBytes hP kB]; exact h.sb, ?_, fun e' he' f hf => ?_⟩
  · rw [h15, h.sb, and_acc h.r15]
    exact ite_congr (propext allOk4_succ.symm) (fun _ => rfl) (fun _ => rfl)
  · rcases (by omega : e' < e ∨ e' = e) with he' | rfl
    · exact L.keepPoly hP (kA e' he') (h.mat e' he' f hf)
    · rw [hP.pa rbx_bases]
      exact hres f (by rw [h.sb]; exact hf)

theorem mat_ok {C : Ctx rbs wbs} {E : Ptr} (hc₁ : matChk (rbs ++ wbs) wbs C.chk E = true)
    (hc₂ : ∀ e < 16, sampEChk (rbs ++ wbs) wbs C.chk E e = true) {ek m r : List Byte} {s : State}
    (h : EIn C E ek m r s) (h15 : s.gpr .r15 = 1) : WP isa (mat E) s (EB C E ek m r 16) := by
  simp only [matChk, Bool.and_eq_true, decide_eq_true_eq] at hc₁
  have L := C.lay h.out
  unfold mat
  refine WP.seq (WP.mono (copy_okL L hc₁.1.2 hc₁.1.1) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have h₁ := h.keep hP₁.b hc₁.2
  refine seqR_ok (I := fun e => EB C E ek m r e) 16 0 (fun e _ he s hs =>
    WP.mono (sampE_step (by omega) (hc₂ e (by omega)) hs) fun _ h => h.2) s₁
    ⟨h₁, ?_, by rw [hP₁.cs .r15 (by decide), h15, ifp (show allOk4 (rhoE ek) 0 from fun _ h => absurd h (Nat.not_lt_zero _))],
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [show pa s₁ (sc oSB) = pa s (sc oSB) from hP₁.pa rbx_cs, hb₁]
  exact h.rho

/-! ## Constant time, for a given `ρ` -/

/-- The entries of `Â` sampled so far, for the `ρ` of `ek`. -/
abbrev EBρ (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (e : Nat) (s : State) : Prop :=
  ∃ ek m r, rhoE ek = ρ ∧ EB C E ek m r e s

theorem sampE_tr {C : Ctx rbs wbs} {E : Ptr} {ρ : List Byte} {e : Nat} (he : e < 16)
    (hc : sampEChk (rbs ++ wbs) wbs C.chk E e = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EBρ C E ρ e x ∧ EBρ C E ρ e y) (sampleIJ4 (e / 4) (e % 4))
      (fun x y => LRel rbs wbs x y ∧ EBρ C E ρ (e + 1) x ∧ EBρ C E ρ (e + 1) y) := by
  have hc' := hc
  simp only [sampEChk, Bool.and_eq_true] at hc'
  refine RelCT.stepL C.bs (RelCT.mono (sampP_tr C.bs (by omega) (by omega) hc'.1.1.1 (KeyGen4.setIJ4_taint e he))
    (fun x y ⟨hl, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => ⟨hl, by rw [h₁.sb, h₂.sb, e₁, e₂]⟩) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (sampE_step he hc hx) fun x' hx' => ⟨⟨_, hx'.1⟩, ek, m, r, eρ, hx'.2⟩

/-- The inputs, for the `ρ` of `ek`, with `r15 = 1`. -/
abbrev EIρ (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (s : State) : Prop :=
  ∃ ek m r, rhoE ek = ρ ∧ EIn C E ek m r s ∧ s.gpr .r15 = 1

theorem mat_tr {C : Ctx rbs wbs} {E : Ptr} (hc₁ : matChk (rbs ++ wbs) wbs C.chk E = true)
    (hc₂ : ∀ e < 16, sampEChk (rbs ++ wbs) wbs C.chk E e = true) {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, E.1]) (copy (sc oSB) (E.1, E.2 + 1536) 32) h).isSome = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EIρ C E ρ x ∧ EIρ C E ρ y) (mat E)
      (fun x y => LRel rbs wbs x y ∧ EBρ C E ρ 16 x ∧ EBρ C E ρ 16 y) := by
  have hc₁' := hc₁
  simp only [matChk, copyChk, wrOk, rdOk, Bool.and_eq_true] at hc₁'
  have hin₁ : inB (rbs ++ wbs) (sc oSB) 32 = true := hc₁'.1.1.1.1.1.1.1.2
  have hin₂ : inB (rbs ++ wbs) (E.1, E.2 + 1536) 32 = true := hc₁'.1.1.1.1.1.2.2
  unfold mat
  refine RelCT.seq (RelCT.stepL (J := EBρ C E ρ 0) C.bs (taintRel [.rbx, E.1] (fun x y h =>
      fa2 (h.1.eq hin₁) (h.1.eq (p := (E.1, E.2 + 1536)) hin₂)) ht) fun x ⟨ek, m, r, eρ, hx, h15⟩ => ?_)
    (seqR_tr (R := fun e => fun x y => LRel rbs wbs x y ∧ EBρ C E ρ e x ∧ EBρ C E ρ e y) 16 0
      fun e _ he => sampE_tr (by omega) (hc₂ e (by omega)))
  simp only [matChk, Bool.and_eq_true, decide_eq_true_eq] at hc₁
  have L := C.lay hx.out
  refine WP.mono (copy_okL L hc₁.1.2 hc₁.1.1) fun x₁ ⟨hP₁, hb₁⟩ => ⟨⟨_, hP₁.b⟩, ek, m, r, eρ, ?_⟩
  refine ⟨hx.keep hP₁.b hc₁.2, ?_, by rw [hP₁.cs .r15 (by decide), h15,
      ifp (show allOk4 (rhoE ek) 0 from fun _ h => absurd h (Nat.not_lt_zero _))],
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [show pa x₁ (sc oSB) = pa x (sc oSB) from hP₁.pa rbx_cs, hb₁]
  exact hx.rho

end Enc4

end VG.Proof.MlKem1024.X86_64
