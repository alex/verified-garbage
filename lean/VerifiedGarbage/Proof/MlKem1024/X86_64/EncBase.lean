import VerifiedGarbage.Proof.MlKem1024.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.EncTop
import VerifiedGarbage.Impl.MlKem1024.X86_64.Encrypt

/-!
# ML-KEM-1024 on x86-64: K-PKE.Encrypt, its context and the matrix

`encrypt1024` runs in both `vg_mlkem1024_encaps` and `vg_mlkem1024_decaps`, in
their layouts, and keeps what each of them holds of its state (`Ctx`, as
ML-KEM-768's `encrypt`: a predicate `Out` kept by the pieces whose writes pass
`chk`). Its inputs (`EIn`): the encryption key at `E`, the message at `M`, the
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

/-- Entries `e, …, e + 3` of `Â`. -/
def quadEChk (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (e : Nat) : Bool :=
  quadChk bs wbs (oP (17 + e)) (oP 35) && inKeep bs chk E (KeyGen4.qW4 e) && keepB bs (KeyGen4.qW4 e) (sc oSB) 32 &&
    (List.range e).all fun e' => keepB bs (KeyGen4.qW4 e) (aS4 (e' / 4) (e' % 4)) 1024

theorem quadE_step (v : Sample4Impl) {C : Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {e : Nat} (he : e + 4 ≤ 16)
    (hc : quadEChk (rbs ++ wbs) wbs C.chk E e = true) {s : State} (h : EB C E ek m r e s) :
    WP isa (quad v.callee 4 e (sc (oP (17 + e))) (pS 35)) s fun s' =>
      PPostB s s' (KeyGen4.qW4 e) ∧ EB C E ek m r (e + 4) s' := by
  simp only [quadEChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨hq, hkc⟩, kB⟩, kA⟩ := hc
  have L := C.lay h.i.out
  refine WP.mono (quad_ok v L C.bs (by omega) hq) fun s' ⟨hP, h15, hres⟩ => ⟨hP, ?_⟩
  refine ⟨h.i.keep hP hkc, by rw [L.keepBytes hP kB]; exact h.sb, ?_, fun e' he' f hf => ?_⟩
  · rw [h15, h.sb, and_acc h.r15]
    exact ite_congr (propext allOk4_add4.symm) (fun _ => rfl) (fun _ => rfl)
  · rcases (by omega : e' < e ∨ e ≤ e') with he'' | he''
    · exact L.keepPoly hP (kA e' he'') (h.mat e' he'' f hf)
    · have := hres (e' - e) (by omega) f (by rw [h.sb, Nat.add_sub_cancel' he'']; exact hf)
      rw [hP.pa rbx_bases, KeyGen4.aS4_eq]
      rwa [show oP (17 + e) + 1024 * (e' - e) = oP (17 + e') by simp only [oP]; omega] at this

/-- The checks of the four groups of four entries of `Â`. -/
structure SampChks (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Prop where
  q0 : quadEChk bs wbs chk E 0 = true
  q4 : quadEChk bs wbs chk E 4 = true
  q8 : quadEChk bs wbs chk E 8 = true
  q12 : quadEChk bs wbs chk E 12 = true

theorem samples_ok (v : Sample4Impl) {C : Ctx rbs wbs} {E : Ptr} (hc : SampChks (rbs ++ wbs) wbs C.chk E)
    {ek m r : List Byte} {s : State} (h : EB C E ek m r 0 s) : WP isa (samples4 v.callee) s (EB C E ek m r 16) :=
  WP.seq (WP.mono (quadE_step v (by decide) hc.q0 h) fun _ h₁ =>
    WP.seq (WP.mono (quadE_step v (by decide) hc.q4 h₁.2) fun _ h₂ =>
      WP.seq (WP.mono (quadE_step v (by decide) hc.q8 h₂.2) fun _ h₃ =>
        WP.mono (quadE_step v (by decide) hc.q12 h₃.2) fun _ h => h.2)))

theorem mat_ok (v : Sample4Impl) {C : Ctx rbs wbs} {E : Ptr} (hc₁ : matChk (rbs ++ wbs) wbs C.chk E = true)
    (hc₂ : SampChks (rbs ++ wbs) wbs C.chk E) {ek m r : List Byte} {s : State}
    (h : EIn C E ek m r s) (h15 : s.gpr .r15 = 1) : WP isa (mat v.callee E) s (EB C E ek m r 16) := by
  simp only [matChk, Bool.and_eq_true, decide_eq_true_eq] at hc₁
  have L := C.lay h.out
  unfold mat
  refine WP.seq (WP.mono (copy_okL L hc₁.1.2 hc₁.1.1) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have h₁ := h.keep hP₁.b hc₁.2
  refine samples_ok v hc₂
    ⟨h₁, ?_, by rw [hP₁.cs .r15 (by decide), h15, ifp (show allOk4 (rhoE ek) 0 from fun _ h => absurd h (Nat.not_lt_zero _))],
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [show pa s₁ (sc oSB) = pa s (sc oSB) from hP₁.pa rbx_cs, hb₁]
  exact h.rho

/-! ## Constant time, for a given `ρ` -/

/-- The entries of `Â` sampled so far, for the `ρ` of `ek`. -/
abbrev EBρ (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (e : Nat) (s : State) : Prop :=
  ∃ ek m r, rhoE ek = ρ ∧ EB C E ek m r e s

theorem quadE_tr (v : Sample4Impl) {C : Ctx rbs wbs} {E : Ptr} {ρ : List Byte} {e : Nat} (he : e + 4 ≤ 16)
    (hc : quadEChk (rbs ++ wbs) wbs C.chk E e = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EBρ C E ρ e x ∧ EBρ C E ρ e y) (quad v.callee 4 e (sc (oP (17 + e))) (pS 35))
      (fun x y => LRel rbs wbs x y ∧ EBρ C E ρ (e + 4) x ∧ EBρ C E ρ (e + 4) y) := by
  have hc' := hc
  simp only [quadEChk, Bool.and_eq_true] at hc'
  refine RelCT.stepL C.bs (RelCT.mono (quad_tr (ρ := ρ) v C.bs (by omega) (fun k hk => ⟨by omega, by omega⟩)
      hc'.1.1.1)
    (fun x y ⟨hl, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => ⟨hl, ⟨by rw [h₁.sb, e₁], fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      ⟨by rw [h₂.sb, e₂], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (quadE_step v he hc hx) fun x' hx' => ⟨⟨_, hx'.1⟩, ek, m, r, eρ, hx'.2⟩

/-- The inputs, for the `ρ` of `ek`, with `r15 = 1`. -/
abbrev EIρ (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (s : State) : Prop :=
  ∃ ek m r, rhoE ek = ρ ∧ EIn C E ek m r s ∧ s.gpr .r15 = 1

theorem mat_tr (v : Sample4Impl) {C : Ctx rbs wbs} {E : Ptr} (hc₁ : matChk (rbs ++ wbs) wbs C.chk E = true)
    (hc₂ : SampChks (rbs ++ wbs) wbs C.chk E) {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, E.1]) (copy (sc oSB) (E.1, E.2 + 1536) 32) h).isSome = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EIρ C E ρ x ∧ EIρ C E ρ y) (mat v.callee E)
      (fun x y => LRel rbs wbs x y ∧ EBρ C E ρ 16 x ∧ EBρ C E ρ 16 y) := by
  have hc₁' := hc₁
  simp only [matChk, copyChk, wrOk, rdOk, Bool.and_eq_true] at hc₁'
  have hin₁ : inB (rbs ++ wbs) (sc oSB) 32 = true := hc₁'.1.1.1.1.1.1.1.2
  have hin₂ : inB (rbs ++ wbs) (E.1, E.2 + 1536) 32 = true := hc₁'.1.1.1.1.1.2.2
  unfold mat
  refine RelCT.seq (RelCT.stepL (J := EBρ C E ρ 0) C.bs (taintRel [.rbx, E.1] (fun x y h =>
      fa2 (h.1.eq hin₁) (h.1.eq (p := (E.1, E.2 + 1536)) hin₂)) ht) fun x ⟨ek, m, r, eρ, hx, h15⟩ => ?_)
    (RelCT.seq (quadE_tr v (by decide) hc₂.q0) (RelCT.seq (quadE_tr v (by decide) hc₂.q4)
      (RelCT.seq (quadE_tr v (by decide) hc₂.q8) (quadE_tr v (by decide) hc₂.q12))))
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
