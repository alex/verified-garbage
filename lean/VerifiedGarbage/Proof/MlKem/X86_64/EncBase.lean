import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Impl.MlKem.X86_64.Encrypt

/-!
# ML-KEM on x86-64: K-PKE.Encrypt, its context and the matrix

`encrypt L` runs in both encapsulation and decapsulation, in their layouts,
and keeps what each of them holds of its state (`Ctx`: a predicate `Out` kept
by the pieces whose writes pass `chk`). Its inputs (`EIn`): the encryption
key at `E`, the message at `M`, the randomness at `G + 32`. The matrix `Â`
from `ρ` (the last 32 bytes of the key), as in key generation (`mat_ok`), and
its constant time, for a given `ρ` (`mat_tr`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- What a top-level function holds of its state, in its layout. -/
structure Ctx (rbs wbs : List (Reg × Nat)) where
  Out : State → Prop
  chk : List (Ptr × Nat) → Bool
  bs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases
  lay : ∀ {s}, Out s → Lay rbs wbs s
  step : ∀ {s s' : State} {ws : List (Ptr × Nat)}, Out s → PPostB s s' ws → chk ws = true → Out s'

/-- Two runs in a layout, each satisfying `I`, each piece keeping the layout. -/
theorem RelCT.stepL {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {c : Prog isa}
    {I J : State → Prop} (htr : RelCT isa (fun x y => LRel rbs wbs x y ∧ I x ∧ I y) c fun _ _ => True)
    (hw : ∀ x, I x → WP isa c x fun x' => (∃ W, PostB x x' W) ∧ J x') :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ I x ∧ I y) c (fun x y => LRel rbs wbs x y ∧ J x ∧ J y) :=
  RelCT.postDep htr (F := fun x x' => (∃ W, PostB x x' W) ∧ J x') (fun x y h => ⟨hw x h.2.1, hw y h.2.2⟩)
    fun _ _ _ _ h ⟨⟨_, hx⟩, jx⟩ ⟨⟨_, hy⟩, jy⟩ => ⟨h.1.post hcs hx hy, jx, jy⟩

/-- The compression and decompression the parameter set `L` calls, verified
for widths `wc` and `wd` that include `d_u` and `d_v`. -/
structure KemCalls (L : Kem) (wc wd : List Nat) : Prop where
  ce : CEImpl L.ceN L.ce wc
  dd : DDImpl L.ddN L.dd wd
  du : L.du ∈ wc ∧ L.du ∈ wd
  dv : L.dv ∈ wc ∧ L.dv ∈ wd

namespace Enc

open VG.Impl.MlKem.X86_64.Encrypt

variable {rbs wbs : List (Reg × Nat)}

/-- `ρ` of the key. -/
abbrev rhoE (L : Kem) (ek : List Byte) : List Byte := ekRho L.p ek

/-- The inputs: `ek` at `E`, `m` at `M` and `r` at `G + 32`. -/
structure EIn (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (s : State) : Prop where
  out : C.Out s
  ek : bytesAt s.mem (pa s E) L.ekLen = ek
  m : bytesAt s.mem (pa s (sc oM)) 32 = m
  r : bytesAt s.mem (pa s sigP) 32 = r

/-- A piece writing `ws` keeps the inputs. -/
def inKeep (L : Kem) (bs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (ws : List (Ptr × Nat)) :
    Bool :=
  chk ws && keepB bs ws E L.ekLen && keepB bs ws (sc oM) 32 && keepB bs ws sigP 32

theorem EIn.keep {L : Kem} {C : Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {s s' : State} (h : EIn L C E ek m r s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hc : inKeep L (rbs ++ wbs) C.chk E ws = true) :
    EIn L C E ek m r s' := by
  simp only [inKeep, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hc, k1⟩, k2⟩, k3⟩ := hc
  have L₀ := C.lay h.out
  exact ⟨C.step h.out hP hc, by rw [L₀.keepBytes hP k1]; exact h.ek, by rw [L₀.keepBytes hP k2]; exact h.m,
    by rw [L₀.keepBytes hP k3]; exact h.r⟩

theorem EIn.rho {L : Kem} {C : Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {s : State} (h : EIn L C E ek m r s) :
    bytesAt s.mem (pa s (E.1, E.2 + 384 * L.k)) 32 = rhoE L ek := by
  rw [← h.ek]
  show _ = ((bytesAt s.mem (pa s E) (384 * L.k + 32)).drop (384 * L.k)).take 32
  rw [bytesAt_slice _ _ (show 384 * L.k + 32 ≤ 384 * L.k + 32 from Nat.le_refl _), pa, pa, off_add]

theorem r14_na : Reg.r14 ∉ argRegs := by decide
theorem r14_cs : Reg.r14 ∈ calleeSaved := by decide

/-! ## The matrix -/

/-- After the first `e` entries of `Â`. -/
structure EB (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (e : Nat) (s : State) : Prop where
  i : EIn L C E ek m r s
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = rhoE L ek
  m : MatB L (rhoE L ek) e s

/-- The copy of `ρ`. -/
def matChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  copyChk bs wbs (sc oSB) (E.1, E.2 + 384 * L.k) 32 && decide (E.1 ≠ .rdi) && inKeep L bs chk E [(sc oSB, 32)]

/-- Entry `e` of `Â`. -/
def sampEChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (e : Nat) : Bool :=
  ijChk bs wbs (pS (L.pA + e)) && inKeep L bs chk E (KeyGen.ijW L e) && keepB bs (KeyGen.ijW L e) (sc oSB) 32 &&
    (List.range e).all fun e' => keepB bs (KeyGen.ijW L e) (pS (L.pA + e')) 1024

theorem sampE_step {L : Kem} {C : Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {e : Nat} (hk : L.k ≤ 4)
    (he : e < L.k * L.k) (hc : sampEChk L (rbs ++ wbs) wbs C.chk E e = true) {s : State} (h : EB L C E ek m r e s) :
    WP isa (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k)) s fun s' =>
      PPostB s s' (KeyGen.ijW L e) ∧ EB L C E ek m r (e + 1) s' := by
  simp only [sampEChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨hij, hkc⟩, kB⟩, kA⟩ := hc
  have L₀ := C.lay h.i.out
  refine WP.mono (sampleIJ_ok L₀ C.bs rbx_na (by have := div_lt_k he; omega) (by have := mod_lt_k he; omega) hij)
    fun s' ⟨hP, h15, hres⟩ => ⟨hP, h.i.keep hP hkc, by rw [L₀.keepBytes hP kB]; exact h.sb,
      h.m.single h.sb L₀ hP kA h15 hres⟩

/-- Entries `e, …, e + 3` of `Â`. -/
def quadEChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (e : Nat) : Bool :=
  quadChk bs wbs (oP (L.pA + e)) (oP L.pW) && inKeep L bs chk E (KeyGen.qW L e) &&
    keepB bs (KeyGen.qW L e) (sc oSB) 32 && (List.range e).all fun e' => keepB bs (KeyGen.qW L e) (pS (L.pA + e')) 1024

theorem quadE_step (v : Sample4Impl) {L : Kem} {C : Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {e : Nat}
    (he : e + 4 ≤ 256) (hc : quadEChk L (rbs ++ wbs) wbs C.chk E e = true) {s : State} (h : EB L C E ek m r e s) :
    WP isa (quad v.callee L.k e (pS (L.pA + e)) (pS L.pW)) s fun s' =>
      PPostB s s' (KeyGen.qW L e) ∧ EB L C E ek m r (e + 4) s' := by
  simp only [quadEChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨hq, hkc⟩, kB⟩, kA⟩ := hc
  have L₀ := C.lay h.i.out
  refine WP.mono (quad_ok v L₀ C.bs he hq) fun s' ⟨hP, h15, hres⟩ =>
    ⟨hP, h.i.keep hP hkc, by rw [L₀.keepBytes hP kB]; exact h.sb, h.m.four h.sb L₀ hP kA h15 hres⟩

theorem mat_ok (v : Sample4Impl) {L : Kem} {C : Ctx rbs wbs} {E : Ptr} (hk : L.k ≤ 4)
    (hc₁ : matChk L (rbs ++ wbs) wbs C.chk E = true)
    (hq : ∀ q < L.k * L.k / 4, quadEChk L (rbs ++ wbs) wbs C.chk E (4 * q) = true)
    (hs : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e → sampEChk L (rbs ++ wbs) wbs C.chk E e = true)
    {ek m r : List Byte} {s : State} (h : EIn L C E ek m r s) (h15 : s.gpr .r15 = 1) :
    WP isa (mat L v.callee E) s (EB L C E ek m r (L.k * L.k)) := by
  simp only [matChk, Bool.and_eq_true, decide_eq_true_eq] at hc₁
  have L₀ := C.lay h.out
  unfold mat
  refine WP.seq (WP.mono (copy_okL L₀ hc₁.1.2 hc₁.1.1) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have h₁ := h.keep hP₁.b hc₁.2
  refine samples_ok' L v.callee (I := EB L C E ek m r) (fun e he he' s hs' => WP.mono (sampE_step hk he (hs e he he') hs')
    fun _ h => h.2) (fun q hq' s hs' => WP.mono (quadE_step v (by
      have : L.k * L.k ≤ 16 := Nat.mul_le_mul hk hk
      omega) (hq q hq') hs') fun _ h => h.2)
    ⟨h₁, ?_, MatB.zero L _ (by rw [hP₁.cs .r15 (by decide), h15])⟩
  rw [show pa s₁ (sc oSB) = pa s (sc oSB) from hP₁.pa rbx_cs, hb₁]
  exact h.rho

/-! ## Constant time, for a given `ρ` -/

/-- The entries of `Â` sampled so far, for the `ρ` of `ek`. -/
abbrev EBρ (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (e : Nat) (s : State) : Prop :=
  ∃ ek m r, rhoE L ek = ρ ∧ EB L C E ek m r e s

theorem sampE_tr {L : Kem} {C : Ctx rbs wbs} {E : Ptr} {ρ : List Byte} {e : Nat} (hk : L.k ≤ 4) (he : e < L.k * L.k)
    (hc : sampEChk L (rbs ++ wbs) wbs C.chk E e = true)
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx])
      (.block (setB (sc (oSB + 32)) (e % L.k) ++ setB (sc (oSB + 33)) (e / L.k))) (.block [])).isSome = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EBρ L C E ρ e x ∧ EBρ L C E ρ e y)
      (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k))
      (fun x y => LRel rbs wbs x y ∧ EBρ L C E ρ (e + 1) x ∧ EBρ L C E ρ (e + 1) y) := by
  have hc' := hc
  simp only [sampEChk, Bool.and_eq_true] at hc'
  refine RelCT.stepL C.bs (RelCT.mono (sampleIJ_tr C.bs rbx_na (by have := div_lt_k he; omega)
      (by have := mod_lt_k he; omega) hc'.1.1.1 ht)
    (fun x y ⟨hl, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => ⟨hl, by rw [h₁.sb, h₂.sb, e₁, e₂]⟩) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (sampE_step hk he hc hx) fun x' hx' => ⟨⟨_, hx'.1⟩, ek, m, r, eρ, hx'.2⟩

/-- The inputs, for the `ρ` of `ek`, with `r15 = 1`. -/
abbrev EIρ (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (s : State) : Prop :=
  ∃ ek m r, rhoE L ek = ρ ∧ EIn L C E ek m r s ∧ s.gpr .r15 = 1

theorem quadE_tr (v : Sample4Impl) {L : Kem} {C : Ctx rbs wbs} {E : Ptr} {ρ : List Byte} {e : Nat} (hk : L.k ≤ 4)
    (he : e + 4 ≤ L.k * L.k) (hc : quadEChk L (rbs ++ wbs) wbs C.chk E e = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EBρ L C E ρ e x ∧ EBρ L C E ρ e y)
      (quad v.callee L.k e (pS (L.pA + e)) (pS L.pW))
      (fun x y => LRel rbs wbs x y ∧ EBρ L C E ρ (e + 4) x ∧ EBρ L C E ρ (e + 4) y) := by
  have hc' := hc
  simp only [quadEChk, Bool.and_eq_true] at hc'
  have h16 : L.k * L.k ≤ 16 := Nat.mul_le_mul hk hk
  refine RelCT.stepL C.bs (RelCT.mono (quad_tr (ρ := ρ) v C.bs (by omega)
      (fun t ht => ⟨by have := div_lt_k (show e + t < L.k * L.k by omega); omega,
        by have := mod_lt_k (show e + t < L.k * L.k by omega); omega⟩) hc'.1.1.1)
    (fun x y ⟨hl, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => ⟨hl, ⟨by rw [h₁.sb, e₁], fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      ⟨by rw [h₂.sb, e₂], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (quadE_step v (by omega) hc hx) fun x' hx' =>
      ⟨⟨_, hx'.1⟩, ek, m, r, eρ, hx'.2⟩

theorem mat_tr (v : Sample4Impl) {L : Kem} {C : Ctx rbs wbs} {E : Ptr} (hk : L.k ≤ 4)
    (hc₁ : matChk L (rbs ++ wbs) wbs C.chk E = true)
    (hq : ∀ q < L.k * L.k / 4, quadEChk L (rbs ++ wbs) wbs C.chk E (4 * q) = true)
    (hs : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e → sampEChk L (rbs ++ wbs) wbs C.chk E e = true)
    (hij : ∀ e < L.k * L.k, (taint.check (X86_64.Taint.ofRegs [.rbx])
      (.block (setB (sc (oSB + 32)) (e % L.k) ++ setB (sc (oSB + 33)) (e / L.k))) (.block [])).isSome = true)
    {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, E.1]) (copy (sc oSB) (E.1, E.2 + 384 * L.k) 32) h).isSome = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EIρ L C E ρ x ∧ EIρ L C E ρ y) (mat L v.callee E)
      (fun x y => LRel rbs wbs x y ∧ EBρ L C E ρ (L.k * L.k) x ∧ EBρ L C E ρ (L.k * L.k) y) := by
  have hc₁' := hc₁
  simp only [matChk, copyChk, wrOk, rdOk, Bool.and_eq_true] at hc₁'
  have hin₁ : inB (rbs ++ wbs) (sc oSB) 32 = true := hc₁'.1.1.1.1.1.1.1.2
  have hin₂ : inB (rbs ++ wbs) (E.1, E.2 + 384 * L.k) 32 = true := hc₁'.1.1.1.1.1.2.2
  unfold mat
  refine RelCT.seq (RelCT.stepL (J := EBρ L C E ρ 0) C.bs (taintRel [.rbx, E.1] (fun x y h =>
      fa2 (h.1.eq hin₁) (h.1.eq (p := (E.1, E.2 + 384 * L.k)) hin₂)) ht) fun x ⟨ek, m, r, eρ, hx, h15⟩ => ?_)
    (samples_tr' L v.callee (R := fun e x y => LRel rbs wbs x y ∧ EBρ L C E ρ e x ∧ EBρ L C E ρ e y)
      (fun e he he' => sampE_tr hk he (hs e he he') (hij e he))
      (fun q hq' => quadE_tr v hk (by omega) (hq q hq')))
  simp only [matChk, Bool.and_eq_true, decide_eq_true_eq] at hc₁
  have L₀ := C.lay hx.out
  refine WP.mono (copy_okL L₀ hc₁.1.2 hc₁.1.1) fun x₁ ⟨hP₁, hb₁⟩ => ⟨⟨_, hP₁.b⟩, ek, m, r, eρ, ?_⟩
  refine ⟨hx.keep hP₁.b hc₁.2, ?_, MatB.zero L _ (by rw [hP₁.cs .r15 (by decide), h15])⟩
  rw [show pa x₁ (sc oSB) = pa x (sc oSB) from hP₁.pa rbx_cs, hb₁]
  exact hx.rho

end Enc

end VG.Proof.MlKem.X86_64
