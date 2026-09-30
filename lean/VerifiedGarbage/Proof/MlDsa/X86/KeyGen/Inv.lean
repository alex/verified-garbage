import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Base

/-!
# ML-DSA key generation on x86 (32-bit): what holds between the pieces

Untrusted: everything here is checked by Lean. After the seeds, `scratch`
holds `(ρ, ρ′, K)` and the seeds of the samplers (`KB`); after the first `e`
entries of `Â` and `r` of `s₁ ‖ s₂`, the polynomials sampled, reduced (and
small), and the AND of the samplers' results, which is 1 if they are those
of the standard for some bounds, and 0 if key generation fails within the
least bounds (`Good`, `KSamp`). Each is kept by a piece that writes only
buffers apart from those it describes (`KB.keep`, `KSamp.keep`).
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly Bounds minBounds rejNTTPoly rejBoundedPoly keyGenInternal toRq polyAt
  Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (seedA seedS)
open VG.Spec.Sha3 (bytesAt)

/-! ## Bytes -/

theorem st8_bytes (s₀ : State) (m : Mem) (sc o v : Nat) :
    bytesAt (m.writeW (Buf.addr s₀ ⟨sc, o, 1⟩) ((BitVec.ofNat 32 v).setWidth 8)) (Buf.addr s₀ ⟨sc, o, 1⟩) 1 =
      [BitVec.ofNat 8 v] := by
  refine Proof.MlKem.bytesAt_eq (L := [BitVec.ofNat 8 v]) rfl fun i hi => ?_
  obtain rfl : i = 0 := by omega
  simp only [BitVec.add_zero, Proof.MlKem.writeW8_apply, List.getElem_cons_zero, ite_true]
  rw [BitVec.setWidth_ofNat_of_le (by decide)]

/-- The bytes of a part of a buffer. -/
theorem bytes_sub {Y : Lay} {s₀ : State} (hp : TPre Y s₀) (m : Mem) {a o L k c : Nat} (hkc : k + c ≤ L)
    (h₁ : Y.ok ⟨a, o, L⟩ = true) (h₂ : Y.ok ⟨a, o + k, c⟩ = true) :
    bytesAt m (Buf.addr s₀ ⟨a, o + k, c⟩) c = ((bytesAt m (Buf.addr s₀ ⟨a, o, L⟩) L).drop k).take c := by
  rw [Proof.MlKem.bytesAt_slice _ _ hkc, Buf.addr_eq hp h₁, Buf.addr_eq hp h₂, BitVec.add_assoc,
    ← BitVec.ofNat_add]

/-- The bytes of two adjacent buffers. -/
theorem bytes_cat {Y : Lay} {s₀ : State} (hp : TPre Y s₀) (m : Mem) {a o l₁ l₂ : Nat}
    (h₂ : Y.ok ⟨a, o + l₁, l₂⟩ = true) (h : Y.ok ⟨a, o, l₁ + l₂⟩ = true) :
    bytesAt m (Buf.addr s₀ ⟨a, o, l₁ + l₂⟩) (l₁ + l₂) =
      bytesAt m (Buf.addr s₀ ⟨a, o, l₁⟩) l₁ ++ bytesAt m (Buf.addr s₀ ⟨a, o + l₁, l₂⟩) l₂ := by
  have e : Buf.addr s₀ ⟨a, o + l₁, l₂⟩ = Buf.addr s₀ ⟨a, o, l₁ + l₂⟩ + BitVec.ofNat 64 l₁ := by
    rw [Buf.addr_eq hp h₂, Buf.addr_eq hp h, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [Proof.MlKem.bytesAt_add, e]

/-- An ML-DSA polynomial apart from what a piece writes. -/
theorem keepPolyD {Y : Lay} {s₀ : State} (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk)
    {a o : Nat} (hs : Y.apart ⟨a, o, 1024⟩ bs = true) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {f : Poly}
    (h : PolyIs m (Buf.addr s₀ ⟨a, o, 1024⟩) f) : PolyIs m' (Buf.addr s₀ ⟨a, o, 1024⟩) f :=
  Proof.MlDsa.KeyGen.polyIs_congr (Top.keep hp hN hs fr) h

theorem keepRedD {Y : Lay} {s₀ : State} (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk)
    {a o : Nat} (hs : Y.apart ⟨a, o, 1024⟩ bs = true) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m')
    (h : Reduced m (Buf.addr s₀ ⟨a, o, 1024⟩)) : Reduced m' (Buf.addr s₀ ⟨a, o, 1024⟩) :=
  Proof.MlDsa.KeyGen.reduced_congr (Top.keep hp hN hs fr) h

theorem keepPolyAtD {Y : Lay} {s₀ : State} (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk)
    {a o : Nat} (hs : Y.apart ⟨a, o, 1024⟩ bs = true) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') :
    polyAt m' (Buf.addr s₀ ⟨a, o, 1024⟩) = polyAt m (Buf.addr s₀ ⟨a, o, 1024⟩) :=
  Proof.MlDsa.KeyGen.polyAt_congr (Top.keep hp hN hs fr)

/-! ## After the seeds -/

section
variable (p : Params) (s₀ : State)

/-- `(ρ, ρ′, K)`, `ρ` and `ρ′ ‖ · ‖ 0` in `scratch`. -/
structure KB (s : State) : Prop where
  ctx : Ctx (YK p) s₀ s
  hx : bytesAt s.mem (Buf.addr s₀ (sb oHX 128)) 128 = hxOf p s₀
  sa : bytesAt s.mem (Buf.addr s₀ (sb oSA 32)) 32 = rhoOf p s₀
  sbb : bytesAt s.mem (Buf.addr s₀ (sb oSB 64)) 64 = rho'Of p s₀
  z : bytesAt s.mem (Buf.addr s₀ (sb (oSB + 65) 1)) 1 = [0]

/-- The buffers of `KB` are apart from `bs`. -/
def safeKB (bs : List Buf) : Bool :=
  (YK p).apart (sb oHX 128) bs && (YK p).apart (sb oSA 32) bs && (YK p).apart (sb oSB 64) bs &&
    (YK p).apart (sb (oSB + 65) 1) bs

end

theorem KB.keep {p : Params} {s₀ s s' : State} (h : KB p s₀ s) (hp : TPre (YK p) s₀) {bs : List Buf} {N : Nat}
    (hN : N + 16 ≤ 96) (hs : safeKB p bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem) (h' : Ctx (YK p) s₀ s') :
    KB p s₀ s' := by
  simp only [safeKB, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨s₁, s₂⟩, s₃⟩, s₄⟩ := hs
  exact ⟨h', by rw [keepBytes hp hN s₁ fr]; exact h.hx, by rw [keepBytes hp hN s₂ fr]; exact h.sa,
    by rw [keepBytes hp hN s₃ fr]; exact h.sbb, by rw [keepBytes hp hN s₄ fr]; exact h.z⟩

/-! ## The samplers -/

/-- The coefficients of `x` are in `[-η, η]`. -/
def Small (η : Nat) (x : IPoly) : Prop := ∀ c ∈ x.toList, -(η : Int) ≤ c ∧ c ≤ η

/-- The AND `v` of the samplers' results after the first `e` entries of `Â` and
`r` of `s₁ ‖ s₂`: 1 if they are those of the standard, `A` and `S`, for some
bounds; 0 if key generation fails within the least bounds. -/
def Good (p : Params) (s₀ : State) (e r : Nat) (A : Nat → Poly) (S : Nat → IPoly) (v : BitVec 32) : Prop :=
  (v = 1 ∧ ∃ b : Bounds, (∀ e' < e, rejNTTPoly b.rejNTT (seedA (rhoOf p s₀) (e' / p.ℓ) (e' % p.ℓ)) = some (A e')) ∧
      ∀ r' < r, rejBoundedPoly p.η b.rejBounded (seedS (rho'Of p s₀) r') = some (S r')) ∨
    (v = 0 ∧ keyGenInternal p minBounds (xiOf s₀) = none)

theorem good_01 {p : Params} {s₀ : State} {e r : Nat} {A : Nat → Poly} {S : Nat → IPoly} {v : BitVec 32}
    (h : Good p s₀ e r A S v) : v = 0 ∨ v = 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inr h, .inl h]

/-- After the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`. -/
structure KSamp (p : Params) (e r : Nat) (s₀ s : State) : Prop where
  kb : KB p s₀ s
  ex : ∃ (A : Nat → Poly) (S : Nat → IPoly), (∀ e' < e, PolyIs s.mem (Buf.addr s₀ (aB e')) (A e')) ∧
    (∀ r' < r, PolyIs s.mem (Buf.addr s₀ (sB p r')) (toRq (S r')) ∧ Small p.η (S r')) ∧
    Good p s₀ e r A S (accV s₀ s)

/-- The buffers of `KSamp` are apart from `bs`. -/
structure SafeS (p : Params) (e r : Nat) (bs : List Buf) : Prop where
  kb : safeKB p bs = true
  acc : (YK p).apart (sb oACC 4) bs = true
  a : ∀ e' < e, (YK p).apart (aB e') bs = true
  s : ∀ r' < r, (YK p).apart (sB p r') bs = true

theorem KSamp.keep {p : Params} {e r : Nat} {s₀ s s' : State} (h : KSamp p e r s₀ s) (hp : TPre (YK p) s₀)
    {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96) (hs : SafeS p e r bs) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (h' : Ctx (YK p) s₀ s') : KSamp p e r s₀ s' := by
  obtain ⟨A, S, hA, hS, hG⟩ := h.ex
  refine ⟨h.kb.keep hp hN hs.kb fr h', A, S, fun e' he' => keepPolyD hp hN (hs.a e' he') fr (hA e' he'),
    fun r' hr' => ⟨keepPolyD hp hN (hs.s r' hr') fr (hS r' hr').1, (hS r' hr').2⟩, ?_⟩
  rw [show accV s₀ s' = accV s₀ s from keepW hp hN hs.acc fr]
  exact hG

end VG.Proof.MlDsa.X86.KeyGen
