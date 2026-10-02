import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
import VerifiedGarbage.Impl.MlKem.AArch64.Decaps

/-!
# ML-KEM on AArch64: `decaps`, the first phase

The prologue, `m' = K-PKE.Decrypt(dk_PKE, c)` (`m_ok`: `û'` by a loop over
`i < k`, and the sum of products by `WPs.dot`), `G(m' ‖ h)` and `ρ` (`a_ok`).
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.MlKem.AArch64 (KemLay)

/-- AArch64 contract for `decaps(dk = x0, ct = x1, key = x2, scratch = x3) ->
w0` of the parameter set `P`. -/
def decapsAArch64 (P : KemLay) : Contract AArch64.isa where
  pre s :=
    let dk : Region := ⟨s.gpr .x0, P.dkLen⟩
    let ct : Region := ⟨s.gpr .x1, P.ctLen⟩
    let key : Region := ⟨s.gpr .x2, 32⟩
    let scratch : Region := ⟨s.gpr .x3, P.scl⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [dk, ct] ∧ s.wr = [key, scratch] ∧ dk.Disjoint key ∧ dk.Disjoint scratch ∧ ct.Disjoint key ∧
    ct.Disjoint scratch ∧ key.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint dk ∧ stack.Disjoint ct ∧
    stack.Disjoint key ∧ stack.Disjoint scratch
  post s s' :=
    Outcome (fun iters => decapsInternal P.params iters (bytesAt s.mem (s.gpr .x0) P.dkLen)
        (bytesAt s.mem (s.gpr .x1) P.ctLen)) ((s'.gpr .x0).setWidth 32) (bytesAt s'.mem (s.gpr .x2) 32)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp ∧
      leakRho (dkRho P.params (bytesAt s₁.mem (s₁.gpr .x0) P.dkLen)) =
        leakRho (dkRho P.params (bytesAt s₂.mem (s₂.gpr .x0) P.dkLen))

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Decaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- 0 `dk`, 1 `ct` (read); 2 `key`, 3 `scratch` (written), kept in `x25`–`x28`. -/
def deL (P : KemLay) : Layout where
  nb := 4
  nrd := 2
  len b := [P.dkLen, P.ctLen, 32, P.scl].getD b 0
  slot k := k

/-- Arithmetic on the offsets and the buffers of `deL`. -/
macro "dek" : tactic => `(tactic| (
  simp -failIfUnchanged only [deL, List.getD_cons_zero, List.getD_cons_succ, Layout.sc]
  first | decide | kom))

theorem pre_of (hP : P.Wf) {s₀ : State} (h : (decapsAArch64 P).pre s₀) : Pre P (deL P) s₀ := by
  obtain ⟨rd, wr, d02, d03, d12, d13, d23, sp16, k0, k1, k2, k3⟩ := h
  refine ⟨by rw [rd]; rfl, by rw [wr]; rfl, ⟨fun b hb c hc hbc hw => ?_, fun b hb => ?_, fun b hb => ?_⟩, sp16,
    fun k hk => hk, by dek, rfl, hP⟩
  · have e : ∀ {x y : Region}, x.Disjoint y → y.Disjoint x := fun h => h.symm
    simp only [deL] at hb hc hw
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hbc | exact absurd hw (by decide) | assumption | exact e ‹_›
  · simp only [deL] at hb
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
      simp only [deL, List.getD_cons_zero, List.getD_cons_succ] <;> lom
  · simp only [deL] at hb
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> assumption

/-- `dk`. -/
abbrev dkD (P : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem (kA s₀ 0) P.dkLen
/-- `c`. -/
abbrev cD (P : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem (kA s₀ 1) P.ctLen
/-- `m'`. -/
abbrev mD (P : KemLay) (s₀ : State) : List Byte := KPke.decM P.params (dkD P s₀) (cD P s₀)
/-- `(K', r') = G(m' ‖ h)`. -/
abbrev gD (P : KemLay) (s₀ : State) : List Byte × List Byte := G (mD P s₀ ++ KPke.dkH P.params (dkD P s₀))
/-- `ρ`. -/
abbrev rhoD (P : KemLay) (s₀ : State) : List Byte := dkRho P.params (dkD P s₀)

/-- Bytes `[o, o + n)` of `dk` or `c`, as they were. -/
theorem slice_eq {s₀ s : State} (h : KB P (deL P) s₀ s) {b o n : Nat} (hb : b < 2) (f : o + n ≤ (deL P).len b) :
    bytesAt s.mem (kA s₀ ((deL P).slot b) + BitVec.ofNat 64 o) n =
      ((bytesAt s₀.mem (kA s₀ b) ((deL P).len b)).drop o).take n := by
  rw [show (deL P).slot b = b from rfl, h.ro_bytes hb f, bytesAt_slice _ _ f]

/-! ## `m'` -/

/-- After `û'[i]` for `i < n`. -/
structure DInv (P : KemLay) (s₀ : State) (n : Nat) (s : State) : Prop where
  kb : KB P (deL P) s₀ s
  x24 : s.gpr .x24 = 1
  u : ∀ i < n, PolyIs s.mem (sA (deL P) s₀ (yOff P i)) (ntt (KPke.dcU P.params (cD P s₀) i))

theorem DInv.frame {s₀ : State} {n : Nat} {s s' : State} (h : DInv P s₀ n s) (hk : KB P (deL P) s₀ s')
    (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, (R (kA s₀) (deL P).sc (YH P) (1024 * n)).Disjoint r) : DInv P s₀ n s' :=
  ⟨hk, by rw [hx, h.x24], fun i hi => polyIs_frame hf (fun r hr => (hW r hr).sub_left
    (R.sub2 (by simp only [yOff]; omega) (by simp only [yOff]; omega))) (h.u i hi)⟩

/-- A buffer of `scratch` past `û'`. -/
theorem dfar {s₀ : State} (hp : Pre P (deL P) s₀) {n o l : Nat} (hn : n ≤ P.k) (f : o + l ≤ SV P + 48)
    (h : o + l ≤ YH P ∨ YH P + 1024 * n ≤ o) :
    (R (kA s₀) (deL P).sc (YH P) (1024 * n)).Disjoint (R (kA s₀) (deL P).sc o l) :=
  sdisj hp (by kom) f (by omega)

theorem u_step {s₀ : State} (hp : Pre P (deL P) s₀) (hc : Calls P) {i : Nat} (hi : i < P.k) {s : State}
    (h : DInv P s₀ i s) : WP isa (P.deU i) s (DInv P s₀ (i + 1)) := by
  have hw := hp.wf
  have hpo := po_y hw hi
  have hu := du_le hi
  have fu : 32 * P.du * i + 32 * P.du ≤ (deL P).len 1 := by dek
  refine WP.seq (WP.mono (ddL_ok hp hc (k := 1) (o := 32 * P.du * i) (d := P.du) (off := yOff P i) (by decide)
    fu (.inl rfl) hpo (.inl (by dek)) h.kb)
    fun s₁ ⟨kb₁, f₁, p₁, x₁⟩ => ?_)
  have e₁ := h.frame kb₁ x₁ f₁ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact dfar hp (by omega) hpo.le (.inr (by simp only [yOff]; omega))
  rw [slice_eq h.kb (b := 1) (by decide) fu] at p₁
  refine WP.mono (ntt_ok hp hpo kb₁ p₁.1) fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ => ?_
  have e₂ := e₁.frame kb₂ x₂ f₂ fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact dfar hp (by omega) hpo.le (.inr (by simp only [yOff]; omega))
    · exact dfar hp (by omega) (by kom) (.inl (by kom))
  rw [p₁.2] at p₂
  refine ⟨e₂.kb, e₂.x24, fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact e₂.u i' hi'
  · refine (congrArg (fun x => PolyIs s₂.mem (sA (deL P) s₀ (yOff P i')) (ntt x)) ?_).mp p₂
    simp only [KPke.dcU, cD, deL, List.getD_cons_zero, List.getD_cons_succ, KemLay.params]

/-- `ŝ[j] = ByteDecode₁₂(dk[384j : 384j + 384])`. -/
theorem dcS_eq (s₀ : State) {j : Nat} (hj : j < P.k) :
    ((bytesAt s₀.mem (kA s₀ 0) ((deL P).len 0)).drop (384 * j)).take 384 =
      ((KPke.dkPke P.params (dkD P s₀)).drop (384 * j)).take 384 := by
  rw [KPke.dkPke, slice_take _ (show 384 * j + 384 ≤ 384 * P.params.k from mul_succ_le hj)]
  rfl

/-- `ŝ[j] û'[j]` into `h` (`TP` or `PP`), with `ŝ[j]` decoded into `TH`. -/
theorem dprod_ok {s₀ : State} (hp : Pre P (deL P) s₀) {j h : Nat} (hj : j < P.k) (hh : h = TP P ∨ h = PP P)
    {s : State} (e : DInv P s₀ P.k s) :
    WPs [dec12At .x25 (384 * j) (TH P), mulAt h (TH P) (yOff P j)] s fun s' =>
      DInv P s₀ P.k s' ∧
      (∀ a, h = PP P → PolyIs s.mem (sA (deL P) s₀ (TP P)) a → PolyIs s'.mem (sA (deL P) s₀ (TP P)) a) ∧
      PolyIs s'.mem (sA (deL P) s₀ h)
        (multiplyNTTs (dcS (KPke.dkPke P.params (dkD P s₀)) j) (ntt (KPke.dcU P.params (cD P s₀) j))) := by
  have hw := hp.wf
  have hjE := mul_succ_le (a := 384) hj
  have fw : ∀ {o : Nat}, YH P + 1024 * P.k ≤ o → o + 1024 ≤ SV P + 48 →
      ∀ r ∈ [R (kA s₀) (deL P).sc o 1024], (R (kA s₀) (deL P).sc (YH P) (1024 * P.k)).Disjoint r :=
    fun h1 h2 r hr => by rw [List.mem_singleton.mp hr]; exact dfar hp (Nat.le_refl _) h2 (.inr h1)
  have fm : ∀ {o : Nat}, YH P + 1024 * P.k ≤ o → o + 1024 ≤ SV P + 48 →
      ∀ r ∈ [R (kA s₀) (deL P).sc o 1024, R (kA s₀) (deL P).sc NS 1024],
        (R (kA s₀) (deL P).sc (YH P) (1024 * P.k)).Disjoint r := fun h1 h2 r hr => by
    rcases mem2' hr with rfl | rfl
    · exact dfar hp (Nat.le_refl _) h2 (.inr h1)
    · exact dfar hp (Nat.le_refl _) (by kom) (.inl (by kom))
  have f0 : 384 * j + 384 ≤ (deL P).len 0 := by dek
  refine WPs.cons (WP.mono (dec12_ok hp (k := 0) (o := 384 * j) (by decide) f0 (po_TH hw) (.inl (by dek))
    e.kb) fun s₁ ⟨kb₁, f₁, d₁, x₁⟩ => ?_)
  have e₁ := e.frame kb₁ x₁ f₁ (fw (by kom) (by kom))
  rw [slice_eq e.kb (b := 0) (by decide) f0, dcS_eq s₀ hj] at d₁
  have y₁ := e₁.u j hj
  have ph : PO P h := by rcases hh with rfl | rfl; exacts [po_TP hw, po_PP hw]
  refine WPs.single (WP.mono (mul_ok hp ph (po_TH hw) (po_y hw hj) (.inl (by rcases hh with rfl | rfl <;> kom))
    (.inr (by rcases hh with rfl | rfl <;> kom)) e₁.kb d₁.1 y₁.1) fun s₂ ⟨kb₂, f₂, t₂, x₂⟩ => ?_)
  rw [d₁.2, y₁.2] at t₂
  refine ⟨e₁.frame kb₂ x₂ f₂ (fm (by rcases hh with rfl | rfl <;> kom) (by rcases hh with rfl | rfl <;> kom)),
    fun a ep ta => ?_, t₂⟩
  subst ep
  refine polyIs_frame f₂ (fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact papart hp (po_TP hw) (po_PP hw) (.inl (by kom))
    · exact pns hp (po_TP hw)) (polyIs_frame f₁ (fun r hr => ?_) ta)
  rw [List.mem_singleton.mp hr]; exact papart hp (po_TP hw) (po_TH hw) (.inl (by kom))

/-- `m'`, into `MB`. -/
theorem m_ok {s₀ : State} (hp : Pre P (deL P) s₀) (hc : Calls P) {s : State} (h : DInv P s₀ 0 s) :
    WP isa P.deM s fun s' => KB P (deL P) s₀ s' ∧ s'.gpr .x24 = 1 ∧
      bytesAt s'.mem (sA (deL P) s₀ MB) 32 = mD P s₀ := by
  have hw := hp.wf
  have k1 := hw.facts.1
  refine WPs.seqs (by simp) (WPs.append (WPs.append (WPs.mono (WPs.range (I := DInv P s₀)
    (fun i hi _ h => u_step hp hc hi h) h) fun s₃ h₃ => WPs.mono (WPs.dot (tp := TP P) (pp := PP P)
      (term := fun j h => [dec12At .x25 (384 * j) (TH P), mulAt h (TH P) (yOff P j)])
      (E := DInv P s₀ P.k)
      (T := fun s a => PolyIs s.mem (sA (deL P) s₀ (TP P)) a)
      (Q := fun s a => PolyIs s.mem (sA (deL P) s₀ (PP P)) a)
      (v := fun j => multiplyNTTs (dcS (KPke.dkPke P.params (dkD P s₀)) j) (ntt (KPke.dcU P.params (cD P s₀) j)))
      (N := P.k)
      (fun s e => WPs.mono (dprod_ok hp k1 (.inl rfl) e) fun _ ⟨e', _, t'⟩ => ⟨e', t'⟩)
      (fun j _ hj s a e t => WPs.mono (dprod_ok hp hj (.inr rfl) e) fun _ ⟨e', ft, q'⟩ => ⟨e', ft a rfl t, q'⟩)
      (fun s a b e t q => WP.mono (add_ok hp (po_TP hw) (po_PP hw) (.inl (by kom)) e.kb t.1 q.1)
        fun s' ⟨kb', f', t', x'⟩ => ⟨e.frame kb' x' f' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact dfar hp (Nat.le_refl _) (by kom) (.inr (by kom)),
          by rw [t.2, q.2] at t'; exact t'⟩) k1 (Nat.le_refl _) h₃) ?_)))
  intro s₄ ⟨h₄, t₄⟩
  refine WPs.cons (WP.mono (nttInv_ok hp (po_TP hw) h₄.kb t₄.1) fun s₅ ⟨kb₅, f₅, t₅, x₅⟩ => ?_)
  rw [t₄.2] at t₅
  have fv : 32 * P.du * P.k + 32 * P.dv ≤ (deL P).len 1 := by
    simp only [deL, List.getD_cons_zero, List.getD_cons_succ, KemLay.ctLen]
    rw [Nat.mul_add, Nat.mul_assoc]
  refine WPs.cons (WP.mono (ddL_ok hp hc (k := 1) (o := 32 * P.du * P.k) (d := P.dv) (off := EP P) (by decide)
    fv (.inr rfl) (po_EP hw) (.inl (by dek)) kb₅) fun s₆ ⟨kb₆, f₆, p₆, x₆⟩ => ?_)
  rw [slice_eq kb₅ (b := 1) (by decide) fv] at p₆
  have t₆ := polyIs_frame f₆ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact papart hp (po_TP hw) (po_EP hw) (.inr (by kom))) t₅
  refine WPs.cons (WP.mono (sub_ok hp (po_EP hw) (po_TP hw) (.inl (by kom)) kb₆ p₆.1 t₆.1)
    fun s₇ ⟨kb₇, f₇, p₇, x₇⟩ => ?_)
  rw [p₆.2, t₆.2] at p₇
  refine WPs.single (WP.mono (ce_ok hp (off := EP P) (d := 1) (k := 3) (o := MB) (po_EP hw) (by decide)
    (by decide) (by dek) (by dek) (.inr ⟨by kom, .inl (by kom)⟩) kb₇ p₇.1) fun s₈ ⟨kb₈, f₈, b₈, x₈⟩ => ?_)
  refine ⟨kb₈, by rw [x₈, x₇, x₆, x₅, h₄.x24], ?_⟩
  rw [show sA (deL P) s₀ MB = kA s₀ ((deL P).slot 3) + BitVec.ofNat 64 MB from rfl, b₈, p₇.2, mD, KPke.decM,
    KPke.kpkeDecrypt_eq]
  rfl

/-! ## `G(m' ‖ h)` and `ρ` -/

/-- After the first phase. -/
structure AfterA (P : KemLay) (s₀ s : State) : Prop where
  kb : KB P (deL P) s₀ s
  x24 : s.gpr .x24 = 1
  m : bytesAt s.mem (sA (deL P) s₀ MB) 32 = mD P s₀
  kp : bytesAt s.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1
  r : bytesAt s.mem (sA (deL P) s₀ RB) 32 = (gD P s₀).2
  rho : bytesAt s.mem (sA (deL P) s₀ SB) 32 = rhoD P s₀

theorem a_ok {s₀ : State} (hp : Pre P (deL P) s₀) (hc : Calls P) :
    WP isa (P.deAWith keccak.callee) s₀ (AfterA P s₀) := by
  have hw := hp.wf
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => WP.seq (WP.mono (m_ok hp hc ⟨h₁.kb, h₁.x24,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s₂ ⟨kb₂, x₂, m₂⟩ => ?_))
  -- `G(m' ‖ h)`
  refine WP.seq (WP.mono (hashWith_ok keccak (hsetup hp kb₂ (by decide : 72 ∈ Spec.Sha3.rates)) (sfx := 6) (by decide)
    (ins := [⟨.x28, MB, 32⟩, ⟨.x25, 768 * P.k + 32, 32⟩]) (outs := [⟨.x28, KP, 32⟩, ⟨.x28, RB, 32⟩]) (by simp)
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 3) hp kb₂ (by decide) (by dek) (.inr (by decide)) (by decide) (by dek)
      · exact pieceOk (k := 0) hp kb₂ (by decide) (by dek) (.inl (by dek)) (by decide) (by dek))
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 3) hp kb₂ (by decide) (by dek) (.inr (by decide)) (by decide) (by dek)
      · exact pieceOk (k := 3) hp kb₂ (by decide) (by dek) (.inr (by decide)) (by decide) (by dek))
    (by
      refine List.pairwise_pair.mpr ?_
      simp only [preg, e28 kb₂]
      exact sdisj hp (by kom) (by kom) (by decide)))
    fun s₃ ⟨k₃, o₃⟩ => ?_)
  have kb₃ := kb₂.hash hp k₃ fun p hp' => by
    rcases mem2' hp' with rfl | rfl
    · exact ⟨3, KP, 32, rfl, by decide, by dek, by dek, .inr (.inr (by kom))⟩
    · exact ⟨3, RB, 32, rfl, by decide, by dek, by dek, .inr (.inr (by kom))⟩
  have msg : (List.map (pbytes s₂) [⟨.x28, MB, 32⟩, ⟨.x25, 768 * P.k + 32, 32⟩]).flatten =
      mD P s₀ ++ KPke.dkH P.params (dkD P s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      e28 kb₂, kb₂.x25]
    rw [m₂, slice_eq kb₂ (b := 0) (by decide) (by dek)]
    rfl
  obtain ⟨o₁, o₂, -⟩ := o₃
  rw [msg] at o₁ o₂
  have hG := G_eq (mD P s₀ ++ KPke.dkH P.params (dkD P s₀))
  have kp₃ : bytesAt s₃.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1 := by
    rw [← e28 kb₂, o₁]; show _ = (G (mD P s₀ ++ KPke.dkH P.params (dkD P s₀))).1; rw [hG]; rfl
  have r₃ : bytesAt s₃.mem (sA (deL P) s₀ RB) 32 = (gD P s₀).2 := by
    rw [← e28 kb₂, o₂]; show _ = (G (mD P s₀ ++ KPke.dkH P.params (dkD P s₀))).2; rw [hG]; rfl
  have k₃' := k₃
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₂.x28, kb₂.sp] at k₃'
  have m₃ : bytesAt s₃.mem (sA (deL P) s₀ MB) 32 = mD P s₀ := by
    rw [bytesAt_frame k₃'.frame (fun r hr => by
      rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
      · exact sdisj hp (by kom) (by kom) (by decide)
      · exact sdisj hp (by kom) (by kom) (by decide)
      · exact below_R hp hp.scb (hp.fs (by kom))
      · exact sdisj hp (by kom) (by kom) (by decide)
      · exact sdisj hp (by kom) (by kom) (by decide)) (by decide)]
    exact m₂
  -- `ρ`
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 0) (D := kA s₀ 3) (so := 768 * P.k) (dO := SB) (by decide)
    (by decide) (by kom) (by decide) (hp.args.rdisj (by dek) (by dek) (by dek) (hp.fs (by kom)) (by dek)
      (by dek)) kb₃.x25 kb₃.x28 (cov_r hp kb₃ (b := 0) (by dek) (by dek)) (cov_s hp kb₃ (by kom)))
    fun s₄ ⟨k₄, f₄, b₄⟩ => ?_
  have kb₄ := kb₃.frame k₄ f₄ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by kom)
  have far₄ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ SB ∨ SB + 32 ≤ o) →
      bytesAt s₄.mem (sA (deL P) s₀ o) l = bytesAt s₃.mem (sA (deL P) s₀ o) l := fun f h => by
    refine bytesAt_frame f₄ (fun r hr => ?_) (by kom)
    rw [List.mem_singleton.mp hr]
    exact sdisj hp f (by kom) h
  refine ⟨kb₄, by rw [k₄.get .x24, k₃.cs _ (by decide) (by decide), x₂],
    by rw [far₄ (o := MB) (l := 32) (by kom) (by decide)]; exact m₃,
    by rw [far₄ (o := KP) (l := 32) (by kom) (by decide)]; exact kp₃,
    by rw [far₄ (o := RB) (l := 32) (by kom) (by decide)]; exact r₃, ?_⟩
  rw [show sA (deL P) s₀ SB = kA s₀ 3 + BitVec.ofNat 64 SB from rfl, b₄,
    show kA s₀ 0 = kA s₀ ((deL P).slot 0) from rfl, slice_eq kb₃ (b := 0) (by decide) (by dek)]
  rfl

end VG.Proof.MlKem.AArch64.Decaps
