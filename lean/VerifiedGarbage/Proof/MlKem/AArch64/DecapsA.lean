import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
import VerifiedGarbage.Impl.MlKem.AArch64.Decaps

/-!
# ML-KEM-768 on AArch64: `vg_mlkem768_decaps`, the first phase

Untrusted: everything here is checked by Lean. The prologue,
`m' = K-PKE.Decrypt(dk_PKE, c)` (`m_ok`), `G(m' ‖ h)` and `ρ` (`a_ok`).
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The contract the proof is written against; the artifact's is the
shared contract of `Spec/`, which implies it. AArch64 contract for
`(decapsWith keccak.callee)(dk = x0, ct = x1, key = x2, scratch = x3) -> w0`. -/
def decapsAArch64 : Contract AArch64.isa where
  pre s :=
    let dk : Region := ⟨s.gpr .x0, 2400⟩
    let ct : Region := ⟨s.gpr .x1, 1088⟩
    let key : Region := ⟨s.gpr .x2, 32⟩
    let scratch : Region := ⟨s.gpr .x3, 32768⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [dk, ct] ∧ s.wr = [key, scratch] ∧ dk.Disjoint key ∧ dk.Disjoint scratch ∧ ct.Disjoint key ∧
    ct.Disjoint scratch ∧ key.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint dk ∧ stack.Disjoint ct ∧
    stack.Disjoint key ∧ stack.Disjoint scratch
  post s s' :=
    Outcome (fun iters => decapsInternal mlKem768 iters (bytesAt s.mem (s.gpr .x0) 2400)
        (bytesAt s.mem (s.gpr .x1) 1088)) ((s'.gpr .x0).setWidth 32) (bytesAt s'.mem (s.gpr .x2) 32)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp ∧
      leakRho (dkRho mlKem768 (bytesAt s₁.mem (s₁.gpr .x0) 2400)) =
        leakRho (dkRho mlKem768 (bytesAt s₂.mem (s₂.gpr .x0) 2400))

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Decaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

/-- 0 `dk`, 1 `ct` (read); 2 `key`, 3 `scratch` (written), kept in `x25`–`x28`. -/
def deL : Layout where
  nb := 4
  nrd := 2
  len b := [2400, 1088, 32, 32768].getD b 0
  slot k := k

theorem pre_of {s₀ : State} (h : decapsAArch64.pre s₀) : Pre deL s₀ := by
  obtain ⟨rd, wr, d02, d03, d12, d13, d23, sp16, k0, k1, k2, k3⟩ := h
  refine ⟨by rw [rd]; rfl, by rw [wr]; rfl, ⟨fun b hb c hc hbc hw => ?_, fun b hb => ?_, fun b hb => ?_⟩, sp16,
    fun k hk => hk, by decide, by decide⟩
  · have e : ∀ {x y : Region}, x.Disjoint y → y.Disjoint x := fun h => h.symm
    simp only [deL] at hb hc hw
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hbc | exact absurd hw (by decide) | assumption | exact e ‹_›
  · simp only [deL] at hb
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> decide
  · simp only [deL] at hb
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> assumption

/-- `dk`. -/
abbrev dkD (s₀ : State) : List Byte := bytesAt s₀.mem (kA s₀ 0) 2400
/-- `c`. -/
abbrev cD (s₀ : State) : List Byte := bytesAt s₀.mem (kA s₀ 1) 1088
/-- `m'`. -/
abbrev mD (s₀ : State) : List Byte := decM (dkD s₀) (cD s₀)
/-- `(K', r') = G(m' ‖ h)`. -/
abbrev gD (s₀ : State) : List Byte × List Byte := G (mD s₀ ++ dkH (dkD s₀))
/-- `ρ`. -/
abbrev rhoD (s₀ : State) : List Byte := dkRho mlKem768 (dkD s₀)

/-- Bytes `[o, o + n)` of `dk` or `c`, as they were. -/
theorem slice_eq {s₀ s : State} (h : KB deL s₀ s) {b o n : Nat} (hb : b < 2) (f : o + n ≤ deL.len b) :
    bytesAt s.mem (kA s₀ (deL.slot b) + BitVec.ofNat 64 o) n =
      ((bytesAt s₀.mem (kA s₀ b) (deL.len b)).drop o).take n := by
  rw [show deL.slot b = b from rfl, h.ro_bytes hb f, bytesAt_slice _ _ f]

/-! ## `m'` -/

/-- After `û'[i]` for `i < n`. -/
structure DInv (s₀ : State) (n : Nat) (s : State) : Prop where
  kb : KB deL s₀ s
  x24 : s.gpr .x24 = 1
  u : ∀ i < n, PolyIs s.mem (sA deL s₀ (yOff i)) (ntt (dcU (cD s₀) i))

theorem DInv.frame {s₀ : State} {n : Nat} (hn : n ≤ 3) {s s' : State} (h : DInv s₀ n s) (hk : KB deL s₀ s')
    (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, (R (kA s₀) deL.sc YH (1024 * n)).Disjoint r) : DInv s₀ n s' :=
  ⟨hk, by rw [hx, h.x24], fun i hi => polyIs_frame hf (fun r hr => (hW r hr).sub_left
    (R.sub2 (by simp only [yOff]; omega) (by simp only [yOff]; omega))) (h.u i hi)⟩

/-- A buffer of `scratch` past `û'`. -/
theorem dfar {s₀ : State} (hp : Pre deL s₀) {n o l : Nat} (hn : n ≤ 3) (f : o + l ≤ 32768)
    (h : o + l ≤ YH ∨ YH + 1024 * n ≤ o) : (R (kA s₀) deL.sc YH (1024 * n)).Disjoint (R (kA s₀) deL.sc o l) :=
  sdisj hp (by simp only [YH]; omega) f (by omega)

theorem dfar_list {s₀ : State} (hp : Pre deL s₀) {n : Nat} (hn : n ≤ 3) {W : List Region}
    (hW : ∀ r ∈ W, ∃ o l, r = R (kA s₀) deL.sc o l ∧ o + l ≤ 32768 ∧ (o + l ≤ YH ∨ YH + 1024 * n ≤ o)) :
    ∀ r ∈ W, (R (kA s₀) deL.sc YH (1024 * n)).Disjoint r := fun r hr => by
  obtain ⟨o, l, rfl, f, h⟩ := hW r hr
  exact dfar hp hn f h

theorem u_step {s₀ : State} (hp : Pre deL s₀) {i : Nat} (hi : i < 3) {s : State} (h : DInv s₀ i s) :
    WP isa (deU i) s (DInv s₀ (i + 1)) := by
  have hpo := po_y hi
  refine WP.seq (WP.mono (dd_ok hp (k := 1) (o := 320 * i) (d := 10) (off := yOff i) (by decide)
    (show 320 * i + 32 * 10 ≤ 1088 by omega) (by decide) hpo (.inl (by decide)) h.kb)
    fun s₁ ⟨kb₁, f₁, p₁, x₁⟩ => ?_)
  have e₁ := h.frame (by omega) kb₁ x₁ f₁ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact dfar hp (by omega) hpo.le (.inr (by simp only [yOff]; omega))
  rw [slice_eq h.kb (b := 1) (by decide) (show 320 * i + 32 * 10 ≤ 1088 by omega)] at p₁
  refine WP.mono (ntt_ok hp hpo kb₁ p₁.1) fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ => ?_
  have e₂ := e₁.frame (by omega) kb₂ x₂ f₂ fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact dfar hp (by omega) hpo.le (.inr (by simp only [yOff]; omega))
    · exact dfar hp (by omega) (by decide) (.inl (by decide))
  rw [p₁.2] at p₂
  refine ⟨e₂.kb, e₂.x24, fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact e₂.u i' hi'
  · exact p₂

/-- `ŝ[j] = ByteDecode₁₂(dk[384j : 384j + 384])`. -/
theorem dcS_eq (s₀ : State) {j : Nat} (hj : j < 3) :
    ((bytesAt s₀.mem (kA s₀ 0) (deL.len 0)).drop (384 * j)).take 384 =
      ((dkPke (dkD s₀)).drop (384 * j)).take 384 := by
  rw [dkPke, slice_take _ (show 384 * j + 384 ≤ 1152 by omega)]
  rfl

/-- `ŝ[0] û'[0] + ŝ[1] û'[1] + ŝ[2] û'[2]`. -/
theorem dot_ok {s₀ : State} (hp : Pre deL s₀) {s : State} (h : DInv s₀ 3 s) {REST : Prog isa}
    {Q : State → Prop}
    (hR : ∀ s', DInv s₀ 3 s' →
      PolyIs s'.mem (sA deL s₀ TP) (dot3 (dcS (dkPke (dkD s₀))) fun i => ntt (dcU (cD s₀) i)) →
      WP isa REST s' Q) :
    WP isa (.seq (dec12At .x25 0 TH) <| .seq (mulAt TP TH (yOff 0)) <|
      .seq (dec12At .x25 384 TH) <| .seq (mulAt PP TH (yOff 1)) <| .seq (addAt TP PP) <|
      .seq (dec12At .x25 768 TH) <| .seq (mulAt PP TH (yOff 2)) <| .seq (addAt TP PP) REST) s Q := by
  have fw : ∀ {o : Nat}, YH + 3072 ≤ o → o + 1024 ≤ 32768 →
      ∀ r ∈ [R (kA s₀) deL.sc o 1024], (R (kA s₀) deL.sc YH (1024 * 3)).Disjoint r := fun h1 h2 r hr => by
    rw [List.mem_singleton.mp hr]; exact dfar hp (by decide) h2 (.inr h1)
  have fm : ∀ {o : Nat}, YH + 3072 ≤ o → o + 1024 ≤ 32768 →
      ∀ r ∈ [R (kA s₀) deL.sc o 1024, R (kA s₀) deL.sc NS 1024],
        (R (kA s₀) deL.sc YH (1024 * 3)).Disjoint r := fun h1 h2 r hr => by
    rcases mem2' hr with rfl | rfl
    · exact dfar hp (by decide) h2 (.inr h1)
    · exact dfar hp (by decide) (by decide) (.inl (by decide))
  have hS : ∀ {u : State}, KB deL s₀ u → ∀ {j o : Nat}, j < 3 → o = 384 * j →
      decode12 (bytesAt u.mem (kA s₀ (deL.slot 0) + BitVec.ofNat 64 o) 384) = dcS (dkPke (dkD s₀)) j :=
    fun hu j o hj ho => by
      subst ho
      rw [slice_eq hu (b := 0) (by decide) (show 384 * j + 384 ≤ 2400 by omega), dcS_eq s₀ hj]
      rfl
  -- `ŝ[0] û'[0]`
  refine WP.seq (WP.mono (dec12_ok hp (k := 0) (o := 0) (by decide) (by decide) po_TH (.inl (by decide)) h.kb)
    fun s₁ ⟨kb₁, f₁, d₁, x₁⟩ => ?_)
  have e₁ := h.frame (by decide) kb₁ x₁ f₁ (fw (by decide) (by decide))
  rw [hS h.kb (j := 0) (by decide) rfl] at d₁
  have y0 := e₁.u 0 (by decide)
  refine WP.seq (WP.mono (mul_ok hp po_TP po_TH (po_y (by decide)) (.inl (by decide)) (.inr (by decide))
    e₁.kb d₁.1 y0.1) fun s₂ ⟨kb₂, f₂, t₂, x₂⟩ => ?_)
  have e₂ := e₁.frame (by decide) kb₂ x₂ f₂ (fm (by decide) (by decide))
  rw [d₁.2, y0.2] at t₂
  -- `ŝ[1] û'[1]`
  refine WP.seq (WP.mono (dec12_ok hp (k := 0) (o := 384) (by decide) (by decide) po_TH (.inl (by decide))
    e₂.kb) fun s₃ ⟨kb₃, f₃, d₃, x₃⟩ => ?_)
  have e₃ := e₂.frame (by decide) kb₃ x₃ f₃ (fw (by decide) (by decide))
  rw [hS e₂.kb (j := 1) (by decide) rfl] at d₃
  have t₃ := polyIs_frame f₃ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact papart hp po_TP po_TH (by decide)) t₂
  have y1 := e₃.u 1 (by decide)
  refine WP.seq (WP.mono (mul_ok hp po_PP po_TH (po_y (by decide)) (.inl (by decide)) (.inr (by decide))
    e₃.kb d₃.1 y1.1) fun s₄ ⟨kb₄, f₄, p₄, x₄⟩ => ?_)
  have e₄ := e₃.frame (by decide) kb₄ x₄ f₄ (fm (by decide) (by decide))
  have t₄ := polyIs_frame f₄ (fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact papart hp po_TP po_PP (by decide)
    · exact pns hp po_TP) t₃
  rw [d₃.2, y1.2] at p₄
  refine WP.seq (WP.mono (add_ok hp po_TP po_PP (.inl (by decide)) e₄.kb t₄.1 p₄.1)
    fun s₅ ⟨kb₅, f₅, t₅, x₅⟩ => ?_)
  have e₅ := e₄.frame (by decide) kb₅ x₅ f₅ (fw (by decide) (by decide))
  rw [t₄.2, p₄.2] at t₅
  -- `ŝ[2] û'[2]`
  refine WP.seq (WP.mono (dec12_ok hp (k := 0) (o := 768) (by decide) (by decide) po_TH (.inl (by decide))
    e₅.kb) fun s₆ ⟨kb₆, f₆, d₆, x₆⟩ => ?_)
  have e₆ := e₅.frame (by decide) kb₆ x₆ f₆ (fw (by decide) (by decide))
  rw [hS e₅.kb (j := 2) (by decide) rfl] at d₆
  have t₆ := polyIs_frame f₆ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact papart hp po_TP po_TH (by decide)) t₅
  have y2 := e₆.u 2 (by decide)
  refine WP.seq (WP.mono (mul_ok hp po_PP po_TH (po_y (by decide)) (.inl (by decide)) (.inr (by decide))
    e₆.kb d₆.1 y2.1) fun s₇ ⟨kb₇, f₇, p₇, x₇⟩ => ?_)
  have e₇ := e₆.frame (by decide) kb₇ x₇ f₇ (fm (by decide) (by decide))
  have t₇ := polyIs_frame f₇ (fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact papart hp po_TP po_PP (by decide)
    · exact pns hp po_TP) t₆
  rw [d₆.2, y2.2] at p₇
  refine WP.seq (WP.mono (add_ok hp po_TP po_PP (.inl (by decide)) e₇.kb t₇.1 p₇.1)
    fun s₈ ⟨kb₈, f₈, t₈, x₈⟩ => ?_)
  have e₈ := e₇.frame (by decide) kb₈ x₈ f₈ (fw (by decide) (by decide))
  rw [t₇.2, p₇.2] at t₈
  exact hR s₈ e₈ t₈

/-- `m'`, into `MB`. -/
theorem m_ok {s₀ : State} (hp : Pre deL s₀) {s : State} (h : DInv s₀ 0 s) :
    WP isa deM s fun s' => KB deL s₀ s' ∧ s'.gpr .x24 = 1 ∧ bytesAt s'.mem (sA deL s₀ MB) 32 = mD s₀ := by
  refine WP.seq (WP.mono (u_step hp (i := 0) (by decide) h) fun _ h₁ =>
    WP.seq (WP.mono (u_step hp (i := 1) (by decide) h₁) fun _ h₂ =>
    WP.seq (WP.mono (u_step hp (i := 2) (by decide) h₂) fun s₃ h₃ =>
    dot_ok hp h₃ fun s₄ h₄ t₄ => ?_)))
  refine WP.seq (WP.mono (nttInv_ok hp po_TP h₄.kb t₄.1) fun s₅ ⟨kb₅, f₅, t₅, x₅⟩ => ?_)
  rw [t₄.2] at t₅
  refine WP.seq (WP.mono (dd_ok hp (k := 1) (o := 960) (d := 4) (off := EP) (by decide) (by decide) (by decide)
    po_EP (.inl (by decide)) kb₅) fun s₆ ⟨kb₆, f₆, p₆, x₆⟩ => ?_)
  rw [slice_eq kb₅ (b := 1) (by decide) (by decide)] at p₆
  have t₆ := polyIs_frame f₆ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact papart hp po_TP po_EP (by decide)) t₅
  refine WP.seq (WP.mono (sub_ok hp po_EP po_TP (.inl (by decide)) kb₆ p₆.1 t₆.1)
    fun s₇ ⟨kb₇, f₇, p₇, x₇⟩ => ?_)
  rw [p₆.2, t₆.2] at p₇
  refine WP.mono (ce_ok hp (off := EP) (d := 1) (k := 3) (o := MB) po_EP (by decide) (by decide) (by decide)
    (by decide) (.inr ⟨by decide, .inl (by decide)⟩) kb₇ p₇.1) fun s₈ ⟨kb₈, f₈, b₈, x₈⟩ => ?_
  refine ⟨kb₈, by rw [x₈, x₇, x₆, x₅, h₄.x24], ?_⟩
  rw [show sA deL s₀ MB = kA s₀ (deL.slot 3) + BitVec.ofNat 64 MB from rfl, b₈, p₇.2, mD, decM, kpkeDecrypt768]
  rfl

/-! ## `G(m' ‖ h)` and `ρ` -/

/-- After the first phase. -/
structure AfterA (s₀ s : State) : Prop where
  kb : KB deL s₀ s
  x24 : s.gpr .x24 = 1
  m : bytesAt s.mem (sA deL s₀ MB) 32 = mD s₀
  kp : bytesAt s.mem (sA deL s₀ KP) 32 = (gD s₀).1
  r : bytesAt s.mem (sA deL s₀ RB) 32 = (gD s₀).2
  rho : bytesAt s.mem (sA deL s₀ SB) 32 = rhoD s₀

theorem a_ok {s₀ : State} (hp : Pre deL s₀) : WP isa (deAWith keccak.callee) s₀ (AfterA s₀) := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => WP.seq (WP.mono (m_ok hp ⟨h₁.kb, h₁.x24,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s₂ ⟨kb₂, x₂, m₂⟩ => ?_))
  -- `G(m' ‖ h)`
  refine WP.seq (WP.mono (hashWith_ok keccak (hsetup hp kb₂ (by decide : 72 ∈ Spec.Sha3.rates)) (sfx := 6) (by decide)
    (ins := [⟨.x28, MB, 32⟩, ⟨.x25, 2336, 32⟩]) (outs := [⟨.x28, KP, 32⟩, ⟨.x28, RB, 32⟩]) (by simp)
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 3) hp kb₂ (by decide) (by decide) (.inr (by decide)) (by decide) (by decide)
      · exact pieceOk (k := 0) hp kb₂ (by decide) (by decide) (.inl (by decide)) (by decide) (by decide))
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 3) hp kb₂ (by decide) (by decide) (.inr (by decide)) (by decide) (by decide)
      · exact pieceOk (k := 3) hp kb₂ (by decide) (by decide) (.inr (by decide)) (by decide) (by decide))
    (by
      refine List.pairwise_pair.mpr ?_
      simp only [preg, e28 kb₂]
      exact sdisj hp (by decide) (by decide) (by decide)))
    fun s₃ ⟨k₃, o₃⟩ => ?_)
  have kb₃ := kb₂.hash hp k₃ fun p hp' => by
    rcases mem2' hp' with rfl | rfl
    · exact ⟨3, KP, 32, rfl, by decide, by decide, by decide, .inr (.inr (by decide))⟩
    · exact ⟨3, RB, 32, rfl, by decide, by decide, by decide, .inr (.inr (by decide))⟩
  have msg : (List.map (pbytes s₂) [⟨.x28, MB, 32⟩, ⟨.x25, 2336, 32⟩]).flatten = mD s₀ ++ dkH (dkD s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      e28 kb₂, kb₂.x25]
    rw [m₂, slice_eq kb₂ (b := 0) (by decide) (by decide)]
    rfl
  obtain ⟨o₁, o₂, -⟩ := o₃
  rw [msg] at o₁ o₂
  have hG := G_eq (mD s₀ ++ dkH (dkD s₀))
  have kp₃ : bytesAt s₃.mem (sA deL s₀ KP) 32 = (gD s₀).1 := by
    rw [← e28 kb₂, o₁]; show _ = (G (mD s₀ ++ dkH (dkD s₀))).1; rw [hG]; rfl
  have r₃ : bytesAt s₃.mem (sA deL s₀ RB) 32 = (gD s₀).2 := by
    rw [← e28 kb₂, o₂]; show _ = (G (mD s₀ ++ dkH (dkD s₀))).2; rw [hG]; rfl
  have k₃' := k₃
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₂.x28, kb₂.sp] at k₃'
  have m₃ : bytesAt s₃.mem (sA deL s₀ MB) 32 = mD s₀ := by
    rw [bytesAt_frame k₃'.frame (fun r hr => by
      rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
      · exact sdisj hp (by decide) (by decide) (by decide)
      · exact sdisj hp (by decide) (by decide) (by decide)
      · exact below_R hp hp.scb (by decide)
      · exact sdisj hp (by decide) (by decide) (by decide)
      · exact sdisj hp (by decide) (by decide) (by decide)) (by decide)]
    exact m₂
  -- `ρ`
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 0) (D := kA s₀ 3) (so := 2304) (dO := SB) (by decide) (by decide)
    (by decide) (by decide) (hp.args.rdisj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) kb₃.x25 kb₃.x28 (cov_r hp kb₃ (b := 0) (by decide) (by decide)) (cov_s hp kb₃ (by decide)))
    fun s₄ ⟨k₄, f₄, b₄⟩ => ?_
  have kb₄ := kb₃.frame k₄ f₄ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by decide)
  have far₄ : ∀ {o l : Nat}, o + l ≤ 32768 → (o + l ≤ SB ∨ SB + 32 ≤ o) →
      bytesAt s₄.mem (sA deL s₀ o) l = bytesAt s₃.mem (sA deL s₀ o) l := fun f h => by
    refine bytesAt_frame f₄ (fun r hr => ?_) (by omega)
    rw [List.mem_singleton.mp hr]
    exact sdisj hp f (by decide) h
  refine ⟨kb₄, by rw [k₄.get .x24, k₃.cs _ (by decide) (by decide), x₂],
    by rw [far₄ (o := MB) (l := 32) (by decide) (by decide)]; exact m₃,
    by rw [far₄ (o := KP) (l := 32) (by decide) (by decide)]; exact kp₃,
    by rw [far₄ (o := RB) (l := 32) (by decide) (by decide)]; exact r₃, ?_⟩
  rw [show sA deL s₀ SB = kA s₀ 3 + BitVec.ofNat 64 SB from rfl, b₄,
    show kA s₀ 0 = kA s₀ (deL.slot 0) from rfl, slice_eq kb₃ (b := 0) (by decide) (by decide)]
  rfl

end VG.Proof.MlKem.AArch64.Decaps
