import VerifiedGarbage.Proof.MlDsa.X86.Verify.Base
import VerifiedGarbage.Proof.MlKem.X86.DecapsCmp
import VerifiedGarbage.Proof.Framework.X86.Wp

/-!
# ML-DSA verification on x86 (32-bit): the code between the calls

Untrusted: everything here is checked by Lean. The result ANDed with `eax`
(`accAnd_piece`); a branch on the result so far (`ifOk_piece`), whose
condition must be public; and the result ANDed with the equality of two
byte strings, compared without a branch on them (`cmpAnd_piece`): `edx` is
the OR of the XORs of their bytes (`Decaps.accB`), and `sub edx, 1; sbb eax,
eax` all ones exactly when it is 0.
-/

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.Sha3 (bytesAt)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-! ## The result ANDed with `eax` -/

theorem accAnd_wp {s₀ s : State} (hp : TPre Y s₀) (hc : Y.okW (accB Y) = true) (h : Ctx Y s₀ s)
    {Q : State → Prop}
    (k : ∀ s', Ctx Y s₀ s' →
      s'.mem = s.mem.writeW (Buf.addr s₀ (accB Y)) (s.mem.readW (Buf.addr s₀ (accB Y)) 32 &&& s.gpr .eax) → Q s') :
    WP isa (.block accAnd) s Q := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 0) (n := 4) (Nat.le_refl _)
  simp only [BitVec.add_zero] at hcr
  have hin : InRegions s.wr (Buf.addr s₀ (accB Y)) 4 := by
    have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 4) (Nat.le_refl _)
    simpa using this
  have hinR : InRegions (s.rd ++ s.wr) (Buf.addr s₀ (accB Y)) 4 := by
    have := Buf.inRegR hp hc₁ h.rd h.wr (o := 0) (n := 4) (Nat.le_refl _)
    simpa using this
  have ea : s.ea (at_ .esi oACC) = Buf.addr s₀ (accB Y) := by simp only [State.ea, at_]; rw [h.esi]
  refine wp_movm' (by rw [ea]; exact hinR) fun s₁ o₁ v₁ => ?_
  have h₁ := h.only o₁ (by decide) (by decide)
  refine wp_andr fun s₂ o₂ v₂ => ?_
  have h₂ := h₁.only o₂ (by decide) (by decide)
  have ea₂ : s₂.ea (at_ .esi oACC) = Buf.addr s₀ (accB Y) := by simp only [State.ea, at_]; rw [h₂.esi]
  refine wp_store' (by rw [ea₂, h₂.wr, ← h.wr]; exact hin) fun s₃ g₃ r₃ w₃ m₃ => WP.block_nil_iff.mpr ?_
  refine k _ ⟨by rw [g₃]; exact h₂.esp, by rw [r₃]; exact h₂.rd, by rw [w₃]; exact h₂.wr,
    by rw [g₃]; exact h₂.esi, ?_⟩ ?_
  · rw [m₃, ea₂]; exact h₂.frame.writeW hr _ hcr
  · rw [m₃, ea₂, o₂.mem, o₁.mem, v₂, v₁, ea, o₁.gpr .eax (by decide)]

theorem accAnd_piece (hc : Y.okW (accB Y) = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (.block accAnd) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      s'.mem = s.mem.writeW (Buf.addr s₀ (accB Y)) (s.mem.readW (Buf.addr s₀ (accB Y)) 32 &&& s.gpr .eax) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.block accAnd) :=
  Piece.taint [.esi] (fun s₀ s hp ha => accAnd_wp hp hc (hA s₀ s hp ha) fun s' c' m' => hQ s₀ s s' hp ha c' m')
    (fun s₀ s₀' s s' hp _ hq ha ha' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]) tt

/-- The result set to `eax`. -/
theorem stAcc_piece (hc : Y.okW (accB Y) = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (.block [.store (at_ .esi oACC) .eax]) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → s'.gpr = s.gpr →
      s'.mem = s.mem.writeW (Buf.addr s₀ (accB Y)) (s.gpr .eax) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.block [.store (at_ .esi oACC) .eax]) := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 0) (n := 4) (Nat.le_refl _)
    simp only [BitVec.add_zero] at hcr
    have hin : InRegions s.wr (Buf.addr s₀ (accB Y)) 4 := by
      have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    have ea : s.ea (at_ .esi oACC) = Buf.addr s₀ (accB Y) := by simp only [State.ea, at_]; rw [h.esi]
    refine wp_store' (by rw [ea]; exact hin) fun s₁ g₁ r₁ w₁ m₁ => WP.block_nil_iff.mpr ?_
    refine hQ s₀ s _ hp ha ⟨by rw [g₁]; exact h.esp, by rw [r₁]; exact h.rd, by rw [w₁]; exact h.wr,
      by rw [g₁]; exact h.esi, ?_⟩ (funext g₁) (by rw [m₁, ea])
    rw [m₁, ea]; exact h.frame.writeW hr _ hcr
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

/-! ## A branch on the result -/

/-- The empty block. -/
theorem nil_piece {Pre : State → Prop} {Pub : State → State → Prop} {A B : State → State → Prop}
    (h : ∀ s₀ s, Pre s₀ → A s₀ s → B s₀ s) : Piece Pre Pub A B (.block []) :=
  ⟨fun s₀ s h₀ ha => WP.block_nil_iff.mpr (h s₀ s h₀ ha), fun _ _ _ _ _ => RelCT.nil fun _ _ _ => trivial⟩

theorem ifOk_piece {c : Prog isa} (b : State → Bool) (hc : Y.ok (accB Y) = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (.block [.mov .eax (.mem (at_ .esi oACC)), .alu .test .eax (.reg .eax)])
      ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hA' : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → s'.mem = s.mem → A s₀ s')
    (hb : ∀ s₀ s, TPre Y s₀ → A s₀ s → (s.mem.readW (Buf.addr s₀ (accB Y)) 32 != 0) = b s₀)
    (hbp : ∀ s₀ s₀', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → b s₀ = b s₀')
    (ht : Piece (TPre Y) (TPub Y lk) (fun s₀ s => A s₀ s ∧ b s₀ = true) B c)
    (he : ∀ s₀ s, TPre Y s₀ → A s₀ s → b s₀ = false → B s₀ s) :
    Piece (TPre Y) (TPub Y lk) A B (ifOk c) := by
  unfold ifOk
  refine Piece.seq (B := fun s₀ s₁ => A s₀ s₁ ∧ isa.eval .ne s₁ = some (b s₀))
    (Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt)
    (Piece.ite b (fun _ _ _ h => h.2) hbp (ht.mono (fun _ _ _ h => ⟨h.1.1, h.2⟩) fun _ _ _ h => h)
      (nil_piece fun s₀ s hp h => he s₀ s hp h.1.1 h.2))
  · have h := hA s₀ s hp ha
    have hinR : InRegions (s.rd ++ s.wr) (Buf.addr s₀ (accB Y)) 4 := by
      have := Buf.inRegR hp hc h.rd h.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    have ea : s.ea (at_ .esi oACC) = Buf.addr s₀ (accB Y) := by simp only [State.ea, at_]; rw [h.esi]
    refine wp_movm' (by rw [ea]; exact hinR) fun s₁ o₁ v₁ => ?_
    have h₁ := h.only o₁ (by decide) (by decide)
    refine Wp.wp_test fun s₂ f₂ z₂ => WP.block_nil_iff.mpr ⟨hA' s₀ s s₂ hp ha
      (h₁.same (by rw [f₂.gpr]) (by rw [f₂.gpr]) f₂.rd f₂.wr f₂.mem) (by rw [f₂.mem, o₁.mem]), ?_⟩
    show s₂.zf.map (!·) = _
    rw [z₂, v₁, ea, BitVec.and_self, ← hb s₀ s hp ha]
    rfl
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

/-! ## The result ANDed with an equality -/

/-- Two byte strings of `n` bytes are equal exactly when `accB` of all their bytes is 0. -/
theorem accB_zero {c c' : List Byte} {n : Nat} (h₁ : c.length = n) (h₂ : c'.length = n) :
    c = c' ↔ Decaps.accB c c' n = 0 := by
  rw [Decaps.accB_eq c c' n (by omega) (by omega), List.take_of_length_le (by omega),
    List.take_of_length_le (by omega)]
  exact eq_iff_foldl_or_xor (by omega)

/-- The comparison, from the setup. -/
structure CL (s₀ : State) (a b : Buf) (m : Mem) (k : Nat) (u : State) : Prop where
  ctx : Ctx Y s₀ u
  mem : u.mem = m
  edi : u.gpr .edi = a.ptr s₀ + BitVec.ofNat 32 k
  ebp : u.gpr .ebp = b.ptr s₀ + BitVec.ofNat 32 k
  ecx : u.gpr .ecx = BitVec.ofNat 32 (a.len - k)
  edx : u.gpr .edx = (Decaps.accB (bytesAt m (Buf.addr s₀ a) a.len) (bytesAt m (Buf.addr s₀ b) a.len) k).setWidth 32

theorem cmp_step {s₀ : State} (hp : TPre Y s₀) {a b : Buf} (ha : Y.ok a = true) (hb : Y.ok b = true)
    (hl : a.len = b.len) (hn : a.len < 2 ^ 32) {m : Mem} {k : Nat} (hk : k < a.len) {u : State}
    (h : CL (Y := Y) s₀ a b m k u) :
    WP isa (.block Impl.MlDsa.X86.Verify.cmpBody) u fun u' => CL (Y := Y) s₀ a b m (k + 1) u' ∧
      isa.eval .ne u' = some (decide (k + 1 < a.len)) := by
  have fa := Buf.fit hp ha
  have fb := Buf.fit hp hb
  have e₁ : u.ea (at_ .edi 0) = Buf.addr s₀ a + BitVec.ofNat 64 k := by
    simp only [State.ea, at_, h.edi]; rw [ea_add (by omega)]; rfl
  have e₂ : u.ea (at_ .ebp 0) = Buf.addr s₀ b + BitVec.ofNat 64 k := by
    simp only [State.ea, at_, h.ebp]; rw [ea_add (by omega)]; rfl
  have i₁ := Buf.inRegR (o := k) (n := 1) hp ha h.ctx.rd h.ctx.wr (show k + 1 ≤ a.len by omega)
  refine Decaps.wp_movzx' (by rw [e₁]; exact i₁) fun u₁ o₁ v₁ => ?_
  have c₁ := h.ctx.only o₁ (by decide) (by decide)
  have e₂' : u₁.ea (at_ .ebp 0) = Buf.addr s₀ b + BitVec.ofNat 64 k := by
    rw [← e₂]; simp only [State.ea, at_, o₁.gpr .ebp (by decide)]
  have i₂ := Buf.inRegR (o := k) (n := 1) hp hb c₁.rd c₁.wr (show k + 1 ≤ b.len by omega)
  refine Decaps.wp_movzx' (by rw [e₂']; exact i₂) fun u₂ o₂ v₂ => ?_
  refine Decaps.wp_xorr fun u₃ o₃ v₃ => Decaps.wp_orr fun u₄ o₄ v₄ => wp_addi fun u₅ o₅ v₅ =>
    wp_addi fun u₆ o₆ v₆ => wp_subi_last fun u₇ o₇ v₇ z₇ => ?_
  have c₇ := (((((c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)).only o₄ (by decide)
    (by decide)).only o₅ (by decide) (by decide)).only o₆ (by decide) (by decide)).only o₇ (by decide) (by decide)
  have m₁ : u₁.mem = m := o₁.mem.trans h.mem
  have x₁ : u.mem (Buf.addr s₀ a + BitVec.ofNat 64 k) = (bytesAt m (Buf.addr s₀ a) a.len).getD k 0 := by
    rw [h.mem, bytesAt_getD _ _ hk]
  have x₂ : u₁.mem (Buf.addr s₀ b + BitVec.ofNat 64 k) = (bytesAt m (Buf.addr s₀ b) a.len).getD k 0 := by
    rw [m₁, bytesAt_getD _ _ hk]
  have ex : u₆.gpr .ecx = BitVec.ofNat 32 (a.len - k) := by
    rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide),
      o₂.gpr _ (by decide), o₁.gpr _ (by decide), h.ecx]
  refine ⟨⟨c₇, by rw [o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, m₁], ?_, ?_, by rw [v₇, ex]; exact cnt_next hk,
    ?_⟩, ?_⟩
  · rw [o₇.gpr .edi (by decide), o₆.gpr .edi (by decide), v₅, o₄.gpr .edi (by decide), o₃.gpr .edi (by decide),
      o₂.gpr .edi (by decide), o₁.gpr .edi (by decide), h.edi,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]
  · rw [o₇.gpr .ebp (by decide), v₆, o₅.gpr .ebp (by decide), o₄.gpr .ebp (by decide), o₃.gpr .ebp (by decide),
      o₂.gpr .ebp (by decide), o₁.gpr .ebp (by decide), h.ebp,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]
  · rw [o₇.gpr .edx (by decide), o₆.gpr .edx (by decide), o₅.gpr .edx (by decide), v₄, v₃, o₃.gpr .edx (by decide),
      o₂.gpr .edx (by decide), o₂.gpr .eax (by decide), v₂, o₁.gpr .edx (by decide), v₁, h.edx, e₁, e₂', x₁, x₂,
      Decaps.accB, BitVec.setWidth_or, BitVec.setWidth_xor]
  · show u₇.zf.map (!·) = _
    rw [z₇, ex]; exact cnt_ne hk hn

/-- The result ANDed with all ones if the bytes of `a` and `b` are equal, and zero otherwise. -/
theorem cmpAnd_piece (hsc : Y.sc = vS) {a b : Buf} (hc : Y.okW (accB Y) = true) (ha : Y.ok a = true)
    (hb : Y.ok b = true) (hl : a.len = b.len) (hn : a.len < 2 ^ 32)
    {h₁ h₂ h₃ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .edi a ++ ptrTo Y.sc .ebp b ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 a.len)), .mov .edx (.imm 0)] : List Instr))) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.edi, .ebp, .ecx]) (.loop (.block Impl.MlDsa.X86.Verify.cmpBody) .ne) h₂).isSome = true)
    (t₃ : (VG.X86.taint.check (τr [.esi]) (.block ([.alu .sub .edx (.imm 1), .alu .sbb .eax (.reg .eax)] ++ accAnd))
      h₃).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      s'.mem = s.mem.writeW (Buf.addr s₀ (accB Y)) (s.mem.readW (Buf.addr s₀ (accB Y)) 32 &&&
        Decaps.mask (bytesAt s.mem (Buf.addr s₀ a) a.len = bytesAt s.mem (Buf.addr s₀ b) a.len)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (cmpAnd a b a.len) := by
  unfold cmpAnd
  rw [← hsc]
  refine Piece.seq (setup_piece (fun s₀ s₁ => s₁.gpr .edi = a.ptr s₀ ∧ s₁.gpr .ebp = b.ptr s₀ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 a.len ∧ s₁.gpr .edx = 0) (fun s₀ s hp h => ?_) hA t₁) ?_
  · simp only [List.append_assoc]
    refine ptrTo_ok hp h ha fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine ptrTo_ok hp c₁ hb fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine wp_movi fun s₃ o₃ v₃ => wp_movi fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_
    have c₄ := (c₂.only o₃ (by decide) (by decide)).only o₄ (by decide) (by decide)
    exact ⟨c₄, o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)),
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁],
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂], by rw [o₄.gpr _ (by decide), v₃], v₄⟩
  refine Piece.seq (B := fun s₀ u => ∃ s, A s₀ s ∧ CL (Y := Y) s₀ a b s.mem a.len u)
    (Piece.taint [.edi, .ebp, .ecx] (fun s₀ s₁ hp ⟨s, hs, c₁, m₁, e₁, e₂, e₃, e₄⟩ => ?_)
      (fun s₀ s₀' s s' hp hp' hq ⟨_, _, _, _, e₁, e₂, e₃, _⟩ ⟨_, _, _, _, e₁', e₂', e₃', _⟩ r hr => ?_) t₂) ?_
  · by_cases h0 : a.len = 0
    · exact absurd (Lay.ok_iff.mp ha).2.1 (by omega)
    refine (wp_count (N := a.len) (by omega) (CL (Y := Y) s₀ a b s.mem) ⟨c₁, m₁, by rw [e₁]; simp,
      by rw [e₂]; simp, by rw [e₃]; simp, by rw [e₄]; rfl⟩ fun k hk u h =>
        cmp_step hp ha hb hl hn hk h).mono fun u h => ⟨s, hs, h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁, e₁', hq.ptr ha]
    · rw [e₂, e₂', hq.ptr hb]
    · rw [e₃, e₃']
  refine Piece.taint [.esi] (fun s₀ u hp ⟨s, hs, h⟩ => ?_) (fun s₀ s₀' u u' hp _ hq ⟨s, hs, h⟩ ⟨s', hs', h'⟩ r hr => ?_)
    t₃
  · refine Decaps.wp_subi fun u₁ o₁ v₁ f₁ => Decaps.wp_sbbself f₁ fun u₂ o₂ v₂ => ?_
    have c₂ := (h.ctx.only o₁ (by decide) (by decide)).only o₂ (by decide) (by decide)
    refine accAnd_wp hp hc c₂ fun s' c' m' => hQ s₀ s s' hp hs c' ?_
    have mu : u₂.mem = s.mem := by rw [o₂.mem, o₁.mem, h.mem]
    rw [m', mu, v₂, CheckEk.sbb_mask, h.edx, Decaps.mask]
    congr 2
    have hl₁ : (bytesAt s.mem (Buf.addr s₀ a) a.len).length = a.len := bytesAt_length _ _ _
    have hl₂ : (bytesAt s.mem (Buf.addr s₀ b) a.len).length = a.len := bytesAt_length _ _ _
    have lt := (Decaps.accB (bytesAt s.mem (Buf.addr s₀ a) a.len) (bytesAt s.mem (Buf.addr s₀ b) a.len) a.len).isLt
    by_cases e : bytesAt s.mem (Buf.addr s₀ a) a.len = bytesAt s.mem (Buf.addr s₀ b) a.len
    · have z := (accB_zero hl₁ hl₂).mp e
      rw [ite_eq_left e, z]; rfl
    · have z : Decaps.accB (bytesAt s.mem (Buf.addr s₀ a) a.len) (bytesAt s.mem (Buf.addr s₀ b) a.len) a.len ≠ 0 :=
        fun z => e ((accB_zero hl₁ hl₂).mpr z)
      rw [ite_eq_right e]
      have : ¬ ((Decaps.accB (bytesAt s.mem (Buf.addr s₀ a) a.len) (bytesAt s.mem (Buf.addr s₀ b) a.len)
          a.len).setWidth 32).toNat < (1 : BitVec 32).toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        intro h'
        exact z (BitVec.eq_of_toNat_eq (by simp at h'; simp [h']))
      simp only [this, decide_false]
      rfl
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.ctx.esi, h'.ctx.esi, hq.sc hp]

end VG.Proof.MlDsa.X86.Verify
