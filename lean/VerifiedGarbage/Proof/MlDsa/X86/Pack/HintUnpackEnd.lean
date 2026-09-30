import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintUnpackMain

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_hint_bit_unpack`, the end

Untrusted: everything here is checked by Lean. After the polynomials, the
bytes from the index up to `ω` must be zero (`trail_piece`; the spec's
`huTrail`): the index ends at `ω`, or 256 if a check failed (`fin`); the
return value is 1 iff it is at most `ω` (`ret_piece`). Then the whole
function (`piece`) and its contract (`hintBitUnpack_verified`).
-/

namespace VG.Proof.MlDsa.X86.Pack.Hint

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Impl.MlKem.X86 (at_ saveRegs)
open VG.Proof.MlKem.X86
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

namespace Up

/-- The spec's state after the polynomials, if no check failed. -/
def cK (s₀ : State) : Array (Vector Bool n) × Nat := (PS s₀ (K s₀)).getD (#[], 0)

/-- Its index. -/
abbrev i₀ (s₀ : State) : Nat := (cK s₀).2

/-- The checks of the first `k` bytes from the index. -/
def TF (s₀ : State) (k : Nat) : Option Unit := optFold (huTrail (Y s₀)) (List.range' (i₀ s₀) k) ()

/-- The result of the spec: the hint, if no check fails. -/
def TS (s₀ : State) : Option (Array (Vector Bool n) × Nat) :=
  (PS s₀ (K s₀)).bind fun st => (optFold (huTrail (Y s₀)) (List.range' st.2 (ω s₀ - st.2)) ()).map fun _ => st

/-- The index at the end: `ω`, or 256 if a check failed. -/
def fin (s₀ : State) : Nat := match TS s₀ with
  | none => 256
  | some _ => ω s₀

/-- The index after byte `k`: 256 if it is not zero. -/
def tr (s₀ : State) (k : Nat) : Nat := if (Y s₀).getD (i₀ s₀ + k) 0 ≠ 0 then 256 else i₀ s₀ + k + 1

theorem Pub.ecK {s₀ s₀' : State} (h : Pub s₀ s₀') : cK s₀ = cK s₀' := by
  unfold cK; rw [h.ePS, h.eK]

theorem Pub.etr {s₀ s₀' : State} (h : Pub s₀ s₀') (k : Nat) : tr s₀ k = tr s₀' k := by
  unfold tr; simp only [i₀, h.ecK, h.y]

theorem Pub.efin {s₀ s₀' : State} (h : Pub s₀ s₀') : fin s₀ = fin s₀' := by
  unfold fin TS; rw [h.eK, h.ePS, h.y, h.eω]

/-- What the end keeps. -/
structure TB (s₀ s : State) : Prop extends Base s₀ s where
  edi : s.gpr .edi = arg s₀ 0
  sr : SR s₀ (PS s₀ (K s₀)) s.mem

theorem TB.keep {s₀ s s' : State} (h : TB s₀ s) {rs : List Reg} (k : Keep rs s s') (hrs : Reg.esp ∉ rs)
    (hdi : Reg.edi ∉ rs) (hm : s'.mem = s.mem) : TB s₀ s' :=
  ⟨h.toBase.keep k hrs (by rw [hm]; exact Frame.refl _ _), by rw [k.gpr hdi, h.edi], by rw [hm]; exact h.sr⟩

/-- Before byte `k` from the index. -/
def TI (k : Nat) (s₀ s : State) : Prop :=
  TB s₀ s ∧ s.gpr .eax = BitVec.ofNat 32 (i₀ s₀ + k) ∧ PS s₀ (K s₀) = some (cK s₀) ∧ i₀ s₀ + k < ω s₀ ∧
    TF s₀ k = some ()

/-- After byte `k`, before the comparison. -/
def TM (k : Nat) (s₀ s : State) : Prop :=
  TB s₀ s ∧ s.gpr .eax = BitVec.ofNat 32 (tr s₀ k) ∧ PS s₀ (K s₀) = some (cK s₀) ∧ i₀ s₀ + k < ω s₀ ∧
    TF s₀ k = some ()

/-- At the end. -/
def TFin (s₀ s : State) : Prop := TB s₀ s ∧ s.gpr .eax = BitVec.ofNat 32 (fin s₀)

theorem sr_le {s₀ : State} {m : Mem} (h : SR s₀ (PS s₀ (K s₀)) m) (e : PS s₀ (K s₀) = some (cK s₀)) :
    i₀ s₀ ≤ ω s₀ := (h _ e).1

theorem TS_some {s₀ : State} (e : PS s₀ (K s₀) = some (cK s₀)) (ht : TF s₀ (ω s₀ - i₀ s₀) = some ()) :
    fin s₀ = ω s₀ := by
  unfold fin TS; rw [e, Option.bind_some]
  unfold TF at ht
  rw [ht]; rfl

theorem TS_none {s₀ : State} (e : PS s₀ (K s₀) = some (cK s₀)) (ht : TF s₀ (ω s₀ - i₀ s₀) = none) :
    fin s₀ = 256 := by
  unfold fin TS; rw [e, Option.bind_some]
  unfold TF at ht
  rw [ht]; rfl

/-! ## The trailing bytes -/

theorem t0_piece : Piece Pre Pub (fun s₀ s => OM s₀ (K s₀) (PS s₀ (K s₀)) s)
    (fun s₀ s => (TB s₀ s ∧ s.gpr .eax = BitVec.ofNat 32 (idxOf (PS s₀ (K s₀)))) ∧
      isa.eval .b s = some (decide (idxOf (PS s₀ (K s₀)) < ω s₀)))
    (.block [.alu .cmp .eax (.mem (at_ .esp 28))]) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := argEa h.esp 2
    have i2 := h.argIn hp (i := 2) (by omega)
    have v2 := h.argw hp (i := 2) (by omega) (by omega) (by omega)
    have hb : WP isa (.block [.alu .cmp .eax (.mem (at_ .esp 28))]) s fun s' =>
        s'.cf = some (decide ((s.gpr .eax).toNat < (arg s₀ 2).toNat)) ∧ s'.gpr .eax = s.gpr .eax ∧
          s'.mem = s.mem := by
      hrun [a2, i2, v2]
    have hl := idxOf_le hp h.sr
    refine (WP.keep [.eax] hb (by decide)).mono fun s' ⟨⟨c, ea, m⟩, k'⟩ => ?_
    have k := k'.drop ea
    refine ⟨⟨⟨h.toBase.keep k (by simp) (by rw [m]; exact Frame.refl _ _), by rw [k.gpr (by simp), h.edi],
      by rw [m]; exact h.sr⟩, by rw [ea, h.eax]⟩, ?_⟩
    show s'.cf = _
    rw [c, h.eax, toNat_ofNat32 (by omega)]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

theorem ne_zero_byte (b : Byte) : (!(BitVec.setWidth 32 b - 0 == 0)) = decide (b ≠ 0) := by
  rw [sub_zero', byte32]
  by_cases hb : b = 0
  · subst hb; rfl
  · have : b.toNat ≠ 0 := fun h => hb (BitVec.eq_of_toNat_eq h)
    rw [ofNat_beq_zero (by have := b.isLt; omega)]
    simpa [this] using hb

theorem load_piece (k : Nat) : Piece Pre Pub (TI k)
    (fun s₀ s => TI k s₀ s ∧ isa.eval .ne s = some (decide ((Y s₀).getD (i₀ s₀ + k) 0 ≠ 0)))
    (.block hbuTrailLoad) := by
  refine Piece.taint [.edi, .eax] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by taint_decide)
  · obtain ⟨hb, hax, e, hl, ht⟩ := h
    have hf := hp.facts
    have hy : i₀ s₀ + k < yL s₀ := by omega
    have ea : addr (s.gpr .edi + s.gpr .eax) 0 = rA s₀ + BitVec.ofNat 64 (i₀ s₀ + k) := by
      rw [hb.edi, hax]; exact yAddr hp hy
    have hin := hb.inY hp hy
    have hv := hb.ybyte hp hy
    have hbk : WP isa (.block hbuTrailLoad) s fun s' =>
        s'.zf = some (BitVec.setWidth 32 ((Y s₀).getD (i₀ s₀ + k) 0) - 0 == 0) ∧ s'.mem = s.mem := by
      hrun [hbuTrailLoad, ea, hin, hv]
    refine (WP.keep [.edx] hbk (by decide)).mono fun s' ⟨⟨z, m⟩, k'⟩ =>
      ⟨⟨hb.keep k' (by simp) (by simp) m, by rw [k'.gpr (by simp), hax], e, hl, ht⟩, ?_⟩
    show s'.zf.map (!·) = _
    rw [z, Option.map_some, ne_zero_byte]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.1.edi, h'.1.edi, hq.a0]
    · rw [h.2.1, h'.2.1]; simp only [i₀, hq.ecK]

theorem tfail_piece (k : Nat) : Piece Pre Pub
    (fun s₀ s => (TI k s₀ s ∧ isa.eval .ne s = some (decide ((Y s₀).getD (i₀ s₀ + k) 0 ≠ 0))) ∧
      decide ((Y s₀).getD (i₀ s₀ + k) 0 ≠ 0) = true) (TM k) hbuFail := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨⟨hb, _, e, hl, ht⟩, _⟩, hc⟩ => ?_)
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
  have hbk : WP isa hbuFail s fun s' => s'.gpr .eax = 256 ∧ s'.mem = s.mem := by hrun [hbuFail]
  exact (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨e1, m⟩, k'⟩ =>
    ⟨hb.keep k' (by simp) (by simp) m, by rw [e1, tr, ite_pos' (of_decide_eq_true hc)]; rfl, e, hl, ht⟩

theorem tinc_piece (k : Nat) : Piece Pre Pub
    (fun s₀ s => (TI k s₀ s ∧ isa.eval .ne s = some (decide ((Y s₀).getD (i₀ s₀ + k) 0 ≠ 0))) ∧
      decide ((Y s₀).getD (i₀ s₀ + k) 0 ≠ 0) = false) (TM k) (.block [.alu .add .eax (.imm 1)]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨⟨hb, hax, e, hl, ht⟩, _⟩, hc⟩ => ?_)
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
  have hbk : WP isa (.block [.alu .add .eax (.imm 1)]) s fun s' => s'.gpr .eax = s.gpr .eax + 1 ∧
      s'.mem = s.mem := by hrun
  exact (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨e1, m⟩, k'⟩ =>
    ⟨hb.keep k' (by simp) (by simp) m, by rw [e1, hax, tr, ite_neg' (of_decide_eq_false hc), ofNat_add_one],
      e, hl, ht⟩

/-- `cmp eax, ω`, after byte `k`. -/
theorem tcmp_piece (k : Nat) : Piece Pre Pub (TM k)
    (fun s₀ s => isa.eval .b s = some (decide (tr s₀ k < ω s₀)) ∧ (decide (tr s₀ k < ω s₀) = true → TI (k + 1) s₀ s) ∧
      (decide (tr s₀ k < ω s₀) = false → TFin s₀ s))
    (.block [.alu .cmp .eax (.mem (at_ .esp 28))]) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · obtain ⟨hb, hax, e, hl, ht⟩ := h
    have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := argEa hb.esp 2
    have i2 := hb.argIn hp (i := 2) (by omega)
    have v2 := hb.argw hp (i := 2) (by omega) (by omega) (by omega)
    have hbk : WP isa (.block [.alu .cmp .eax (.mem (at_ .esp 28))]) s fun s' =>
        s'.cf = some (decide ((s.gpr .eax).toNat < (arg s₀ 2).toNat)) ∧ s'.gpr .eax = s.gpr .eax ∧
          s'.mem = s.mem := by
      hrun [a2, i2, v2]
    have hf := hp.facts
    have htr : tr s₀ k ≤ 256 := by unfold tr; split <;> omega
    refine (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨c, ea, m⟩, k'⟩ => ?_
    have kk := k'.drop ea
    have hb' := hb.keep kk (by simp) (by simp) m
    have hax' : s'.gpr .eax = BitVec.ofNat 32 (tr s₀ k) := by rw [ea, hax]
    refine ⟨?_, fun hc => ?_, fun hc => ?_⟩
    · show s'.cf = _
      rw [c, hax, toNat_ofNat32 (by omega)]
    · -- The byte is zero, and the index still below `ω`.
      have hc := of_decide_eq_true hc
      have hz : ¬ (Y s₀).getD (i₀ s₀ + k) 0 ≠ 0 := fun h => by rw [tr, ite_pos' h] at hc; omega
      have htk : tr s₀ k = i₀ s₀ + k + 1 := by rw [tr, ite_neg' hz]
      refine ⟨hb', by rw [hax', htk]; rfl, e, by omega, ?_⟩
      unfold TF at ht ⊢
      rw [optFold_range'_succ, ht, Option.bind_some]
      exact ite_neg' hz _ _
    · have hc := of_decide_eq_false hc
      refine ⟨hb', ?_⟩
      rw [hax']
      by_cases hz : (Y s₀).getD (i₀ s₀ + k) 0 ≠ 0
      · rw [tr, ite_pos' hz, TS_none e]
        have h1 : TF s₀ (k + 1) = none := by
          unfold TF at ht ⊢
          rw [optFold_range'_succ, ht, Option.bind_some]
          exact ite_pos' hz _ _
        unfold TF at h1 ⊢
        exact optFold_range'_none _ _ (show k + 1 ≤ ω s₀ - i₀ s₀ by omega) h1
      · have htk : tr s₀ k = i₀ s₀ + k + 1 := by rw [tr, ite_neg' hz]
        rw [htk] at hc ⊢
        rw [TS_some e, show i₀ s₀ + k + 1 = ω s₀ by omega]
        rw [show ω s₀ - i₀ s₀ = k + 1 by omega]
        unfold TF at ht ⊢
        rw [optFold_range'_succ, ht, Option.bind_some]
        exact ite_neg' hz _ _
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.1.esp, h'.1.esp, P0_esp, P0_esp, hq.e0]

theorem tloop_piece : Piece Pre Pub (TI 0) TFin (.loop (.seq (.block hbuTrailLoad)
    (.seq (.ite .ne hbuFail (.block [.alu .add .eax (.imm 1)])) (.block [.alu .cmp .eax (.mem (at_ .esp 28))]))) .b) :=
  loopC TI TFin (fun s₀ => ω s₀ - i₀ s₀) (fun k s₀ => decide (tr s₀ k < ω s₀))
    (fun k s₀ hp hc => by
      have hf := hp.facts
      have hc := of_decide_eq_true hc
      show k + 1 < ω s₀ - i₀ s₀
      unfold tr at hc
      split at hc <;> omega)
    (fun k s₀ s₀' _ _ hq => by rw [hq.etr, hq.eω])
    fun k => Piece.seq (load_piece k) (Piece.seq (Piece.ite
      (fun s₀ => decide ((Y s₀).getD (i₀ s₀ + k) 0 ≠ 0)) (fun _ _ _ h => h.2)
      (fun s₀ s₀' _ _ hq => by simp only [i₀, hq.ecK, hq.y]) (tfail_piece k) (tinc_piece k)) (tcmp_piece k))

theorem trail_piece : Piece Pre Pub (fun s₀ s => OM s₀ (K s₀) (PS s₀ (K s₀)) s) TFin hbuTrail := by
  refine Piece.seq t0_piece (Piece.ite (fun s₀ => decide (idxOf (PS s₀ (K s₀)) < ω s₀)) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.ePS, hq.eK, hq.eω]) ?_ ?_)
  · refine tloop_piece.mono (fun s₀ s hp ⟨⟨⟨hb, hax⟩, _⟩, hc⟩ => ?_) fun _ _ _ h => h
    have hc := of_decide_eq_true hc
    have hf := hp.facts
    cases e : PS s₀ (K s₀) with
    | none => rw [e] at hc; simp only [idxOf] at hc; omega
    | some st =>
      have ec : cK s₀ = st := by unfold cK; rw [e]; rfl
      rw [e] at hc hax
      refine ⟨hb, by rw [hax, Nat.add_zero]; simp only [idxOf, i₀, ec], by rw [ec]; exact e, ?_, rfl⟩
      simp only [idxOf] at hc
      simp only [i₀, ec]; omega
  · refine nil_piece fun s₀ s hp ⟨⟨⟨hb, hax⟩, _⟩, hc⟩ => ⟨hb, ?_⟩
    have hc := of_decide_eq_false hc
    rw [hax]
    cases e : PS s₀ (K s₀) with
    | none => unfold fin TS; rw [e]; rfl
    | some st =>
      have ec : cK s₀ = st := by unfold cK; rw [e]; rfl
      have hle := (hb.sr st e).1
      rw [e] at hc
      simp only [idxOf] at hc ⊢
      rw [TS_some (by rw [e, ec]) (by rw [show ω s₀ - i₀ s₀ = 0 by simp only [i₀, ec]; omega]; rfl)]
      congr 1; omega

/-! ## The return value -/

/-- 1 if no check failed. -/
def res (s₀ : State) : BitVec 32 := match TS s₀ with
  | none => 0
  | some _ => 1

theorem ret_piece : Piece Pre Pub TFin (fun s₀ s => TB s₀ s ∧ s.gpr .eax = res s₀) (.block hbuRet) := by
  refine Piece.taint [.esp] (fun s₀ s hp ⟨hb, hax⟩ => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := argEa hb.esp 2
    have i2 := hb.argIn hp (i := 2) (by omega)
    have v2 := hb.argw hp (i := 2) (by omega) (by omega) (by omega)
    have hbk : WP isa (.block hbuRet) s fun s' =>
        s'.gpr .eax = 1 - 0 - (BitVec.ofBool (decide ((arg s₀ 2).toNat < (s.gpr .eax).toNat))).setWidth 32 ∧
          s'.mem = s.mem := by
      hrun [hbuRet, a2, i2, v2]
    have hf := hp.facts
    refine (WP.keep [.edx, .eax] hbk (by decide)).mono fun s' ⟨⟨e, m⟩, k⟩ =>
      ⟨hb.keep k (by simp) (by simp) m, ?_⟩
    rw [e, hax]
    cases hT : TS s₀ with
    | none =>
      have e1 : fin s₀ = 256 := by unfold fin; rw [hT]
      have e2 : res s₀ = 0 := by unfold res; rw [hT]
      rw [e1, e2, toNat_ofNat32 (by omega), decide_eq_true (show (arg s₀ 2).toNat < 256 by simp only [ω] at hf; omega)]
      rfl
    | some _ =>
      have e1 : fin s₀ = ω s₀ := by unfold fin; rw [hT]
      have e2 : res s₀ = 1 := by unfold res; rw [hT]
      rw [e1, e2, toNat_ofNat32 (by omega), decide_eq_false (Nat.lt_irrefl _)]
      rfl
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.1.esp, h'.1.esp, P0_esp, P0_esp, hq.e0]

/-! ## The function -/

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀)
    (fun s₀ s => LeafEnd s₀ (W s₀) s ∧ TB s₀ s ∧ s.gpr .eax = res s₀)
    (.seq (.block hbuZeroInit) (.seq (.loop (.block hbuZeroBody) .ne)
      (.seq (.block hbuSetup) (.seq (.loop (.seq hbuPoly (.block hbuPolyEnd)) .ne) (.seq hbuTrail (.block hbuRet)))))) :=
  (Piece.seq zinit_piece <| Piece.seq zloop_piece <| Piece.seq setup_piece <| Piece.seq polys_piece <|
    Piece.seq trail_piece ret_piece).mono (fun _ _ _ h => h)
    fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h⟩

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀)
    (fun s₀ s' => LeafPost (fun s => TB s₀ s ∧ s.gpr .eax = res s₀) s₀ s') Impl.MlDsa.X86.Pack.hintBitUnpack :=
  Piece.leaf W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp => hp.hW) (fun _ _ _ _ hq => hq.e0) body_piece

/-- The spec, as the result. -/
theorem hintBitUnpack_TS (s₀ : State) :
    hintBitUnpack (ω s₀) (K s₀) (bytesAt s₀.mem (rA s₀) (yL s₀)) = (TS s₀).map (·.1.toList) := by
  rw [hintBitUnpack_eq]
  change (match PS s₀ (K s₀) with
    | none => none
    | some (h, idx) => Option.map (fun _ => h.toList) (optFold (huTrail (Y s₀)) (List.range' idx (ω s₀ - idx)) ())) = _
  unfold TS
  cases PS s₀ (K s₀) with
  | none => rfl
  | some st =>
    obtain ⟨hA, idx⟩ := st
    simp only [Option.bind_some]
    cases optFold (huTrail (Y s₀)) (List.range' idx (ω s₀ - idx)) () <;> rfl

theorem TS_PS {s₀ : State} {st : Array (Vector Bool n) × Nat} (h : TS s₀ = some st) : PS s₀ (K s₀) = some st := by
  unfold TS at h
  cases e : PS s₀ (K s₀) with
  | none => rw [e] at h; cases h
  | some st' =>
    rw [e, Option.bind_some] at h
    cases e' : optFold (huTrail (Y s₀)) (List.range' st'.2 (ω s₀ - st'.2)) () with
    | none => rw [e'] at h; cases h
    | some _ => rw [e'] at h; cases h; rfl

end Up

/-- Memory with the arguments `0`, `84`, `80`, `0x1000` and `1024` at `0x5004`. -/
def unpackSatMem : Mem := fun a =>
  if a = 0x5008 then 84 else if a = 0x500c then 80 else if a = 0x5011 then 0x10 else if a = 0x5015 then 4 else 0

theorem hintBitUnpack_verified :
    Verified X86.target Impl.MlDsa.X86.Pack.hintBitUnpack (hintBitUnpackContract X86.abi 16) := by
  refine Piece.verified ((Up.piece.pre_mono (fun _ h => Up.Pre.of h)
    fun _ _ _ _ hq => Up.Pub.of hq).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, ⟨hb, hax⟩, hm, hax'⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [hintBitUnpackContract, hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax', hax, hm]
    show match hintBitUnpack (ω s₀) (Up.K s₀) (bytesAt s₀.mem (rA s₀) (Up.yL s₀)) with
      | some hint => Up.res s₀ = 1 ∧ HintIs s.mem (wA s₀) (Up.K s₀) hint
      | none => Up.res s₀ = 0
    rw [Up.hintBitUnpack_TS]
    unfold Up.res
    cases e : Up.TS s₀ with
    | none => rfl
    | some st => exact ⟨rfl, harr_hintIs (hb.sr st (Up.TS_PS e)).2⟩
  · refine ⟨satState unpackSatMem [⟨0, 84⟩] [⟨0x1000, 4096⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_sat_check [hintBitUnpackContract, hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

end VG.Proof.MlDsa.X86.Pack.Hint
