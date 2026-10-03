import VerifiedGarbage.Proof.MlKem.X86.TopSeq
import VerifiedGarbage.Proof.MlKem.KPke

/-!
# ML-KEM on x86 (32-bit): SHA-3 and SHAKE in the top-level functions

The Keccak state set to zero (`zeroTop_piece`), the Keccak calls with their
arguments (`absorbC_piece`, `padC_piece`, `squeezeC_piece`), and a SHA-3 or
SHAKE function of one or two buffers (`hash1_piece`, `hash2_piece`): the
output is `squeezeFrom` of the padded state (`Proof/MlKem/KPke.lean`).
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (Repr bytesAt stateAt squeezeFrom absorb pad rates)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-- A loop of `N ≥ 1` iterations of a block, counting down with `sub ecx, 1`. -/
theorem wp_count {body : List Instr} {N : Nat} (hN : 0 < N) (I : Nat → State → Prop) {s : State}
    (h0 : I 0 s)
    (hs : ∀ k < N, ∀ s, I k s → WP isa (.block body) s fun s' => I (k + 1) s' ∧
      isa.eval .ne s' = some (decide (k + 1 < N))) :
    WP isa (.loop (.block body) .ne) s (I N) := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ k, n = N - k ∧ k < N ∧ I k s)
    (fun n s hi => ?_) N s ⟨0, (Nat.sub_zero N).symm, hN, h0⟩
  obtain ⟨k, hn, hk, hi⟩ := hi
  refine (hs k hk _ hi).mono fun s' ⟨hi', hc⟩ => ?_
  by_cases h : k + 1 < N
  · exact .inr ⟨by rw [hc, decide_eq_true h], N - (k + 1), by omega, k + 1, rfl, h, hi'⟩
  · exact .inl ⟨by rw [hc, decide_eq_false h], by rw [show N = k + 1 by omega]; exact hi'⟩

theorem wp_subi_last {d : Reg} {v : BitVec 32} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d - v → s'.zf = some (s.gpr d - v == 0) → Q s') :
    WP isa (.block [.alu .sub d (.imm v)]) s Q := by
  refine wp_cons (s' := (arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat))
      (subOverflow (s.gpr d) v (s.gpr d - v))).setReg d (s.gpr d - v))
    (by simp only [exec, execAlu, readSrc, Option.bind_some]) (WP.block_nil_iff.mpr ?_)
  exact k _ (Only.flags s d _ _ _) (by simp [State.setReg]) rfl

/-! ## The Keccak state set to zero -/

theorem zeroTop_piece (st : Nat) (hc : Y.okW ⟨Y.sc, st, 200⟩ = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (zeroTop st) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 0]) s.mem s'.mem →
      stateAt s'.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) = Spec.Sha3.zero → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (zeroTop st) := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    have fit : (Buf.ptr s₀ ⟨Y.sc, st, 200⟩).toNat + 200 ≤ 2 ^ 32 := Buf.fit hp hc₁
    refine WP.seq (wp_movr' fun s₁ o₁ v₁ => wp_addi fun s₂ o₂ v₂ => wp_movi fun s₃ o₃ v₃ =>
      wp_movi fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_)
    have o := (((o₁.trans o₂).trans o₃).trans o₄).mono (es := [.edx, .eax, .ecx]) (by simp)
    have c₄ := h.only o (by decide) (by decide)
    let I : Nat → State → Prop := fun k u => Ctx Y s₀ u ∧
      u.gpr .edx = Buf.ptr s₀ ⟨Y.sc, st, 200⟩ + BitVec.ofNat 32 (4 * k) ∧ u.gpr .ecx = BitVec.ofNat 32 (50 - k) ∧
      u.gpr .eax = 0 ∧ Frame [Buf.rgn s₀ ⟨Y.sc, st, 200⟩] s.mem u.mem ∧
      ∀ j < 4 * k, u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩ + BitVec.ofNat 64 j) = 0
    have i0 : I 0 s₄ := ⟨c₄, by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂, v₁, h.esi]; simp,
      v₄, by rw [o₄.gpr _ (by decide), v₃], by rw [o.mem]; exact Frame.refl _ _,
      fun j hj => absurd hj (by omega)⟩
    refine (wp_count (N := 50) (by decide) I i0 fun k hk u hu => ?_).mono fun u hu => ?_
    · obtain ⟨cu, eu, ecu, eau, fu, zu⟩ := hu
      have ea : u.ea (at_ .edx 0) = Buf.addr s₀ ⟨Y.sc, st, 200⟩ + BitVec.ofNat 64 (4 * k) := by
        simp only [State.ea, at_, eu]
        rw [ea_add (by omega)]
        rfl
      have hin : InRegions u.wr (u.ea (at_ .edx 0)) 4 := by
        rw [ea]; exact Buf.inRegW hp hc₁ hc₂ cu.wr (by show 4 * k + 4 ≤ 200; omega)
      obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 4 * k) (n := 4) (by show 4 * k + 4 ≤ 200; omega)
      have cm : Ctx Y s₀ { u with mem := u.mem.writeW (u.ea (at_ .edx 0)) (u.gpr .eax) } :=
        ⟨cu.esp, cu.rd, cu.wr, cu.esi, by rw [ea]; exact cu.frame.writeW hr _ hcr⟩
      refine wp_store hin (wp_addi fun u₁ o₁ v₁ => wp_subi_last fun u₂ o₂ v₂ z₂ => ?_)
      have cm₂ := (cm.only o₁ (by decide) (by decide)).only o₂ (by decide) (by decide)
      have m₂ : u₂.mem = u.mem.writeW (Buf.addr s₀ ⟨Y.sc, st, 200⟩ + BitVec.ofNat 64 (4 * k)) (0 : BitVec 32) := by
        rw [o₂.mem, o₁.mem, ← eau, ← ea]
      have x₂ : u₂.gpr .ecx = BitVec.ofNat 32 (50 - (k + 1)) := by
        rw [v₂, o₁.gpr _ (by decide)]; exact (congrArg (· - 1) ecu).trans (cnt_next hk)
      refine ⟨⟨cm₂, ?_, x₂, by rw [o₂.gpr _ (by decide), o₁.gpr _ (by decide)]; exact eau, ?_, ?_⟩, ?_⟩
      · rw [o₂.gpr _ (by decide), v₁, eu]
        show _ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
        rw [add_ofNat_add, show 4 * (k + 1) = 4 * k + 4 by omega]
      · rw [m₂]
        exact fu.writeW (List.mem_singleton_self _) _ (by
          show (⟨Buf.addr s₀ ⟨Y.sc, st, 200⟩, 200⟩ : Region).Contains _ 4
          simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
      · rw [m₂]; exact Sample.zero_write zu
      · show u₂.zf.map (!·) = _
        have e₁ : u₁.gpr .ecx = BitVec.ofNat 32 (50 - k) := (o₁.gpr _ (by decide)).trans ecu
        rw [z₂, e₁]; exact cnt_ne hk (by decide)
    · obtain ⟨cu, -, -, -, fu, zu⟩ := hu
      exact hQ s₀ s u hp ha cu (fu.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩)
        (Sample.stateAt_zero fun j hj => zu j (by omega))
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

/-! ## The Keccak calls, with their arguments -/

theorem absorbC_piece (st wk rate pos : Nat) (b : Buf) (hr : rate ∈ rates) (hpos : pos < rate)
    (hc : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.ok b && Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩ &&
      Y.sep b ⟨Y.sc, st, 200⟩ && Y.sep b ⟨Y.sc, wk, 640⟩) = true) (hN : 56 ≤ Y.stk) (hlen : b.len < 2 ^ 32)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 pos))] : List Instr) ++
      ptrTo Y.sc .ebx b ++ ([.mov .ebp (.imm (BitVec.ofNat 32 b.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      (∀ msg, Repr s.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate msg → pos = msg.length % rate →
        Repr s'.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate (msg ++ bytesAt s.mem (b.addr s₀) b.len)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (absorbC Y.sc st wk rate pos b) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, -⟩, -⟩, -⟩ := hc'
  refine Piece.seq (setup_piece (fun s₀ s₁ => AbsArgs s₁ (Buf.ptr s₀ ⟨Y.sc, st, 200⟩) (b.ptr s₀)
      (Buf.ptr s₀ ⟨Y.sc, wk, 640⟩) rate pos b.len) (fun s₀ s hp h => ?_) hA tt)
    (absorb_call Y.sc st Y.sc wk b rate pos hr hpos hc hN hlen (fun s₀ s₁ hp ⟨_, _, h₁, _, a₁⟩ => ⟨h₁, a₁⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movi fun s₂ o₂ v₂ => wp_movi fun s₃ o₃ v₃ => ?_
    have c₃ := (c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)
    refine ptrTo_ok hp c₃ h2 fun s₄ o₄ v₄ => ?_
    have c₄ := c₃.only o₄ (by decide) (by decide)
    refine wp_movi fun s₅ o₅ v₅ => ?_
    have c₅ := c₄.only o₅ (by decide) (by decide)
    rw [← List.append_nil (ptrTo Y.sc .edi _)]
    refine ptrTo_ok hp c₅ (Lay.okW_iff.mp h1).1 fun s₆ o₆ v₆ => WP.block_nil_iff.mpr ?_
    refine ⟨c₅.only o₆ (by decide) (by decide),
      o₆.mem.trans (o₅.mem.trans (o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)))), ⟨?_, ?_, ?_, ?_, ?_, v₆⟩⟩
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide),
        o₂.gpr _ (by decide), v₁]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), v₄]
    · rw [o₆.gpr _ (by decide), v₅]
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

theorem padC_piece (st wk rate pos sfx : Nat) (hr : rate ∈ rates) (hpos : pos < rate)
    (hc : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩) = true)
    (hN : 56 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 pos)),
        .mov .ebx (.imm (BitVec.ofNat 32 sfx))] : List Instr) ++ ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      (∀ msg, Repr s.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate msg → pos = msg.length % rate →
        stateAt s'.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) =
          absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8) msg)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (padC Y.sc st wk rate pos sfx) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨h0, h1⟩, -⟩ := hc'
  refine Piece.seq (setup_piece (fun s₀ s₁ => PadArgs s₁ (Buf.ptr s₀ ⟨Y.sc, st, 200⟩)
      (Buf.ptr s₀ ⟨Y.sc, wk, 640⟩) rate pos sfx) (fun s₀ s hp h => ?_) hA tt)
    (pad_call Y.sc st Y.sc wk rate pos sfx hr hpos hc hN (fun s₀ s₁ hp ⟨_, _, h₁, _, a₁⟩ => ⟨h₁, a₁⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movi fun s₂ o₂ v₂ => wp_movi fun s₃ o₃ v₃ => wp_movi fun s₄ o₄ v₄ => ?_
    have c₄ := ((c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)).only o₄ (by decide)
      (by decide)
    rw [← List.append_nil (ptrTo Y.sc .edi _)]
    refine ptrTo_ok hp c₄ (Lay.okW_iff.mp h1).1 fun s₅ o₅ v₅ => WP.block_nil_iff.mpr ?_
    refine ⟨c₄.only o₅ (by decide) (by decide),
      o₅.mem.trans (o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem))), ⟨?_, ?_, ?_, ?_, v₅⟩⟩
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁]
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂]
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃]
    · rw [o₅.gpr _ (by decide), v₄]
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

theorem squeezeC_piece (st wk rate : Nat) (o : Buf) (hr : rate ∈ rates)
    (hc : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.okW o && Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩ &&
      Y.sep ⟨Y.sc, st, 200⟩ o && Y.sep o ⟨Y.sc, wk, 640⟩) = true) (hN : 56 ≤ Y.stk) (hlen : o.len < 2 ^ 32)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm 0)] : List Instr) ++
      ptrTo Y.sc .ebx o ++ ([.mov .ebp (.imm (BitVec.ofNat 32 o.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩, o, ⟨Y.sc, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      bytesAt s'.mem (o.addr s₀) o.len =
        squeezeFrom rate (stateAt s.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩)) 0 o.len → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (squeezeC Y.sc st wk rate o) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, -⟩, -⟩, -⟩ := hc'
  refine Piece.seq (setup_piece (fun s₀ s₁ => AbsArgs s₁ (Buf.ptr s₀ ⟨Y.sc, st, 200⟩) (o.ptr s₀)
      (Buf.ptr s₀ ⟨Y.sc, wk, 640⟩) rate 0 o.len) (fun s₀ s hp h => ?_) hA tt)
    (squeeze_call Y.sc st Y.sc wk o rate 0 hr (Nat.zero_le _) hc hN hlen
      (fun s₀ s₁ hp ⟨_, _, h₁, _, a₁⟩ => ⟨h₁, a₁⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr r₁ _ => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movi fun s₂ o₂ v₂ => wp_movi fun s₃ o₃ v₃ => ?_
    have c₃ := (c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)
    refine ptrTo_ok hp c₃ (Lay.okW_iff.mp h2).1 fun s₄ o₄ v₄ => ?_
    have c₄ := c₃.only o₄ (by decide) (by decide)
    refine wp_movi fun s₅ o₅ v₅ => ?_
    have c₅ := c₄.only o₅ (by decide) (by decide)
    rw [← List.append_nil (ptrTo Y.sc .edi _)]
    refine ptrTo_ok hp c₅ (Lay.okW_iff.mp h1).1 fun s₆ o₆ v₆ => WP.block_nil_iff.mpr ?_
    refine ⟨c₅.only o₆ (by decide) (by decide),
      o₆.mem.trans (o₅.mem.trans (o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)))), ⟨?_, ?_, ?_, ?_, ?_, v₆⟩⟩
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide),
        o₂.gpr _ (by decide), v₁]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃]; rfl
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), v₄]
    · rw [o₆.gpr _ (by decide), v₅]
  · rw [m₁] at fr r₁
    exact hQ s₀ s s' hp ha h' fr r₁

/-! ## Hashes -/

/-- The frame of the Keccak calls: the state, the working space and their stack. -/
abbrev kF (st wk : Nat) (Y : Lay) (s₀ : State) : List Region :=
  [⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]

theorem kF_zero {s₀ : State} (hp : TPre Y s₀) {st wk : Nat} (hN : 56 ≤ Y.stk) {m m' : Mem}
    (fr : Frame ([⟨Y.sc, st, 200⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 0]) m m') : Frame (kF st wk Y s₀) m m' :=
  fr.sub fun r hr => by
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (E1 s₀) 40, by simp, stk_sub hp (by omega) (by omega)⟩

theorem kF_bytes {s₀ : State} (hp : TPre Y s₀) {st wk : Nat} (hN : 56 ≤ Y.stk) {b : Buf} (hb : Y.ok b = true)
    (hs : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.sep b ⟨Y.sc, st, 200⟩ && Y.sep b ⟨Y.sc, wk, 640⟩) = true)
    {m m' : Mem} (fr : Frame (kF st wk Y s₀) m m') : bytesAt m' (b.addr s₀) b.len = bytesAt m (b.addr s₀) b.len := by
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨h₁, h₂⟩, d₁⟩, d₂⟩ := hs
  exact bytesAt_frame fr (Buf.frD hp hb (bs := [⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩])
    (by simp [(Lay.okW_iff.mp h₁).1, (Lay.okW_iff.mp h₂).1, d₁, d₂]) (by omega))
    (by show b.len ≤ 2 ^ 64; have := Buf.fit hp hb; omega)

/-- The SHA-3 or SHAKE function (`rate`, suffix `sfx`) of the bytes of `b₁` and `b₂`, into `o`. -/
theorem hash2_piece (st wk rate sfx : Nat) (b₁ b₂ o : Buf) (hr : rate ∈ rates)
    (hc : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.ok b₁ && Y.ok b₂ && Y.okW o &&
      Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩ && Y.sep b₁ ⟨Y.sc, st, 200⟩ && Y.sep b₁ ⟨Y.sc, wk, 640⟩ &&
      Y.sep b₂ ⟨Y.sc, st, 200⟩ && Y.sep b₂ ⟨Y.sc, wk, 640⟩ && Y.sep ⟨Y.sc, st, 200⟩ o &&
      Y.sep o ⟨Y.sc, wk, 640⟩) = true) (hN : 56 ≤ Y.stk)
    (hl₁ : b₁.len < 2 ^ 32) (hl₂ : b₂.len < 2 ^ 32) (hlo : o.len < 2 ^ 32)
    {h₀ h₁ h₂ h₃ h₄ : Taint.Hint VG.X86.Taint.T}
    (t₀ : (VG.X86.taint.check (τr [.esi]) (zeroTop st) h₀).isSome = true)
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 0))] : List Instr) ++
      ptrTo Y.sc .ebx b₁ ++ ([.mov .ebp (.imm (BitVec.ofNat 32 b₁.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 (b₁.len % rate)))] : List Instr) ++
      ptrTo Y.sc .ebx b₂ ++ ([.mov .ebp (.imm (BitVec.ofNat 32 b₂.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₂).isSome = true)
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 ((b₁.len + b₂.len) % rate))),
        .mov .ebx (.imm (BitVec.ofNat 32 sfx))] : List Instr) ++ ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₃).isSome = true)
    (t₄ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm 0)] : List Instr) ++
      ptrTo Y.sc .ebx o ++ ([.mov .ebp (.imm (BitVec.ofNat 32 o.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₄).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩, o].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      bytesAt s'.mem (o.addr s₀) o.len = squeezeFrom rate (absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8)
        (bytesAt s.mem (b₁.addr s₀) b₁.len ++ bytesAt s.mem (b₂.addr s₀) b₂.len))) 0 o.len → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (hash2 Y.sc st wk rate sfx b₁ b₂ o) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hS, hW⟩, hb₁⟩, hb₂⟩, hO⟩, dSW⟩, d₁S⟩, d₁W⟩, d₂S⟩, d₂W⟩, dSO⟩, dOW⟩ := hc'
  have hrate := (rate_lt hr)
  have hr0 : 0 < rate := by simp [rates] at hr; omega
  -- after zeroing, absorbing `b₁`, absorbing `b₂`, padding
  let P : Nat → State → State → Prop := fun i s₀ u => ∃ s, A s₀ s ∧ Ctx Y s₀ u ∧ Frame (kF st wk Y s₀) s.mem u.mem ∧
    (i = 0 → stateAt u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) = Spec.Sha3.zero) ∧
    (i = 1 → Repr u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate (bytesAt s.mem (b₁.addr s₀) b₁.len)) ∧
    (i = 2 → Repr u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate
      (bytesAt s.mem (b₁.addr s₀) b₁.len ++ bytesAt s.mem (b₂.addr s₀) b₂.len)) ∧
    (i = 3 → stateAt u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) = absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8)
      (bytesAt s.mem (b₁.addr s₀) b₁.len ++ bytesAt s.mem (b₂.addr s₀) b₂.len)))
  have cS : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩) = true := by
    simp [hS, hW, dSW]
  refine Piece.seq (B := P 0) (zeroTop_piece st hS t₀ hA fun s₀ s s' hp ha h' fr z =>
    ⟨s, ha, h', kF_zero hp hN fr, fun _ => z, by simp, by simp, by simp⟩) ?_
  refine Piece.seq (B := P 1) (absorbC_piece st wk rate 0 b₁ hr hr0 (by simp [hS, hW, hb₁, dSW, d₁S, d₁W])
    hN hl₁ t₁ (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, z, _⟩ h' fr post => ?_) ?_
  · have r := post [] (repr_nil (z rfl)) (by simp)
    rw [List.nil_append, kF_bytes hp hN hb₁ (by simp [hS, hW, d₁S, d₁W]) fu] at r
    exact ⟨s, ha, h', fu.trans fr, by simp, fun _ => r, by simp, by simp⟩
  refine Piece.seq (B := P 2) (absorbC_piece st wk rate (b₁.len % rate) b₂ hr (Nat.mod_lt _ hr0)
    (by simp [hS, hW, hb₂, dSW, d₂S, d₂W]) hN hl₂ t₂ (fun s₀ u _ ⟨_, _, h, _⟩ => h)
    fun s₀ u u' hp ⟨s, ha, _, fu, _, r, _⟩ h' fr post => ?_) ?_
  · have r' := post _ (r rfl) (by rw [bytesAt_length])
    rw [kF_bytes hp hN hb₂ (by simp [hS, hW, d₂S, d₂W]) fu] at r'
    exact ⟨s, ha, h', fu.trans fr, by simp, by simp, fun _ => r', by simp⟩
  refine Piece.seq (B := P 3) (padC_piece st wk rate ((b₁.len + b₂.len) % rate) sfx hr (Nat.mod_lt _ hr0) cS hN t₃
    (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, _, _, r, _⟩ h' fr post => ?_) ?_
  · exact ⟨s, ha, h', fu.trans fr, by simp, by simp, by simp,
      fun _ => post _ (r rfl) (by rw [List.length_append, bytesAt_length, bytesAt_length])⟩
  refine squeezeC_piece st wk rate o hr (by simp [hS, hW, hO, dSW, dSO, dOW]) hN hlo t₄
    (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, _, _, _, z⟩ h' fr r₁ => ?_
  rw [z rfl] at r₁
  refine hQ s₀ s u' hp ha h' ((fu.sub fun r hr => ?_).trans (fr.sub fun r hr => ?_)) r₁
  · simp only [kF, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

/-- The SHA-3 or SHAKE function (`rate`, suffix `sfx`) of the bytes of `b`, into `o`. -/
theorem hash1_piece (st wk rate sfx : Nat) (b o : Buf) (hr : rate ∈ rates)
    (hc : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.ok b && Y.okW o &&
      Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩ && Y.sep b ⟨Y.sc, st, 200⟩ && Y.sep b ⟨Y.sc, wk, 640⟩ &&
      Y.sep ⟨Y.sc, st, 200⟩ o && Y.sep o ⟨Y.sc, wk, 640⟩) = true) (hN : 56 ≤ Y.stk)
    (hl : b.len < 2 ^ 32) (hlo : o.len < 2 ^ 32)
    {h₀ h₁ h₃ h₄ : Taint.Hint VG.X86.Taint.T}
    (t₀ : (VG.X86.taint.check (τr [.esi]) (zeroTop st) h₀).isSome = true)
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 0))] : List Instr) ++
      ptrTo Y.sc .ebx b ++ ([.mov .ebp (.imm (BitVec.ofNat 32 b.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₁).isSome = true)
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 (b.len % rate))),
        .mov .ebx (.imm (BitVec.ofNat 32 sfx))] : List Instr) ++ ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₃).isSome = true)
    (t₄ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm 0)] : List Instr) ++
      ptrTo Y.sc .ebx o ++ ([.mov .ebp (.imm (BitVec.ofNat 32 o.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₄).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩, o].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      bytesAt s'.mem (o.addr s₀) o.len = squeezeFrom rate (absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8)
        (bytesAt s.mem (b.addr s₀) b.len))) 0 o.len → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (hash1 Y.sc st wk rate sfx b o) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hS, hW⟩, hb⟩, hO⟩, dSW⟩, dbS⟩, dbW⟩, dSO⟩, dOW⟩ := hc'
  have hr0 : 0 < rate := by simp [rates] at hr; omega
  let P : Nat → State → State → Prop := fun i s₀ u => ∃ s, A s₀ s ∧ Ctx Y s₀ u ∧ Frame (kF st wk Y s₀) s.mem u.mem ∧
    (i = 0 → stateAt u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) = Spec.Sha3.zero) ∧
    (i = 1 → Repr u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate (bytesAt s.mem (b.addr s₀) b.len)) ∧
    (i = 3 → stateAt u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) = absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8)
      (bytesAt s.mem (b.addr s₀) b.len)))
  have cS : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩) = true := by
    simp [hS, hW, dSW]
  refine Piece.seq (B := P 0) (zeroTop_piece st hS t₀ hA fun s₀ s s' hp ha h' fr z =>
    ⟨s, ha, h', kF_zero hp hN fr, fun _ => z, by simp, by simp⟩) ?_
  refine Piece.seq (B := P 1) (absorbC_piece st wk rate 0 b hr hr0 (by simp [hS, hW, hb, dSW, dbS, dbW])
    hN hl t₁ (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, z, _⟩ h' fr post => ?_) ?_
  · have r := post [] (repr_nil (z rfl)) (by simp)
    rw [List.nil_append, kF_bytes hp hN hb (by simp [hS, hW, dbS, dbW]) fu] at r
    exact ⟨s, ha, h', fu.trans fr, by simp, fun _ => r, by simp⟩
  refine Piece.seq (B := P 3) (padC_piece st wk rate (b.len % rate) sfx hr (Nat.mod_lt _ hr0) cS hN t₃
    (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, _, r, _⟩ h' fr post => ?_) ?_
  · exact ⟨s, ha, h', fu.trans fr, by simp, by simp, fun _ => post _ (r rfl) (by rw [bytesAt_length])⟩
  refine squeezeC_piece st wk rate o hr (by simp [hS, hW, hO, dSW, dSO, dOW]) hN hlo t₄
    (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, _, _, z⟩ h' fr r₁ => ?_
  rw [z rfl] at r₁
  refine hQ s₀ s u' hp ha h' ((fu.sub fun r hr => ?_).trans (fr.sub fun r hr => ?_)) r₁
  · simp only [kF, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

end VG.Proof.MlKem.X86.Top
