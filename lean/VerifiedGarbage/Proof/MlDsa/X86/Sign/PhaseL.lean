import VerifiedGarbage.Proof.MlDsa.X86.Sign.PhaseK

/-!
# ML-DSA signing on x86 (32-bit): the rejection sampling loop

Iteration `t` runs the commitment, `SampleInBall`, and the checks if it
succeeded, and ends with `CNT ← CNT - 1` (`iter_piece`). The loop runs `NI`
iterations (`loop_piece`): after `t < NI` of them, iteration `t` is next
(`IT`); after all of them, the last one's outcome is in `OK`, with `c̃`, `z`
and the hint if it succeeded (`Fin`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

/-- The outcome of the last iteration, `u`. -/
structure Fin' (p : Params) (F : PrimsOk P) (u : Nat) (s₀ s : State) : Prop where
  ctx : Ctx (Y p) s₀ s
  run : Run p F u s₀
  ok : scw s₀ s oOK = if (F.ballF p.τ (CTv p s₀ (p.ℓ * u)) && decide (passS p u s₀)) then 1 else 0
  out : F.ballF p.τ (CTv p s₀ (p.ℓ * u)) = true → passS p u s₀ →
    Fam s₀ s.mem (yB p) p.ℓ (Zv p s₀ (p.ℓ * u)) ∧ HF s₀ s.mem p.k (Hv p s₀ (p.ℓ * u)) ∧
      bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = CTv p s₀ (p.ℓ * u)
  none : F.ballF p.τ (CTv p s₀ (p.ℓ * u)) = false → sampleInBall p.τ minBounds.ball (CTv p s₀ (p.ℓ * u)) = none

/-- After `t` iterations. -/
structure LI (p : Params) (F : PrimsOk P) (t : Nat) (s₀ s : State) : Prop where
  good : Good p F s₀
  le : t ≤ NI p F s₀
  it : t < NI p F s₀ → IT p t s₀ s
  fin : t = NI p F s₀ → Fin' p F (NI p F s₀ - 1) s₀ s

/-- A store to the word at `o`, which keeps the flags. -/
theorem wp_stscZ {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {o : Nat} (hc : (Y p).okW (sc o 4) = true)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → (∀ x, s'.gpr x = s.gpr x) → s'.zf = s.zf →
      s'.mem = s.mem.writeW (Buf.addr s₀ (sc o 4)) (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.store (at_ .esi o) r :: is)) s Q := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  have hin : InRegions s.wr (Buf.addr s₀ (sc o 4)) 4 := by
    have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 4) (Nat.le_refl _)
    simpa using this
  refine VG.Proof.MlKem.X86.wp_store (by rw [ea_sc h o 4]; exact hin) ?_
  have c := ctx_write hp h hc (w := 32) (by decide) (s.gpr r)
  refine k _ ?_ (fun _ => rfl) rfl (by rw [ea_sc h o 4])
  rw [ea_sc h o 4]; exact c

theorem ofNat_sub_one {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 32) : BitVec.ofNat 32 x - 1 = BitVec.ofNat 32 (x - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have : (1 : BitVec 32).toNat = 1 := rfl
  rw [this]
  omega

/-- `CNT ← CNT - 1`, which sets `ZF` when the loop ends. -/
theorem tail_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (ED p F t) (fun s₀ s => LI p F (t + 1) s₀ s ∧ isa.eval .ne s = some (decide (t + 1 < NI p F s₀)))
      (.block [.mov .eax (.mem (at_ .esi oCNT)), .alu .sub .eax (.imm 1), .store (at_ .esi oCNT) .eax]) := by
  refine blk_piece (fun _ _ _ h => h.kd.ctx) (fun s₀ s hp h => ?_) rfl
  refine wp_ldsc hp h.kd.ctx (sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => wp_subi fun s₂ o₂ v₂ z₂ => ?_
  have o := o₁.trans o₂
  have c₂ := h.kd.ctx.only o (by simp) (by simp)
  refine wp_stscZ hp c₂ (sc_ok ps (by decide) (by decide)) fun s' c' g' z' m' => WP.block_nil_iff.mpr ?_
  have fr : Frame (FR s₀ [sc oCNT 4] 80) s.mem s'.mem := fr0 hp (by decide) (by
    rw [m', o.mem]; exact frW32 (Y := Y p))
  have hrun := h.run
  have hNI := NI_good hrun.1
  have ht := hrun.2
  have hlt := hrun.lt
  have hnext : t + 1 < NI p F s₀ ↔ contS p F t s₀ = true ∧ t + 1 < 814 := by
    rw [hNI]; exact nIt_next _ (by have := ht; rw [hNI] at this; exact this)
  have hcnt : scw s₀ s' oCNT = scw s₀ s oCNT - 1 := by
    rw [scw, m', Mem.readW_writeW_self32, v₂, v₁]
  have hz : isa.eval .ne s' = some (decide (t + 1 < NI p F s₀)) := by
    show s'.zf.map (!·) = _
    rw [z', z₂, v₁, h.cnt]
    cases e : contS p F t s₀
    · simp only [e, Bool.false_eq_true, false_and, iff_false] at hnext
      rw [decide_eq_false hnext]; simp
    · simp only [e, true_and] at hnext
      simp only [↓reduceIte]
      rw [show decide (t + 1 < NI p F s₀) = decide (t + 1 < 814) from decide_eq_decide.mpr hnext]
      by_cases e' : t + 1 < 814
      · rw [decide_eq_true e']
        rw [ofNat_sub_one (by omega) (by omega)]
        have : (BitVec.ofNat 32 (814 - t - 1) == 0) = false := by
          apply beq_eq_false_iff_ne.mpr
          intro h0
          have := congrArg BitVec.toNat h0
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          exact absurd this (by show ¬ (814 - t - 1 = 0); omega)
        rw [this]; rfl
      · rw [decide_eq_false e', show 814 - t = 1 by omega]; rfl
  refine ⟨⟨hrun.1, ht, fun ht' => ?_, fun ht' => ?_⟩, hz⟩
  · have hc : contS p F t s₀ = true := (hnext.mp ht').1
    refine ⟨h.kd.keep hp ps c' (by decide) fr (by ofs), ?_, ?_, (hnext.mp ht').2⟩
    · rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofs)]; exact h.kap hc
    · rw [hcnt, h.cnt, hc]
      simp only [↓reduceIte]
      rw [ofNat_sub_one (by omega) (by omega), Nat.sub_sub]
  · rw [← ht', Nat.add_sub_cancel]
    refine ⟨c', hrun, ?_, fun hb hq => ?_, h.none⟩
    · rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofs)]; exact h.ok
    · obtain ⟨f1, f2, f3⟩ := h.out hb hq
      have := ps.hcLen
      exact ⟨f1.keep hp ps (by decide) fr (by simp only [nS, yB]; omega) (by ofs),
        f2.keep hp ps (by decide) fr (by simp only [nS]; omega) (by ofs),
        by rw [keepB hp (by decide) fr (by ofs) (by ofs), f3]⟩

/-- `OK ← 0` and `CNT ← 1`, when `SampleInBall` failed. -/
theorem ballFail_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (fun s₀ s => (∃ s', IB p F t s₀ s' ∧ Ctx (Y p) s₀ s ∧ s.mem = s'.mem ∧ s.zf = some (!ballB p F t s₀)) ∧
      ballB p F t s₀ = false) (ED p F t) (.block (st32 oOK 0 ++ st32 oCNT 1)) := by
  refine blk_piece (fun _ _ _ h => h.1.choose_spec.2.1) (fun s₀ s hp h => ?_) rfl
  obtain ⟨⟨s', ib, c, m, _⟩, hb⟩ := h
  have hf : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = false := by rw [← ballB_of ib.run]; exact hb
  have kd := ib.cc.cw.cm.it.kd.keep hp ps c (N := 0) (bs := []) (by decide) (by rw [m]; exact Frame.refl _ _)
    (by simp)
  refine wp_st32 hp c (sc_ok ps (by decide) (by decide)) 0 fun s₁ c₁ f₁ v₁ => ?_
  rw [← List.append_nil (st32 oCNT 1)]
  refine wp_st32 hp c₁ (sc_ok ps (by decide) (by decide)) 1 fun s₂ c₂ f₂ v₂ => WP.block_nil_iff.mpr ?_
  have kd₁ := kd.keep hp ps c₁ (N := 80) (by decide) (fr0 hp (by decide) f₁) (by ofs)
  have hc : contS p F t s₀ = false := by simp only [contS, contV, hf, Bool.false_and]
  refine ⟨kd₁.keep hp ps c₂ (N := 80) (by decide) (fr0 hp (by decide) f₂) (by ofs), ib.run, by rw [hc, v₂]; rfl,
    (fun e => by rw [hc] at e; cases e), ?_, (fun e => by rw [hf] at e; cases e), fun _ => ib.no hf⟩
  rw [scw, keepW' hp (N := 80) (by decide) (fr0 hp (by decide) f₂) (sc_ok' ps (by decide) (by decide)) (by ofs), ← scw,
    v₁, hf, Bool.false_and]; rfl

/-- Iteration `t`. -/
theorem iter_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (fun s₀ s => LI p F t s₀ s ∧ t < NI p F s₀)
      (fun s₀ s => LI p F (t + 1) s₀ s ∧ isa.eval .ne s = some (decide (t + 1 < NI p F s₀))) (iter P p) := by
  unfold iter
  refine Piece.seq (B := fun s₀ s => CC p t s₀ s ∧ Run p F t s₀)
    ((sp_pure (Run p F t) (commit_piece F ps t)).mono (fun s₀ s _ h =>
      ⟨⟨h.1.it h.2, fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _)⟩,
        h.1.good, h.2⟩) fun _ _ _ h => h) ?_
  refine Piece.seq (ballCall_piece F ps t) ?_
  refine Piece.seq (ballTest_piece F t) ?_
  refine Piece.seq (Piece.ite (ballB p F t) (fun s₀ s _ h => ?_) (fun s₀ s₀' _ _ hq => ballB_eq ps hq)
    ((checks_piece F ps t).mono (fun s₀ s hp h => ?_) fun _ _ _ h => h) (ballFail_piece F ps t)) (tail_piece F ps t)
  · show s.zf.map (!·) = _
    rw [h.choose_spec.2.2.2]; cases ballB p F t s₀ <;> rfl
  · obtain ⟨⟨s', ib, c, m, _⟩, hb⟩ := h
    have hs : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true := by rw [← ballB_of ib.run]; exact hb
    exact ⟨⟨ib.cc.ofMem hp ps c m, ib.run, hs⟩, by rw [m]; exact ib.yes hs⟩

/-- `κ ← 0`, `CNT ← 814`, and the loop. -/
theorem signLoop_piece (F : PrimsOk P) (ps : PS p) :
    SP p (fun s₀ s => KD p s₀ s ∧ Good p F s₀) (fun s₀ s => Fin' p F (NI p F s₀ - 1) s₀ s) (Impl.MlDsa.X86.Sign.signLoop P p) := by
  unfold Impl.MlDsa.X86.Sign.signLoop
  refine Piece.seq (B := LI p F 0) ?_ ((loopN (NI p F) (LI p F) (fun s₀ _ => NI_pos (p := p) F s₀)
    (fun s₀ s₀' _ _ hq => NI_eq ps hq) fun t => iter_piece F ps t).mono (fun _ _ _ h => h)
      fun s₀ s _ h => h.fin rfl)
  refine blk_piece (fun _ _ _ h => h.1.ctx) (fun s₀ s hp h => ?_) rfl
  refine wp_st32 hp h.1.ctx (sc_ok ps (by decide) (by decide)) 0 fun s₁ c₁ f₁ v₁ => ?_
  rw [← List.append_nil (st32 oCNT 814)]
  refine wp_st32 hp c₁ (sc_ok ps (by decide) (by decide)) 814 fun s₂ c₂ f₂ v₂ => WP.block_nil_iff.mpr ?_
  have kd₁ := h.1.keep hp ps c₁ (N := 80) (by decide) (fr0 hp (by decide) f₁) (by ofs)
  have hpos := NI_pos (p := p) F s₀
  refine ⟨h.2, Nat.zero_le _, fun _ => ⟨kd₁.keep hp ps c₂ (N := 80) (by decide) (fr0 hp (by decide) f₂) (by ofs),
    ?_, v₂, by decide⟩, fun e => absurd e (by omega)⟩
  rw [scw, keepW' hp (N := 80) (by decide) (fr0 hp (by decide) f₂) (sc_ok' ps (by decide) (by decide)) (by ofs), ← scw,
    v₁]; rfl

end VG.Proof.MlDsa.X86.Sign
