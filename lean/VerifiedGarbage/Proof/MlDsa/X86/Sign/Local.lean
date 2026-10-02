import VerifiedGarbage.Proof.MlDsa.X86.Sign.Call

/-!
# ML-DSA signing on x86 (32-bit): copies and hashes

A copy of words (`copy_piece`), and SHAKE256 of two buffers (`shake2_piece`),
as ML-KEM's `copyW_piece` and `hash2_piece`, but with the moves of their
arguments proven constant time by `esOk` rather than the taint analysis, so
that their buffers may be at offsets that depend on the parameter set.
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_ callWith callRet copyW zeroTop absorbC padC squeezeC hash2)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (Repr bytesAt stateAt squeezeFrom absorb pad rates)

variable {p : Params} {A B : State → State → Prop}

theorem ptrTo_esOk {r : Reg} (h₁ : r ≠ .esp) (h₂ : r ≠ .esi) (b : Buf) : (ptrTo SC r b).all esOk = true :=
  Arg.mov_esOk h₁ h₂ (.buf b)

/-- A block that moves arguments into registers, from `Ctx`. -/
theorem setup_es {is : List Instr} (P : State → State → Prop)
    (hw : ∀ s₀ s, TPre (Y p) s₀ → Ctx (Y p) s₀ s → WP isa (.block is) s fun s₁ => Ctx (Y p) s₀ s₁ ∧ s₁.mem = s.mem ∧ P s₀ s₁)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s) (h : is.all esOk = true) :
    SP p A (fun s₀ s₁ => ∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ s₁.mem = s.mem ∧ P s₀ s₁) (.block is) :=
  blk_piece hA (fun s₀ s hp ha => (hw s₀ s hp (hA s₀ s hp ha)).mono fun _ h₁ => ⟨s, ha, h₁⟩) h

theorem copy_piece (sa so da dO n : Nat) (hn : 0 < n) (hn' : n < 2 ^ 30)
    (hc : ((Y p).ok ⟨sa, so, 4 * n⟩ && (Y p).okW ⟨da, dO, 4 * n⟩ && (Y p).sep ⟨sa, so, 4 * n⟩ ⟨da, dO, 4 * n⟩) = true)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' →
      Frame [Buf.rgn s₀ ⟨da, dO, 4 * n⟩] s.mem s'.mem →
      bytesAt s'.mem (Buf.addr s₀ ⟨da, dO, 4 * n⟩) (4 * n) = bytesAt s.mem (Buf.addr s₀ ⟨sa, so, 4 * n⟩) (4 * n) →
      B s₀ s') :
    SP p A B (copyW SC ⟨sa, so, 4 * n⟩ ⟨da, dO, 4 * n⟩ n) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨hS, hD⟩, dSD⟩ := hc'
  have hD₁ := (Lay.okW_iff.mp hD).1
  let S : Buf := ⟨sa, so, 4 * n⟩
  let D : Buf := ⟨da, dO, 4 * n⟩
  refine Piece.seq (setup_es (fun s₀ s₁ => s₁.gpr .edi = S.ptr s₀ ∧ s₁.gpr .ebp = D.ptr s₀ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n) (fun s₀ s hp h => ?_) hA
      (by simp only [List.all_append, ptrTo_esOk (r := .edi) (by decide) (by decide),
        ptrTo_esOk (r := .ebp) (by decide) (by decide)]; rfl)) ?_
  · simp only [List.append_assoc]
    refine ptrTo_ok hp h hS fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine ptrTo_ok hp c₁ hD₁ fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine wp_movi fun s₃ o₃ v₃ => WP.block_nil_iff.mpr ?_
    exact ⟨c₂.only o₃ (by decide) (by decide), o₃.mem.trans (o₂.mem.trans o₁.mem),
      by rw [o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁], by rw [o₃.gpr _ (by decide), v₂], v₃⟩
  refine Piece.taint [.edi, .ebp, .ecx] (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂, e₃⟩ => ?_)
    (fun s₀ s₀' s s' hp hp' hq ⟨_, _, _, _, e₁, e₂, e₃⟩ ⟨_, _, _, _, e₁', e₂', e₃'⟩ r hr => ?_) (by taint_decide)
  · have fS : (S.ptr s₀).toNat + 4 * n ≤ 2 ^ 32 := Buf.fit hp hS
    have fD : (D.ptr s₀).toNat + 4 * n ≤ 2 ^ 32 := Buf.fit hp hD₁
    have dd := Buf.disj hp hS hD₁ dSD
    let I : Nat → State → Prop := fun k u => Ctx (Y p) s₀ u ∧ u.gpr .edi = S.ptr s₀ + BitVec.ofNat 32 (4 * k) ∧
      u.gpr .ebp = D.ptr s₀ + BitVec.ofNat 32 (4 * k) ∧ u.gpr .ecx = BitVec.ofNat 32 (n - k) ∧
      Frame [D.rgn s₀] s.mem u.mem ∧ ∀ j < 4 * k, u.mem (D.addr s₀ + BitVec.ofNat 64 j) = s.mem (S.addr s₀ + BitVec.ofNat 64 j)
    have i0 : I 0 s₁ := ⟨h₁, by rw [e₁]; simp, by rw [e₂]; simp, e₃, by rw [m₁]; exact Frame.refl _ _,
      fun j hj => absurd hj (by omega)⟩
    refine (wp_count hn I i0 fun k hk u ⟨cu, du, bu, xu, fu, cpu⟩ => ?_).mono fun u ⟨cu, _, _, _, fu, cpu⟩ => ?_
    · have eS : u.ea (at_ .edi 0) = S.addr s₀ + BitVec.ofNat 64 (4 * k) := by
        simp only [State.ea, at_, du]; rw [ea_add (by omega)]; rfl
      have eD : u.ea (at_ .ebp 0) = D.addr s₀ + BitVec.ofNat 64 (4 * k) := by
        simp only [State.ea, at_, bu]; rw [ea_add (by omega)]; rfl
      have hinS : InRegions (u.rd ++ u.wr) (S.addr s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
        Buf.inRegR hp hS cu.rd cu.wr (show 4 * k + 4 ≤ 4 * n by omega)
      refine wp_movm' (by rw [eS]; exact hinS) fun u₁ o₁ v₁ => ?_
      have c₁ := cu.only o₁ (by decide) (by decide)
      have eD₁ : u₁.ea (at_ .ebp 0) = D.addr s₀ + BitVec.ofNat 64 (4 * k) := by
        rw [← eD]; simp only [State.ea, at_, o₁.gpr _ (by decide : Reg.ebp ∉ [Reg.eax])]
      have hinD : InRegions u₁.wr (D.addr s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
        Buf.inRegW hp hD₁ (Lay.okW_iff.mp hD).2 c₁.wr (show 4 * k + 4 ≤ 4 * n by omega)
      refine wp_store' (by rw [eD₁]; exact hinD) fun u₂ g₂ r₂ w₂ m₂ => ?_
      obtain ⟨r, hr, hcr⟩ := Buf.contains hp hD₁ (Lay.okW_iff.mp hD).2 (o := 4 * k) (n := 4)
        (show 4 * k + 4 ≤ 4 * n by omega)
      have c₂ : Ctx (Y p) s₀ u₂ := ⟨by rw [g₂]; exact c₁.esp, by rw [r₂]; exact c₁.rd, by rw [w₂]; exact c₁.wr,
        by rw [g₂]; exact c₁.esi, by rw [m₂, eD₁]; exact c₁.frame.writeW hr _ hcr⟩
      refine wp_addi fun u₃ o₃ v₃ => wp_addi fun u₄ o₄ v₄ => wp_subi_last fun u₅ o₅ v₅ z₅ => ?_
      have c₅ := ((c₂.only o₃ (by decide) (by decide)).only o₄ (by decide) (by decide)).only o₅ (by decide)
        (by decide)
      have m₅ : u₅.mem = u₁.mem.writeW (D.addr s₀ + BitVec.ofNat 64 (4 * k)) (u.mem.readW (S.addr s₀ +
          BitVec.ofNat 64 (4 * k)) 32) := by
        rw [o₅.mem, o₄.mem, o₃.mem, m₂, eD₁, v₁, eS]
      have ex : u₄.gpr .ecx = BitVec.ofNat 32 (n - k) := by
        rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), g₂, o₁.gpr _ (by decide), xu]
      refine ⟨⟨c₅, ?_, ?_, by rw [v₅, ex]; exact cnt_next hk, ?_, ?_⟩, ?_⟩
      · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃, g₂, o₁.gpr _ (by decide), du]
        show _ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
        rw [add_ofNat_add, show 4 * (k + 1) = 4 * k + 4 by omega]
      · rw [o₅.gpr _ (by decide), v₄, o₃.gpr _ (by decide), g₂, o₁.gpr _ (by decide), bu]
        show _ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
        rw [add_ofNat_add, show 4 * (k + 1) = 4 * k + 4 by omega]
      · rw [m₅, o₁.mem]
        exact fu.writeW (List.mem_singleton_self _) _ (by
          show (⟨D.addr s₀, 4 * n⟩ : Region).Contains _ 4
          simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
      · intro j hj
        rw [m₅, o₁.mem, wordw_bytes (by omega) hj]
        split
        · rename_i e
          rw [← Mem.readW_byte _ _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
            show 4 * k + (j - 4 * k) = j by omega]
          exact fu.bytes (R := S.rgn s₀) (fun r hr => by
            rw [List.mem_singleton] at hr; subst hr; exact dd) (by show 4 * n ≤ 2 ^ 64; omega)
            (show j < 4 * n by omega)
        · exact cpu j (by omega)
      · show u₅.zf.map (!·) = _
        rw [z₅, ex]; exact cnt_ne hk (by omega)
    · refine hQ s₀ s u hp ha cu fu ?_
      exact List.map_congr_left fun j hj => cpu j (List.mem_range.mp hj)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁, e₁', hq.t.ptr hS]
    · rw [e₂, e₂', hq.t.ptr hD₁]
    · rw [e₃, e₃']


theorem absorbC_piece' (st wk rate pos : Nat) (b : Buf) (hr : rate ∈ rates) (hpos : pos < rate)
    (hc : ((Y p).okW ⟨SC, st, 200⟩ && (Y p).okW ⟨SC, wk, 640⟩ && (Y p).ok b && (Y p).sep ⟨SC, st, 200⟩ ⟨SC, wk, 640⟩ &&
      (Y p).sep b ⟨SC, st, 200⟩ && (Y p).sep b ⟨SC, wk, 640⟩) = true)  (hlen : b.len < 2 ^ 32)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' →
      Frame ([⟨SC, st, 200⟩, ⟨SC, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      (∀ msg, Repr s.mem (Buf.addr s₀ ⟨SC, st, 200⟩) rate msg → pos = msg.length % rate →
        Repr s'.mem (Buf.addr s₀ ⟨SC, st, 200⟩) rate (msg ++ bytesAt s.mem (b.addr s₀) b.len)) → B s₀ s') :
    SP p A B (absorbC SC st wk rate pos b) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, -⟩, -⟩, -⟩ := hc'
  refine Piece.seq (setup_es (fun s₀ s₁ => AbsArgs s₁ (Buf.ptr s₀ ⟨SC, st, 200⟩) (b.ptr s₀)
      (Buf.ptr s₀ ⟨SC, wk, 640⟩) rate pos b.len) (fun s₀ s hp h => ?_) hA (by simp only [List.all_append, ptrTo_esOk (r := .eax) (by decide) (by decide), ptrTo_esOk (r := .ebx) (by decide) (by decide), ptrTo_esOk (r := .edi) (by decide) (by decide)]; rfl))
    (lift (absorb_call (Y := Y p) SC st SC wk b rate pos hr hpos hc (show 56 ≤ 96 by decide) hlen (fun s₀ s₁ hp ⟨_, _, h₁, _, a₁⟩ => ⟨h₁, a₁⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_))
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movi fun s₂ o₂ v₂ => wp_movi fun s₃ o₃ v₃ => ?_
    have c₃ := (c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)
    refine ptrTo_ok hp c₃ h2 fun s₄ o₄ v₄ => ?_
    have c₄ := c₃.only o₄ (by decide) (by decide)
    refine wp_movi fun s₅ o₅ v₅ => ?_
    have c₅ := c₄.only o₅ (by decide) (by decide)
    rw [← List.append_nil (ptrTo SC .edi _)]
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

theorem padC_piece' (st wk rate pos sfx : Nat) (hr : rate ∈ rates) (hpos : pos < rate)
    (hc : ((Y p).okW ⟨SC, st, 200⟩ && (Y p).okW ⟨SC, wk, 640⟩ && (Y p).sep ⟨SC, st, 200⟩ ⟨SC, wk, 640⟩) = true)

    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' →
      Frame ([⟨SC, st, 200⟩, ⟨SC, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      (∀ msg, Repr s.mem (Buf.addr s₀ ⟨SC, st, 200⟩) rate msg → pos = msg.length % rate →
        stateAt s'.mem (Buf.addr s₀ ⟨SC, st, 200⟩) =
          absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8) msg)) → B s₀ s') :
    SP p A B (padC SC st wk rate pos sfx) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨h0, h1⟩, -⟩ := hc'
  refine Piece.seq (setup_es (fun s₀ s₁ => PadArgs s₁ (Buf.ptr s₀ ⟨SC, st, 200⟩)
      (Buf.ptr s₀ ⟨SC, wk, 640⟩) rate pos sfx) (fun s₀ s hp h => ?_) hA (by simp only [List.all_append, ptrTo_esOk (r := .eax) (by decide) (by decide), ptrTo_esOk (r := .edi) (by decide) (by decide)]; rfl))
    (lift (pad_call (Y := Y p) SC st SC wk rate pos sfx hr hpos hc (show 56 ≤ 96 by decide) (fun s₀ s₁ hp ⟨_, _, h₁, _, a₁⟩ => ⟨h₁, a₁⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_))
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movi fun s₂ o₂ v₂ => wp_movi fun s₃ o₃ v₃ => wp_movi fun s₄ o₄ v₄ => ?_
    have c₄ := ((c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)).only o₄ (by decide)
      (by decide)
    rw [← List.append_nil (ptrTo SC .edi _)]
    refine ptrTo_ok hp c₄ (Lay.okW_iff.mp h1).1 fun s₅ o₅ v₅ => WP.block_nil_iff.mpr ?_
    refine ⟨c₄.only o₅ (by decide) (by decide),
      o₅.mem.trans (o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem))), ⟨?_, ?_, ?_, ?_, v₅⟩⟩
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁]
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂]
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃]
    · rw [o₅.gpr _ (by decide), v₄]
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

theorem squeezeC_piece' (st wk rate : Nat) (o : Buf) (hr : rate ∈ rates)
    (hc : ((Y p).okW ⟨SC, st, 200⟩ && (Y p).okW ⟨SC, wk, 640⟩ && (Y p).okW o && (Y p).sep ⟨SC, st, 200⟩ ⟨SC, wk, 640⟩ &&
      (Y p).sep ⟨SC, st, 200⟩ o && (Y p).sep o ⟨SC, wk, 640⟩) = true)  (hlen : o.len < 2 ^ 32)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' →
      Frame ([⟨SC, st, 200⟩, o, ⟨SC, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      bytesAt s'.mem (o.addr s₀) o.len =
        squeezeFrom rate (stateAt s.mem (Buf.addr s₀ ⟨SC, st, 200⟩)) 0 o.len → B s₀ s') :
    SP p A B (squeezeC SC st wk rate o) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, -⟩, -⟩, -⟩ := hc'
  refine Piece.seq (setup_es (fun s₀ s₁ => AbsArgs s₁ (Buf.ptr s₀ ⟨SC, st, 200⟩) (o.ptr s₀)
      (Buf.ptr s₀ ⟨SC, wk, 640⟩) rate 0 o.len) (fun s₀ s hp h => ?_) hA (by simp only [List.all_append, ptrTo_esOk (r := .eax) (by decide) (by decide), ptrTo_esOk (r := .ebx) (by decide) (by decide), ptrTo_esOk (r := .edi) (by decide) (by decide)]; rfl))
    (lift (squeeze_call (Y := Y p) SC st SC wk o rate 0 hr (Nat.zero_le _) hc (show 56 ≤ 96 by decide) hlen
      (fun s₀ s₁ hp ⟨_, _, h₁, _, a₁⟩ => ⟨h₁, a₁⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr r₁ _ => ?_))
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movi fun s₂ o₂ v₂ => wp_movi fun s₃ o₃ v₃ => ?_
    have c₃ := (c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)
    refine ptrTo_ok hp c₃ (Lay.okW_iff.mp h2).1 fun s₄ o₄ v₄ => ?_
    have c₄ := c₃.only o₄ (by decide) (by decide)
    refine wp_movi fun s₅ o₅ v₅ => ?_
    have c₅ := c₄.only o₅ (by decide) (by decide)
    rw [← List.append_nil (ptrTo SC .edi _)]
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

/-- The SHA-3 or SHAKE function (`rate`, suffix `sfx`) of the bytes of `b₁` and `b₂`, into `o`. -/
theorem hash2_piece' (rate sfx : Nat) (b₁ b₂ o : Buf) (hr : rate ∈ rates)
    (hc : ((Y p).okW ⟨SC, oST, 200⟩ && (Y p).okW ⟨SC, oWK, 640⟩ && (Y p).ok b₁ && (Y p).ok b₂ && (Y p).okW o &&
      (Y p).sep ⟨SC, oST, 200⟩ ⟨SC, oWK, 640⟩ && (Y p).sep b₁ ⟨SC, oST, 200⟩ && (Y p).sep b₁ ⟨SC, oWK, 640⟩ &&
      (Y p).sep b₂ ⟨SC, oST, 200⟩ && (Y p).sep b₂ ⟨SC, oWK, 640⟩ && (Y p).sep ⟨SC, oST, 200⟩ o &&
      (Y p).sep o ⟨SC, oWK, 640⟩) = true)
    (hl₁ : b₁.len < 2 ^ 32) (hl₂ : b₂.len < 2 ^ 32) (hlo : o.len < 2 ^ 32)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' →
      Frame ([⟨SC, oST, 200⟩, ⟨SC, oWK, 640⟩, o].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      bytesAt s'.mem (o.addr s₀) o.len = squeezeFrom rate (absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8)
        (bytesAt s.mem (b₁.addr s₀) b₁.len ++ bytesAt s.mem (b₂.addr s₀) b₂.len))) 0 o.len → B s₀ s') :
    SP p A B (hash2 SC oST oWK rate sfx b₁ b₂ o) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hS, hW⟩, hb₁⟩, hb₂⟩, hO⟩, dSW⟩, d₁S⟩, d₁W⟩, d₂S⟩, d₂W⟩, dSO⟩, dOW⟩ := hc'
  have hrate := (rate_lt hr)
  have hr0 : 0 < rate := by simp [rates] at hr; omega
  -- after zeroing, absorbing `b₁`, absorbing `b₂`, padding
  let P : Nat → State → State → Prop := fun i s₀ u => ∃ s, A s₀ s ∧ Ctx (Y p) s₀ u ∧ Frame (kF oST oWK (Y p) s₀) s.mem u.mem ∧
    (i = 0 → stateAt u.mem (Buf.addr s₀ ⟨SC, oST, 200⟩) = Spec.Sha3.zero) ∧
    (i = 1 → Repr u.mem (Buf.addr s₀ ⟨SC, oST, 200⟩) rate (bytesAt s.mem (b₁.addr s₀) b₁.len)) ∧
    (i = 2 → Repr u.mem (Buf.addr s₀ ⟨SC, oST, 200⟩) rate
      (bytesAt s.mem (b₁.addr s₀) b₁.len ++ bytesAt s.mem (b₂.addr s₀) b₂.len)) ∧
    (i = 3 → stateAt u.mem (Buf.addr s₀ ⟨SC, oST, 200⟩) = absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8)
      (bytesAt s.mem (b₁.addr s₀) b₁.len ++ bytesAt s.mem (b₂.addr s₀) b₂.len)))
  have cS : ((Y p).okW ⟨SC, oST, 200⟩ && (Y p).okW ⟨SC, oWK, 640⟩ && (Y p).sep ⟨SC, oST, 200⟩ ⟨SC, oWK, 640⟩) = true := by
    simp [hS, hW, dSW]
  refine Piece.seq (B := P 0) (lift (zeroTop_piece (Y := Y p) oST hS (by taint_decide) hA fun s₀ s s' hp ha h' fr z =>
    ⟨s, ha, h', kF_zero hp (show 56 ≤ 96 by decide) fr, fun _ => z, by simp, by simp, by simp⟩)) ?_
  refine Piece.seq (B := P 1) (absorbC_piece' oST oWK rate 0 b₁ hr hr0 (by simp [hS, hW, hb₁, dSW, d₁S, d₁W])
    hl₁ (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, z, _⟩ h' fr post => ?_) ?_
  · have r := post [] (repr_nil (z rfl)) (by simp)
    rw [List.nil_append, kF_bytes hp (show 56 ≤ 96 by decide) hb₁ (by simp [Y_sc, hS, hW, d₁S, d₁W]) fu] at r
    exact ⟨s, ha, h', fu.trans fr, by simp, fun _ => r, by simp, by simp⟩
  refine Piece.seq (B := P 2) (absorbC_piece' oST oWK rate (b₁.len % rate) b₂ hr (Nat.mod_lt _ hr0)
    (by simp [hS, hW, hb₂, dSW, d₂S, d₂W]) hl₂ (fun s₀ u _ ⟨_, _, h, _⟩ => h)
    fun s₀ u u' hp ⟨s, ha, _, fu, _, r, _⟩ h' fr post => ?_) ?_
  · have r' := post _ (r rfl) (by rw [bytesAt_length])
    rw [kF_bytes hp (show 56 ≤ 96 by decide) hb₂ (by simp [Y_sc, hS, hW, d₂S, d₂W]) fu] at r'
    exact ⟨s, ha, h', fu.trans fr, by simp, by simp, fun _ => r', by simp⟩
  refine Piece.seq (B := P 3) (padC_piece' oST oWK rate ((b₁.len + b₂.len) % rate) sfx hr (Nat.mod_lt _ hr0) cS
    (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, _, _, r, _⟩ h' fr post => ?_) ?_
  · exact ⟨s, ha, h', fu.trans fr, by simp, by simp, by simp,
      fun _ => post _ (r rfl) (by rw [List.length_append, bytesAt_length, bytesAt_length])⟩
  refine squeezeC_piece' oST oWK rate o hr (by simp [hS, hW, hO, dSW, dSO, dOW]) hlo
    (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, _, _, _, z⟩ h' fr r₁ => ?_
  rw [z rfl] at r₁
  refine hQ s₀ s u' hp ha h' ((fu.sub fun r hr => ?_).trans (fr.sub fun r hr => ?_)) r₁
  · simp only [kF, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp [Y_sc], fun _ h => h⟩
  · simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

end VG.Proof.MlDsa.X86.Sign
