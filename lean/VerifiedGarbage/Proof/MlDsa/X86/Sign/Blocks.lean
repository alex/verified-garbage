import VerifiedGarbage.Proof.MlDsa.X86.Sign.Local
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Params

/-!
# ML-DSA signing on x86 (32-bit): the blocks between calls

Untrusted: everything here is checked by Lean. Loads and stores of words
and bytes of `scratch` from `Ctx` (`wp_ldsc`, `wp_stsc`, `wp_st8sc`), and
the pieces made of them: sequences (`seqR_piece`), the empty block
(`nil_piece`), and the branch on `OK` (`okIte_piece`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {A B : State → State → Prop}

/-- The word of `scratch` at `o`. -/
abbrev scw (s₀ s : State) (o : Nat) : BitVec 32 := s.mem.readW (Buf.addr s₀ (sc o 4)) 32

theorem ea_sc {s₀ s : State} (h : Ctx (Y p) s₀ s) (o : Nat) (n : Nat) :
    s.ea (at_ .esi o) = Buf.addr s₀ (sc o n) := by
  simp only [State.ea, at_]; rw [h.esi]; rfl

/-- `r ← ` the word of `scratch` at `o`. -/
theorem wp_ldsc {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {o : Nat} (hc : (Y p).ok (sc o 4) = true)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Only [r] s s' → s'.gpr r = scw s₀ s o → WP isa (.block is) s' Q) :
    WP isa (.block (.mov r (.mem (at_ .esi o)) :: is)) s Q := by
  have hin : InRegions (s.rd ++ s.wr) (Buf.addr s₀ (sc o 4)) 4 := by
    have := Buf.inRegR hp hc h.rd h.wr (o := 0) (n := 4) (Nat.le_refl _)
    simpa using this
  exact wp_movm' (by rw [ea_sc h o 4]; exact hin) fun s' o' v' => k s' o' (by rw [v', ea_sc h o 4])

theorem ctx_write {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {o n w : Nat} (hc : (Y p).okW (sc o n) = true)
    (hw : w / 8 ≤ n) (v : BitVec w) : Ctx (Y p) s₀ { s with mem := s.mem.writeW (Buf.addr s₀ (sc o n)) v } := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 0) (n := w / 8) (by show 0 + w / 8 ≤ n; omega)
  rw [BitVec.add_zero] at hcr
  exact ⟨h.esp, h.rd, h.wr, h.esi, h.frame.writeW hr _ hcr⟩

/-- The word of `scratch` at `o` ← `r`. -/
theorem wp_stsc {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {o : Nat} (hc : (Y p).okW (sc o 4) = true)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → (∀ x, s'.gpr x = s.gpr x) → s'.mem = s.mem.writeW (Buf.addr s₀ (sc o 4)) (s.gpr r) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.store (at_ .esi o) r :: is)) s Q := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  have hin : InRegions s.wr (Buf.addr s₀ (sc o 4)) 4 := by
    have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 4) (Nat.le_refl _)
    simpa using this
  refine wp_store' (by rw [ea_sc h o 4]; exact hin) fun s' g' r' w' m' => ?_
  rw [ea_sc h o 4] at m'
  have c := ctx_write hp h hc (w := 32) (by decide) (s.gpr r)
  exact k s' ⟨by rw [g']; exact c.esp, by rw [r']; exact c.rd, by rw [w']; exact c.wr, by rw [g']; exact c.esi,
    by rw [m']; exact c.frame⟩ g' m'

/-- The byte of `scratch` at `o` ← the low byte of `r`. -/
theorem wp_st8sc {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {o : Nat} (hc : (Y p).okW (sc o 1) = true)
    {r : Reg8} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → (∀ x, s'.gpr x = s.gpr x) →
      s'.mem = s.mem.writeW (Buf.addr s₀ (sc o 1)) ((s.gpr r.reg).setWidth 8) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 (at_ .esi o) r :: is)) s Q := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  have hin : InRegions s.wr (Buf.addr s₀ (sc o 1)) 1 := by
    have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 1) (Nat.le_refl _)
    simpa using this
  refine wp_store8 (by rw [ea_sc h o 1]; exact hin) ?_
  rw [ea_sc h o 1]
  exact k _ (ctx_write hp h hc (w := 8) (by decide) _) (fun _ => rfl) rfl

theorem wp_addr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d + s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d + s.gpr r) (decide (2 ^ 32 ≤ (s.gpr d).toNat + (s.gpr r).toNat))
      (addOverflow (s.gpr d) (s.gpr r) (s.gpr d + s.gpr r))).setReg d (s.gpr d + s.gpr r))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_test {r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [] s s' → s'.zf = some (s.gpr r &&& s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test r (.reg r) :: is)) s Q :=
  wp_cons (s' := arithFlags s (s.gpr r &&& s.gpr r) false false)
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_subi {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d - v → s'.zf = some (s.gpr d - v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat))
      (subOverflow (s.gpr d) v (s.gpr d - v))).setReg d (s.gpr d - v))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]) rfl)

/-! ## Pieces -/

/-- The empty block. -/
theorem nil_piece (h : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → B s₀ s) : SP p A B (.block []) where
  wp s₀ s hp ha := WP.block_nil_iff.mpr (h s₀ s hp ha)
  ct _ _ _ _ _ := fun _ _ _ _ _ _ _ e₁ e₂ => by
    rw [Exec.block_iff] at e₁ e₂
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    exact ⟨e₁.2.symm.trans e₂.2, trivial⟩

/-- `f a, …, f (a + n - 1)`, from pieces for each. -/
theorem seqR_piece {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ (a n : Nat), (∀ i, a ≤ i → i < a + n → SP p (I i) (I (i + 1)) (f i)) → SP p (I a) (I (a + n)) (seqR f a n)
  | a, 0, _ => nil_piece fun _ _ _ h => h
  | a, n + 1, h => by
    refine Piece.seq (h a (Nat.le_refl _) (by omega)) ?_
    have := seqR_piece (I := I) (a + 1) n fun i hi hi' => h i (by omega) (by omega)
    rwa [show a + 1 + n = a + (n + 1) by omega] at this

/-- The branch on `OK`, which is 1 or 0 as `b` of the initial state says. -/
theorem okIte_piece (hc : (Y p).ok (sc oOK 4) = true) {t e : Prog isa} (b : State → Bool)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s ∧ scw s₀ s oOK = if b s₀ then 1 else 0)
    (hb : ∀ s₀ s₀', TPre (Y p) s₀ → TPre (Y p) s₀' → SPub p s₀ s₀' → b s₀ = b s₀')
    (ht : SP p (fun s₀ s₁ => (∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ s₁.mem = s.mem) ∧ b s₀ = true) B t)
    (he : SP p (fun s₀ s₁ => (∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ s₁.mem = s.mem) ∧ b s₀ = false) B e) :
    SP p A B (ifOkElse t e) := by
  refine Piece.seq (B := fun s₀ s₁ => (∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ s₁.mem = s.mem) ∧
    s₁.zf = some (!b s₀)) (blk_piece (fun s₀ s hp ha => (hA s₀ s hp ha).1) (fun s₀ s hp ha => ?_) rfl) ?_
  · obtain ⟨h, hok⟩ := hA s₀ s hp ha
    refine wp_ldsc hp h hc fun s₁ o₁ v₁ => wp_test fun s₂ o₂ z₂ => WP.block_nil_iff.mpr ?_
    have o := o₁.trans o₂
    refine ⟨⟨s, ha, h.only o (by simp) (by simp), o.mem⟩, ?_⟩
    rw [z₂, v₁, hok]
    cases b s₀ <;> rfl
  · refine Piece.ite b (fun s₀ s₁ hp ha => ?_) hb (ht.mono (fun _ _ _ h => ⟨h.1.1, h.2⟩) fun _ _ _ h => h)
      (he.mono (fun _ _ _ h => ⟨h.1.1, h.2⟩) fun _ _ _ h => h)
    show s₁.zf.map (!·) = _
    rw [ha.2]; cases b s₀ <;> rfl

end VG.Proof.MlDsa.X86.Sign
