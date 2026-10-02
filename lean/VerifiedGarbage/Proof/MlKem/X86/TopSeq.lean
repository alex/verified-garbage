import VerifiedGarbage.Proof.MlKem.X86.TopPrim2
import VerifiedGarbage.Proof.MlKem.X86.TopPrim3

/-!
# ML-KEM on x86 (32-bit): the calls of the top-level functions, with their arguments

A buffer's address, computed by `ptrTo` from `esi` or from the argument on the
stack (`ptrTo_ok`); the block that sets a call's arguments (`setup_piece`,
whose addresses depend only on `esp` and `esi`); and each call with it
(`nttC_piece`, …), whose postcondition relates the state before the block to
the state after the call.
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-! ## Single instructions -/

theorem Only.flags (s : State) (d : Reg) (x : BitVec 32) (c o : Bool) :
    Only [d] s ((arithFlags s x c o).setReg d x) :=
  ⟨fun r hr => by
    simp only [State.setReg]
    rw [ite_eq_right_iff.mpr fun (e : r = d) => absurd (e ▸ List.mem_singleton_self d) hr]
    rfl, rfl, rfl, rfl⟩

theorem wp_movi {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = v → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  wp_cons (s' := s.setReg d v) (by simp only [exec, readSrc, Option.map_some])
    (k _ (Only.setReg s d v) (by simp [State.setReg]))

theorem wp_addi {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d + v → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d + v) (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat))
      (addOverflow (s.gpr d) v (s.gpr d + v))).setReg d (s.gpr d + v))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_movr' {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  wp_movr (k _ (Only.setReg s d _) (by simp [State.setReg]))

theorem wp_movm' {d b : Reg} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ b disp)) 4)
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.mem.readW (s.ea (at_ b disp)) 32 → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (at_ b disp)) :: is)) s Q :=
  wp_movm hin (k _ (Only.setReg s d _) (by simp [State.setReg]))

theorem Ctx.only {s₀ s s' : State} (h : Ctx Y s₀ s) {ds : List Reg} (o : Only ds s s')
    (hd : Reg.esp ∉ ds) (hd' : Reg.esi ∉ ds) : Ctx Y s₀ s' :=
  h.same (o.gpr _ hd) (o.gpr _ hd') o.rd o.wr o.mem

/-! ## Addresses -/

theorem ptrTo_ok {s₀ s : State} (hp : TPre Y s₀) (h : Ctx Y s₀ s) {b : Buf} (hb : Y.ok b = true) {r : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Only [r] s s' → s'.gpr r = b.ptr s₀ → WP isa (.block is) s' Q) :
    WP isa (.block (ptrTo Y.sc r b ++ is)) s Q := by
  obtain ⟨hb₁, -, -⟩ := Lay.ok_iff.mp hb
  unfold ptrTo
  rw [List.cons_append, List.singleton_append]
  split
  · rename_i e
    refine wp_movr' fun s₁ o₁ v₁ => ?_
    exact wp_addi fun s₂ o₂ v₂ => k s₂ (o₁.trans o₂ |>.mono (by simp)) (by rw [v₂, v₁, h.esi, Buf.ptr, e])
  · have ea : s.ea (at_ .esp (20 + 4 * b.arg)) = argAddr s₀ b.arg := h.argEa
    refine wp_movm' (by rw [ea]; exact h.argIn hp hb₁) fun s₁ o₁ v₁ => ?_
    exact wp_addi fun s₂ o₂ v₂ => k s₂ (o₁.trans o₂ |>.mono (by simp))
      (by rw [v₂, v₁, ea, h.argw hp hb₁])

/-- A block that sets registers, whose addresses depend only on `esp` and `esi`. -/
theorem setup_piece {is : List Instr} (P : State → State → Prop)
    (hw : ∀ s₀ s, TPre Y s₀ → Ctx Y s₀ s → WP isa (.block is) s fun s₁ => Ctx Y s₀ s₁ ∧ s₁.mem = s.mem ∧ P s₀ s₁)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    {ht : Taint.Hint VG.X86.Taint.T} (t : (VG.X86.taint.check (τr [.esp, .esi]) (.block is) ht).isSome = true) :
    Piece (TPre Y) (TPub Y lk) A (fun s₀ s₁ => ∃ s, A s₀ s ∧ Ctx Y s₀ s₁ ∧ s₁.mem = s.mem ∧ P s₀ s₁)
      (.block is) :=
  Piece.taint [.esp, .esi] (fun s₀ s hp ha => (hw s₀ s hp (hA s₀ s hp ha)).mono fun s₁ h₁ => ⟨s, ha, h₁⟩)
    (fun s₀ s₀' s s' hp _ hq ha ha' r hr => by
      have h := hA s₀ s hp ha
      have h' := hA s₀' s' ‹_› ha'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.esp, h'.esp, hq.E1]
      · rw [h.esi, h'.esi, hq.sc hp]) t

/-- Two addresses, in `eax` and `ecx`. -/
theorem ptr2_ok {s₀ s : State} (hp : TPre Y s₀) (h : Ctx Y s₀ s) {b₀ b₁ : Buf} (h₀ : Y.ok b₀ = true)
    (h₁ : Y.ok b₁ = true) :
    WP isa (.block (ptrTo Y.sc .eax b₀ ++ ptrTo Y.sc .ecx b₁)) s fun s' => Ctx Y s₀ s' ∧ s'.mem = s.mem ∧
      s'.gpr .eax = b₀.ptr s₀ ∧ s'.gpr .ecx = b₁.ptr s₀ := by
  rw [← List.append_nil (ptrTo Y.sc .ecx b₁)]
  refine ptrTo_ok hp h h₀ fun s₁ o₁ v₁ => ?_
  have c₁ := h.only o₁ (by decide) (by decide)
  refine ptrTo_ok hp c₁ h₁ fun s₂ o₂ v₂ => WP.block_nil_iff.mpr ?_
  exact ⟨c₁.only o₂ (by decide) (by decide), o₂.mem.trans o₁.mem, by rw [o₂.gpr _ (by decide), v₁], v₂⟩

/-- The block setting two addresses. -/
theorem setup2 {b₀ b₁ : Buf} (h₀ : Y.ok b₀ = true) (h₁ : Y.ok b₁ = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    {ht : Taint.Hint VG.X86.Taint.T}
    (t : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax b₀ ++ ptrTo Y.sc .ecx b₁)) ht).isSome = true) :
    Piece (TPre Y) (TPub Y lk) A (fun s₀ s₁ => ∃ s, A s₀ s ∧ Ctx Y s₀ s₁ ∧ s₁.mem = s.mem ∧
      (s₁.gpr .eax = b₀.ptr s₀ ∧ s₁.gpr .ecx = b₁.ptr s₀)) (.block (ptrTo Y.sc .eax b₀ ++ ptrTo Y.sc .ecx b₁)) :=
  setup_piece _ (fun _ _ hp h => (ptr2_ok hp h h₀ h₁).mono fun _ ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩) hA t

/-- `f ← NTT(f)` or `NTT⁻¹(f)`, with its arguments. -/
theorem inPlaceC_piece {t : Poly → Poly} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c (inPlaceContract X86.abi t 16)) (hsp : NoSp c) (hst : stackUse c = 16)
    (fa fo sa so : Nat)
    (hc : (Y.okW ⟨fa, fo, 1024⟩ && Y.okW ⟨sa, so, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨sa, so, 1024⟩) = true)
    (hN : 44 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .ecx ⟨sa, so, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩, ⟨sa, so, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (t (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (.seq (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .ecx ⟨sa, so, 1024⟩)) (callWith [.ecx, .eax] nm c)) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  refine Piece.seq (setup2 (Lay.okW_iff.mp hc'.1.1).1 (Lay.okW_iff.mp hc'.1.2).1 (fun s₀ s hp ha => (hA s₀ s hp ha).1) tt)
    (inPlace_call hv hsp hst fa fo sa so hc hN (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂⟩ =>
      ⟨h₁, e₁, e₂, m₁ ▸ (hA s₀ s hp ha).2⟩) fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  rw [m₁] at fr post
  exact hQ s₀ s s' hp ha h' fr post

/-- `f ← op(f, g)` (`vg_mlkem_add` or `vg_mlkem_sub`), with its arguments. -/
theorem accC_piece {op : Poly → Poly → Poly} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c (accSig.contract X86.abi (pre := fun f g m => Reduced m f ∧ Reduced m g)
      (post := fun f g m m' _ => PolyIs m' f (op (polyAt m f) (polyAt m g))) (writeArgs := true) (stack := 16)))
    (hsp : NoSp c) (hst : stackUse c = 16) (fa fo ga go : Nat)
    (hc : (Y.okW ⟨fa, fo, 1024⟩ && Y.ok ⟨ga, go, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩) = true)
    (hN : 44 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .ecx ⟨ga, go, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (op (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (.seq (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .ecx ⟨ga, go, 1024⟩)) (callWith [.ecx, .eax] nm c)) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  refine Piece.seq (setup2 (Lay.okW_iff.mp hc'.1.1).1 hc'.1.2 (fun s₀ s hp ha => (hA s₀ s hp ha).1) tt)
    (acc_call hv hsp hst fa fo ga go hc hN (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂⟩ =>
      ⟨h₁, e₁, e₂, m₁ ▸ (hA s₀ s hp ha).2.1, m₁ ▸ (hA s₀ s hp ha).2.2⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  rw [m₁] at fr post
  exact hQ s₀ s s' hp ha h' fr post

/-- `f ← SamplePolyCBD₂(b)`, with its arguments. -/
theorem cbd2C_piece (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 128⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 128⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 44 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨ba, bo, 128⟩ ++ ptrTo Y.sc .ecx ⟨fa, fo, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (samplePolyCBD 2 (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 128⟩) 128)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (cbd2C Y.sc ⟨ba, bo, 128⟩ ⟨fa, fo, 1024⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  refine Piece.seq (setup2 hc'.1.1 (Lay.okW_iff.mp hc'.1.2).1 hA tt)
    (cbd2_call ba bo fa fo hc hN (fun s₀ s₁ hp ⟨_, _, h₁, _, e₁, e₂⟩ => ⟨h₁, e₁, e₂⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  rw [m₁] at fr post
  exact hQ s₀ s s' hp ha h' fr post

/-- `o ← ByteEncode₁₂(f)`, with its arguments. -/
theorem enc12C_piece (fa fo oa oo : Nat)
    (hc : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, 384⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, 384⟩) = true)
    (hN : 44 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .ecx ⟨oa, oo, 384⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨oa, oo, 384⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, 384⟩) 384 =
        encode12 (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (enc12C Y.sc ⟨fa, fo, 1024⟩ ⟨oa, oo, 384⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  refine Piece.seq (setup2 hc'.1.1 (Lay.okW_iff.mp hc'.1.2).1 (fun s₀ s hp ha => (hA s₀ s hp ha).1) tt)
    (encode12_call fa fo oa oo hc hN (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂⟩ =>
      ⟨h₁, e₁, e₂, m₁ ▸ (hA s₀ s hp ha).2⟩) fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  rw [m₁] at fr post
  exact hQ s₀ s s' hp ha h' fr post

/-- `f ← ByteDecode₁₂(b)`, with its arguments. -/
theorem dec12C_piece (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 384⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 384⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 44 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨ba, bo, 384⟩ ++ ptrTo Y.sc .ecx ⟨fa, fo, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (decode12 (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 384⟩) 384)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (dec12C Y.sc ⟨ba, bo, 384⟩ ⟨fa, fo, 1024⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  refine Piece.seq (setup2 hc'.1.1 (Lay.okW_iff.mp hc'.1.2).1 hA tt)
    (decode12_call ba bo fa fo hc hN (fun s₀ s₁ hp ⟨_, _, h₁, _, e₁, e₂⟩ => ⟨h₁, e₁, e₂⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  rw [m₁] at fr post
  exact hQ s₀ s s' hp ha h' fr post

end VG.Proof.MlKem.X86.Top
