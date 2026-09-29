import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_add` and `vg_mlkem_sub`

Untrusted: everything here is checked by Lean. Both are `mapLoop` around an
arithmetic step; the loop is proven once for any step that computes a
function `F` of the two coefficients (`OpSpec`).
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Spec.MlKem

/-- `op` computes `F a b` in `eax` from `eax = a` and `[edi] = b`, changing
only `eax`, `edx` and the flags. -/
def OpSpec (op : List Instr) (F : Nat → Nat → Nat) : Prop :=
  ∀ (is : List Instr) (s : State) (Q : State → Prop) (a b : Nat), a < q → b < q →
    (s.gpr .eax).toNat = a → InRegions (s.rd ++ s.wr) (s.ea (at_ .edi 0)) 4 →
    (s.mem.readW (s.ea (at_ .edi 0)) 32).toNat = b →
    (∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = F a b → WP isa (.block is) s' Q) →
    WP isa (.block (op ++ is)) s Q

theorem addOp_spec : OpSpec addOp fun a b => condSub (a + b) := by
  intro is s P a b ha hb h₁ hin h₂ k
  simp only [State.ea, at_] at hin h₂
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addOp, csub, at_, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, Option.map_some, hin, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]
  · have e : (s.gpr .eax + s.mem.readW (BitVec.setWidth 64 (s.gpr .edi + 0#32)) 32).toNat = a + b := by
      rw [BitVec.toNat_add, h₁, h₂, Nat.mod_eq_of_lt (by rw [q_eq] at ha hb; omega)]
    simp only [ite_true]
    rw [condSub_bv _ _ (by rw [e]; omega), e]

theorem subOp_spec : OpSpec subOp fun a b => condSub (a + q - b) := by
  intro is s P a b ha hb h₁ hin h₂ k
  simp only [State.ea, at_] at hin h₂
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [subOp, csub, at_, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, Option.map_some, hin, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]
  · have e : (s.gpr .eax + Q - s.mem.readW (BitVec.setWidth 64 (s.gpr .edi + 0#32)) 32).toNat =
        a + q - b := by
      rw [q_eq] at ha hb ⊢
      have hQ : (s.gpr .eax + Q).toNat = a + 3329 := by
        rw [BitVec.toNat_add, h₁, show Q.toNat = 3329 from rfl, Nat.mod_eq_of_lt (by omega)]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hQ, h₂]; omega), hQ, h₂]
    simp only [ite_true]
    rw [condSub_bv _ _ (by rw [e]; omega), e]

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev fP : BitVec 32 := arg s₀ 0
abbrev gP : BitVec 32 := arg s₀ 1
abbrev fA : Addr := (fP s₀).setWidth 64
abbrev gA : Addr := (gP s₀).setWidth 64
abbrev aR2 : Region := ⟨argAddr s₀ 0, 8⟩
/-- The stack below the return address, as the contract states it. -/
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
end

structure AccPre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 8 ≤ 2 ^ 32
  rd : s₀.rd = [polyRegion (gA s₀)]
  wr : s₀.wr = [polyRegion (fA s₀), aR2 s₀]
  f_g : (polyRegion (fA s₀)).Disjoint (polyRegion (gA s₀))
  f_a : (polyRegion (fA s₀)).Disjoint (aR2 s₀)
  g_a : (polyRegion (gA s₀)).Disjoint (aR2 s₀)
  ret_f : (retR s₀).Disjoint (polyRegion (fA s₀))
  ret_g : (retR s₀).Disjoint (polyRegion (gA s₀))
  ret_a : (retR s₀).Disjoint (aR2 s₀)
  stk_f : (stkR s₀).Disjoint (polyRegion (fA s₀))
  stk_g : (stkR s₀).Disjoint (polyRegion (gA s₀))
  stk_a : (stkR s₀).Disjoint (aR2 s₀)
  f_fit : (fP s₀).toNat + 1024 ≤ 2 ^ 32
  g_fit : (gP s₀).toNat + 1024 ≤ 2 ^ 32
  f_red : Reduced s₀.mem (fA s₀)
  g_red : Reduced s₀.mem (gA s₀)

theorem AccPre.of_add {s₀ : State} (h : (addContract X86.abi 16).pre s₀) : AccPre s₀ := by
  sig_pre [addContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem AccPre.of_sub {s₀ : State} (h : (subContract X86.abi 16).pre s₀) : AccPre s₀ := by
  sig_pre [subContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem stkR_eq {s₀ : State} (h : 16 ≤ (E0 s₀).toNat) : stkR s₀ = frameR s₀ := by
  simp only [stkR, frameR, below]; rw [Taint.sub_setWidth h]

/-- The push changes nothing of a region apart from the frame. -/
theorem P0_mem {s₀ : State} (h : 16 ≤ (E0 s₀).toNat) :
    Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact h)
  rw [saveRegs_len] at hf
  exact hf

/-! ## The loop -/

/-- The new value of coefficient `i`. -/
def newC (F : Nat → Nat → Nat) (s₀ : State) (i : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (F (coeffAt s₀.mem (fA s₀) i).toNat (coeffAt s₀.mem (gA s₀) i).toNat)

/-- After `k` coefficients. -/
structure MapInv (F : Nat → Nat → Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = fP s₀ + BitVec.ofNat 32 (4 * k)
  edi : s.gpr .edi = gP s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  frame : Frame [polyRegion (fA s₀)] (P0 s₀).mem s.mem
  f : ∀ i < 256, coeffAt s.mem (fA s₀) i = if i < k then newC F s₀ i else coeffAt s₀.mem (fA s₀) i

theorem polyLen (p : Addr) : (polyRegion p).len ≤ 2 ^ 64 := by show 1024 ≤ 2 ^ 64; decide

namespace AccPre
variable {s₀ : State} (hp : AccPre s₀)
include hp

theorem in_f {s : State} (hw : s.wr = (P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions s.wr (coeffAddr (fA s₀) k) 4 := by
  rw [hw, P0_wr, hp.wr]
  exact ⟨polyRegion (fA s₀), by simp, coeff_contains _ hk⟩

theorem in_f' {s : State} (hw : s.wr = (P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (fA s₀) k) 4 :=
  let ⟨r, h, c⟩ := hp.in_f hw hk; ⟨r, List.mem_append_right _ h, c⟩

theorem in_g {s : State} (hr : s.rd = (P0 s₀).rd) {k : Nat} (hk : k < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (gA s₀) k) 4 := by
  rw [hr, pushed_rd, hp.rd]
  exact ⟨polyRegion (gA s₀), by simp, coeff_contains _ hk⟩

/-- `g` is never written. -/
theorem g_keep {s : State} (hf : Frame [polyRegion (fA s₀)] (P0 s₀).mem s.mem) {i : Nat} (hi : i < 256) :
    coeffAt s.mem (gA s₀) i = coeffAt s₀.mem (gA s₀) i := by
  have f₁ := P0_mem hp.sp
  rw [coeffAt_congr (m := s.mem) (m' := s₀.mem) (fun j hj => ?_) hi]
  rw [hf.bytes (R := polyRegion (gA s₀)) (by simpa using hp.f_g.symm) (polyLen _) hj,
    f₁.bytes (R := polyRegion (gA s₀)) (by simpa [← stkR_eq hp.sp] using hp.stk_g.symm) (polyLen _) hj]

theorem f_P0 {i : Nat} (hi : i < 256) : coeffAt (P0 s₀).mem (fA s₀) i = coeffAt s₀.mem (fA s₀) i :=
  coeffAt_congr (fun j hj => (P0_mem hp.sp).bytes (R := polyRegion (fA s₀))
    (by simpa [← stkR_eq hp.sp] using hp.stk_f.symm) (polyLen _) hj) hi

theorem ea_f (k : Nat) (hk : k < 256) :
    (fP s₀ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (fA s₀) k := by
  rw [ea_add (by have := hp.f_fit; omega), Nat.add_zero]

theorem ea_g (k : Nat) (hk : k < 256) :
    (gP s₀ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (gA s₀) k := by
  rw [ea_add (by have := hp.g_fit; omega), Nat.add_zero]

end AccPre

theorem map_step {op : List Instr} {F : Nat → Nat → Nat} (hop : OpSpec op F) {s₀ : State} (hp : AccPre s₀) {k : Nat} (hk : k < 256)
    {s : State} (h : MapInv F s₀ k s) :
    WP isa (.block (mapBody op)) s fun s' =>
      MapInv F s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have hk' : k < n := hk
  have ef : s.ea (at_ .esi 0) = coeffAddr (fA s₀) k := by
    rw [State.ea, at_, h.esi]; exact hp.ea_f k hk
  refine wp_movm (by rw [ef]; exact hp.in_f' h.wr hk) ?_
  set s₁ := s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32) with hs₁
  have ha : (coeffAt s₀.mem (fA s₀) k).toNat < q := hp.f_red k hk'
  have hb : (coeffAt s₀.mem (gA s₀) k).toNat < q := hp.g_red k hk'
  have eg : s₁.ea (at_ .edi 0) = coeffAddr (gA s₀) k := by
    simp only [hs₁, State.ea, at_, State.setReg, show Reg.edi ≠ Reg.eax by decide, ite_false, h.edi]
    exact hp.ea_g k hk
  refine hop _ s₁ _ _ _ ha hb ?_ ?_ ?_ fun s₂ o₂ v₂ => ?_
  · simp only [hs₁, State.setReg, ite_true]
    rw [ef, ← coeffAt_eq, h.f k hk, ite_eq_right (Nat.lt_irrefl k)]
  · rw [eg]; exact hp.in_g h.rd hk
  · rw [eg, show s₁.mem = s.mem from rfl, ← coeffAt_eq, hp.g_keep h.frame hk]
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → s₂.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [o₂.gpr r (by simp [h₁, h₂])]; simp [hs₁, State.setReg, h₁]
  have m₂ : s₂.mem = s.mem := o₂.mem
  have r₂ : s₂.rd = (P0 s₀).rd := o₂.rd.trans h.rd
  have w₂ : s₂.wr = (P0 s₀).wr := o₂.wr.trans h.wr
  have esi₂ : s₂.gpr .esi = fP s₀ + BitVec.ofNat 32 (4 * k) := by rw [g₂ _ (by decide) (by decide), h.esi]
  have edi₂ : s₂.gpr .edi = gP s₀ + BitVec.ofNat 32 (4 * k) := by rw [g₂ _ (by decide) (by decide), h.edi]
  have ecx₂ : s₂.gpr .ecx = BitVec.ofNat 32 (256 - k) := by rw [g₂ _ (by decide) (by decide), h.ecx]
  have out : InRegions s₂.wr (coeffAddr (fA s₀) k) 4 := hp.in_f w₂ hk
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, at_, State.store32, State.setReg, arithFlags, State.setFlags, esi₂,
    hp.ea_f k hk, out, ite_true, ite_false, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hv : s₂.gpr .eax = newC F s₀ k := eq_ofNat_of_toNat v₂
  refine ⟨⟨by simp [g₂, h.esp], r₂, w₂, ?_, ?_, ?_, ?_, fun i hi => ?_⟩, ?_⟩
  · simp only [ite_true, ite_false, show Reg.esi ≠ Reg.ecx by decide, show Reg.esi ≠ Reg.edi by decide]
    exact ptr_next _ _ 4
  · simp only [ite_true, ite_false, show Reg.edi ≠ Reg.ecx by decide, edi₂]
    exact ptr_next _ _ 4
  · simp only [ite_true, ecx₂]
    exact cnt_next hk
  · rw [m₂]; exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hk')
  · dsimp only
    rw [coeffAt_writeW _ _ (show i < n from hi) hk', m₂, hv, h.f i hi]
    by_cases e : k = i
    · subst e; simp
    · rw [ite_eq_right e]
      by_cases hik : i < k
      · rw [ite_eq_left hik, ite_eq_left (by omega)]
      · rw [ite_eq_right hik, ite_eq_right (by omega)]
  · simp only [eval, ecx₂]
    exact cnt_ne hk (by decide)

/-! ## The function -/

/-- The public data: the stack pointer and the pointers. -/
def AccPub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

/-- The arguments, which the push leaves in place. -/
theorem AccPre.arg_P0 {s₀ : State} (hp : AccPre s₀) {i : Nat} (hi : i < 2) :
    ((P0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i ∧
      InRegions ((P0 s₀).rd ++ (P0 s₀).wr) (argAddr s₀ i) 4 ∧
      (P0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have hc : (aR2 s₀).Contains (argAddr s₀ i) 4 := by
    have := hp.sp'
    simp only [argAddr, Region.Contains, E0] at this ⊢
    bv_omega
  refine ⟨?_, ⟨aR2 s₀, by simp [hp.wr], hc⟩, ?_⟩
  · rw [P0_esp]; simp only [argAddr, E0]; congr 1; bv_omega
  · exact (P0_mem hp.sp).readW hc (by simpa [← stkR_eq hp.sp] using hp.stk_a.symm) (by decide)

theorem init_piece (F : Nat → Nat → Nat) :
    Piece AccPre AccPub (fun s₀ s => s = P0 s₀) (MapInv F · 0) (.block mapInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    obtain ⟨a₀, i₀, v₀⟩ := hp.arg_P0 (i := 0) (by omega)
    obtain ⟨a₁, i₁, v₁⟩ := hp.arg_P0 (i := 1) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd] at a₀ a₁
    apply WP.of_runBlock
    simp (config := {decide := true}) only [mapInit, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₀, a₁, i₀, i₁, v₀, v₁,
      ite_true, ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨by simp, rfl, rfl, by simp, by simp, by simp, Frame.refl _ _, fun i hi => ?_⟩
    simp only [Nat.not_lt_zero, ite_false]
    exact hp.f_P0 hi
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

theorem loop_piece {op : List Instr} {F : Nat → Nat → Nat} (hop : OpSpec op F)
    {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (mapBody op)) hc).isSome = true) :
    Piece AccPre AccPub (MapInv F · 0) (MapInv F · 256) (.loop (.block (mapBody op)) .ne) :=
  Piece.loop (fun k s₀ s => MapInv F s₀ k s) (by decide) fun k hk =>
    Piece.taint [.esp, .esi, .edi, .ecx] (fun _ _ hp h => map_step hop hp hk h)
      (fun s₀ s₀' s s' _ _ hq h h' r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
        · rw [h.esi, h'.esi, fP, fP, hq.2.1]
        · rw [h.edi, h'.edi, gP, gP, hq.2.2]
        · rw [h.ecx, h'.ecx]) ht

theorem map_piece {op : List Instr} {F : Nat → Nat → Nat} (hop : OpSpec op F)
    (hsp : NoSp (mapLoop op)) {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (mapBody op)) hc).isSome = true) :
    Piece AccPre AccPub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (MapInv F s₀ 256) s₀ s')
      (leaf (mapLoop op)) :=
  Piece.leaf (fun s₀ => [polyRegion (fA s₀)]) hsp (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← stkR_eq hp.sp]; exact hp.stk_f, hp.ret_f⟩)
    (fun _ _ _ _ hq => hq.1)
    ((Piece.seq (init_piece F) (loop_piece hop ht)).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem vec_zipWith_get (G : Zq → Zq → Zq) (f g : Poly) {i : Nat} (hi : i < n) :
    (Vector.zipWith G f g)[i]! = G f[i]! g[i]! := by
  rw [getElem!_eq _ hi, getElem!_eq _ hi, getElem!_eq _ hi, Vector.getElem_zipWith]

/-- The polynomial the loop leaves. -/
theorem map_post {F : Nat → Nat → Nat} {G : Zq → Zq → Zq} (hG : ∀ x y : Zq, (G x y).val = F x.val y.val)
    {s₀ s : State} (hp : AccPre s₀) (h : MapInv F s₀ 256 s) :
    PolyIs s.mem (fA s₀) (Vector.zipWith G (polyAt s₀.mem (fA s₀)) (polyAt s₀.mem (gA s₀))) := by
  refine polyIs_of_toNat fun i hi => ?_
  have hlt := val_lt (G (polyAt s₀.mem (fA s₀))[i]! (polyAt s₀.mem (gA s₀))[i]!)
  rw [hG, polyAt_val hp.f_red hi, polyAt_val hp.g_red hi] at hlt
  rw [h.f i hi, ite_eq_left hi, vec_zipWith_get _ _ _ hi, hG, polyAt_val hp.f_red hi, polyAt_val hp.g_red hi,
    newC, toNat_ofNat32 (by omega)]

/-- All-zero memory holds a reduced polynomial. -/
theorem reduced_of_zero {m : Mem} {p : Addr} (h : ∀ k < 1024, m (p + BitVec.ofNat 64 k) = 0) :
    Reduced m p := fun i hi => by
  rw [coeffAt_congr (m' := m) (m := fun _ => 0) (fun k hk => h k hk) hi]
  simp [coeffAt, Mem.readW, Mem.read]

/-- Memory whose argument words (at `0x5004`) hold `0` and `0x400`. -/
def accSatMem : Mem := fun a => if a = 0x5009 then 4 else 0

/-- A state satisfying the precondition: `f` at `0`, `g` at `0x400`. -/
def accSat : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := accSatMem
  rd := [⟨0x400, 1024⟩]
  wr := [⟨0, 1024⟩, ⟨0x5004, 8⟩]

theorem accSat_red (p : Nat) (hp : p + 1024 ≤ 0x5000) : Reduced accSatMem (BitVec.ofNat 64 p) :=
  reduced_of_zero fun k hk => by
    simp only [accSatMem]
    rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega)]

theorem add_verified : Verified X86.target add (addContract X86.abi 16) := by
  refine Piece.verified (((map_piece addOp_spec (NoSp.of_all (by decide +kernel)) (by taint_decide)).pre_mono
    (fun _ h => AccPre.of_add h) fun s s' _ _ h => by
      sig_pub [addContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [addContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact map_post (G := (· + ·)) (fun x y => val_add x y) (AccPre.of_add h₀) hinv
  · have a0 : arg accSat 0 = 0 := by decide
    have a1 : arg accSat 1 = 0x400 := by decide
    have e : argAddr accSat 0 = 0x5004 := by decide
    have esp : accSat.gpr .esp = 0x5000 := rfl
    refine ⟨accSat, ?_⟩
    sig_pre [addContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, e, esp]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide,
      accSat_red 0 (by decide), accSat_red 0x400 (by decide)⟩ <;>
    exact Region.disjoint_of_sep (by decide)

theorem sub_verified : Verified X86.target sub (subContract X86.abi 16) := by
  refine Piece.verified (((map_piece subOp_spec (NoSp.of_all (by decide +kernel)) (by taint_decide)).pre_mono
    (fun _ h => AccPre.of_sub h) fun s s' _ _ h => by
      sig_pub [subContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [subContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact map_post (G := (· - ·)) (fun x y => val_sub x y) (AccPre.of_sub h₀) hinv
  · have a0 : arg accSat 0 = 0 := by decide
    have a1 : arg accSat 1 = 0x400 := by decide
    have e : argAddr accSat 0 = 0x5004 := by decide
    have esp : accSat.gpr .esp = 0x5000 := rfl
    refine ⟨accSat, ?_⟩
    sig_pre [subContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, e, esp]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide,
      accSat_red 0 (by decide), accSat_red 0x400 (by decide)⟩ <;>
    exact Region.disjoint_of_sep (by decide)
end VG.Proof.MlKem.X86
