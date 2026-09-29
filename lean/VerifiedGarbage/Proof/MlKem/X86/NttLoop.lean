import VerifiedGarbage.Proof.MlKem.X86.Bfly
import VerifiedGarbage.Proof.MlKem.X86.Table
import VerifiedGarbage.Proof.MlKem.X86.Leaf
import VerifiedGarbage.Spec.MlKem.Poly

/-!
# ML-KEM on x86 (32-bit): the layers of the NTT and its inverse

Untrusted: everything here is checked by Lean. A layer
(`Impl.MlKem.X86.layerCode body dz len`) is a loop over its blocks, each a
loop of butterflies `body`; this file proves it once for any butterfly that
computes a function `op` of the polynomial (`Bfly`), with `ebp` moving up
(`dz = zUp`) or down (`zDown`) the zeta table, from its entry state `s₀`
(`vg_mlkem_ntt(f, scratch)` or `vg_mlkem_inv_ntt(f, scratch)`, after the
setup that stores the table in `scratch` and `f + 1024` in the argument
slot of `scratch`).

* `blockN op H len k start t`: the first `t` butterflies of a block;
  `layerN op kf P len c`: the first `c` blocks of a layer, block `c` with
  the zeta `kf len c` (as in `Ntt.lean`, of which these are `nttBlockN`,
  `nttLayerN` and their inverses).
* `MemOK s₀ G m`: memory holds `G` at `f`, the table, `f` and `f + 1024`
  in the argument slots, and differs from the entry only in `f`, `scratch`
  and the arguments.
-/

namespace VG.Proof.MlKem.X86.NttLoop

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem

section
variable (s₀ : State)
abbrev fP : BitVec 32 := arg s₀ 0
abbrev sP : BitVec 32 := arg s₀ 1
abbrev fA : Addr := (fP s₀).setWidth 64
abbrev sA : Addr := (sP s₀).setWidth 64
abbrev aR : Region := ⟨argAddr s₀ 0, 8⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 8 ≤ 2 ^ 32
  rd : s₀.rd = []
  wr : s₀.wr = [polyRegion (fA s₀), polyRegion (sA s₀), aR s₀]
  f_s : (polyRegion (fA s₀)).Disjoint (polyRegion (sA s₀))
  f_a : (polyRegion (fA s₀)).Disjoint (aR s₀)
  s_a : (polyRegion (sA s₀)).Disjoint (aR s₀)
  ret_f : (retR s₀).Disjoint (polyRegion (fA s₀))
  ret_s : (retR s₀).Disjoint (polyRegion (sA s₀))
  ret_a : (retR s₀).Disjoint (aR s₀)
  stk_f : (stkR s₀).Disjoint (polyRegion (fA s₀))
  stk_s : (stkR s₀).Disjoint (polyRegion (sA s₀))
  stk_a : (stkR s₀).Disjoint (aR s₀)
  f_fit : (fP s₀).toNat + 1024 ≤ 2 ^ 32
  s_fit : (sP s₀).toNat + 1024 ≤ 2 ^ 32
  f_red : Reduced s₀.mem (fA s₀)

def Pub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

theorem pub_esp {s₀ s₀' : State} (hq : Pub s₀ s₀') : (P0 s₀).gpr .esp = (P0 s₀').gpr .esp := by
  rw [P0_esp, P0_esp, hq.1]

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem stk_eq : stkR s₀ = frameR s₀ := by
  simp only [stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem arg_in {i : Nat} (hi : i < 2) : (aR s₀).Contains (argAddr s₀ i) 4 := by
  have := hp.sp'
  simp only [argAddr, Region.Contains, E0] at this ⊢
  bv_omega

theorem in_f {s : State} (hw : s.wr = (P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions s.wr (coeffAddr (fA s₀) k) 4 :=
  ⟨polyRegion (fA s₀), by rw [hw, P0_wr, hp.wr]; simp, coeff_contains _ (by rw [n_eq]; exact hk)⟩

theorem in_s {s : State} (hw : s.wr = (P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions s.wr (coeffAddr (sA s₀) k) 4 :=
  ⟨polyRegion (sA s₀), by rw [hw, P0_wr, hp.wr]; simp, coeff_contains _ (by rw [n_eq]; exact hk)⟩

theorem in_a {s : State} (hw : s.wr = (P0 s₀).wr) {i : Nat} (hi : i < 2) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 :=
  ⟨aR s₀, List.mem_append_right _ (by rw [hw, P0_wr, hp.wr]; simp), hp.arg_in hi⟩

/-- The push changes nothing of `f`, `scratch` or the arguments. -/
theorem P0_keep : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rw [saveRegs_len] at hf
  exact hf

end Pre

/-! ## Memory -/

/-- Memory during the layers, holding `G` at `f`. -/
structure MemOK (s₀ : State) (G : Poly) (m : Mem) : Prop where
  frame : Frame [polyRegion (fA s₀), polyRegion (sA s₀), aR s₀] (P0 s₀).mem m
  tbl : ∀ k < 128, coeffAt m (sA s₀) k = BitVec.ofNat 32 (zetas.getD k 0)
  arg0 : m.readW (argAddr s₀ 0) 32 = fP s₀
  slot : m.readW (argAddr s₀ 1) 32 = fP s₀ + 1024
  poly : PolyIs m (fA s₀) G

/-- Writes to `f` keep the rest. -/
theorem MemOK.step {s₀ : State} (hp : Pre s₀) {G G' : Poly} {m m' : Mem} (h : MemOK s₀ G m)
    (hf : Frame [polyRegion (fA s₀)] m m') (hG : PolyIs m' (fA s₀) G') : MemOK s₀ G' m' where
  frame := h.frame.trans (hf.mono fun r hr => by simp at hr ⊢; exact .inl hr)
  tbl k hk := by
    rw [coeffAt_congr (m := m) (fun j hj => hf.bytes (R := polyRegion (sA s₀))
      (by simpa using hp.f_s.symm) (polyLen _) hj) (by rw [n_eq]; omega)]
    exact h.tbl k hk
  arg0 := by rw [hf.readW (hp.arg_in (by decide)) (by simpa using hp.f_a.symm) (by decide)]; exact h.arg0
  slot := by rw [hf.readW (hp.arg_in (by decide)) (by simpa using hp.f_a.symm) (by decide)]; exact h.slot
  poly := hG

/-! ## The butterflies of a block -/

/-- A butterfly code and the function of the polynomial it computes. -/
structure Bfly where
  body : List Instr
  op : Poly → Nat → Nat → Zq → Poly
  spec : ∀ {s : State} {p : Addr} {G : Poly} {j len : Nat} {zA : Addr} {z : Nat},
    BIn s p G j len zA z → WP isa (.block body) s (BOut s p (op G j len (ofNat z)))

/-- The first `t` butterflies of a block. -/
def blockN (op : Poly → Nat → Nat → Zq → Poly) (f : Poly) (len k start t : Nat) : Poly :=
  (List.range' start t).foldl (fun f j => op f j len (zeta k)) f

theorem blockN_succ (op : Poly → Nat → Nat → Zq → Poly) (f : Poly) (len k start t : Nat) :
    blockN op f len k start (t + 1) = op (blockN op f len k start t) (start + t) len (zeta k) :=
  foldl_range'_succ _ _ _ _

/-- The first `c` blocks of a layer, block `c` with the zeta `kf len c`. -/
def layerN (op : Poly → Nat → Nat → Zq → Poly) (kf : Nat → Nat → Nat) (f : Poly) (len c : Nat) : Poly :=
  (List.range c).foldl (fun f c => blockN op f len (kf len c) (2 * len * c) len) f

theorem layerN_succ (op : Poly → Nat → Nat → Zq → Poly) (kf : Nat → Nat → Nat) (f : Poly) (len c : Nat) :
    layerN op kf f len (c + 1) = blockN op (layerN op kf f len c) len (kf len c) (2 * len * c) len :=
  foldl_range_succ _ _ _

/-- In a block: `t` butterflies done. -/
structure BL (s₀ : State) (op : Poly → Nat → Nat → Zq → Poly) (H : Poly) (len k start t : Nat)
    (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = fP s₀ + BitVec.ofNat 32 (4 * (start + t))
  edi : s.gpr .edi = fP s₀ + BitVec.ofNat 32 (4 * (start + len + t))
  ebp : s.gpr .ebp = sP s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (len - t)
  mem : MemOK s₀ (blockN op H len k start t) s.mem

theorem zetas_lt {k : Nat} (hk : k < 128) : zetas.getD k 0 < q := by
  rw [zetas_getD hk]; exact (zeta k).isLt

theorem bfly_step {s₀ : State} (hp : Pre s₀) (b : Bfly) {H : Poly} {len k start t : Nat}
    (hl : 0 < len) (hs : start + 2 * len ≤ 256) (hk : k < 128) (ht : t < len) {s : State}
    (h : BL s₀ b.op H len k start t s) :
    WP isa (.block b.body) s fun s' => BL s₀ b.op H len k start (t + 1) s' ∧
      eval .ne s' = some (decide (t + 1 < len)) := by
  have ff := hp.f_fit
  have fs := hp.s_fit
  have bin : BIn s (fA s₀) (blockN b.op H len k start t) (start + t) len (coeffAddr (sA s₀) k)
      (zetas.getD k 0) := {
    ea_i := by rw [h.esi, ea_add (by omega), Nat.add_zero]
    ea_d := by rw [h.edi, ea_add (by omega), Nat.add_zero]; congr 2; omega
    ea_z := by rw [h.ebp, ea_add (by omega), Nat.add_zero]
    in_i := hp.in_f h.wr (by omega)
    in_d := hp.in_f h.wr (by omega)
    in_z := inRd (hp.in_s h.wr (by omega))
    z_v := by rw [← coeffAt_eq, h.mem.tbl k hk]
    z_lt := zetas_lt hk
    z_sep := hp.f_s.symm.sep (coeff_contains _ (by rw [n_eq]; omega)) (coeff_contains _ (by rw [n_eq]; omega))
    poly := h.mem.poly
    hj := by omega
    hl := hl }
  refine (b.spec bin).mono fun s' o => ⟨⟨?_, o.rd.trans h.rd, o.wr.trans h.wr, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [o.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.esp]
  · rw [o.esi, h.esi, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · rw [o.edi, h.edi, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · rw [o.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.ebp]
  · rw [o.ecx, h.ecx]; exact cnt_next ht
  · rw [blockN_succ, zeta_eq hk]
    exact h.mem.step hp o.frame o.poly
  · rw [o.ne, h.ecx]
    exact (Option.map_some (f := (!·)) _).symm.trans (cnt_ne ht (by omega))

/-! ## The blocks of a layer -/

/-- In a layer: `c` blocks done. -/
structure KL (s₀ : State) (op : Poly → Nat → Nat → Zq → Poly) (kf : Nat → Nat → Nat) (P : Poly)
    (len c : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = fP s₀ + BitVec.ofNat 32 (4 * (2 * len * c))
  ebp : s.gpr .ebp = sP s₀ + BitVec.ofNat 32 (4 * kf len c)
  mem : MemOK s₀ (layerN op kf P len c) s.mem

/-- Between layers. -/
structure LB (s₀ : State) (G : Poly) (z : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  ebp : s.gpr .ebp = sP s₀ + BitVec.ofNat 32 (4 * z)
  mem : MemOK s₀ G s.mem

variable (b : Bfly) (kf : Nat → Nat → Nat) (P : State → Poly)

theorem blockInit_piece (len c : Nat) {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr []) (.block (blockInit len)) hc).isSome = true) :
    Piece Pre Pub (fun s₀ s => KL s₀ b.op kf (P s₀) len c s)
      (fun s₀ s => BL s₀ b.op (layerN b.op kf (P s₀) len c) len (kf len c) (2 * len * c) 0 s)
      (.block (blockInit len)) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) ht
  apply WP.of_runBlock
  simp only [blockInit, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.map_some,
    Option.bind_some, State.setReg, arithFlags, State.setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨by simp [h.esp], h.rd, h.wr, by simp [h.esi], ?_, by simp [h.ebp], by simp, ?_⟩
  · simp only [show Reg.edi ≠ Reg.ecx by decide, ite_false, ite_true, h.esi]
    rw [add_ofNat_add]; congr 2; omega
  · rw [blockN, List.range'_zero, List.foldl_nil]; exact h.mem

theorem bflyLoop_piece (len c : Nat) (hl : 0 < len) (hs : 2 * len * c + 2 * len ≤ 256)
    (hk : kf len c < 128) {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp, .ecx]) (.block b.body) hc).isSome = true) :
    Piece Pre Pub
      (fun s₀ s => BL s₀ b.op (layerN b.op kf (P s₀) len c) len (kf len c) (2 * len * c) 0 s)
      (fun s₀ s => BL s₀ b.op (layerN b.op kf (P s₀) len c) len (kf len c) (2 * len * c) len s)
      (.loop (.block b.body) .ne) :=
  Piece.countLoop hl (fun t s₀ s => BL s₀ b.op (layerN b.op kf (P s₀) len c) len (kf len c) (2 * len * c) t s)
    [.esp, .esi, .edi, .ebp, .ecx]
    (fun t ht s₀ s hp h => bfly_step hp b hl hs hk ht h)
    (fun t _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.esp, h'.esp, pub_esp hq]
      · rw [h.esi, h'.esi, fP, fP, hq.2.1]
      · rw [h.edi, h'.edi, fP, fP, hq.2.1]
      · rw [h.ebp, h'.ebp, sP, sP, hq.2.2]
      · rw [h.ecx, h'.ecx]) ht

/-- `ebp` moves up (`zUp`) or down (`zDown`) to the next zeta. -/
def dzOf (up : Bool) : Instr := if up then zUp else zDown

theorem ptr_prev (x : BitVec 32) {a b : Nat} (h : b ≤ a) :
    x + BitVec.ofNat 32 a - BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a - b) := by
  rw [show x + BitVec.ofNat 32 a = x + BitVec.ofNat 32 (a - b) + BitVec.ofNat 32 b by
    rw [add_ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

/-- The loop over blocks goes on while blocks are left. -/
theorem blk_cond {len B c : Nat} (hB : len * B = 128) (hc : c < B) :
    (!decide (4 * (2 * len * c + len + len) = 1024)) = decide (c + 1 < B) := by
  have hl : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h | h
    · rw [h, Nat.zero_mul] at hB; exact absurd hB (by decide)
    · exact h
  have e : 4 * (2 * len * c + len + len) = 8 * (len * (c + 1)) := by
    rw [Nat.mul_succ, Nat.mul_assoc 2]; omega
  rw [e]
  by_cases h : c + 1 = B
  · rw [h, hB]; simp
  · have hlt : len * (c + 1) < len * B := Nat.mul_lt_mul_of_pos_left (by omega) hl
    rw [hB] at hlt
    simp only [show ¬ 8 * (len * (c + 1)) = 1024 by omega, decide_false, Bool.not_false,
      show c + 1 < B by omega, decide_true]

/-- The pointer compared with the end of `f`. -/
theorem end_cmp (x : BitVec 32) {X : Nat} (hX : X ≤ 1024) :
    (x + BitVec.ofNat 32 X - (x + 1024) == 0) = decide (X = 1024) := by
  rw [sub_beq_zero, BitVec.toNat_add, BitVec.toNat_add, toNat_ofNat32 (by omega),
    show (1024 : BitVec 32).toNat = 1024 from rfl]
  simp only [Nat.reducePow]
  exact decide_eq_decide.mpr (by constructor <;> intro h <;> omega)

theorem blockEnd_piece (up : Bool) (len c B : Nat) (hB : len * B = 128) (hc : c < B)
    (hkf : kf len (c + 1) = if up then kf len c + 1 else kf len c - 1)
    (hk : up = false → 1 ≤ kf len c) {hh : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp]) (.block (blockEnd (dzOf up))) hh).isSome = true) :
    Piece Pre Pub
      (fun s₀ s => BL s₀ b.op (layerN b.op kf (P s₀) len c) len (kf len c) (2 * len * c) len s)
      (fun s₀ s => KL s₀ b.op kf (P s₀) len (c + 1) s ∧ eval .ne s = some (decide (c + 1 < B)))
      (.block (blockEnd (dzOf up))) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) ht
  · have ff := hp.f_fit
    have hsl : (s.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = argAddr s₀ 1 := by
      rw [h.esp]; exact P0_argAddr s₀ 1
    have ins : InRegions (s.rd ++ s.wr) (argAddr s₀ 1) 4 := hp.in_a h.wr (by decide)
    have hlc : 2 * len * c + 2 * len ≤ 256 := by
      have : len * (c + 1) ≤ len * B := Nat.mul_le_mul_left _ hc
      rw [Nat.mul_succ] at this; rw [Nat.mul_assoc]; omega
    apply WP.of_runBlock
    cases up
    all_goals
      simp (config := {decide := true}) only [blockEnd, dzOf, zUp, zDown, runBlock_cons, runStep_some,
        runBlock_nil, exec, execAlu, readSrc, Option.map_some, Option.bind_some, State.setReg, arithFlags,
        State.setFlags, State.ea, at_, State.load32, hsl, ins, h.mem.slot, ite_true, ite_false,
        Option.some.injEq, exists_eq_left']
      refine ⟨⟨by simp [h.esp], h.rd, h.wr, ?_, ?_, ?_⟩, ?_⟩
    · simp only [show Reg.esi ≠ Reg.ebp by decide, ite_false, ite_true, h.edi]
      congr 2; rw [Nat.mul_succ]; omega
    · simp only [ite_true, h.ebp, hkf, Bool.false_eq_true, ite_false]
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ptr_prev _ (by have := hk rfl; omega)]
      congr 2; have := hk rfl; omega
    · rw [layerN_succ]; exact h.mem
    · simp only [eval, Option.map_some, h.edi]
      rw [end_cmp _ (by omega), blk_cond hB hc]
    · simp only [show Reg.esi ≠ Reg.ebp by decide, ite_false, ite_true, h.edi]
      congr 2; rw [Nat.mul_succ]; omega
    · simp only [ite_true, h.ebp, hkf, ite_true]
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
    · rw [layerN_succ]; exact h.mem
    · simp only [eval, Option.map_some, h.edi]
      rw [end_cmp _ (by omega), blk_cond hB hc]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, pub_esp hq]

theorem layer_piece (up : Bool) (len B : Nat) (hB : len * B = 128) (hBp : 0 < B)
    (hkf : ∀ c < B, kf len (c + 1) = if up then kf len c + 1 else kf len c - 1)
    (hk : ∀ c < B, kf len c < 128) (hk1 : up = false → ∀ c < B, 1 ≤ kf len c)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp 20))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr []) (.block (blockInit len)) h₂).isSome = true)
    {h₃ : Taint.Hint VG.X86.Taint.T}
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp, .ecx]) (.block b.body) h₃).isSome = true)
    {h₄ : Taint.Hint VG.X86.Taint.T}
    (t₄ : (VG.X86.taint.check (τr [.esp]) (.block (blockEnd (dzOf up))) h₄).isSome = true) :
    Piece Pre Pub (fun s₀ s => LB s₀ (P s₀) (kf len 0) s)
      (fun s₀ s => LB s₀ (layerN b.op kf (P s₀) len B) (kf len B) s) (layerCode b.body (dzOf up) len) := by
  have hl : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h | h
    · rw [h, Nat.zero_mul] at hB; exact absurd hB (by decide)
    · exact h
  refine Piece.seq (B := fun s₀ s => KL s₀ b.op kf (P s₀) len 0 s) ?_ ((Piece.loop
    (fun c s₀ s => KL s₀ b.op kf (P s₀) len c s) hBp fun c hc =>
      Piece.seq (blockInit_piece b kf P len c t₂) (Piece.seq (bflyLoop_piece b kf P len c hl ?_ (hk c hc) t₃)
        (blockEnd_piece b kf P up len c B hB hc (hkf c hc) (fun e => hk1 e c hc) t₄))).mono
    (fun _ _ _ h => h) fun _ _ _ h => ⟨h.esp, h.rd, h.wr, h.ebp, h.mem⟩)
  · refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) t₁
    · have hsl : (s.gpr .esp + BitVec.ofNat 32 20).setWidth 64 = argAddr s₀ 0 := by
        rw [h.esp]; exact P0_argAddr s₀ 0
      have ins : InRegions (s.rd ++ s.wr) (argAddr s₀ 0) 4 := hp.in_a h.wr (by decide)
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, State.setReg,
        State.ea, at_, State.load32, hsl, ins, h.mem.arg0, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨by simp [h.esp], h.rd, h.wr, by simp, by simp [h.ebp], ?_⟩
      rw [layerN, List.range_zero, List.foldl_nil]; exact h.mem
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [h.esp, h'.esp, pub_esp hq]
  · have : len * (c + 1) ≤ len * B := Nat.mul_le_mul_left _ hc
    rw [Nat.mul_succ] at this; rw [Nat.mul_assoc]; omega

end VG.Proof.MlKem.X86.NttLoop
