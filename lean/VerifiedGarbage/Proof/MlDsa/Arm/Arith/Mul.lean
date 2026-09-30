import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving
import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Mul

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

Untrusted: everything here is checked by Lean. The loop body is three
blocks, each symbolically executed once for any state: the loads and the
zPieces (`head_ok`), `mulz` (`mulz_ok`) and the rest (`tail_ok`,
`tailAdd_ok`); the loop invariant says which coefficients of `h` are done
(`Inv`), and `wp_saving` puts the loop in the frames that save `r4`–`r9`.
-/

namespace VG.Proof.MlDsa.Arm.Arith.Mul

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr inRegions_of)
open VG.Proof.MlDsa.Arm.Arith.AddSub (ptr_succ reduced_zero ctRegs)

/-! ## The loop body -/

/-- The registers the body does not write, of those it must preserve. -/
def Keep (s s' : State) : Prop := s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .r11 = s.gpr .r11 ∧ s'.gpr .lr = s.gpr .lr

theorem Keep.trans {s₁ s₂ s₃ : State} (h₁ : Keep s₁ s₂) (h₂ : Keep s₂ s₃) : Keep s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

theorem head_ok {s : State} {y w : BitVec 32} (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = w)
    (iF : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4)
    (iG : InRegions (s.rd ++ s.wr) (State.addr (w + BitVec.ofNat 32 0)) 4) :
    WP isa (.block ([.ldr .r12 .r1 0] ++ zPieces .r12 ++ [.ldr .r8 .r2 0])) s fun s' =>
      s'.gpr .r5 = s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32 >>> 14 ∧
      s'.gpr .r6 = s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32 <<< 18 >>> 25 ∧
      s'.gpr .r7 = s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32 <<< 25 >>> 25 ∧
      s'.gpr .r8 = s.mem.readW (State.addr (w + BitVec.ofNat 32 0)) 32 ∧
      (∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [zPieces, h1, h2, iF, iG]
  and_intros
  all_goals first | trivial | (intro r h5 h6 h7 h8 h12; simp [h5, h6, h7, h8, h12])

/-- What the rest of an iteration does, but for the value stored. -/
def Step (s : State) (x y w c v : BitVec 32) (s' : State) : Prop :=
  s'.gpr .r0 = x + 4 ∧ s'.gpr .r1 = y + 4 ∧ s'.gpr .r2 = w + 4 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
    s'.gpr .r4 = Qw ∧ Keep s s' ∧
    s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0)) v ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

section
variable {s : State} {x y w c p : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = w)
  (h3 : s.gpr .r3 = c) (h4 : s.gpr .r4 = Qw) (h9 : s.gpr .r9 = p)
  (oH : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 h3 h4 h9 oH

theorem tail_ok : WP isa (.block (csub .r9 .r12 .r4 ++ [.str .r9 .r0 0] ++ step3)) s (Step s x y w c (bcsub p)) := by
  run_block [csub, fixup, step3, Step, Keep, bcsub, bfix, h0, h1, h2, h3, h4, h9, oH]

theorem tailAdd_ok (iH : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block ([.ldr .r8 .r0 0, .dp .add .r9 .r9 (.reg .r8)] ++ red .r9 .r12 .r4 ++
      csub .r9 .r12 .r4 ++ [.str .r9 .r0 0] ++ step3)) s
      (Step s x y w c (bcsub (bred (p + s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32)))) := by
  run_block [red, csub, fixup, step3, Step, Keep, bcsub, bfix, bred, h0, h1, h2, h3, h4, h9, oH, iH]

end

/-- The product of the coefficients at `y` and `w`, as `mulHead` leaves it. -/
abbrev prod (m : Mem) (y w : BitVec 32) : BitVec 32 :=
  let a := m.readW (State.addr (y + BitVec.ofNat 32 0)) 32
  bmulz (m.readW (State.addr (w + BitVec.ofNat 32 0)) 32) (a >>> 14) (a <<< 18 >>> 25) (a <<< 25 >>> 25)

section
variable {s : State} {x y w c : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = w)
  (h3 : s.gpr .r3 = c) (h4 : s.gpr .r4 = Qw)
  (iF : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4)
  (iG : InRegions (s.rd ++ s.wr) (State.addr (w + BitVec.ofNat 32 0)) 4)
  (oH : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 h3 h4 iF iG oH

omit oH in
/-- The head and `mulz`, and then `k`. -/
theorem headMul {Q : State → Prop}
    (k : ∀ s', s'.gpr .r0 = x → s'.gpr .r1 = y → s'.gpr .r2 = w → s'.gpr .r3 = c → s'.gpr .r4 = Qw →
      s'.gpr .r9 = prod s.mem y w → Keep s s' → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block (mulHead ++ [])) s Q := by
  rw [List.append_nil, mulHead, WP.block_append_iff]
  refine WP.mono (head_ok h1 h2 iF iG) fun s₁ ⟨e5, e6, e7, e8, eo, m₁, rd₁, wr₁, sp₁⟩ => ?_
  refine WP.mono (mulz_ok (by rw [eo _ (by decide) (by decide) (by decide) (by decide) (by decide), h4]) e5 e6 e7 e8)
    fun s₂ ⟨e9, eo₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  have g : ∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → r ≠ .r12 → s₂.gpr r = s.gpr r :=
    fun r a5 a6 a7 a8 a9 a12 => (eo₂ r a9 a12).trans (eo r a5 a6 a7 a8 a12)
  refine k s₂ ((g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0)
    ((g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1)
    ((g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2)
    ((g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h3)
    ((g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h4)
    e9 ⟨g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
    (m₂.trans m₁) (rd₂.trans rd₁) (wr₂.trans wr₁) (sp₂.trans sp₁)

theorem body_ok : WP isa (.block mulBody) s (Step s x y w c (bcsub (prod s.mem y w))) := by
  rw [mulBody, List.append_assoc, List.append_assoc, WP.block_append_iff, ← List.append_nil mulHead]
  refine headMul h0 h1 h2 h3 h4 iF iG fun s₂ e0 e1 e2 e3 e4 e9 eo m rd wr sp => ?_
  rw [← List.append_assoc]
  have iH' : InRegions s₂.wr (State.addr (x + BitVec.ofNat 32 0)) 4 := by rw [wr]; exact oH
  refine WP.mono (tail_ok e0 e1 e2 e3 e4 e9 iH') fun s' ⟨r0, r1, r2, r3, z, r4, ro, m', rd', wr', sp'⟩ =>
    ⟨r0, r1, r2, r3, z, r4, eo.trans ro, by rw [m', m], rd'.trans rd, wr'.trans wr,
      sp'.trans sp⟩

theorem bodyAdd_ok (iH : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block mulAddBody) s (Step s x y w c
      (bcsub (bred (prod s.mem y w + s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32)))) := by
  rw [mulAddBody, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff, ← List.append_nil mulHead]
  refine headMul h0 h1 h2 h3 h4 iF iG fun s₂ e0 e1 e2 e3 e4 e9 eo m rd wr sp => ?_
  simp only [← List.append_assoc]
  have iH' : InRegions s₂.wr (State.addr (x + BitVec.ofNat 32 0)) 4 := by rw [wr]; exact oH
  have iH'' : InRegions (s₂.rd ++ s₂.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 := by rw [wr, rd]; exact iH
  refine WP.mono (tailAdd_ok e0 e1 e2 e3 e4 e9 iH' iH'')
    fun s' ⟨r0, r1, r2, r3, z, r4, ro, m', rd', wr', sp'⟩ =>
    ⟨r0, r1, r2, r3, z, r4, eo.trans ro, by rw [m', m], rd'.trans rd, wr'.trans wr,
      sp'.trans sp⟩

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev ph : BitVec 32 := s₀.gpr .r0
abbrev pf : BitVec 32 := s₀.gpr .r1
abbrev pg : BitVec 32 := s₀.gpr .r2
abbrev H : Addr := State.addr (ph s₀)
abbrev F : Addr := State.addr (pf s₀)
abbrev G : Addr := State.addr (pg s₀)

end

/-- What the body's loop needs of the state it starts in. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (F s₀), polyRegion (G s₀)]
  wr : polyRegion (H s₀) ∈ s₀.wr
  hf : (polyRegion (H s₀)).Disjoint (polyRegion (F s₀))
  hg : (polyRegion (H s₀)).Disjoint (polyRegion (G s₀))
  fitH : (ph s₀).toNat + 1024 ≤ 2 ^ 32
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitG : (pg s₀).toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s₀.mem (F s₀)
  redG : Reduced s₀.mem (G s₀)

/-- After `i` iterations, writing `out j` to coefficient `j` of `h`. -/
structure Inv (out : Nat → BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = ph s₀ + BitVec.ofNat 32 (4 * i)
  r1 : s.gpr .r1 = pf s₀ + BitVec.ofNat 32 (4 * i)
  r2 : s.gpr .r2 = pg s₀ + BitVec.ofNat 32 (4 * i)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (256 - i))
  r4 : s.gpr .r4 = Qw
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : Keep s₀ s
  frame : Frame [polyRegion (H s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (H s₀) j = if j < i then out j else coeffAt s₀.mem (H s₀) j

/-- The facts about memory an iteration needs. -/
structure Acc (s₀ : State) (i : Nat) (s : State) : Prop where
  iF : InRegions (s.rd ++ s.wr) (State.addr (pf s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 4
  iG : InRegions (s.rd ++ s.wr) (State.addr (pg s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 4
  iH : InRegions (s.rd ++ s.wr) (State.addr (ph s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 4
  oH : InRegions s.wr (State.addr (ph s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 4
  vF : s.mem.readW (State.addr (pf s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (F s₀) i
  vG : s.mem.readW (State.addr (pg s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (G s₀) i
  vH : s.mem.readW (State.addr (ph s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (H s₀) i

theorem acc_of {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {s : State}
    (h : Inv out s₀ i s) : Acc s₀ i s := by
  have fF := hp.fitF
  have fG := hp.fitG
  have fH := hp.fitH
  have eF : State.addr (pf s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (F s₀) i :=
    addr_ptr _ _ _ (by omega)
  have eG : State.addr (pg s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (G s₀) i :=
    addr_ptr _ _ _ (by omega)
  have eH : State.addr (ph s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (H s₀) i :=
    addr_ptr _ _ _ (by omega)
  have cF := coeff_contains (F s₀) (i := i) hi
  have cG := coeff_contains (G s₀) (i := i) hi
  have cH := coeff_contains (H s₀) (i := i) hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eF, h.rd, h.wr, hp.rd]; exact inRegions_of (by simp) cF
  · rw [eG, h.rd, h.wr, hp.rd]; exact inRegions_of (by simp) cG
  · rw [eH, h.rd, h.wr]; exact inRegions_of (List.mem_append_right _ hp.wr) cH
  · rw [eH, h.wr]; exact inRegions_of hp.wr cH
  · rw [eF, ← coeffAt_eq]
    exact coeffAt_frame h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hf.symm) hi
  · rw [eG, ← coeffAt_eq]
    exact coeffAt_frame h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hg.symm) hi
  · rw [eH, ← coeffAt_eq, h.coeff i hi, ite_eq_right (Nat.lt_irrefl i)]

/-- One iteration, from the value the body stores. -/
theorem inv_step {out : Nat → BitVec 32} {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256)
    {s : State} (h : Inv out s₀ i s) {body : List Instr}
    (hb : WP isa (.block body) s (Step s (ph s₀ + BitVec.ofNat 32 (4 * i)) (pf s₀ + BitVec.ofNat 32 (4 * i))
      (pg s₀ + BitVec.ofNat 32 (4 * i)) (BitVec.ofNat 32 (1 * (256 - i))) (out i))) :
    WP isa (.block body) s fun s' => Inv out s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 256) := by
  have fH := hp.fitH
  have eH : State.addr (ph s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (H s₀) i :=
    addr_ptr _ _ _ (by omega)
  have cH := coeff_contains (H s₀) (i := i) hi
  refine WP.mono hb fun s' ⟨r0, r1, r2, r3, z, r4, ro, m, rd, wr, sp⟩ => ⟨⟨?_, ?_, ?_, ?_, r4,
    rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, h.keep.trans ro, ?_, ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 4 i
  · rw [r1]; exact ptr_succ _ 4 i
  · rw [r2]; exact ptr_succ _ 4 i
  · rw [r3]; exact count_sub (k := 1) hi
  · rw [m, eH]
    exact h.frame.writeW (List.mem_singleton_self _) _ cH
  · intro j hj
    rw [m, eH, coeffAt_writeW _ _ hj hi, h.coeff j hj]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right hij]
      by_cases hj' : j < i
      · rw [ite_eq_left hj', ite_eq_left (by omega)]
      · rw [ite_eq_right hj', ite_eq_right (by omega)]
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

/-- The loop, after `q` is loaded. -/
theorem loop_ok {out : Nat → BitVec 32} {s₀ : State} {body : List Instr}
    (hb : ∀ i < 256, ∀ s, Inv out s₀ i s → WP isa (.block body) s fun s' =>
      Inv out s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 256)) :
    WP isa (.seq (.block (loadQ .r4 ++ [.mov .r3 (.imm 256)])) (.loop (.block body) .ne)) s₀ (Inv out s₀ 256) := by
  refine WP.seq (WP.of_runBlock ?_)
  refine ⟨_, by simp only [loadQ, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    exec, Op2.eval, isa]; rfl,
    wp_loop_ne (Inv out s₀) (N := 256) (by decide) hb (fun _ h => h) ?_⟩
  refine ⟨by simp [State.setReg], by simp [State.setReg], by simp [State.setReg], rfl, ?_, rfl, rfl, rfl,
    ⟨by simp [State.setReg], by simp [State.setReg], by simp [State.setReg]⟩, Frame.refl _ _, fun j _ => rfl⟩
  simp only [State.setReg]; exact loadQ_val

/-- The value stored in coefficient `j` by `vg_mldsa_multiply_ntt`. -/
def mulOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((multiplyNTT (polyAt s₀.mem (F s₀)) (polyAt s₀.mem (G s₀)))[j]!).val

/-- The value stored in coefficient `j` by `vg_mldsa_multiply_add_ntt`. -/
def mulAddOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((add (polyAt s₀.mem (H s₀)) (multiplyNTT (polyAt s₀.mem (F s₀)) (polyAt s₀.mem (G s₀))))[j]!).val

theorem prod_val {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {m : Mem} {y w : BitVec 32}
    (hy : m.readW (State.addr (y + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (F s₀) i)
    (hw : m.readW (State.addr (w + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (G s₀) i) :
    (bcsub (prod m y w)).toNat = ((multiplyNTT (polyAt s₀.mem (F s₀)) (polyAt s₀.mem (G s₀)))[i]!).val := by
  simp only [prod, hy, hw]
  rw [bcsub_mulz (hp.redG i hi) (hp.redF i hi), mul_get _ _ hi, val_mul, polyAt_val hp.redF hi,
    polyAt_val hp.redG hi, Nat.mul_comm]

theorem mul_hb {s₀ : State} (hp : Pre s₀) : ∀ i < 256, ∀ s, Inv (mulOut s₀) s₀ i s →
    WP isa (.block mulBody) s fun s' => Inv (mulOut s₀) s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 256) := by
  intro i hi s h
  have a := acc_of hp hi h
  refine inv_step hp hi h (WP.mono (body_ok h.r0 h.r1 h.r2 h.r3 h.r4 a.iF a.iG a.oH) fun s' hs => ?_)
  refine (?_ : _ = mulOut s₀ i) ▸ hs
  exact ofNat_val_eq (prod_val hp hi a.vF a.vG)

theorem mulAdd_hb {s₀ : State} (hp : Pre s₀) (hH : Reduced s₀.mem (H s₀)) :
    ∀ i < 256, ∀ s, Inv (mulAddOut s₀) s₀ i s →
    WP isa (.block mulAddBody) s fun s' => Inv (mulAddOut s₀) s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 256) := by
  intro i hi s h
  have a := acc_of hp hi h
  refine inv_step hp hi h (WP.mono (bodyAdd_ok h.r0 h.r1 h.r2 h.r3 h.r4 a.iF a.iG a.oH a.iH) fun s' hs => ?_)
  refine (?_ : _ = mulAddOut s₀ i) ▸ hs
  refine ofNat_val_eq ?_
  have hG := hp.redG i hi
  have hF := hp.redF i hi
  have hle := bmulz_le hG hF
  have hmod : (bmulz (coeffAt s₀.mem (G s₀) i) (coeffAt s₀.mem (F s₀) i >>> 14)
      (coeffAt s₀.mem (F s₀) i <<< 18 >>> 25) (coeffAt s₀.mem (F s₀) i <<< 25 >>> 25)).toNat % q =
      (coeffAt s₀.mem (G s₀) i).toNat * (coeffAt s₀.mem (F s₀) i).toNat % q := by
    rw [bmulz_toNat hG (Nat.lt_of_lt_of_le hF (by decide)), mulzN_mod]
  have hHi := hH i hi
  simp only [prod, a.vF, a.vG, a.vH] at hle ⊢
  generalize bmulz _ _ _ _ = P at hle hmod ⊢
  have hs : (P + coeffAt s₀.mem (H s₀) i).toNat = P.toNat + (coeffAt s₀.mem (H s₀) i).toNat := by
    unfold redMax at hle; rw [q_eq] at hHi; bv_omega
  have hr := red23_le (x := (P + coeffAt s₀.mem (H s₀) i).toNat) (BitVec.isLt _)
  rw [bcsub_toNat (by rw [bred_toNat]; exact Nat.lt_of_le_of_lt hr redMax_lt), bred_toNat, red23_mod, hs,
    add_get _ _ hi, val_add', mul_get _ _ hi, val_mul, polyAt_val hH hi, polyAt_val hp.redF hi,
    polyAt_val hp.redG hi, Nat.mul_comm (coeffAt s₀.mem (F s₀) i).toNat]
  generalize (coeffAt s₀.mem (G s₀) i).toNat * (coeffAt s₀.mem (F s₀) i).toNat = X at *
  rw [q_eq] at *
  omega

/-! ## Verified -/

/-- The precondition of both functions, on entry. -/
structure PreE (s : State) : Prop where
  sp : 24 ≤ s.sp.toNat
  rd : s.rd = [polyRegion (F s), polyRegion (G s)]
  wr : s.wr = [polyRegion (H s)]
  hf : (polyRegion (H s)).Disjoint (polyRegion (F s))
  hg : (polyRegion (H s)).Disjoint (polyRegion (G s))
  sH : (belowA s.sp 24).Disjoint (polyRegion (H s))
  sF : (belowA s.sp 24).Disjoint (polyRegion (F s))
  sG : (belowA s.sp 24).Disjoint (polyRegion (G s))
  fitH : (ph s).toNat + 1024 ≤ 2 ^ 32
  fitF : (pf s).toNat + 1024 ≤ 2 ^ 32
  fitG : (pg s).toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s.mem (F s)
  redG : Reduced s.mem (G s)

theorem pre_of {s : State} (h : (Spec.MlDsa.mulContract Arm.abi 24).pre s) : PreE s := by
  sig_pre [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem preAdd_of {s : State} (h : (Spec.MlDsa.mulAddContract Arm.abi 24).pre s) :
    PreE s ∧ Reduced s.mem (H s) := by
  sig_pre [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h0, h12, h13⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, h0⟩

/-- The loop's precondition, in the state after the pushes. -/
theorem pre_entry {s s₁ : State} (hp : PreE s) (hE : Entry 24 s s₁) :
    Pre s₁ ∧ polyAt s₁.mem (F s₁) = polyAt s.mem (F s) ∧ polyAt s₁.mem (G s₁) = polyAt s.mem (G s) ∧
      polyAt s₁.mem (H s₁) = polyAt s.mem (H s) ∧ (Reduced s.mem (H s) → Reduced s₁.mem (H s₁)) := by
  have g := hE.gpr
  have eF : F s₁ = F s := by simp only [F, pf, g]
  have eG : G s₁ = G s := by simp only [G, pg, g]
  have eH : H s₁ = H s := by simp only [H, ph, g]
  have fr := hE.frame
  have dF : ∀ r ∈ [belowA s.sp 24], (polyRegion (F s)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.sF.symm
  have dG : ∀ r ∈ [belowA s.sp 24], (polyRegion (G s)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.sG.symm
  have dH : ∀ r ∈ [belowA s.sp 24], (polyRegion (H s)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.sH.symm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [eF]; exact polyAt_frame fr dF,
    by rw [eG]; exact polyAt_frame fr dG, by rw [eH]; exact polyAt_frame fr dH,
    fun h => by rw [eH]; exact reduced_frame fr dH h⟩
  · rw [hE.rd, hp.rd, eF, eG]
  · rw [eH]; exact hE.wr _ (by rw [hp.wr]; exact List.mem_singleton_self _)
  · rw [eH, eF]; exact hp.hf
  · rw [eH, eG]; exact hp.hg
  · simp only [ph, g]; exact hp.fitH
  · simp only [pf, g]; exact hp.fitF
  · simp only [pg, g]; exact hp.fitG
  · rw [eF]; exact reduced_frame fr dF hp.redF
  · rw [eG]; exact reduced_frame fr dG hp.redG

theorem correct {s : State} (hp : PreE s) :
    WP isa Impl.MlDsa.Arm.Arith.mul s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (H s) (multiplyNTT (polyAt s.mem (F s)) (polyAt s.mem (G s))) := by
  refine WP.mono (wp_saving mulSaved _ (W := [polyRegion (H s)])
    (fun s₂ => Keep s s₂ ∧ PolyIs s₂.mem (H s) (multiplyNTT (polyAt s.mem (F s)) (polyAt s.mem (G s))))
    s hp.sp (fun R hR => by rw [List.mem_singleton] at hR; subst hR; exact hp.sH) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨hk, hq⟩, hm, _, hsp, _, hg⟩ => ⟨preserved_of_saving hg fun r hr hn => ?_, hsp, hm ▸ hq⟩
  · obtain ⟨hp₁, eF, eG, eH, -⟩ := pre_entry hp hE
    have eH' : H s₁ = H s := by simp only [H, ph, hE.gpr]
    refine WP.mono (loop_ok (mul_hb hp₁)) fun s₂ h => ⟨?_, ?_, ?_⟩
    · rw [← eH']; exact h.frame
    · have k := h.keep
      simp only [Keep, hE.gpr] at k ⊢
      exact k
    · rw [← eH', ← eF, ← eG]
      exact polyIs_of_toNat fun j hj => by
        rw [h.coeff j hj, ite_eq_left hj, mulOut, toNat_val]
  · simp only [preserved, mulSaved, List.mem_cons, List.not_mem_nil, or_false] at hr hn
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hn
    · exact hk.1
    · exact hk.2.1
    · exact hk.2.2

theorem correctAdd {s : State} (hp : PreE s) (hH : Reduced s.mem (H s)) :
    WP isa Impl.MlDsa.Arm.Arith.mulAdd s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (H s) (add (polyAt s.mem (H s)) (multiplyNTT (polyAt s.mem (F s)) (polyAt s.mem (G s)))) := by
  refine WP.mono (wp_saving mulSaved _ (W := [polyRegion (H s)])
    (fun s₂ => Keep s s₂ ∧
      PolyIs s₂.mem (H s) (add (polyAt s.mem (H s)) (multiplyNTT (polyAt s.mem (F s)) (polyAt s.mem (G s)))))
    s hp.sp (fun R hR => by rw [List.mem_singleton] at hR; subst hR; exact hp.sH) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨hk, hq⟩, hm, _, hsp, _, hg⟩ => ⟨preserved_of_saving hg fun r hr hn => ?_, hsp, hm ▸ hq⟩
  · obtain ⟨hp₁, eF, eG, eH, rH⟩ := pre_entry hp hE
    have eH' : H s₁ = H s := by simp only [H, ph, hE.gpr]
    refine WP.mono (loop_ok (mulAdd_hb hp₁ (rH hH))) fun s₂ h => ⟨?_, ?_, ?_⟩
    · rw [← eH']; exact h.frame
    · have k := h.keep
      simp only [Keep, hE.gpr] at k ⊢
      exact k
    · rw [← eH, ← eF, ← eG, ← eH']
      exact polyIs_of_toNat fun j hj => by
        rw [h.coeff j hj, ite_eq_left hj, mulAddOut, toNat_val]
  · simp only [preserved, mulSaved, List.mem_cons, List.not_mem_nil, or_false] at hr hn
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hn
    · exact hk.1
    · exact hk.2.1
    · exact hk.2.2

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem mul_verified : Verified Arm.target Impl.MlDsa.Arm.Arith.mul (Spec.MlDsa.mulContract Arm.abi 24) := by
  refine ⟨fun s hs => ?_, ct_of_saving mulSaved _ [.r0, .r1, .r2] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1, h2⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

theorem mulAdd_verified :
    Verified Arm.target Impl.MlDsa.Arm.Arith.mulAdd (Spec.MlDsa.mulAddContract Arm.abi 24) := by
  refine ⟨fun s hs => ?_, ct_of_saving mulSaved _ [.r0, .r1, .r2] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨hp, hH⟩ := preAdd_of hs
    obtain ⟨t, s', he, hpres, hsp, h⟩ := correctAdd hp hH
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1, h2⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Arith.Mul
