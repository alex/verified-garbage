import VerifiedGarbage.Proof.Blake2.Arm.CompressS.Exec

/-!
# BLAKE2s on ARMv7: the rounds

Untrusted: everything here is checked by Lean. `G`, executed once for any of
its registers and offsets (`wp_g`), and the rounds on the work vector: words
0–3 in `r0`–`r3`, words 4–7 rotated left by 7 in `r4`–`r7`, words 8–11 in
`scratch[64, 80)` and words 12–15 rotated left by 8 in `r8`–`r11` (`RI`).
-/

namespace VG.Proof.Blake2.ArmS

open VG VG.Arm
open VG.Impl.Blake2.Arm.S (wreg cOff g gAt round rounds)
open VG.Proof.Sha512.Arm (Only A A_eq)
open VG.Proof.MdStream.Arm (Upd Mupd wp_add wp_ldr wp_str op2_reg)
open VG.Spec.Blake2 (Work Block)

/-! ## One `G` -/

/-- What `G` leaves, from `s`, with the words `r` (`mix`'s order). -/
structure GOut (a b d : Reg) (V : BitVec 32) (c : Nat) (s s' : State)
    (r : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) : Prop where
  ra : s'.gpr a = r.1
  rb : s'.gpr b = r.2.1.rotateLeft 7
  rdd : s'.gpr d = r.2.2.2.rotateLeft 8
  other : ∀ q, q ≠ a → q ≠ b → q ≠ d → q ≠ .lr → s'.gpr q = s.gpr q
  mem : s'.mem = s.mem.writeW (A V (cOff c)) r.2.2.1
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_g {a b d : Reg} {c x y : Nat} {V : BitVec 32}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (haS : a ≠ .r12) (hbS : b ≠ .r12) (hdS : d ≠ .r12) (haT : a ≠ .lr) (hbT : b ≠ .lr) (hdT : d ≠ .lr)
    (hc : cOff c < 4096) (hx : 4 * x < 4096) (hy : 4 * y < 4096) (hV : s.gpr .r12 = V)
    (iX : InRegions (s.rd ++ s.wr) (A V (4 * x)) 4) (iY : InRegions (s.rd ++ s.wr) (A V (4 * y)) 4)
    (oC : InRegions s.wr (A V (cOff c)) 4)
    (K : ∀ s', GOut a b d V c s s' (Proof.Blake2.mix Spec.Blake2.s (s.gpr a) ((s.gpr b).rotateRight 7)
      (s.mem.readW (A V (cOff c)) 32) ((s.gpr d).rotateRight 8) (s.mem.readW (A V (4 * x)) 32)
      (s.mem.readW (A V (4 * y)) 32)) → WP isa (.block rest) s' Q) :
    WP isa (.block (g a b d c x y ++ rest)) s Q := by
  have iC : InRegions (s.rd ++ s.wr) (A V (cOff c)) 4 :=
    let ⟨r, hr, h⟩ := oC; ⟨r, List.mem_append_right _ hr, h⟩
  simp only [g, Impl.Blake2.Arm.S.T, Impl.Blake2.Arm.S.S, List.cons_append, List.nil_append]
  refine wp_ldr hx (by rw [hV]) iX fun s₁ u₁ => ?_
  refine wp_add (op2_ror (by decide)) fun s₂ u₂ => ?_
  refine wp_add (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_eor (op2_ror (by decide)) fun s₄ u₄ => ?_
  have hS : ∀ q : Reg, q ≠ .lr → q ≠ a → q ≠ d → s₄.gpr q = s.gpr q := fun q h1 h2 h3 => by
    rw [u₄.other q h3, u₃.other q h2, u₂.other q h2, u₁.other q h1]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_ldr hy (by rw [hS _ (by decide) (Ne.symm haS) (Ne.symm hdS), hV])
    (by rw [rd₄, wr₄]; exact iY) fun s₅ u₅ => ?_
  refine wp_add (op2_reg _ _) fun s₆ u₆ => ?_
  refine wp_ldr hc (by rw [u₆.other _ (Ne.symm haS), u₅.other _ (by decide),
      hS _ (by decide) (Ne.symm haS) (Ne.symm hdS), hV])
    (by rw [u₆.rd, u₅.rd, rd₄, u₆.wr, u₅.wr, wr₄]; exact iC) fun s₇ u₇ => ?_
  refine wp_add (op2_ror (by decide)) fun s₈ u₈ => ?_
  refine wp_eor (op2_ror (by decide)) fun s₉ u₉ => ?_
  refine wp_add (op2_ror (by decide)) fun s₁₀ u₁₀ => ?_
  refine wp_eor (op2_ror (by decide)) fun s₁₁ u₁₁ => ?_
  refine wp_add (op2_ror (by decide)) fun s₁₂ u₁₂ => ?_
  refine wp_eor (op2_ror (by decide)) fun s₁₃ u₁₃ => ?_
  have hS' : ∀ q : Reg, q ≠ .lr → q ≠ a → q ≠ b → q ≠ d → s₁₃.gpr q = s.gpr q := fun q h1 h2 h3 h4 => by
    rw [u₁₃.other q h3, u₁₂.other q h1, u₁₁.other q h4, u₁₀.other q h2, u₉.other q h3, u₈.other q h1,
      u₇.other q h1, u₆.other q h2, u₅.other q h1, hS q h1 h2 h4]
  have m₁₃ : s₁₃.mem = s.mem := by
    rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄]
  refine wp_str hc (by rw [hS' _ (by decide) (Ne.symm haS) (Ne.symm hbS) (Ne.symm hdS), hV])
    (by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄]; exact oC)
    fun s₁₄ m₁₄ => K s₁₄ ?_
  -- The registers, step by step.
  have v2 : s₂.gpr a = s.gpr a + (s.gpr b).rotateRight 7 := by rw [u₂.gpr, u₁.other a haT, u₁.other b hbT]
  have a3 : s₃.gpr a = s.gpr a + (s.gpr b).rotateRight 7 + s.mem.readW (A V (4 * x)) 32 := by
    rw [u₃.gpr, v2, u₂.other .lr (Ne.symm haT), u₁.gpr]
  have b3 : s₃.gpr b = s.gpr b := by rw [u₃.other b (Ne.symm hab), u₂.other b (Ne.symm hab), u₁.other b hbT]
  have d3 : s₃.gpr d = s.gpr d := by rw [u₃.other d (Ne.symm had), u₂.other d (Ne.symm had), u₁.other d hdT]
  have e4 : s₄.gpr d = s₃.gpr a ^^^ (s.gpr d).rotateRight 8 := by rw [u₄.gpr, d3]
  have a4 : s₄.gpr a = s₃.gpr a := u₄.other a had
  have b4 : s₄.gpr b = s.gpr b := by rw [u₄.other b hbd, b3]
  have a6 : s₆.gpr a = s₃.gpr a + s.mem.readW (A V (4 * y)) 32 := by
    rw [u₆.gpr, u₅.other a haT, a4, u₅.gpr, m₄]
  have c7 : s₇.gpr .lr = s.mem.readW (A V (cOff c)) 32 := by rw [u₇.gpr, u₆.mem, u₅.mem, m₄]
  have d7 : s₇.gpr d = s₄.gpr d := by rw [u₇.other d hdT, u₆.other d (Ne.symm had), u₅.other d hdT]
  have b7 : s₇.gpr b = s.gpr b := by rw [u₇.other b hbT, u₆.other b (Ne.symm hab), u₅.other b hbT, b4]
  have a7 : s₇.gpr a = s₆.gpr a := u₇.other a haT
  have c8 : s₈.gpr .lr = s.mem.readW (A V (cOff c)) 32 + (s₄.gpr d).rotateRight 16 := by
    rw [u₈.gpr, c7, d7]
  have f9 : s₉.gpr b = s₈.gpr .lr ^^^ (s.gpr b).rotateRight 7 := by rw [u₉.gpr, u₈.other b hbT, b7]
  have a9 : s₉.gpr a = s₆.gpr a := by rw [u₉.other a hab, u₈.other a haT, a7]
  have d9 : s₉.gpr d = s₄.gpr d := by rw [u₉.other d (Ne.symm hbd), u₈.other d hdT, d7]
  have c9 : s₉.gpr .lr = s₈.gpr .lr := u₉.other .lr (Ne.symm hbT)
  have a10 : s₁₀.gpr a = s₆.gpr a + (s₉.gpr b).rotateRight 12 := by rw [u₁₀.gpr, a9]
  have d10 : s₁₀.gpr d = s₄.gpr d := by rw [u₁₀.other d (Ne.symm had), d9]
  have b10 : s₁₀.gpr b = s₉.gpr b := u₁₀.other b (Ne.symm hab)
  have c10 : s₁₀.gpr .lr = s₈.gpr .lr := by rw [u₁₀.other .lr (Ne.symm haT), c9]
  have e11 : s₁₁.gpr d = s₁₀.gpr a ^^^ (s₄.gpr d).rotateRight 16 := by rw [u₁₁.gpr, d10]
  have a11 : s₁₁.gpr a = s₁₀.gpr a := u₁₁.other a had
  have b11 : s₁₁.gpr b = s₉.gpr b := by rw [u₁₁.other b hbd, b10]
  have c11 : s₁₁.gpr .lr = s₈.gpr .lr := by rw [u₁₁.other .lr (Ne.symm hdT), c10]
  have c12 : s₁₂.gpr .lr = s₈.gpr .lr + (s₁₁.gpr d).rotateRight 8 := by rw [u₁₂.gpr, c11]
  have a12 : s₁₂.gpr a = s₁₀.gpr a := by rw [u₁₂.other a haT, a11]
  have b12 : s₁₂.gpr b = s₉.gpr b := by rw [u₁₂.other b hbT, b11]
  have d12 : s₁₂.gpr d = s₁₁.gpr d := u₁₂.other d hdT
  have f13 : s₁₃.gpr b = s₁₂.gpr .lr ^^^ (s₉.gpr b).rotateRight 12 := by rw [u₁₃.gpr, b12]
  have a13 : s₁₃.gpr a = s₁₀.gpr a := by rw [u₁₃.other a hab, a12]
  have d13 : s₁₃.gpr d = s₁₁.gpr d := by rw [u₁₃.other d (Ne.symm hbd), d12]
  have c13 : s₁₃.gpr .lr = s₁₂.gpr .lr := u₁₃.other .lr (Ne.symm hbT)
  rw [mix_s]
  refine ⟨?_, ?_, ?_, fun q h1 h2 h3 h4 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₁₄.gpr, a13, a10, a6, f9, c8, e4, a3]
  · rw [m₁₄.gpr, f13, c12, f9, c8, e11, a10, a6, f9, c8, e4, a3, rotl_rotr _ (by decide)]
  · rw [m₁₄.gpr, d13, e11, a10, a6, f9, c8, e4, a3, rotl_rotr _ (by decide)]
  · rw [m₁₄.gpr, hS' q h4 h1 h2 h3]
  · rw [m₁₄.mem, m₁₃, c13, c12, e11, a10, a6, f9, c8, e4, a3]
  · rw [m₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd₄]
  · rw [m₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄]
  · rw [m₁₄.sp, u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp,
      u₁.sp]

end

/-! ## The work vector -/

/-- Word `k` of the work vector is `x`: in its register (rotated for words
4–7 and 12–15) or, for words 8–11, in `scratch`. -/
def Holds (V : BitVec 32) (s : State) (k : Nat) (x : BitVec 32) : Prop :=
  if k < 4 then s.gpr (wreg k) = x
  else if k < 8 then s.gpr (wreg k) = x.rotateLeft 7
  else if k < 12 then s.mem.readW (A V (cOff k)) 32 = x
  else s.gpr (wreg k) = x.rotateLeft 8

theorem holds_lo {V : BitVec 32} {s : State} {k : Nat} {x : BitVec 32} (h : k < 4) :
    Holds V s k x ↔ s.gpr (wreg k) = x := by simp only [Holds, h, ↓reduceIte]

theorem holds_mid {V : BitVec 32} {s : State} {k : Nat} {x : BitVec 32} (h₁ : 4 ≤ k) (h₂ : k < 8) :
    Holds V s k x ↔ s.gpr (wreg k) = x.rotateLeft 7 := by
  simp only [Holds, show ¬ k < 4 by omega, h₂, ↓reduceIte]

theorem holds_c {V : BitVec 32} {s : State} {k : Nat} {x : BitVec 32} (h₁ : 8 ≤ k) (h₂ : k < 12) :
    Holds V s k x ↔ s.mem.readW (A V (cOff k)) 32 = x := by
  simp only [Holds, show ¬ k < 4 by omega, show ¬ k < 8 by omega, h₂, ↓reduceIte]

theorem holds_hi {V : BitVec 32} {s : State} {k : Nat} {x : BitVec 32} (h₁ : 12 ≤ k) :
    Holds V s k x ↔ s.gpr (wreg k) = x.rotateLeft 8 := by
  simp only [Holds, show ¬ k < 4 by omega, show ¬ k < 8 by omega, show ¬ k < 12 by omega, ↓reduceIte]

/-- Words 8–11 of the work vector, in `scratch[64, 80)`. -/
abbrev cR (V : BitVec 32) : Region := ⟨State.addr V + BitVec.ofNat 64 64, 16⟩

/-- What the rounds need of the state `s₀` at their start: the scratch space
at `V` (in `r12`), holding the message block `M` in its first 64 bytes. -/
structure RCtx (V : BitVec 32) (M : Block 32) (s₀ : State) : Prop where
  r12 : s₀.gpr .r12 = V
  fitV : V.toNat + 512 ≤ 2 ^ 32
  wV : ∀ o, o + 4 ≤ 512 → InRegions s₀.wr (A V o) 4
  msg : ∀ j (hj : j < 16), s₀.mem.readW (A V (4 * j)) 32 = M ⟨j, hj⟩

/-- The rounds invariant, relative to the state `s₀` at their start: the work
vector is `v`, and nothing else has changed but `lr`, `r0`–`r11` and
`scratch[64, 80)`. -/
structure RI (V : BitVec 32) (s₀ : State) (v : Work 32) (s : State) : Prop where
  vars : ∀ k (hk : k < 16), Holds V s k v[k]
  r12 : s.gpr .r12 = s₀.gpr .r12
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [cR V] s₀.mem s.mem

theorem wreg_ne : ∀ k < 16, wreg k ≠ .r12 ∧ wreg k ≠ .lr := by decide

theorem wreg_inj' : ∀ k < 16, ∀ j < 16, wreg k = wreg j → k = j ∨ (8 ≤ k ∧ k < 12) ∨ (8 ≤ j ∧ j < 12) := by
  decide

theorem wreg_inj (k : Nat) (hk : k < 16) (j : Nat) (hj : j < 16) (h₁ : ¬ (8 ≤ k ∧ k < 12))
    (h₂ : ¬ (8 ≤ j ∧ j < 12)) (e : wreg k = wreg j) : k = j := by
  rcases wreg_inj' k hk j hj e with h | h | h
  · exact h
  · exact absurd h h₁
  · exact absurd h h₂

theorem cOff_A {V : BitVec 32} (fit : V.toNat + 512 ≤ 2 ^ 32) {o : Nat} (ho : o < 512) :
    A V o = State.addr V + BitVec.ofNat 64 o := A_eq (by omega)

theorem gAt_ok {x y z u : Nat} (hx : x < 4) (hy₁ : 4 ≤ y) (hy : y < 8) (hz₁ : 8 ≤ z) (hz : z < 12)
    (hu₁ : 12 ≤ u) (hu : u < 16) (r i : Nat) {V : BitVec 32} {M : Block 32} {s₀ s : State}
    {v : Work 32} (c : RCtx V M s₀) (h : RI V s₀ v s) :
    WP isa (gAt r i x y z u) s (RI V s₀ (Spec.Blake2.G Spec.Blake2.s v ⟨x, by omega⟩ ⟨y, by omega⟩
      ⟨z, by omega⟩ ⟨u, hu⟩ (M (Spec.Blake2.sigmaAt r (2 * i))) (M (Spec.Blake2.sigmaAt r (2 * i + 1))))) := by
  have sj := (Spec.Blake2.sigmaAt r (2 * i)).isLt
  have sk := (Spec.Blake2.sigmaAt r (2 * i + 1)).isLt
  have fitV := c.fitV
  have nx := wreg_ne x (by omega)
  have ny := wreg_ne y (by omega)
  have nu := wreg_ne u (by omega)
  have ixy : wreg x ≠ wreg y := fun e => absurd (wreg_inj x (by omega) y (by omega) (by omega) (by omega) e)
    (by omega)
  have ixu : wreg x ≠ wreg u := fun e => absurd (wreg_inj x (by omega) u (by omega) (by omega) (by omega) e)
    (by omega)
  have iyu : wreg y ≠ wreg u := fun e => absurd (wreg_inj y (by omega) u (by omega) (by omega) (by omega) e)
    (by omega)
  have hcz : cOff z < 4096 := by unfold cOff; omega
  have hV : s.gpr .r12 = V := by rw [h.r12, c.r12]
  -- The message words are unchanged.
  have hm : ∀ j (hj : j < 16), s.mem.readW (A V (4 * j)) 32 = M ⟨j, hj⟩ := fun j hj => by
    rw [← c.msg j hj, cOff_A fitV (by omega)]
    refine h.frame.readW (r := ⟨State.addr V, 64⟩) (Offset.contains_base _ (by omega) (by omega)) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    exact (Offset.disjoint_base _ (by omega) (by omega)).symm
  have iV : ∀ o, o + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (A V o) 4 := fun o ho =>
    let ⟨r, hr, hc⟩ := c.wV o ho; ⟨r, List.mem_append_right _ (by rw [h.wr]; exact hr), hc⟩
  unfold gAt
  rw [← List.append_nil (g _ _ _ _ _ _)]
  refine wp_g ixy ixu iyu nx.1 ny.1 nu.1 nx.2 ny.2 nu.2 hcz (by omega) (by omega) hV
    (iV _ (by omega)) (iV _ (by omega)) (by rw [h.wr]; exact c.wV _ (by unfold cOff; omega))
    fun s' w => WP.block_nil ?_
  have va : s.gpr (wreg x) = v[x] := (holds_lo hx).mp (h.vars x (by omega))
  have vb : (s.gpr (wreg y)).rotateRight 7 = v[y] := by
    rw [(holds_mid hy₁ hy).mp (h.vars y (by omega)), rotr_rotl _ (by decide)]
  have vc : s.mem.readW (A V (cOff z)) 32 = v[z] := (holds_c hz₁ hz).mp (h.vars z (by omega))
  have vd : (s.gpr (wreg u)).rotateRight 8 = v[u] := by
    rw [(holds_hi hu₁).mp (h.vars u hu), rotr_rotl _ (by decide)]
  rw [va, vb, vc, vd, hm _ sj, hm _ sk] at w
  have hwm : ∀ k, 8 ≤ k → k < 12 → k ≠ z →
      s'.mem.readW (A V (cOff k)) 32 = s.mem.readW (A V (cOff k)) 32 := fun k h1 h2 hk => by
    rw [w.mem, cOff_A fitV (by unfold cOff; omega), cOff_A fitV (by unfold cOff; omega)]
    exact Mem.readW_writeW_sep (Offset.sep _ (by unfold cOff; omega) (by unfold cOff; omega)
      (by unfold cOff; omega)) (by decide)
  refine ⟨fun k hk => ?_, by rw [w.other _ (Ne.symm nx.1) (Ne.symm ny.1) (Ne.symm nu.1) (by decide), h.r12],
    by rw [w.rd, h.rd], by rw [w.wr, h.wr], by rw [w.sp, h.sp], ?_⟩
  · rw [Proof.Blake2.G_get _ v (a := ⟨x, by omega⟩) (b := ⟨y, by omega⟩) (c := ⟨z, by omega⟩) (d := ⟨u, hu⟩)
      (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
      (by dsimp only; omega) (by dsimp only; omega) _ _ k hk]
    simp only [Fin.getElem_fin]
    by_cases ey : y = k
    · subst ey; simp only [↓reduceIte]; exact (holds_mid hy₁ hy).mpr w.rb
    by_cases ez : z = k
    · subst ez; simp only [ey, ↓reduceIte]
      exact (holds_c hz₁ hz).mpr (by rw [w.mem]; exact Mem.readW_writeW_self32 _ _ _)
    by_cases eu : u = k
    · subst eu; simp only [ey, ez, ↓reduceIte]; exact (holds_hi hu₁).mpr w.rdd
    by_cases ex : x = k
    · subst ex; simp only [ey, ez, eu, ↓reduceIte]; exact (holds_lo hx).mpr w.ra
    simp only [ey, ez, eu, ex, ↓reduceIte]
    have hv := h.vars k hk
    by_cases hc8 : 8 ≤ k ∧ k < 12
    · rw [holds_c hc8.1 hc8.2] at hv ⊢; rw [hwm k hc8.1 hc8.2 (Ne.symm ez), hv]
    · have hn : ∀ j < 16, ¬ (8 ≤ j ∧ j < 12) → j ≠ k → wreg k ≠ wreg j := fun j hj hj' hjk e =>
        hjk (wreg_inj k hk j hj hc8 hj' e).symm
      have ho : s'.gpr (wreg k) = s.gpr (wreg k) :=
        w.other _ (hn x (by omega) (by omega) ex) (hn y (by omega) (by omega) ey) (hn u hu (by omega) eu)
          (wreg_ne k hk).2
      unfold Holds at hv ⊢
      split <;> [rw [ho]; skip] <;> rename_i h4 <;> simp only [h4, ↓reduceIte] at hv
      · exact hv
      split <;> [rw [ho]; skip] <;> rename_i h8 <;> simp only [h8, ↓reduceIte] at hv
      · exact hv
      simp only [show ¬ k < 12 by omega, ↓reduceIte] at hv ⊢; rw [ho]; exact hv
  · rw [w.mem]
    refine h.frame.writeW (List.mem_singleton_self _) _ ?_
    rw [cOff_A fitV (by unfold cOff; omega)]
    exact Offset.contains _ (by unfold cOff; omega) (by unfold cOff; omega) (by omega)

section
open VG.Spec.Blake2 (G sigmaAt s)

/-- A round, as the eight `G`s `round` runs. -/
theorem round_eq (M : Block 32) (v : Work 32) (r : Nat) :
    Spec.Blake2.round s M v r =
      G s (G s (G s (G s (G s (G s (G s (G s v
        ⟨0, by decide⟩ ⟨4, by decide⟩ ⟨8, by decide⟩ ⟨12, by decide⟩ (M (sigmaAt r (2 * 0)))
          (M (sigmaAt r (2 * 0 + 1))))
        ⟨1, by decide⟩ ⟨5, by decide⟩ ⟨9, by decide⟩ ⟨13, by decide⟩ (M (sigmaAt r (2 * 1)))
          (M (sigmaAt r (2 * 1 + 1))))
        ⟨2, by decide⟩ ⟨6, by decide⟩ ⟨10, by decide⟩ ⟨14, by decide⟩ (M (sigmaAt r (2 * 2)))
          (M (sigmaAt r (2 * 2 + 1))))
        ⟨3, by decide⟩ ⟨7, by decide⟩ ⟨11, by decide⟩ ⟨15, by decide⟩ (M (sigmaAt r (2 * 3)))
          (M (sigmaAt r (2 * 3 + 1))))
        ⟨0, by decide⟩ ⟨5, by decide⟩ ⟨10, by decide⟩ ⟨15, by decide⟩ (M (sigmaAt r (2 * 4)))
          (M (sigmaAt r (2 * 4 + 1))))
        ⟨1, by decide⟩ ⟨6, by decide⟩ ⟨11, by decide⟩ ⟨12, by decide⟩ (M (sigmaAt r (2 * 5)))
          (M (sigmaAt r (2 * 5 + 1))))
        ⟨2, by decide⟩ ⟨7, by decide⟩ ⟨8, by decide⟩ ⟨13, by decide⟩ (M (sigmaAt r (2 * 6)))
          (M (sigmaAt r (2 * 6 + 1))))
        ⟨3, by decide⟩ ⟨4, by decide⟩ ⟨9, by decide⟩ ⟨14, by decide⟩ (M (sigmaAt r (2 * 7)))
          (M (sigmaAt r (2 * 7 + 1))) := rfl

end

theorem round_ok (r : Nat) {V : BitVec 32} {M : Block 32} {s₀ s : State} {v : Work 32}
    (c : RCtx V M s₀) (h : RI V s₀ v s) :
    WP isa (round r) s (RI V s₀ (Spec.Blake2.round Spec.Blake2.s M v r)) := by
  unfold round
  rw [round_eq]
  refine WP.seq (WP.mono (gAt_ok (x := 0) (y := 4) (z := 8) (u := 12) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 0 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 1) (y := 5) (z := 9) (u := 13) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 1 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 2) (y := 6) (z := 10) (u := 14) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 2 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 3) (y := 7) (z := 11) (u := 15) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 3 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 0) (y := 5) (z := 10) (u := 15) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 4 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 1) (y := 6) (z := 11) (u := 12) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 5 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 2) (y := 7) (z := 8) (u := 13) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 6 c h) fun s h => ?_)
  exact WP.mono (gAt_ok (x := 3) (y := 4) (z := 9) (u := 14) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 7 c h) fun s h => h

theorem rounds_ok {V : BitVec 32} {M : Block 32} {s₀ : State} {v : Work 32} (c : RCtx V M s₀)
    (hv : ∀ k (hk : k < 16), Holds V s₀ k v[k]) (n : Nat) :
    WP isa (rounds n) s₀ (RI V s₀ ((List.range n).foldl (Spec.Blake2.round Spec.Blake2.s M) v)) := by
  induction n with
  | zero => exact WP.block_nil ⟨hv, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    refine WP.seq (WP.mono ih fun s hs => ?_)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact round_ok n c hs

end VG.Proof.Blake2.ArmS
