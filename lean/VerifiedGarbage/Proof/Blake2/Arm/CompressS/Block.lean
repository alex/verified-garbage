import VerifiedGarbage.Proof.Blake2.Arm.CompressS.Rounds

/-!
# BLAKE2s on ARMv7: one block

Untrusted: everything here is checked by Lean. Setting up the work vector
(`init_ok`): copying the block to `scratch`, loading the state into
registers and the IV words; and XORing the work vector into the state
(`fin_ok`).
-/

namespace VG.Proof.Blake2.ArmS

open VG VG.Arm
open VG.Impl.Blake2.Arm.S (wreg cOff xOff stOff blkOff movImm ld lds ivC ivD ivCs ivDs copyMsg finX finHi finLo)
open VG.Proof.Sha512.Arm (A A_eq)
open VG.Proof.MdStream.Arm (Upd Mupd wp_add wp_ldr wp_str wp_mov op2_reg op2_imm)
open VG.Spec.Blake2 (Work Block HashValue)

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_movImm {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d v → WP isa (.block rest) s' Q) :
    WP isa (.block (movImm d v ++ rest)) s Q := by
  simp only [movImm, List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => k s₂ ⟨?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂.gpr, u₁.gpr, movw_movt]
  · rw [u₂.other r h, u₁.other r h]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]
  · rw [u₂.sp, u₁.sp]

end

theorem iv_getD {k : Nat} (hk : k < 8) : Spec.Blake2.s.IV.toList.getD k 0 = Spec.Blake2.s.IV[k] := by
  simp [List.getD_eq_getElem?_getD, hk]

/-! ## Copying the block -/

structure CInv (V B : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .lr → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨State.addr V, 64⟩] s.mem s'.mem
  msg : ∀ j < n, s'.mem.readW (A V (4 * j)) 32 = s.mem.readW (A B (4 * j)) 32

theorem copyMsg_ok {V B : BitVec 32} {s : State} (hV : s.gpr .r12 = V) (hB : s.gpr .r0 = B)
    (fitV : V.toNat + 512 ≤ 2 ^ 32) (fitB : B.toNat + 64 ≤ 2 ^ 32)
    (wV : ∀ o, o + 4 ≤ 512 → InRegions s.wr (A V o) 4)
    (rB : ∀ o, o + 4 ≤ 64 → InRegions (s.rd ++ s.wr) (A B o) 4)
    (hd : Region.Disjoint ⟨State.addr B, 64⟩ ⟨State.addr V, 64⟩) :
    ∀ n ≤ 16, WP isa (copyMsg n) s (CInv V B s n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ h₁ => ?_)
    simp only [Impl.Blake2.Arm.S.T, Impl.Blake2.Arm.S.S]
    refine wp_ldr (by omega) (by rw [h₁.gpr _ (by decide), hB]) (by rw [h₁.rd, h₁.wr]; exact rB _ (by omega))
      fun s₂ u₂ => ?_
    refine wp_str (by omega) (by rw [u₂.other _ (by decide), h₁.gpr _ (by decide), hV])
      (by rw [u₂.wr, h₁.wr]; exact wV _ (by omega)) fun s₃ m₃ => WP.block_nil ?_
    refine ⟨fun r hr => by rw [m₃.gpr, u₂.other r hr, h₁.gpr r hr], by rw [m₃.rd, u₂.rd, h₁.rd],
      by rw [m₃.wr, u₂.wr, h₁.wr], by rw [m₃.sp, u₂.sp, h₁.sp], ?_, fun j hj => ?_⟩
    · rw [m₃.mem, u₂.mem]
      exact h₁.frame.writeW (List.mem_singleton_self _) _
        (by rw [addr_add (by omega)]; exact Offset.contains_base _ (by omega) (by omega))
    · have eB : State.addr (B + BitVec.ofNat 32 (4 * n)) = State.addr B + BitVec.ofNat 64 (4 * n) :=
        addr_add (by omega)
      have eV : ∀ i, i < 16 → State.addr (V + BitVec.ofNat 32 (4 * i)) = State.addr V + BitVec.ofNat 64 (4 * i) :=
        fun i hi => addr_add (by omega)
      show (s₃.mem.readW (State.addr (V + BitVec.ofNat 32 (4 * j))) 32 =
        s.mem.readW (State.addr (B + BitVec.ofNat 32 (4 * j))) 32)
      rw [m₃.mem, u₂.gpr, u₂.mem]
      by_cases e : j = n
      · subst e
        rw [Mem.readW_writeW_self32, eB]
        exact h₁.frame.readW (r := ⟨State.addr B, 64⟩) (Offset.contains_base _ (by omega) (by omega))
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) (by decide)
      · rw [Mem.readW_writeW_sep (by
          rw [eV j (by omega), eV n (by omega)]
          exact Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact h₁.msg j (by omega)

/-! ## Loading the state -/

/-- Word `k` (0–7) of the state `H` as `init` loads it: words 4–7 rotated left
by 7. -/
def ldv (H : Nat → BitVec 32) (k : Nat) : BitVec 32 := if k < 4 then H k else (H k).rotateLeft 7

theorem wreg_ne8 {j k : Nat} (hj : j < 8) (hk : k < 8) (h : j ≠ k) : wreg j ≠ wreg k :=
  fun e => h (wreg_inj j (by omega) k (by omega) (by omega) (by omega) e)

structure LdInv (st : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, (∀ k < 8, r ≠ wreg k) → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vars : ∀ k < n, s'.gpr (wreg k) = ldv (fun k => s.mem.readW (A st (4 * k)) 32) k

theorem lds_ok {st : BitVec 32} {s : State} (h11 : s.gpr .r11 = st)
    (rS : ∀ o, o + 4 ≤ 32 → InRegions (s.rd ++ s.wr) (A st o) 4) :
    ∀ n ≤ 8, WP isa (lds n) s (LdInv st s n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega)⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ h₁ => ?_)
    have h11' : s₁.gpr .r11 = st := by rw [h₁.gpr _ (by decide), h11]
    have hfin : ∀ s₃ : State, Upd s₁ s₃ (wreg n)
        (ldv (fun k => s.mem.readW (A st (4 * k)) 32) n) → LdInv st s (n + 1) s₃ := fun s₃ u₃ =>
      ⟨fun r hr => by rw [u₃.other r (hr n (by omega)), h₁.gpr r hr], by rw [u₃.mem, h₁.mem],
        by rw [u₃.rd, h₁.rd], by rw [u₃.wr, h₁.wr], by rw [u₃.sp, h₁.sp], fun k hk => by
          by_cases e : k = n
          · subst e; exact u₃.gpr
          · rw [u₃.other _ (wreg_ne8 (by omega) (by omega) e)]; exact h₁.vars k (by omega)⟩
    simp only [ld]
    refine wp_ldr (by omega) (by rw [h11']) (by rw [h₁.rd, h₁.wr]; exact rS _ (by omega)) fun s₂ u₂ => ?_
    by_cases h4 : n < 4
    · simp only [h4, ↓reduceIte]
      exact WP.block_nil (hfin s₂ (by simpa only [ldv, h4, ↓reduceIte, h₁.mem] using u₂))
    · simp only [h4, ↓reduceIte]
      refine wp_mov (op2_ror (by decide)) fun s₃ u₃ => WP.block_nil (hfin s₃ ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩)
      · rw [u₃.gpr, u₂.gpr, h₁.mem, rotr_eq_rotl _ (by decide) (by decide)]
        simp only [ldv, h4, ↓reduceIte]
      · rw [u₃.other r hr, u₂.other r hr]
      · rw [u₃.mem, u₂.mem]
      · rw [u₃.rd, u₂.rd]
      · rw [u₃.wr, u₂.wr]
      · rw [u₃.sp, u₂.sp]

/-! ## The IV words -/

structure CvInv (V : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .lr → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [cR V] s.mem s'.mem
  c : ∀ j < n, s'.mem.readW (A V (cOff (j + 8))) 32 = Spec.Blake2.s.IV.toList.getD j 0

theorem ivCs_ok {V : BitVec 32} {s : State} (hV : s.gpr .r12 = V) (fitV : V.toNat + 512 ≤ 2 ^ 32)
    (wV : ∀ o, o + 4 ≤ 512 → InRegions s.wr (A V o) 4) :
    ∀ n ≤ 4, WP isa (ivCs n) s (CvInv V s n) := by
  intro n hn
  have eV : ∀ i, i < 512 → State.addr (V + BitVec.ofNat 32 i) = State.addr V + BitVec.ofNat 64 i :=
    fun i hi => addr_add (by omega)
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ h₁ => ?_)
    simp only [ivC, Impl.Blake2.Arm.S.T, Impl.Blake2.Arm.S.S, show n + 8 - 8 = n by omega]
    refine wp_movImm fun s₂ u₂ => wp_str (by unfold cOff; omega)
      (by rw [u₂.other _ (by decide), h₁.gpr _ (by decide), hV])
      (by rw [u₂.wr, h₁.wr]; exact wV _ (by unfold cOff; omega)) fun s₃ m₃ => WP.block_nil ?_
    refine ⟨fun r hr => by rw [m₃.gpr, u₂.other r hr, h₁.gpr r hr], by rw [m₃.rd, u₂.rd, h₁.rd],
      by rw [m₃.wr, u₂.wr, h₁.wr], by rw [m₃.sp, u₂.sp, h₁.sp], ?_, fun j hj => ?_⟩
    · have hc : (cR V).Contains (State.addr (V + BitVec.ofNat 32 (cOff (n + 8)))) (32 / 8) := by
        rw [eV _ (by unfold cOff; omega)]
        exact Offset.contains _ (by unfold cOff; omega) (by unfold cOff; omega) (by omega)
      rw [m₃.mem, u₂.mem]
      exact h₁.frame.writeW (List.mem_singleton_self _) _ hc
    · show s₃.mem.readW (State.addr (V + BitVec.ofNat 32 (cOff (j + 8)))) 32 = _
      rw [m₃.mem, u₂.gpr, u₂.mem]
      by_cases e : j = n
      · subst e; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (by
          rw [eV _ (by unfold cOff; omega), eV _ (by unfold cOff; omega)]
          exact Offset.sep _ (by unfold cOff; omega) (by unfold cOff; omega) (by unfold cOff; omega))
          (by decide)]
        exact h₁.c j (by omega)

theorem wreg_hi_ne : ∀ j < 4, ∀ i < 4, wreg (j + 12) = wreg (i + 12) → j = i := by decide
theorem wreg_hi_ne' : ∀ j < 4, wreg (j + 12) ≠ .lr ∧ wreg (j + 12) ≠ .r12 := by decide

structure DvInv (V : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .lr → (∀ j < 4, r ≠ wreg (j + 12)) → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vars : ∀ j < n, s'.gpr (wreg (j + 12)) =
    (Spec.Blake2.s.IV.toList.getD (j + 4) 0 ^^^ s.mem.readW (A V (xOff (j + 12))) 32).rotateLeft 8

theorem ivDs_ok {V : BitVec 32} {s : State} (hV : s.gpr .r12 = V)
    (rV : ∀ o, o + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (A V o) 4) :
    ∀ n ≤ 4, WP isa (ivDs n) s (DvInv V s n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega)⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ h₁ => ?_)
    have hw := wreg_hi_ne' n (by omega)
    simp only [ivD, Impl.Blake2.Arm.S.T, Impl.Blake2.Arm.S.S, show n + 12 - 8 = n + 4 by omega]
    refine wp_movImm fun s₂ u₂ => ?_
    refine wp_ldr (by unfold xOff; omega) (by
        rw [u₂.other _ (Ne.symm hw.2), h₁.gpr _ (by decide) (by decide), hV])
      (by rw [u₂.rd, u₂.wr, h₁.rd, h₁.wr]; exact rV _ (by unfold xOff; omega)) fun s₃ u₃ => ?_
    refine wp_eor (op2_ror (by decide)) fun s₄ u₄ => WP.block_nil ?_
    refine ⟨fun r h1 h2 => ?_, by rw [u₄.mem, u₃.mem, u₂.mem, h₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, h₁.rd],
      by rw [u₄.wr, u₃.wr, u₂.wr, h₁.wr], by rw [u₄.sp, u₃.sp, u₂.sp, h₁.sp], fun j hj => ?_⟩
    · rw [u₄.other r (h2 n (by omega)), u₃.other r h1, u₂.other r (h2 n (by omega)), h₁.gpr r h1 h2]
    · by_cases e : j = n
      · subst e
        rw [u₄.gpr, u₃.other _ hw.1, u₂.gpr, u₃.gpr, u₂.mem, h₁.mem, rotr_eq_rotl _ (by decide) (by decide),
          rotl_xor]
      · have hne : wreg (j + 12) ≠ wreg (n + 12) := fun h => e (wreg_hi_ne j (by omega) n (by omega) h)
        rw [u₄.other _ hne, u₃.other _ (wreg_hi_ne' j (by omega)).1, u₂.other _ hne]
        exact h₁.vars j (by omega)

/-! ## Setting up the work vector -/

/-- A word of `scratch` outside the regions a frame allows to change. -/
theorem scr_word {V : BitVec 32} (fitV : V.toNat + 512 ≤ 2 ^ 32) {rs : List Region} {m m' : Mem}
    (hf : Frame rs m m') {d : Nat} (hd : d + 4 ≤ 512)
    (hdis : ∀ r ∈ rs, Region.Disjoint ⟨State.addr V + BitVec.ofNat 64 d, 4⟩ r) :
    m'.readW (A V d) 32 = m.readW (A V d) 32 := by
  rw [cOff_A fitV (by omega)]; exact hf.readW (Region.contains_self _ _) hdis (by decide)

/-- The words `init` sets up, from the state words `H` and the words `X` of
`scratch` XORed into words 12–15. -/
def initW (H X : Nat → BitVec 32) (k : Nat) : BitVec 32 :=
  if k < 8 then H k else if k < 12 then Spec.Blake2.s.IV.toList.getD (k - 8) 0
  else Spec.Blake2.s.IV.toList.getD (k - 8) 0 ^^^ X k

/-- The regions of `scratch` that `init` writes. -/
abbrev initR (V : BitVec 32) : List Region :=
  [⟨State.addr V, 80⟩, ⟨State.addr V + BitVec.ofNat 64 blkOff, 4⟩]

structure IOut (V st B : BitVec 32) (s s' : State) : Prop where
  r12 : s'.gpr .r12 = V
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (initR V) s.mem s'.mem
  blk : s'.mem.readW (A V blkOff) 32 = B + 64
  msg : ∀ j < 16, s'.mem.readW (A V (4 * j)) 32 = s.mem.readW (A B (4 * j)) 32
  vars : ∀ k < 16, Holds V s' k (initW (fun k => s.mem.readW (A st (4 * k)) 32)
    (fun k => s.mem.readW (A V (xOff k)) 32) k)

theorem init_ok {V st B : BitVec 32} {s : State} (hV : s.gpr .r12 = V) (fitV : V.toNat + 512 ≤ 2 ^ 32)
    (fitS : st.toNat + 32 ≤ 2 ^ 32) (fitB : B.toNat + 64 ≤ 2 ^ 32)
    (wV : ∀ o, o + 4 ≤ 512 → InRegions s.wr (A V o) 4)
    (rS : ∀ o, o + 4 ≤ 32 → InRegions (s.rd ++ s.wr) (A st o) 4)
    (rB : ∀ o, o + 4 ≤ 64 → InRegions (s.rd ++ s.wr) (A B o) 4)
    (hst : s.mem.readW (A V stOff) 32 = st) (hblk : s.mem.readW (A V blkOff) 32 = B)
    (hdB : Region.Disjoint ⟨State.addr B, 64⟩ ⟨State.addr V, 64⟩)
    (hdS : Region.Disjoint ⟨State.addr st, 32⟩ ⟨State.addr V, 512⟩) :
    WP isa Impl.Blake2.Arm.S.init s (IOut V st B s) := by
  have eV : ∀ i, i < 512 → State.addr (V + BitVec.ofNat 32 i) = State.addr V + BitVec.ofNat 64 i :=
    fun i hi => addr_add (by omega)
  have rV : ∀ o, o + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (A V o) 4 := fun o ho =>
    let ⟨r, hr, hc⟩ := wV o ho; ⟨r, List.mem_append_right _ hr, hc⟩
  -- The regions `init` writes, and what lies outside them.
  have sub64 : ∀ r ∈ [(⟨State.addr V, 64⟩ : Region)], ∃ r' ∈ initR V, Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, Region.sub_prefix (by omega)⟩
  have subC : ∀ r ∈ [cR V], ∃ r' ∈ initR V, Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by omega)⟩
  have hBlk : (⟨State.addr V + BitVec.ofNat 64 blkOff, 4⟩ : Region).Contains
      (State.addr (V + BitVec.ofNat 32 blkOff)) (32 / 8) := by
    rw [eV _ (by decide)]; exact Region.contains_self _ _
  have outR : ∀ d, 88 ≤ d → d + 4 ≤ 512 → ∀ r ∈ initR V,
      Region.Disjoint ⟨State.addr V + BitVec.ofNat 64 d, 4⟩ r := fun d h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (by simp only [blkOff]; omega) (by omega) (by simp only [blkOff]; omega)
  have stR : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨State.addr V, 512⟩) → ∀ {m m' : Mem},
      Frame rs m m' → ∀ k < 8, m'.readW (A st (4 * k)) 32 = m.readW (A st (4 * k)) 32 :=
    fun hs m m' hf k hk => by
      rw [A_eq (by omega)]
      exact hf.readW (r := ⟨State.addr st, 32⟩) (Offset.contains_base _ (by omega) (by omega))
        (fun r hr => hdS.sub_right (hs r hr)) (by decide)
  unfold Impl.Blake2.Arm.S.init
  simp only [Impl.Blake2.Arm.S.S]
  refine WP.seq (wp_ldr (by decide) (by rw [hV]) (rV _ (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  have hB₁ : s₁.gpr .r0 = B := by rw [u₁.gpr]; exact hblk
  have V₁ : s₁.gpr .r12 = V := by rw [u₁.other _ (by decide), hV]
  refine WP.seq (WP.mono (copyMsg_ok V₁ hB₁ fitV fitB (by rw [u₁.wr]; exact wV) (by rw [u₁.rd, u₁.wr]; exact rB)
    hdB 16 (Nat.le_refl _)) fun s₂ h₂ => ?_)
  have V₂ : s₂.gpr .r12 = V := by rw [h₂.gpr _ (by decide), V₁]
  refine WP.seq (wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_str (by decide)
    (by rw [u₃.other _ (by decide), V₂]) (by rw [u₃.wr, h₂.wr, u₁.wr]; exact wV _ (by decide))
    fun s₄ m₄ => wp_ldr (by decide) (by rw [m₄.gpr, u₃.other _ (by decide), V₂])
    (by rw [m₄.rd, m₄.wr, u₃.rd, u₃.wr, h₂.rd, h₂.wr, u₁.rd, u₁.wr]; exact rV _ (by decide))
    fun s₅ u₅ => WP.block_nil ?_)
  have f₄ : Frame (initR V) s.mem s₄.mem := by
    rw [m₄.mem, u₃.mem, ← u₁.mem]
    exact (h₂.frame.sub sub64).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ hBlk
  have h11 : s₅.gpr .r11 = st := by
    rw [u₅.gpr, ← hst]
    exact scr_word fitV f₄ (d := stOff) (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ (by decide) (by decide)
      · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  have m₅ : s₅.mem = s₄.mem := u₅.mem
  have rd₅ : s₅.rd = s.rd := by rw [u₅.rd, m₄.rd, u₃.rd, h₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s.wr := by rw [u₅.wr, m₄.wr, u₃.wr, h₂.wr, u₁.wr]
  have V₅ : s₅.gpr .r12 = V := by rw [u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), V₂]
  refine WP.seq (WP.mono (lds_ok h11 (by rw [rd₅, wr₅]; exact rS) 8 (Nat.le_refl _)) fun s₆ h₆ => ?_)
  have V₆ : s₆.gpr .r12 = V := by rw [h₆.gpr _ (by decide), V₅]
  refine WP.seq (WP.mono (ivCs_ok V₆ fitV (by rw [h₆.wr, wr₅]; exact wV) 4 (Nat.le_refl _)) fun s₇ h₇ => ?_)
  have V₇ : s₇.gpr .r12 = V := by rw [h₇.gpr _ (by decide), V₆]
  refine WP.mono (ivDs_ok V₇ (by rw [h₇.rd, h₇.wr, h₆.rd, h₆.wr, rd₅, wr₅]; exact rV) 4 (Nat.le_refl _))
    fun s₈ h₈ => ?_
  have f₈ : Frame (initR V) s.mem s₈.mem := by
    rw [h₈.mem]; exact (f₄.trans (by rw [h₆.mem, m₅]; exact Frame.refl _ _)).trans (h₇.frame.sub subC)
  refine ⟨by rw [h₈.gpr _ (by decide) (by decide), V₇], by rw [h₈.rd, h₇.rd, h₆.rd, rd₅],
    by rw [h₈.wr, h₇.wr, h₆.wr, wr₅], ?_, f₈, ?_, fun j hj => ?_, fun k hk => ?_⟩
  · rw [h₈.sp, h₇.sp, h₆.sp, u₅.sp, m₄.sp, u₃.sp, h₂.sp, u₁.sp]
  · -- The block pointer.
    have hd : ∀ r ∈ [cR V], Region.Disjoint ⟨State.addr V + BitVec.ofNat 64 blkOff, 4⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by decide) (by decide) (by decide)
    rw [h₈.mem, scr_word fitV h₇.frame (by decide) hd, h₆.mem, m₅]
    show s₄.mem.readW (State.addr (V + BitVec.ofNat 32 blkOff)) 32 = _
    rw [m₄.mem, Mem.readW_writeW_self32, u₃.gpr, h₂.gpr _ (by decide), hB₁]
  · -- The message words.
    have hd : ∀ r ∈ [cR V], Region.Disjoint ⟨State.addr V + BitVec.ofNat 64 (4 * j), 4⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    have hsep : Mem.Sep (State.addr V + BitVec.ofNat 64 (4 * j)) (32 / 8)
        (State.addr (V + BitVec.ofNat 32 blkOff)) (32 / 8) := by
      rw [eV _ (by decide)]
      exact Offset.sep _ (by simp only [blkOff]; omega) (by omega) (by simp only [blkOff]; omega)
    rw [h₈.mem, scr_word fitV h₇.frame (by omega) hd, h₆.mem, m₅, m₄.mem,
      show (A V (4 * j)) = State.addr V + BitVec.ofNat 64 (4 * j) from eV _ (by omega),
      Mem.readW_writeW_sep hsep (by decide), u₃.mem, ← eV _ (by omega), h₂.msg j hj, u₁.mem]
  · -- The work vector.
    have hS₅ : ∀ i < 8, s₅.mem.readW (A st (4 * i)) 32 = s.mem.readW (A st (4 * i)) 32 := fun i hi =>
      stR (rs := initR V) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Region.sub_prefix (by omega)
        · exact Offset.sub_base _ (by simp only [blkOff]; omega)) (by rw [m₅]; exact f₄) i hi
    have hX : ∀ i, 88 ≤ xOff i → xOff i + 4 ≤ 512 →
        s₇.mem.readW (A V (xOff i)) 32 = s.mem.readW (A V (xOff i)) 32 := fun i h1 h2 => by
      have f₇ : Frame (initR V) s.mem s₇.mem :=
        (f₄.trans (by rw [h₆.mem, m₅]; exact Frame.refl _ _)).trans (h₇.frame.sub subC)
      exact scr_word fitV f₇ h2 (outR _ h1 h2)
    have hr : ∀ i < 8, s₈.gpr (wreg i) = s₆.gpr (wreg i) := fun i hi => by
      rw [h₈.gpr _ (wreg_ne i (by omega)).2 (fun j hj e => absurd
        (wreg_inj i (by omega) (j + 12) (by omega) (by omega) (by omega) e) (by omega)),
        h₇.gpr _ (wreg_ne i (by omega)).2]
    unfold Holds initW
    by_cases h4 : k < 4
    · simp only [h4, ↓reduceIte, show k < 8 by omega]
      rw [hr k (by omega), h₆.vars k (by omega)]
      simp only [ldv, h4, ↓reduceIte]; exact hS₅ k (by omega)
    by_cases h8 : k < 8
    · simp only [h4, h8, ↓reduceIte]
      rw [hr k h8, h₆.vars k h8]
      simp only [ldv, h4, ↓reduceIte]; rw [hS₅ k h8]
    by_cases h12 : k < 12
    · simp only [h4, h8, h12, ↓reduceIte]
      rw [h₈.mem]
      have := h₇.c (k - 8) (by omega)
      rwa [show k - 8 + 8 = k by omega] at this
    · simp only [h4, h8, h12, ↓reduceIte]
      have := h₈.vars (k - 12) (by omega)
      rw [show k - 12 + 12 = k by omega, show k - 12 + 4 = k - 8 by omega] at this
      rw [this, hX k (by unfold xOff; omega) (by unfold xOff; omega)]

/-! ## XORing the work vector into the state -/

/-- What `fin` needs of the state `s₀` at its start: the state at `st` and
the scratch space at `V`, holding words 8–11 of the work vector `v`. -/
structure FCtx (V st : BitVec 32) (v : Work 32) (s₀ : State) : Prop where
  fitS : st.toNat + 32 ≤ 2 ^ 32
  fitV : V.toNat + 512 ≤ 2 ^ 32
  wS : ∀ o, o + 4 ≤ 32 → InRegions s₀.wr (A st o) 4
  rV : ∀ o, o + 4 ≤ 512 → InRegions (s₀.rd ++ s₀.wr) (A V o) 4
  c : ∀ k (hk : k < 4), s₀.mem.readW (A V (cOff (k + 8))) 32 = v[k + 8]
  disj : Region.Disjoint ⟨State.addr st, 32⟩ ⟨State.addr V, 512⟩

/-- The invariant of `fin`, from `s₀`, with the words `D` of the state done. -/
structure FI (V st : BitVec 32) (H : Nat → BitVec 32) (v : Work 32) (s₀ : State) (D : List Nat)
    (s : State) : Prop where
  r8 : s.gpr .r8 = st
  r12 : s.gpr .r12 = V
  r9 : s.gpr .r9 = s₀.mem.readW (A V blkOff) 32
  r10 : s.gpr .r10 = s₀.mem.readW (A V Impl.Blake2.Arm.S.nOff) 32
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr st, 32⟩] s₀.mem s.mem
  lo : ∀ k (hk : k < 4), k ∉ D → s.gpr (wreg k) = v[k]
  mid : ∀ k (hk : k < 4), s.gpr (wreg (k + 4)) = (v[k + 4] ^^^ v[k + 4 + 8]).rotateLeft 7
  words : ∀ k (hk : k < 8), s.mem.readW (A st (4 * k)) 32 =
    if k ∈ D then H k ^^^ (v[k] ^^^ v[k + 8]) else H k

theorem wreg_lo_ne : ∀ k < 8, wreg k ≠ .lr ∧ wreg k ≠ .r8 ∧ wreg k ≠ .r12 := by decide
theorem wreg_lo_ne' : ∀ k < 4, wreg k ≠ .r9 ∧ wreg k ≠ .r10 := by decide

theorem FI.st_addr {V st : BitVec 32} {v : Work 32} {s₀ : State} (c : FCtx V st v s₀) {k : Nat} (hk : k < 8) :
    State.addr (st + BitVec.ofNat 32 (4 * k)) = State.addr st + BitVec.ofNat 64 (4 * k) :=
  addr_add (by have := c.fitS; omega)

theorem FI.words_upd {V st : BitVec 32} {H : Nat → BitVec 32} {v : Work 32} {s₀ s : State} {D : List Nat}
    (c : FCtx V st v s₀) (h : FI V st H v s₀ D s) {j : Nat} (hj : j < 8) {m : Mem}
    (hm : m = s.mem.writeW (State.addr (st + BitVec.ofNat 32 (4 * j))) (H j ^^^ (v[j] ^^^ v[j + 8]))) :
    ∀ k (hk : k < 8), m.readW (A st (4 * k)) 32 =
      if k ∈ j :: D then H k ^^^ (v[k] ^^^ v[k + 8]) else H k := fun k hk => by
  subst hm
  show (s.mem.writeW _ _).readW (State.addr (st + BitVec.ofNat 32 (4 * k))) 32 = _
  by_cases e : k = j
  · subst e; simp only [List.mem_cons_self, ↓reduceIte]; exact Mem.readW_writeW_self32 _ _ _
  · rw [Mem.readW_writeW_sep (by
      rw [FI.st_addr c hk, FI.st_addr c hj]; exact Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
    simp only [List.mem_cons, e, false_or]; exact h.words k hk

theorem FI.frame_upd {V st : BitVec 32} {H : Nat → BitVec 32} {v : Work 32} {s₀ s : State} {D : List Nat}
    (c : FCtx V st v s₀) (h : FI V st H v s₀ D s) {j : Nat} (hj : j < 8) (x : BitVec 32) :
    Frame [⟨State.addr st, 32⟩] s₀.mem (s.mem.writeW (State.addr (st + BitVec.ofNat 32 (4 * j))) x) :=
  h.frame.writeW (List.mem_singleton_self _) _ (by
    rw [FI.st_addr c hj]; exact Offset.contains_base _ (by omega) (by omega))

theorem finHi_ok {V st : BitVec 32} {H : Nat → BitVec 32} {v : Work 32} {s₀ s : State} {D : List Nat}
    (c : FCtx V st v s₀) {k : Nat} (hk : k < 4) (hD : k + 4 ∉ D) (h : FI V st H v s₀ D s) :
    WP isa (.block (finHi (k + 4))) s (FI V st H v s₀ ((k + 4) :: D)) := by
  have nw := wreg_lo_ne (k + 4) (by omega)
  simp only [finHi, Impl.Blake2.Arm.S.T]
  refine wp_ldr (by omega) (by rw [h.r8]) (by
      rw [h.rd, h.wr]; exact let ⟨r, hr, hc⟩ := c.wS _ (by omega); ⟨r, List.mem_append_right _ hr, hc⟩)
    fun s₁ u₁ => wp_eor (op2_ror (by decide)) fun s₂ u₂ => wp_str (by omega)
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r8])
      (by rw [u₂.wr, u₁.wr, h.wr]; exact c.wS _ (by omega)) fun s₃ m₃ => WP.block_nil ?_
  have hv : s₂.gpr .lr = H (k + 4) ^^^ (v[k + 4] ^^^ v[k + 4 + 8]) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ nw.1, h.mid k hk, rotr_rotl _ (by decide)]
    have := h.words (k + 4) (by omega)
    simp only [hD, ↓reduceIte] at this
    rw [← this]
  refine ⟨by rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r8],
    by rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r12],
    by rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r9],
    by rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r10],
    by rw [m₃.rd, u₂.rd, u₁.rd, h.rd], by rw [m₃.wr, u₂.wr, u₁.wr, h.wr], by rw [m₃.sp, u₂.sp, u₁.sp, h.sp],
    by rw [m₃.mem, u₂.mem, u₁.mem]; exact h.frame_upd c (by omega) _, fun j hj hjD => ?_, fun j hj => ?_,
    h.words_upd c (j := k + 4) (by omega) (by rw [m₃.mem, hv, u₂.mem, u₁.mem])⟩
  · have := wreg_lo_ne j (by omega)
    rw [m₃.gpr, u₂.other _ this.1, u₁.other _ this.1, h.lo j hj fun hm => hjD (List.mem_cons_of_mem _ hm)]
  · have := wreg_lo_ne (j + 4) (by omega)
    rw [m₃.gpr, u₂.other _ this.1, u₁.other _ this.1, h.mid j hj]

theorem finLo_ok {V st : BitVec 32} {H : Nat → BitVec 32} {v : Work 32} {s₀ s : State} {D : List Nat}
    (c : FCtx V st v s₀) {k : Nat} (hk : k < 4) (hD : k ∉ D) (h : FI V st H v s₀ D s) :
    WP isa (.block (finLo k)) s (FI V st H v s₀ (k :: D)) := by
  have nw := wreg_lo_ne k (by omega)
  have iS : InRegions (s.rd ++ s.wr) (A st (4 * k)) 4 := by
    rw [h.rd, h.wr]; exact let ⟨r, hr, hc⟩ := c.wS _ (by omega); ⟨r, List.mem_append_right _ hr, hc⟩
  simp only [finLo, Impl.Blake2.Arm.S.T, Impl.Blake2.Arm.S.S]
  refine wp_ldr (by unfold cOff; omega) (by rw [h.r12]) (by rw [h.rd, h.wr]; exact c.rV _ (by unfold cOff; omega))
    fun s₁ u₁ => wp_eor (op2_reg _ _) fun s₂ u₂ => wp_ldr (by omega)
      (by rw [u₂.other _ (Ne.symm nw.2.1), u₁.other _ (by decide), h.r8]) (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact iS)
      fun s₃ u₃ => wp_eor (op2_reg _ _) fun s₄ u₄ => wp_str (by omega)
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (Ne.symm nw.2.1), u₁.other _ (by decide),
        h.r8])
      (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact c.wS _ (by omega)) fun s₅ m₅ => WP.block_nil ?_
  have hc : s.mem.readW (A V (cOff (k + 8))) 32 = v[k + 8] := by
    rw [← c.c k hk, cOff_A c.fitV (by unfold cOff; omega)]
    exact h.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (c.disj.sub_right (Offset.sub_base _ (by unfold cOff; omega))).symm) (by decide)
  have hw : s₃.gpr (wreg k) = v[k] ^^^ v[k + 8] := by
    rw [u₃.other _ nw.1, u₂.gpr, u₁.other _ nw.1, h.lo k hk hD, u₁.gpr]
    exact congrArg _ hc
  have hv : s₄.gpr .lr = H k ^^^ (v[k] ^^^ v[k + 8]) := by
    rw [u₄.gpr, u₃.gpr, u₂.mem, u₁.mem, hw]
    have := h.words k (by omega)
    simp only [hD, ↓reduceIte] at this
    exact congrArg (· ^^^ _) this
  have n9 := wreg_lo_ne' k hk
  refine ⟨?_, ?_, by rw [m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (Ne.symm n9.1),
      u₁.other _ (by decide), h.r9],
    by rw [m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (Ne.symm n9.2),
      u₁.other _ (by decide), h.r10], by rw [m₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [m₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [m₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    by rw [m₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact h.frame_upd c (by omega) _, fun j hj hjD => ?_,
    fun j hj => ?_, h.words_upd c (j := k) (by omega) (by rw [m₅.mem, hv, u₄.mem, u₃.mem, u₂.mem, u₁.mem])⟩
  · rw [m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (Ne.symm nw.2.1), u₁.other _ (by decide),
      h.r8]
  · rw [m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (Ne.symm nw.2.2), u₁.other _ (by decide),
      h.r12]
  · have nj := wreg_lo_ne j (by omega)
    have ne : wreg j ≠ wreg k := wreg_ne8 (by omega) (by omega) fun e => hjD (e ▸ List.mem_cons_self)
    rw [m₅.gpr, u₄.other _ nj.1, u₃.other _ nj.1, u₂.other _ ne, u₁.other _ nj.1,
      h.lo j hj fun hm => hjD (List.mem_cons_of_mem _ hm)]
  · have nj := wreg_lo_ne (j + 4) (by omega)
    have ne : wreg (j + 4) ≠ wreg k := wreg_ne8 (by omega) (by omega) (by omega)
    rw [m₅.gpr, u₄.other _ nj.1, u₃.other _ nj.1, u₂.other _ ne, u₁.other _ nj.1, h.mid j hj]

theorem finPre_ok {V st : BitVec 32} {v : Work 32} {s : State} (c : FCtx V st v s)
    (hv : ∀ k (hk : k < 16), Holds V s k v[k]) (hV : s.gpr .r12 = V)
    (hst : s.mem.readW (A V stOff) 32 = st) :
    WP isa (.block (finX 4 ++ finX 5 ++ finX 6 ++ finX 7 ++ ([.ldr .r8 Impl.Blake2.Arm.S.S stOff,
      .ldr .r9 Impl.Blake2.Arm.S.S blkOff, .ldr .r10 Impl.Blake2.Arm.S.S Impl.Blake2.Arm.S.nOff] : List Instr))) s
      (FI V st (fun k => s.mem.readW (A st (4 * k)) 32) v s []) := by
  simp only [finX, Impl.Blake2.Arm.S.S, List.cons_append, List.nil_append]
  refine wp_eor (op2_ror (by decide)) fun s₁ u₁ => wp_eor (op2_ror (by decide)) fun s₂ u₂ =>
    wp_eor (op2_ror (by decide)) fun s₃ u₃ => wp_eor (op2_ror (by decide)) fun s₄ u₄ => ?_
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have V₄ : s₄.gpr .r12 = V := by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, hV]
  refine wp_ldr (a := A V stOff) (by decide) (by rw [V₄]) (by rw [rd₄, wr₄]; exact c.rV _ (by decide))
    fun s₅ u₅ => wp_ldr (a := A V blkOff) (by decide) (by rw [u₅.other _ (by decide), V₄])
    (by rw [u₅.rd, u₅.wr, rd₄, wr₄]; exact c.rV _ (by decide))
    fun s₆ u₆ => wp_ldr (a := A V Impl.Blake2.Arm.S.nOff) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), V₄])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, rd₄, wr₄]; exact c.rV _ (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, m₄]
  have mid : ∀ k (hk : k < 4), s.gpr (wreg (k + 4)) ^^^ (s.gpr (wreg (k + 4 + 8))).rotateRight 1 =
      (v[k + 4] ^^^ v[k + 4 + 8]).rotateLeft 7 := fun k hk => by
    rw [(holds_mid (by omega) (by omega)).mp (hv (k + 4) (by omega)),
      (holds_hi (by omega)).mp (hv (k + 4 + 8) (by omega)), rotl8_rotr1, rotl_xor]
  refine ⟨by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, m₄]; exact hst,
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), V₄],
    by rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, m₄],
    by rw [u₇.gpr, u₆.mem, u₅.mem, m₄],
    by rw [u₇.rd, u₆.rd, u₅.rd, rd₄], by rw [u₇.wr, u₆.wr, u₅.wr, wr₄],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], by rw [m₇]; exact Frame.refl _ _,
    fun k hk _ => ?_, fun k hk => ?_, fun k hk => by rw [m₇]; rfl⟩
  · have e := (holds_lo hk).mp (hv k (by omega))
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
      exact e
  · have e := mid k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr]
      exact e
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other]
      exact e
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.other, u₁.other]
      exact e
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other]
      exact e

theorem fin_ok {V st : BitVec 32} {v : Work 32} {s : State} (c : FCtx V st v s)
    (hv : ∀ k (hk : k < 16), Holds V s k v[k]) (hV : s.gpr .r12 = V)
    (hst : s.mem.readW (A V stOff) 32 = st) :
    WP isa Impl.Blake2.Arm.S.fin s fun s' =>
      s'.gpr .r12 = V ∧ s'.gpr .r8 = st ∧ s'.gpr .r9 = s.mem.readW (A V blkOff) 32 ∧
      s'.gpr .r10 = s.mem.readW (A V Impl.Blake2.Arm.S.nOff) 32 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr st, 32⟩] s.mem s'.mem ∧
      ∀ k (hk : k < 8), s'.mem.readW (A st (4 * k)) 32 =
        s.mem.readW (A st (4 * k)) 32 ^^^ (v[k] ^^^ v[k + 8]) := by
  unfold Impl.Blake2.Arm.S.fin
  refine WP.seq (WP.mono (finPre_ok c hv hV hst) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (finHi_ok (k := 0) c (by decide) (by decide) h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (finHi_ok (k := 1) c (by decide) (by decide) h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (finHi_ok (k := 2) c (by decide) (by decide) h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (finHi_ok (k := 3) c (by decide) (by decide) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (finLo_ok (k := 0) c (by decide) (by decide) h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (finLo_ok (k := 1) c (by decide) (by decide) h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (finLo_ok (k := 2) c (by decide) (by decide) h₇) fun s₈ h₈ => ?_)
  refine WP.mono (finLo_ok (k := 3) c (by decide) (by decide) h₈) fun s₉ h₉ => ?_
  refine ⟨h₉.r12, h₉.r8, h₉.r9, h₉.r10, h₉.rd, h₉.wr, h₉.sp, h₉.frame, fun k hk => ?_⟩
  rw [h₉.words k hk]
  have : k ∈ [3, 2, 1, 0, 0 + 4 + 3 - 3 + 3, 2 + 4, 1 + 4, 0 + 4] := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [this, ↓reduceIte]

end VG.Proof.Blake2.ArmS
