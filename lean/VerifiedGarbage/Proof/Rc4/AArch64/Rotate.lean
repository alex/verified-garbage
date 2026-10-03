import VerifiedGarbage.Proof.Rc4.AArch64.Prga

/-!
# The rotation after a group

`rotate_ok`: the table registers move down by one (byte `k` becomes the old
byte `k + 16`, around the table), `j` and `-B` move back by 16, and the base
in `x8` advances by 16.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

def movs (n : Nat) : List Instr := (List.range n).map fun r => .vop (.mov (treg r) (treg (r + 1)))

theorem movs_succ (n : Nat) :
    movs (n + 1) = movs n ++ ([.vop (.mov (treg n) (treg (n + 1)))] : List Instr) := by
  simp only [movs, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem movs_run (s : State) {n : Nat} (hn : n ≤ 15) :
    ∃ t, runBlock isa (movs n) s = some t ∧ (∀ r < 16, t.v (treg r) =
      if r < n then s.v (treg (r + 1)) else s.v (treg r)) ∧ Only (treg 0 :: (List.range 15).map treg) s t := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun r _ => by simp, Only.refl _ _⟩
  | succ n ih =>
    obtain ⟨t, run, v, o⟩ := ih (by omega)
    let t' := t.setV (treg n) (t.v (treg (n + 1)))
    refine ⟨t', ?_, fun r hr => ?_, o.trans (Only.setV _ (by
      simp only [List.mem_cons, List.mem_map, List.mem_range]
      exact .inr ⟨n, by omega, rfl⟩) _)⟩
    · rw [movs_succ]
      exact runBlock_cat_some run (by rw [runBlock_cons]; exact rfl)
    · by_cases h : r = n
      · subst h
        simp only [t', v_setV_self, v (r + 1) (by omega), show ¬ r + 1 < r by omega, ite_false,
          show r < r + 1 by omega, ite_true]
      · rw [v_setV_of_ne _ _ (fun e => h (treg_inj _ hr _ (by omega) e)), v r hr]
        exact ite_iff ⟨fun h' => by omega, fun h' => by omega⟩ _ _

theorem lanes_diff : VArr.b16.map2 (fun _ x y => x - y) (laneNums 1) (laneNums 0) = bc 16 :=
  vbyte_ext fun e he => by
    rw [vbyte_map2 _ _ _ he, laneNums, laneNums, vbyte_ofVBytes _ he, vbyte_ofVBytes _ he,
      vbyte_bc _ he]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (16 : BitVec 8).toNat = 16 from rfl]
    omega

theorem rotate_eq (prga : Bool) : rotate prga =
    ([.vop (.sub .b16 .v7 (lanes 1) (lanes 0)), .vop (.sub .b16 (dq 0) (dq 0) .v7)] : List Instr) ++
      ((if prga then [.vop (.sub .b16 negBase negBase .v7)] else []) ++
        (([.vop (.mov .v7 (treg 0))] : List Instr) ++ (movs 15 ++
          ([.vop (.mov (treg 15) .v7), .addImm .x .x8 .x8 16] : List Instr)))) := by
  simp only [rotate, movs, List.append_assoc]

/-- The vector registers a rotation changes. -/
def rotRegs : List VReg := .v7 :: dq 0 :: negBase :: (List.range 16).map treg

theorem rotate_ok (prga : Bool) {s : State} (hk : Consts s) {J NB : BitVec 8}
    (hj : s.v (dq 0) = bc J) (hn : prga = true → s.v negBase = bc NB) :
    WP isa (.block (rotate prga)) s fun t =>
      (∀ k < 256, tbyte t.v k = tbyte s.v ((k + 16) % 256)) ∧ t.v (dq 0) = bc (J - 16) ∧
      t.v negBase = (if prga then bc (NB - 16) else s.v negBase) ∧
      t.gpr .x8 = s.gpr .x8 + 16 ∧ (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧
      (∀ r, r ∉ rotRegs → t.v r = s.v r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  let s₁ := s.setV .v7 (VArr.b16.map2 (fun _ x y => x - y) (s.v (lanes 1)) (s.v (lanes 0)))
  have v₁ : s₁.v .v7 = bc 16 := by
    rw [v_setV_self, hk.lns 1 (by decide), hk.lns 0 (by decide), lanes_diff]
  let s₂ := s₁.setV (dq 0) (VArr.b16.map2 (fun _ x y => x - y) (s₁.v (dq 0)) (s₁.v .v7))
  have j₂ : s₂.v (dq 0) = bc (J - 16) := by
    rw [v_setV_self, v₁, v_setV_of_ne _ _ (by decide), hj, sub_bc]
  obtain ⟨s₃, run₃, n₃, o₃⟩ : ∃ s₃, runBlock isa
      ((if prga then [.vop (.sub .b16 negBase negBase .v7)] else []) : List Instr) s₂ = some s₃ ∧
      s₃.v negBase = (if prga then bc (NB - 16) else s.v negBase) ∧ Only [negBase] s₂ s₃ := by
    cases prga
    · refine ⟨s₂, by simp only [Bool.false_eq_true, ite_false]; exact runBlock_nil, ?_, Only.refl _ _⟩
      simp only [Bool.false_eq_true, ite_false]
      rw [v_setV_of_ne _ _ (by decide), v_setV_of_ne _ _ (by decide)]
    · refine ⟨s₂.setV negBase (VArr.b16.map2 (fun _ x y => x - y) (s₂.v negBase) (s₂.v .v7)),
        by simp only [ite_true]; rw [runBlock_cons]; rfl, ?_, Only.setV _ (by simp) _⟩
      simp only [ite_true]
      rw [v_setV_self, v_setV_of_ne _ _ (by decide), v_setV_of_ne _ _ (by decide), hn rfl,
        v_setV_of_ne _ _ (by decide), v₁, sub_bc]
  let s₄ := s₃.setV .v7 (s₃.v (treg 0))
  obtain ⟨s₅, run₅, v₅, o₅⟩ := movs_run s₄ (n := 15) (Nat.le_refl _)
  let s₆ := s₅.setV (treg 15) (s₅.v .v7)
  let s₇ := s₆.write .x .x8 (s₆.read .x .x8 + BitVec.ofNat _ 16)
  have run : runBlock isa (rotate prga) s = some s₇ := by
    rw [rotate_eq]
    refine runBlock_cat_some (s₁ := s₂) (by
      rw [runBlock_cons, show exec (.vop (.sub .b16 .v7 (lanes 1) (lanes 0))) s = some s₁ from rfl,
        runStep_some, runBlock_cons, show exec (.vop (.sub .b16 (dq 0) (dq 0) .v7)) s₁ = some s₂ from rfl,
        runStep_some, runBlock_nil]) ?_
    refine runBlock_cat_some run₃ ?_
    rw [List.singleton_append, runBlock_cons, show exec (.vop (.mov .v7 (treg 0))) s₃ = some s₄ from rfl,
      runStep_some]
    refine runBlock_cat_some run₅ ?_
    rw [runBlock_cons, show exec (.vop (.mov (treg 15) .v7)) s₅ = some s₆ from rfl, runStep_some,
      runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_nil]
  refine WP.of_runBlock ⟨s₇, run, ?_⟩
  have v₇ : s₇.v = s₆.v := rfl
  have movsRegs : ∀ r, r ∉ (treg 0 :: (List.range 15).map treg) → r ∉ (List.range 16).map treg →
      True := fun _ _ _ => trivial
  -- what the moves leave alone
  have keep₅ : ∀ r, NotTable r → s₅.v r = s₄.v r := fun r hr => o₅.2 r (by
    simp only [List.mem_cons, List.mem_map, List.mem_range, not_or, not_exists, not_and]
    exact ⟨fun h => hr.ne 0 h.symm, fun a _ h => hr.ne a h⟩)
  have keep₂ : ∀ r, NotTable r → r ≠ .v7 → r ≠ dq 0 → r ≠ negBase → s₃.v r = s.v r := by
    intro r _ h7 hd hn
    rw [o₃.2 r (by simp [hn]), v_setV_of_ne _ _ hd, v_setV_of_ne _ _ h7]
  have tab₃ : ∀ a < 16, s₃.v (treg a) = s.v (treg a) := by
    intro a ha
    rw [o₃.2 _ (by simp; exact fun h => absurd h (by revert a; decide)),
      v_setV_of_ne _ _ (by revert a; decide), v_setV_of_ne _ _ (by revert a; decide)]
  have g₆ : s₆.gpr = s.gpr := by
    show s₅.gpr = s.gpr; rw [o₅.gpr]; show s₃.gpr = s.gpr; rw [o₃.gpr]; rfl
  have m₇ : s₇.mem = s.mem := by
    show s₅.mem = s.mem; rw [o₅.mem]; show s₃.mem = s.mem; rw [o₃.mem]; rfl
  have rd₇ : s₇.rd = s.rd := by
    show s₅.rd = s.rd; rw [o₅.rd]; show s₃.rd = s.rd; rw [o₃.rd]; rfl
  have wr₇ : s₇.wr = s.wr := by
    show s₅.wr = s.wr; rw [o₅.wr]; show s₃.wr = s.wr; rw [o₃.wr]; rfl
  have sp₇ : s₇.sp = s.sp := by
    show s₅.sp = s.sp; rw [o₅.sp]; show s₃.sp = s.sp; rw [o₃.sp]; rfl
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_, m₇, rd₇, wr₇, sp₇⟩
  · simp only [tbyte, v₇]
    by_cases h15 : k / 16 = 15
    · rw [h15, show s₆.v (treg 15) = s₅.v .v7 from v_setV_self _ _ _,
        keep₅ _ (by decide), v_setV_self, tab₃ 0 (by decide),
        show (k + 16) % 256 / 16 = 0 by omega, show (k + 16) % 256 % 16 = k % 16 by omega]
    · rw [v_setV_of_ne _ _ (fun e => h15 (treg_inj _ (by omega) _ (by decide) e)),
        v₅ _ (by omega), ite_eq_left (show k / 16 < 15 by omega),
        v_setV_of_ne _ _ ((show NotTable .v7 by decide).ne _), tab₃ _ (by omega),
        show (k + 16) % 256 / 16 = k / 16 + 1 by omega, show (k + 16) % 256 % 16 = k % 16 by omega]
  · rw [v₇, v_setV_of_ne _ _ ((show NotTable (dq 0) by decide).ne _ |>.symm),
      keep₅ _ (by decide), v_setV_of_ne _ _ (by decide), o₃.2 _ (by decide), j₂]
  · rw [v₇, v_setV_of_ne _ _ ((show NotTable negBase by decide).ne _ |>.symm),
      keep₅ _ (by decide), v_setV_of_ne _ _ (by decide), n₃]
  · simp only [s₇, State.write, State.read, BitVec.setWidth_eq, ite_true]
    rw [g₆]; rfl
  · simp only [s₇, State.write, BitVec.setWidth_eq, hr, ite_false]
    rw [g₆]
  · simp only [rotRegs, List.mem_cons, List.mem_map, List.mem_range, not_or, not_exists,
      not_and] at hr
    obtain ⟨h7, hd, hn, ht⟩ := hr
    rw [v₇, v_setV_of_ne _ _ (fun e => ht 15 (by decide) e.symm), keep₅ r (fun a ha e => ht a (by omega) e),
      v_setV_of_ne _ _ h7, o₃.2 r (by simp [hn]), v_setV_of_ne _ _ hd, v_setV_of_ne _ _ h7]

end VG.Proof.Rc4.AArch64
