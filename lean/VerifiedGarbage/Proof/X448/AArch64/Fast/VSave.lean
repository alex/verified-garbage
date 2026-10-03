import VerifiedGarbage.Proof.X448.AArch64.Fast.Env
import VerifiedGarbage.Proof.Curve448.AArch64.Neon.NFinish
import VerifiedGarbage.Proof.X448.AArch64.Weak.Iter

/-!
# X448 on AArch64: saving `v8`–`v15`

Untrusted: everything here is checked by Lean. The AdvSIMD products use
every vector register, so the function saves `v8`–`v15` (whose low halves
are callee-saved) at `VSAVE`, past everything else it writes, and restores
them last.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Fast (VSAVE vsave vrestore)
open VG.Impl.Curve448.AArch64.Neon (V ldq stq)
open VG.Proof.Curve448.AArch64.Neon (exec_ldq exec_stq off_add st_outside read16_write scr_of setMem setMem_mem V_ne)
open VG.Proof.X448.AArch64 (Scr off Outside Outside2 FieldMem ofs)
open VG.Proof.X448.AArch64.Weak (ofs_off')

theorem _root_.VG.Proof.X448.AArch64.Outside.read16 {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat} (hd : d + 16 ≤ o ∨ o + n ≤ d) (hd' : d + 16 ≤ 8192) :
    m'.read (off base d) 16 = m.read (off base d) 16 :=
  (Mem.read_congr fun i hi => (h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)]; omega)).symm).symm

/-- The low halves of `v8`–`v15` of `v`, saved in the working space. -/
def SavedV (base : Addr) (v : VReg → BitVec 128) (m : Mem) : Prop :=
  ∀ k < 8, (m.read (off base (VSAVE + 16 * k)) 16).extractLsb' 0 64 = (v (V (8 + k))).extractLsb' 0 64

theorem SavedV.frame {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : SavedV base v m)
    (he : ∀ d, VSAVE ≤ d → d < VSAVE + 128 → m' (off base d) = m (off base d)) : SavedV base v m' := by
  intro k hk
  rw [← h k hk, Mem.read_congr fun i hi => ?_]
  have hV : VSAVE = 4736 := rfl
  rw [off_add]
  exact he _ (by omega) (by omega)

theorem SavedV.outside2 {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : SavedV base v m)
    {x nx y ny : Nat} (ho : Outside2 base x nx y ny m m') (hx : x + nx ≤ VSAVE) (hy : y + ny ≤ VSAVE) :
    SavedV base v m' :=
  h.frame fun d h1 h2 => ho _ (by rw [ofs_off' base (by simp only [VSAVE] at h2; omega)]; omega)
    (by rw [ofs_off' base (by simp only [VSAVE] at h2; omega)]; omega)

theorem SavedV.outside {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : SavedV base v m)
    {o n : Nat} (ho : Outside base o n m m') (hx : o + n ≤ VSAVE ∨ VSAVE + 128 ≤ o) : SavedV base v m' :=
  h.frame fun d h1 h2 => ho _ (by rw [ofs_off' base (by simp only [VSAVE] at h2; omega)]; omega)

theorem SavedV.field {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : SavedV base v m)
    {o : Nat} (ho : FieldMem base o m m') (hx : o + 128 ≤ VSAVE) : SavedV base v m' := by
  have hA : ACC = 3584 := rfl
  have hV : VSAVE = 4736 := rfl
  exact h.frame fun d h1 h2 => ho _ (by rw [ofs_off' base (by omega)]; omega)
    (by rw [ofs_off' base (by omega)]; omega)

/-- Away from the output: `hfar` as `output_word` takes it. -/
theorem SavedV.output {base p : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : SavedV base v m)
    {n : Nat} (ho : Outside p 0 n m m') (hn : n ≤ 56) (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) :
    SavedV base v m' :=
  h.frame fun d h1 h2 => ho _ (Or.inr (Nat.le_trans (by omega) (hfar d (by simp only [VSAVE] at h2; omega))))

theorem vsave_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block vsave) s fun t =>
      SavedV base s.v t.mem ∧ Outside base VSAVE 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  have hV : VSAVE = 4736 := rfl
  have e : vsave = (List.range 8).flatMap fun k => [stq (8 + k) (VSAVE + 16 * k)] := by
    simp only [vsave]; rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, t.mem.read (off base (VSAVE + 16 * k)) 16 = s.v (V (8 + k))) ∧
    Outside base VSAVE 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.v = s.v ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tO, tg, tvv, tr, tw⟩ => ?_) 8
    (by decide) s ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, rfl, rfl, rfl, rfl⟩)
    fun t ⟨tv, tO, tg, _, tr, tw⟩ => ⟨fun k hk => by rw [tv k hk], tO, tg, tr, tw⟩
  have ts : Scr t base := scr_of hs tg tw
  refine WP.block_cons_iff.mpr ⟨_, exec_stq ts (8 + n) (d := VSAVE + 16 * n) (by omega) (by omega),
    WP.block_nil_iff.mpr ⟨fun k hk => ?_, tO.trans ((st_outside _ _ _ (by omega)).mono (by omega) (by omega)),
      tg, tvv, tr, tw⟩⟩
  simp only [setMem_mem]
  by_cases h : k = n
  · subst h; rw [read16_write, tvv]
  · rw [((st_outside t.mem base (t.v (V (8 + n))) (d := VSAVE + 16 * n) (by omega))).read16 (by omega)
      (by omega)]
    exact tv k (by omega)

theorem vrestore_ok {s : State} {base : Addr} (hs : Scr s base) {v : VReg → BitVec 128}
    (hsv : SavedV base v s.mem) :
    WP isa (.block vrestore) s fun t =>
      (∀ k < 8, (t.v (V (8 + k))).extractLsb' 0 64 = (v (V (8 + k))).extractLsb' 0 64) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hV : VSAVE = 4736 := rfl
  have e : vrestore = (List.range 8).flatMap fun k => [ldq (8 + k) (VSAVE + 16 * k)] := by
    simp only [vrestore]; rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, (t.v (V (8 + k))).extractLsb' 0 64 = (v (V (8 + k))).extractLsb' 0 64) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tm, tg, tr, tw⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl, rfl, rfl⟩
  have ts : Scr t base := scr_of hs tg tw
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq ts (8 + n) (d := VSAVE + 16 * n) (by omega) (by omega),
    WP.block_nil_iff.mpr ⟨fun k hk => ?_, by rw [RegUpd.mem_setV, tm], by rw [RegUpd.gpr_setV, tg],
      by rw [RegUpd.rd_setV, tr], by rw [RegUpd.wr_setV, tw]⟩⟩
  by_cases h : k = n
  · subst h; rw [RegUpd.v_setV_self, tm]; exact hsv k hn
  · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by omega) (by omega))]
    exact tv k (by omega)

end VG.Proof.X448.AArch64.Fast
