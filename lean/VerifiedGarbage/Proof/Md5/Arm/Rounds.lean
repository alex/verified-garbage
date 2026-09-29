import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Md5.Spec
import VerifiedGarbage.Impl.Md5.Arm
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-!
# MD5 compression function on ARMv7: the 64 operations

Untrusted: everything here is checked by Lean. Each operation is the
auxiliary function of its round, symbolically executed once per round
(`fn_ok`), followed by the additions and the rotation, symbolically executed
once for all operations (`tail_ok`).
-/

namespace VG.Proof.Md5.Arm

open VG VG.Arm VG.Impl.Md5.Arm
open VG.Spec.Md5 (HashValue Word Block ks Ts roundFn F G H I)

/-- The words `v` are in the registers of operation `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0] ∧ s.gpr (var t 1) = v[1] ∧ s.gpr (var t 2) = v[2] ∧ s.gpr (var t 3) = v[3]

/-- The pointers, the count, `Ones` and the registers the operations never
write. -/
def pubRegs : List Reg := [.r0, .r1, .r2, .r3, .r8, .r10, .r11, .lr]

/-- The words move one register along each operation. -/
theorem var_succ (t k : Nat) (hk : k < 3) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 3 := by
  simp only [var]; congr 1; omega

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 4 - t % 4) % 4]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne' : ∀ r ∈ work, r ≠ T0 ∧ r ≠ T1 ∧ ∀ p ∈ pubRegs, r ≠ p := by decide

theorem var_ne_T0 (t k : Nat) : var t k ≠ T0 := (work_ne' _ (var_mem t k)).1

theorem var_ne_T1 (t k : Nat) : var t k ≠ T1 := (work_ne' _ (var_mem t k)).2.1

theorem var_ne_pub (t k : Nat) {p : Reg} (hp : p ∈ pubRegs) : var t k ≠ p :=
  (work_ne' _ (var_mem t k)).2.2 p hp

theorem var_ne_aux : ∀ c < 4, ∀ i < 4, ∀ j < 4, i ≠ j →
    work.getD ((i + 4 - c) % 4) .r4 ≠ work.getD ((j + 4 - c) % 4) .r4 := by decide

/-- The registers of an operation are all different. -/
theorem var_ne (t : Nat) {i j : Nat} (hi : i < 4) (hj : j < 4) (h : i ≠ j) : var t i ≠ var t j :=
  var_ne_aux (t % 4) (Nat.mod_lt _ (by omega)) i hi j hj h

/-! ## The auxiliary functions -/

theorem fn_ok (r : Nat) (hr : r < 4) (b c d : Reg) (hb : b ≠ T0) (hc : c ≠ T0) (hd : d ≠ T0)
    (s : State) (vb vc vd : Word) (h₁ : s.gpr b = vb) (h₂ : s.gpr c = vc)
    (h₃ : s.gpr d = vd) (h₄ : s.gpr Ones = ones) :
    WP isa (.block (fn r b c d)) s fun s' =>
      s'.gpr T0 = roundFn r vb vc vd ∧ (∀ x, x ≠ T0 → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [T0, Ones] at hb hc hd h₄ ⊢
  apply WP.of_runBlock
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [fn, T0, Ones, runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, ite_true, ite_false, hb, hc, hd,
    h₁, h₂, h₃, h₄, Option.map_some, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨?_, fun x hx => by simp [hx], trivial⟩
  · rw [show roundFn 0 = F from rfl, F_eq]
  · rw [show roundFn 1 = G from rfl, G_eq]
  · rfl
  · rw [show roundFn 3 = I from rfl, I_eq]; rfl

/-! ## The rest of an operation -/

/-- The instructions of an operation after the auxiliary function. -/
def tailI (a b : Reg) (k : Nat) (T : Word) (n : Nat) : List Instr := [
  .dp .add a a (.reg T0),
  .ldr T1 .r1 (4 * k),
  .dp .add a a (.reg T1),
  .movw T1 (T.extractLsb' 0 16),
  .movt T1 (T.extractLsb' 16 16),
  .dp .add a a (.reg T1),
  .dp .add a b (.shifted a .ror n)]

theorem step_split (t : Nat) :
    step t = fn (t / 16) (var t 1) (var t 2) (var t 3) ++
      tailI (var t 0) (var t 1) (ks.getD t 0) (Ts.getD t 0) (32 - Proof.Md5.rot t) := rfl

theorem tail_ok (a b : Reg) (k : Nat) (hk : k < 16) (T : Word) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 31) (hba : b ≠ a)
    (ha₁ : a ≠ T1) (hb₁ : b ≠ T1) (hax : a ≠ .r1)
    (s : State) (va vb f x : Word) (bp : BitVec 32)
    (h₁ : s.gpr a = va) (h₂ : s.gpr b = vb) (h₃ : s.gpr T0 = f)
    (hr1 : s.gpr .r1 = bp) (hin : InRegions (s.rd ++ s.wr) (State.addr (bp + BitVec.ofNat 32 (4 * k))) 4)
    (hx : s.mem.readW (State.addr (bp + BitVec.ofNat 32 (4 * k))) 32 = x) :
    WP isa (.block (tailI a b k T n)) s fun s' =>
      s'.gpr a = vb + (va + f + x + T).rotateRight n ∧
      (∀ r, r ≠ a → r ≠ T1 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have ho : 4 * k < 4096 := by omega
  have ha₁' : T1 ≠ a := fun h => ha₁ h.symm
  have hax' : Reg.r1 ≠ a := fun h => hax h.symm
  simp only [T0, T1] at h₃ ha₁ ha₁' hb₁ ⊢
  apply WP.of_runBlock
  simp (config := {decide := true}) only [tailI, T0, T1, runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, State.load32, ho, hn, ite_true, ite_false,
    ha₁, ha₁', hb₁, hba, hax', h₁, h₂, h₃, hr1, hin, hx, and_self,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [movw_movt], fun r hr hr' => by simp [hr, hr'], trivial⟩

/-! ## One operation -/

/-- The operation is symbolically executed once per round for the auxiliary
function and once for the rest, for any registers `a … d`. -/
theorem step_ok (t : Nat) (ht : t < 64) (s : State) (v : HashValue) (X : Block) (bp : BitVec 32)
    (hv : Vars t s v) (hr1 : s.gpr .r1 = bp) (hones : s.gpr Ones = ones)
    (hin : ∀ k < 16, InRegions (s.rd ++ s.wr) (State.addr (bp + BitVec.ofNat 32 (4 * k))) 4)
    (hX : ∀ k (hk : k < 16), s.mem.readW (State.addr (bp + BitVec.ofNat 32 (4 * k))) 32 = X ⟨k, hk⟩) :
    WP isa (.block (step t)) s fun s' =>
      Vars (t + 1) s' (Spec.Md5.step X v t) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3⟩ := hv
  have hk := ks_lt t ht
  have hr := rot_range t ht
  rw [step_split, WP.block_append_iff]
  refine WP.mono (fn_ok (t / 16) (by omega) _ _ _ (var_ne_T0 t 1) (var_ne_T0 t 2) (var_ne_T0 t 3) s
    v[1] v[2] v[3] h1 h2 h3 hones) fun s₁ ⟨f₁, e₁, m₁, rd₁, wr₁⟩ => ?_
  have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k => e₁ _ (var_ne_T0 t k)
  refine WP.mono (tail_ok (var t 0) (var t 1) (ks.getD t 0) hk (Ts.getD t 0) (32 - rot t)
    (by omega) (var_ne t (by omega) (by omega) (by omega)) (var_ne_T1 t 0)
    (var_ne_T1 t 1) (var_ne_pub t 0 (by decide)) s₁ v[0] v[1] (roundFn (t / 16) v[1] v[2] v[3])
    (X ⟨ks.getD t 0, hk⟩) bp (by rw [e]; exact h0) (by rw [e]; exact h1) f₁
    (by rw [e₁ _ (by decide)]; exact hr1)
    (by rw [rd₁, wr₁]; exact hin _ hk) (by rw [m₁]; exact hX _ hk))
    fun s₂ ⟨a₂, e₂, m₂, rd₂, wr₂⟩ => ?_
  have g : ∀ r, r ≠ var t 0 → r ≠ T0 → r ≠ T1 → s₂.gpr r = s.gpr r := fun r h h' h'' => by
    rw [e₂ r h h'', e₁ r h']
  refine ⟨?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun r hr =>
    g r (fun h => var_ne_pub t 0 hr h.symm) (fun h => by subst h; simp [pubRegs, T0] at hr)
      (fun h => by subst h; simp [pubRegs, T1] at hr)⟩
  rw [step_eq X v ht]
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 3 by omega),
    var_succ t _ (show 1 < 3 by omega), var_succ t _ (show 2 < 3 by omega), stepKX,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 3) (var_ne_T1 t 3), h3]
  · rw [a₂, rotateLeft_eq _ hr.1 hr.2]
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 1) (var_ne_T1 t 1), h1]
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 2) (var_ne_T1 t 2), h2]

/-! ## The 64 operations -/

/-- Invariant, relative to the state `sB` at the start of the operations. -/
structure RInv (H : HashValue) (X : Block) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (Spec.Md5.steps H X t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  mem : s.mem = sB.mem

theorem steps_ok (H : HashValue) (X : Block) (bp : BitVec 32) (sB : State) (hr1 : sB.gpr .r1 = bp)
    (hones : sB.gpr Ones = ones)
    (hin : ∀ k < 16, InRegions (sB.rd ++ sB.wr) (State.addr (bp + BitVec.ofNat 32 (4 * k))) 4)
    (hX : ∀ k (hk : k < 16), sB.mem.readW (State.addr (bp + BitVec.ofNat 32 (4 * k))) 32 = X ⟨k, hk⟩)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 64, WP isa (steps t) sB (RInv H X sB t) := by
  intro t ht
  induction t with
  | zero => exact WP.block_nil (M := isa) ⟨h0, fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    have hs_r1 : s.gpr .r1 = bp := (hs.pub .r1 (by decide)).trans hr1
    have hs_ones : s.gpr Ones = ones := (hs.pub .r8 (by decide)).trans hones
    refine WP.mono (step_ok t (by omega) s _ X bp hs.vars hs_r1 hs_ones
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.mem]; exact hX)) fun s' ⟨hv, hm, hrd, hwr, hp⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hp r hr, hs.pub r hr], by rw [hrd, hs.rd], by rw [hwr, hs.wr],
      by rw [hm, hs.mem]⟩
    rw [Proof.Md5.steps_succ]; exact hv

end VG.Proof.Md5.Arm
