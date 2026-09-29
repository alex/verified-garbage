import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Md5.Spec
import VerifiedGarbage.Impl.Md5.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# MD5 compression function on x86-64: the 64 operations

Untrusted: everything here is checked by Lean. Each operation is the
auxiliary function of its round, symbolically executed once per round
(`fn_ok`), followed by the additions and the rotation, symbolically executed
once for all operations (`tail_ok`).
-/

namespace VG.Proof.Md5.X86_64

open VG VG.X86_64 VG.Impl.Md5.X86_64
open VG.Spec.Md5 (HashValue Word Block ks Ts roundFn F G H I)

/-- The words `v` are in the registers of operation `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0].setWidth 64 ∧ s.gpr (var t 1) = v[1].setWidth 64 ∧
  s.gpr (var t 2) = v[2].setWidth 64 ∧ s.gpr (var t 3) = v[3].setWidth 64

/-- The registers that hold pointers and the count, and `rsp`: never written by the operations. -/
def pubRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .rsp]

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

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T0 ∧ ∀ p ∈ pubRegs, r ≠ p := by
  simp only [work, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem var_ne_T0 (t k : Nat) : var t k ≠ T0 := (work_ne (var_mem t k)).1

theorem var_ne_pub (t k : Nat) {p : Reg} (hp : p ∈ pubRegs) : var t k ≠ p :=
  (work_ne (var_mem t k)).2 p hp

theorem var_ne_aux : ∀ c < 4, ∀ i < 4, ∀ j < 4, i ≠ j →
    work.getD ((i + 4 - c) % 4) .rax ≠ work.getD ((j + 4 - c) % 4) .rax := by decide

/-- The registers of an operation are all different. -/
theorem var_ne (t : Nat) {i j : Nat} (hi : i < 4) (hj : j < 4) (h : i ≠ j) : var t i ≠ var t j :=
  var_ne_aux (t % 4) (Nat.mod_lt _ (by omega)) i hi j hj h

/-! ## The auxiliary functions -/

theorem fn_ok (r : Nat) (hr : r < 4) (b c d : Reg) (hb : b ≠ T0) (hc : c ≠ T0) (hd : d ≠ T0)
    (s : State) (vb vc vd : Word) (h₁ : s.gpr b = vb.setWidth 64) (h₂ : s.gpr c = vc.setWidth 64)
    (h₃ : s.gpr d = vd.setWidth 64) :
    WP isa (.block (fn r b c d)) s fun s' =>
      s'.gpr T0 = (roundFn r vb vc vd).setWidth 64 ∧ (∀ x, x ≠ T0 → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [T0] at hb hc hd ⊢
  apply WP.of_runBlock
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [fn, T0, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, readSrc32,
    isa, State.setReg32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, ite_true, ite_false, hb, hc, hd,
    h₁, h₂, h₃, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨?_, fun x hx => by simp [hx], trivial⟩
  · rw [show roundFn 0 = F from rfl, F_eq]
  · rw [show roundFn 1 = G from rfl, G_eq]
  · rfl
  · rw [show roundFn 3 = I from rfl, I_eq]

/-! ## The rest of an operation -/

/-- The instructions of an operation after the auxiliary function. -/
def tailI (a b : Reg) (k : Nat) (T : Word) (n : Nat) : List Instr := [
  .alu32 .add a (.reg T0),
  .alu32 .add a (.mem (at_ .rsi (4 * k))),
  .alu32 .add a (.imm T),
  .shift32 .ror a n,
  .alu32 .add a (.reg b)]

theorem step_split (t : Nat) :
    step t = fn (t / 16) (var t 1) (var t 2) (var t 3) ++
      tailI (var t 0) (var t 1) (ks.getD t 0) (Ts.getD t 0) (32 - Proof.Md5.rot t) := rfl

theorem tail_ok (a b : Reg) (k : Nat) (T : Word) (n : Nat) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 31)
    (hab : a ≠ b) (hsi : a ≠ .rsi)
    (s : State) (va vb f x : Word) (bp : Addr)
    (h₁ : s.gpr a = va.setWidth 64) (h₂ : s.gpr b = vb.setWidth 64) (h₃ : s.gpr T0 = f.setWidth 64)
    (hrsi : s.gpr .rsi = bp) (hin : InRegions (s.rd ++ s.wr) (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4)
    (hx : s.mem.readW (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = x) :
    WP isa (.block (tailI a b k T n)) s fun s' =>
      s'.gpr a = ((va + f + x + T).rotateRight n + vb).setWidth 64 ∧
      (∀ r, r ≠ a → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsi' : Reg.rsi ≠ a := fun h => hsi h.symm
  have hba : b ≠ a := fun h => hab h.symm
  simp only [T0] at h₃
  apply WP.of_runBlock
  simp (config := {decide := true}) only [tailI, T0, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, execShift32, readSrc32, State.ea, State.load32, at_,
    isa, State.setReg32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, ite_true, ite_false, hsi', hba,
    hn₁, hn₂, and_self, h₁, h₂, h₃, hrsi, hin, hx, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

/-! ## One operation -/

/-- The operation is symbolically executed once per round for the auxiliary
function and once for the rest, for any registers `a … d`. -/
theorem step_ok (t : Nat) (ht : t < 64) (s : State) (v : HashValue) (X : Block) (bp : Addr)
    (hv : Vars t s v) (hrsi : s.gpr .rsi = bp)
    (hin : ∀ k < 16, InRegions (s.rd ++ s.wr) (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4)
    (hX : ∀ k (hk : k < 16), s.mem.readW (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = X ⟨k, hk⟩) :
    WP isa (.block (step t)) s fun s' =>
      Vars (t + 1) s' (Spec.Md5.step X v t) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3⟩ := hv
  have hk := ks_lt t ht
  have hr := rot_range t ht
  rw [step_split, WP.block_append_iff]
  refine WP.mono (fn_ok (t / 16) (by omega) _ _ _ (var_ne_T0 t 1) (var_ne_T0 t 2) (var_ne_T0 t 3) s
    v[1] v[2] v[3] h1 h2 h3) fun s₁ ⟨f₁, e₁, m₁, rd₁, wr₁⟩ => ?_
  have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k => e₁ _ (var_ne_T0 t k)
  refine WP.mono (tail_ok (var t 0) (var t 1) (ks.getD t 0) (Ts.getD t 0) (32 - rot t) (by omega)
    (by omega) (var_ne t (by omega) (by omega) (by omega))
    (var_ne_pub t 0 (by simp [pubRegs])) s₁ v[0] v[1] (roundFn (t / 16) v[1] v[2] v[3]) (X ⟨ks.getD t 0, hk⟩) bp
    (by rw [e]; exact h0) (by rw [e]; exact h1) f₁ (by rw [e₁ _ (by decide)]; exact hrsi)
    (by rw [rd₁, wr₁]; exact hin _ hk) (by rw [m₁]; exact hX _ hk))
    fun s₂ ⟨a₂, e₂, m₂, rd₂, wr₂⟩ => ?_
  have g : ∀ r, r ≠ var t 0 → r ≠ T0 → s₂.gpr r = s.gpr r := fun r h h' => by rw [e₂ r h, e₁ r h']
  refine ⟨?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun r hr =>
    g r (fun h => var_ne_pub t 0 hr h.symm) (fun h => by subst h; simp [pubRegs, T0] at hr)⟩
  rw [step_eq X v ht]
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 3 by omega),
    var_succ t _ (show 1 < 3 by omega), var_succ t _ (show 2 < 3 by omega), stepKX,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 3), h3]
  · rw [a₂, rotateLeft_eq _ hr.1 hr.2, BitVec.add_comm (v[1])]
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 1), h1]
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 2), h2]

/-! ## The 64 operations -/

/-- Invariant, relative to the state `sB` at the start of the operations. -/
structure RInv (H : HashValue) (X : Block) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (Spec.Md5.steps H X t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  mem : s.mem = sB.mem

theorem steps_ok (H : HashValue) (X : Block) (bp : Addr) (sB : State) (hrsi : sB.gpr .rsi = bp)
    (hin : ∀ k < 16, InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4)
    (hX : ∀ k (hk : k < 16), sB.mem.readW (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = X ⟨k, hk⟩)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 64, WP isa (steps t) sB (RInv H X sB t) := by
  intro t ht
  induction t with
  | zero => exact WP.block_nil (M := isa) ⟨h0, fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    have hs_rsi : s.gpr .rsi = bp := (hs.pub .rsi (by decide)).trans hrsi
    refine WP.mono (step_ok t (by omega) s _ X bp hs.vars hs_rsi (by rw [hs.rd, hs.wr]; exact hin)
      (by rw [hs.mem]; exact hX)) fun s' ⟨hv, hm, hrd, hwr, hp⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hp r hr, hs.pub r hr], by rw [hrd, hs.rd], by rw [hwr, hs.wr],
      by rw [hm, hs.mem]⟩
    rw [Proof.Md5.steps_succ]; exact hv

end VG.Proof.Md5.X86_64
