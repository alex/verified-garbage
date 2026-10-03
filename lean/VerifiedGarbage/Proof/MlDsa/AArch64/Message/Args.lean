import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Layout

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: the moves of a call's arguments

Untrusted: everything here is checked by Lean. Each argument's value
(`Arg.val`): a saved argument (a slot at `x28 + f`), plus an offset, an
offset from `x28`, an immediate, or `x0`. The moves of a list of arguments
into distinct registers but `x28`, with `x0` read only before it is written
(`argsOk`), leave each its value and change nothing else (`setArgs_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only wp_nil wp_ldrx wp_addImm wp_movz)

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.MlDsa.AArch64.Message.Arg.val (s : State) : Arg → BitVec 64
  | .slot f => s.mem.readW (s.gpr .x28 + BitVec.ofNat 64 f) 64
  | .slotOff f o => s.mem.readW (s.gpr .x28 + BitVec.ofNat 64 f) 64 + BitVec.ofNat 64 o
  | .off o => s.gpr .x28 + BitVec.ofNat 64 o
  | .imm v => BitVec.ofNat 64 v
  | .ret => s.gpr .x0

/-- A slot within the 1 KiB, an offset or an immediate the instructions take. -/
def _root_.VG.Impl.MlDsa.AArch64.Message.Arg.ok : Arg → Bool
  | .slot f => decide (f % 8 = 0) && decide (f + 8 ≤ 1024)
  | .slotOff f o => decide (f % 8 = 0) && decide (f + 8 ≤ 1024) && decide (o < 4096)
  | .off o => decide (o < 4096)
  | .imm v => decide (v < 65536)
  | .ret => true

def _root_.VG.Impl.MlDsa.AArch64.Message.Arg.isRet : Arg → Bool
  | .ret => true
  | _ => false

/-- The slots of the 1 KiB are readable. -/
abbrev XOk (s : State) : Prop := ∀ f, f + 8 ≤ 1024 → InRegions (s.rd ++ s.wr) (s.gpr .x28 + BitVec.ofNat 64 f) 8

theorem Arg.mov_ok (d : Reg) (a : Arg) (ha : a.ok = true) (s : State) (hx : XOk s) :
    WP isa (.block (a.mov d)) s fun s1 => s1.gpr d = a.val s ∧ Only [d] s s1 := by
  cases a with
  | slot f =>
    simp only [Arg.ok, Bool.and_eq_true, decide_eq_true_eq] at ha
    refine wp_ldrx ⟨ha.1, by omega⟩ rfl (hx f ha.2) fun s1 o1 e1 => wp_nil ⟨e1, o1⟩
  | slotOff f o =>
    simp only [Arg.ok, Bool.and_eq_true, decide_eq_true_eq] at ha
    refine wp_ldrx ⟨ha.1.1, by omega⟩ rfl (hx f ha.1.2) fun s1 o1 e1 => ?_
    refine wp_addImm ha.2 fun s2 o2 e2 => wp_nil ⟨by rw [e2, e1]; rfl, ?_⟩
    exact (o1.trans o2).mono (fun r hr => by simpa using hr)
  | off o =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    exact wp_addImm ha fun s1 o1 e1 => wp_nil ⟨e1, o1⟩
  | imm v =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    refine wp_movz fun s1 o1 e1 => wp_nil ⟨?_, o1⟩
    rw [e1]
    apply BitVec.eq_of_toNat_eq
    simp only [Arg.val, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  | ret =>
    exact wp_addImm (by decide) fun s1 o1 e1 => wp_nil ⟨by rw [e1, BitVec.add_zero]; rfl, o1⟩

/-- Distinct registers but `x28`, each argument fit for its instructions,
and `x0` read only before it is written. -/
def argsOk : List (Reg × Arg) → Bool
  | [] => true
  | (d, a) :: as => a.ok && d != .x28 &&
      as.all (fun da => da.1 != d && (d != .x0 || !da.2.isRet)) && argsOk as

/-- The value of an argument is the same after a move into another register
(not `x28`, and not `x0` if the argument is `x0`). -/
theorem Arg.val_only {d : Reg} (hd : d ≠ .x28) {s s1 : State} (o : Only [d] s s1) (a : Arg)
    (ha : d ≠ .x0 ∨ a.isRet = false) : a.val s1 = a.val s := by
  have h28 : s1.gpr .x28 = s.gpr .x28 := o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hd h.symm)
  cases a with
  | ret =>
    simp only [Arg.isRet, Bool.true_eq_false, or_false] at ha
    simp only [Arg.val]
    exact o.gpr _ (by simp only [List.mem_singleton]; exact fun h => ha h.symm)
  | _ => simp only [Arg.val, h28, o.mem]

theorem XOk.only {d : Reg} (hd : d ≠ .x28) {s s1 : State} (o : Only [d] s s1) (h : XOk s) : XOk s1 := by
  intro f hf
  rw [o.rd, o.wr, o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hd h.symm)]
  exact h f hf

/-- The moves of the arguments `as`. -/
theorem setArgs_ok : ∀ (as : List (Reg × Arg)), argsOk as = true → ∀ s : State, XOk s →
    WP isa (.block (setArgs as)) s fun s1 => (∀ da ∈ as, s1.gpr da.1 = da.2.val s) ∧ Only (as.map (·.1)) s s1
  | [], _, s, _ => wp_nil ⟨fun _ h => by simp at h, Only.refl _ _⟩
  | (d, a) :: as, h, s, hx => by
    simp only [argsOk, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at h
    obtain ⟨⟨⟨ha, hd⟩, hall⟩, hrest⟩ := h
    simp only [setArgs, List.flatMap_cons]
    rw [WP.block_append_iff]
    refine WP.mono (Arg.mov_ok d a ha s hx) fun s1 ⟨h1, o1⟩ => ?_
    refine WP.mono (setArgs_ok as hrest s1 (hx.only hd o1)) fun s2 ⟨h2, o2⟩ => ⟨fun da hda => ?_, ?_⟩
    · rcases List.mem_cons.mp hda with rfl | hda
      · rw [o2.gpr _ (fun hm => by
          obtain ⟨x, hx', hx''⟩ := List.mem_map.mp hm
          exact (hall x hx').1 hx''), h1]
      · rw [h2 da hda, Arg.val_only hd o1 da.2 ((hall da hda).2.elim .inl fun h' => .inr h')]
    · exact (o1.trans o2).mono (by simp)

/-! ## In `Ctx` -/

section
variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem Ctx.xOk (hc : Ctx L g v m₀ t) (hL : L.Ok) : XOk t := fun f hf => by
  rw [hc.x28]; exact hc.inX hL hf (by omega)

theorem Ctx.off (hc : Ctx L g v m₀ t) (o : Nat) : (Arg.off o).val t = L.X + BitVec.ofNat 64 o := by
  simp only [Arg.val, hc.x28]

/-- The saved argument `j`. -/
theorem Ctx.slotJ (hc : Ctx L g v m₀ t) {j : Nat} (hj : j < 8) :
    (Arg.slot (920 + 8 * j)).val t = L.vals.getD j 0 := by
  have := hc.slot j hj
  simp only [Arg.val, hc.x28]
  rw [add_add] at this
  rw [← this, show 904 + (16 + 8 * j) = 920 + 8 * j by omega]

end

end VG.Proof.MlDsa.AArch64.Message
