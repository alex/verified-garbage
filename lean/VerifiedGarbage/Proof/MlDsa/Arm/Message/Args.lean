import VerifiedGarbage.Proof.MlDsa.Arm.Message.Step

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: the moves of a call's arguments

Untrusted: everything here is checked by Lean. Each argument's value
(`Arg.val`): a saved argument (a slot at `r7 + f`), plus an offset, an
offset from `r7`, an immediate, or `r0`. The moves of a list of arguments
into distinct registers but `r7`, with `r0` read only before it is written
(`argsOk`), leave each its value and change nothing else (`setArgs_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.MlDsa.Arm.Message.Arg.val (s : State) : Arg → BitVec 32
  | .slot f => s.mem.readW (State.addr (s.gpr .r7 + BitVec.ofNat 32 f)) 32
  | .slotOff f o => s.mem.readW (State.addr (s.gpr .r7 + BitVec.ofNat 32 f)) 32 + BitVec.ofNat 32 o
  | .off o => s.gpr .r7 + BitVec.ofNat 32 o
  | .imm v => BitVec.ofNat 32 v
  | .ret => s.gpr .r0

/-- A slot within the 1 KiB, an offset or an immediate the instructions take. -/
def _root_.VG.Impl.MlDsa.Arm.Message.Arg.ok : Arg → Bool
  | .slot f => decide (f + 4 ≤ 1024)
  | .slotOff f o => decide (f + 4 ≤ 1024) && encodable (BitVec.ofNat 32 o)
  | .off o => decide (o < 65536)
  | .imm v => decide (v < 65536)
  | .ret => true

def _root_.VG.Impl.MlDsa.Arm.Message.Arg.isRet : Arg → Bool
  | .ret => true
  | _ => false

/-- The slots of the 1 KiB are readable. -/
abbrev XOk (s : State) : Prop :=
  ∀ f, f + 4 ≤ 1024 → InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r7 + BitVec.ofNat 32 f)) 4

theorem setWidth_ofNat16 {v : Nat} (h : v < 65536) : (BitVec.ofNat 16 v).setWidth 32 = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem Arg.mov_ok (d : Reg) (hd : d ≠ .r7) (a : Arg) (ha : a.ok = true) (s : State) (hx : XOk s) :
    WP isa (.block (a.mov d)) s fun s1 => s1.gpr d = a.val s ∧ Only [d] s s1 := by
  cases a with
  | slot f =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    exact wp_ldr (by omega) (hx f ha) fun s1 o1 e1 => wp_nil ⟨e1, o1⟩
  | slotOff f o =>
    simp only [Arg.ok, Bool.and_eq_true, decide_eq_true_eq] at ha
    refine wp_ldr (by omega) (hx f ha.1) fun s1 o1 e1 => ?_
    refine wp_addImm ha.2 fun s2 o2 e2 => wp_nil ⟨by rw [e2, e1]; rfl, ?_⟩
    exact (o1.trans o2).mono (fun r hr => by simpa using hr)
  | off o =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    refine wp_movw fun s1 o1 e1 => wp_addReg fun s2 o2 e2 => wp_nil ⟨?_, (o1.trans o2).mono fun r hr => by simpa using hr⟩
    rw [e2, e1, o1.get .r7 (by simpa using hd.symm), setWidth_ofNat16 ha]
    rfl
  | imm v =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    exact wp_movw fun s1 o1 e1 => wp_nil ⟨by rw [e1, setWidth_ofNat16 ha]; rfl, o1⟩
  | ret => exact wp_movReg fun s1 o1 e1 => wp_nil ⟨e1, o1⟩

/-- Distinct registers but `r7`, each argument fit for its instructions,
and `r0` read only before it is written. -/
def argsOk : List (Reg × Arg) → Bool
  | [] => true
  | (d, a) :: as => a.ok && d != .r7 &&
      as.all (fun da => da.1 != d && (d != .r0 || !da.2.isRet)) && argsOk as

/-- The value of an argument is the same after a move into another register
(not `r7`, and not `r0` if the argument is `r0`). -/
theorem Arg.val_only {d : Reg} (hd : d ≠ .r7) {s s1 : State} (o : Only [d] s s1) (a : Arg)
    (ha : d ≠ .r0 ∨ a.isRet = false) : a.val s1 = a.val s := by
  have h7 : s1.gpr .r7 = s.gpr .r7 := o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hd h.symm)
  cases a with
  | ret =>
    simp only [Arg.isRet, Bool.true_eq_false, or_false] at ha
    simp only [Arg.val]
    exact o.gpr _ (by simp only [List.mem_singleton]; exact fun h => ha h.symm)
  | _ => simp only [Arg.val, h7, o.mem]

theorem XOk.only {d : Reg} (hd : d ≠ .r7) {s s1 : State} (o : Only [d] s s1) (h : XOk s) : XOk s1 := by
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
    refine WP.mono (Arg.mov_ok d hd a ha s hx) fun s1 ⟨h1, o1⟩ => ?_
    refine WP.mono (setArgs_ok as hrest s1 (hx.only hd o1)) fun s2 ⟨h2, o2⟩ => ⟨fun da hda => ?_, ?_⟩
    · rcases List.mem_cons.mp hda with rfl | hda
      · rw [o2.gpr _ (fun hm => by
          obtain ⟨x, hx', hx''⟩ := List.mem_map.mp hm
          exact (hall x hx').1 hx''), h1]
      · rw [h2 da hda, Arg.val_only hd o1 da.2 ((hall da hda).2.elim .inl fun h' => .inr h')]
    · exact (o1.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
        (o2.mono fun r hr => by simp only [List.map_cons]; exact List.mem_cons_of_mem _ hr)

/-! ## In `Ctx` -/

section
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem Ctx.xOk (hc : Ctx L g m₀ t) (hL : L.Ok) : XOk t := fun f hf => by
  rw [hc.r7, hL.xo (by omega)]; exact hc.inX hL hf

theorem Ctx.off (hc : Ctx L g m₀ t) (o : Nat) : (Arg.off o).val t = L.X32 + BitVec.ofNat 32 o := by
  simp only [Arg.val, hc.r7]

/-- The saved argument `j`. -/
theorem Ctx.slotV (hc : Ctx L g m₀ t) (hL : L.Ok) {f j : Nat} (hf : f = 912 + 4 * j) (hj : j < 8) :
    (Arg.slot f).val t = L.vals.getD j 0 := by
  subst hf
  have := hc.slot j hj
  simp only [Arg.val, hc.r7]
  rw [hL.xo (by omega), ← this, show 904 + (8 + 4 * j) = 912 + 4 * j by omega]

end

end VG.Proof.MlDsa.Arm.Message
