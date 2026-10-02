import VerifiedGarbage.Proof.MlDsa.X86.Message.Layout

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: the moves of a call's arguments

Untrusted: everything here is checked by Lean. Each argument's value
(`Arg.val`): an argument of the function (at `[esp + 20 + 4i]`), plus an
offset, an offset from `esi`, an immediate, or `eax`. The moves of a list
of arguments into distinct registers but `esp` and `esi`, with `eax` read
only before it is written (`argsOk`), leave each its value and change
nothing else (`setArgs_ok`).
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Only)

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.MlDsa.X86.Message.Arg.val (s : State) : Arg → BitVec 32
  | .arg i => s.mem.readW (addr (s.gpr .esp) (20 + 4 * i)) 32
  | .argOff i o => s.mem.readW (addr (s.gpr .esp) (20 + 4 * i)) 32 + BitVec.ofNat 32 o
  | .off o => s.gpr .esi + BitVec.ofNat 32 o
  | .imm v => BitVec.ofNat 32 v
  | .ret => s.gpr .eax

/-- An argument of the function among its `n`. -/
def _root_.VG.Impl.MlDsa.X86.Message.Arg.ok (n : Nat) : Arg → Bool
  | .arg i => decide (i < n)
  | .argOff i _ => decide (i < n)
  | _ => true

def _root_.VG.Impl.MlDsa.X86.Message.Arg.isRet : Arg → Bool
  | .ret => true
  | _ => false

/-- The arguments of the function are readable. -/
abbrev AOk (n : Nat) (s : State) : Prop := ∀ i < n, InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (20 + 4 * i)) 4

theorem only_upd {s s' : State} {d : Reg} {v : BitVec 32} (u : Upd s s' d v) : Only [d] s s' :=
  ⟨fun r hr => u.other r (by simpa using hr), u.mem, u.rd, u.wr⟩

theorem Arg.set_ok {n : Nat} (d : Reg) (a : Arg) (ha : a.ok n = true) (s : State) (hx : AOk n s) :
    WP isa (.block (a.set d)) s fun s1 => s1.gpr d = a.val s ∧ Only [d] s s1 := by
  cases a with
  | arg i =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    exact wp_ldm (b := .esp) rfl (hx i ha) fun s1 u => WP.block_nil ⟨u.gpr, only_upd u⟩
  | argOff i o =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    refine wp_ldm (b := .esp) rfl (hx i ha) fun s1 u1 => wp_addi fun s2 u2 => WP.block_nil ⟨?_, ?_⟩
    · rw [u2.gpr, u1.gpr]; rfl
    · exact ((only_upd u1).trans (only_upd u2)).mono fun r hr => by simpa using hr
  | off o =>
    refine wp_mov fun s1 u1 => wp_addi fun s2 u2 => WP.block_nil ⟨?_, ?_⟩
    · rw [u2.gpr, u1.gpr]; rfl
    · exact ((only_upd u1).trans (only_upd u2)).mono fun r hr => by simpa using hr
  | imm v => exact wp_movi fun s1 u => WP.block_nil ⟨u.gpr, only_upd u⟩
  | ret => exact wp_mov fun s1 u => WP.block_nil ⟨u.gpr, only_upd u⟩

/-- Distinct registers but `esp` and `esi`, each argument fit, and `eax`
read only before it is written. -/
def argsOk (n : Nat) : List (Reg × Arg) → Bool
  | [] => true
  | (d, a) :: as => a.ok n && d != .esp && d != .esi &&
      as.all (fun da => da.1 != d && (d != .eax || !da.2.isRet)) && argsOk n as

/-- The value of an argument is the same after a move into another register
(not `esp` or `esi`, and not `eax` if the argument is `eax`). -/
theorem Arg.val_only {d : Reg} (hd : d ≠ .esp) (hs : d ≠ .esi) {s s1 : State} (o : Only [d] s s1) (a : Arg)
    (ha : d ≠ .eax ∨ a.isRet = false) : a.val s1 = a.val s := by
  have hsp : s1.gpr .esp = s.gpr .esp := o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hd h.symm)
  have hsi : s1.gpr .esi = s.gpr .esi := o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hs h.symm)
  cases a with
  | ret =>
    simp only [Arg.isRet, Bool.true_eq_false, or_false] at ha
    simp only [Arg.val]
    exact o.gpr _ (by simp only [List.mem_singleton]; exact fun h => ha h.symm)
  | _ => simp only [Arg.val, hsp, hsi, o.mem]

theorem AOk.only {n : Nat} {d : Reg} (hd : d ≠ .esp) {s s1 : State} (o : Only [d] s s1) (h : AOk n s) :
    AOk n s1 := by
  intro i hi
  rw [o.rd, o.wr, o.gpr _ (by simp only [List.mem_singleton]; exact fun h => hd h.symm)]
  exact h i hi

/-- The moves of the arguments `as`. -/
theorem setArgs_ok {n : Nat} : ∀ (as : List (Reg × Arg)), argsOk n as = true → ∀ s : State, AOk n s →
    WP isa (.block (setArgs as)) s fun s1 => (∀ da ∈ as, s1.gpr da.1 = da.2.val s) ∧ Only (as.map (·.1)) s s1
  | [], _, s, _ => WP.block_nil ⟨fun _ h => by simp at h, Only.refl _ _⟩
  | (d, a) :: as, h, s, hx => by
    simp only [argsOk, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨ha, hd⟩, hs⟩, hall⟩, hrest⟩ := h
    simp only [setArgs, List.flatMap_cons]
    rw [WP.block_append_iff]
    refine WP.mono (Arg.set_ok d a ha s hx) fun s1 ⟨h1, o1⟩ => ?_
    refine WP.mono (setArgs_ok as hrest s1 (hx.only hd o1)) fun s2 ⟨h2, o2⟩ => ⟨fun da hda => ?_, ?_⟩
    · rcases List.mem_cons.mp hda with rfl | hda
      · rw [o2.gpr _ (fun hm => by
          obtain ⟨x, hx', hx''⟩ := List.mem_map.mp hm
          exact (hall x hx').1 hx''), h1]
      · rw [h2 da hda, Arg.val_only hd hs o1 da.2 ((hall da hda).2.elim .inl fun h' => .inr h')]
    · exact (o1.trans o2).mono (by simp)

/-! ## In `Ctx` -/

section
variable {L : Lay} {m₁ : Mem} {t : State}

theorem Ctx.aOk (hc : Ctx L m₁ t) (hL : L.Ok) : AOk L.nA t := fun i hi => by
  rw [hc.esp, Lay.Ok.argAt_eq, hc.rd, hc.wr]
  exact ⟨L.ARGS, List.mem_append_right _ (List.mem_cons_of_mem _ hL.inArgs), hL.argIn hi⟩

theorem Ctx.off (hc : Ctx L m₁ t) (o : Nat) : (Arg.off o).val t = L.X32 + BitVec.ofNat 32 o := by
  simp only [Arg.val, hc.esi]

/-- Argument `i` of the function. -/
theorem Ctx.argV (hc : Ctx L m₁ t) {i : Nat} (hi : i < L.nA) : (Arg.arg i).val t = L.argv.getD i 0 := by
  simp only [Arg.val, hc.esp, Lay.Ok.argAt_eq]; exact hc.args i hi

theorem Ctx.argOffV (hc : Ctx L m₁ t) {i : Nat} (hi : i < L.nA) (o : Nat) :
    (Arg.argOff i o).val t = L.argv.getD i 0 + BitVec.ofNat 32 o := by
  simp only [Arg.val, hc.esp, Lay.Ok.argAt_eq]; rw [hc.args i hi]

end

end VG.Proof.MlDsa.X86.Message
