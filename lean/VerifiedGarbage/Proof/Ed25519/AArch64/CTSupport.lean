import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-! Untrusted: relational constant-time composition with a public stack pointer.
The AArch64 taint domain always includes sp; this wrapper carries its agreement
through every composition, while individual relations describe the other data. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64

def CT (P : State → State → Prop) (c : Prog isa) (Q : State → State → Prop) : Prop :=
  RelCT isa (fun x y => x.sp = y.sp ∧ P x y) c (fun x y => x.sp = y.sp ∧ Q x y)

namespace CT

theorem mono {P P' Q Q' : State → State → Prop} {c : Prog isa} (h : CT P c Q)
    (hp : ∀ x y, P' x y → P x y) (hq : ∀ x y, Q x y → Q' x y) : CT P' c Q' :=
  VG.RelCT.mono h (fun x y h => ⟨h.1, hp x y h.2⟩) (fun x y h => ⟨h.1, hq x y h.2⟩)

theorem seq {P R Q : State → State → Prop} {c d : Prog isa} (h : CT P c R) (k : CT R d Q) :
    CT P (.seq c d) Q := VG.RelCT.seq h k

theorem ite {P Q : State → State → Prop} {c : Cond} {yes no : Prog isa}
    (hc : ∀ x y, P x y → eval c x = eval c y)
    (hy : CT (fun x y => P x y ∧ eval c x = some true) yes Q)
    (hn : CT (fun x y => P x y ∧ eval c x = some false) no Q) :
    CT P (.ite c yes no) Q :=
  VG.RelCT.ite (fun x y h => hc x y h.2)
    (VG.RelCT.mono hy (fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩) (fun _ _ h => h))
    (VG.RelCT.mono hn (fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩) (fun _ _ h => h))

theorem of_false {P Q : State → State → Prop} {c : Prog isa} (h : ∀ x y, ¬ P x y) : CT P c Q :=
  VG.RelCT.of_false (fun x y hp => h x y hp.2)

theorem wp {P Q : State → State → Prop} {F G : State → Prop} {c : Prog isa}
    (h : CT P c Q) (hw : ∀ x y, P x y → WP isa c x F ∧ WP isa c y G) :
    CT P c (fun x y => Q x y ∧ F x ∧ G y) :=
  VG.RelCT.mono (VG.RelCT.wp h (fun x y hp => hw x y hp.2)) (fun _ _ h => h)
    (fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩)

theorem loop {body : Prog isa} {c : Cond} {Q : State → State → Prop}
    (I : Nat → State → State → Prop)
    (hstep : ∀ n, CT (I n) body fun x y => eval c x = eval c y ∧
      (eval c x = some false → Q x y) ∧ (eval c x = some true → ∃ m < n, I m x y))
    (n : Nat) : CT (I n) (.loop body c) Q := by
  apply VG.RelCT.loop (M := isa) (fun n x y => x.sp = y.sp ∧ I n x y) ?_ n
  intro n
  exact VG.RelCT.mono (hstep n) (fun _ _ h => h) (fun _ _ h =>
    ⟨h.2.1, fun hf => ⟨h.1, h.2.2.1 hf⟩, fun ht =>
      let ⟨m, hm, hi⟩ := h.2.2.2 ht
      ⟨m, hm, h.1, hi⟩⟩)

theorem taint {P : State → State → Prop} {c : Prog isa} (τ : VG.AArch64.Taint.T)
    (hp : ∀ x y, P x y → ∀ r ∈ τ, x.gpr r = y.gpr r) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (VG.AArch64.taint.check τ c hc).isSome = true) : CT P c (fun _ _ => True) := by
  intro x y tx ty u v ⟨hsp, hp'⟩ ex ey
  obtain ⟨τ', hh⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hh (show VG.AArch64.Taint.Agree τ x y from ⟨hsp, hp x y hp'⟩) ex ey
  exact ⟨ht, ha.1, True.intro⟩

theorem taintRegs {τ : VG.AArch64.Taint.T} {P : State → State → Prop} {c : Prog isa}
    (hp : ∀ x y, P x y → ∀ r ∈ τ, x.gpr r = y.gpr r) (rs : List Reg)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : ((VG.AArch64.taint.check τ c hc).map fun τ' => (RegSet.ofList rs).subset τ') = some true) :
    CT P c (fun x y => ∀ r ∈ rs, x.gpr r = y.gpr r) := by
  intro x y tx ty u v ⟨hsp, hp'⟩ ex ey
  obtain ⟨τ', hh, hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hh (show VG.AArch64.Taint.Agree τ x y from ⟨hsp, hp x y hp'⟩) ex ey
  exact ⟨ht, ha.1, fun r hr => ha.2 r (RegSet.mem_of_subset hs (RegSet.mem_ofList.mpr hr))⟩

end CT

theorem agree_ofRegs {rs : List Reg} {x y : State} (h : ∀ r ∈ rs, x.gpr r = y.gpr r) :
    ∀ r ∈ VG.AArch64.Taint.ofRegs rs, x.gpr r = y.gpr r := fun r hr => h r (VG.AArch64.Taint.mem_ofRegs.mp hr)

theorem execBlock_append_seq {xs ys : List Instr} {s t : State} {tr : List Leak}
    (h : Exec isa (.block (xs ++ ys)) s tr t) :
    Exec isa (.seq (.block xs) (.block ys)) s tr t := by
  rw [Exec.block_iff, execBlock_append] at h
  obtain ⟨⟨u, tx⟩, hu, ht⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨v, ty⟩, hv, he⟩ := Option.map_eq_some_iff.mp ht
  cases he
  exact .seq (.block hu) (.block hv)

theorem blockAppend_ct {P R Q : State → State → Prop} {xs ys : List Instr}
    (hx : CT P (.block xs) R) (hy : CT R (.block ys) Q) : CT P (.block (xs ++ ys)) Q :=
  fun _ _ _ _ _ _ hp ex ey => CT.seq hx hy _ _ _ _ _ _ hp
    (execBlock_append_seq ex) (execBlock_append_seq ey)

theorem withRuns {P Q F G : State → State → Prop} {c : Prog isa}
    (h : CT P c Q) (hw : ∀ x y, P x y → WP isa c x (F x) ∧ WP isa c y (G y)) :
    CT P c (fun u v => Q u v ∧ ∃ x y, P x y ∧ F x u ∧ G y v) := by
  intro x y tx ty u v ⟨hsp, hp⟩ ex ey
  obtain ⟨ht, hs, hq⟩ := h _ _ _ _ _ _ ⟨hsp, hp⟩ ex ey
  obtain ⟨⟨_, u', eu, hu⟩, ⟨_, v', ev, hv⟩⟩ := hw x y hp
  obtain ⟨-, rfl⟩ := Exec.det ex eu
  obtain ⟨-, rfl⟩ := Exec.det ey ev
  exact ⟨ht, hs, hq, x, y, hp, hu, hv⟩

end VG.Proof.Ed25519.AArch64
