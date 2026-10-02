import VerifiedGarbage.Impl.MlDsa.AArch64.Call
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# ML-DSA on AArch64: moves, layouts and what code leaves

The framework of the proofs of `vg_mldsa*_keygen`, `vg_mldsa*_sign` and
`vg_mldsa*_verify` on AArch64:

* The moves of a call's arguments (`glue_ok`): each argument register holds
  the argument's value (`Arg.val`: a pointer's address `pa`, or an integer).
* Layouts (`Lay S`, `Proof/Framework/CallLay.lean`): the function keeps the
  address of each buffer it works in (its arguments and its working space)
  in a callee-saved register of `keptRegs`; a layout lists these registers
  with the lengths of their buffers, read (`rbs`) or written (`wbs`), which
  are apart from the `S` bytes of stack below the stack pointer (which the
  calls use), and from each other where one of them is written. A pointer (a
  register and an offset) into a buffer, and two pointers apart, are checked
  by evaluation (`inB`, `sepB`).
* What a piece of code leaves (`PostB`): the permissions, the registers
  `keptRegs` and the stack pointer, the low halves of v8–v15, and memory but
  within the regions it writes and the stack.
* Two runs whose registers `B` (the function's `bases`) agree (`SameIn B`).
-/

namespace VG.Proof.MlDsa.AArch64

open VG VG.AArch64 VG.Impl.MlDsa.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_movImm wp_addImm wp_add)
open VG.Spec.Sha3 (bytesAt)

/-! ## Relating two runs -/

/-- Two states each related by `I` to an entry state; the entry states
satisfy `Pre` and agree by `Pub`. -/
def Rel2 (Pre : State → Prop) (Pub : State → State → Prop) (I : State → State → Prop) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, Pre σ₁ ∧ Pre σ₂ ∧ Pub σ₁ σ₂ ∧ I σ₁ s₁ ∧ I σ₂ s₂

/-- A piece that leaks the same from states related by `I`, and takes each
run from `I` to `I'`. -/
theorem relInv {Pre : State → Prop} {Pub : State → State → Prop} {I I' : State → State → Prop}
    {c : Prog isa} (hw : ∀ σ s, Pre σ → I σ s → WP isa c s (I' σ))
    (ht : RelCT isa (Rel2 Pre Pub I) c fun _ _ => True) :
    RelCT isa (Rel2 Pre Pub I) c (Rel2 Pre Pub I') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', -⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩ := hr
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩

/-- Constant time, from a relation of the runs from the entry states. -/
theorem relStart {Pre : State → Prop} {Pub : State → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Rel2 Pre Pub fun σ s => s = σ) c Q) : ConstantTime isa Pre Pub c :=
  RelCT.constantTime (RelCT.mono h (fun s₁ s₂ ⟨p₁, p₂, hp⟩ => ⟨s₁, s₂, p₁, p₂, hp, rfl, rfl⟩) fun _ _ h => h)

/-- The final states of two runs related by `P` satisfy what correctness
says of each, from its own initial state. -/
theorem RelCT.postDep {P Q : State → State → Prop} {c : Prog isa} {F : State → State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x (F x) ∧ WP isa c y (F y))
    (hQ : ∀ x y x' y', P x y → F x x' → F y y' → Q x' y') : RelCT isa P c Q :=
  RelCT.mono (RelCT.wpDep h hw) (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, f₁, f₂⟩ => hQ _ _ _ _ hp f₁ f₂

/-- Code the taint analysis proves constant time from the registers `rs`,
which hold the same values in runs related by `P`, as does the stack pointer. -/
theorem taintRel {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint AArch64.Taint.T}
    (h : (taint.check (AArch64.Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (AArch64.Taint.ofRegs rs)
    (fun x y hp => ⟨(hr x y hp).1, fun r h => (hr x y hp).2 r (AArch64.Taint.mem_ofRegs.mp h)⟩) h

/-! ## Moves -/

/-- The address of the pointer `p` in `s`. -/
abbrev pa (s : State) (p : Ptr) : Addr := s.gpr p.1 + BitVec.ofNat 64 p.2

/-- The registers the moves of arguments, and the other blocks between
calls, write. -/
abbrev argRegs : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9]

theorem argRegs_pres : ∀ r ∈ preserved, r ∉ argRegs := by decide

theorem imm16_ofNat {v : Nat} (h : v < 65536) : (BitVec.ofNat 16 v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem movV_ok (d : Reg) (v : Nat) {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = BitVec.ofNat 64 v → WP isa (.block is) s' Q) :
    WP isa (.block (movV d v ++ is)) s Q := by
  unfold movV
  split
  · exact wp_movz fun s' h e => k s' h (by rw [e, imm16_ofNat ‹_›])
  · exact wp_movImm k

theorem lea_ok {d b : Reg} (hd : d ≠ b) (off : Nat) {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr b + BitVec.ofNat 64 off → WP isa (.block is) s' Q) :
    WP isa (.block (lea d b off ++ is)) s Q := by
  unfold lea
  split
  · exact wp_addImm ‹_› k
  · rw [List.append_assoc]
    refine movV_ok d off fun s₁ h₁ e₁ => wp_add fun s₂ h₂ e₂ => k s₂ ((h₁.trans h₂).mono (by simp)) ?_
    rw [e₂, h₁.get b (by simpa using hd.symm), e₁]

/-- The value of an argument. -/
def _root_.VG.Impl.MlDsa.AArch64.Arg.val (s : State) : Arg → BitVec 64
  | .ptr p => pa s p
  | .imm v => BitVec.ofNat 64 v

/-- An argument whose moves `glue` makes: a pointer based in a register the
moves do not write. -/
def _root_.VG.Impl.MlDsa.AArch64.Arg.Ok : Arg → Prop
  | .ptr p => p.1 ∉ argRegs
  | .imm _ => True

theorem arg_ok (d : Reg) (hd : d ∈ argRegs) (a : Arg) (ha : a.Ok) (s : State) :
    WP isa (.block (a.instrs d)) s fun s' => s'.gpr d = a.val s ∧ Only [d] s s' := by
  cases a with
  | ptr p =>
    rw [← List.append_nil (Arg.instrs d _)]
    exact lea_ok (fun e => ha (by rw [← e]; exact hd)) p.2 fun s' h e => wp_nil ⟨e, h⟩
  | imm v =>
    rw [← List.append_nil (Arg.instrs d _)]
    exact movV_ok d v fun s' h e => wp_nil ⟨e, h⟩

/-- The arguments of a call, in their registers. -/
abbrev Args (as : List (Reg × Arg)) (s s1 : State) : Prop :=
  ((∀ a ∈ as, s1.gpr a.1 = a.2.val s) ∧ s1.mem = s.mem) ∧ Keep argRegs s s1

theorem glue_aux : ∀ (as : List (Reg × Arg)), (∀ a ∈ as, a.2.Ok ∧ a.1 ∈ argRegs) → (as.map (·.1)).Nodup →
    ∀ s : State, WP isa (.block (glue as)) s fun s' =>
      ((∀ a ∈ as, s'.gpr a.1 = a.2.val s) ∧ s'.mem = s.mem) ∧ Keep (as.map (·.1)) s s'
  | [], _, _, s => WP.block_nil ⟨⟨fun _ h => absurd h List.not_mem_nil, rfl⟩, Keep.refl _ _⟩
  | (d, a) :: as, hok, hnd, s => by
    simp only [glue]
    rw [WP.block_append_iff]
    have ha := hok (d, a) (List.mem_cons_self ..)
    rw [List.map_cons, List.nodup_cons] at hnd
    refine WP.mono (arg_ok d ha.2 a ha.1 s) fun s₁ ⟨hd, h₁⟩ => ?_
    refine WP.mono (glue_aux as (fun b hb => hok b (List.mem_cons_of_mem _ hb)) hnd.2 s₁)
      fun s₂ ⟨⟨hv, hm₂⟩, k₂⟩ => ⟨⟨fun b hb => ?_, hm₂.trans h₁.mem⟩, (h₁.keep.trans k₂).mono fun r hr => ?_⟩
    · have hval : ∀ c : Arg, c.Ok → c.val s₁ = c.val s := fun c hc => by
        cases c with
        | ptr p => simp only [Arg.val, pa]; rw [h₁.get p.1 (fun h => hc (by
            simp only [List.mem_singleton] at h; rw [h]; exact ha.2))]
        | imm v => rfl
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [k₂.gpr _ hnd.1, hd]
      · rw [hv b hb, hval b.2 (hok b (List.mem_cons_of_mem _ hb)).1]
    · rcases List.mem_append.mp hr with hr | hr
      · simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ hr

/-- The moves of the arguments `as`, to distinct argument registers. -/
theorem glue_ok {as : List (Reg × Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ argRegs) (hnd : (as.map (·.1)).Nodup)
    (s : State) : WP isa (.block (glue as)) s (Args as s) :=
  WP.mono (glue_aux as hok hnd s) fun _ ⟨h, k⟩ => ⟨h, k.mono fun r hr => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr; exact (hok a ha).2⟩

/-! ## What a piece leaves -/

/-- The callee-saved registers the functions never write (all but `x24`, and
`x30`, which calls overwrite): the functions keep the addresses of their
buffers in some of them. -/
abbrev keptRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27, .x28]

theorem kept_pres : ∀ r ∈ keptRegs, r ∈ preserved ∧ r ≠ .x30 := by decide

/-- What a call leaves: the permissions, the stack pointer and the
callee-saved GPRs but `x30`, the low halves of v8–v15, and memory changed only within `W` and the
`S` bytes of stack below the stack pointer. -/
structure Post (S : Nat) (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame (W ++ [below s.sp S]) s.mem s'.mem
  vcs : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-- What a piece of code leaves: the permissions, the registers `keptRegs`,
the stack pointer, the low halves of v8–v15, and memory but within `W` and
the stack. -/
structure PostB (S : Nat) (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ keptRegs, s'.gpr r = s.gpr r
  frame : Frame (W ++ [below s.sp S]) s.mem s'.mem
  vcs : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

section
variable {S : Nat}

theorem Post.b {s s' : State} {W : List Region} (h : Post S s s' W) : PostB S s s' W :=
  ⟨h.rd, h.wr, h.sp, fun r hr => h.cs r (kept_pres r hr).1 (kept_pres r hr).2, h.frame, h.vcs⟩

theorem PostB.bs {s s' : State} {W : List Region} (h : PostB S s s' W) : ∀ r ∈ keptRegs, s'.gpr r = s.gpr r :=
  h.cs

theorem PostB.refl (s : State) (W : List Region) : PostB S s s W :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, fun _ _ => rfl⟩

theorem PostB.trans {s s₁ s₂ : State} {W₁ W₂ W : List Region} (h₁ : PostB S s s₁ W₁) (h₂ : PostB S s₁ s₂ W₂)
    (hw₁ : ∀ r ∈ W₁, r ∈ W) (hw₂ : ∀ r ∈ W₂, r ∈ W) : PostB S s s₂ W := by
  refine ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, fun r hr => (h₂.cs r hr).trans (h₁.cs r hr), ?_,
    fun r hr => (h₂.vcs r hr).trans (h₁.vcs r hr)⟩
  have f₂ := h₂.frame
  rw [h₁.sp] at f₂
  refine (h₁.frame.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₁ r hr), List.mem_append_right _ hr]
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₂ r hr), List.mem_append_right _ hr]

/-- A block that keeps the registers `keptRegs` and the permissions, and writes within `W`. -/
theorem postB_of_keep {rs : List Reg} {s s' : State} {W : List Region} (k : Keep rs s s')
    (hrs : ∀ r ∈ keptRegs, r ∉ rs) (hf : Frame W s.mem s'.mem) : PostB S s s' W :=
  ⟨k.rd, k.wr, k.sp, fun r hr => k.gpr r (hrs r hr), (hf.mono fun _ hr => List.mem_append_left _ hr), k.vcs⟩

theorem PostB.pa {s s' : State} {W : List Region} (hP : PostB S s s' W) {p : Ptr} (h : p.1 ∈ keptRegs) :
    pa s' p = pa s p := by
  simp only [VG.Proof.MlDsa.AArch64.pa, hP.bs _ h]

end

/-! ## Checks -/

export VG.CallLay (inB isW lookup_mem inB_spec contains_trans inRegions_sub)

/-- The `l` bytes at `p` and the `k` bytes at `q` lie within their buffers,
apart: in different buffers, one of them written, or in the same buffer. -/
abbrev sepB (rbs wbs : List (Reg × Nat)) (p : Ptr) (l : Nat) (q : Ptr) (k : Nat) : Bool :=
  CallLay.sepB (isW wbs) (rbs ++ wbs) p l q k

/-- The `l` bytes at `p` lie in the layout, apart from the regions `ws`, and
`p`'s register is one of `keptRegs`. -/
abbrev keepB (rbs wbs : List (Reg × Nat)) (ws : List (Ptr × Nat)) (p : Ptr) (l : Nat) : Bool :=
  CallLay.keepB (fun r => decide (r ∈ keptRegs)) (isW wbs) (rbs ++ wbs) ws p l

theorem sepB_spec {rbs wbs : List (Reg × Nat)} {p q : Ptr} {l k : Nat} (h : sepB rbs wbs p l q k = true) :
    inB (rbs ++ wbs) p l = true ∧ inB (rbs ++ wbs) q k = true ∧
      ((p.1 ≠ q.1 ∧ (isW wbs p.1 || isW wbs q.1) = true) ∨ (p.1 = q.1 ∧ (p.2 + l ≤ q.2 ∨ q.2 + k ≤ p.2))) :=
  CallLay.sepB_spec h

theorem keepB_bs {rbs wbs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {p : Ptr} {l : Nat}
    (hc : keepB rbs wbs ws p l = true) : p.1 ∈ keptRegs :=
  of_decide_eq_true (CallLay.keepB_kp (kp := fun r => decide (r ∈ keptRegs)) hc)

theorem keepB_in {rbs wbs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {p : Ptr} {l : Nat}
    (hc : keepB rbs wbs ws p l = true) : inB (rbs ++ wbs) p l = true :=
  CallLay.keepB_in hc

/-! ## Regions -/

theorem covers_one {X : List Region} {a : Addr} {l : Nat} (h : InRegions X a l) : Covers [⟨a, l⟩] X := by
  intro a' n' ⟨r0, hr0, hc⟩
  simp only [List.mem_singleton] at hr0
  subst hr0
  obtain ⟨r, hr, hc'⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc hc' ⊢
  rw [show a' - r.base = (a' - a) + (a - r.base) by rw [Offset.sub_add_sub_cancel], BitVec.toNat_add]
  have := Nat.mod_le ((a' - a).toNat + (a - r.base).toNat) (2 ^ 64)
  omega

theorem covers_nil {X : List Region} : Covers [] X := fun _ _ ⟨_, h, _⟩ => absurd h List.not_mem_nil

theorem covers_cons {r : Region} {rs X : List Region} (h : Covers [r] X) (h' : Covers rs X) :
    Covers (r :: rs) X := by
  intro a n ⟨r0, hr0, hc⟩
  rcases List.mem_cons.mp hr0 with rfl | hr0
  · exact h a n ⟨r0, List.mem_singleton_self _, hc⟩
  · exact h' a n ⟨r0, hr0, hc⟩

theorem covers_append {rs ts X : List Region} (h : Covers rs X) (h' : Covers ts X) : Covers (rs ++ ts) X := by
  intro a n ⟨r0, hr0, hc⟩
  rcases List.mem_append.mp hr0 with hr0 | hr0
  · exact h a n ⟨r0, hr0, hc⟩
  · exact h' a n ⟨r0, hr0, hc⟩

theorem covers_wr {rs : List Region} {s : State} (h : Covers rs s.wr) : Covers rs (s.rd ++ s.wr) :=
  fun a n hi => by
    obtain ⟨r, hr, hc⟩ := h a n hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## Layouts -/

/-- The buffers of `rbs` (read) and `wbs` (written), at the addresses in
their registers (`CallLay.Lay`): small, apart from each other (where one is
written) and from the `S` bytes of stack below the stack pointer, not
wrapping around, and permitted; and in registers of `keptRegs`. -/
structure Lay (S : Nat) (rbs wbs : List (Reg × Nat)) (s : State) : Prop
    extends CallLay.Lay (isW wbs) s.gpr s.rd s.wr (below s.sp S) rbs wbs where
  bs : ∀ b ∈ rbs ++ wbs, b.1 ∈ keptRegs
  spS : S ≤ s.sp.toNat

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s)
include L

omit L in
theorem sub_of_inB {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    ∃ n, (p.1, n) ∈ rbs ++ wbs ∧ Region.Sub ⟨pa s p, l⟩ ⟨s.gpr p.1, n⟩ :=
  CallLay.sub_of_inB h

theorem Lay.disj {p q : Ptr} {l k : Nat} (h : sepB rbs wbs p l q k = true) :
    Region.Disjoint ⟨pa s p, l⟩ ⟨pa s q, k⟩ :=
  L.toLay.disj h

theorem Lay.stkD {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    (below s.sp S).Disjoint ⟨pa s p, l⟩ :=
  L.toLay.stkD h

theorem Lay.nwp {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : (pa s p).toNat + l ≤ 2 ^ 64 :=
  L.toLay.nwp h

theorem Lay.inR {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : InRegions (s.rd ++ s.wr) (pa s p) l :=
  L.toLay.inR h

theorem Lay.inW {p : Ptr} {l : Nat} (h : inB wbs p l = true) : InRegions s.wr (pa s p) l :=
  L.toLay.inW h

theorem Lay.cR {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : Covers [⟨pa s p, l⟩] (s.rd ++ s.wr) :=
  covers_one (L.inR h)

theorem Lay.cW {p : Ptr} {l : Nat} (h : inB wbs p l = true) : Covers [⟨pa s p, l⟩] s.wr :=
  covers_one (L.inW h)

theorem Lay.s64 : S < 2 ^ 64 := Nat.lt_of_le_of_lt L.spS s.sp.isLt

theorem Lay.ptrBs {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : p.1 ∈ keptRegs := by
  obtain ⟨n, hn, _⟩ := inB_spec h
  exact L.bs (p.1, n) hn

theorem Lay.post {s' : State} {W : List Region} (hP : PostB S s s' W) : Lay S rbs wbs s' := by
  have L' := L.toLay.congr (g' := s'.gpr) fun b hb => hP.bs _ (L.bs b hb)
  rw [← hP.rd, ← hP.wr, ← hP.sp] at L'
  exact ⟨L', L.bs, by rw [hP.sp]; exact L.spS⟩

end

/-! ## What is kept -/

/-- The region of `w.2` bytes at the pointer `w.1`. -/
abbrev toR (s : State) (w : Ptr × Nat) : Region := ⟨pa s w.1, w.2⟩

/-- `PostB`, with the regions written given as pointers. -/
abbrev PPostB (S : Nat) (s s' : State) (ws : List (Ptr × Nat)) : Prop := PostB S s s' (ws.map (toR s))

section
variable {S : Nat}

theorem map_toR_post {s s' : State} {W : List Region} (hP : PostB S s s' W) {ws : List (Ptr × Nat)}
    (h : ∀ w ∈ ws, w.1.1 ∈ keptRegs) : ws.map (toR s') = ws.map (toR s) :=
  List.map_congr_left fun w hw => by simp only [toR, hP.pa (h w hw)]

theorem PPostB.trans {s s₁ s₂ : State} {ws₁ ws₂ ws : List (Ptr × Nat)} (h₁ : PPostB S s s₁ ws₁)
    (h₂ : PPostB S s₁ s₂ ws₂) (hcs : ∀ w ∈ ws₂, w.1.1 ∈ keptRegs) (hw₁ : ∀ w ∈ ws₁, w ∈ ws)
    (hw₂ : ∀ w ∈ ws₂, w ∈ ws) : PPostB S s s₂ ws := by
  have h₂' : PostB S s₁ s₂ (ws₂.map (toR s)) := by rw [← map_toR_post h₁ hcs]; exact h₂
  refine PostB.trans h₁ h₂' (fun r hr => ?_) fun r hr => ?_
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₁ w hw)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₂ w hw)

theorem PPostB.mono {s s' : State} {ws ws' : List (Ptr × Nat)} (h : PPostB S s s' ws) (hw : ∀ w ∈ ws, w ∈ ws') :
    PPostB S s s' ws' :=
  PostB.trans (PostB.refl s []) h (fun _ h => absurd h List.not_mem_nil) fun r hr => by
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw w hw')

end

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay S rbs wbs s) {ws : List (Ptr × Nat)}
  {p : Ptr} {l : Nat}
include L

theorem Lay.fdisj (hc : keepB rbs wbs ws p l = true) :
    ∀ r ∈ ws.map (toR s) ++ [below s.sp S], Region.Disjoint ⟨pa s p, l⟩ r :=
  L.toLay.fdisj hc

theorem Lay.keepBytes (hP : PPostB S s s' ws) (hc : keepB rbs wbs ws p l = true) :
    bytesAt s'.mem (pa s' p) l = bytesAt s.mem (pa s p) l := by
  rw [hP.pa (keepB_bs hc)]
  obtain ⟨n, hn, hl⟩ := inB_spec (keepB_in hc)
  exact Proof.MlKem.bytesAt_frame hP.frame (L.fdisj hc) (by have := L.small _ hn; simp only at this; omega)

theorem Lay.keepPoly {f : Spec.MlDsa.Poly} (hP : PPostB S s s' ws) (hc : keepB rbs wbs ws p 1024 = true)
    (h : Spec.MlDsa.PolyIs s.mem (pa s p) f) : Spec.MlDsa.PolyIs s'.mem (pa s' p) f := by
  rw [hP.pa (keepB_bs hc)]
  exact Proof.MlDsa.Verify.polyIs_frame hP.frame (L.fdisj hc) h

theorem Lay.keepPolyAt (hP : PPostB S s s' ws) (hc : keepB rbs wbs ws p 1024 = true) :
    Spec.MlDsa.polyAt s'.mem (pa s' p) = Spec.MlDsa.polyAt s.mem (pa s p) := by
  rw [hP.pa (keepB_bs hc)]
  exact Proof.MlDsa.Verify.polyAt_frame hP.frame (L.fdisj hc)

theorem Lay.keepRed (hP : PPostB S s s' ws) (hc : keepB rbs wbs ws p 1024 = true)
    (h : Spec.MlDsa.Reduced s.mem (pa s p)) : Spec.MlDsa.Reduced s'.mem (pa s' p) := by
  rw [hP.pa (keepB_bs hc)]
  exact Proof.MlDsa.Verify.reduced_frame hP.frame (L.fdisj hc) h

theorem Lay.keepHint {k : Nat} {h : List (Vector Bool Spec.MlDsa.n)} (hP : PPostB S s s' ws)
    (hc : keepB rbs wbs ws p (1024 * k) = true)
    (hh : Spec.MlDsa.HintIs s.mem (pa s p) k h) : Spec.MlDsa.HintIs s'.mem (pa s' p) k h := by
  rw [hP.pa (keepB_bs hc)]
  obtain ⟨n, hn, hl⟩ := inB_spec (keepB_in hc)
  exact Proof.MlDsa.Verify.hintIs_frame hP.frame (by have := L.small _ hn; simp only at this; omega)
    (L.fdisj hc) hh

theorem Lay.keepW (hP : PPostB S s s' ws) (hc : keepB rbs wbs ws p 8 = true) :
    s'.mem.readW (pa s' p) 64 = s.mem.readW (pa s p) 64 := by
  rw [hP.pa (keepB_bs hc)]
  exact hP.frame.readW (Region.contains_self _ _) (L.fdisj hc) (by decide)

end

/-! ## Two runs -/

/-- Two states whose registers `B` and stack pointer agree. -/
def SameIn (B : List Reg) (x y : State) : Prop := (∀ r ∈ B, x.gpr r = y.gpr r) ∧ x.sp = y.sp

theorem SameIn.pa {B : List Reg} {x y : State} (h : SameIn B x y) {p : Ptr} (hp : p.1 ∈ B) : pa x p = pa y p := by
  simp only [VG.Proof.MlDsa.AArch64.pa, h.1 _ hp]

/-- The buffers of a layout are in registers of `B` (which are among `keptRegs`). -/
def LayIn (B : List Reg) (bs : List (Reg × Nat)) : Prop := ∀ b ∈ bs, b.1 ∈ B ∧ b.1 ∈ keptRegs

theorem ptr_bs {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {p : Ptr} {l : Nat}
    (h : inB bs p l = true) : p.1 ∈ B := by
  obtain ⟨n, hn, _⟩ := inB_spec h
  exact (L (p.1, n) hn).1

theorem ptr_kept {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {p : Ptr} {l : Nat}
    (h : inB bs p l = true) : p.1 ∈ keptRegs := by
  obtain ⟨n, hn, _⟩ := inB_spec h
  exact (L (p.1, n) hn).2

theorem Lay.ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) :
    LayIn keptRegs (rbs ++ wbs) :=
  fun b hb => ⟨L.bs b hb, L.bs b hb⟩

end VG.Proof.MlDsa.AArch64
