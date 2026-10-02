import VerifiedGarbage.Impl.MlDsa.X86_64.Verify.Verify
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.TCB.X86_64.Target

/-!
# ML-DSA verification on x86-64: moves, layouts and calls

Untrusted: everything here is checked by Lean.

* The moves of a call's arguments (`glue_ok`): each argument register holds
  the argument's value (`Arg.val`: a pointer's address `pa`, or an integer).
* Layouts (`Lay`): the function keeps the address of each buffer it works in
  (its arguments and its working space) in a callee-saved register; a
  layout lists these registers with the lengths of their buffers, which are
  apart from the stack, and from each other where one of them is written
  (only `scratch`, in `rbx`: the inputs may overlap each other). A pointer
  (a register and an offset) into a buffer, and two pointers apart, are
  checked by evaluation (`inB`, `sepB`).
* What a piece of code leaves (`PostB`): the permissions, the registers of
  the layout and the stack pointer, and memory but within the regions it
  writes and the 32 bytes of stack below `rsp` (its calls' return
  addresses).
* A call of verified code, with the moves of its arguments before it
  (`callAt_ok`, `callAt_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.Sha3 (bytesAt)

/-! ## Moves -/

/-- The address of the pointer `p` in `s`. -/
abbrev pa (s : State) (p : Ptr) : Addr := s.gpr p.1 + BitVec.ofNat 64 p.2

/-- The registers the moves of arguments write. -/
abbrev argRegs : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9]

theorem argRegs_cs : ∀ r ∈ calleeSaved, r ∉ argRegs := by decide

/-- The value of an argument. -/
def _root_.VG.Impl.MlDsa.X86_64.Verify.Arg.val (s : State) : Arg → BitVec 64
  | .ptr p => pa s p
  | .imm v => BitVec.ofNat 64 v

/-- An argument whose moves `glue` makes: a pointer with an offset that fits
an immediate, based in a register the moves do not write, or an integer of
at most 31 bits. -/
def _root_.VG.Impl.MlDsa.X86_64.Verify.Arg.Ok : Arg → Prop
  | .ptr p => p.2 < 2 ^ 31 ∧ p.1 ∉ argRegs
  | .imm v => v < 2 ^ 31

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sw_ofNat {n : Nat} (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_setWidth64, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

theorem arg_ok (d : Reg) (a : Arg) (ha : a.Ok) (s : State) :
    WP isa (.block (a.instrs d)) s fun s' => (s'.gpr d = a.val s ∧ s'.mem = s.mem) ∧ Keep [d] s s' := by
  refine WP.keep _ ?_ (by cases a <;> cases d <;> rfl)
  cases a with
  | ptr p => simp only [Arg.instrs, Arg.val]; xrun [sx_ofNat ha.1]
  | imm v => simp only [Arg.instrs, Arg.val]; xrun [sw_ofNat (show v < 2 ^ 32 by have : v < 2 ^ 31 := ha; omega)]

/-- The moves of the arguments `as`, to distinct registers. -/
theorem glue_ok : ∀ (as : List (Reg × Arg)), (∀ a ∈ as, a.2.Ok ∧ a.1 ∈ argRegs) → (as.map (·.1)).Nodup →
    ∀ s : State, WP isa (.block (glue as)) s fun s' =>
      ((∀ a ∈ as, s'.gpr a.1 = a.2.val s) ∧ s'.mem = s.mem) ∧ Keep (as.map (·.1)) s s'
  | [], _, _, s => WP.block_nil ⟨⟨fun _ h => absurd h List.not_mem_nil, rfl⟩, Keep.refl _ _⟩
  | (d, a) :: as, hok, hnd, s => by
    simp only [glue]
    rw [WP.block_append_iff]
    have ha := hok (d, a) (List.mem_cons_self ..)
    rw [List.map_cons, List.nodup_cons] at hnd
    refine WP.mono (arg_ok d a ha.1 s) fun s₁ ⟨⟨hd, hm⟩, k₁⟩ => ?_
    refine WP.mono (glue_ok as (fun b hb => hok b (List.mem_cons_of_mem _ hb)) hnd.2 s₁)
      fun s₂ ⟨⟨hv, hm₂⟩, k₂⟩ => ⟨⟨fun b hb => ?_, hm₂.trans hm⟩, (k₁.trans k₂).mono fun r hr => ?_⟩
    · have hval : ∀ c : Arg, c.Ok → c.val s₁ = c.val s := fun c hc => by
        cases c with
        | ptr p => simp only [Arg.val, pa]; rw [k₁.gpr (fun h => hc.2 (by
            simp only [List.mem_singleton] at h; rw [h]; exact ha.2))]
        | imm v => rfl
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [k₂.gpr hnd.1, hd]
      · rw [hv b hb, hval b.2 (hok b (List.mem_cons_of_mem _ hb)).1]
    · rcases List.mem_append.mp hr with hr | hr
      · simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ hr

/-- The moves of the arguments, which write only argument registers. -/
theorem glue_ok' {as : List (Reg × Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ argRegs) (hnd : (as.map (·.1)).Nodup)
    (s : State) : WP isa (.block (glue as)) s fun s' =>
      ((∀ a ∈ as, s'.gpr a.1 = a.2.val s) ∧ s'.mem = s.mem) ∧ Keep argRegs s s' :=
  WP.mono (glue_ok as hok hnd s) fun _ ⟨h, k⟩ => ⟨h, k.mono fun r hr => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr; exact (hok a ha).2⟩


/-! ## What a piece leaves -/

/-- The registers the function keeps the addresses of its buffers in. -/
abbrev bases : List Reg := [.rbx, .rbp, .r12, .r13]

/-- The registers of the buffers the function writes (`scratch`): a buffer
it only reads may overlap another such buffer, but not one of these. -/
abbrev wRegs : List Reg := [.rbx]

/-- What a call leaves: the permissions and the callee-saved registers, and
memory changed only within `W` and the stack. -/
structure Post (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame (W ++ [below (s.gpr .rsp) 32]) s.mem s'.mem

/-- What a piece of code leaves: the permissions, the registers `bases` and
the stack pointer, and memory but within `W` and the stack. -/
structure PostB (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bs : ∀ r ∈ bases, s'.gpr r = s.gpr r
  rsp : s'.gpr .rsp = s.gpr .rsp
  frame : Frame (W ++ [below (s.gpr .rsp) 32]) s.mem s'.mem

theorem Post.rsp {s s' : State} {W : List Region} (h : Post s s' W) : s'.gpr .rsp = s.gpr .rsp :=
  h.cs .rsp (by decide)

theorem Post.b {s s' : State} {W : List Region} (h : Post s s' W) : PostB s s' W :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
    simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide), h.rsp, h.frame⟩

theorem PostB.refl (s : State) (W : List Region) : PostB s s W :=
  ⟨rfl, rfl, fun _ _ => rfl, rfl, Frame.refl _ _⟩

theorem PostB.trans {s s₁ s₂ : State} {W₁ W₂ W : List Region} (h₁ : PostB s s₁ W₁) (h₂ : PostB s₁ s₂ W₂)
    (hw₁ : ∀ r ∈ W₁, r ∈ W) (hw₂ : ∀ r ∈ W₂, r ∈ W) : PostB s s₂ W := by
  refine ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hr => (h₂.bs r hr).trans (h₁.bs r hr),
    h₂.rsp.trans h₁.rsp, ?_⟩
  have f₂ := h₂.frame
  rw [h₁.rsp] at f₂
  refine (h₁.frame.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₁ r hr), List.mem_append_right _ hr]
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₂ r hr), List.mem_append_right _ hr]

/-- A block that keeps the registers `bases` and `rsp` and the permissions,
and writes within `W`. -/
theorem postB_of_keep {rs : List Reg} {s s' : State} {W : List Region} (k : Keep rs s s')
    (hrs : ∀ r ∈ .rsp :: bases, r ∉ rs) (hf : Frame W s.mem s'.mem) : PostB s s' W :=
  ⟨k.2.1, k.2.2, fun r hr => k.gpr (hrs r (List.mem_cons_of_mem _ hr)), k.gpr (hrs _ (List.mem_cons_self ..)),
    hf.mono fun _ hr => List.mem_append_left _ hr⟩

theorem PostB.pa {s s' : State} {W : List Region} (hP : PostB s s' W) {p : Ptr} (h : p.1 ∈ bases) :
    pa s' p = pa s p := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.pa, hP.bs _ h]

/-! ## Checks -/

/-- The `len` bytes at `p` lie within the buffer of its register in the layout `bs`. -/
def inB (bs : List (Reg × Nat)) (p : Ptr) (len : Nat) : Bool :=
  match bs.lookup p.1 with
  | some n => decide (p.2 + len ≤ n)
  | none => false

/-- The `l` bytes at `p` and the `k` bytes at `q` lie within their buffers,
apart: in different buffers, one of them written, or in the same buffer. -/
def sepB (bs : List (Reg × Nat)) (p : Ptr) (l : Nat) (q : Ptr) (k : Nat) : Bool :=
  inB bs p l && inB bs q k &&
    ((p.1 != q.1 && (decide (p.1 ∈ wRegs) || decide (q.1 ∈ wRegs))) ||
      (p.1 == q.1 && (decide (p.2 + l ≤ q.2) || decide (q.2 + k ≤ p.2))))

theorem lookup_mem : ∀ {bs : List (Reg × Nat)} {r : Reg} {n : Nat}, bs.lookup r = some n → (r, n) ∈ bs
  | [], _, _, h => by simp [List.lookup] at h
  | (r', n') :: bs, r, n, h => by
    unfold List.lookup at h
    by_cases e : r = r'
    · subst e
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
    · have : (r == r') = false := by simp [e]
      rw [this] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

theorem inB_spec {bs : List (Reg × Nat)} {p : Ptr} {l : Nat} (h : inB bs p l = true) :
    ∃ n, (p.1, n) ∈ bs ∧ p.2 + l ≤ n := by
  unfold inB at h
  split at h
  · rename_i n hn; exact ⟨n, lookup_mem hn, of_decide_eq_true h⟩
  · cases h

theorem sepB_spec {bs : List (Reg × Nat)} {p q : Ptr} {l k : Nat} (h : sepB bs p l q k = true) :
    inB bs p l = true ∧ inB bs q k = true ∧
      ((p.1 ≠ q.1 ∧ (p.1 ∈ wRegs ∨ q.1 ∈ wRegs)) ∨ (p.1 = q.1 ∧ (p.2 + l ≤ q.2 ∨ q.2 + k ≤ p.2))) := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ## Regions -/

theorem inRegions_sub {X : List Region} {a : Addr} {n off l : Nat} (h : InRegions X a n) (hl : off + l ≤ n)
    (hn : n < 2 ^ 64) : InRegions X (a + BitVec.ofNat 64 off) l := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  rw [show a + BitVec.ofNat 64 off - r.base = (a - r.base) + BitVec.ofNat 64 off by bv_omega, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega)]
  have := Nat.mod_le ((a - r.base).toNat + off) (2 ^ 64)
  omega

theorem covers_one {X : List Region} {a : Addr} {l : Nat} (h : InRegions X a l) : Covers [⟨a, l⟩] X := by
  intro a' n' ⟨r0, hr0, hc⟩
  simp only [List.mem_singleton] at hr0
  subst hr0
  obtain ⟨r, hr, hc'⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc hc' ⊢
  rw [show a' - r.base = (a' - a) + (a - r.base) by bv_omega, BitVec.toNat_add]
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
their registers: small, apart from each other (where one is written) and
from the stack, not wrapping around, and permitted. -/
structure Lay (rbs wbs : List (Reg × Nat)) (s : State) : Prop where
  small : ∀ b ∈ rbs ++ wbs, b.2 < 2 ^ 31
  dj : ∀ b ∈ rbs ++ wbs, ∀ b' ∈ rbs ++ wbs, b.1 ≠ b'.1 → (b.1 ∈ wRegs ∨ b'.1 ∈ wRegs) →
    Region.Disjoint ⟨s.gpr b.1, b.2⟩ ⟨s.gpr b'.1, b'.2⟩
  stk : ∀ b ∈ rbs ++ wbs, (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr b.1, b.2⟩
  nw : ∀ b ∈ rbs ++ wbs, (s.gpr b.1).toNat + b.2 ≤ 2 ^ 64
  rd : ∀ b ∈ rbs ++ wbs, InRegions (s.rd ++ s.wr) (s.gpr b.1) b.2
  wr : ∀ b ∈ wbs, InRegions s.wr (s.gpr b.1) b.2
  ret : ∀ b ∈ rbs ++ wbs, (Region.mk (s.gpr .rsp) 8).Disjoint ⟨s.gpr b.1, b.2⟩
  bs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases
  sp32 : 32 ≤ (s.gpr .rsp).toNat

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s)
include L

theorem Lay.sub {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    ∃ n, (p.1, n) ∈ rbs ++ wbs ∧ Region.Sub ⟨pa s p, l⟩ ⟨s.gpr p.1, n⟩ := by
  obtain ⟨n, hm, hl⟩ := inB_spec h
  exact ⟨n, hm, sub_offset' hl (by have := L.small _ hm; omega)⟩

theorem Lay.disj {p q : Ptr} {l k : Nat} (h : sepB (rbs ++ wbs) p l q k = true) :
    Region.Disjoint ⟨pa s p, l⟩ ⟨pa s q, k⟩ := by
  obtain ⟨hp, hq, hs⟩ := sepB_spec h
  obtain ⟨n, hn, hl⟩ := inB_spec hp
  obtain ⟨m, hm, hk⟩ := inB_spec hq
  have sn := L.small _ hn
  have sm := L.small _ hm
  rcases hs with ⟨e, hw⟩ | ⟨e, hs⟩
  · exact ((L.dj _ hn _ hm e hw).sub_left (sub_offset' hl (by omega))).sub_right (sub_offset' hk (by omega))
  · show Region.Disjoint ⟨s.gpr p.1 + _, l⟩ ⟨s.gpr q.1 + _, k⟩
    rw [← e]
    rcases hs with h1 | h2
    · exact off_disj h1 (by omega)
    · exact (off_disj h2 (by omega)).symm

theorem Lay.stkD {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    (below (s.gpr .rsp) 32).Disjoint ⟨pa s p, l⟩ := by
  obtain ⟨n, hn, hsub⟩ := L.sub h
  exact (L.stk _ hn).sub_right hsub

theorem Lay.retD {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    (Region.mk (s.gpr .rsp) 8).Disjoint ⟨pa s p, l⟩ := by
  obtain ⟨n, hn, hsub⟩ := L.sub h
  exact (L.ret _ hn).sub_right hsub

theorem Lay.nwp {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : (pa s p).toNat + l ≤ 2 ^ 64 := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  have h1 := L.nw _ hn
  have h2 := L.small _ hn
  simp only at h1 h2
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.2) (by omega)]
  have := Nat.mod_le ((s.gpr p.1).toNat + p.2) (2 ^ 64)
  omega

theorem Lay.inR {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : InRegions (s.rd ++ s.wr) (pa s p) l := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  exact inRegions_sub (L.rd (p.1, n) hn) hl (by have := L.small _ hn; omega)

theorem Lay.inW {p : Ptr} {l : Nat} (h : inB wbs p l = true) : InRegions s.wr (pa s p) l := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  exact inRegions_sub (L.wr (p.1, n) hn) hl (by have := L.small _ (List.mem_append_right _ hn); omega)

theorem Lay.cR {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : Covers [⟨pa s p, l⟩] (s.rd ++ s.wr) :=
  covers_one (L.inR h)

theorem Lay.cW {p : Ptr} {l : Nat} (h : inB wbs p l = true) : Covers [⟨pa s p, l⟩] s.wr :=
  covers_one (L.inW h)

theorem Lay.post {s' : State} {W : List Region} (hP : PostB s s' W) : Lay rbs wbs s' := by
  have e : ∀ b ∈ rbs ++ wbs, s'.gpr b.1 = s.gpr b.1 := fun b hb => hP.bs _ (L.bs b hb)
  refine ⟨L.small, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_, L.bs, by rw [hP.rsp]; exact L.sp32⟩
  · rw [e b hb, e b' hb']; exact L.dj b hb b' hb' hne hw
  · rw [e b hb, hP.rsp]; exact L.stk b hb
  · rw [e b hb]; exact L.nw b hb
  · rw [e b hb, hP.rd, hP.wr]; exact L.rd b hb
  · rw [e b (List.mem_append_right _ hb), hP.wr]; exact L.wr b hb
  · rw [e b hb, hP.rsp]; exact L.ret b hb

end

/-! ## What is kept -/

/-- The region of `w.2` bytes at the pointer `w.1`. -/
abbrev toR (s : State) (w : Ptr × Nat) : Region := ⟨pa s w.1, w.2⟩

/-- `PostB`, with the regions written given as pointers. -/
abbrev PPostB (s s' : State) (ws : List (Ptr × Nat)) : Prop := PostB s s' (ws.map (toR s))

theorem map_toR_post {s s' : State} {W : List Region} (hP : PostB s s' W) {ws : List (Ptr × Nat)}
    (h : ∀ w ∈ ws, w.1.1 ∈ bases) : ws.map (toR s') = ws.map (toR s) :=
  List.map_congr_left fun w hw => by simp only [toR, hP.pa (h w hw)]

theorem PPostB.trans {s s₁ s₂ : State} {ws₁ ws₂ ws : List (Ptr × Nat)} (h₁ : PPostB s s₁ ws₁)
    (h₂ : PPostB s₁ s₂ ws₂) (hcs : ∀ w ∈ ws₂, w.1.1 ∈ bases) (hw₁ : ∀ w ∈ ws₁, w ∈ ws)
    (hw₂ : ∀ w ∈ ws₂, w ∈ ws) : PPostB s s₂ ws := by
  have h₂' : PostB s₁ s₂ (ws₂.map (toR s)) := by rw [← map_toR_post h₁ hcs]; exact h₂
  refine PostB.trans h₁ h₂' (fun r hr => ?_) fun r hr => ?_
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₁ w hw)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₂ w hw)

theorem PPostB.mono {s s' : State} {ws ws' : List (Ptr × Nat)} (h : PPostB s s' ws) (hw : ∀ w ∈ ws, w ∈ ws') :
    PPostB s s' ws' :=
  PostB.trans (PostB.refl s []) h (fun _ h => absurd h List.not_mem_nil) fun r hr => by
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw w hw')

/-- The `l` bytes at `p` lie in the layout, apart from the regions `ws`, and
`p`'s register is one of `bases`. -/
def keepB (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) (p : Ptr) (l : Nat) : Bool :=
  decide (p.1 ∈ bases) && inB bs p l && ws.all fun w => sepB bs p l w.1 w.2

theorem keepB_nil {bs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {p : Ptr} {l : Nat}
    (hc : keepB bs ws p l = true) : keepB bs [] p l = true := by
  simp only [keepB, Bool.and_eq_true, List.all_nil, and_true] at hc ⊢
  exact hc.1

theorem keepB_nil_of {bs : List (Reg × Nat)} {p : Ptr} {l : Nat} (hb : p.1 ∈ bases) (h : inB bs p l = true) :
    keepB bs [] p l = true := by
  simp only [keepB, Bool.and_eq_true, List.all_nil, and_true, decide_eq_true_eq]
  exact ⟨hb, h⟩

theorem keepB_bs {bs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {p : Ptr} {l : Nat}
    (hc : keepB bs ws p l = true) : p.1 ∈ bases := by
  simp only [keepB, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.1.1

section
variable {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay rbs wbs s) {ws : List (Ptr × Nat)}
  {p : Ptr} {l : Nat}
include L

theorem Lay.fdisj (hc : keepB (rbs ++ wbs) ws p l = true) :
    ∀ r ∈ ws.map (toR s) ++ [below (s.gpr .rsp) 32], Region.Disjoint ⟨pa s p, l⟩ r := by
  simp only [keepB, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨_, hin⟩, hall⟩ := hc
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact L.disj (hall w hw)
  · rw [List.mem_singleton] at hr
    subst hr
    exact (L.stkD hin).symm

theorem Lay.keepBytes (hP : PPostB s s' ws) (hc : keepB (rbs ++ wbs) ws p l = true) :
    bytesAt s'.mem (pa s' p) l = bytesAt s.mem (pa s p) l := by
  rw [hP.pa (keepB_bs hc)]
  have hin : inB (rbs ++ wbs) p l = true := by
    simp only [keepB, Bool.and_eq_true] at hc; exact hc.1.2
  obtain ⟨n, hn, hl⟩ := inB_spec hin
  exact Proof.MlKem.bytesAt_frame hP.frame (L.fdisj hc) (by have := L.small _ hn; omega)

theorem Lay.keepPoly {f : Spec.MlDsa.Poly} (hP : PPostB s s' ws) (hc : keepB (rbs ++ wbs) ws p 1024 = true)
    (h : Spec.MlDsa.PolyIs s.mem (pa s p) f) : Spec.MlDsa.PolyIs s'.mem (pa s' p) f := by
  rw [hP.pa (keepB_bs hc)]
  exact Proof.MlDsa.Verify.polyIs_frame hP.frame (L.fdisj hc) h

theorem Lay.keepPolyAt (hP : PPostB s s' ws) (hc : keepB (rbs ++ wbs) ws p 1024 = true) :
    Spec.MlDsa.polyAt s'.mem (pa s' p) = Spec.MlDsa.polyAt s.mem (pa s p) := by
  rw [hP.pa (keepB_bs hc)]
  exact Proof.MlDsa.Verify.polyAt_frame hP.frame (L.fdisj hc)

theorem Lay.keepRed (hP : PPostB s s' ws) (hc : keepB (rbs ++ wbs) ws p 1024 = true)
    (h : Spec.MlDsa.Reduced s.mem (pa s p)) : Spec.MlDsa.Reduced s'.mem (pa s' p) := by
  rw [hP.pa (keepB_bs hc)]
  exact Proof.MlDsa.Verify.reduced_frame hP.frame (L.fdisj hc) h

theorem Lay.keepHint {k : Nat} {h : List (Vector Bool Spec.MlDsa.n)} (hP : PPostB s s' ws)
    (hc : keepB (rbs ++ wbs) ws p (1024 * k) = true)
    (hh : Spec.MlDsa.HintIs s.mem (pa s p) k h) : Spec.MlDsa.HintIs s'.mem (pa s' p) k h := by
  rw [hP.pa (keepB_bs hc)]
  have hin : inB (rbs ++ wbs) p (1024 * k) = true := by
    simp only [keepB, Bool.and_eq_true] at hc; exact hc.1.2
  obtain ⟨n, hn, hl⟩ := inB_spec hin
  exact Proof.MlDsa.Verify.hintIs_frame hP.frame (by have := L.small _ hn; omega) (L.fdisj hc) hh

theorem Lay.keepW (hP : PPostB s s' ws) (hc : keepB (rbs ++ wbs) ws p 8 = true) :
    s'.mem.readW (pa s' p) 64 = s.mem.readW (pa s p) 64 := by
  rw [hP.pa (keepB_bs hc)]
  exact hP.frame.readW (Region.contains_self _ _) (L.fdisj hc) (by decide)

end

/-- The return address is kept by code that writes within the layout and the stack. -/
theorem Lay.keepRet {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay rbs wbs s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hin : ∀ w ∈ ws, inB (rbs ++ wbs) w.1 w.2 = true) :
    s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  refine hP.frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    obtain ⟨n, hn, hsub⟩ := L.sub (hin w hw)
    exact (L.ret _ hn).sub_right hsub
  · rw [List.mem_singleton] at hr; subst hr
    intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    bv_omega

end VG.Proof.MlDsa.X86_64.Verify
