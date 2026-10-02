import VerifiedGarbage.Proof.MlKem.X86.Keccak
import VerifiedGarbage.Proof.MlKem.X86.Leaf
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.MlKem.X86.Top

/-!
# ML-KEM on x86 (32-bit): the setting of the top-level functions

A top-level function takes buffers as arguments (`Lay`: each one's length, and
whether it is written), one of which (`sc`) is its working space `scratch`;
its precondition (`TPre`, which its contract implies) says where they are. It
saves its caller's registers in a frame of 16 bytes (`leaf`), keeps `esi =
scratch`, and calls the primitives and the Keccak functions, whose calls use
the `stk - 16` bytes of stack below the frame.

Buffers are named by an argument and an offset (`Buf`), so that whether
two are disjoint (`Buf.sep`), and whether one lies in its argument
(`Buf.ok`), are computed (`decide`) from the numbers. `Ctx` is what holds
throughout the body: `esp`, `esi`, the permissions, and memory changed only
in the written arguments and the calls' stack (`W`).
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.Sha3.X86 (reg32)

/-- The layout of a top-level function: its arguments' lengths and whether
each is written; which one is `scratch`; and the stack its contract gives. -/
structure Lay where
  args : List (Nat × Bool)
  sc : Nat
  stk : Nat

namespace Lay
variable (Y : Lay)
def alen (i : Nat) : Nat := (Y.args.getD i (0, false)).1
def awr (i : Nat) : Bool := (Y.args.getD i (0, false)).2
def n : Nat := Y.args.length

/-- `b` is within its argument, and not empty. -/
def ok (b : Buf) : Bool := decide (b.arg < Y.n) && decide (0 < b.len) && decide (b.off + b.len ≤ Y.alen b.arg)
/-- `b` is within an argument that is written. -/
def okW (b : Buf) : Bool := Y.ok b && Y.awr b.arg
/-- `b` and `c` do not overlap, or are in arguments one of which is written
(which the precondition makes disjoint). -/
def sep (b c : Buf) : Bool :=
  if b.arg = c.arg then decide (b.off + b.len ≤ c.off) || decide (c.off + c.len ≤ b.off)
  else Y.awr b.arg || Y.awr c.arg
end Lay

section
variable (Y : Lay) (s₀ : State)
abbrev argR (i : Nat) : Region := ⟨(arg s₀ i).setWidth 64, Y.alen i⟩
abbrev gR : Region := ⟨argAddr s₀ 0, 4 * Y.n⟩
/-- `esp` in the body. -/
abbrev E1 : BitVec 32 := (P0 s₀).gpr .esp
/-- The stack the calls use. -/
abbrev cR : Region := below (E1 s₀) (Y.stk - 16)
/-- What the body may change: the written arguments and the calls' stack. -/
def W : List Region := ((List.range Y.n).filter Y.awr).map (argR Y s₀) ++ [cR Y s₀]
end

section
variable (s₀ : State) (b : Buf)
/-- The address of `b`. -/
abbrev _root_.VG.Impl.MlKem.X86.Buf.ptr : BitVec 32 := VG.X86.arg s₀ b.arg + BitVec.ofNat 32 b.off
abbrev _root_.VG.Impl.MlKem.X86.Buf.addr : Addr := (b.ptr s₀).setWidth 64
abbrev _root_.VG.Impl.MlKem.X86.Buf.rgn : Region := reg32 (b.ptr s₀) b.len
end

structure TPre (Y : Lay) (s₀ : State) : Prop where
  sp : Y.stk ≤ (E0 s₀).toNat
  sp16 : 16 ≤ Y.stk
  sp' : (E0 s₀).toNat + 4 + 4 * Y.n ≤ 2 ^ 32
  rd : ∀ i < Y.n, Y.awr i = false → argR Y s₀ i ∈ s₀.rd
  wr : ∀ i < Y.n, Y.awr i = true → argR Y s₀ i ∈ s₀.wr
  gwr : gR Y s₀ ∈ s₀.rd ++ s₀.wr
  disj : ∀ i < Y.n, ∀ j < Y.n, i ≠ j → (Y.awr i || Y.awr j) = true → (argR Y s₀ i).Disjoint (argR Y s₀ j)
  g_disj : ∀ i < Y.n, (gR Y s₀).Disjoint (argR Y s₀ i)
  ret : ∀ i < Y.n, (retR s₀).Disjoint (argR Y s₀ i)
  stk_a : ∀ i < Y.n, (below (E0 s₀) Y.stk).Disjoint (argR Y s₀ i)
  stk_g : (below (E0 s₀) Y.stk).Disjoint (gR Y s₀)
  fit : ∀ i < Y.n, (arg s₀ i).toNat + Y.alen i ≤ 2 ^ 32
  sc_lt : Y.sc < Y.n

/-- Two runs agree on `esp`, the arguments and what `lk` says the function may leak. -/
def TPub (Y : Lay) (lk : State → List Byte) (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ (∀ i < Y.n, arg s₀ i = arg s₀' i) ∧ lk s₀ = lk s₀'

theorem TPub.E1 {Y : Lay} {lk : State → List Byte} {s₀ s₀' : State} (hq : TPub Y lk s₀ s₀') :
    E1 s₀ = E1 s₀' := by
  simp only [P0_esp, hq.1]

theorem TPub.sc {Y : Lay} {lk : State → List Byte} {s₀ s₀' : State} (hq : TPub Y lk s₀ s₀') (hp : TPre Y s₀) :
    arg s₀ Y.sc = arg s₀' Y.sc := hq.2.1 _ hp.sc_lt

theorem TPub.ptr {Y : Lay} {lk : State → List Byte} {s₀ s₀' : State} (hq : TPub Y lk s₀ s₀') {b : Buf}
    (hb : Y.ok b = true) : b.ptr s₀ = b.ptr s₀' := by
  simp only [Lay.ok, Bool.and_eq_true, decide_eq_true_eq] at hb
  simp only [Buf.ptr, hq.2.1 _ hb.1.1]

/-! ## Stack geometry -/

theorem below_adj {sp : BitVec 32} {a b : Nat} (h : a + b ≤ sp.toNat) :
    (below sp a).Disjoint (below (sp - BitVec.ofNat 32 a) b) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have hk : b ≤ (sp - BitVec.ofNat 32 a).toNat := by rw [sub_toNat (by omega)]; omega
  rw [Taint.sub_setWidth (by omega)] at h₁
  rw [Taint.sub_setWidth hk, Taint.sub_setWidth (by omega)] at h₂
  have := sp.isLt
  have hE : (sp.setWidth 64).toNat = sp.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  generalize sp.setWidth 64 = E at *
  bv_omega

theorem ret_below {sp : BitVec 32} {n : Nat} (h : n ≤ sp.toNat) :
    (⟨sp.setWidth 64, 4⟩ : Region).Disjoint (below sp n) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth h] at h₂
  have := sp.isLt
  have hE : (sp.setWidth 64).toNat = sp.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  generalize sp.setWidth 64 = E at *
  bv_omega

theorem E1_nat (s₀ : State) (h : 16 ≤ (E0 s₀).toNat) : (E1 s₀).toNat = (E0 s₀).toNat - 16 := by
  rw [E1, P0_esp]; exact sub_toNat (k := 16) h

theorem E1_eq (s₀ : State) : E1 s₀ = E0 s₀ - BitVec.ofNat 32 16 := P0_esp s₀

theorem toNat_off {x : BitVec 32} {o : Nat} (h : x.toNat + o < 2 ^ 32) :
    (x + BitVec.ofNat 32 o).toNat = x.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt h]

namespace TPre
variable {Y : Lay} {s₀ : State} (hp : TPre Y s₀)
include hp

theorem E0_big : 16 ≤ (E0 s₀).toNat := Nat.le_trans hp.sp16 hp.sp

theorem stk_eq : (⟨(E0 s₀).setWidth 64 - BitVec.ofNat 64 Y.stk, Y.stk⟩ : Region) = below (E0 s₀) Y.stk := by
  simp only [below]; rw [Taint.sub_setWidth hp.sp]

theorem frame_sub : Region.Sub (frameR s₀) (below (E0 s₀) Y.stk) := below_sub hp.sp16 hp.sp

theorem c_sub : Region.Sub (cR Y s₀) (below (E0 s₀) Y.stk) := by
  rw [cR, E1_eq]
  exact below_inner (by have := hp.sp16; omega) hp.sp

theorem frame_c : (frameR s₀).Disjoint (cR Y s₀) := by
  rw [cR, E1_eq]; exact below_adj (by have := hp.sp; have := hp.sp16; omega)

theorem ret_c : (retR s₀).Disjoint (cR Y s₀) := (ret_below hp.sp).sub_right hp.c_sub

theorem fr16 : (⟨(E0 s₀).setWidth 64 - 16#64, 16⟩ : Region) = frameR s₀ := by
  simp only [frameR, below]; rw [Taint.sub_setWidth hp.E0_big]

omit hp in
theorem mem_W {r : Region} (h : r ∈ W Y s₀) : (∃ i < Y.n, Y.awr i = true ∧ r = argR Y s₀ i) ∨ r = cR Y s₀ := by
  simp only [W, List.mem_append, List.mem_map, List.mem_filter, List.mem_range, List.mem_singleton] at h
  rcases h with ⟨i, ⟨hi, hw⟩, rfl⟩ | rfl
  · exact .inl ⟨i, hi, hw, rfl⟩
  · exact .inr rfl

theorem hW : ∀ r ∈ W Y s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro r hr
  rcases mem_W hr with ⟨i, hi, _, rfl⟩ | rfl
  · exact ⟨(hp.stk_a i hi).sub_left hp.frame_sub, hp.ret i hi⟩
  · exact ⟨hp.frame_c, hp.ret_c⟩

omit hp in
theorem argW {i : Nat} (hi : i < Y.n) (hw : Y.awr i = true) : argR Y s₀ i ∈ W Y s₀ := by
  simp only [W, List.mem_append, List.mem_map, List.mem_filter, List.mem_range]
  exact .inl ⟨i, ⟨hi, hw⟩, rfl⟩

omit hp in
theorem cW : cR Y s₀ ∈ W Y s₀ := by simp [W]

/-- A buffer read-only on entry is disjoint from everything the body changes. -/
theorem roW {i : Nat} (hi : i < Y.n) (hw : Y.awr i = false) : ∀ r ∈ W Y s₀, (argR Y s₀ i).Disjoint r := by
  intro r hr
  rcases mem_W hr with ⟨j, hj, hwj, rfl⟩ | rfl
  · exact hp.disj i hi j hj (by rintro rfl; rw [hw] at hwj; cases hwj) (by rw [hwj]; simp)
  · exact ((hp.stk_a i hi).sub_left hp.c_sub).symm

theorem gW : ∀ r ∈ W Y s₀, (gR Y s₀).Disjoint r := by
  intro r hr
  rcases mem_W hr with ⟨j, hj, _, rfl⟩ | rfl
  · exact hp.g_disj j hj
  · exact (hp.stk_g.sub_left hp.c_sub).symm

end TPre

/-! ## Buffers -/

/-- Two parts of a region at a 32-bit pointer that do not overlap. -/
theorem disj_at {x : BitVec 32} {len a b n k : Nat} (ha : a + n ≤ len) (hb : b + k ≤ len)
    (hx : x.toNat + len ≤ 2 ^ 32) (h : a + n ≤ b ∨ b + k ≤ a) :
    (⟨x.setWidth 64 + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨x.setWidth 64 + BitVec.ofNat 64 b, k⟩ :=
  fun y h₁ h₂ => sep_at ha hb hx h y (by simp only [Region.Contains] at h₁; omega)
    (by simp only [Region.Contains] at h₂; omega)

theorem Lay.ok_iff {Y : Lay} {b : Buf} :
    Y.ok b = true ↔ b.arg < Y.n ∧ 0 < b.len ∧ b.off + b.len ≤ Y.alen b.arg := by
  simp [Lay.ok, and_assoc]

theorem Lay.okW_iff {Y : Lay} {b : Buf} : Y.okW b = true ↔ Y.ok b = true ∧ Y.awr b.arg = true := by
  simp [Lay.okW]

namespace Buf
variable {Y : Lay} {s₀ : State} (hp : TPre Y s₀) {b : Buf} (hb : Y.ok b = true)
include hp hb

theorem ptr_nat : (b.ptr s₀).toNat = (X86.arg s₀ b.arg).toNat + b.off := by
  obtain ⟨h₁, h₂, h₃⟩ := Lay.ok_iff.mp hb
  have := hp.fit _ h₁
  exact toNat_off (by omega)

theorem fit : (b.ptr s₀).toNat + b.len ≤ 2 ^ 32 := by
  obtain ⟨h₁, h₂, h₃⟩ := Lay.ok_iff.mp hb
  have := hp.fit _ h₁
  rw [ptr_nat hp hb]; omega

theorem addr_eq : b.addr s₀ = (X86.arg s₀ b.arg).setWidth 64 + BitVec.ofNat 64 b.off := by
  obtain ⟨h₁, h₂, h₃⟩ := Lay.ok_iff.mp hb
  have := hp.fit _ h₁
  exact ea_off (by omega)

theorem sub : Region.Sub (b.rgn s₀) (argR Y s₀ b.arg) := by
  obtain ⟨h₁, h₂, h₃⟩ := Lay.ok_iff.mp hb
  show Region.Sub ⟨b.addr s₀, b.len⟩ _
  rw [addr_eq hp hb]
  exact sub_of_contains (contains_at h₃ (hp.fit _ h₁))

theorem stkD {N : Nat} (hN : N + 16 ≤ Y.stk) : (below (E1 s₀) N).Disjoint (b.rgn s₀) := by
  obtain ⟨h₁, -, -⟩ := Lay.ok_iff.mp hb
  refine ((hp.stk_a _ h₁).sub_left ?_).sub_right (sub hp hb)
  rw [E1_eq]
  exact below_inner hN hp.sp

theorem disj {c : Buf} (hc : Y.ok c = true) (hs : Y.sep b c = true) : (b.rgn s₀).Disjoint (c.rgn s₀) := by
  obtain ⟨hb₁, hb₂, hb₃⟩ := Lay.ok_iff.mp hb
  obtain ⟨hc₁, hc₂, hc₃⟩ := Lay.ok_iff.mp hc
  unfold Lay.sep at hs
  split at hs
  · rename_i e
    show Region.Disjoint ⟨b.addr s₀, b.len⟩ ⟨c.addr s₀, c.len⟩
    rw [addr_eq hp hb, addr_eq hp hc, ← e]
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hs
    rw [e] at hb₃
    exact disj_at (len := Y.alen c.arg) (by omega) hc₃ (by rw [← e]; exact hp.fit _ hb₁) hs
  · rename_i e
    exact ((hp.disj _ hb₁ _ hc₁ e hs).sub_left (sub hp hb)).sub_right (sub hp hc)

theorem within {s : State} (hr : s.rd = (P0 s₀).rd) (hw : s.wr = (P0 s₀).wr) :
    Within (b.rgn s₀) (s.rd ++ s.wr) := by
  obtain ⟨h₁, -, h₃⟩ := Lay.ok_iff.mp hb
  refine ⟨argR Y s₀ b.arg, ?_, b.off, addr_eq hp hb, h₃⟩
  rw [hr, hw, pushed_rd, P0_wr]
  cases e : Y.awr b.arg
  · exact List.mem_append_left _ (hp.rd _ h₁ e)
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ (hp.wr _ h₁ e))

theorem withinW (hw' : Y.awr b.arg = true) {s : State} (hw : s.wr = (P0 s₀).wr) : Within (b.rgn s₀) s.wr := by
  obtain ⟨h₁, -, h₃⟩ := Lay.ok_iff.mp hb
  refine ⟨argR Y s₀ b.arg, ?_, b.off, addr_eq hp hb, h₃⟩
  rw [hw, P0_wr]
  exact List.mem_cons_of_mem _ (hp.wr _ h₁ hw')

theorem inW (hw' : Y.awr b.arg = true) : ∃ r ∈ W Y s₀, Region.Sub (b.rgn s₀) r :=
  ⟨_, TPre.argW (Lay.ok_iff.mp hb).1 hw', sub hp hb⟩

theorem roW (hro : Y.awr b.arg = false) : ∀ r ∈ W Y s₀, (b.rgn s₀).Disjoint r :=
  fun r hr => (hp.roW (Lay.ok_iff.mp hb).1 hro r hr).sub_left (sub hp hb)

/-- A buffer apart from the regions a call changes. -/
theorem frD {bs : List Buf} (hbs : bs.all (fun c => Y.ok c && Y.sep b c) = true) {N : Nat}
    (hN : N + 16 ≤ Y.stk) : ∀ r ∈ bs.map (Buf.rgn s₀) ++ [below (E1 s₀) N], (b.rgn s₀).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    have := List.all_eq_true.mp hbs c hc
    simp only [Bool.and_eq_true] at this
    exact disj hp hb this.1 this.2
  · rw [List.mem_singleton] at hr; subst hr
    exact (stkD hp hb hN).symm

theorem inRegW (hw' : Y.awr b.arg = true) {s : State} (hw : s.wr = (P0 s₀).wr) {o n : Nat}
    (h : o + n ≤ b.len) : InRegions s.wr (b.addr s₀ + BitVec.ofNat 64 o) n := by
  obtain ⟨h₁, -, h₃⟩ := Lay.ok_iff.mp hb
  refine ⟨argR Y s₀ b.arg, by rw [hw, P0_wr]; exact List.mem_cons_of_mem _ (hp.wr _ h₁ hw'), ?_⟩
  rw [addr_eq hp hb, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact contains_at (by omega) (hp.fit _ h₁)

theorem inRegR {s : State} (hr : s.rd = (P0 s₀).rd) (hw : s.wr = (P0 s₀).wr) {o n : Nat}
    (h : o + n ≤ b.len) : InRegions (s.rd ++ s.wr) (b.addr s₀ + BitVec.ofNat 64 o) n := by
  obtain ⟨h₁, -, h₃⟩ := Lay.ok_iff.mp hb
  refine ⟨argR Y s₀ b.arg, ?_, ?_⟩
  · rw [hr, hw, pushed_rd, P0_wr]
    cases e : Y.awr b.arg
    · exact List.mem_append_left _ (hp.rd _ h₁ e)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (hp.wr _ h₁ e))
  · rw [addr_eq hp hb, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact contains_at (by omega) (hp.fit _ h₁)

/-- The part of `b` at `o`, within its argument, for a store. -/
theorem contains (hw' : Y.awr b.arg = true) {o n : Nat} (h : o + n ≤ b.len) :
    ∃ r ∈ W Y s₀, r.Contains (b.addr s₀ + BitVec.ofNat 64 o) n := by
  obtain ⟨h₁, -, h₃⟩ := Lay.ok_iff.mp hb
  refine ⟨argR Y s₀ b.arg, TPre.argW h₁ hw', ?_⟩
  rw [addr_eq hp hb, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact contains_at (by omega) (hp.fit _ h₁)

omit hb in
theorem frSub {bs : List Buf} (hbs : bs.all Y.okW = true) {N : Nat} (hN : N + 16 ≤ Y.stk) :
    ∀ r ∈ bs.map (Buf.rgn s₀) ++ [below (E1 s₀) N], ∃ r' ∈ W Y s₀, Region.Sub r r' := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    obtain ⟨h₁, h₂⟩ := Lay.okW_iff.mp (List.all_eq_true.mp hbs c hc)
    exact inW hp h₁ h₂
  · rw [List.mem_singleton] at hr; subst hr
    exact ⟨cR Y s₀, TPre.cW, below_sub (by omega) (by rw [E1_nat s₀ hp.E0_big]; have := hp.sp; omega)⟩

end Buf

/-! ## What holds throughout the body -/

structure Ctx (Y : Lay) (s₀ s : State) : Prop where
  esp : s.gpr .esp = E1 s₀
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = arg s₀ Y.sc
  frame : Frame (W Y s₀) (P0 s₀).mem s.mem

namespace Ctx
variable {Y : Lay} {s₀ s : State}

theorem same {s' : State} (h : Ctx Y s₀ s) (e₁ : s'.gpr .esp = s.gpr .esp) (e₂ : s'.gpr .esi = s.gpr .esi)
    (e₃ : s'.rd = s.rd) (e₄ : s'.wr = s.wr) (e₅ : s'.mem = s.mem) : Ctx Y s₀ s' :=
  ⟨by rw [e₁, h.esp], by rw [e₃, h.rd], by rw [e₄, h.wr], by rw [e₂, h.esi], by rw [e₅]; exact h.frame⟩

/-- After a call that changes memory only within `rs`, parts of `W`. -/
theorem call {s' : State} (h : Ctx Y s₀ s) (e₁ : s'.rd = s.rd) (e₂ : s'.wr = s.wr)
    (e₃ : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {rs : List Region} (fr : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ W Y s₀, Region.Sub r r') : Ctx Y s₀ s' :=
  ⟨by rw [e₃ .esp (by simp [calleeSaved]), h.esp], by rw [e₁, h.rd], by rw [e₂, h.wr],
    by rw [e₃ .esi (by simp [calleeSaved]), h.esi], h.frame.trans (fr.sub hs)⟩

variable (hp : TPre Y s₀) (h : Ctx Y s₀ s)
include hp h

/-- The bytes of a buffer read-only on entry. -/
theorem ro {b : Buf} (hb : Y.ok b = true) (hro : Y.awr b.arg = false) {i : Nat} (hi : i < b.len) :
    s.mem (b.addr s₀ + BitVec.ofNat 64 i) = s₀.mem (b.addr s₀ + BitVec.ofNat 64 i) := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.E0_big)
  rw [saveRegs_len] at hf
  obtain ⟨h₁, -, -⟩ := Lay.ok_iff.mp hb
  rw [h.frame.bytes (R := b.rgn s₀) (Buf.roW hp hb hro) (by show b.len ≤ 2 ^ 64; have := Buf.fit hp hb; omega) hi]
  exact hf.bytes (R := b.rgn s₀) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact (((hp.stk_a _ h₁).sub_left hp.frame_sub).sub_right (Buf.sub hp hb)).symm)
    (by show b.len ≤ 2 ^ 64; have := Buf.fit hp hb; omega) hi

theorem roBytes {b : Buf} (hb : Y.ok b = true) (hro : Y.awr b.arg = false) :
    Spec.Sha3.bytesAt s.mem (b.addr s₀) b.len = Spec.Sha3.bytesAt s₀.mem (b.addr s₀) b.len :=
  bytesAt_congr fun _ hi => h.ro hp hb hro hi

theorem argw {i : Nat} (hi : i < Y.n) : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have fit := hp.sp'
  rw [h.frame.readW (arg_contains hi fit) hp.gW (by decide)]
  exact P0_arg hp.E0_big hi fit (by rw [hp.fr16]; exact hp.stk_g.sub_left hp.frame_sub)

theorem argIn {i : Nat} (hi : i < Y.n) : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [h.rd, h.wr]
  refine ⟨gR Y s₀, ?_, arg_contains hi hp.sp'⟩
  rw [pushed_rd, P0_wr]
  rcases List.mem_append.mp hp.gwr with e | e
  · exact List.mem_append_left _ e
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ e)

omit hp in
theorem argEa {i : Nat} : (s.gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i := by
  rw [h.esp]; exact P0_argAddr s₀ i

end Ctx

end VG.Proof.MlKem.X86.Top
