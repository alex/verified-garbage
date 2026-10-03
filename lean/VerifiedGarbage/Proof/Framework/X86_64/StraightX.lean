import VerifiedGarbage.Proof.Framework.X86_64.StraightY

/-!
# x86-64: straight-line bitwise SSE2 code, quadword lane by lane

As `StraightY`, for the 128-bit `xmm` registers of two-operand SSE2 code and
16-byte slots: a block of `pxor`, `pand`, `por`, `pandn`, `movdqa`,
quadword shifts (`psllq`, `psrlq`) and `movdqu` loads and stores of slots
`[base + 16k]` computes each of the two quadwords of its results from the
same quadword of its operands. `eval` runs it once over an abstract domain on
64-bit words, and `run` relates quadword `q` of every register and slot by
`R q`, for each `q < 2`. A constant in both quadwords (a mask) is made by
`movabs r, v`, `movq x, r` and `punpcklqdq x, x`. The legacy SSE
instructions leave bits 511:128 of their registers alone, and the evaluator
says nothing of them.
-/

namespace VG.X86_64.StraightX

open VG.Bitslice
open VG.X86_64.StraightY (andn shl qword_xor qword_and qword_or qword_andn qword_app
  qword_psrlq qword_psllq andn_eq shl_eq)

/-- The slots: `[base + 16k]` for `k < slots`, read and written. -/
structure Cfg where
  base : Reg
  slots : Nat
  deriving DecidableEq, Repr

/-- The abstract values of the registers and slots, the known constants of
general-purpose registers and of the low quadword of vector registers. -/
structure Env (α : Type) where
  reg : XReg → Option α
  slot : Nat → Option α
  gc : Reg → Option (BitVec 64) := fun _ => none
  xc : XReg → Option (BitVec 64) := fun _ => none

variable {α : Type}

def Env.setReg (e : Env α) (d : XReg) (v : α) : Env α :=
  { e with reg := fun r => if r = d then some v else e.reg r,
           xc := fun r => if r = d then none else e.xc r }

def Env.setSlot (e : Env α) (k : Nat) (v : α) : Env α :=
  { e with slot := fun j => if j = k then some v else e.slot j }

def Cfg.loc (c : Cfg) (m : MemOp) : Option Nat :=
  if m.index = none ∧ m.base = c.base ∧ 0 ≤ m.disp ∧ m.disp % 16 = 0 ∧ m.disp.toNat / 16 < c.slots
  then some (m.disp.toNat / 16) else none

/-- The register an SSE instruction writes, if any. -/
def xdst : Instr → Option XReg
  | .xop (.bin _ d _) | .xop (.shift _ d _) | .xop (.movq d _) => some d
  | .movdquLoad d _ => some d
  | _ => none

section
variable (D : Dom α 64) (c : Cfg)

/-- `op d, s` of the abstract values of `d` and `s`. -/
def binop : XBinOp → Option (α → α → Option α)
  | .pxor => some D.xor
  | .pand => some D.and
  | .por => some D.or
  | .pandn => some (andn D)
  | _ => none

def step (e : Env α) : Instr → Option (Env α)
  | .xop (.bin .movdqa d r) => (e.reg r).map (e.setReg d)
  | .xop (.bin .punpcklqdq d x) =>
    if x = d then (e.xc x).bind fun v => (D.const v).map fun a =>
      { e with reg := fun r => if r = d then some a else e.reg r,
               xc := fun r => if r = d then some v else e.xc r }
    else none
  | .xop (.bin op d r) =>
    match binop D op, e.reg d, e.reg r with
    | some f, some x, some y => (f x y).map (e.setReg d)
    | _, _, _ => none
  | .xop (.shift op d n) =>
    if 1 ≤ n.toNat ∧ n.toNat ≤ 63 then
      match op, e.reg d with
      | .psrlq, some a => (D.shr n.toNat a).map (e.setReg d)
      | .psllq, some a => (shl D n.toNat a).map (e.setReg d)
      | _, _ => none
    else none
  | .movdquLoad d m => match c.loc m with
    | some k => (e.slot k).map (e.setReg d)
    | none => none
  | .movdquStore m r => match c.loc m with
    | some k => (e.reg r).map (e.setSlot k)
    | none => none
  | .movImm64 d v => if d = c.base then none else
    some { e with gc := fun r => if r = d then some v else e.gc r }
  | .xop (.movq d r) => (e.gc r).map fun v =>
    { e with reg := fun x => if x = d then none else e.reg x,
             xc := fun x => if x = d then some v else e.xc x }
  | _ => none

def eval : List Instr → Env α → Option (Env α)
  | [], e => some e
  | i :: is, e => (step D c e i).bind (eval is)

def check (is : List Instr) (e : Env α) (post : Env α → Bool) : Bool :=
  match eval D c is e with
  | some e' => post e'
  | none => false

theorem of_check {is : List Instr} {e : Env α} {post : Env α → Bool}
    (h : check D c is e post = true) : ∃ e', eval D c is e = some e' ∧ post e' = true := by
  unfold check at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · cases h

end

/-! ## Quadwords -/

theorem getLsbD_qword (x : BitVec 128) {q i : Nat} (hi : i < 64) :
    (qword x q).getLsbD i = x.getLsbD (64 * q + i) := by
  simp [qword, hi]

/-! ## Relating abstract and machine states -/

/-- The address of slot `k` of the base address `b`. -/
abbrev xAddr (b : Addr) (k : Nat) : Addr := b + BitVec.ofNat 64 (16 * k)

structure Rel (R : Nat → α → BitVec 64 → Prop) (c : Cfg) (e : Env α) (s : State) : Prop where
  reg : ∀ r a, e.reg r = some a → ∀ q < 2, R q a (qword (s.xmm r) q)
  slot : ∀ k a, k < c.slots → e.slot k = some a →
    ∀ q < 2, R q a (qword (s.mem.readW (xAddr (s.gpr c.base) k) 128) q)
  gc : ∀ r v, e.gc r = some v → s.gpr r = v
  xc : ∀ r v, e.xc r = some v → qword (s.xmm r) 0 = v

structure Ok (c : Cfg) (s : State) : Prop where
  slotIn : ∀ k < c.slots, InRegions s.wr (xAddr (s.gpr c.base) k) 16
  slots : 16 * c.slots < 2 ^ 64

def slotRegion (c : Cfg) (s : State) : Region := ⟨s.gpr c.base, 16 * c.slots⟩

theorem Ok.congr {c : Cfg} {s s' : State} (h : Ok c s) (hb : s'.gpr c.base = s.gpr c.base)
    (hwr : s'.wr = s.wr) : Ok c s' where
  slotIn k hk := by rw [hb, hwr]; exact h.slotIn k hk
  slots := h.slots

theorem slot_sep (b : Addr) {j k : Nat} (hj : 16 * j < 2 ^ 64) (hk : 16 * k < 2 ^ 64) (h : j ≠ k) :
    Mem.Sep (xAddr b j) 16 (xAddr b k) 16 := by
  intro x h₁ h₂
  simp only [xAddr, Offset.sub_add_eq, Offset.toNat_sub_ofNat] at h₁ h₂
  have := (x - b).isLt
  omega

theorem slot_contains (b : Addr) {n k : Nat} (hk : k < n) (hn : 16 * n < 2 ^ 64) :
    (⟨b, 16 * n⟩ : Region).Contains (xAddr b k) (128 / 8) := by
  simp only [Region.Contains, xAddr]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem loc_some {c : Cfg} {m : MemOp} {k : Nat} (h : c.loc m = some k) :
    m.base = c.base ∧ m.index = none ∧ m.disp = ((16 * k : Nat) : Int) ∧ k < c.slots := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    cases h
    obtain ⟨hi, hb, h0, hm, hlt⟩ := h1
    exact ⟨hb, hi, by omega, hlt⟩
  · cases h

theorem ea_of {s : State} {m : MemOp} {b : Reg} {k : Nat} (hb : m.base = b) (hi : m.index = none)
    (hd : m.disp = ((16 * k : Nat) : Int)) : s.ea m = xAddr (s.gpr b) k := by
  simp only [State.ea, hi, hb, hd, xAddr]
  congr 1

theorem xmm_setXmm (s : State) (d r : XReg) (v : BitVec 128) :
    (s.setXmm d v).xmm r = if r = d then v else s.xmm r := rfl

section
variable {D : Dom α 64} {R : Nat → α → BitVec 64 → Prop} {c : Cfg}

structure Post (R : Nat → α → BitVec 64 → Prop) (c : Cfg) (e' : Env α) (s s' : State)
    (writes : XReg → Prop) (gwrites : Reg → Prop) : Prop where
  rel : Rel R c e' s'
  ok : Ok c s'
  base : s'.gpr c.base = s.gpr c.base
  gpr : ∀ r, ¬ gwrites r → s'.gpr r = s.gpr r
  cf : s'.cf = s.cf
  zf : s'.zf = s.zf
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  other : ∀ r, ¬ writes r → s'.xmm r = s.xmm r
  frame : Frame [slotRegion c s] s.mem s'.mem

theorem Post.writes {e' : Env α} {s s' : State} {W W' : XReg → Prop} {G G' : Reg → Prop}
    (p : Post R c e' s s' W G) (h : ∀ r, W r → W' r) (hg : ∀ r, G r → G' r) :
    Post R c e' s s' W' G' :=
  { p with other := fun r hr => p.other r fun hw => hr (h r hw),
           gpr := fun r hr => p.gpr r fun hw => hr (hg r hw) }

/-- A register written by `setXmm` whose quadwords are related. -/
theorem post_setXmm {e : Env α} {s : State} (hok : Ok c s) (hrel : Rel R c e s) {d : XReg} {a : α}
    {v : BitVec 128} (hv : ∀ q < 2, R q a (qword v q)) :
    Post R c (e.setReg d a) s (s.setXmm d v) (· = d) (fun _ => False) where
  rel := {
    reg := fun r b h q hq => by
      simp only [Env.setReg] at h
      rw [xmm_setXmm]
      split at h
      · rename_i hr; cases h; simp only [hr, ite_true]; exact hv q hq
      · rename_i hr; simp only [hr, ite_false]; exact hrel.reg r b h q hq
    slot := fun k b hk h q hq => by
      simpa [State.setXmm] using hrel.slot k b hk h q hq
    gc := fun r v h => by simpa [State.setXmm] using hrel.gc r v h
    xc := fun r v h => by
      simp only [Env.setReg] at h
      rw [xmm_setXmm]
      split at h
      · cases h
      · rename_i hr; simp only [hr, ite_false]; exact hrel.xc r v h }
  ok := hok.congr (by simp [State.setXmm]) (by simp [State.setXmm])
  base := by simp [State.setXmm]
  gpr _ _ := by simp [State.setXmm]
  cf := by simp [State.setXmm]
  zf := by simp [State.setXmm]
  rd := by simp [State.setXmm]
  wr := by simp [State.setXmm]
  other r hr := by rw [xmm_setXmm]; simp [hr]
  frame := by simp only [State.setXmm]; exact Frame.refl _ _

theorem step_ok (hD : ∀ q < 2, D.Sound (R q)) {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c e s) {i : Instr} (h : step D c e i = some e') :
    ∃ s', exec i s = some s' ∧
      Post R c e' s s' (fun r => xdst i = some r) (fun r => i.dst = some r) := by
  cases i with
  | xop o =>
    cases o with
    | bin op d r =>
      by_cases hm : op = .movdqa
      · subst hm
        simp only [step] at h
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        exact ⟨_, rfl, (post_setXmm hok hrel fun q hq => by
          simp only [XBinOp.eval]; exact hrel.reg r a ha q hq).writes
          (fun r h => by simp [xdst, h]) (fun _ h => h.elim)⟩
      by_cases hp : op = .punpcklqdq
      · subst hp
        simp only [step] at h
        split at h
        · rename_i hrd
          subst hrd
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨v, hv, h⟩ := h
          obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
          have hx := hrel.xc r v hv
          refine ⟨_, rfl, ⟨⟨fun x b hx' q hq => ?_, fun k b hk hb q hq => ?_, fun r' w hw => ?_,
            fun x w hw => ?_⟩, hok.congr (by simp [XOp.exec, State.setXmm])
              (by simp [XOp.exec, State.setXmm]),
            by simp [XOp.exec, State.setXmm], fun _ _ => by simp [XOp.exec, State.setXmm],
            by simp [XOp.exec, State.setXmm], by simp [XOp.exec, State.setXmm],
            by simp [XOp.exec, State.setXmm], by simp [XOp.exec, State.setXmm],
            fun x hx' => ?_, by simp only [XOp.exec, State.setXmm]; exact Frame.refl _ _⟩⟩
          · simp only at hx'
            simp only [XOp.exec, xmm_setXmm]
            split at hx'
            · rename_i hxd; cases hx'; simp only [hxd, ite_true, XBinOp.eval]
              rw [qword_app _ _ hq, hx]
              split <;> exact (hD q hq).const ha
            · rename_i hxd; simp only [hxd, ite_false]; exact hrel.reg x b hx' q hq
          · simpa [XOp.exec, State.setXmm] using hrel.slot k b hk hb q hq
          · simpa [XOp.exec, State.setXmm] using hrel.gc r' w hw
          · simp only at hw
            simp only [XOp.exec, xmm_setXmm]
            split at hw
            · rename_i hxd; cases hw; simp only [hxd, ite_true, XBinOp.eval]
              rw [qword_app _ _ (by decide), hx]; rfl
            · rename_i hxd; simp only [hxd, ite_false]; exact hrel.xc x w hw
          · simp only [xdst, Option.some.injEq] at hx'
            simp only [XOp.exec, xmm_setXmm, Ne.symm hx', ite_false]
        · cases h
      · have hstep : step D c e (.xop (.bin op d r)) =
            match binop D op, e.reg d, e.reg r with
            | some f, some x, some y => (f x y).map (e.setReg d)
            | _, _, _ => none := by
          cases op <;> first | rfl | exact absurd rfl hp | exact absurd rfl hm
        rw [hstep] at h
        split at h
        · rename_i f x y hf hx hy
          obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
          have hRx := hrel.reg d x hx
          have hRy := hrel.reg r y hy
          refine ⟨_, rfl, (post_setXmm hok hrel fun q hq => ?_).writes
            (fun r h => by simp [xdst, h]) (fun _ h => h.elim)⟩
          cases op <;> simp only [binop, reduceCtorEq, Option.some.injEq] at hf <;> subst hf <;>
            simp only [XBinOp.eval]
          · rw [qword_xor]; exact (hD q hq).xor (hRx q hq) (hRy q hq) ht
          · rw [qword_or]; exact (hD q hq).or (hRx q hq) (hRy q hq) ht
          · rw [qword_and]; exact (hD q hq).and (hRx q hq) (hRy q hq) ht
          · rw [qword_andn _ _ hq]
            simp only [andn, Option.bind_eq_some_iff] at ht
            obtain ⟨t', ⟨o, ho, ht'⟩, hc⟩ := ht
            rw [← andn_eq]
            exact (hD q hq).and ((hD q hq).xor (hRx q hq) ((hD q hq).const ho) ht') (hRy q hq) hc
        · cases h
    | shift op d n =>
      simp only [step] at h
      split at h
      · rename_i hn
        refine ⟨_, rfl, ?_⟩
        split at h
        · rename_i a ha
          obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
          refine (post_setXmm hok hrel fun q hq => ?_).writes (fun r h => by simp [xdst, h])
            (fun _ h => h.elim)
          rw [qword_psrlq _ (by omega) hq]
          exact (hD q hq).shr (hrel.reg d a ha q hq) hb
        · rename_i a ha
          obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
          refine (post_setXmm hok hrel fun q hq => ?_).writes (fun r h => by simp [xdst, h])
            (fun _ h => h.elim)
          rw [qword_psllq _ (by omega) hq, ← shl_eq _ hn.1 hn.2]
          simp only [shl, Option.bind_eq_some_iff] at hb
          obtain ⟨t, ⟨o, ho, ht⟩, hc⟩ := hb
          exact (hD q hq).ror ((hD q hq).and (hrel.reg d a ha q hq) ((hD q hq).const ho) ht) hc
        · cases h
      · cases h
    | movq d r =>
      simp only [step] at h
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
      have hg := hrel.gc r v hv
      refine ⟨_, rfl, ⟨⟨fun x b hx q hq => ?_, fun k b hk hb q hq => ?_, fun r' w hw => ?_,
        fun x w hw => ?_⟩, hok.congr (by simp [XOp.exec, State.setXmm])
          (by simp [XOp.exec, State.setXmm]),
        by simp [XOp.exec, State.setXmm], fun _ _ => by simp [XOp.exec, State.setXmm],
        by simp [XOp.exec, State.setXmm], by simp [XOp.exec, State.setXmm],
        by simp [XOp.exec, State.setXmm], by simp [XOp.exec, State.setXmm],
        fun x hx => ?_, by simp only [XOp.exec, State.setXmm]; exact Frame.refl _ _⟩⟩
      · simp only at hx
        split at hx
        · cases hx
        · rename_i hxd
          simp only [XOp.exec, xmm_setXmm, hxd, ite_false]
          exact hrel.reg x b hx q hq
      · simpa [XOp.exec, State.setXmm] using hrel.slot k b hk hb q hq
      · simpa [XOp.exec, State.setXmm] using hrel.gc r' w hw
      · simp only at hw
        simp only [XOp.exec, xmm_setXmm]
        split at hw
        · rename_i hxd; cases hw; simp only [hxd, ite_true]
          rw [qword_app _ _ (by decide)]; simp [hg]
        · rename_i hxd; simp only [hxd, ite_false]; exact hrel.xc x w hw
      · simp only [xdst, Option.some.injEq] at hx
        simp only [XOp.exec, xmm_setXmm, Ne.symm hx, ite_false]
    | _ => simp [step] at h
  | movdquLoad d m =>
    simp only [step] at h
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hi, hd, hlt⟩ := loc_some hk
      have hea := ea_of (s := s) hb hi hd
      obtain ⟨r, hr, hc⟩ := hok.slotIn k hlt
      have hin : InRegions (s.rd ++ s.wr) (xAddr (s.gpr c.base) k) 16 :=
        ⟨r, List.mem_append_right _ hr, hc⟩
      refine ⟨s.setXmm d (s.mem.readW (xAddr (s.gpr c.base) k) 128),
        by simp [exec, State.load128, hea, hin], ?_⟩
      exact (post_setXmm hok hrel fun q hq => hrel.slot k a hlt ha q hq).writes
        (fun r h => by simp [xdst, h]) (fun _ h => h.elim)
    · cases h
  | movdquStore m r =>
    simp only [step] at h
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hi, hd, hlt⟩ := loc_some hk
      have hea := ea_of (s := s) hb hi hd
      have hin := hok.slotIn k hlt
      refine ⟨{ s with mem := s.mem.writeW (xAddr (s.gpr c.base) k) (s.xmm r) },
        by simp [exec, State.store128, hea, hin], ?_⟩
      have hsep : ∀ j < c.slots, j ≠ k → Mem.Sep (xAddr (s.gpr c.base) j) (128 / 8)
          (xAddr (s.gpr c.base) k) (128 / 8) := fun j hj hjk =>
        slot_sep _ (by have := hok.slots; omega) (by have := hok.slots; omega) hjk
      refine ⟨⟨fun r' b hr' => hrel.reg r' b hr', fun j b hj hjb => ?_,
        fun r' w hw => hrel.gc r' w hw, fun r' w hw => hrel.xc r' w hw⟩,
        hok.congr rfl rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
      · simp only [Env.setSlot] at hjb
        split at hjb
        · rename_i hjk
          subst hjk
          rw [← Option.some.inj hjb]
          intro q hq
          have e := Mem.readW_writeW_self s.mem (xAddr (s.gpr c.base) j) 16 (s.xmm r) (by decide)
          simp only at e ⊢
          rw [e]
          exact hrel.reg r a ha q hq
        · rename_i hjk
          intro q hq
          simp only
          rw [Mem.readW_writeW_sep (hsep j hj hjk) (by decide)]
          exact hrel.slot j b hj hjb q hq
      · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (slot_contains _ hlt hok.slots)
    · cases h
  | movImm64 d v =>
    simp only [step] at h
    split at h
    · cases h
    · rename_i hdb
      cases h
      refine ⟨s.setReg d v, rfl, ⟨⟨fun r b hr q hq => ?_, fun k b hk hb q hq => ?_,
        fun r w hw => ?_, fun r w hw => ?_⟩, hok.congr ?_ (by simp [State.setReg]), ?_,
        fun r hr => ?_, by simp [State.setReg], by simp [State.setReg], by simp [State.setReg],
        by simp [State.setReg], fun r _ => by simp [State.setReg], ?_⟩⟩
      · simpa [State.setReg] using hrel.reg r b hr q hq
      · simpa [State.setReg, Ne.symm hdb] using hrel.slot k b hk hb q hq
      · simp only at hw
        simp only [State.setReg]
        split at hw
        · rename_i hrd; cases hw; simp [hrd]
        · rename_i hrd; simp only [hrd, ite_false]; exact hrel.gc r w hw
      · simpa [State.setReg] using hrel.xc r w hw
      · simp [State.setReg, Ne.symm hdb]
      · simp [State.setReg, Ne.symm hdb]
      · simp only [Instr.dst, Option.some.injEq] at hr
        simp [State.setReg, Ne.symm hr]
      · simp only [State.setReg]; exact Frame.refl _ _
  | _ => simp [step] at h

theorem run (hD : ∀ q < 2, D.Sound (R q)) {is : List Instr} {e e' : Env α} {s : State}
    (hok : Ok c s) (hrel : Rel R c e s) (h : eval D c is e = some e') :
    ∃ s', runBlock isa is s = some s' ∧
      Post R c e' s s' (fun r => (is.all fun i => xdst i != some r) = false)
        (fun r => (is.all fun i => i.dst != some r) = false) := by
  induction is generalizing e s with
  | nil =>
    cases h
    exact ⟨s, runBlock_nil, hrel, hok, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl,
      Frame.refl _ _⟩
  | cons i is ih =>
    simp only [eval, Option.bind_eq_some_iff] at h
    obtain ⟨e₁, h₁, h₂⟩ := h
    obtain ⟨s₁, hs₁, p₁⟩ := step_ok hD hok hrel h₁
    obtain ⟨s', hs', p⟩ := ih p₁.ok p₁.rel h₂
    refine ⟨s', by rw [runBlock_cons, hs₁, runStep_some]; exact hs', p.rel, p.ok,
      p.base.trans p₁.base, fun r hr => ?_, p.cf.trans p₁.cf, p.zf.trans p₁.zf, p.rd.trans p₁.rd,
      p.wr.trans p₁.wr, fun r hr => ?_, ?_⟩
    · simp only [List.all_cons, Bool.and_eq_false_iff, bne_eq_false_iff_eq, not_or] at hr
      exact (p.gpr r hr.2).trans (p₁.gpr r hr.1)
    · simp only [List.all_cons, Bool.and_eq_false_iff, bne_eq_false_iff_eq, not_or] at hr
      exact (p.other r hr.2).trans (p₁.other r hr.1)
    · refine p₁.frame.trans ?_
      have := p.frame
      simp only [slotRegion, p₁.base] at this
      exact this

end

/-- `Ok` for slots at offset `off` of a writable region. -/
theorem Ok.of_off {c : Cfg} {s : State} {r : Region} {off : Nat} (hr : r ∈ s.wr)
    (hb : s.gpr c.base = r.base + BitVec.ofNat 64 off) (hlen : off + 16 * c.slots ≤ r.len)
    (hn : r.len < 2 ^ 64) : Ok c s where
  slotIn k hk := ⟨r, hr, by
    simp only [Region.Contains, xAddr, hb]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    omega⟩
  slots := by omega

end VG.X86_64.StraightX
