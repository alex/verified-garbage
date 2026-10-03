import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.Arm.Target

/-!
# A scratch buffer on the stack (ARMv7)

`Verified.stackScratch`: code verified for a function whose last argument,
passed on the stack, is a scratch buffer (its contract `Sig.scratchContract`)
runs as a function without that argument when `withStackScratch` allocates
the buffer in a frame on the stack, with `bytes` more bytes of stack. The
frame holds what the code expects at and above `sp` on entry: a copy of the
stack arguments, then the buffer's address (`setArgs`). The code runs from
the state after the frame's push and `setArgs`, with the permissions of the
contract with the argument (`narrow`), and its run there is its run from that
state (`Exec.widen`).

Where AAPCS puts each argument (`classify`) is checked for the signature at
hand (`hcl`, `hloc`, decidable): the buffer is the stack argument after the
others, which take `4m` bytes of stack and otherwise `r0`–`r3`, which
`setArgs` keeps. The copies are memory the code reads on entry, which the
contract without the argument says nothing of: the precondition and
postcondition must read memory only within the function's buffers (`hpre`,
`hpost`), which the frame lies outside of.
-/

namespace VG.Arm

open VG.Impl.StackScratch.Arm VG.Arm.FrameStack

theorem abi_ptrBits : abi.ptrBits = 32 := rfl

/-- The widths of the arguments of `sig`. -/
def widths (sig : Sig) : List Nat := (sig.words abi.ptrBits).map (·.bits abi.ptrBits)

/-- Where AAPCS passes the arguments of `sig`. -/
def locs (sig : Sig) : List Loc := (classify (widths sig) 0 0).1

/-- The bytes of stack the arguments of `sig` take. -/
def nsaa (sig : Sig) : Nat := (classify (widths sig) 0 0).2

/-- The arguments of `sig`. -/
def armArgs (sig : Sig) (s : State) : List (BitVec 64) := (locs sig).map (Loc.val s)

/-- Every argument is 32 or 64 bits wide. -/
theorem widths_mem (sig : Sig) : ∀ w ∈ widths sig, w = 32 ∨ w = 64 := by
  intro w hw
  simp only [widths, Sig.words, List.map_flatMap, List.mem_flatMap] at hw
  obtain ⟨p, -, hp⟩ := hw
  cases h : p.2 with
  | int ty _ =>
    rw [h] at hp; cases ty <;> simp [Param.words, ArgWord.bits, IntTy.bits, abi_ptrBits] at hp <;>
      omega
  | array _ _ _ => rw [h] at hp; simp [Param.words, ArgWord.bits, abi_ptrBits] at hp; omega
  | slice _ _ _ =>
    rw [h] at hp; simp [Param.words, ArgWord.bits, abi_ptrBits] at hp; omega

theorem args_arm (sig : Sig) :
    abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) = some (armArgs sig) := by
  have hw : ((sig.words 32).map (fun x => ArgWord.bits 32 x)).all
      (fun w => decide (w = 32 ∨ w = 64)) = true :=
    List.all_eq_true.mpr fun w h => decide_eq_true (widths_mem sig w h)
  simp only [abi, hw, ite_true]
  rfl

/-- The stack arguments of `sig`, which a contract lets the function only
read. -/
def argArea (sig : Sig) (s : State) : List (Region × Bool) :=
  if nsaa sig = 0 then [] else [(⟨stackArgAddr s 0, nsaa sig⟩, false)]

theorem argArea_arm (sig : Sig) (wa : Bool) (s : State) :
    (abi.argArea ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) s).map
        (fun (r, w) => (r, w && wa)) = argArea sig s := by
  show (if nsaa sig = 0 then [] else [((⟨stackArgAddr s 0, nsaa sig⟩ : Region), false)]).map
    (fun (r, w) => (r, w && wa)) = _
  by_cases h : nsaa sig = 0 <;> simp [argArea, h]

/-- The buffers and the stack arguments of `sig`, and whether each is
writable. -/
def allRegions (sig : Sig) (s : State) : List (Region × Bool) :=
  Sig.bufs sig.params (armArgs sig s) ++ argArea sig s

/-- The precondition of a contract, by where AAPCS passes the arguments. -/
theorem pre_arm {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State} :
    (sig.contract abi pre post wa stack leak).pre s ↔
      ((stack = 0 ∨ stack ≤ s.sp.toNat) ∧ s.sp.toNat + nsaa sig ≤ 2 ^ 32) ∧
      s.rd = ((allRegions sig s).filter (!·.2)).map (·.1) ∧
      s.wr = ((allRegions sig s).filter (·.2)).map (·.1) ∧
      (allRegions sig s).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) ∧
      (∀ r ∈ stackBelow (State.addr s.sp) stack, ∀ a ∈ allRegions sig s, r.Disjoint a.1) ∧
      (∀ a ∈ Sig.bufs sig.params (armArgs sig s), a.1.base.toNat + a.1.len ≤ 2 ^ 32) ∧
      Curry.apply (sig.words abi.ptrBits) pre (armArgs sig s) s.mem := by
  have hwf : abi.wf ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) stack s ↔
      ((stack = 0 ∨ stack ≤ s.sp.toNat) ∧ s.sp.toNat + nsaa sig ≤ 2 ^ 32) := by
    show (match stack with
      | 0 => s.sp.toNat + nsaa sig ≤ 2 ^ 32
      | n => n ≤ s.sp.toNat ∧ s.sp.toNat + nsaa sig ≤ 2 ^ 32) ↔ _
    cases stack <;> simp
  simp only [Sig.contract]
  rw [args_arm]
  simp only [argArea_arm]
  rw [hwf]
  exact Iff.rfl

/-- The postcondition of a contract, by where AAPCS passes the arguments. -/
theorem post_arm {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s s' : State} :
    (sig.contract abi pre post wa stack leak).post s s' ↔
      Curry.apply (sig.words abi.ptrBits) post (armArgs sig s) s.mem s'.mem
        ((s'.gpr .r1 ++ s'.gpr .r0).setWidth _) := by
  simp only [Sig.contract]
  rw [args_arm]
  exact Iff.rfl

/-- The public data of a contract that leaks nothing, by where AAPCS passes
the arguments. -/
theorem pub_arm {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat} {s₁ s₂ : State} :
    (sig.contract abi pre post wa stack none).pub s₁ s₂ ↔
      s₁.sp = s₂.sp ∧
      ∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((armArgs sig s₁).getD i 0).setWidth ((widths sig).getD i 64) =
          ((armArgs sig s₂).getD i 0).setWidth ((widths sig).getD i 64) := by
  simp only [Sig.contract]
  rw [args_arm]
  exact Iff.rfl

theorem classify_length : ∀ (ws : List Nat) (ncrn nsaa : Nat), (classify ws ncrn nsaa).1.length = ws.length
  | [], _, _ => rfl
  | w :: ws, ncrn, nsaa => by
    unfold classify
    split
    · simp only []
      split <;> simp only [List.length_cons, classify_length]
    · simp only []
      split <;> simp only [List.length_cons, classify_length]

theorem armArgs_length (sig : Sig) (s : State) :
    (armArgs sig s).length = (sig.params.flatMap fun p => p.2.words abi.ptrBits).length := by
  rw [armArgs, List.length_map, locs, classify_length, widths, List.length_map]
  rfl

/-! ## The argument with the buffer -/

theorem widths_withScratch (sig : Sig) (nm : String) (e : Elem) (n : Nat) :
    widths (sig.withScratch nm e n) = widths sig ++ [32] := by
  rw [widths, widths, Sig.words_withScratch, List.map_append]
  rfl

/-- AAPCS passes the buffer after the other arguments, on the stack. -/
abbrev ScratchOnStack (sig : Sig) : Prop :=
  classify (widths sig ++ [32]) 0 0 = (locs sig ++ [.stack (nsaa sig) 32], nsaa sig + 4)

theorem nsaa_withScratch {sig : Sig} (hcl : ScratchOnStack sig) (nm : String) (e : Elem) (n : Nat) :
    nsaa (sig.withScratch nm e n) = nsaa sig + 4 := by
  rw [nsaa, widths_withScratch, hcl]

theorem armArgs_withScratch {sig : Sig} (hcl : ScratchOnStack sig) (nm : String) (e : Elem) (n : Nat)
    (s : State) :
    armArgs (sig.withScratch nm e n) s =
      (locs sig).map (Loc.val s) ++ [(stackArg s (nsaa sig / 4)).setWidth 64] := by
  rw [armArgs, locs, widths_withScratch, hcl, List.map_append]
  rfl

/-- `l` is a register `setArgs` keeps, or a stack argument in whole slots
among the first `N` bytes. -/
def Loc.ok (N : Nat) : Loc → Bool
  | .reg r => decide (r ∈ argRegs)
  | .pair lo hi => decide (lo ∈ argRegs) && decide (hi ∈ argRegs)
  | .stack off b => decide (off % 4 = 0) && decide (off + (if b = 64 then 8 else 4) ≤ N)

/-- An argument in a register `s'` keeps, or in a slot it holds a copy of, has
the same value in both. -/
theorem Loc.val_congr {N : Nat} {s s' : State} (hr : ∀ r ∈ argRegs, s'.gpr r = s.gpr r)
    (hs : ∀ i, 4 * i + 4 ≤ N → stackArg s' i = stackArg s i) :
    ∀ l : Loc, l.ok N = true → l.val s' = l.val s
  | .reg r, h => by
    simp only [Loc.ok, decide_eq_true_eq] at h
    simp only [Loc.val, hr r h]
  | .pair lo hi, h => by
    simp only [Loc.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Loc.val, hr lo h.1, hr hi h.2]
  | .stack off b, h => by
    simp only [Loc.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h4, hN⟩ := h
    by_cases hb : b = 64
    · subst hb
      simp only [ite_true] at hN
      simp only [Loc.val]
      rw [hs (off / 4) (by omega), hs (off / 4 + 1) (by omega)]
    · simp only [hb, ite_false] at hN
      have hv : ∀ t : State, Loc.val t (.stack off b) = (stackArg t (off / 4)).setWidth 64 := by
        intro t; unfold Loc.val; split <;> simp_all
      rw [hv, hv, hs (off / 4) (by omega)]

/-! ## Running `setArgs` -/

/-- The address `d` bytes above `sp`. -/
abbrev sa (sp : BitVec 32) (d : Nat) : Addr := State.addr (sp + BitVec.ofNat 32 d)

theorem sa_eq {sp : BitVec 32} {d : Nat} (h : sp.toNat + d < 2 ^ 32) :
    sa sp d = State.addr sp + BitVec.ofNat 64 d := addr_add h

/-- The state after `copyArg bytes j` from `w`. -/
def copyState (bytes j : Nat) (w : State) : State :=
  { w.setReg .lr (w.mem.readW (sa w.sp (bytes + 4 * j)) 32) with
    mem := w.mem.writeW (sa w.sp (4 * j)) (w.mem.readW (sa w.sp (bytes + 4 * j)) 32) }

theorem copyArg_run {bytes j : Nat} {w : State} (hr12 : w.gpr .r12 = w.sp) (ho : bytes + 4 * j < 4096)
    (hr : InRegions (w.rd ++ w.wr) (sa w.sp (bytes + 4 * j)) 4) (hw : InRegions w.wr (sa w.sp (4 * j)) 4) :
    execBlock isa (copyArg bytes j) w =
      some (copyState bytes j w, [.addr (sa w.sp (bytes + 4 * j)), .addr (sa w.sp (4 * j))]) := by
  have h4 : 4 * j < 4096 := by omega
  simp only [copyArg, execBlock, isa, exec, ho, h4, ite_true, State.load32, hr, Option.map_some,
    addrs, State.store32]
  simp [State.setReg, hr12, hw, copyState]

@[simp] theorem copyState_sp (bytes j : Nat) (w : State) : (copyState bytes j w).sp = w.sp := rfl
@[simp] theorem copyState_rd (bytes j : Nat) (w : State) : (copyState bytes j w).rd = w.rd := rfl
@[simp] theorem copyState_wr (bytes j : Nat) (w : State) : (copyState bytes j w).wr = w.wr := rfl
theorem copyState_gpr (bytes j : Nat) (w : State) {q : Reg} (h : q ≠ .lr) :
    (copyState bytes j w).gpr q = w.gpr q := by
  simp [copyState, State.setReg, h]

/-- The state after copying the first `m` argument slots from `w`. -/
def copiedState (bytes : Nat) (w : State) : Nat → State
  | 0 => w
  | m + 1 => copyState bytes m (copiedState bytes w m)

@[simp] theorem copiedState_sp (bytes : Nat) (w : State) : ∀ m, (copiedState bytes w m).sp = w.sp
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_sp, copiedState_sp bytes w m]
@[simp] theorem copiedState_rd (bytes : Nat) (w : State) : ∀ m, (copiedState bytes w m).rd = w.rd
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_rd, copiedState_rd bytes w m]
@[simp] theorem copiedState_wr (bytes : Nat) (w : State) : ∀ m, (copiedState bytes w m).wr = w.wr
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_wr, copiedState_wr bytes w m]
theorem copiedState_gpr (bytes : Nat) (w : State) {q : Reg} (h : q ≠ .lr) :
    ∀ m, (copiedState bytes w m).gpr q = w.gpr q
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_gpr _ _ _ h, copiedState_gpr bytes w h m]

/-- The addresses copying the first `m` slots accesses. -/
def copyTrace (bytes : Nat) (sp : BitVec 32) (m : Nat) : List Leak :=
  (List.range m).flatMap fun j => [.addr (sa sp (bytes + 4 * j)), .addr (sa sp (4 * j))]

theorem copies_run {bytes : Nat} {w : State} (hr12 : w.gpr .r12 = w.sp) :
    ∀ m, bytes + 4 * m ≤ 4096 → (∀ j < m, InRegions (w.rd ++ w.wr) (sa w.sp (bytes + 4 * j)) 4) →
      (∀ j < m, InRegions w.wr (sa w.sp (4 * j)) 4) →
      execBlock isa ((List.range m).flatMap (copyArg bytes)) w =
        some (copiedState bytes w m, copyTrace bytes w.sp m)
  | 0, _, _, _ => rfl
  | m + 1, ho, hr, hw => by
    rw [List.range_succ, List.flatMap_append, execBlock_append,
      copies_run hr12 m (by omega) (fun j hj => hr j (by omega)) (fun j hj => hw j (by omega))]
    simp only [Option.bind_some, List.flatMap_singleton]
    rw [copyArg_run (by rw [copiedState_gpr _ _ (by decide), copiedState_sp]; exact hr12) (by omega)
      (by simpa using hr m (by omega)) (by simpa using hw m (by omega))]
    simp only [Option.map_some, copiedState, copiedState_sp, copyTrace, List.range_succ,
      List.flatMap_append, List.flatMap_singleton]

/-- Copying the first `m` slots writes only within the `m` destination slots
(from `sp`), which then hold the source slots (from `sp + bytes`). -/
theorem copiedState_mem {bytes : Nat} {w : State} :
    ∀ m, w.sp.toNat + bytes + 4 * m ≤ 2 ^ 32 → 4 * m ≤ bytes →
      Frame [⟨State.addr w.sp, 4 * m⟩] w.mem (copiedState bytes w m).mem ∧
      ∀ j < m, (copiedState bytes w m).mem.readW (sa w.sp (4 * j)) 32 =
        w.mem.readW (sa w.sp (bytes + 4 * j)) 32
  | 0, _, _ => ⟨Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | m + 1, hfit, hb => by
    obtain ⟨f, hv⟩ := copiedState_mem (bytes := bytes) (w := w) m (by omega) (by omega)
    have hA : ∀ d, d < bytes + 4 * (m + 1) → sa w.sp d = State.addr w.sp + BitVec.ofNat 64 d :=
      fun d hd => sa_eq (by omega)
    have hR : Region.Sub ⟨State.addr w.sp, 4 * m⟩ ⟨State.addr w.sp, 4 * (m + 1)⟩ :=
      Region.sub_prefix (by omega)
    have f' : Frame [⟨State.addr w.sp, 4 * (m + 1)⟩] w.mem (copiedState bytes w m).mem :=
      Frame.sub f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, hR⟩
    -- The source of slot `m` is above the first `m` destinations.
    have hsrc : (copiedState bytes w m).mem.readW (sa w.sp (bytes + 4 * m)) 32 =
        w.mem.readW (sa w.sp (bytes + 4 * m)) 32 := by
      rw [hA _ (by omega)]
      refine f.readW (r := ⟨State.addr w.sp + BitVec.ofNat 64 (bytes + 4 * m), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (d := bytes + 4 * m) (n := 4) (k := 4 * m) (by omega) (by omega)
    refine ⟨?_, fun j hj => ?_⟩
    · show Frame _ w.mem ((copiedState bytes w m).mem.writeW _ _)
      rw [copiedState_sp]
      refine f'.writeW (List.mem_singleton_self _) _ ?_
      rw [hA _ (by omega)]
      exact Offset.contains_base _ (d := 4 * m) (k := 4 * (m + 1)) (by omega) (by omega)
    · show ((copiedState bytes w m).mem.writeW (sa (copiedState bytes w m).sp (4 * m))
          ((copiedState bytes w m).mem.readW
            (sa (copiedState bytes w m).sp (bytes + 4 * m)) 32)).readW _ 32 = _
      rw [copiedState_sp]
      rcases Nat.lt_or_ge j m with hj' | hj'
      · rw [Mem.readW_writeW_sep, hv j hj']
        · rw [hA _ (by omega), hA _ (by omega)]
          exact Offset.sep _ (d := 4 * j) (n := 4) (e := 4 * m) (k := 4) (by omega) (by omega)
            (by omega)
        · decide
      · obtain rfl : j = m := by omega
        rw [Mem.readW_writeW_self32, hsrc]

/-- The state after saving `lr` at `sp + 4m + 4` (and `r12 = sp`). -/
def savedState (m : Nat) (u : State) : State :=
  { u.setReg .r12 u.sp with mem := u.mem.writeW (sa u.sp (4 * m + 4)) (u.gpr .lr) }

theorem head_run {m : Nat} {u : State} (hm : 4 * m + 4 < 4096)
    (hw : InRegions u.wr (sa u.sp (4 * m + 4)) 4) :
    execBlock isa [.addSp .r12 0, .str .lr .r12 (4 * m + 4)] u =
      some (savedState m u, [.addr (sa u.sp (4 * m + 4))]) := by
  simp only [execBlock, isa, exec, show (0 : Nat) < 256 by decide, ite_true, hm, Option.map_some,
    addrs, State.store32]
  simp [State.setReg, savedState, hw]

@[simp] theorem savedState_sp (m : Nat) (u : State) : (savedState m u).sp = u.sp := rfl
@[simp] theorem savedState_rd (m : Nat) (u : State) : (savedState m u).rd = u.rd := rfl
@[simp] theorem savedState_wr (m : Nat) (u : State) : (savedState m u).wr = u.wr := rfl
theorem savedState_gpr (m : Nat) (u : State) {q : Reg} (h : q ≠ .r12) :
    (savedState m u).gpr q = u.gpr q := by
  simp [savedState, State.setReg, h]
theorem savedState_r12 (m : Nat) (u : State) : (savedState m u).gpr .r12 = u.sp := by
  simp [savedState, State.setReg]

/-- `add lr, sp, #4m + 8; str lr, [r12, #4m]; ldr lr, [sp, #4m + 4]`: pass the
buffer, and restore `lr`. -/
theorem tail_run {m : Nat} {w : State} (hr12 : w.gpr .r12 = w.sp) (himm : 4 * m + 8 < 256)
    (hw : InRegions w.wr (sa w.sp (4 * m)) 4) (hr : InRegions (w.rd ++ w.wr) (sa w.sp (4 * m + 4)) 4) :
    ∃ w', execBlock isa [.addSp .lr (4 * m + 8), .str .lr .r12 (4 * m), .ldrSp .lr (4 * m + 4)] w =
        some (w', [.addr (sa w.sp (4 * m)), .addr (sa w.sp (4 * m + 4))]) ∧
      w'.rd = w.rd ∧ w'.wr = w.wr ∧ w'.sp = w.sp ∧ (∀ q, q ≠ .lr → w'.gpr q = w.gpr q) ∧
      w'.mem = w.mem.writeW (sa w.sp (4 * m)) (w.sp + BitVec.ofNat 32 (4 * m + 8)) ∧
      w'.gpr .lr = w'.mem.readW (sa w.sp (4 * m + 4)) 32 := by
  have h₁ : 4 * m < 4096 := by omega
  have h₂ : 4 * m + 4 < 4096 := by omega
  simp only [execBlock, isa, exec, himm, h₁, h₂, ite_true, Option.map_some, addrs, State.store32,
    State.load32]
  simp [State.setReg, hr12, hw, hr]
  intro q hq; simp [hq]

/-- The addresses `setArgs bytes m` accesses, from `sp`. -/
def setArgsTrace (bytes : Nat) (sp : BitVec 32) (m : Nat) : List Leak :=
  [.addr (sa sp (4 * m + 4))] ++ copyTrace bytes sp m ++ [.addr (sa sp (4 * m)), .addr (sa sp (4 * m + 4))]

/-- The state after `setArgs bytes m` from `u`, if it runs. -/
def setArgsState (bytes m : Nat) (u : State) : State :=
  ((execBlock isa (setArgs bytes m) u).map Prod.fst).getD u

/-- `setArgs`: the stack argument slots copied into the frame, the buffer's
address after them; nothing else written but the saved `lr`, and only `r12`
changed. -/
theorem setArgs_run {bytes m : Nat} {u : State}
    (hfit : u.sp.toNat + bytes + 4 * m ≤ 2 ^ 32) (hb : 4 * m + 8 ≤ bytes) (himm : 4 * m + 8 < 256)
    (ho : bytes + 4 * m ≤ 4096)
    (hr : ∀ j < m, InRegions (u.rd ++ u.wr) (sa u.sp (bytes + 4 * j)) 4)
    (hfr : ⟨State.addr u.sp, bytes⟩ ∈ u.wr) :
    execBlock isa (setArgs bytes m) u = some (setArgsState bytes m u, setArgsTrace bytes u.sp m) ∧
      (setArgsState bytes m u).rd = u.rd ∧ (setArgsState bytes m u).wr = u.wr ∧
      (setArgsState bytes m u).sp = u.sp ∧
      (∀ q, q ≠ .r12 → (setArgsState bytes m u).gpr q = u.gpr q) ∧
      Frame [⟨State.addr u.sp, 4 * m + 8⟩] u.mem (setArgsState bytes m u).mem ∧
      (∀ j < m, (setArgsState bytes m u).mem.readW (sa u.sp (4 * j)) 32 =
        u.mem.readW (sa u.sp (bytes + 4 * j)) 32) ∧
      (setArgsState bytes m u).mem.readW (sa u.sp (4 * m)) 32 = u.sp + BitVec.ofNat 32 (4 * m + 8) := by
  have hA : ∀ d, u.sp.toNat + d < 2 ^ 32 → sa u.sp d = State.addr u.sp + BitVec.ofNat 64 d :=
    fun d hd => sa_eq hd
  have hW : ∀ d, d + 4 ≤ bytes → InRegions u.wr (sa u.sp d) 4 := fun d hd =>
    ⟨_, hfr, by rw [hA d (by omega)]; exact Offset.contains_base _ hd (by omega)⟩
  have hh := head_run (u := u) (m := m) (by omega) (hW _ (by omega))
  have hc := copies_run (bytes := bytes) (w := savedState m u) (savedState_r12 m u) m ho
    (fun j hj => by simpa using hr j hj) (fun j hj => by simpa using hW (4 * j) (by omega))
  obtain ⟨f, hv⟩ := copiedState_mem (bytes := bytes) (w := savedState m u) m (by simpa using hfit)
    (by omega)
  simp only [savedState_sp] at f hv
  obtain ⟨w', ht, hrd, hwr, hsp, hg, hm, hlr⟩ := tail_run (m := m)
    (w := copiedState bytes (savedState m u) m)
    (by rw [copiedState_gpr _ _ (by decide), savedState_r12, copiedState_sp, savedState_sp]) himm
    (by simpa using hW (4 * m) (by omega))
    (by
      simp only [copiedState_rd, copiedState_wr, savedState_rd, savedState_wr, copiedState_sp,
        savedState_sp]
      exact ⟨_, List.mem_append_right _ hfr, by
        rw [hA _ (by omega)]; exact Offset.contains_base _ (by omega) (by omega)⟩)
  simp only [copiedState_sp, savedState_sp, copiedState_rd, copiedState_wr, savedState_rd,
    savedState_wr] at hrd hwr hsp hm hlr
  have hrun : execBlock isa (setArgs bytes m) u = some (w', setArgsTrace bytes u.sp m) := by
    rw [setArgs, execBlock_append, execBlock_append, hh]
    simp only [Option.bind_some, Option.map_some, hc, savedState_sp]
    rw [ht]
    simp only [Option.map_some, setArgsTrace, List.singleton_append, copiedState_sp, savedState_sp]
  have hst : setArgsState bytes m u = w' := by simp [setArgsState, hrun]
  rw [hst]
  -- The slots, by offset from `sp`.
  have hR : ∀ d, d + 4 ≤ 4 * m + 8 →
      (⟨State.addr u.sp, 4 * m + 8⟩ : Region).Contains (sa u.sp d) 4 := fun d hd => by
    rw [hA d (by omega)]; exact Offset.contains_base _ hd (by omega)
  have hsep : ∀ d e, d + 4 ≤ e ∨ e + 4 ≤ d → u.sp.toNat + d < 2 ^ 32 → u.sp.toNat + e < 2 ^ 32 →
      Mem.Sep (sa u.sp d) (32 / 8) (sa u.sp e) (32 / 8) := fun d e h hd he => by
    rw [hA d hd, hA e he]; exact Offset.sep _ h (by omega) (by omega)
  -- The saved `lr` is where `setArgs` left it.
  have hsaved : w'.gpr .lr = u.gpr .lr := by
    rw [hlr, hm, Mem.readW_writeW_sep (hsep _ _ (by omega) (by omega) (by omega)) (by decide)]
    rw [f.readW (r := ⟨sa u.sp (4 * m + 4), 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact Mem.readW_writeW_self32 _ _ _
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hA _ (by omega)]
      exact Offset.disjoint_base _ (by omega) (by omega)
  have f₀ : Frame [⟨State.addr u.sp, 4 * m + 8⟩] u.mem (savedState m u).mem :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hR _ (by omega))
  have f₁ : Frame [⟨State.addr u.sp, 4 * m + 8⟩] u.mem (copiedState bytes (savedState m u) m).mem :=
    f₀.trans (Frame.sub f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
  refine ⟨hrun, by rw [hrd], by rw [hwr], hsp, fun q hq => ?_, ?_, fun j hj => ?_, ?_⟩
  · by_cases hql : q = .lr
    · subst hql; exact hsaved
    · rw [hg q hql, copiedState_gpr _ _ hql, savedState_gpr _ _ hq]
  · rw [hm]; exact f₁.writeW (List.mem_singleton_self _) _ (hR _ (by omega))
  · rw [hm, Mem.readW_writeW_sep (hsep _ _ (by omega) (by omega) (by omega)) (by decide), hv j hj]
    show (u.mem.writeW (sa u.sp (4 * m + 4)) (u.gpr .lr)).readW _ 32 = _
    rw [Mem.readW_writeW_sep (hsep _ _ (by omega) (by omega) (by omega)) (by decide)]
  · rw [hm, Mem.readW_writeW_self32]

/-! ## The run from `narrow` -/

/-- `sp - b + d` is `sp - (b - d)`, in 64 bits, for addresses that do not wrap. -/
theorem sa_sub {sp : BitVec 32} {b d : Nat} (hd : d ≤ b) (hb : b ≤ sp.toNat) :
    sa (sp - BitVec.ofNat 32 b) d = State.addr sp - BitVec.ofNat 64 (b - d) := by
  show State.addr (sp - BitVec.ofNat 32 b + BitVec.ofNat 32 d) = _
  rw [show sp - BitVec.ofNat 32 b + BitVec.ofNat 32 d = sp - BitVec.ofNat 32 (b - d) by
    rw [Offset.sub_ofNat_eq sp (show b - d ≤ b by omega), Nat.sub_sub_self hd]]
  exact addr_sub' (by omega)

theorem toNat_sub64 {a : Addr} {k : Nat} (h : k ≤ a.toNat) :
    (a - BitVec.ofNat 64 k).toNat = a.toNat - k := by
  have := a.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
    show 2 ^ 64 - k + a.toNat = (a.toNat - k) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem below_disjoint (p : Addr) (c : Nat) {a n b k : Nat} (ha : a ≤ c) (hb : b ≤ c)
    (h : c - a + n ≤ c - b ∨ c - b + k ≤ c - a) (hn : c - a + n ≤ 2 ^ 64) (hk : c - b + k ≤ 2 ^ 64) :
    Region.Disjoint ⟨p - BitVec.ofNat 64 a, n⟩ ⟨p - BitVec.ofNat 64 b, k⟩ := fun x h₁ h₂ =>
  Offset.sep_below p c ha hb h hn hk x (by simp only [Region.Contains] at h₁; omega)
    (by simp only [Region.Contains] at h₂; omega)

/-- The state after the push of `withStackScratch`'s frame. -/
def allocState (bytes : Nat) (s : State) : State :=
  { s with sp := s.sp - BitVec.ofNat 32 bytes,
           wr := ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr }

@[simp] theorem allocState_sp (bytes : Nat) (s : State) :
    (allocState bytes s).sp = s.sp - BitVec.ofNat 32 bytes := rfl
@[simp] theorem allocState_mem (bytes : Nat) (s : State) : (allocState bytes s).mem = s.mem := rfl
@[simp] theorem allocState_rd (bytes : Nat) (s : State) : (allocState bytes s).rd = s.rd := rfl
@[simp] theorem allocState_wr (bytes : Nat) (s : State) :
    (allocState bytes s).wr = ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr := rfl
@[simp] theorem allocState_gpr (bytes : Nat) (s : State) : (allocState bytes s).gpr = s.gpr := rfl

/-- The regions of the contract with the buffer, from the state after
`setArgs`: the buffers, the buffer, and the stack arguments in the frame. -/
def oldRegions (sig : Sig) (e : Elem) (n bytes m : Nat) (s : State) : List (Region × Bool) :=
  Sig.bufs sig.params (armArgs sig s) ++
    [(⟨sa (s.sp - BitVec.ofNat 32 bytes) (4 * m + 8), n * e.size⟩, true),
      (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), 4 * m + 4⟩, false)]

/-- The state the code runs from, with the permissions of the contract with
the buffer: the state after the frame's push and `setArgs`, which may read
and write what the contract with the buffer lets it. -/
def narrow (sig : Sig) (e : Elem) (n bytes m : Nat) (s : State) : State :=
  (setArgsState bytes m (allocState bytes s)).withRegions
    (((oldRegions sig e n bytes m s).filter (!·.2)).map (·.1))
    (((oldRegions sig e n bytes m s).filter (·.2)).map (·.1))

theorem narrow_mem (sig : Sig) (e : Elem) (n bytes m : Nat) (s : State) :
    (narrow sig e n bytes m s).mem = (setArgsState bytes m (allocState bytes s)).mem :=
  State.withRegions_mem _ _ _

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes m : Nat}

/-- The sizes `withStackScratch` needs: the frame holds the copies, the
buffer's address, the saved `lr` and the buffer; the offsets are encodable. -/
abbrev Fits (m bytes : Nat) (e : Elem) (n : Nat) : Prop :=
  4 * m + 8 + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 8 = 0 ∧
    encodable (BitVec.ofNat 32 bytes) = true ∧ 4 * m + 8 < 256 ∧ bytes + 4 * m ≤ 4096

/-- What `setArgs` gives, from a state satisfying the contract without the
buffer. -/
theorem argsState_run {s : State} (hs : (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hN : nsaa sig = 4 * m) (hb : Fits m bytes e n) :
    let u := allocState bytes s
    execBlock isa (setArgs bytes m) u =
        some (setArgsState bytes m u, setArgsTrace bytes u.sp m) ∧
      (setArgsState bytes m u).rd = u.rd ∧ (setArgsState bytes m u).wr = u.wr ∧
      (setArgsState bytes m u).sp = u.sp ∧
      (∀ q, q ≠ .r12 → (setArgsState bytes m u).gpr q = s.gpr q) ∧
      Frame [⟨State.addr u.sp, 4 * m + 8⟩] s.mem (setArgsState bytes m u).mem ∧
      (∀ j < m, stackArg (setArgsState bytes m u) j = stackArg s j) ∧
      stackArg (setArgsState bytes m u) m = u.sp + BitVec.ofNat 32 (4 * m + 8) := by
  intro u
  obtain ⟨hb1, -, -, -, himm, ho⟩ := hb
  rw [pre_arm] at hs
  obtain ⟨⟨hst, hfit⟩, hrd, -, -, -, -, -⟩ := hs
  have hsb : bytes ≤ s.sp.toNat := by omega
  have hE : u.sp.toNat = s.sp.toNat - bytes := sub_toNat' hsb
  have hsrc : ∀ j, sa u.sp (bytes + 4 * j) = sa s.sp (4 * j) := fun j => by
    simp only [u, allocState_sp, sa]
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  -- The caller's stack arguments hold the sources.
  have hargs : ∀ j < m, InRegions (u.rd ++ u.wr) (sa u.sp (bytes + 4 * j)) 4 := fun j hj => by
    have hmem : (⟨stackArgAddr s 0, nsaa sig⟩, false) ∈ allRegions sig s := by
      simp [allRegions, argArea, show nsaa sig ≠ 0 by omega]
    refine ⟨⟨stackArgAddr s 0, nsaa sig⟩, List.mem_append_left _ ?_, ?_⟩
    · simp only [u, allocState_rd, hrd]
      exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
    · rw [hsrc, sa_eq (by omega), hN]
      show (⟨State.addr (s.sp + BitVec.ofNat 32 (4 * 0)), 4 * m⟩ : Region).Contains _ 4
      rw [show s.sp + BitVec.ofNat 32 (4 * 0) = s.sp by simp]
      exact Offset.contains_base _ (by omega) (by omega)
  obtain ⟨hrun, hrd', hwr', hsp', hg, hf, hv, hl⟩ := setArgs_run (bytes := bytes) (m := m) (u := u)
    (by rw [hE]; omega) (by omega) himm ho hargs (List.mem_cons_self ..)
  refine ⟨hrun, hrd', hwr', hsp', fun q hq => hg q hq, hf, fun j hj => ?_, ?_⟩
  · show (setArgsState bytes m u).mem.readW
      (State.addr ((setArgsState bytes m u).sp + BitVec.ofNat 32 (4 * j))) 32 = _
    rw [hsp']
    exact (hv j hj).trans (by rw [hsrc]; rfl)
  · show (setArgsState bytes m u).mem.readW
      (State.addr ((setArgsState bytes m u).sp + BitVec.ofNat 32 (4 * m))) 32 = _
    rw [hsp']
    exact hl

theorem armArgs_congr {s s' : State} (hloc : (locs sig).all (Loc.ok (4 * m)) = true)
    (hr : ∀ r ∈ argRegs, s'.gpr r = s.gpr r) (hs : ∀ i < m, stackArg s' i = stackArg s i) :
    (locs sig).map (Loc.val s') = armArgs sig s :=
  List.map_congr_left fun l hl =>
    Loc.val_congr hr (fun i hi => hs i (by omega)) l (List.all_eq_true.mp hloc l hl)

/-- What `narrow` keeps of `s`, and what it holds. -/
theorem narrow_facts (hcl : ScratchOnStack sig) (hN : nsaa sig = 4 * m)
    (hloc : (locs sig).all (Loc.ok (4 * m)) = true) (hb : Fits m bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) :
    (narrow sig e n bytes m s).sp = s.sp - BitVec.ofNat 32 bytes ∧
      (∀ q, q ≠ .r12 → (narrow sig e n bytes m s).gpr q = s.gpr q) ∧
      armArgs (sig.withScratch nm e n) (narrow sig e n bytes m s) =
        armArgs sig s ++ [sa (s.sp - BitVec.ofNat 32 bytes) (4 * m + 8)] ∧
      Frame [⟨State.addr (s.sp - BitVec.ofNat 32 bytes), 4 * m + 8⟩] s.mem (narrow sig e n bytes m s).mem := by
  obtain ⟨-, -, -, hsp', hg, hf, hv, hl⟩ := argsState_run hs hN hb
  refine ⟨hsp', hg, ?_, by rw [narrow_mem]; exact hf⟩
  rw [armArgs_withScratch hcl, hN, show 4 * m / 4 = m by omega]
  refine congr (congrArg HAppend.hAppend (armArgs_congr hloc (fun r hr => hg r ?_) ?_)) ?_
  · intro h; subst h; simp [argRegs] at hr
  · intro i hi
    exact (stackArg_withRegions _ _ _ i).trans (hv i hi)
  · rw [show stackArg (narrow sig e n bytes m s) m = stackArg (setArgsState bytes m (allocState bytes s)) m
      from stackArg_withRegions _ _ _ m, hl]
    rfl

theorem stackBelow_sub (E : Addr) (bytes stack : Nat) :
    stackBelow (E - BitVec.ofNat 64 bytes) stack =
      if stack = 0 then [] else [⟨E - BitVec.ofNat 64 (bytes + stack), stack⟩] := by
  cases stack with
  | zero => rfl
  | succ k => simp [stackBelow, BitVec.sub_sub, BitVec.ofNat_add]

/-- The buffers lie outside the frame: `narrow`'s memory is `s`'s there. -/
theorem narrow_agree (hcl : ScratchOnStack sig) (hN : nsaa sig = 4 * m)
    (hloc : (locs sig).all (Loc.ok (4 * m)) = true) (hb : Fits m bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) :
    ∀ b ∈ Sig.bufs sig.params (armArgs sig s), ∀ x, b.1.Contains x 1 →
      (narrow sig e n bytes m s).mem x = s.mem x := by
  obtain ⟨-, -, -, hf⟩ := narrow_facts (nm := "") hcl hN hloc hb hs
  obtain ⟨hb1, -⟩ := hb
  rw [pre_arm] at hs
  obtain ⟨⟨hst, -⟩, -, -, -, hres, -, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by omega
  have hbelow : (⟨State.addr s.sp - BitVec.ofNat 64 (stack + bytes), stack + bytes⟩ : Region) ∈
      stackBelow (State.addr s.sp) (stack + bytes) := by
    rw [show stack + bytes = (stack + bytes - 1) + 1 by omega]; simp [stackBelow]
  intro b hb x hx
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  rw [addr_sub' (by omega)] at hc
  exact (Region.Disjoint.symm (hres _ hbelow b (List.mem_append_left _ hb))).sub_right
    (Offset.sub_below _ (by omega) (by omega)) x hx hc

/-- The precondition of the contract without the buffer gives the one with it
in `narrow`, if the precondition reads memory only within the buffers. -/
theorem narrow_pre (hcl : ScratchOnStack sig) (hN : nsaa sig = 4 * m)
    (hloc : (locs sig).all (Loc.ok (4 * m)) = true) (hb : Fits m bytes e n)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) :
    (Sig.scratchContract abi sig nm e n pre post wa stack).pre (narrow sig e n bytes m s) := by
  obtain ⟨hsp₂, -, hst', -⟩ := narrow_facts (nm := nm) hcl hN hloc hb hs
  have hag := narrow_agree hcl hN hloc hb hs
  obtain ⟨hb1, -⟩ := hb
  rw [pre_arm] at hs
  obtain ⟨⟨hst, hfit⟩, hrd, hwr, hpw, hres, hnw, hpr⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by omega
  have hlt := s.sp.isLt
  -- Addresses as offsets below `E`.
  have hsp : State.addr (s.sp - BitVec.ofNat 32 bytes) = State.addr s.sp - BitVec.ofNat 64 bytes :=
    addr_sub' (by omega)
  have hscr : sa (s.sp - BitVec.ofNat 32 bytes) (4 * m + 8) =
      State.addr s.sp - BitVec.ofNat 64 (bytes - (4 * m + 8)) := sa_sub (by omega) (by omega)
  have hE : (State.addr s.sp).toNat = s.sp.toNat := by
    simp only [State.addr, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  have hbelow : (⟨State.addr s.sp - BitVec.ofNat 64 (stack + bytes), stack + bytes⟩ : Region) ∈
      stackBelow (State.addr s.sp) (stack + bytes) := by
    rw [show stack + bytes = (stack + bytes - 1) + 1 by omega]; simp [stackBelow]
  -- The buffers lie outside the frame.
  have hout : ∀ a ∈ Sig.bufs sig.params (armArgs sig s), ∀ {x k : Nat}, x ≤ stack + bytes →
      stack + bytes - x + k ≤ stack + bytes →
      a.1.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 x, k⟩ := fun a ha _ _ hx hk =>
    (Region.Disjoint.symm (hres _ hbelow a (List.mem_append_left _ ha))).sub_right
      (Offset.sub_below _ hx hk)
  -- The arguments of the contract with the buffer.
  have hlen := armArgs_length sig s
  have harg0 : stackArgAddr (narrow sig e n bytes m s) 0 = State.addr (s.sp - BitVec.ofNat 32 bytes) := by
    show State.addr ((narrow sig e n bytes m s).sp + BitVec.ofNat 32 (4 * 0)) = _
    rw [hsp₂]; simp
  have hbufs : Sig.bufs (sig.withScratch nm e n).params
      (armArgs sig s ++ [sa (s.sp - BitVec.ofNat 32 bytes) (4 * m + 8)]) =
      Sig.bufs sig.params (armArgs sig s) ++
        [(⟨sa (s.sp - BitVec.ofNat 32 bytes) (4 * m + 8), n * e.size⟩, true)] :=
    Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _ hlen
  have hall : allRegions (sig.withScratch nm e n) (narrow sig e n bytes m s) =
      oldRegions sig e n bytes m s := by
    rw [allRegions, hst', argArea, nsaa_withScratch hcl, harg0, hN, hbufs]
    simp only [show 4 * m + 4 ≠ 0 by omega, ite_false, oldRegions, List.append_assoc,
      List.singleton_append]
  refine (pre_arm (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)).mpr ?_
  rw [hall, hsp₂, nsaa_withScratch hcl, hst', hN]
  refine ⟨⟨.inr ?_, ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [sub_toNat' (by omega)]; omega
  · rw [sub_toNat' (by omega)]; omega
  · -- Pairwise disjoint.
    simp only [oldRegions]
    rw [List.pairwise_append]
    refine ⟨List.Pairwise.sublist (List.sublist_append_left _ _) hpw, ?_, fun a ha b hb _ => ?_⟩
    · simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
        List.Pairwise.nil, and_true, Bool.true_or, forall_const]
      rw [hscr, hsp]
      exact ⟨below_disjoint _ (stack + bytes) (a := bytes - (4 * m + 8)) (n := n * e.size)
        (b := bytes) (k := 4 * m + 4) (by omega) (by omega) (.inr (by omega)) (by omega) (by omega),
        fun _ h => h.elim⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · rw [hscr]; exact hout a ha (by omega) (by omega)
      · rw [hsp]; exact hout a ha (by omega) (by omega)
  · -- The reserved stack: the stack below the frame.
    intro r hr a ha
    rw [hsp, stackBelow_sub] at hr
    by_cases h0 : stack = 0
    · simp [h0] at hr
    simp only [h0, ite_false, List.mem_singleton] at hr; subst hr
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · exact Region.Disjoint.symm (hout a ha (by omega) (by omega))
    · rw [hscr]
      exact below_disjoint _ (stack + bytes) (a := bytes + stack) (n := stack)
        (b := bytes - (4 * m + 8)) (k := n * e.size) (by omega) (by omega) (.inl (by omega))
        (by omega) (by omega)
    · rw [hsp]
      exact below_disjoint _ (stack + bytes) (a := bytes + stack) (n := stack) (b := bytes)
        (k := 4 * m + 4) (by omega) (by omega) (.inl (by omega)) (by omega) (by omega)
  · -- No buffer wraps around.
    intro a ha
    rw [hbufs] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hnw a ha
    · simp only [List.mem_singleton] at ha; subst ha
      show (sa (s.sp - BitVec.ofNat 32 bytes) (4 * m + 8)).toNat + n * e.size ≤ 2 ^ 32
      rw [hscr, toNat_sub64 (by omega), hE]
      omega
  · -- The precondition, which reads only the buffers.
    refine Eq.mpr (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params pre _ _ hlen) _) ?_
    exact hpre _ _ _ hlen (fun b hb x hx => (hag b hb x hx).symm) hpr

/-- The public data of the contract without the buffer gives that of the
one with it in `narrow`: the buffer's address is the stack pointer's. -/
theorem narrow_pub (hcl : ScratchOnStack sig) (hN : nsaa sig = 4 * m)
    (hloc : (locs sig).all (Loc.ok (4 * m)) = true) (hb : Fits m bytes e n) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + bytes)).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + bytes)).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + bytes)).pub s₁ s₂) :
    (Sig.scratchContract abi sig nm e n pre post wa stack).pub (narrow sig e n bytes m s₁)
      (narrow sig e n bytes m s₂) := by
  rw [pub_arm] at hp
  obtain ⟨hsp, hpa⟩ := hp
  obtain ⟨e₁, -, a₁, -⟩ := narrow_facts (nm := nm) hcl hN hloc hb h₁
  obtain ⟨e₂, -, a₂, -⟩ := narrow_facts (nm := nm) hcl hN hloc hb h₂
  refine (pub_arm (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)).mpr ?_
  rw [e₁, e₂, a₁, a₂, hsp]
  refine ⟨rfl, fun i hi => ?_⟩
  have l₁ := armArgs_length sig s₁
  have l₂ := armArgs_length sig s₂
  have lp := Sig.pubs_length sig.params abi.ptrBits
  have lw : (widths sig).length = (sig.params.flatMap fun p => p.2.words abi.ptrBits).length := by
    rw [widths, List.length_map]; rfl
  have hps : ((sig.withScratch nm e n).params.flatMap (·.2.pubs)) =
      sig.params.flatMap (·.2.pubs) ++ [true] := by
    simp [Sig.withScratch, Param.pubs]
  rw [hps] at hi
  rw [widths_withScratch]
  by_cases hik : i < (sig.params.flatMap fun p => p.2.words abi.ptrBits).length
  · have hw : (widths sig ++ ([32] : List Nat)).getD i 64 = (widths sig).getD i 64 := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [lw]; exact hik)]
    rw [hw]
    simp only [List.getD_eq_getElem?_getD] at hi hpa ⊢
    rw [List.getElem?_append_left (by rw [l₁]; exact hik),
      List.getElem?_append_left (by rw [l₂]; exact hik)]
    rw [List.getElem?_append_left (by rw [lp]; exact hik)] at hi
    exact hpa i hi
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), l₁, l₂]

/-- The state after the pop of `withStackScratch`'s frame, from the state
`s₃` its code ends in when it starts in `s`. -/
def popState (bytes : Nat) (s s₃ : State) : State :=
  { s₃.withRegions s.rd (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) with
    sp := s.sp, wr := s.wr }

/-- A run of the code from `narrow s` is a run of `withStackScratch` from
`s`, after `setArgs`'s accesses, which keeps what the calling convention
requires, and whose memory and registers are those of the code's run. -/
theorem withStackScratch_run {c : Prog isa} (hcl : ScratchOnStack sig) (hN : nsaa sig = 4 * m)
    (hloc : (locs sig).all (Loc.ok (4 * m)) = true) (hb : Fits m bytes e n) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrow sig e n bytes m s) t s₃) (ha : abiPreserved (narrow sig e n bytes m s) s₃) :
    Exec isa (withStackScratch bytes m c) s
        (setArgsTrace bytes (s.sp - BitVec.ofNat 32 bytes) m ++ t) (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
  obtain ⟨hrun, hrd', hwr', -, -, -, -, -⟩ := argsState_run hs hN hb
  obtain ⟨hsp₂, hg, -, -⟩ := narrow_facts (nm := "") hcl hN hloc hb hs
  obtain ⟨hb1, hb2, hb3, hb4, -⟩ := hb
  rw [pre_arm] at hs
  obtain ⟨⟨hst, -⟩, hrd, hwr, -, -, -, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by omega
  have hsp : State.addr (s.sp - BitVec.ofNat 32 bytes) = State.addr s.sp - BitVec.ofNat 64 bytes :=
    addr_sub' (by omega)
  have hscr : sa (s.sp - BitVec.ofNat 32 bytes) (4 * m + 8) =
      State.addr s.sp - BitVec.ofNat 64 (bytes - (4 * m + 8)) := sa_sub (by omega) (by omega)
  -- The frame's push.
  have hpush : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push]
    exact ite_eq_left ⟨by omega, hb2, hb3, hb4, by omega⟩
  -- The regions of `narrow`: the buffers, and the frame's buffer and arguments.
  have hF : ∀ {a k : Nat}, a ≤ bytes → bytes - a + k ≤ bytes →
      Covers [⟨State.addr s.sp - BitVec.ofNat 64 a, k⟩]
        (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) := fun ha hk =>
    Covers.one ⟨_, List.mem_cons_self .., by
      rw [hsp]; exact Offset.contains_below _ ha hk (by omega)⟩
  have hbufR : ∀ a ∈ Sig.bufs sig.params (armArgs sig s), a.2 = false → a.1 ∈ s.rd := fun a ha h => by
    rw [hrd]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, by simp [h]⟩, rfl⟩
  have hbufW : ∀ a ∈ Sig.bufs sig.params (armArgs sig s), a.2 = true → a.1 ∈ s.wr := fun a ha h => by
    rw [hwr]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, h⟩, rfl⟩
  have hcovW : Covers (((oldRegions sig e n bytes m s).filter (·.2)).map (·.1))
      (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · exact Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ (hbufW a ha hf')
    · rw [hscr]; exact hF (by omega) (by omega)
    · simp at hf'
  have hcovR : Covers (((oldRegions sig e n bytes m s).filter (!·.2)).map (·.1))
      (s.rd ++ ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha (by simpa using hf'))
    · simp at hf'
    · exact Covers.right (by simpa only [hsp] using hF (a := bytes) (k := 4 * m + 4) (by omega) (by omega))
  have hw := Exec.widen he (rd := s.rd)
    (wr := ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr)
    (Covers.append_left hcovR (Covers.right hcovW)) hcovW
  rw [show (narrow sig e n bytes m s).withRegions s.rd
      (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) =
      setArgsState bytes m (allocState bytes s) by
    rw [narrow, State.withRegions_withRegions, ← allocState_rd bytes s, ← hrd',
      show ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr = (allocState bytes s).wr
        from rfl, ← hwr', State.withRegions_self]] at hw
  -- The pop.
  have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 32 bytes := ha.2.trans hsp₂
  have hpop : isa.pop (.free bytes) (allocState bytes s)
      (s₃.withRegions s.rd (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr)) =
      some (popState bytes s s₃) := by
    simp only [isa, pop, State.withRegions_sp, State.withRegions_wr, allocState_sp, allocState_wr,
      hsp₃, List.head?_cons, show 0 < bytes by omega, hb2, hb3, hb4, and_self, ite_true,
      List.tail_cons, BitVec.sub_add_cancel]
    rfl
  have hex := Exec.frame hpush (Exec.seq (Exec.block hrun) hw) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil, allocState_sp] at hex
  refine ⟨hex, ⟨fun q hq => ?_, rfl⟩, rfl, rfl⟩
  have hq12 : q ≠ .r12 := fun h => by subst h; simp [preserved] at hq
  show s₃.gpr q = s.gpr q
  rw [ha.1 q hq, hg q hq12]

/-- Code verified for a function whose last argument, on the stack, is a
scratch buffer of `n` elements `e`, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack (`withStackScratch`), if its precondition and
postcondition read memory only within the function's buffers (`hpre`,
`hpost`). The other arguments are in `r0`–`r3` and the first `4m` bytes of
stack (`hcl`, `hN`, `hloc`). -/
theorem Verified.stackScratch {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hcl : ScratchOnStack sig) (hN : nsaa sig = 4 * m)
    (hloc : (locs sig).all (Loc.ok (4 * m)) = true) (hb : Fits m bytes e n)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s) :
    Verified target (withStackScratch bytes m c) (sig.contract abi pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  -- Every run is `setArgs`, then the code's run from `narrow`.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃,
      Exec isa c (narrow sig e n bytes m s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrow sig e n bytes m s) s₃ ∧
      Exec isa (withStackScratch bytes m c) s
        (setArgsTrace bytes (s.sp - BitVec.ofNat 32 bytes) m ++ t) (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_pre hcl hN hloc hb hpre hs)
    exact ⟨t, s₃, he, hq, withStackScratch_run hcl hN hloc hb hs he ha⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, hg⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_arm]
    have hq' := (post_arm (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)).mp hq
    obtain ⟨-, -, hargs, -⟩ := narrow_facts (nm := nm) hcl hN hloc hb hs
    rw [hargs] at hq'
    rw [hm, hg]
    have hq'' := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (armArgs_length sig s)) _) s₃.mem) _) hq'
    exact hpost _ _ _ _ _ (armArgs_length sig s) (narrow_agree hcl hN hloc hb hs) hq''
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, (pub_arm.mp hp).1,
      hct _ _ _ _ _ _ (narrow_pre hcl hN hloc hb hpre h₁) (narrow_pre hcl hN hloc hb hpre h₂)
        (narrow_pub hcl hN hloc hb h₁ h₂ hp) f₁ f₂]

end

end VG.Arm
