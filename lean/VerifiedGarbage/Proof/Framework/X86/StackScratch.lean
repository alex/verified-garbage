import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.X86.Target

/-!
# A scratch buffer on the stack (x86)

`Verified.stackScratch`: code verified for a function whose last argument is
a scratch buffer (its contract `Sig.scratchContract`) runs as a function
without that argument when `withStackScratch` allocates the buffer in a frame
on the stack, with `bytes` more bytes of stack. Every argument is on the
stack, so the frame holds what the code expects at and above `esp` on entry:
a word for its return address, a copy of the arguments, then the buffer's
address (`setArgs`). The code runs from the state after the frame's push and
`setArgs`, with the permissions of the contract with the argument
(`narrow`), and its run there is its run from that state (`Exec.widen`).

The copies are memory the code reads on entry, which the contract without the
argument says nothing of: the precondition and postcondition must read memory
only within the function's buffers (`hpre`, `hpost`), which the frame lies
outside of.
-/

namespace VG.X86

open VG.Impl.StackScratch.X86

theorem abi_ptrBits : abi.ptrBits = 32 := rfl

/-- The widths of the arguments of `sig`. -/
def widths (sig : Sig) : List Nat := (sig.words abi.ptrBits).map (·.bits abi.ptrBits)

/-- The number of four-byte argument slots of `sig`. -/
def slots (sig : Sig) : Nat := ((widths sig).map (· / 32)).sum

/-- The arguments of `sig`, from the stack. -/
def stackArgs (sig : Sig) (s : State) : List (BitVec 64) :=
  ((widths sig).zip (argSlots (widths sig) 0)).map fun (w, i) => argVal s w i

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

theorem argSlots_length : ∀ (ws : List Nat) (i : Nat), (argSlots ws i).length = ws.length
  | [], _ => rfl
  | _ :: ws, i => by simp [argSlots, argSlots_length ws]

theorem argSlots_append (w : Nat) : ∀ (ws : List Nat) (i : Nat),
    argSlots (ws ++ [w]) i = argSlots ws i ++ [i + (ws.map (· / 32)).sum]
  | [], i => by simp [argSlots]
  | w' :: ws, i => by
    simp only [List.cons_append, argSlots, argSlots_append w ws, List.map_cons, List.sum_cons,
      Nat.add_assoc]

/-- Each argument's slots are among the first `(ws.map (· / 32)).sum`. -/
theorem argSlots_lt : ∀ (ws : List Nat) (i : Nat), ∀ p ∈ ws.zip (argSlots ws i),
    p.2 + p.1 / 32 ≤ i + (ws.map (· / 32)).sum
  | [], _, _, h => by simp at h
  | w :: ws, i, p, h => by
    simp only [argSlots, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · simp only [List.map_cons, List.sum_cons]; omega
    · have := argSlots_lt ws (i + w / 32) p h
      simp only [List.map_cons, List.sum_cons]; omega

theorem widths_withScratch (sig : Sig) (nm : String) (e : Elem) (n : Nat) :
    widths (sig.withScratch nm e n) = widths sig ++ [32] := by
  rw [widths, widths, Sig.words_withScratch, List.map_append]
  rfl

theorem slots_withScratch (sig : Sig) (nm : String) (e : Elem) (n : Nat) :
    slots (sig.withScratch nm e n) = slots sig + 1 := by
  rw [slots, slots, widths_withScratch, List.map_append, List.sum_append]
  rfl

/-- The arguments of the function with the buffer, from slots that hold
those of the function without it, and the buffer's address. -/
theorem stackArgs_withScratch (sig : Sig) (nm : String) (e : Elem) (n : Nat) {s s₀ : State}
    (h : ∀ j < slots sig, arg s j = arg s₀ j) :
    stackArgs (sig.withScratch nm e n) s =
      stackArgs sig s₀ ++ [(arg s (slots sig)).setWidth 64] := by
  have e₁ : (widths sig ++ [32]).zip (argSlots (widths sig ++ [32]) 0) =
      (widths sig).zip (argSlots (widths sig) 0) ++ [(32, slots sig)] := by
    rw [argSlots_append, List.zip_append (by rw [argSlots_length])]
    simp only [List.zip_cons_cons, List.zip_nil_left, Nat.zero_add, slots]
  unfold stackArgs
  rw [widths_withScratch, e₁, List.map_append]
  refine congr (congrArg HAppend.hAppend ?_) ?_
  · refine List.map_congr_left fun p hp => ?_
    have hl := argSlots_lt (widths sig) 0 p hp
    have hw := widths_mem sig p.1 (List.of_mem_zip hp).1
    simp only [Nat.zero_add] at hl
    simp only [argVal]
    rcases hw with hw | hw <;> rw [hw] at hl
    · simp only [hw, show (32 : Nat) ≠ 64 by decide, ite_false]
      rw [h _ (by simp only [slots]; omega)]
    · simp only [hw, ite_true]
      rw [h _ (by simp only [slots]; omega), h _ (by simp only [slots]; omega)]
  · simp only [List.map_cons, List.map_nil, argVal, show (32 : Nat) ≠ 64 by decide, ite_false]

/-- The buffers and the argument area of a function with signature `sig`
(whose contract may write its arguments if `wa`), and whether each is
writable. -/
def allRegions (sig : Sig) (wa : Bool) (s : State) : List (Region × Bool) :=
  Sig.bufs sig.params (stackArgs sig s) ++
    (if slots sig = 0 then [] else [(⟨argAddr s 0, 4 * slots sig⟩, wa)])

theorem args_stack (sig : Sig) :
    abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) = some (stackArgs sig) := by
  have hw : ((sig.words 32).map (fun x => ArgWord.bits 32 x)).all
      (fun w => decide (w = 32 ∨ w = 64)) = true :=
    List.all_eq_true.mpr fun w h => decide_eq_true (widths_mem sig w h)
  simp only [abi, hw, ite_true]
  rfl

theorem argArea_stack (sig : Sig) (wa : Bool) (s : State) :
    (abi.argArea ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) s).map
        (fun (r, w) => (r, w && wa)) =
      if slots sig = 0 then [] else [(⟨argAddr s 0, 4 * slots sig⟩, wa)] := by
  show (if argBytes (widths sig) = 0 then [] else
    [((⟨argAddr s 0, argBytes (widths sig)⟩ : Region), true)]).map (fun (r, w) => (r, w && wa)) = _
  rw [show argBytes (widths sig) = 4 * slots sig from rfl]
  by_cases h : slots sig = 0
  · simp [h]
  · have : 4 * slots sig ≠ 0 := by omega
    simp [h, this]

/-- The precondition of a contract, with every argument on the stack. -/
theorem pre_stack {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State} :
    (sig.contract abi pre post wa stack leak).pre s ↔
      (stack ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + 4 * slots sig ≤ 2 ^ 32) ∧
      s.rd = ((allRegions sig wa s).filter (!·.2)).map (·.1) ∧
      s.wr = ((allRegions sig wa s).filter (·.2)).map (·.1) ∧
      (allRegions sig wa s).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) ∧
      (∀ r ∈ (⟨(s.gpr .esp).setWidth 64, 4⟩ :: stackBelow ((s.gpr .esp).setWidth 64) stack :
          List Region), ∀ a ∈ allRegions sig wa s, r.Disjoint a.1) ∧
      (∀ a ∈ Sig.bufs sig.params (stackArgs sig s), a.1.base.toNat + a.1.len ≤ 2 ^ 32) ∧
      Curry.apply (sig.words abi.ptrBits) pre (stackArgs sig s) s.mem := by
  have hwf : abi.wf (widths sig) stack s ↔
      (stack ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + 4 * slots sig ≤ 2 ^ 32) := by
    cases stack <;> simp [abi, argBytes, slots]
  have hwf' : abi.wf ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) stack s ↔
      (stack ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + 4 * slots sig ≤ 2 ^ 32) := hwf
  simp only [Sig.contract]
  rw [args_stack]
  simp only [argArea_stack]
  rw [hwf']
  exact Iff.rfl

/-! ## Copying the arguments -/

/-- The state after `copyArg bytes j` from `u`. -/
def copyState (bytes j : Nat) (u : State) : State :=
  { u.setReg .eax (u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32) with
    mem := u.mem.writeW (addr (u.gpr .esp) (4 + 4 * j))
      (u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32) }

theorem copyArg_run {bytes j : Nat} {u : State}
    (hr : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 4)
    (hw : InRegions u.wr (addr (u.gpr .esp) (4 + 4 * j)) 4) :
    execBlock isa (copyArg bytes j) u = some (copyState bytes j u,
      [.addr (addr (u.gpr .esp) (bytes + 4 + 4 * j)), .addr (addr (u.gpr .esp) (4 + 4 * j))]) := by
  have hesp : (u.setReg .eax (u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32)).gpr .esp =
      u.gpr .esp := by simp [State.setReg]
  simp only [copyArg, execBlock, isa, exec, readSrc, State.load32, ea_mk, hr, ite_true,
    Option.map_some, addrs, srcAddrs, State.store32, hesp]
  simp [copyState, State.setReg, hw]

@[simp] theorem copyState_esp (bytes j : Nat) (u : State) : (copyState bytes j u).gpr .esp = u.gpr .esp := by
  simp [copyState, State.setReg]
@[simp] theorem copyState_rd (bytes j : Nat) (u : State) : (copyState bytes j u).rd = u.rd := rfl
@[simp] theorem copyState_wr (bytes j : Nat) (u : State) : (copyState bytes j u).wr = u.wr := rfl
theorem copyState_gpr (bytes j : Nat) (u : State) {q : Reg} (h : q ≠ .eax) :
    (copyState bytes j u).gpr q = u.gpr q := by
  simp [copyState, State.setReg, h]

/-- The state after copying the first `m` argument slots from `u`. -/
def copiedState (bytes : Nat) (u : State) : Nat → State
  | 0 => u
  | m + 1 => copyState bytes m (copiedState bytes u m)

@[simp] theorem copiedState_esp (bytes : Nat) (u : State) :
    ∀ m, (copiedState bytes u m).gpr .esp = u.gpr .esp
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_esp, copiedState_esp bytes u m]
@[simp] theorem copiedState_rd (bytes : Nat) (u : State) : ∀ m, (copiedState bytes u m).rd = u.rd
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_rd, copiedState_rd bytes u m]
@[simp] theorem copiedState_wr (bytes : Nat) (u : State) : ∀ m, (copiedState bytes u m).wr = u.wr
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_wr, copiedState_wr bytes u m]
theorem copiedState_gpr (bytes : Nat) (u : State) {q : Reg} (h : q ≠ .eax) :
    ∀ m, (copiedState bytes u m).gpr q = u.gpr q
  | 0 => rfl
  | m + 1 => by rw [copiedState, copyState_gpr _ _ _ h, copiedState_gpr bytes u h m]

/-- The addresses copying the first `m` slots accesses. -/
def copyTrace (bytes : Nat) (sp : BitVec 32) (m : Nat) : List Leak :=
  (List.range m).flatMap fun j => [.addr (addr sp (bytes + 4 + 4 * j)), .addr (addr sp (4 + 4 * j))]

theorem copies_run {bytes : Nat} {u : State} :
    ∀ m, (∀ j < m, InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 4) →
      (∀ j < m, InRegions u.wr (addr (u.gpr .esp) (4 + 4 * j)) 4) →
      execBlock isa ((List.range m).flatMap (copyArg bytes)) u =
        some (copiedState bytes u m, copyTrace bytes (u.gpr .esp) m)
  | 0, _, _ => rfl
  | m + 1, hr, hw => by
    rw [List.range_succ, List.flatMap_append, execBlock_append,
      copies_run m (fun j hj => hr j (by omega)) (fun j hj => hw j (by omega))]
    simp only [Option.bind_some, List.flatMap_singleton]
    rw [copyArg_run (by simpa using hr m (by omega)) (by simpa using hw m (by omega))]
    simp only [Option.map_some, copiedState, copiedState_esp, copyTrace, List.range_succ,
      List.flatMap_append, List.flatMap_singleton]

/-- Copying the first `m` slots writes only within the `m` destination slots
(from `esp + 4`), which then hold the source slots (from `esp + bytes + 4`). -/
theorem copiedState_mem {bytes : Nat} {u : State} :
    ∀ m, (u.gpr .esp).toNat + bytes + 4 + 4 * m ≤ 2 ^ 32 → 4 * m ≤ bytes →
      Frame [⟨(u.gpr .esp).setWidth 64 + 4, 4 * m⟩] u.mem (copiedState bytes u m).mem ∧
      ∀ j < m, (copiedState bytes u m).mem.readW (addr (u.gpr .esp) (4 + 4 * j)) 32 =
        u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32
  | 0, _, _ => ⟨Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | m + 1, hfit, hb => by
    obtain ⟨f, hv⟩ := copiedState_mem (bytes := bytes) (u := u) m (by omega) (by omega)
    have hA : ∀ d, d < 4 + bytes + 4 * (m + 1) → addr (u.gpr .esp) d =
        (u.gpr .esp).setWidth 64 + BitVec.ofNat 64 d := fun d hd => addr_eq (by omega)
    have hR : Region.Sub ⟨(u.gpr .esp).setWidth 64 + 4, 4 * m⟩
        ⟨(u.gpr .esp).setWidth 64 + 4, 4 * (m + 1)⟩ := Region.sub_prefix (by omega)
    have f' : Frame [⟨(u.gpr .esp).setWidth 64 + 4, 4 * (m + 1)⟩] u.mem (copiedState bytes u m).mem :=
      Frame.sub f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, hR⟩
    -- The source of slot `m` is above the first `m` destinations.
    have hsrc : (copiedState bytes u m).mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * m)) 32 =
        u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * m)) 32 := by
      rw [hA _ (by omega)]
      refine f.readW (r := ⟨(u.gpr .esp).setWidth 64 + BitVec.ofNat 64 (bytes + 4 + 4 * m), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (d := bytes + 4 + 4 * m) (n := 4) (e := 4) (k := 4 * m) (.inr (by omega))
        (by omega) (by omega)
    refine ⟨?_, fun j hj => ?_⟩
    · show Frame _ u.mem ((copiedState bytes u m).mem.writeW _ _)
      rw [copiedState_esp]
      refine f'.writeW (List.mem_singleton_self _) _ ?_
      rw [hA _ (by omega)]
      exact Offset.contains _ (d := 4 + 4 * m) (e := 4) (k := 4 * (m + 1)) (by omega) (by omega)
        (by omega)
    · show ((copiedState bytes u m).mem.writeW (addr ((copiedState bytes u m).gpr .esp) (4 + 4 * m))
          ((copiedState bytes u m).mem.readW
            (addr ((copiedState bytes u m).gpr .esp) (bytes + 4 + 4 * m)) 32)).readW _ 32 = _
      rw [copiedState_esp]
      rcases Nat.lt_or_ge j m with hj' | hj'
      · rw [Mem.readW_writeW_sep, hv j hj']
        · rw [hA _ (by omega), hA _ (by omega)]
          exact Offset.sep _ (d := 4 + 4 * j) (n := 4) (e := 4 + 4 * m) (k := 4) (by omega) (by omega)
            (by omega)
        · decide
      · obtain rfl : j = m := by omega
        rw [Mem.readW_writeW_self32, hsrc]

/-- `mov eax, esp; add eax, 8 + 4n; mov [esp + 4 + 4n], eax`: pass the buffer. -/
theorem tail_run {n : Nat} {w : State} (hw : InRegions w.wr (addr (w.gpr .esp) (4 + 4 * n)) 4) :
    ∃ w', execBlock isa [.mov .eax (.reg .esp), .alu .add .eax (.imm (BitVec.ofNat 32 (8 + 4 * n))),
        .store ⟨.esp, 4 + 4 * n⟩ .eax] w = some (w', [.addr (addr (w.gpr .esp) (4 + 4 * n))]) ∧
      w'.rd = w.rd ∧ w'.wr = w.wr ∧ (∀ q, q ≠ .eax → w'.gpr q = w.gpr q) ∧
      w'.mem = w.mem.writeW (addr (w.gpr .esp) (4 + 4 * n)) (w.gpr .esp + BitVec.ofNat 32 (8 + 4 * n)) := by
  simp only [execBlock, isa, exec, readSrc, Option.map_some, execAlu, Option.bind_some, addrs,
    srcAddrs, State.store32, ea_mk]
  simp [State.setReg, arithFlags, State.setFlags, hw]
  intro q hq; simp [hq]

/-- The addresses `setArgs bytes n` accesses, from `esp = sp`. -/
def setArgsTrace (bytes : Nat) (sp : BitVec 32) (n : Nat) : List Leak :=
  copyTrace bytes sp n ++ [.addr (addr sp (4 + 4 * n))]

/-- The state after `setArgs bytes n` from `u`, if it runs. -/
def setArgsState (bytes n : Nat) (u : State) : State :=
  ((execBlock isa (setArgs bytes n) u).map Prod.fst).getD u

/-- `setArgs`: the argument slots copied into the frame, the buffer's address
after them; nothing else written, and only `eax` changed. -/
theorem setArgs_run {bytes n : Nat} {u : State}
    (hfit : (u.gpr .esp).toNat + bytes + 4 + 4 * n ≤ 2 ^ 32) (hb : 4 * n + 4 ≤ bytes)
    (hr : ∀ j < n, InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 4)
    (hw : ∀ j ≤ n, InRegions u.wr (addr (u.gpr .esp) (4 + 4 * j)) 4) :
    execBlock isa (setArgs bytes n) u = some (setArgsState bytes n u, setArgsTrace bytes (u.gpr .esp) n) ∧
      (setArgsState bytes n u).rd = u.rd ∧ (setArgsState bytes n u).wr = u.wr ∧
      (∀ q, q ≠ .eax → (setArgsState bytes n u).gpr q = u.gpr q) ∧
      Frame [⟨(u.gpr .esp).setWidth 64 + 4, 4 * (n + 1)⟩] u.mem (setArgsState bytes n u).mem ∧
      (∀ j < n, (setArgsState bytes n u).mem.readW (addr (u.gpr .esp) (4 + 4 * j)) 32 =
        u.mem.readW (addr (u.gpr .esp) (bytes + 4 + 4 * j)) 32) ∧
      (setArgsState bytes n u).mem.readW (addr (u.gpr .esp) (4 + 4 * n)) 32 =
        u.gpr .esp + BitVec.ofNat 32 (8 + 4 * n) := by
  have hc := copies_run (bytes := bytes) (u := u) n hr (fun j hj => hw j (by omega))
  obtain ⟨f, hv⟩ := copiedState_mem (bytes := bytes) (u := u) n (by omega) (by omega)
  obtain ⟨w', ht, hrd, hwr, hg, hm⟩ := tail_run (n := n) (w := copiedState bytes u n)
    (by simpa using hw n (Nat.le_refl _))
  have hrun : execBlock isa (setArgs bytes n) u = some (w', setArgsTrace bytes (u.gpr .esp) n) := by
    rw [setArgs, execBlock_append, hc]
    simp only [Option.bind_some, ht, Option.map_some, copiedState_esp, setArgsTrace]
  have hst : setArgsState bytes n u = w' := by simp [setArgsState, hrun]
  rw [hst]
  have hA : ∀ d, d < 4 + bytes + 4 * n → addr (u.gpr .esp) d =
      (u.gpr .esp).setWidth 64 + BitVec.ofNat 64 d := fun d hd => addr_eq (by omega)
  refine ⟨hrun, by rw [hrd, copiedState_rd], by rw [hwr, copiedState_wr], fun q hq => ?_, ?_,
    fun j hj => ?_, ?_⟩
  · rw [hg q hq, copiedState_gpr _ _ hq]
  · rw [hm, copiedState_esp]
    refine (Frame.sub f fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · rw [hA _ (by omega)]
      exact Offset.contains _ (d := 4 + 4 * n) (e := 4) (k := 4 * (n + 1)) (by omega) (by omega)
        (by omega)
  · rw [hm, copiedState_esp, Mem.readW_writeW_sep, hv j hj]
    · rw [hA _ (by omega), hA _ (by omega)]
      exact Offset.sep _ (d := 4 + 4 * j) (n := 4) (e := 4 + 4 * n) (k := 4) (by omega) (by omega)
        (by omega)
    · decide
  · rw [hm, copiedState_esp, Mem.readW_writeW_self32]

/-! ## The run from `narrow` -/

/-- `e - b + d` is `e - (b - d)`, in 64 bits, for addresses that do not wrap. -/
theorem sub_add_setWidth {e : BitVec 32} {b d : Nat} (hd : d ≤ b) (hb : b ≤ e.toNat) :
    (e - BitVec.ofNat 32 b + BitVec.ofNat 32 d).setWidth 64 = e.setWidth 64 - BitVec.ofNat 64 (b - d) := by
  rw [show e - BitVec.ofNat 32 b + BitVec.ofNat 32 d = e - BitVec.ofNat 32 (b - d) by
    rw [Offset.sub_ofNat_eq e (show b - d ≤ b by omega), Nat.sub_sub_self hd]]
  exact Taint.sub_setWidth (by omega)

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
  { s.setReg .esp (s.gpr .esp - BitVec.ofNat 32 bytes) with
    wr := ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr }

@[simp] theorem allocState_esp (bytes : Nat) (s : State) :
    (allocState bytes s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes := by
  simp [allocState, State.setReg]
@[simp] theorem allocState_mem (bytes : Nat) (s : State) : (allocState bytes s).mem = s.mem := rfl
@[simp] theorem allocState_rd (bytes : Nat) (s : State) : (allocState bytes s).rd = s.rd := rfl
@[simp] theorem allocState_wr (bytes : Nat) (s : State) :
    (allocState bytes s).wr = ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr := rfl
theorem allocState_gpr (bytes : Nat) (s : State) {q : Reg} (h : q ≠ .esp) :
    (allocState bytes s).gpr q = s.gpr q := by
  simp [allocState, State.setReg, h]

/-- The regions of the contract with the buffer, from the state after
`setArgs`: the buffers, the buffer, and the arguments in the frame. -/
def oldRegions (sig : Sig) (e : Elem) (n bytes : Nat) (wa : Bool) (s : State) :
    List (Region × Bool) :=
  Sig.bufs sig.params (stackArgs sig s) ++
    [(⟨(s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 (8 + 4 * slots sig)).setWidth 64,
        n * e.size⟩, true),
      (⟨(s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 4).setWidth 64,
        4 * (slots sig + 1)⟩, wa)]

/-- The state the code runs from, with the permissions of the contract with
the buffer: the state after the frame's push and `setArgs`, which may read
and write what the contract with the buffer lets it. -/
def narrow (sig : Sig) (e : Elem) (n bytes : Nat) (wa : Bool) (s : State) : State :=
  (setArgsState bytes (slots sig) (allocState bytes s)).withRegions
    (((oldRegions sig e n bytes wa s).filter (!·.2)).map (·.1))
    (((oldRegions sig e n bytes wa s).filter (·.2)).map (·.1))

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes : Nat}

/-- What `setArgs` gives, from a state satisfying the contract without the
buffer. -/
theorem argsState_run {s : State} (hs : (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hb : 8 + 4 * slots sig + n * e.size ≤ bytes) :
    let u := allocState bytes s
    execBlock isa (setArgs bytes (slots sig)) u =
        some (setArgsState bytes (slots sig) u, setArgsTrace bytes (u.gpr .esp) (slots sig)) ∧
      (setArgsState bytes (slots sig) u).rd = u.rd ∧ (setArgsState bytes (slots sig) u).wr = u.wr ∧
      (∀ q, q ≠ .eax → (setArgsState bytes (slots sig) u).gpr q = u.gpr q) ∧
      Frame [⟨(u.gpr .esp).setWidth 64 + 4, 4 * (slots sig + 1)⟩] s.mem
        (setArgsState bytes (slots sig) u).mem ∧
      (∀ j < slots sig, arg (setArgsState bytes (slots sig) u) j = arg s j) ∧
      arg (setArgsState bytes (slots sig) u) (slots sig) =
        s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 (8 + 4 * slots sig) := by
  intro u
  rw [pre_stack] at hs
  obtain ⟨⟨hst, hfit⟩, hrd, hwr, -, -, -, -⟩ := hs
  have hE : (u.gpr .esp).toNat = (s.gpr .esp).toNat - bytes := by
    simp only [u, allocState_esp]; exact sub_toNat (by omega)
  have hsrc : ∀ j, addr (u.gpr .esp) (bytes + 4 + 4 * j) = argAddr s j := fun j => by
    simp only [u, allocState_esp, addr, argAddr]
    refine congrArg (BitVec.setWidth 64) ?_
    rw [show bytes + 4 + 4 * j = bytes + (4 + 4 * j) by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
      BitVec.sub_add_cancel]
  have hesp : u.gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes := allocState_esp _ _
  -- The caller's argument area holds the sources.
  have hpos : ∀ j < slots sig, 0 < slots sig := fun j hj => by omega
  have hargs : ∀ j < slots sig, InRegions (u.rd ++ u.wr) (argAddr s j) 4 := fun j hj => by
    have hmem : (⟨argAddr s 0, 4 * slots sig⟩, wa) ∈ allRegions sig wa s := by
      simp [allRegions, show slots sig ≠ 0 by omega]
    have hc : (⟨argAddr s 0, 4 * slots sig⟩ : Region).Contains (argAddr s j) 4 := by
      show (⟨addr (s.gpr .esp) (4 + 4 * 0), 4 * slots sig⟩ : Region).Contains
        (addr (s.gpr .esp) (4 + 4 * j)) 4
      rw [addr_eq (x := s.gpr .esp) (k := 4 + 4 * 0) (by omega),
        addr_eq (x := s.gpr .esp) (k := 4 + 4 * j) (by omega)]
      exact Offset.contains _ (by omega) (by omega) (by omega)
    cases wa with
    | false =>
      refine ⟨_, List.mem_append_left _ ?_, hc⟩
      simp only [u, allocState_rd, hrd]
      exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
    | true =>
      refine ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ ?_), hc⟩
      rw [hwr]
      exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
  have hframe : ∀ j ≤ slots sig, InRegions u.wr (addr (u.gpr .esp) (4 + 4 * j)) 4 := fun j hj => by
    refine ⟨_, List.mem_cons_self .., ?_⟩
    have h₁ : (s.gpr .esp - BitVec.ofNat 32 bytes).toNat = (s.gpr .esp).toNat - bytes :=
      sub_toNat (by omega)
    rw [hesp, addr_eq (x := s.gpr .esp - BitVec.ofNat 32 bytes) (k := 4 + 4 * j) (by rw [h₁]; omega)]
    exact Offset.contains_base _ (by omega) (by omega)
  obtain ⟨hrun, hrd', hwr', hg, hf, hv, hl⟩ := setArgs_run (bytes := bytes) (n := slots sig) (u := u)
    (by rw [hE]; omega) (by omega) (fun j hj => by rw [hsrc]; exact hargs j hj) hframe
  have hesp₂ : (setArgsState bytes (slots sig) u).gpr .esp = u.gpr .esp := hg _ (by decide)
  refine ⟨hrun, hrd', hwr', hg, hf, fun j hj => ?_, ?_⟩
  · show (setArgsState bytes (slots sig) u).mem.readW
      (((setArgsState bytes (slots sig) u).gpr .esp + BitVec.ofNat 32 (4 + 4 * j)).setWidth 64) 32 = _
    rw [hesp₂]
    exact (hv j hj).trans (by rw [hsrc]; rfl)
  · show (setArgsState bytes (slots sig) u).mem.readW
      (((setArgsState bytes (slots sig) u).gpr .esp + BitVec.ofNat 32 (4 + 4 * slots sig)).setWidth 64) 32 = _
    rw [hesp₂]
    exact hl.trans (by rw [hesp])

/-- The bytes below `E` that the contract without the buffer reserves contain
each region at `E - a` of `n` bytes that the frame (of `bytes` bytes, below
the `stack` bytes the code uses) holds. -/
theorem below_sub' (E : Addr) {a n stack bytes : Nat} (ha : a ≤ stack + bytes)
    (hn : stack + bytes - a + n ≤ stack + bytes) :
    Region.Sub ⟨E - BitVec.ofNat 64 a, n⟩ ⟨E - BitVec.ofNat 64 (stack + bytes), stack + bytes⟩ :=
  Offset.sub_below E ha hn

theorem stackBelow_sp' (E : Addr) (bytes stack : Nat) :
    stackBelow (E - BitVec.ofNat 64 bytes) stack =
      if stack = 0 then [] else [⟨E - BitVec.ofNat 64 (bytes + stack), stack⟩] := by
  cases stack with
  | zero => rfl
  | succ k => simp [stackBelow, BitVec.sub_sub, BitVec.ofNat_add]

theorem stackArgs_length (sig : Sig) (s : State) :
    (stackArgs sig s).length = (sig.params.flatMap fun p => p.2.words abi.ptrBits).length := by
  rw [stackArgs, List.length_map, List.length_zip, argSlots_length, Nat.min_self, widths,
    List.length_map]
  rfl

theorem narrow_mem (sig : Sig) (e : Elem) (n bytes : Nat) (wa : Bool) (s : State) :
    (narrow sig e n bytes wa s).mem = (setArgsState bytes (slots sig) (allocState bytes s)).mem :=
  State.withRegions_mem _ _ _

/-- What `narrow` keeps of `s`, and what it holds. -/
theorem narrow_facts (hb : 8 + 4 * slots sig + n * e.size ≤ bytes) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) :
    (narrow sig e n bytes wa s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes ∧
      (∀ q, q ≠ .eax → q ≠ .esp → (narrow sig e n bytes wa s).gpr q = s.gpr q) ∧
      stackArgs (sig.withScratch nm e n) (narrow sig e n bytes wa s) =
        stackArgs sig s ++
          [(s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 (8 + 4 * slots sig)).setWidth 64] ∧
      Frame [⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - 4), 4 * (slots sig + 1)⟩]
        s.mem (narrow sig e n bytes wa s).mem := by
  obtain ⟨-, -, -, hg, hf, hargs, hlast⟩ := argsState_run hs hb
  rw [pre_stack] at hs
  obtain ⟨⟨hst, -⟩, -, -, -, -, -, -⟩ := hs
  refine ⟨(hg .esp (by decide)).trans (allocState_esp _ _), fun q h₁ h₂ => ?_, ?_, ?_⟩
  · exact (hg q h₁).trans (allocState_gpr _ _ h₂)
  · rw [stackArgs_withScratch sig nm e n (s := narrow sig e n bytes wa s) (s₀ := s)
      fun j hj => (arg_withRegions (setArgsState bytes (slots sig) (allocState bytes s)) _ _ j).trans
        (hargs j hj)]
    exact congrArg (fun x => stackArgs sig s ++ [BitVec.setWidth 64 x])
      ((arg_withRegions (setArgsState bytes (slots sig) (allocState bytes s)) _ _ _).trans hlast)
  · have h₁ : ((allocState bytes s).gpr .esp).setWidth 64 + 4 =
        (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - 4) := by
      rw [allocState_esp, Taint.sub_setWidth (by omega),
        Offset.sub_ofNat_eq _ (show bytes - 4 ≤ bytes by omega), Nat.sub_sub_self (by omega)]
      rfl
    rw [narrow_mem, ← h₁]; exact hf

/-- The precondition of the contract without the buffer gives the one with it
in `narrow`, if the precondition reads memory only within the buffers. -/
theorem narrow_pre (hb : 8 + 4 * slots sig + n * e.size ≤ bytes)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) :
    (Sig.scratchContract abi sig nm e n pre post wa stack).pre (narrow sig e n bytes wa s) := by
  obtain ⟨-, -, -, hg, hf, -, -⟩ := argsState_run hs hb
  have hst' := (narrow_facts (nm := nm) hb hs).2.2.1
  rw [pre_stack] at hs
  obtain ⟨⟨hst, hfit⟩, hrd, hwr, hpw, hres, hnw, hpr⟩ := hs
  have hS : 0 < bytes := by omega
  -- Addresses as offsets below `E`.
  have hsp : (s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 bytes := Taint.sub_setWidth (by omega)
  have hscr : (s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 (8 + 4 * slots sig)).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (8 + 4 * slots sig)) :=
    sub_add_setWidth (by omega) (by omega)
  have harea : (s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 4).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - 4) :=
    sub_add_setWidth (by omega) (by omega)
  have hbelow : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (stack + bytes), stack + bytes⟩ : Region) ∈
      (⟨(s.gpr .esp).setWidth 64, 4⟩ :: stackBelow ((s.gpr .esp).setWidth 64) (stack + bytes) :
        List Region) := by
    rw [show stack + bytes = (stack + bytes - 1) + 1 by omega]; simp [stackBelow]
  -- The buffers lie outside the frame.
  have hout : ∀ a ∈ Sig.bufs sig.params (stackArgs sig s), ∀ {x : Nat} {k : Nat}, x ≤ stack + bytes →
      stack + bytes - x + k ≤ stack + bytes →
      a.1.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 x, k⟩ := fun a ha _ _ hx hk =>
    (Region.Disjoint.symm (hres _ hbelow a (List.mem_append_left _ ha))).sub_right
      (below_sub' _ hx hk)
  -- The arguments of the contract with the buffer.
  have hlen := stackArgs_length sig s
  have hesp₂ : (narrow sig e n bytes wa s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes :=
    (hg .esp (by decide)).trans (allocState_esp _ _)
  have harg0 : argAddr (narrow sig e n bytes wa s) 0 =
      (s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 4).setWidth 64 := by
    show ((narrow sig e n bytes wa s).gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = _
    rw [hesp₂]
  have hall : allRegions (sig.withScratch nm e n) wa (narrow sig e n bytes wa s) =
      oldRegions sig e n bytes wa s := by
    rw [allRegions, hst', slots_withScratch, harg0]
    rw [show (sig.withScratch nm e n).params = sig.params ++ [((nm, .array true e n) : String × Param)]
      from rfl, Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _ hlen]
    simp only [Nat.add_one_ne_zero, ite_false, oldRegions, List.append_assoc, List.cons_append,
      List.nil_append]
  -- The positions, from the bottom of the stack the contract without the buffer reserves.
  have hfit' : (s.gpr .esp).toNat < 2 ^ 32 := (s.gpr .esp).isLt
  refine (pre_stack (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)).mpr ?_
  rw [hall, hesp₂, slots_withScratch, hst']
  refine ⟨⟨?_, ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [sub_toNat (by omega)]; omega
  · rw [sub_toNat (by omega)]; omega
  · -- Pairwise disjoint.
    simp only [oldRegions]
    rw [List.pairwise_append]
    refine ⟨List.Pairwise.sublist (List.sublist_append_left _ _) hpw, ?_, fun a ha b hb _ => ?_⟩
    · simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
        List.Pairwise.nil, and_true, Bool.true_or, forall_const]
      rw [hscr, harea]
      exact ⟨Region.Disjoint.symm (below_disjoint _ (stack + bytes) (a := bytes - 4)
        (n := 4 * (slots sig + 1)) (b := bytes - (8 + 4 * slots sig)) (k := n * e.size)
        (by omega) (by omega) (.inl (by omega)) (by omega) (by omega)), fun _ h => h.elim⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · rw [hscr]; exact hout a ha (by omega) (by omega)
      · rw [harea]; exact hout a ha (by omega) (by omega)
  · -- The reserved stack: the frame's first word and the stack below it.
    intro r hr a ha
    rw [hsp] at hr
    simp only [List.mem_cons, stackBelow_sp'] at hr
    have hr' : r = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 bytes, 4⟩ ∨
        (stack ≠ 0 ∧ r = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes + stack), stack⟩) := by
      rcases hr with rfl | hr
      · exact .inl rfl
      · by_cases h0 : stack = 0
        · simp [h0] at hr
        · simp only [h0, ite_false, List.mem_singleton] at hr; exact .inr ⟨h0, hr⟩
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · rcases hr' with rfl | ⟨-, rfl⟩
      · exact Region.Disjoint.symm (hout a ha (by omega) (by omega))
      · exact Region.Disjoint.symm (hout a ha (by omega) (by omega))
    · rw [hscr]
      rcases hr' with rfl | ⟨h0, rfl⟩
      · exact below_disjoint _ (stack + bytes) (a := bytes) (n := 4) (b := bytes - (8 + 4 * slots sig))
          (k := n * e.size) (by omega) (by omega) (.inl (by omega)) (by omega) (by omega)
      · exact below_disjoint _ (stack + bytes) (a := bytes + stack) (n := stack)
          (b := bytes - (8 + 4 * slots sig)) (k := n * e.size) (by omega) (by omega) (.inl (by omega))
          (by omega) (by omega)
    · rw [harea]
      rcases hr' with rfl | ⟨h0, rfl⟩
      · exact below_disjoint _ (stack + bytes) (a := bytes) (n := 4) (b := bytes - 4)
          (k := 4 * (slots sig + 1)) (by omega) (by omega) (.inl (by omega)) (by omega) (by omega)
      · exact below_disjoint _ (stack + bytes) (a := bytes + stack) (n := stack) (b := bytes - 4)
          (k := 4 * (slots sig + 1)) (by omega) (by omega) (.inl (by omega)) (by omega) (by omega)
  · -- No buffer wraps around.
    intro a ha
    rw [show (sig.withScratch nm e n).params = sig.params ++ [((nm, .array true e n) : String × Param)]
      from rfl, Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _ hlen] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hnw a ha
    · simp only [List.mem_singleton] at ha; subst ha
      show (BitVec.setWidth 64 (s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 (8 + 4 * slots sig))).toNat +
        n * e.size ≤ 2 ^ 32
      rw [hscr, toNat_sub64 (by simp; omega)]
      simp; omega
  · -- The precondition, which reads only the buffers.
    rw [narrow_mem]
    refine Eq.mpr (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params pre _ _ hlen) _) ?_
    refine hpre _ _ _ (stackArgs_length sig s) (fun b hb x hx => (hf x fun r hr hc => ?_).symm) hpr
    simp only [List.mem_singleton] at hr; subst hr
    rw [allocState_esp, hsp] at hc
    rw [show (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 bytes + 4 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - 4) by
        rw [Offset.sub_ofNat_eq _ (show bytes - 4 ≤ bytes by omega), Nat.sub_sub_self (by omega)]; rfl] at hc
    exact hout b hb (x := bytes - 4) (k := 4 * (slots sig + 1)) (by omega) (by omega) x hx hc

/-- The buffers lie outside the frame: `narrow`'s memory is `s`'s there. -/
theorem narrow_agree (hb : 8 + 4 * slots sig + n * e.size ≤ bytes) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) :
    ∀ b ∈ Sig.bufs sig.params (stackArgs sig s), ∀ x, b.1.Contains x 1 →
      (narrow sig e n bytes wa s).mem x = s.mem x := by
  obtain ⟨-, -, -, hf⟩ := narrow_facts (nm := "") hb hs
  rw [pre_stack] at hs
  obtain ⟨⟨hst, -⟩, -, -, -, hres, -, -⟩ := hs
  have hbelow : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (stack + bytes), stack + bytes⟩ : Region) ∈
      (⟨(s.gpr .esp).setWidth 64, 4⟩ :: stackBelow ((s.gpr .esp).setWidth 64) (stack + bytes) :
        List Region) := by
    rw [show stack + bytes = (stack + bytes - 1) + 1 by omega]; simp [stackBelow]
  intro b hb x hx
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact (Region.Disjoint.symm (hres _ hbelow b (List.mem_append_left _ hb))).sub_right
    (below_sub' _ (by omega) (by omega)) x hx hc

/-- The postcondition of a contract, with every argument on the stack. -/
theorem post_stack {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s s' : State} :
    (sig.contract abi pre post wa stack leak).post s s' ↔
      Curry.apply (sig.words abi.ptrBits) post (stackArgs sig s) s.mem s'.mem
        ((s'.gpr .edx ++ s'.gpr .eax).setWidth _) := by
  simp only [Sig.contract]
  rw [args_stack]
  exact Iff.rfl

/-- The public data of a contract that leaks nothing, with every argument on
the stack. -/
theorem pub_stack {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat} {s₁ s₂ : State} :
    (sig.contract abi pre post wa stack none).pub s₁ s₂ ↔
      s₁.gpr .esp = s₂.gpr .esp ∧
      ∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((stackArgs sig s₁).getD i 0).setWidth ((widths sig).getD i 64) =
          ((stackArgs sig s₂).getD i 0).setWidth ((widths sig).getD i 64) := by
  simp only [Sig.contract]
  rw [args_stack]
  exact Iff.rfl


/-- The state after the pop of `withStackScratch`'s frame, from the state
`s₃` its code ends in when it starts in `s`. -/
def popState (bytes : Nat) (s s₃ : State) : State :=
  { (s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)).setReg
      .esp (s.gpr .esp) with wr := s.wr }

/-- A run of the code from `narrow s` is a run of `withStackScratch` from
`s`, after `setArgs`'s accesses, which keeps what the calling convention
requires, and whose memory and result are those of the code's run. -/
theorem withStackScratch_run {c : Prog isa}
    (hb : 8 + 4 * slots sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 4 = 0)
    (hsp : NoSp c) (hd : stackUse c ≤ stack) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrow sig e n bytes wa s) t s₃) (ha : abiPreserved (narrow sig e n bytes wa s) s₃) :
    Exec isa (withStackScratch bytes (slots sig) c) s
        (setArgsTrace bytes (s.gpr .esp - BitVec.ofNat 32 bytes) (slots sig) ++ t) (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr .eax = s₃.gpr .eax ∧ (popState bytes s s₃).gpr .edx = s₃.gpr .edx := by
  obtain ⟨hb, hb1, hb2⟩ := hb
  obtain ⟨hrun, hrd', hwr', -, -, -, -⟩ := argsState_run hs hb
  obtain ⟨hesp, hg, -, hf⟩ := narrow_facts (nm := "") hb hs
  have hagree := narrow_agree hb hs
  rw [pre_stack] at hs
  obtain ⟨⟨hst, hfit⟩, hrd, hwr, -, hres, -, -⟩ := hs
  have hbelow : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (stack + bytes), stack + bytes⟩ : Region) ∈
      (⟨(s.gpr .esp).setWidth 64, 4⟩ :: stackBelow ((s.gpr .esp).setWidth 64) (stack + bytes) :
        List Region) := by
    rw [show stack + bytes = (stack + bytes - 1) + 1 by omega]; simp [stackBelow]
  have hsp64 : (s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 bytes := Taint.sub_setWidth (by omega)
  -- The frame's push and `setArgs`.
  have hpush : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, show 0 < bytes by omega, hb1, hb2, show bytes ≤ (s.gpr .esp).toNat by omega,
      and_self, ite_true]
    rfl
  -- The regions of `narrow`: the buffers, and the frame's buffer and arguments.
  have hF : ∀ {a k : Nat}, a ≤ bytes → bytes - a + k ≤ bytes →
      Covers [⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 a, k⟩]
        (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr) := fun ha hk =>
    Covers.one ⟨_, List.mem_cons_self .., by
      rw [hsp64]; exact Offset.contains_below _ ha hk (by omega)⟩
  have hscr : (s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 (8 + 4 * slots sig)).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - (8 + 4 * slots sig)) :=
    sub_add_setWidth (by omega) (by omega)
  have harea : (s.gpr .esp - BitVec.ofNat 32 bytes + BitVec.ofNat 32 4).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (bytes - 4) :=
    sub_add_setWidth (by omega) (by omega)
  have hbufR : ∀ a ∈ Sig.bufs sig.params (stackArgs sig s), a.2 = false → a.1 ∈ s.rd := fun a ha h => by
    rw [hrd]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, by simp [h]⟩, rfl⟩
  have hbufW : ∀ a ∈ Sig.bufs sig.params (stackArgs sig s), a.2 = true → a.1 ∈ s.wr := fun a ha h => by
    rw [hwr]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, h⟩, rfl⟩
  have hcovW : Covers (((oldRegions sig e n bytes wa s).filter (·.2)).map (·.1))
      (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · exact Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ (hbufW a ha hf')
    · rw [hscr]; exact hF (by omega) (by omega)
    · rw [harea]; exact hF (by omega) (by omega)
  have hcovR : Covers (((oldRegions sig e n bytes wa s).filter (!·.2)).map (·.1))
      (s.rd ++ ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr) := by
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha (by simpa using hf'))
    · simp at hf'
    · exact Covers.right (by rw [harea]; exact hF (by omega) (by omega))
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)
    (Covers.append_left hcovR (Covers.right hcovW)) hcovW
  rw [show (narrow sig e n bytes wa s).withRegions s.rd
      (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr) =
      setArgsState bytes (slots sig) (allocState bytes s) by
    rw [narrow, State.withRegions_withRegions, ← allocState_rd bytes s, ← hrd',
      show ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr = (allocState bytes s).wr
        from rfl, ← hwr', State.withRegions_self]] at hw
  -- The pop.
  have hesp₃ : s₃.gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes :=
    (ha.1 .esp (by simp [calleeSaved])).trans hesp
  have hpop : isa.pop (.free bytes) (allocState bytes s)
      (s₃.withRegions s.rd (⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr)) =
      some (popState bytes s s₃) := by
    simp only [isa, pop, State.withRegions_gpr, State.withRegions_wr, allocState_esp, allocState_wr,
      hesp₃, List.head?_cons, show 0 < bytes by omega, hb1, hb2, and_self, ite_true, List.tail_cons,
      BitVec.sub_add_cancel]
    rfl
  have hex := Exec.frame hpush (Exec.seq (Exec.block hrun) hw) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil, allocState_esp] at hex
  refine ⟨hex, ⟨fun q hq => ?_, ?_⟩, rfl, ?_, ?_⟩
  · simp only [popState, State.setReg, State.withRegions_gpr]
    by_cases hqs : q = .esp
    · subst hqs; simp only [ite_true]
    · simp only [hqs, ite_false]
      have hqa : q ≠ .eax := fun h => by subst h; simp [calleeSaved] at hq
      rw [ha.1 q hq, hg q hqa hqs]
  · -- The return address: the code writes only its regions and below `esp`.
    have hfs := Exec.frameSp he hsp (by rw [hesp, sub_toNat (by omega)]; omega)
    have hR : ∀ {x k : Nat}, x ≤ stack + bytes → stack + bytes - x + k ≤ stack + bytes →
        (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
          ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 x, k⟩ := fun hx hk =>
      (Offset.base_disjoint_below _ (n := stack + bytes) (k := 4) (by omega)).sub_right
        (below_sub' _ hx hk)
    show s₃.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32
    rw [hfs.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
    · exact hf.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hR (by omega) (by omega)) (by decide)
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
        obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
        simp only [oldRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with ha | rfl | rfl
        · exact hres _ (List.mem_cons_self ..) a (List.mem_append_left _ ha)
        · rw [hscr]; exact hR (by omega) (by omega)
        · rw [harea]; exact hR (by omega) (by omega)
      · simp only [List.mem_singleton] at hr; subst hr
        rw [hesp]
        show (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
          ⟨(s.gpr .esp - BitVec.ofNat 32 bytes - BitVec.ofNat 32 (stackUse c)).setWidth 64, stackUse c⟩
        rw [BitVec.sub_sub, ← BitVec.ofNat_add, Taint.sub_setWidth (by omega)]
        exact hR (by omega) (by omega)
  · simp [popState, State.setReg]
  · simp [popState, State.setReg]


/-- The public data of the contract without the buffer gives that of the
one with it in `narrow`: the buffer's address is the stack pointer's. -/
theorem narrow_pub (hb : 8 + 4 * slots sig + n * e.size ≤ bytes) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + bytes)).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + bytes)).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + bytes)).pub s₁ s₂) :
    (Sig.scratchContract abi sig nm e n pre post wa stack).pub (narrow sig e n bytes wa s₁)
      (narrow sig e n bytes wa s₂) := by
  rw [pub_stack] at hp
  obtain ⟨hsp, hpa⟩ := hp
  obtain ⟨e₁, -, a₁, -⟩ := narrow_facts (nm := nm) hb h₁
  obtain ⟨e₂, -, a₂, -⟩ := narrow_facts (nm := nm) hb h₂
  refine (pub_stack (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)).mpr ?_
  rw [e₁, e₂, a₁, a₂, hsp]
  refine ⟨rfl, fun i hi => ?_⟩
  have l₁ := stackArgs_length sig s₁
  have l₂ := stackArgs_length sig s₂
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

/-- Code verified for a function whose last argument is a scratch buffer of
`n` elements `e`, with `stack` bytes of stack, is verified for the function
without it, which allocates the buffer in a frame of `bytes` more bytes of
stack (`withStackScratch`), if its precondition and postcondition read
memory only within the function's buffers (`hpre`, `hpost`). -/
theorem Verified.stackScratch {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hb : 8 + 4 * slots sig + n * e.size ≤ bytes ∧ bytes < 4096 ∧ bytes % 4 = 0)
    (hsp : c.allInstrs (fun i => !Taint.clobbers i .esp) = true) (hd : stackUse c ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s) :
    Verified target (withStackScratch bytes (slots sig) c)
      (sig.contract abi pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hnsp : NoSp c := fun i hi => by
    rw [Code.allInstrs_eq, List.all_eq_true] at hsp
    simpa using hsp i hi
  -- Every run is `setArgs`, then the code's run from `narrow`.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃,
      Exec isa c (narrow sig e n bytes wa s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrow sig e n bytes wa s) s₃ ∧
      Exec isa (withStackScratch bytes (slots sig) c) s
        (setArgsTrace bytes (s.gpr .esp - BitVec.ofNat 32 bytes) (slots sig) ++ t)
        (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr .eax = s₃.gpr .eax ∧ (popState bytes s s₃).gpr .edx = s₃.gpr .edx := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_pre hb.1 hpre hs)
    exact ⟨t, s₃, he, hq, withStackScratch_run hb hnsp hd hs he ha⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, heax, hedx⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_stack]
    have hq' := (post_stack (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)).mp hq
    obtain ⟨-, -, hargs, -⟩ := narrow_facts (nm := nm) hb.1 hs
    rw [hargs] at hq'
    rw [hm, heax, hedx]
    have hq'' := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (stackArgs_length sig s)) _) s₃.mem) _) hq'
    exact hpost _ _ _ _ _ (stackArgs_length sig s) (narrow_agree hb.1 hs) hq''
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, (pub_stack.mp hp).1,
      hct _ _ _ _ _ _ (narrow_pre hb.1 hpre h₁) (narrow_pre hb.1 hpre h₂)
        (narrow_pub hb.1 h₁ h₂ hp) f₁ f₂]


end

end VG.X86
