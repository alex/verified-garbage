import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.X86_64.Target

/-!
# A scratch buffer on the stack (x86-64)

`Verified.stackScratch`: code verified for a function whose last
argument, passed in a register, is a scratch buffer (its contract
`Sig.scratchContract`), runs as a function without that argument when
`withStackScratch` allocates the buffer in a frame on the stack, with
`bytes` more bytes of stack. The code runs from the state after the frame's
push with the permissions of the contract with the argument (`narrow`), and
its run there is its run from that state (`Exec.widen`). The frame's first
eight bytes stand for the return address of the contract with the argument,
which keeps them out of the buffers; the code changes no memory at or above
the frame but in the buffers (`Exec.stackFrame`), so it keeps the return
address of the function without the argument.
-/

namespace VG.X86_64

open VG.Impl.StackScratch.X86_64

/-- The arguments of a function with signature `sig`, all in registers. -/
abbrev regArgs (sig : Sig) (s : State) : List (BitVec 64) :=
  (argRegs.take (sig.words abi.ptrBits).length).map s.gpr

theorem stackBelow_pos (sp : Addr) {n : Nat} (h : 0 < n) : stackBelow sp n = [below sp n] := by
  cases n with
  | zero => omega
  | succ n => rfl

theorem argRegs_take_succ (g : Reg → BitVec 64) :
    ∀ k < 6, (argRegs.take (k + 1)).map g = (argRegs.take k).map g ++ [g (argRegs.getD k .rax)]
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl
  | _ + 6, h => absurd h (by omega)

theorem argRegs_scratch :
    ∀ k < 6, argRegs.getD k .rax ≠ .rsp ∧ argRegs.getD k .rax ∉ calleeSaved ∧
      ∀ q ∈ argRegs.take k, q ≠ argRegs.getD k .rax ∧ q ≠ .rsp := by
  decide

theorem regArgs_length (sig : Sig) (s : State) (hk : (sig.words abi.ptrBits).length ≤ 6) :
    (regArgs sig s).length = (sig.words abi.ptrBits).length := by
  simp only [regArgs, List.length_map, List.length_take, argRegs, List.length_cons, List.length_nil]
  omega

/-- The precondition of a contract whose arguments are all in registers. -/
theorem pre_regs {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
    {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State}
    (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true) :
    (sig.contract abi pre post wa stack leak).pre s ↔
      (stack = 0 ∨ stack ≤ (s.gpr .rsp).toNat) ∧
      s.rd = ((Sig.bufs sig.params (regArgs sig s)).filter (!·.2)).map (·.1) ∧
      s.wr = ((Sig.bufs sig.params (regArgs sig s)).filter (·.2)).map (·.1) ∧
      (Sig.bufs sig.params (regArgs sig s)).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) ∧
      (∀ r ∈ (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) stack : List Region),
        ∀ a ∈ Sig.bufs sig.params (regArgs sig s), r.Disjoint a.1) ∧
      (∀ a ∈ Sig.bufs sig.params (regArgs sig s), a.1.base.toNat + a.1.len ≤ 2 ^ 64) ∧
      Curry.apply (sig.words abi.ptrBits) pre (regArgs sig s) s.mem := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 6 := hk
    simpa [argRegs] using this
  have h0 : (sig.words 64).length - argRegs.length = 0 := by omega
  have hwf : (match stack with | 0 => True | n => n ≤ (s.gpr .rsp).toNat) ↔
      (stack = 0 ∨ stack ≤ (s.gpr .rsp).toNat) := by
    cases stack <;> simp
  have hL := fun vs => Sig.lists_of_noLists 64 s.mem sig.params vs hl
  simp only [Sig.contract, abi, List.length_map, hk', h0, ite_true, List.map_nil, List.append_nil, hL]
  exact and_congr hwf Iff.rfl

/-- The postcondition of a contract whose arguments are all in registers. -/
theorem post_regs {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
    {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s s' : State}
    (hk : (sig.words abi.ptrBits).length ≤ 6) :
    (sig.contract abi pre post wa stack leak).post s s' ↔
      Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem s'.mem ((s'.gpr .rax).setWidth _) := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 6 := hk
    simpa [argRegs] using this
  simp only [Sig.contract, abi, List.length_map, hk', ite_true]
  exact Iff.rfl

/-- The public data of a contract whose arguments are all in registers, and
which leaks nothing. -/
theorem pub_regs {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
    {wa : Bool} {stack : Nat} {s₁ s₂ : State} (hk : (sig.words abi.ptrBits).length ≤ 6)
    (hl : Sig.noLists sig.params = true) :
    (sig.contract abi pre post wa stack none).pub s₁ s₂ ↔
      s₁.gpr .rsp = s₂.gpr .rsp ∧
      ∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((regArgs sig s₁).getD i 0).setWidth (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) =
          ((regArgs sig s₂).getD i 0).setWidth (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 6 := hk
    simpa [argRegs] using this
  have hD := fun vs => Sig.descs_of_noLists 64 sig.params vs hl
  simp only [Sig.contract, abi, List.length_map, hk', ite_true, hD, List.not_mem_nil, false_implies,
    implies_true, and_true]
  exact Iff.rfl

/-- The value of argument word `i` of `sig` in `satRegs`: `2⁴⁰ (i + 1)` for a
pointer, 0 for an integer. -/
def satArg (sig : Sig) (i : Nat) : BitVec 64 :=
  match (sig.words abi.ptrBits)[i]? with
  | some .addr => BitVec.ofNat 64 (2 ^ 40 * (i + 1))
  | _ => 0

/-- A state for the satisfiability of a contract whose arguments are all in
registers: each pointer `2⁴⁰ (i + 1)`, each integer 0 (so each slice is
empty), `rsp` `2⁶³`, and permissions exactly for the buffers. -/
def satRegs (sig : Sig) : State :=
  let g : Reg → BitVec 64 := fun r => match r with
    | .rdi => satArg sig 0 | .rsi => satArg sig 1 | .rdx => satArg sig 2
    | .rcx => satArg sig 3 | .r8 => satArg sig 4 | .r9 => satArg sig 5
    | .rsp => BitVec.ofNat 64 (2 ^ 63) | _ => 0
  let bufs := Sig.bufs sig.params ((argRegs.take (sig.words abi.ptrBits).length).map g)
  { gpr := g, cf := none, zf := none, sf := none, of := none, mem := fun _ => 0,
    rd := (bufs.filter (!·.2)).map (·.1), wr := (bufs.filter (·.2)).map (·.1) }

/-- A contract whose arguments are all in registers is satisfiable if
`satRegs` satisfies what `Sig.check` evaluates and its further
precondition. -/
theorem sat_regs {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    (hk : (sig.words abi.ptrBits).length ≤ 6) (hs : stack ≤ 2 ^ 63)
    (hc : Sig.check abi sig wa stack (satRegs sig) = true)
    (hp : Curry.apply (sig.words abi.ptrBits) pre (regArgs sig (satRegs sig)) (fun _ => 0)) :
    ∃ s, (sig.contract abi pre post wa stack).pre s := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 6 := hk
    simpa [argRegs] using this
  refine ⟨satRegs sig, Sig.contract_pre_of_check hc ?_⟩
  simp only [Sig.wfPre, abi, List.length_map, hk', ite_true]
  refine ⟨?_, hp⟩
  cases stack with
  | zero => trivial
  | succ m => simp only [satRegs, BitVec.toNat_ofNat]; omega

/-- The state after the push of `withStackScratch`'s frame. -/
def allocState (bytes : Nat) (s : State) : State :=
  { s.setReg .rsp (s.gpr .rsp - BitVec.ofNat 64 bytes) with
    wr := ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr }

/-- The block passing the buffer's address in `r`. -/
abbrev setScratch (r : Reg) : List Instr := [.mov r (.reg .rsp), .alu .add r (.imm 8)]

/-- The state after `setScratch`. -/
def scratchState (r : Reg) (s : State) : State :=
  ((execBlock isa (setScratch r) s).map Prod.fst).getD s

theorem setScratch_run (r : Reg) (s : State) :
    execBlock isa (setScratch r) s = some (scratchState r s, []) := rfl

theorem scratchState_gpr {r : Reg} (hr : r ≠ .rsp) (s : State) (q : Reg) :
    (scratchState r s).gpr q = if q = r then s.gpr .rsp + 8 else s.gpr q := by
  simp only [scratchState, execBlock, isa, exec, readSrc, execAlu, Option.map_some,
    Option.bind_some, Option.getD_some, arithFlags, State.setFlags, State.setReg]
  by_cases h : q = r
  · subst h; simp
  · simp [h]

@[simp] theorem scratchState_mem (r : Reg) (s : State) : (scratchState r s).mem = s.mem := rfl
@[simp] theorem scratchState_rd (r : Reg) (s : State) : (scratchState r s).rd = s.rd := rfl
@[simp] theorem scratchState_wr (r : Reg) (s : State) : (scratchState r s).wr = s.wr := rfl
@[simp] theorem scratchState_mxcsr (r : Reg) (s : State) : (scratchState r s).mxcsr = s.mxcsr := rfl

/-- `withStackScratch` writes `rsp` only in its frame if its code does. -/
theorem withStackScratch_spSafe {bytes : Nat} {r : Reg} {c : Prog isa} (hr : r ≠ .rsp)
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (withStackScratch bytes r c).all (fun i => !isa.writesSp i) = true := by
  simp only [withStackScratch, Code.all, List.all_cons, List.all_nil, h]
  simp [Instr.dst, hr]

section
variable {sig : Sig} {nm : String} {e : Elem} {n n' : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool} {stack bytes : Nat}

/-- The state the code runs from, with the permissions of the contract with
the buffer: the state after the push of the frame and `setScratch`, which
may read `s.rd` and write `s.wr` and the buffer. -/
def narrow (sig : Sig) (e : Elem) (n bytes : Nat) (s : State) : State :=
  (scratchState (argRegs.getD (sig.words abi.ptrBits).length .rax) (allocState bytes s)).withRegions s.rd
    (s.wr ++ [⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩])

theorem narrow_gpr (hk : (sig.words abi.ptrBits).length < 6) (s : State) (q : Reg) :
    (narrow sig e n bytes s).gpr q =
      if q = argRegs.getD (sig.words abi.ptrBits).length .rax then s.gpr .rsp - BitVec.ofNat 64 bytes + 8
      else if q = .rsp then s.gpr .rsp - BitVec.ofNat 64 bytes else s.gpr q := by
  obtain ⟨hr1, -, -⟩ := argRegs_scratch _ hk
  simp only [narrow, State.withRegions_gpr, scratchState_gpr hr1, allocState, State.setReg,
    ite_true]

@[simp] theorem narrow_mem (s : State) : (narrow sig e n bytes s).mem = s.mem := rfl
@[simp] theorem narrow_rd (s : State) : (narrow sig e n bytes s).rd = s.rd := rfl
@[simp] theorem narrow_wr (s : State) :
    (narrow sig e n bytes s).wr = s.wr ++ [⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩] := rfl
@[simp] theorem narrow_mxcsr (s : State) : (narrow sig e n bytes s).mxcsr = s.mxcsr := rfl

theorem narrow_rsp (hk : (sig.words abi.ptrBits).length < 6) (s : State) :
    (narrow sig e n bytes s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes := by
  obtain ⟨hr1, -, -⟩ := argRegs_scratch _ hk
  simp only [narrow_gpr hk, Ne.symm hr1, ↓reduceIte]

theorem narrow_regArgs (hk : (sig.words abi.ptrBits).length < 6) (s : State) :
    regArgs (sig.withScratch nm e n) (narrow sig e n' bytes s) =
      regArgs sig s ++ [s.gpr .rsp - BitVec.ofNat 64 bytes + 8] := by
  obtain ⟨-, -, hr3⟩ := argRegs_scratch _ hk
  simp only [regArgs, Sig.words_withScratch, List.length_append, List.length_singleton]
  rw [argRegs_take_succ _ _ hk]
  congr 1
  · refine List.map_congr_left fun q hq => ?_
    obtain ⟨hq1, hq2⟩ := hr3 q hq
    simp only [narrow_gpr hk, hq1, hq2, ↓reduceIte]
  · simp only [narrow_gpr hk, ↓reduceIte]

/-- `rsp - bytes + 8` is `rsp - (bytes - 8)`. -/
theorem sub_add_eight (p : Addr) {b : Nat} (h : 8 ≤ b) :
    p - BitVec.ofNat 64 b + 8 = p - BitVec.ofNat 64 (b - 8) := by
  rw [Offset.sub_ofNat_eq p (show b - 8 ≤ b by omega), Nat.sub_sub_self h]; rfl

/-- The precondition of the contract without the buffer gives the one with it
in `narrow`. -/
theorem narrow_pre (hk : (sig.words abi.ptrBits).length < 6)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0 ∧ 8 + n * e.size ≤ bytes)
    (hst : stack + bytes + 8 ≤ 2 ^ 64) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) (hl : Sig.noLists sig.params = true) :
    (Sig.scratchContract abi sig nm e n pre post wa stack).pre (narrow sig e n bytes s) := by
  obtain ⟨hb0, -, -, hb3⟩ := hb
  rw [pre_regs (by omega) hl] at hs
  obtain ⟨hwf, hrd, hwr, hpw, hres, hnw, hpr⟩ := hs
  have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hwf with h | h <;> omega
  have hlen := regArgs_length sig s (by omega)
  have hscr : s.gpr .rsp - BitVec.ofNat 64 bytes + 8 = s.gpr .rsp - BitVec.ofNat 64 (bytes - 8) :=
    sub_add_eight _ (by omega)
  have hbufs : Sig.bufs (sig.withScratch nm e n).params
      (regArgs sig s ++ [s.gpr .rsp - BitVec.ofNat 64 bytes + 8]) =
      Sig.bufs sig.params (regArgs sig s) ++
        [(⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩, true)] :=
    Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _ hlen
  -- The stack below `rsp` that the contract without the buffer reserves.
  have hbelow : below (s.gpr .rsp) (stack + bytes) ∈
      (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (stack + bytes) : List Region) := by
    rw [stackBelow_pos _ (by omega)]; simp
  have hscrSub : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩
      (below (s.gpr .rsp) (stack + bytes)) := by
    rw [hscr]; exact Offset.sub_below _ (by omega) (by omega)
  have hslot : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, 8⟩ (below (s.gpr .rsp) (stack + bytes)) :=
    Offset.sub_below _ (by omega) (by omega)
  have hscrD : ∀ a ∈ Sig.bufs sig.params (regArgs sig s),
      a.1.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩ :=
    fun a ha => (Region.Disjoint.symm (hres _ hbelow a ha)).sub_right hscrSub
  refine (pre_regs (sig := sig.withScratch nm e n) (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega)
    (Sig.noLists_withScratch nm e n hl)).mpr ?_
  rw [narrow_regArgs hk, hbufs, narrow_rsp hk]
  refine ⟨.inr ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [toNat_sub_ofNat (by omega)]; omega
  · simp only [narrow_rd, hrd, List.filter_append, List.map_append]; simp
  · simp only [narrow_wr, hwr, List.filter_append, List.map_append]; simp
  · refine List.pairwise_append.mpr ⟨hpw, List.pairwise_singleton _ _, fun a ha b hb _ => ?_⟩
    simp only [List.mem_singleton] at hb; subst hb
    exact hscrD a ha
  · intro x hx a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact (hres _ hbelow a ha).sub_left hslot
      · rcases Nat.eq_zero_or_pos stack with h0 | h0
        · subst h0; simp [stackBelow] at hx
        · rw [stackBelow_pos _ h0, List.mem_singleton] at hx; subst hx
          exact (hres _ hbelow a ha).sub_left (below_below _ bytes stack)
    · simp only [List.mem_singleton] at ha; subst ha
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Offset.base_disjoint _ (e := 8) (k := 8) (Nat.le_refl _) (by omega)
      · rcases Nat.eq_zero_or_pos stack with h0 | h0
        · subst h0; simp [stackBelow] at hx
        · rw [stackBelow_pos _ h0, List.mem_singleton] at hx; subst hx
          exact Region.Disjoint.symm (Offset.disjoint_below _ (n := stack) (d := 8) (k := n * e.size) (by omega))
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hnw a ha
    · simp only [List.mem_singleton] at ha; subst ha
      show (s.gpr .rsp - BitVec.ofNat 64 bytes + 8).toNat + n * e.size ≤ 2 ^ 64
      rw [hscr, toNat_sub_ofNat (by omega)]; omega
  · exact Eq.mpr (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params pre _ _ hlen) s.mem) hpr

/-- The public data of the contract without the buffer is public in
`narrow` for the contract with it. -/
theorem narrow_pub (hk : (sig.words abi.ptrBits).length < 6) {s₁ s₂ : State}
    (hp : (sig.contract abi pre post wa (stack + bytes)).pub s₁ s₂) (hl : Sig.noLists sig.params = true) :
    (Sig.scratchContract abi sig nm e n pre post wa stack).pub (narrow sig e n bytes s₁)
      (narrow sig e n bytes s₂) := by
  rw [pub_regs (by omega) hl] at hp
  obtain ⟨hsp, hpa⟩ := hp
  refine (pub_regs (sig := sig.withScratch nm e n) (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega)
    (Sig.noLists_withScratch nm e n hl)).mpr ?_
  rw [narrow_regArgs hk, narrow_regArgs hk, narrow_rsp hk, narrow_rsp hk, hsp]
  refine ⟨rfl, fun i hi => ?_⟩
  have l₁ := regArgs_length sig s₁ (by omega)
  have l₂ := regArgs_length sig s₂ (by omega)
  have lp := Sig.pubs_length sig.params abi.ptrBits
  have hps : ((sig.withScratch nm e n).params.flatMap (·.2.pubs)) =
      sig.params.flatMap (·.2.pubs) ++ [true] := by
    simp [Sig.withScratch, Param.pubs]
  rw [hps] at hi
  by_cases hik : i < (sig.words abi.ptrBits).length
  · have hW : (((sig.withScratch nm e n).words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64 =
        ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64 := by
      rw [Sig.words_withScratch, List.map_append]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [List.length_map]; exact hik)]
    rw [hW]
    simp only [List.getD_eq_getElem?_getD] at hi hpa ⊢
    rw [List.getElem?_append_left (by rw [l₁]; exact hik),
      List.getElem?_append_left (by rw [l₂]; exact hik)]
    rw [List.getElem?_append_left (by rw [lp]; exact hik)] at hi
    exact hpa i hi
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), l₁, l₂]

/-- The state after the pop of `withStackScratch`'s frame, from the state
`s₃` its code ends in (with the permissions of `narrow`) when it starts in
`s`. -/
def popState (bytes : Nat) (s s₃ : State) : State :=
  { (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)).setReg .rsp
      (s₃.gpr .rsp + BitVec.ofNat 64 bytes) with wr := s.wr }

/-- A run of the code from `narrow s` is a run of `withStackScratch` from
`s`, with the same trace, which keeps what the calling convention requires,
and whose memory and `rax` are those of the code's run. -/
theorem withStackScratch_run {c : Prog isa} (hk : (sig.words abi.ptrBits).length < 6)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0 ∧ 8 + n * e.size ≤ bytes)
    (hst : stack + bytes + 8 ≤ 2 ^ 64) (hsafe : SpSafe c) (hd : c.x86_64Depth ≤ stack) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrow sig e n bytes s) t s₃) (ha : abiPreserved (narrow sig e n bytes s) s₃)
    (hl : Sig.noLists sig.params = true) :
    Exec isa (withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .rax) c) s t
        (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr .rax = s₃.gpr .rax := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hb
  obtain ⟨hr1, hr2, -⟩ := argRegs_scratch _ hk
  rw [pre_regs (by omega) hl] at hs
  obtain ⟨hwf, -, hwr, -, hres, -, -⟩ := hs
  have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hwf with h | h <;> omega
  -- The frame's push, then `setScratch`.
  have hpush : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨hb0, hb1, hb2, by omega⟩
  have hblk := Exec.block (M := isa) (setScratch_run (argRegs.getD (sig.words abi.ptrBits).length .rax)
    (allocState bytes s))
  -- The code, with the permissions of the state after the push.
  have hcov : Covers (s.wr ++ [⟨s.gpr .rsp - BitVec.ofNat 64 bytes + 8, n * e.size⟩])
      (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) :=
    Covers.append_left (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)
      (Covers.one ⟨_, List.mem_cons_self .., Offset.contains_base _ (d := 8) (by omega) (by omega)⟩)
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)
    (by simpa using Covers.append (Covers.refl s.rd) hcov) (by simpa using hcov)
  rw [show (narrow sig e n bytes s).withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) =
      scratchState (argRegs.getD (sig.words abi.ptrBits).length .rax) (allocState bytes s) from rfl] at hw
  -- The pop.
  have hrsp₃ : s₃.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 bytes :=
    (ha.1 .rsp (by simp [calleeSaved])).trans (narrow_rsp hk s)
  have hpop : isa.pop (.free bytes) (allocState bytes s)
      (s₃.withRegions s.rd (⟨s.gpr .rsp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) =
      some (popState bytes s s₃) := by
    simp only [isa, pop, State.withRegions_gpr, State.withRegions_wr]
    refine ite_eq_left ⟨hb0, hb1, hb2, ?_, rfl, ?_⟩
    · rw [hrsp₃]; simp [allocState, State.setReg]
    · simp [allocState, State.setReg]
  have hex := Exec.frame hpush (Exec.seq hblk hw) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at hex
  refine ⟨hex, ⟨fun q hq => ?_, ?_, ?_⟩, rfl, ?_⟩
  · -- The callee-saved registers.
    simp only [popState, State.setReg, State.withRegions_gpr]
    by_cases hqs : q = .rsp
    · subst hqs; simp only [ite_true, hrsp₃, BitVec.sub_add_cancel]
    · simp only [hqs, ite_false]
      rw [ha.1 q hq, narrow_gpr hk]
      have hqr : q ≠ argRegs.getD (sig.words abi.ptrBits).length .rax := fun h => hr2 (h ▸ hq)
      simp only [hqr, hqs, ↓reduceIte]
  · -- The return address: the code writes only its buffers and below `rsp`.
    have hf := Exec.stackFrame hsafe he (by omega)
    simp only [narrow_wr, narrow_mem, narrow_rsp hk] at hf
    show s₃.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64
    refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r' hr' => ?_) (by decide)
    rcases List.mem_append.mp hr' with hr' | hr'
    · rcases List.mem_append.mp hr' with hr' | hr'
      · rw [hwr] at hr'
        obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hr'
        exact hres _ (List.mem_cons_self ..) a (List.mem_filter.mp ha').1
      · simp only [List.mem_singleton] at hr'; subst hr'
        have := Offset.disjoint (s.gpr .rsp - BitVec.ofNat 64 bytes) (d := bytes) (n := 8) (e := 8)
          (k := n * e.size) (.inr (by omega)) (by omega) (by omega)
        rwa [BitVec.sub_add_cancel] at this
    · simp only [List.mem_singleton] at hr'; subst hr'
      have := Offset.disjoint_below (s.gpr .rsp - BitVec.ofNat 64 bytes) (n := c.x86_64Depth)
        (d := bytes) (k := 8) (by omega)
      rwa [BitVec.sub_add_cancel] at this
  · -- MXCSR.
    exact ha.2.2
  · simp [popState, State.setReg]

/-- Code verified for a function whose last argument, in a register, is a
scratch buffer of `n` elements `e`, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack (`withStackScratch`). -/
theorem Verified.stackScratch {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hk : (sig.words abi.ptrBits).length < 6)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0 ∧ 8 + n * e.size ≤ bytes)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .rax) c)
      (sig.contract abi pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hsafe := SpSafe.of_all hsp
  have hlen := regArgs_length sig
  -- Every run is the code's run from `narrow`.
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃,
      Exec isa c (narrow sig e n bytes s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrow sig e n bytes s) s₃ ∧
      Exec isa (withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .rax) c) s t
        (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr .rax = s₃.gpr .rax := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_pre hk hb hst hs hl)
    exact ⟨t, s₃, he, hq, withStackScratch_run hk hb hst hsafe hd hs he ha hl⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, hrax⟩ := hrun s hs
    refine ⟨t, _, hex, ha, ?_⟩
    rw [post_regs (by omega)]
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega)).mp hq
    rw [narrow_regArgs hk] at hq'
    rw [hm, hrax]
    exact Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params post
      _ _ (hlen s (by omega))) s.mem) s₃.mem) _) hq'
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1]
    exact hct _ _ _ _ _ _ (narrow_pre hk hb hst h₁ hl) (narrow_pre hk hb hst h₂ hl)
      (narrow_pub hk hp hl) f₁ f₂

end

end VG.X86_64
