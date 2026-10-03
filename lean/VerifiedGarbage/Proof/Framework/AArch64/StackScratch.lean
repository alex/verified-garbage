import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-!
# A scratch buffer on the stack (AArch64)

`Verified.stackScratch`: code verified for a function whose last argument,
passed in a register, is a scratch buffer (its contract
`Sig.scratchContract`), runs as a function without that argument when
`withStackScratch` allocates the buffer in a frame on the stack, with
`bytes` more bytes of stack. The code runs from the state after the frame's
push with the permissions of the contract with the argument (`narrow`), and
its run there is its run from that state (`Exec.widen`). The return address
is in `x30`, which the code keeps, so the buffer can start at the stack
pointer.
-/

namespace VG.AArch64

open VG.Impl.StackScratch.AArch64

/-- The arguments of a function with signature `sig`, all in registers. -/
abbrev regArgs (sig : Sig) (s : State) : List (BitVec 64) :=
  (argRegs.take (sig.words abi.ptrBits).length).map s.gpr

theorem stackBelow_pos (sp : Addr) {n : Nat} (h : 0 < n) : stackBelow sp n = [below sp n] := by
  cases n with
  | zero => omega
  | succ n => rfl

theorem Region.contains_self' {a : Addr} {n k : Nat} (h : n ≤ k) :
    (⟨a, k⟩ : Region).Contains a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem toNat_sub_ofNat' {a : Addr} {k : Nat} (h : k ≤ a.toNat) :
    (a - BitVec.ofNat 64 k).toNat = a.toNat - k := by
  have := a.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
    show 2 ^ 64 - k + a.toNat = (a.toNat - k) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- The stack below `sp - a`, within the stack below `sp`. -/
theorem below_below (sp : Addr) (a n : Nat) :
    Region.Sub (below (sp - BitVec.ofNat 64 a) n) (below sp (n + a)) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (sp - BitVec.ofNat 64 (n + a)) = x - (sp - BitVec.ofNat 64 a - BitVec.ofNat 64 n) by
    rw [BitVec.sub_sub sp, BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 n)]]
  omega

theorem argRegs_take_succ (g : Reg → BitVec 64) :
    ∀ k < 8, (argRegs.take (k + 1)).map g = (argRegs.take k).map g ++ [g (argRegs.getD k .x0)]
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl
  | 6, _ => rfl | 7, _ => rfl
  | _ + 8, h => absurd h (by omega)

theorem argRegs_scratch :
    ∀ k < 8, argRegs.getD k .x0 ∉ preserved ∧ ∀ q ∈ argRegs.take k, q ≠ argRegs.getD k .x0 := by
  decide

theorem regArgs_length (sig : Sig) (s : State) (hk : (sig.words abi.ptrBits).length ≤ 8) :
    (regArgs sig s).length = (sig.words abi.ptrBits).length := by
  simp only [regArgs, List.length_map, List.length_take, argRegs, List.length_cons, List.length_nil]
  omega

/-- The precondition of a contract whose arguments are all in registers. -/
theorem pre_regs {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State}
    (hk : (sig.words abi.ptrBits).length ≤ 8) :
    (sig.contract abi pre post wa stack leak).pre s ↔
      (stack = 0 ∨ stack ≤ s.sp.toNat) ∧
      s.rd = ((Sig.bufs sig.params (regArgs sig s)).filter (!·.2)).map (·.1) ∧
      s.wr = ((Sig.bufs sig.params (regArgs sig s)).filter (·.2)).map (·.1) ∧
      (Sig.bufs sig.params (regArgs sig s)).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) ∧
      (∀ r ∈ stackBelow s.sp stack, ∀ a ∈ Sig.bufs sig.params (regArgs sig s), r.Disjoint a.1) ∧
      (∀ a ∈ Sig.bufs sig.params (regArgs sig s), a.1.base.toNat + a.1.len ≤ 2 ^ 64) ∧
      Curry.apply (sig.words abi.ptrBits) pre (regArgs sig s) s.mem := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 8 := hk
    simpa [argRegs] using this
  have h0 : (sig.words 64).length - argRegs.length = 0 := by omega
  have hwf : (match stack with | 0 => True | n => n ≤ s.sp.toNat) ↔
      (stack = 0 ∨ stack ≤ s.sp.toNat) := by
    cases stack <;> simp
  simp only [Sig.contract, abi, List.length_map, hk', h0, ite_true, List.map_nil, List.append_nil]
  exact and_congr hwf Iff.rfl

/-- The postcondition of a contract whose arguments are all in registers. -/
theorem post_regs {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s s' : State}
    (hk : (sig.words abi.ptrBits).length ≤ 8) :
    (sig.contract abi pre post wa stack leak).post s s' ↔
      Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem s'.mem
        ((s'.gpr .x0).setWidth _) := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 8 := hk
    simpa [argRegs] using this
  simp only [Sig.contract, abi, List.length_map, hk', ite_true]
  exact Iff.rfl

/-- The public data of a contract whose arguments are all in registers, and
which leaks nothing. -/
theorem pub_regs {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat} {s₁ s₂ : State}
    (hk : (sig.words abi.ptrBits).length ≤ 8) :
    (sig.contract abi pre post wa stack none).pub s₁ s₂ ↔
      s₁.sp = s₂.sp ∧
      ∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((regArgs sig s₁).getD i 0).setWidth
            (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) =
          ((regArgs sig s₂).getD i 0).setWidth
            (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 8 := hk
    simpa [argRegs] using this
  simp only [Sig.contract, abi, List.length_map, hk', ite_true]
  exact Iff.rfl

/-- The value of argument word `i` of `sig` in `satRegs`: `2⁴⁰ (i + 1)` for a
pointer, 0 for an integer. -/
def satArg (sig : Sig) (i : Nat) : BitVec 64 :=
  match (sig.words abi.ptrBits)[i]? with
  | some .addr => BitVec.ofNat 64 (2 ^ 40 * (i + 1))
  | _ => 0

/-- A state for the satisfiability of a contract whose arguments are all in
registers: each pointer `2⁴⁰ (i + 1)`, each integer 0 (so each slice is
empty), `sp` `2⁶³`, and permissions exactly for the buffers. -/
def satRegs (sig : Sig) : State :=
  let g : Reg → BitVec 64 := fun r => match r with
    | .x0 => satArg sig 0 | .x1 => satArg sig 1 | .x2 => satArg sig 2 | .x3 => satArg sig 3
    | .x4 => satArg sig 4 | .x5 => satArg sig 5 | .x6 => satArg sig 6 | .x7 => satArg sig 7
    | _ => 0
  let bufs := Sig.bufs sig.params ((argRegs.take (sig.words abi.ptrBits).length).map g)
  { gpr := g, sp := BitVec.ofNat 64 (2 ^ 63), mem := fun _ => 0,
    rd := (bufs.filter (!·.2)).map (·.1), wr := (bufs.filter (·.2)).map (·.1) }

/-- A contract whose arguments are all in registers is satisfiable if
`satRegs` satisfies what `Sig.check` evaluates and its further
precondition. -/
theorem sat_regs {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hs : stack ≤ 2 ^ 63)
    (hc : Sig.check abi sig wa stack (satRegs sig) = true)
    (hp : Curry.apply (sig.words abi.ptrBits) pre (regArgs sig (satRegs sig)) (fun _ => 0)) :
    ∃ s, (sig.contract abi pre post wa stack).pre s := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 8 := hk
    simpa [argRegs] using this
  refine ⟨satRegs sig, Sig.contract_pre_of_check hc ?_⟩
  simp only [Sig.wfPre, abi, List.length_map, hk', ite_true]
  refine ⟨?_, hp⟩
  cases stack with
  | zero => trivial
  | succ m => simp only [satRegs, BitVec.toNat_ofNat]; omega

/-- `withStackScratch`'s code satisfies `spSafe` (no AArch64 instruction
writes `sp`). -/
theorem withStackScratch_spSafe (bytes : Nat) (r : Reg) (c : Prog isa) :
    (withStackScratch bytes r c).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_forall (fun _ => rfl) _

section
variable {sig : Sig} {nm : String} {e : Elem} {n n' : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes : Nat}

/-- The state after the push of the frame and passing the buffer's address
in the register of the last argument. -/
def scratchState (sig : Sig) (bytes : Nat) (s : State) : State :=
  (allocated bytes s).write .x (argRegs.getD (sig.words abi.ptrBits).length .x0)
    ((allocated bytes s).sp + BitVec.ofNat 64 0)

/-- The state the code runs from, with the permissions of the contract with
the buffer: `scratchState`, which may read `s.rd` and write `s.wr` and the
buffer. -/
def narrow (sig : Sig) (e : Elem) (n bytes : Nat) (s : State) : State :=
  (scratchState sig bytes s).withRegions s.rd (s.wr ++ [⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩])

theorem narrow_gpr (s : State) (q : Reg) :
    (narrow sig e n bytes s).gpr q =
      if q = argRegs.getD (sig.words abi.ptrBits).length .x0 then s.sp - BitVec.ofNat 64 bytes
      else s.gpr q := by
  simp only [narrow, scratchState, State.withRegions, allocated, State.write, BitVec.add_zero,
    BitVec.setWidth_eq]

@[simp] theorem narrow_mem (s : State) : (narrow sig e n bytes s).mem = s.mem := rfl
@[simp] theorem narrow_rd (s : State) : (narrow sig e n bytes s).rd = s.rd := rfl
@[simp] theorem narrow_wr (s : State) :
    (narrow sig e n bytes s).wr = s.wr ++ [⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩] := rfl
@[simp] theorem narrow_v (s : State) : (narrow sig e n bytes s).v = s.v := rfl
@[simp] theorem narrow_sp (s : State) : (narrow sig e n bytes s).sp = s.sp - BitVec.ofNat 64 bytes :=
  rfl

theorem narrow_regArgs (hk : (sig.words abi.ptrBits).length < 8) (s : State) :
    regArgs (sig.withScratch nm e n) (narrow sig e n' bytes s) =
      regArgs sig s ++ [s.sp - BitVec.ofNat 64 bytes] := by
  obtain ⟨-, hr3⟩ := argRegs_scratch _ hk
  simp only [regArgs, Sig.words_withScratch, List.length_append, List.length_singleton]
  rw [argRegs_take_succ _ _ hk]
  congr 1
  · refine List.map_congr_left fun q hq => ?_
    simp only [narrow_gpr, hr3 q hq, ↓reduceIte]
  · simp only [narrow_gpr, ↓reduceIte]

/-- The precondition of the contract without the buffer gives the one with it
in `narrow`. -/
theorem narrow_pre (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) :
    (Sig.scratchContract abi sig nm e n pre post wa stack).pre (narrow sig e n bytes s) := by
  obtain ⟨hb0, -, -, hb3⟩ := hb
  rw [pre_regs (by omega)] at hs
  obtain ⟨hwf, hrd, hwr, hpw, hres, hnw, hpr⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hwf with h | h <;> omega
  have hlen := regArgs_length sig s (by omega)
  have hbufs : Sig.bufs (sig.withScratch nm e n).params (regArgs sig s ++ [s.sp - BitVec.ofNat 64 bytes]) =
      Sig.bufs sig.params (regArgs sig s) ++ [(⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩, true)] :=
    Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _ hlen
  have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
    rw [stackBelow_pos _ (by omega)]; simp
  have hscrSub : Region.Sub ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ (below s.sp (stack + bytes)) :=
    Offset.sub_below _ (by omega) (by omega)
  have hscrD : ∀ a ∈ Sig.bufs sig.params (regArgs sig s),
      a.1.Disjoint ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ :=
    fun a ha => (Region.Disjoint.symm (hres _ hbelow a ha)).sub_right hscrSub
  refine (pre_regs (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega)).mpr ?_
  rw [narrow_regArgs hk, hbufs, narrow_sp]
  refine ⟨.inr ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [toNat_sub_ofNat' (by omega)]; omega
  · simp only [narrow_rd, hrd, List.filter_append, List.map_append]; simp
  · simp only [narrow_wr, hwr, List.filter_append, List.map_append]; simp
  · refine List.pairwise_append.mpr ⟨hpw, List.pairwise_singleton _ _, fun a ha b hb _ => ?_⟩
    simp only [List.mem_singleton] at hb; subst hb
    exact hscrD a ha
  · intro x hx a ha
    rcases Nat.eq_zero_or_pos stack with h0 | h0
    · subst h0; simp [stackBelow] at hx
    rw [stackBelow_pos _ h0, List.mem_singleton] at hx; subst hx
    rcases List.mem_append.mp ha with ha | ha
    · exact (hres _ hbelow a ha).sub_left (below_below _ bytes stack)
    · simp only [List.mem_singleton] at ha; subst ha
      exact Region.Disjoint.symm (Offset.base_disjoint_below _ (n := stack) (k := n * e.size)
        (by omega))
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hnw a ha
    · simp only [List.mem_singleton] at ha; subst ha
      show (s.sp - BitVec.ofNat 64 bytes).toNat + n * e.size ≤ 2 ^ 64
      rw [toNat_sub_ofNat' (by omega)]; omega
  · exact Eq.mpr (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params pre _ _ hlen) s.mem) hpr

/-- The public data of the contract without the buffer is public in
`narrow` for the contract with it. -/
theorem narrow_pub (hk : (sig.words abi.ptrBits).length < 8) {s₁ s₂ : State}
    (hp : (sig.contract abi pre post wa (stack + bytes)).pub s₁ s₂) :
    (Sig.scratchContract abi sig nm e n pre post wa stack).pub (narrow sig e n bytes s₁)
      (narrow sig e n bytes s₂) := by
  rw [pub_regs (by omega)] at hp
  obtain ⟨hsp, hpa⟩ := hp
  refine (pub_regs (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega)).mpr ?_
  rw [narrow_regArgs hk, narrow_regArgs hk, narrow_sp, narrow_sp, hsp]
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
  { s₃.withRegions s.rd (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) with sp := s.sp, wr := s.wr }

/-- A run of the code from `narrow s` is a run of `withStackScratch` from
`s`, with the same trace, which keeps what the calling convention requires,
and whose memory and registers are those of the code's run. -/
theorem withStackScratch_run {c : Prog isa} (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrow sig e n bytes s) t s₃) (ha : abiPreserved (narrow sig e n bytes s) s₃) :
    Exec isa (withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .x0) c) s t
        (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hb
  obtain ⟨hr2, -⟩ := argRegs_scratch _ hk
  rw [pre_regs (by omega)] at hs
  obtain ⟨hwf, -, -, -, -, -, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hwf with h | h <;> omega
  have hpush : isa.push (.alloc bytes) s = some (allocated bytes s) := by
    simp only [isa, push, allocated]
    exact ite_eq_left ⟨hb0, hb1, hb2, by omega⟩
  have hblk : Exec isa (.block [.addSp (argRegs.getD (sig.words abi.ptrBits).length .x0) 0])
      (allocated bytes s) [] (scratchState sig bytes s) :=
    .block (by simp only [execBlock, isa, exec, show (0 : Nat) < 4096 by decide, ite_true,
      Option.map_some, addrs, List.map_nil, List.append_nil, scratchState])
  have hcov : Covers (s.wr ++ [⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩])
      (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) :=
    Covers.append_left (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)
      (Covers.one ⟨_, List.mem_cons_self .., Region.contains_self' (by omega)⟩)
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)
    (by simpa using Covers.append (Covers.refl s.rd) hcov) (by simpa using hcov)
  rw [show (narrow sig e n bytes s).withRegions s.rd (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) =
      scratchState sig bytes s from rfl] at hw
  have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans (narrow_sp s)
  have hpop : isa.pop (.free bytes) (allocated bytes s)
      (s₃.withRegions s.rd (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) =
      some (popState bytes s s₃) := by
    simp only [isa, pop, State.withRegions, allocated, hsp₃, List.head?_cons, List.tail_cons, hb0,
      hb1, hb2, and_self, ite_true, BitVec.sub_add_cancel]
    rfl
  have hex := Exec.frame hpush (Exec.seq hblk hw) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at hex
  refine ⟨hex, ⟨fun q hq => ?_, ?_, fun q hq => ?_⟩, rfl, rfl⟩
  · have hqr : q ≠ argRegs.getD (sig.words abi.ptrBits).length .x0 := fun h => hr2 (h ▸ hq)
    show s₃.gpr q = s.gpr q
    rw [ha.1 q hq, narrow_gpr]
    simp only [hqr, ↓reduceIte]
  · rfl
  · show (s₃.v q).extractLsb' 0 64 = (s.v q).extractLsb' 0 64
    exact ha.2.2 q hq

/-- Code verified for a function whose last argument, in a register, is a
scratch buffer of `n` elements `e`, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack (`withStackScratch`). -/
theorem Verified.stackScratch {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s) :
    Verified target (withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .x0) c)
      (sig.contract abi pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hlen := regArgs_length sig
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃,
      Exec isa c (narrow sig e n bytes s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrow sig e n bytes s) s₃ ∧
      Exec isa (withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .x0) c) s t
        (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_pre hk hb hs)
    exact ⟨t, s₃, he, hq, withStackScratch_run hk hb hs he ha⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, hg⟩ := hrun s hs
    refine ⟨t, _, hex, ha, ?_⟩
    rw [post_regs (by omega)]
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega)).mp hq
    rw [narrow_regArgs hk] at hq'
    rw [hm, hg]
    exact Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params post
      _ _ (hlen s (by omega))) s.mem) s₃.mem) _) hq'
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1]
    exact hct _ _ _ _ _ _ (narrow_pre hk hb h₁) (narrow_pre hk hb h₂) (narrow_pub hk hp) f₁ f₂

end

end VG.AArch64
