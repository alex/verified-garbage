import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# A scratch buffer in a register, on the stack (ARMv7)

`Verified.regScratch`: code verified for a function whose last argument is a
scratch buffer that AAPCS passes in a register `r` (as it does the other
arguments: `ScratchInReg`, `Loc.avoids`, decidable), runs as a function
without that argument when `withRegScratch` allocates the buffer in a frame on
the stack and passes its address in `r`, with `bytes` more bytes of stack. The
code runs from the state after the frame's push with the permissions of the
contract with the argument (`narrowR`), and its run there is its run from that
state (`Exec.widen`), as on AArch64. The return address is in `lr`, which the
code keeps, so the buffer can start at the stack pointer, and nothing is
written to memory: unlike `Verified.stackScratch`, the precondition and
postcondition may read any memory.
-/

namespace VG.Arm

open VG.Impl.StackScratch.Arm VG.Arm.FrameStack

/-- AAPCS passes the buffer in `r`, after the other arguments, all in
registers. -/
abbrev ScratchInReg (sig : Sig) (r : Reg) : Prop :=
  r ∈ argRegs ∧ nsaa sig = 0 ∧ classify (widths sig ++ [32]) 0 0 = (locs sig ++ [.reg r], 0)

/-- `l` is in registers among `r0`–`r3` other than `r`. -/
def Loc.avoids (r : Reg) : Loc → Bool
  | .reg q => decide (q ∈ argRegs) && decide (q ≠ r)
  | .pair lo hi => decide (lo ∈ argRegs) && decide (lo ≠ r) && decide (hi ∈ argRegs) && decide (hi ≠ r)
  | .stack .. => false

/-- An argument in registers that `s'` keeps has the same value in both. -/
theorem Loc.val_avoids {r : Reg} {s s' : State} (hr : ∀ q, q ≠ r → s'.gpr q = s.gpr q) :
    ∀ l : Loc, l.avoids r = true → l.val s' = l.val s
  | .reg q, h => by
    simp only [Loc.avoids, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Loc.val, hr q h.2]
  | .pair lo hi, h => by
    simp only [Loc.avoids, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Loc.val, hr lo h.1.1.2, hr hi h.2]
  | .stack .., h => by simp [Loc.avoids] at h

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes : Nat} {r : Reg}

theorem armArgs_withScratch_reg (hcl : ScratchInReg sig r) (nm : String) (e : Elem) (n : Nat)
    (s : State) :
    armArgs (sig.withScratch nm e n) s = (locs sig).map (Loc.val s) ++ [(s.gpr r).setWidth 64] := by
  rw [armArgs, locs, widths_withScratch, hcl.2.2, List.map_append]
  rfl

theorem nsaa_withScratch_reg (hcl : ScratchInReg sig r) (nm : String) (e : Elem) (n : Nat) :
    nsaa (sig.withScratch nm e n) = 0 := by
  rw [nsaa, widths_withScratch, hcl.2.2]

theorem argArea_eq_nil {sig : Sig} (h : nsaa sig = 0) (s : State) : argArea sig s = [] := by
  simp [argArea, h]

/-- The state after the push of the frame and passing the buffer's address
in `r`. -/
def regState (bytes : Nat) (r : Reg) (s : State) : State :=
  (allocState bytes s).setReg r ((allocState bytes s).sp + BitVec.ofNat 32 0)

/-- The state the code runs from, with the permissions of the contract with
the buffer: `regState`, which may read `s.rd` and write `s.wr` and the
buffer. -/
def narrowR (e : Elem) (n bytes : Nat) (r : Reg) (s : State) : State :=
  (regState bytes r s).withRegions s.rd
    (s.wr ++ [⟨State.addr (s.sp - BitVec.ofNat 32 bytes), n * e.size⟩])

@[simp] theorem narrowR_mem (s : State) : (narrowR e n bytes r s).mem = s.mem := rfl
@[simp] theorem narrowR_rd (s : State) : (narrowR e n bytes r s).rd = s.rd := rfl
@[simp] theorem narrowR_wr (s : State) :
    (narrowR e n bytes r s).wr = s.wr ++ [⟨State.addr (s.sp - BitVec.ofNat 32 bytes), n * e.size⟩] :=
  rfl
@[simp] theorem narrowR_sp (s : State) : (narrowR e n bytes r s).sp = s.sp - BitVec.ofNat 32 bytes :=
  rfl
theorem narrowR_gpr (s : State) (q : Reg) :
    (narrowR e n bytes r s).gpr q = if q = r then s.sp - BitVec.ofNat 32 bytes else s.gpr q := by
  simp only [narrowR, regState, State.withRegions_gpr, State.setReg, allocState_sp, allocState_gpr,
    BitVec.add_zero]

theorem narrowR_armArgs (hcl : ScratchInReg sig r) (hloc : (locs sig).all (Loc.avoids r) = true)
    (s : State) :
    armArgs (sig.withScratch nm e n) (narrowR e n bytes r s) =
      armArgs sig s ++ [State.addr (s.sp - BitVec.ofNat 32 bytes)] := by
  rw [armArgs_withScratch_reg hcl]
  refine congr (congrArg HAppend.hAppend (List.map_congr_left fun l hl =>
    Loc.val_avoids (fun q hq => ?_) l (List.all_eq_true.mp hloc l hl))) ?_
  · rw [narrowR_gpr]; simp only [hq, ↓reduceIte]
  · rw [narrowR_gpr]; simp only [↓reduceIte]; rfl

/-- The sizes `withRegScratch` needs. -/
abbrev FitsR (bytes : Nat) (e : Elem) (n : Nat) : Prop :=
  0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0 ∧ encodable (BitVec.ofNat 32 bytes) = true ∧
    n * e.size ≤ bytes

/-- The precondition of the contract without the buffer gives the one with it
in `narrowR`. -/
theorem narrowR_pre (hcl : ScratchInReg sig r) (hloc : (locs sig).all (Loc.avoids r) = true)
    (hb : FitsR bytes e n) {s : State} (hs : (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true) :
    (Sig.scratchContract abi sig nm e n pre post wa stack).pre (narrowR e n bytes r s) := by
  obtain ⟨hb0, -, -, -, hb4⟩ := hb
  rw [pre_arm hl] at hs
  obtain ⟨⟨hst, -⟩, hrd, hwr, hpw, hres, hnw, hpr⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by omega
  have hlt := s.sp.isLt
  have hsp : State.addr (s.sp - BitVec.ofNat 32 bytes) = State.addr s.sp - BitVec.ofNat 64 bytes :=
    addr_sub' (by omega)
  have hE : (State.addr s.sp).toNat = s.sp.toNat := by
    simp only [State.addr, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  have hlen := armArgs_length sig s
  have hnil := argArea_eq_nil hcl.2.1 s
  rw [allRegions, hnil, List.append_nil] at hrd hwr hpw hres
  have hbufs : Sig.bufs (sig.withScratch nm e n).params
      (armArgs sig s ++ [State.addr (s.sp - BitVec.ofNat 32 bytes)]) =
      Sig.bufs sig.params (armArgs sig s) ++
        [(⟨State.addr (s.sp - BitVec.ofNat 32 bytes), n * e.size⟩, true)] :=
    Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _ hlen
  have hbelow : (⟨State.addr s.sp - BitVec.ofNat 64 (stack + bytes), stack + bytes⟩ : Region) ∈
      stackBelow (State.addr s.sp) (stack + bytes) := by
    rw [show stack + bytes = (stack + bytes - 1) + 1 by omega]; simp [stackBelow]
  have hout : ∀ a ∈ Sig.bufs sig.params (armArgs sig s), ∀ {x k : Nat}, x ≤ stack + bytes →
      stack + bytes - x + k ≤ stack + bytes →
      a.1.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 x, k⟩ := fun a ha _ _ hx hk =>
    (Region.Disjoint.symm (hres _ hbelow a ha)).sub_right (Offset.sub_below _ hx hk)
  refine (pre_arm (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (Sig.noLists_withScratch nm e n hl)).mpr ?_
  rw [allRegions, narrowR_armArgs hcl hloc, argArea_eq_nil (nsaa_withScratch_reg hcl nm e n), hbufs,
    nsaa_withScratch_reg hcl, narrowR_sp, List.append_nil]
  refine ⟨⟨.inr ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sub_toNat' (by omega)]; omega
  · rw [sub_toNat' (by omega)]; omega
  · simp only [narrowR_rd, hrd, List.filter_append, List.map_append]; simp
  · simp only [narrowR_wr, hwr, List.filter_append, List.map_append]; simp
  · refine List.pairwise_append.mpr ⟨hpw, List.pairwise_singleton _ _, fun a ha b hb _ => ?_⟩
    simp only [List.mem_singleton] at hb; subst hb
    rw [hsp]; exact hout a ha (by omega) (by omega)
  · intro x hx a ha
    rw [hsp, stackBelow_sub] at hx
    by_cases h0 : stack = 0
    · simp [h0] at hx
    simp only [h0, ite_false, List.mem_singleton] at hx; subst hx
    rcases List.mem_append.mp ha with ha | ha
    · exact Region.Disjoint.symm (hout a ha (by omega) (by omega))
    · simp only [List.mem_singleton] at ha; subst ha
      rw [hsp]
      exact below_disjoint _ (stack + bytes) (a := bytes + stack) (n := stack) (b := bytes)
        (k := n * e.size) (by omega) (by omega) (.inl (by omega)) (by omega) (by omega)
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hnw a ha
    · simp only [List.mem_singleton] at ha; subst ha
      show (State.addr (s.sp - BitVec.ofNat 32 bytes)).toNat + n * e.size ≤ 2 ^ 32
      rw [hsp, toNat_sub64 (by omega), hE]; omega
  · exact Eq.mpr (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params pre _ _ hlen) s.mem) hpr

/-- The public data of the contract without the buffer is public in
`narrowR` for the contract with it. -/
theorem narrowR_pub (hcl : ScratchInReg sig r) (hloc : (locs sig).all (Loc.avoids r) = true)
    {s₁ s₂ : State} (hp : (sig.contract abi pre post wa (stack + bytes)).pub s₁ s₂) (hl : Sig.noLists sig.params = true) :
    (Sig.scratchContract abi sig nm e n pre post wa stack).pub (narrowR e n bytes r s₁)
      (narrowR e n bytes r s₂) := by
  rw [pub_arm hl] at hp
  obtain ⟨hsp, hpa⟩ := hp
  refine (pub_arm (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (Sig.noLists_withScratch nm e n hl)).mpr ?_
  rw [narrowR_armArgs hcl hloc, narrowR_armArgs hcl hloc, narrowR_sp, narrowR_sp, hsp]
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

/-- A run of the code from `narrowR s` is a run of `withRegScratch` from `s`,
with the same trace, which keeps what the calling convention requires, and
whose memory and registers are those of the code's run. -/
theorem withRegScratch_run {c : Prog isa} (hcl : ScratchInReg sig r) (hb : FitsR bytes e n)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes)).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrowR e n bytes r s) t s₃) (ha : abiPreserved (narrowR e n bytes r s) s₃)
    (hl : Sig.noLists sig.params = true) :
    Exec isa (withRegScratch bytes r c) s t (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hb
  rw [pre_arm hl] at hs
  obtain ⟨⟨hst, -⟩, -, -, -, -, -, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by omega
  have hsp : State.addr (s.sp - BitVec.ofNat 32 bytes) = State.addr s.sp - BitVec.ofNat 64 bytes :=
    addr_sub' (by omega)
  have hpush : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push]
    exact ite_eq_left ⟨hb0, hb1, hb2, hb3, by omega⟩
  have hblk : Exec isa (.block [.addSp r 0]) (allocState bytes s) [] (regState bytes r s) :=
    .block (by simp only [execBlock, isa, exec, show (0 : Nat) < 256 by decide, ite_true,
      Option.map_some, addrs, List.map_nil, List.append_nil, regState])
  have hcov : Covers (s.wr ++ [⟨State.addr (s.sp - BitVec.ofNat 32 bytes), n * e.size⟩])
      (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) :=
    Covers.append_left (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)
      (Covers.one ⟨_, List.mem_cons_self .., by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩)
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr)
    (by simpa using Covers.append (Covers.refl s.rd) hcov) (by simpa using hcov)
  rw [show (narrowR e n bytes r s).withRegions s.rd
      (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) = regState bytes r s from rfl] at hw
  have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 32 bytes := ha.2.trans (narrowR_sp s)
  have hpop : isa.pop (.free bytes) (allocState bytes s)
      (s₃.withRegions s.rd (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr)) =
      some (popState bytes s s₃) := by
    simp only [isa, pop, State.withRegions_sp, State.withRegions_wr, allocState_sp, allocState_wr,
      hsp₃, List.head?_cons, hb0, hb1, hb2, hb3, and_self, ite_true, List.tail_cons,
      BitVec.sub_add_cancel]
    rfl
  have hex := Exec.frame hpush (Exec.seq hblk hw) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at hex
  refine ⟨hex, ⟨fun q hq => ?_, rfl⟩, rfl, rfl⟩
  have hpa : ∀ q ∈ preserved, q ∉ argRegs := by decide
  have hqr : q ≠ r := fun h => hpa q hq (h ▸ hcl.1)
  show s₃.gpr q = s.gpr q
  rw [ha.1 q hq, narrowR_gpr]
  simp only [hqr, ↓reduceIte]

/-- Code verified for a function whose last argument, in a register `r`, is a
scratch buffer of `n` elements `e`, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack (`withRegScratch`). The other arguments are in
registers too (`hcl`, `hloc`). -/
theorem Verified.regScratch {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack))
    (hcl : ScratchInReg sig r) (hloc : (locs sig).all (Loc.avoids r) = true) (hb : FitsR bytes e n)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (withRegScratch bytes r c) (sig.contract abi pre post wa (stack + bytes)) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hlen := armArgs_length sig
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃,
      Exec isa c (narrowR e n bytes r s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrowR e n bytes r s) s₃ ∧
      Exec isa (withRegScratch bytes r c) s t (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowR_pre hcl hloc hb hs hl)
    exact ⟨t, s₃, he, hq, withRegScratch_run hcl hb hs he ha hl⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, hg⟩ := hrun s hs
    refine ⟨t, _, hex, ha, ?_⟩
    rw [post_arm]
    have hq' := (post_arm (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)).mp hq
    rw [narrowR_armArgs hcl hloc] at hq'
    rw [hm, hg]
    exact Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params post
      _ _ (hlen s)) s.mem) s₃.mem) _) hq'
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1]
    exact hct _ _ _ _ _ _ (narrowR_pre hcl hloc hb h₁ hl) (narrowR_pre hcl hloc hb h₂ hl)
      (narrowR_pub hcl hloc hp hl) f₁ f₂

end

end VG.Arm
