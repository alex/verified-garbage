import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Setup
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Layout
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

def value (E : BitVec 32) (m : Mem) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => E + BitVec.ofNat 32 d
  | .caller j d => m.readW (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 32 + BitVec.ofNat 32 d

def valid : Value → Prop
  | .const n => n < 65536
  | .frame d => d < 256
  | .caller j d => j < 6 ∧ d < 256

structure SetupStep (rs : List Reg) (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = s.mem
  regs : ∀ r, r ∉ rs → t.gpr r = s.gpr r

theorem SetupStep.refl (s : State) : SetupStep [] s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem SetupStep.trans {rs rs' : List Reg} {s t u : State}
    (h : SetupStep rs s t) (h' : SetupStep rs' t u) : SetupStep (rs ++ rs') s u := by
  refine ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp,
    h'.mem.trans h.mem, ?_⟩
  intro r hr
  exact (h'.regs r (fun hmem => hr (List.mem_append_right _ hmem))).trans
    (h.regs r (fun hmem => hr (List.mem_append_left _ hmem)))

theorem setArg_ok {s : State} {E : BitVec 32} {r : Reg} {v : Value}
    (he : s.sp = E) (hE : E.toNat + 272 ≤ 2^32) (hv : valid v)
    (hr : ∀ j d, v = .caller j d → InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4) :
    WP isa (.block (setArg r v)) s fun t => SetupStep [r] s t ∧ t.gpr r = value E s.mem v := by
  cases v with
  | const n =>
    change n < 65536 at hv
    have hn : (BitVec.ofNat 16 n).setWidth 32 = BitVec.ofNat 32 n := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
    apply WP.of_runBlock
    simp only [setArg, value, runBlock_cons, runStep_some, runBlock_nil, exec,
      hn, Option.some.injEq, exists_eq_left']
    refine ⟨⟨rfl,rfl,rfl,rfl,?_⟩, RegUpd.gpr_setReg_self ..⟩
    intro q hq
    exact RegUpd.gpr_setReg_of_ne s _ (by simpa using hq)
  | frame d =>
    change d < 256 at hv
    apply WP.of_runBlock
    simp only [setArg, value, runBlock_cons, runStep_some, runBlock_nil, exec,
      hv, ite_true, he, Option.some.injEq, exists_eq_left']
    refine ⟨⟨rfl,rfl,rfl,rfl,?_⟩, RegUpd.gpr_setReg_self ..⟩
    intro q hq
    exact RegUpd.gpr_setReg_of_ne s _ (by simpa using hq)
  | caller j d =>
    obtain ⟨hj,hd⟩ := hv
    have ha : 248 + 4*j < 4096 := by omega
    have he' : State.addr (E + BitVec.ofNat 32 (248 + 4*j)) =
        State.addr E + BitVec.ofNat 64 (248 + 4*j) := addr_add (by omega)
    have enc : encodable (BitVec.ofNat 32 d) = true := by
      apply List.any_eq_true.mpr
      refine ⟨0, by decide, ?_⟩
      simp only [Nat.mul_zero, BitVec.rotateLeft, BitVec.rotateLeftAux, Nat.zero_mod, Nat.sub_zero,
        BitVec.shiftLeft_zero, BitVec.ushiftRight_eq_zero (Nat.le_refl 32), BitVec.or_zero,
        BitVec.toNat_ofNat, decide_eq_true_eq]
      omega
    have hr' := hr j d rfl
    apply WP.of_runBlock
    simp only [setArg,value,runBlock_cons,runStep_some,runBlock_nil,exec,
      ha,ite_true,he,he',State.load32,hr',Option.map_some,Op2.eval,enc,
      RegUpd.gpr_setReg_self,Option.some.injEq,exists_eq_left']
    refine ⟨⟨rfl,rfl,rfl,rfl,?_⟩, True.intro⟩
    intro q hq
    have hqr : q ≠ r := by simpa using hq
    rw [RegUpd.gpr_setReg_of_ne _ _ hqr,RegUpd.gpr_setReg_of_ne _ _ hqr]

/-- Setup does not touch memory and writes each destination exactly once. -/
theorem setupRegs_ok {s : State} {E : BitVec 32} {args : List (Reg × Value)}
    (he : s.sp = E) (hE : E.toNat + 272 ≤ 2^32) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, valid p.2)
    (hr : ∀ j < 6, InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4) :
    WP isa (.block (args.flatMap fun (r,v) => setArg r v)) s fun t => SetupStep (args.map Prod.fst) s t ∧
      ∀ p ∈ args, t.gpr p.1 = value E s.mem p.2 := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨SetupStep.refl s, fun _ h => by cases h⟩
  | cons p ps ih =>
    obtain ⟨r, v⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [List.flatMap_cons, WP.block_append_iff]
    have hv0 := hv (r,v) List.mem_cons_self
    refine WP.mono (setArg_ok he hE hv0 ?_) fun u ⟨hu, hval⟩ => ?_
    · intro j d h
      subst v
      exact hr j hv0.1
    refine WP.mono (ih (hu.sp.trans he) hn.2
      (fun p hp => hv p (List.mem_cons_of_mem _ hp)) ?_) fun t ⟨ht, hvals⟩ => ?_
    · intro j hj
      rw [hu.rd, hu.wr]
      exact hr j hj
    refine ⟨hu.trans ht, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (ht.regs r hn.1).trans hval
    · rw [hvals p hp, hu.mem]


/-- Values only read the saved arguments, beyond the outgoing stack slots. -/
theorem value_frame {E : BitVec 32} {m m' : Mem}
    (hf : Frame [⟨State.addr E,24⟩] m m') {v : Value} (hv : valid v) :
    value E m' v = value E m v := by
  cases v with
  | const n => rfl
  | frame d => rfl
  | caller j d =>
    obtain ⟨hj,hd⟩ := hv
    unfold value
    apply congrArg (· + BitVec.ofNat 32 d)
    refine hf.readW (r := ⟨State.addr E + BitVec.ofNat 64 (248+4*j),4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint_base _ (d := 248+4*j) (by omega) (by omega)

structure StackStep (E : BitVec 32) (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  regs : ∀ r, r ≠ .r0 → r ≠ .r12 → t.gpr r = s.gpr r
  frame : Frame [⟨State.addr E,24⟩] s.mem t.mem

theorem StackStep.refl (E : BitVec 32) (s : State) : StackStep E s s :=
  ⟨rfl,rfl,rfl,fun _ _ _ => rfl,Frame.refl _ _⟩

theorem StackStep.trans {E : BitVec 32} {s t u : State}
    (h : StackStep E s t) (h' : StackStep E t u) : StackStep E s u :=
  ⟨h'.rd.trans h.rd,h'.wr.trans h.wr,h'.sp.trans h.sp,
    fun r h0 h12 => (h'.regs r h0 h12).trans (h.regs r h0 h12),h.frame.trans h'.frame⟩

theorem putArg_ok {s : State} {E : BitVec 32} {j : Nat} {v : Value}
    (he : s.sp = E) (hE : E.toNat+272 ≤ 2^32) (hj : j < 6) (hv : valid v)
    (hr : ∀ i < 6, InRegions (s.rd++s.wr) (State.addr E+BitVec.ofNat 64 (248+4*i)) 4)
    (hw : InRegions s.wr (State.addr E+BitVec.ofNat 64 (4*j)) 4) :
    WP isa (.block (putArg j v)) s fun t => StackStep E s t ∧
      t.mem = s.mem.writeW (State.addr E+BitVec.ofNat 64 (4*j)) (value E s.mem v) := by
  rw [putArg,WP.block_append_iff]
  refine WP.mono (setArg_ok he hE hv ?_) fun u ⟨hu,hval⟩ => ?_
  · intro i d h
    subst v
    exact hr i hv.1
  have hoff : 4*j < 256 := by omega
  have ha : State.addr (E+BitVec.ofNat 32 (4*j)) = State.addr E+BitVec.ofNat 64 (4*j) :=
    addr_add (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,hoff,ite_true,
    State.store32,Nat.reduceLT,RegUpd.gpr_setReg,RegUpd.wr_setReg,reduceCtorEq,
    ite_false,BitVec.add_zero,hu.sp,he,ha,hu.wr,hw,RegUpd.mem_setReg,hu.mem,
    hval,Option.some.injEq,exists_eq_left']
  refine ⟨⟨hu.rd,rfl,hu.sp,?_,?_⟩,True.intro⟩
  · intro r h0 h12
    rw [RegUpd.gpr_setReg_of_ne _ _ h12]
    exact hu.regs r (by simpa using h0)
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))

structure StackReady (E : BitVec 32) (s : State) (start : Nat) (vs : List Value) (t : State) : Prop where
  step : StackStep E s t
  frame : Frame [⟨State.addr E + BitVec.ofNat 64 (4*start),4*vs.length⟩] s.mem t.mem
  words : ∀ j (hj : j < vs.length), t.mem.readW (State.addr E+BitVec.ofNat 64 (4*(start+j))) 32 = value E s.mem (vs[j]'hj)


theorem setupStack_ok {E : BitVec 32} (hE : E.toNat+272 ≤ 2^32)
    {s : State} {start : Nat} {vs : List Value}
    (he : s.sp = E) (hs : start+vs.length ≤ 6)
    (hv : ∀ v ∈ vs, valid v)
    (hr : ∀ j < 6, InRegions (s.rd++s.wr) (State.addr E+BitVec.ofNat 64 (248+4*j)) 4)
    (hw : ∀ j < 6, InRegions s.wr (State.addr E+BitVec.ofNat 64 (4*j)) 4) :
    WP isa (.block (setupStack start vs)) s (StackReady E s start vs) := by
  induction vs generalizing s start with
  | nil => exact WP.block_nil ⟨.refl _ _,Frame.refl _ _,fun j hj => by simp at hj⟩
  | cons v vs ih =>
    rw [setupStack,WP.block_append_iff]
    have hj : start < 6 := by simp only [List.length_cons] at hs; omega
    refine WP.mono (putArg_ok he hE hj (hv v List.mem_cons_self) hr (hw start hj)) fun u ⟨hu,hmem⟩ => ?_
    refine WP.mono (ih (hu.sp.trans he) (by simp only [List.length_cons] at hs; omega)
      (fun v hv' => hv v (List.mem_cons_of_mem _ hv'))
      (by intro j hj; rw [hu.rd,hu.wr]; exact hr j hj)
      (by intro j hj; rw [hu.wr]; exact hw j hj)) fun t ht => ?_
    refine ⟨hu.trans ht.step,?_,?_⟩
    · have first : Frame [⟨State.addr E+BitVec.ofNat 64 (4*start),4*(v::vs).length⟩] s.mem u.mem := by
        rw [hmem]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (by simp only [Region.Contains,BitVec.sub_self,BitVec.toNat_zero,Nat.zero_add,List.length_cons]; omega)
      refine first.trans (Frame.sub ht.frame ?_)
      intro r hr
      rw [List.mem_singleton.mp hr]
      refine ⟨_,List.mem_singleton_self _,?_⟩
      exact Offset.sub _ (by omega) (by simp only [List.length_cons]; omega)
    · intro j hj'
      cases j with
      | zero =>
        simp only [Nat.add_zero,List.getElem_cons_zero]
        rw [ht.frame.readW (r := ⟨State.addr E+BitVec.ofNat 64 (4*start),4⟩)
          (Region.contains_self _ _) (by
            intro r hr
            rw [List.mem_singleton.mp hr]
            exact Offset.disjoint _ (by omega) (by omega) (by simp only [List.length_cons] at hs; omega)) (by decide)]
        rw [hmem,Mem.readW_writeW_self32]
      | succ j =>
        have hj : j < vs.length := by simpa using hj'
        have hw' := ht.words j hj
        rw [value_frame hu.frame (hv vs[j] (List.mem_cons_of_mem _ (List.getElem_mem hj)))] at hw'
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 j] using hw'

theorem Ctx.setup {E : BitVec 32} {g : Reg → BitVec 32}
    {m₀ : Mem} {rd wr : List Region} {s : State} (hc : Ctx E g m₀ rd wr s)
    (hE : E.toNat+272 ≤ 2^32)
    {args : List (Reg × Value)} {stack : List Value}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, valid p.2)
    (hs : stack.length ≤ 6) (hvs : ∀ v ∈ stack, valid v)
    (hr : ARGS E ∈ rd) (hregs : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setup args stack)) s fun t => Ctx E g m₀ rd wr t ∧
      Frame [⟨State.addr E,24⟩] s.mem t.mem ∧
      (∀ p ∈ args, t.gpr p.1 = value E s.mem p.2) ∧
      (∀ j (hj : j < stack.length), stackArg t j = value E s.mem (stack[j]'hj)) := by
  have read : ∀ j < 6, InRegions (s.rd++s.wr) (State.addr E+BitVec.ofNat 64 (248+4*j)) 4 := by
    intro j hj
    rw [hc.rd,hc.wr]
    refine ⟨ARGS E,List.mem_append_left _ hr,?_⟩
    exact Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)
  have write : ∀ j < 6, InRegions s.wr (State.addr E+BitVec.ofNat 64 (4*j)) 4 := by
    intro j hj
    exact hc.writable_frame (Offset.contains_base _ (by omega) (by omega))
  rw [Impl.Ed25519.Arm.Whole.setup,WP.block_append_iff]
  refine WP.mono (setupStack_ok hE hc.sp (by simpa using hs) hvs read write) fun u hu => ?_
  refine WP.mono (setupRegs_ok (hu.step.sp.trans hc.sp) hE hn hv
    (by intro j hj; rw [hu.step.rd,hu.step.wr]; exact read j hj)) fun t ⟨ht,hvals⟩ => ?_
  have hcu : Ctx E g m₀ rd wr u := by
    refine hc.of_frame hu.step.rd hu.step.wr hu.step.sp ?_ hu.step.frame ?_
    · intro r hr _
      exact hu.step.regs r (by intro h; subst r; exact (by decide : Reg.r0 ∉ preserved) hr) (by intro h; subst r; exact (by decide : Reg.r12 ∉ preserved) hr)
    · intro R hR
      rw [List.mem_singleton.mp hR]
      exact .inl (Region.sub_prefix (by decide))
  have hct : Ctx E g m₀ rd wr t := by
    refine hcu.regs ht.rd ht.wr ht.sp ?_ ht.mem
    intro r hpres _
    apply ht.regs
    intro hm
    obtain ⟨p,hp,heq⟩ := List.mem_map.mp hm
    exact hregs p hp (heq ▸ hpres)
  refine ⟨hct,ht.mem ▸ hu.step.frame,?_,?_⟩
  · intro p hp
    rw [hvals p hp,value_frame hu.step.frame (hv p hp)]
  · intro j hj
    have hsp : t.sp = E := ht.sp.trans (hu.step.sp.trans hc.sp)
    have ha : State.addr (E+BitVec.ofNat 32 (4*j)) = State.addr E+BitVec.ofNat 64 (4*j) :=
      addr_add (by omega)
    simp only [stackArg,stackArgAddr,hsp,ha,ht.mem]
    simpa only [Nat.zero_add] using hu.words j hj

end VG.Proof.Ed25519.Arm.Whole
