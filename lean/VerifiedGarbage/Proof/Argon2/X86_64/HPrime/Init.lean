import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Backend
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Copy

/-! # H′: initializing an unkeyed BLAKE2b computation -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure InitArgs (s t : State) : Prop where
  state : t.gpr .rdi = s.gpr .rbx
  key : t.gpr .rdx = s.gpr .rbx + 832
  keylen : t.gpr .rcx = 0
  other : ∀ r, r ≠ .rdi → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem initArgs_ok (s : State) : WP isa (.block initArgs) s (InitArgs s) := by
  apply WP.of_runBlock
  simp only [initArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, execAlu, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  simp only [State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h1, h2, h3, ite_false]

theorem init_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (hret : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rbx, 192⟩) :
    WP isa (init (hash v)) s fun t =>
      Spec.Blake2.Repr Spec.Blake2.b (Spec.Blake2.init Spec.Blake2.b (s.gpr .rsi).toNat 0)
        t.mem (s.gpr .rbx) [] ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨s.gpr .rbx, 192⟩, below (s.gpr .rsp) 8] s.mem t.mem := by
  unfold init
  refine WP.seq ((initArgs_ok s).mono fun u hu => ?_)
  have hsp : u.gpr .rsp = s.gpr .rsp := hu.other _ (by decide) (by decide) (by decide)
  have hlen' : u.gpr .rsi = s.gpr .rsi := hu.other _ (by decide) (by decide) (by decide)
  have g : ∀ r, r ≠ .rsp → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have hp : (Proof.Blake2.initX86_64 Spec.Blake2.b).pre
      (u.callEntry.withRegions [⟨s.gpr .rbx + 832, 0⟩] [⟨s.gpr .rbx, 192⟩]) := by
    simp only [Proof.Blake2.initX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g _ (by decide : Reg.rdi ≠ .rsp),
      g _ (by decide : Reg.rdx ≠ .rsp), g _ (by decide : Reg.rcx ≠ .rsp),
      g _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_rsp,
      hu.state, hu.key, hu.keylen, hlen', hsp]
    refine ⟨rfl, rfl, ?_, hret, hlen.1, hlen.2, by decide⟩
    exact (Offset.base_disjoint (s.gpr .rbx) (e := 832) (n := 0) (k := 192) (by decide) (by decide)).symm
  have cover : Covers [⟨s.gpr .rbx + 832, 0⟩, ⟨s.gpr .rbx, 192⟩] (u.rd ++ u.wr) := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .rbx, 16384⟩, List.mem_append_right _ (hu.wr.symm ▸ hwr), ?_⟩
    rcases hr with rfl | rfl
    · exact ⟨832, rfl, by change 832 ≤ 16384; decide⟩
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
  have writes : Covers [⟨s.gpr .rbx, 192⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨s.gpr .rbx, 16384⟩, hu.wr.symm ▸ hwr, 0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
  refine WP.call (k := Proof.Blake2.initX86_64 Spec.Blake2.b)
    Proof.Blake2.X86_64.Stream.initB_correct (hash_ok v).initNoSp
    (by decide) hp cover writes ?_
  intro t rd wr cs frame keep ⟨t', hm, hg, post⟩
  have post' := post
  simp only [Proof.Blake2.initX86_64, State.withRegions_gpr, g _ (by decide : Reg.rdi ≠ .rsp),
    g _ (by decide : Reg.rsi ≠ .rsp), g _ (by decide : Reg.rdx ≠ .rsp),
    g _ (by decide : Reg.rcx ≠ .rsp), hu.state, hu.key, hu.keylen, hlen', hm,
    Spec.Blake2.bytesAt, Spec.Blake2.keyBlock] at post'
  refine ⟨post', fun r hr => (cs r hr).trans ?_, rd.trans hu.rd, wr.trans hu.wr, ?_⟩
  · have hn : r ≠ .rdi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2.1 hn.2.2
  · simpa only [show (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b).depth = 0 from rfl, Nat.zero_add, Nat.mul_one, hsp, hu.mem,
      List.singleton_append, List.nil_append] using frame

end VG.Proof.Argon2.X86_64.HPrime
