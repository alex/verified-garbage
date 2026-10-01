import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentBulk
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Backend
import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Resident
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentMath
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentBoundary
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64

/-- The general absorber can run with wider ambient memory regions, including
its existing stack frame. Narrowing changes permissions only, not registers,
SIMD state, memory, or the trace. -/
theorem generic_widen (v : Proof.Sha3.AArch64.Permutation) (s : State)
    (rd wr : List Region)
    (hp : Proof.Sha3.absorbAArch64.pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (Impl.Sha3.AArch64.Stream.absorbGenericWith v.callee) s fun s' =>
      abiPreserved s s' ∧ Proof.Sha3.absorbAArch64.post
        (s.withRegions rd wr) (s'.withRegions rd wr) := by
  obtain ⟨t, q, he, ha, hq⟩ :=
    Stream.Absorb.correct v (Stream.Absorb.pre_of hp).1 (Stream.Absorb.pre_of hp).2
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) hc hw
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  obtain ⟨hr, hw', _⟩ := Exec.rdwr he
  simp only [State.withRegions_rd, State.withRegions_wr] at hr hw'
  have eq : (q.withRegions s.rd s.wr).withRegions rd wr = q := by
    rw [State.withRegions_withRegions, ← hr, ← hw']
    rfl
  exact ⟨t, q.withRegions s.rd s.wr, he', ha, by rw [eq]; exact hq⟩

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Proof.Sha3 (Rep)
open VG.Proof.Sha3.AArch64.Stream.Absorb

/-- An aligned prefix has advanced the input arguments while retaining the
original sponge's meaning, permissions, and preserved registers. -/
structure Tail (a : State) (consumed : Nat) (s : State) : Prop where
  c_le : consumed ≤ Stream.Absorb.len a
  aligned : consumed % rt a = 0
  abi : abiPreserved a s
  rd : s.rd = a.rd
  wr : s.wr = a.wr
  frame : Frame [stR a, scR a] a.mem s.mem
  x0 : s.gpr .x0 = a.gpr .x0
  x1 : s.gpr .x1 = a.gpr .x1
  x2 : s.gpr .x2 = a.gpr .x2
  x3 : s.gpr .x3 = dp a + BitVec.ofNat 64 consumed
  x4 : s.gpr .x4 = BitVec.ofNat 64 (Stream.Absorb.len a - consumed)
  x5 : s.gpr .x5 = a.gpr .x5
  repr : ∀ msg, Msg a msg →
    stateAt s.mem (Stream.Absorb.st a) = Rep (rt a) (msg ++ Stream.Absorb.D a consumed)

/-- The ordinary streaming implementation finishes a resident prefix without
losing the original message contract or imposing syntactic SIMD restrictions. -/
theorem finish (v : Proof.Sha3.AArch64.Permutation) {a s : State} {c : Nat}
    (hp : Stream.Absorb.Pre a) (hs : Stack a) (hz : a.gpr .x2 = 0) (h : Tail a c s) :
    WP isa (Impl.Sha3.AArch64.Stream.absorbGenericWith v.callee) s fun s' =>
      abiPreserved a s' ∧ Proof.Sha3.absorbAArch64.post a s' := by
  have hpos : (a.gpr .x2).toNat = 0 := congrArg BitVec.toNat hz
  let tail : Region := ⟨dp a + BitVec.ofNat 64 c, Stream.Absorb.len a - c⟩
  have hsub : Region.Sub tail (dR a) := Offset.sub_base _ (by omega_using [h.c_le])
  have hlen : (s.gpr .x4).toNat = Stream.Absorb.len a - c := by
    rw [h.x4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (len_lt a)
  have pre : Proof.Sha3.absorbAArch64.pre (s.withRegions [tail] s.wr) := by
    simp only [Proof.Sha3.absorbAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, h.x0, h.x1, h.x2, h.x3, hlen,
      h.x5, h.wr, hp.wr, h.abi.2.1]
    exact ⟨rfl, trivial, hp.st_scr, hp.d_st.sub_left hsub, hp.d_scr.sub_left hsub,
      hs.sp16, hs.st, hs.d.sub_right hsub, hs.scr, hp.rate, hp.pos_lt⟩
  have hcov : Covers [tail] s.rd := by
    rw [h.rd, hp.rd]
    apply Covers.of_sub
    intro r hr
    have er : r = tail := List.mem_singleton.mp hr
    subst r
    exact ⟨dR a, by simp, c, rfl, by exact Nat.le_of_eq (Nat.add_sub_of_le h.c_le)⟩
  refine WP.mono (generic_widen v s [tail] s.wr pre
    (Covers.append hcov (fun _ _ hx => hx)) (fun _ _ hx => hx)) ?_
  intro q ⟨ha, hq⟩
  refine ⟨⟨fun r hr => (ha.1 r hr).trans (h.abi.1 r hr),
    ha.2.1.trans h.abi.2.1, fun r hr => (ha.2.2 r hr).trans (h.abi.2.2 r hr)⟩, ?_⟩
  simp only [Proof.Sha3.absorbAArch64, State.withRegions_gpr,
    State.withRegions_mem, h.x0, h.x1, h.x2, h.x3, hlen] at hq
  constructor
  · intro msg hm hmpos
    have hm' : Msg a msg := ⟨hm, hmpos⟩
    have haligned : (msg ++ Stream.Absorb.D a c).length % rt a = 0 := by
      change (msg ++ bytesAt a.mem (dp a) c).length % rt a = 0
      rw [List.length_append, VG.Proof.Sha3.bytesAt_length, Nat.add_mod,
        ← hmpos, hpos, h.aligned]
      rfl
    have hd : bytesAt s.mem (dp a + BitVec.ofNat 64 c) (Stream.Absorb.len a - c) =
        bytesAt a.mem (dp a + BitVec.ofNat 64 c) (Stream.Absorb.len a - c) := by
      apply VG.Proof.Sha3.AArch64.bytesAt_congr
      intro i hi
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact h.frame.bytes (R := dR a) (by simpa using ⟨hp.d_st, hp.d_scr⟩)
        (Nat.le_of_lt (len_lt a)) (by change c + i < Stream.Absorb.len a; omega_using [h.c_le, hi])
    have out := hq.1 (msg ++ Stream.Absorb.D a c) (h.repr msg hm') (by
      exact hpos.trans haligned.symm)
    rw [hd, List.append_assoc, ← bytesAt_add, Nat.add_sub_of_le h.c_le] at out
    exact out
  · have heq : (Stream.Absorb.len a - c) % rt a = Stream.Absorb.len a % rt a := by
      have eq := Nat.add_mod c (Stream.Absorb.len a - c) (rt a)
      rw [Nat.add_sub_of_le h.c_le, h.aligned, Nat.zero_add, Nat.mod_mod] at eq
      exact eq.symm
    change (q.gpr .x0).toNat = ((a.gpr .x2).toNat + Stream.Absorb.len a) % rt a
    rw [hpos, Nat.zero_add]
    simpa only [hpos, Nat.zero_add, heq] using hq.2

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64
open VG.Proof.Sha3.AArch64

structure Entry (a s : State) : Prop where
  args : ∀ r ∈ [Reg.x0,.x1,.x2,.x3,.x4,.x5], s.gpr r = a.gpr r
  abi : abiPreserved a s
  mem : s.mem = a.mem
  rd : s.rd = a.rd
  wr : s.wr = a.wr

theorem Entry.refl (a : State) : Entry a a :=
  ⟨fun _ _ => rfl, ⟨fun _ _ => rfl,rfl,fun _ _ => rfl⟩,rfl,rfl,rfl⟩

theorem Entry.upd {a s q : State} (h : Entry a s) {r : Reg} {v : BitVec 64}
    (u : Upd s q r v) (hr : r = .x6 ∨ r = .x7) : Entry a q := by
  have args : ∀ k ∈ [Reg.x0,.x1,.x2,.x3,.x4,.x5], k ≠ r := by
    rcases hr with rfl | rfl <;> decide +kernel
  have kept : ∀ k ∈ preserved, k ≠ r := by
    rcases hr with rfl | rfl <;> decide +kernel
  exact ⟨fun k hk => (u.other k (args k hk)).trans (h.args k hk),
    ⟨fun k hk => (u.other k (kept k hk)).trans (h.abi.1 k hk),
      u.sp.trans h.abi.2.1,fun k hk => by rw [u.vec]; exact h.abi.2.2 k hk⟩,
    u.mem.trans h.mem,u.rd.trans h.rd,u.wr.trans h.wr⟩

theorem Entry.pre {a s : State} (h : Entry a s) (hp : Proof.Sha3.absorbAArch64.pre a) :
    Proof.Sha3.absorbAArch64.pre s := by
  simp only [Proof.Sha3.absorbAArch64,h.args .x0 (by decide),h.args .x1 (by decide),h.args .x2 (by decide),h.args .x3 (by decide),h.args .x4 (by decide),h.args .x5 (by decide),h.rd,h.wr,h.abi.2.1]
  exact hp

theorem Entry.post {a s q : State} (h : Entry a s)
    (hp : Proof.Sha3.absorbAArch64.post s q) : Proof.Sha3.absorbAArch64.post a q := by
  simpa only [Proof.Sha3.absorbAArch64,h.args .x0 (by decide),h.args .x1 (by decide),h.args .x2 (by decide),h.args .x3 (by decide),h.args .x4 (by decide),h.args .x5 (by decide),h.mem] using hp

theorem generic_entry (v : Permutation) {a s : State} (hp : Proof.Sha3.absorbAArch64.pre a)
    (h : Entry a s) :
    WP isa (Impl.Sha3.AArch64.Stream.absorbGenericWith v.callee) s fun q =>
      abiPreserved a q ∧ Proof.Sha3.absorbAArch64.post a q := by
  refine WP.mono (Stream.Absorb.correct v (Stream.Absorb.pre_of (h.pre hp)).1
    (Stream.Absorb.pre_of (h.pre hp)).2) ?_
  intro q ⟨ha,hq⟩
  exact ⟨⟨fun r hr => (ha.1 r hr).trans (h.abi.1 r hr),
    ha.2.1.trans h.abi.2.1,fun r hr => (ha.2.2 r hr).trans (h.abi.2.2 r hr)⟩,h.post hq⟩

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64
open VG.Proof.Sha3.AArch64
open VG.Proof.Sha3.AArch64.Stream.Absorb

private theorem upd_abi {a s : State} {r : Reg} {x : BitVec 64} (h : Upd a s r x)
    (hr : r ∉ preserved) : abiPreserved a s :=
  ⟨fun k hk => h.other k (fun e => hr (e ▸ hk)),h.sp,fun _ _ => by rw [h.vec]⟩

private theorem abi_trans {a b c : State} (h : abiPreserved a b) (k : abiPreserved b c) :
    abiPreserved a c :=
  ⟨fun r hr => (k.1 r hr).trans (h.1 r hr),k.2.1.trans h.2.1,
    fun r hr => (k.2.2 r hr).trans (h.2.2 r hr)⟩

private theorem bulk_tail (v : Permutation)
    (hb : ∀ b, BulkPre b → WP isa Impl.Sha3.AArch64.Sha3.Vector.Resident.bulk b (BulkPost b))
    {a b : State} (hp : Proof.Sha3.absorbAArch64.pre a) (he : Entry a b)
    (hz : a.gpr .x2 = 0) (h6 : b.gpr .x6 = a.gpr .x1)
    (hen : rt a ≤ Stream.Absorb.len a) (hlt : Stream.Absorb.len a < 2^63 + rt a) :
    WP isa (.seq (.block [Impl.Sha3.AArch64.mov .x1 .x5])
      (.seq Impl.Sha3.AArch64.Sha3.Vector.Resident.bulk
        (.block [Impl.Sha3.AArch64.mov .x1 .x6]))) b fun r =>
      WP isa (Impl.Sha3.AArch64.Stream.absorbGenericWith v.callee) r fun q =>
        abiPreserved a q ∧ Proof.Sha3.absorbAArch64.post a q := by
  obtain ⟨pa,sa⟩ := Stream.Absorb.pre_of hp
  refine WP.seq (wp_mov fun b' u => wp_nil ?_)
  have e0 : b'.gpr .x0 = a.gpr .x0 := (u.other _ (by decide)).trans (he.args _ (by decide))
  have e1 : b'.gpr .x1 = a.gpr .x5 := u.gpr.trans (he.args _ (by decide))
  have e2 : b'.gpr .x2 = a.gpr .x2 := (u.other _ (by decide)).trans (he.args _ (by decide))
  have e3 : b'.gpr .x3 = a.gpr .x3 := (u.other _ (by decide)).trans (he.args _ (by decide))
  have e4 : b'.gpr .x4 = a.gpr .x4 := (u.other _ (by decide)).trans (he.args _ (by decide))
  have e5 : b'.gpr .x5 = a.gpr .x5 := (u.other _ (by decide)).trans (he.args _ (by decide))
  have e6 : b'.gpr .x6 = a.gpr .x1 := (u.other _ (by decide)).trans h6
  have em : b'.mem = a.mem := u.mem.trans he.mem
  have er : b'.rd = a.rd := u.rd.trans he.rd
  have ew : b'.wr = a.wr := u.wr.trans he.wr
  have ba : abiPreserved a b' := abi_trans he.abi (upd_abi u (by decide))
  have bp : BulkPre b' := by
    constructor <;> simp only [dataR,data,len,stateR,st,scratchR,scratch,rate,
      e0,e1,e2,e3,e4,e5,e6,er,ew]
    · exact pa.rd
    · exact pa.wr
    · exact pa.st_scr
    · exact pa.d_st
    · exact pa.d_scr
    · exact pa.rate
    · exact hen
    · exact hlt
    · exact hz
  refine WP.seq (WP.mono (hb b' bp) fun q ⟨c,h⟩ => ?_)
  refine wp_mov fun r ur => wp_nil ?_
  apply finish v (c := c) pa sa hz
  refine ⟨?_,?_,abi_trans (abi_trans ba h.abi) (upd_abi ur (by decide)),
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [len,e4] using h.c_le
  · simpa only [rate,e6] using h.aligned
  · exact ur.rd.trans (h.rd.trans er)
  · exact ur.wr.trans (h.wr.trans ew)
  · simpa only [ur.mem,stateR,st,scratchR,scratch,e0,e1,em] using h.frame
  · exact (ur.other _ (by decide)).trans (h.x0.trans e0)
  · exact ur.gpr.trans (h.x6.trans e6)
  · exact (ur.other _ (by decide)).trans (h.x2.trans e2)
  · simp only [ur.other .x3 (by decide),h.x3,data,e3]
  · simp only [ur.other .x4 (by decide),h.x4,len,e4]
  · exact (ur.other _ (by decide)).trans (h.x5.trans e5)
  · intro msg ⟨hm,hpos⟩
    have hzero : msg.length % rt a = 0 := hpos.symm.trans (congrArg BitVec.toNat hz)
    simpa only [ur.mem,st,rate,data,e0,e3,e6,em] using
      h.repr msg (by simpa only [st,rate,e0,e6,em] using hm)
        (by simpa only [rate,e6] using hzero)

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64
open VG.Proof.Sha3.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector.Resident

/-- The public guards select either the proved resident prefix or the ordinary
streaming tail. Every branch retains the same scalar-compatible contract. -/
theorem correct (v : Permutation)
    (hb : ∀ b, BulkPre b → WP isa bulk b (BulkPost b))
    (a : State) (hp : Proof.Sha3.absorbAArch64.pre a) :
    WP isa (absorb v.callee) a fun q =>
      abiPreserved a q ∧ Proof.Sha3.absorbAArch64.post a q := by
  unfold absorb bulkPrefix
  refine WP.seq (WP.ite (a.gpr .x2 == 0) (eval_zero _ _) (fun hz => ?_) (fun _ => ?_))
  · have hz' : a.gpr .x2 = 0 := eq_of_beq hz
    unfold test
    refine WP.seq (wp_mov fun a1 u1 => wp_sub fun a2 u2 =>
      wp_lsr (by decide) fun a3 u3 => wp_nil ?_)
    have he : Entry a a3 := ((Entry.refl a).upd u1 (.inl rfl)).upd u2 (.inr rfl) |>.upd u3 (.inr rfl)
    have h6 : a3.gpr .x6 = a.gpr .x1 := by
      rw [u3.other _ (by decide),u2.other _ (by decide),u1.gpr]
    have h7 : a3.gpr .x7 = (a.gpr .x4 - a.gpr .x1) >>> 63 := by
      rw [u3.gpr,u2.gpr,u1.other _ (by decide),u1.gpr]
    refine WP.ite (a3.gpr .x7 == 0) (eval_zero _ _) (fun hen => ?_) (fun _ => ?_)
    · have heq : (a.gpr .x4 - a.gpr .x1) >>> 63 = 0 := h7.symm.trans (eq_of_beq hen)
      have hr := (Stream.Absorb.pre_of hp).1.rt_pos
      have hn := (enough_iff (a.gpr .x4).toNat (a.gpr .x1).toNat
        (a.gpr .x4).isLt hr.2).mp (by simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using heq)
      exact bulk_tail v hb hp he hz' h6 hn.1 hn.2
    · exact wp_nil (generic_entry v hp he)
  · exact wp_nil (generic_entry v hp (Entry.refl a))

theorem absorb_correct (v : Permutation)
    (hb : ∀ b, BulkPre b → WP isa bulk b (BulkPost b))
    (a : State) (hp : Proof.Sha3.absorbAArch64.pre a) :
    ∃ t q, Exec isa (absorb v.callee) a t q ∧ abiPreserved a q ∧
      Proof.Sha3.absorbAArch64.post a q := by
  obtain ⟨t,q,he,hq⟩ := correct v hb a hp
  exact ⟨t,q,he,hq⟩

theorem bulk_depth : bulk.aarch64Depth = 0 := by rfl

theorem absorb_depth (v : Permutation) : (absorb v.callee).aarch64Depth = 1 := by
  change Nat.max 0 ((Impl.Sha3.AArch64.Stream.absorbMainWith v.callee).aarch64Depth + 1) = 1
  rw [v.absorbMain_depth]
  rfl

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64

/-- The selected hardware absorber branches only on public arguments. -/
theorem absorb_taint : ∃ h, (taint.check (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x5])
    (Impl.Sha3.AArch64.Sha3.Vector.Resident.absorb Sha3.callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem absorb_ct : ConstantTime isa Proof.Sha3.absorbAArch64.pre Proof.Sha3.absorbAArch64.pub
    (Impl.Sha3.AArch64.Sha3.Vector.Resident.absorb Sha3.callee) := by
  obtain ⟨h,hh⟩ := absorb_taint
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x5])
    (fun _ _ _ _ hp => Stream.Absorb.agree₀ hp) hh

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64

/-- The selected hardware absorber, with the actual resident-loop theorem
supplied to the generic outer composition proof. -/
theorem hardware_absorb_correct (a : State) (hp : Proof.Sha3.absorbAArch64.pre a) :
    ∃ t q, Exec isa (Impl.Sha3.AArch64.Sha3.Vector.Resident.absorb Sha3.callee) a t q ∧
      abiPreserved a q ∧ Proof.Sha3.absorbAArch64.post a q :=
  absorb_correct Sha3.backend bulk_correct a hp

theorem hardware_absorb_depth :
    (Impl.Sha3.AArch64.Sha3.Vector.Resident.absorb Sha3.callee).aarch64Depth = 1 :=
  absorb_depth Sha3.backend

#assert_standard_axioms hardware_absorb_correct

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
