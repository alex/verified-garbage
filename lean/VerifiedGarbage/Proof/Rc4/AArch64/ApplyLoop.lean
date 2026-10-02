import VerifiedGarbage.Proof.Rc4.AArch64.ApplyStep
import VerifiedGarbage.Proof.Rc4.Stream

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

/-- A stream iteration also preserves all memory outside the table and byte. -/
theorem apply_step_frame (s : State) (i j : Byte)
    (hi : s.gpr .x12 = i.setWidth 64) (hj : s.gpr .x13 = j.setWidth 64)
    (hm : s.gpr .x9 = 255#64) (hp : InRegions s.wr (s.gpr .x0) 256)
    (hd : InRegions s.wr (s.gpr .x1) 1) :
    WP isa applyStep s fun t => StreamFrame (s.gpr .x0) (s.gpr .x1) 1 s.mem t.mem := by
  refine WP.mono (apply_step s i j hi hj hm hp hd) fun t ht => ?_
  rw [ht.1]
  exact stream_frame_step _ _ _ _ _ _

/-- The unconsumed data remains unchanged by a stream iteration. -/
theorem apply_step_tail (s : State) (i j : Byte) (n : Nat)
    (hn : n + 1 < 2 ^ 64)
    (hi : s.gpr .x12 = i.setWidth 64) (hj : s.gpr .x13 = j.setWidth 64)
    (hm : s.gpr .x9 = 255#64) (hp : InRegions s.wr (s.gpr .x0) 256)
    (hd : InRegions s.wr (s.gpr .x1) 1)
    (hs : Mem.Sep (s.gpr .x0) 256 (s.gpr .x1) (n + 1)) :
    WP isa applyStep s fun t =>
      bytesAt t.mem (s.gpr .x1 + 1#64) n = bytesAt s.mem (s.gpr .x1 + 1#64) n := by
  refine WP.mono (apply_step s i j hi hj hm hp hd) fun t ht => ?_
  rw [ht.1]
  rw [bytes_write_sep _ _ _ _ _ (by omega)
    (sep_symm (Offset.sep_base (s.gpr .x1) (by decide) (by omega)))]
  exact bytes_table_frame _ _ _ _ _ (by omega) (swap_frame _ _ _ _)
    (sep_symm (sep_tail hn hs))

structure LoopPost (s : State) (ctx : Context) (n : Nat) (t : State) : Prop where
  table : (contextAt t.mem (s.gpr .x0)).table = (update ctx (bytesAt s.mem (s.gpr .x1) n)).1.table
  i : t.gpr .x12 = (update ctx (bytesAt s.mem (s.gpr .x1) n)).1.i.setWidth 64
  j : t.gpr .x13 = (update ctx (bytesAt s.mem (s.gpr .x1) n)).1.j.setWidth 64
  data : bytesAt t.mem (s.gpr .x1) n = (update ctx (bytesAt s.mem (s.gpr .x1) n)).2
  frame : StreamFrame (s.gpr .x0) (s.gpr .x1) n s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  p : t.gpr .x0 = s.gpr .x0
  dataPtr : t.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 n
  len : t.gpr .x2 = 0#64
  mask : t.gpr .x9 = 255#64

/-- Streaming correctness by induction on the public byte count. -/
theorem apply_loop (n : Nat) (s : State) (ctx : Context)
    (hn : n + 1 < 2 ^ 64)
    (htable : (contextAt s.mem (s.gpr .x0)).table = ctx.table)
    (hi : s.gpr .x12 = ctx.i.setWidth 64) (hj : s.gpr .x13 = ctx.j.setWidth 64)
    (hm : s.gpr .x9 = 255#64) (hlen : s.gpr .x2 = BitVec.ofNat 64 (n + 1))
    (hp : InRegions s.wr (s.gpr .x0) 256)
    (hd : InRegions s.wr (s.gpr .x1) (n + 1))
    (hs : Mem.Sep (s.gpr .x0) 256 (s.gpr .x1) (n + 1)) :
    WP isa (.loop applyStep (.nonzero .x .x2)) s (LoopPost s ctx (n + 1)) := by
  induction n generalizing s ctx with
  | zero =>
    have hd1 : InRegions s.wr (s.gpr .x1) 1 := hd
    have hctx : ({ table := (contextAt s.mem (s.gpr .x0)).table, i := ctx.i, j := ctx.j } : Context) = ctx :=
      context_ext htable rfl rfl
    have hstep := apply_step_table s ctx.i ctx.j hi hj hm hp hd1 hs
    rw [hctx] at hstep
    obtain ⟨tr, t, he, ht⟩ := hstep
    obtain ⟨htab, hti, htj, hbyte, hrd, hwr, hp0, hdptr, hcount, hmask⟩ := ht
    have hf : StreamFrame (s.gpr .x0) (s.gpr .x1) 1 s.mem t.mem := by
      obtain ⟨_, u, he', hf⟩ := apply_step_frame s ctx.i ctx.j hi hj hm hp hd1
      obtain ⟨_, rfl⟩ := Exec.det he' he
      exact hf
    have hz : t.gpr .x2 = 0#64 := by rw [hcount, hlen]; rfl
    have hbytes (m : Mem) : bytesAt m (s.gpr .x1) 1 = [m (s.gpr .x1)] := by
      simp [bytesAt]
    refine ⟨_, t, .loopExit he ?_, ?_⟩
    · simp only [eval, State.read, BitVec.setWidth_eq, hz, bne]
      rfl
    · constructor
      · simpa only [Nat.zero_add, hbytes, update] using htab
      · simpa only [Nat.zero_add, hbytes, update] using hti
      · simpa only [Nat.zero_add, hbytes, update] using htj
      · simp only [Nat.zero_add, hbytes, update, hbyte]
      · exact hf
      · exact hrd
      · exact hwr
      · exact hp0
      · exact hdptr
      · exact hz
      · exact hmask
  | succ n ih =>
    have hd1 : InRegions s.wr (s.gpr .x1) 1 := by
      have hh := region_offset _ _ _ 0 1 (by decide) (by omega) hd
      simpa only [BitVec.add_zero] using hh
    have hs1 : Mem.Sep (s.gpr .x0) 256 (s.gpr .x1) 1 := fun x hx hy => hs x hx (by omega)
    have hctx : ({ table := (contextAt s.mem (s.gpr .x0)).table, i := ctx.i, j := ctx.j } : Context) = ctx :=
      context_ext htable rfl rfl
    have hstep := apply_step_table s ctx.i ctx.j hi hj hm hp hd1 hs1
    rw [hctx] at hstep
    obtain ⟨tr, t, he, ht⟩ := hstep
    obtain ⟨htab, hti, htj, hbyte, hrd, hwr, hp0, hdptr, hcount, hmask⟩ := ht
    have hf : StreamFrame (s.gpr .x0) (s.gpr .x1) 1 s.mem t.mem := by
      obtain ⟨_, u, he', hf⟩ := apply_step_frame s ctx.i ctx.j hi hj hm hp hd1
      obtain ⟨_, rfl⟩ := Exec.det he' he
      exact hf
    have htail : bytesAt t.mem (s.gpr .x1 + 1#64) (n + 1) =
        bytesAt s.mem (s.gpr .x1 + 1#64) (n + 1) := by
      obtain ⟨_, u, he', hh⟩ := apply_step_tail s ctx.i ctx.j (n + 1) hn hi hj hm hp hd1 hs
      obtain ⟨_, rfl⟩ := Exec.det he' he
      exact hh
    have htlen : t.gpr .x2 = BitVec.ofNat 64 (n + 1) := by
      rw [hcount, hlen]
      exact Offset.ofNat_sub_ofNat (by omega)
    have hpt : InRegions t.wr (t.gpr .x0) 256 := by rw [hwr, hp0]; exact hp
    have hdt : InRegions t.wr (t.gpr .x1) (n + 1) := by
      rw [hwr, hdptr]
      exact region_offset _ _ _ 1 (n + 1) (by decide) (by omega) hd
    have hst : Mem.Sep (t.gpr .x0) 256 (t.gpr .x1) (n + 1) := by
      rw [hp0, hdptr]
      exact sep_tail hn hs
    have htab' : (contextAt t.mem (t.gpr .x0)).table = (step ctx).1.table := by rw [hp0]; exact htab
    obtain ⟨tr', u, he', hu⟩ := ih t (step ctx).1 (by omega) htab' hti htj hmask htlen hpt hdt hst
    refine ⟨_, u, .loopNext he ?_ he', ?_⟩
    · have hnz : BitVec.ofNat 64 (n + 1) ≠ 0#64 := by
        intro hz
        have hh := congrArg BitVec.toNat hz
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hh
        change n + 1 = 0 at hh
        omega
      simp only [eval, State.read, BitVec.setWidth_eq, htlen, bne, BitVec.ofNat_eq_ofNat,
        beq_eq_false_iff_ne.mpr hnz]
      rfl
    · have hresult : update ctx (bytesAt s.mem (s.gpr .x1) (n + 1 + 1)) =
          ((update (step ctx).1 (bytesAt t.mem (t.gpr .x1) (n + 1))).1,
            (s.mem (s.gpr .x1) ^^^ (step ctx).2) ::
              (update (step ctx).1 (bytesAt t.mem (t.gpr .x1) (n + 1))).2) := by
        rw [bytes_cons, hdptr, htail]
        rfl
      constructor
      · rw [hresult, ← hp0]; exact hu.table
      · rw [hresult]; exact hu.i
      · rw [hresult]; exact hu.j
      · rw [bytes_cons, hresult]
        have hh : u.mem (s.gpr .x1) = t.mem (s.gpr .x1) := by
          have hf' := hu.frame
          rw [hp0, hdptr] at hf'
          exact stream_head _ _ _ _ _ hn hf' hs
        rw [hh, hbyte, ← hdptr, hu.data]
      · have hf' := hu.frame
        rw [hp0, hdptr] at hf'
        exact stream_frame_trans_tail hf hf'
      · exact hu.rd.trans hrd
      · exact hu.wr.trans hwr
      · exact hu.p.trans hp0
      · rw [hu.dataPtr, hdptr]
        simpa only [Nat.add_comm 1 (n + 1)] using Offset.add_ofNat_add_ofNat (s.gpr .x1) 1 (n + 1)
      · exact hu.len
      · exact hu.mask

end VG.Proof.Rc4.AArch64
