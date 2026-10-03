import VerifiedGarbage.Proof.Rc4.X86_64.ApplyStep

/-! # RC4 on x86-64: the stream function -/

namespace VG.Proof.Rc4.X86_64
open VG VG.X86_64 VG.Impl.Rc4.X86_64 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)

/-- The concrete stream iteration realizes the abstract PRGA transition. -/
theorem apply_step_table (s : State) (i j : Byte)
    (hcx : s.gpr .rcx = i.setWidth 64) (h8 : s.gpr .r8 = j.setWidth 64)
    (hp : InRegions s.wr (s.gpr .rdi) 256) (hd : InRegions s.wr (s.gpr .rsi) 1)
    (hs : Mem.Sep (s.gpr .rdi) 256 (s.gpr .rsi) 1) :
    let next := step { table := (contextAt s.mem (s.gpr .rdi)).table, i, j }
    WP isa (.block applyStep) s fun t =>
      (contextAt t.mem (s.gpr .rdi)).table = next.1.table ∧
      t.gpr .rcx = next.1.i.setWidth 64 ∧ t.gpr .r8 = next.1.j.setWidth 64 ∧
      t.mem (s.gpr .rsi) = s.mem (s.gpr .rsi) ^^^ next.2 ∧
      StreamFrame (s.gpr .rdi) (s.gpr .rsi) 1 s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .rdi = s.gpr .rdi ∧
      t.gpr .rsi = s.gpr .rsi + 1#64 ∧ t.gpr .rdx = s.gpr .rdx - 1#64 ∧
      t.zf = some (s.gpr .rdx - 1#64 == 0#64) := by
  dsimp only
  rw [step_eq]
  dsimp only
  simp only [table_get]
  have hone : (1 : Byte) = 1#8 := rfl
  simp only [hone]
  refine WP.mono (apply_step s i j hcx h8 hp hd) fun t ht => ?_
  obtain ⟨hmem, hrd, hwr, h0, h1, h2, hz, hi, hj⟩ := ht
  refine ⟨?_, hi, hj, ?_, ?_, hrd, hwr, h0, h1, h2, hz⟩
  · rw [hmem, table_write_sep _ _ _ _ hs, table_swap]
  · rw [hmem, write_byte, ite_eq_left rfl]
    have hne (idx : Byte) : s.gpr .rsi ≠ s.gpr .rdi + BitVec.ofNat 64 idx.toNat := by
      intro he
      have hn := hs (s.gpr .rsi) (by rw [he, Mem.sub_ofNat_toNat _ (by omega)]; exact idx.isLt)
      exact hn (by simp [BitVec.sub_self])
    rw [write_byte, ite_eq_right (hne _), write_byte, ite_eq_right (hne _)]
    have ht := table_swap s.mem (s.gpr .rdi) (i + 1#8)
      (j + s.mem (s.gpr .rdi + BitVec.ofNat 64 (i + 1#8).toNat))
    rw [← ht, table_get]
  · rw [hmem]
    exact stream_frame_step _ _ _ _ _ _

/-- The unconsumed data remains unchanged by a stream iteration. -/
theorem apply_step_tail (s : State) (i j : Byte) (n : Nat)
    (hn : n + 1 < 2 ^ 64)
    (hcx : s.gpr .rcx = i.setWidth 64) (h8 : s.gpr .r8 = j.setWidth 64)
    (hp : InRegions s.wr (s.gpr .rdi) 256) (hd : InRegions s.wr (s.gpr .rsi) 1)
    (hs : Mem.Sep (s.gpr .rdi) 256 (s.gpr .rsi) (n + 1)) :
    WP isa (.block applyStep) s fun t =>
      bytesAt t.mem (s.gpr .rsi + 1#64) n = bytesAt s.mem (s.gpr .rsi + 1#64) n := by
  refine WP.mono (apply_step s i j hcx h8 hp hd) fun t ht => ?_
  rw [ht.1]
  rw [bytes_write_sep _ _ _ _ _ (by omega)
    (sep_symm (Offset.sep_base (s.gpr .rsi) (by decide) (by omega)))]
  exact bytes_table_frame _ _ _ _ _ (by omega) (swap_frame _ _ _ _)
    (sep_symm (sep_tail hn hs))

structure LoopPost (s : State) (ctx : Context) (n : Nat) (t : State) : Prop where
  table : (contextAt t.mem (s.gpr .rdi)).table =
    (update ctx (bytesAt s.mem (s.gpr .rsi) n)).1.table
  i : t.gpr .rcx = (update ctx (bytesAt s.mem (s.gpr .rsi) n)).1.i.setWidth 64
  j : t.gpr .r8 = (update ctx (bytesAt s.mem (s.gpr .rsi) n)).1.j.setWidth 64
  data : bytesAt t.mem (s.gpr .rsi) n = (update ctx (bytesAt s.mem (s.gpr .rsi) n)).2
  frame : StreamFrame (s.gpr .rdi) (s.gpr .rsi) n s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  p : t.gpr .rdi = s.gpr .rdi

/-- Streaming correctness by induction on the public byte count. -/
theorem apply_loop (n : Nat) (s : State) (ctx : Context)
    (hn : n + 1 < 2 ^ 64)
    (htable : (contextAt s.mem (s.gpr .rdi)).table = ctx.table)
    (hcx : s.gpr .rcx = ctx.i.setWidth 64) (h8 : s.gpr .r8 = ctx.j.setWidth 64)
    (hlen : s.gpr .rdx = BitVec.ofNat 64 (n + 1))
    (hp : InRegions s.wr (s.gpr .rdi) 256)
    (hd : InRegions s.wr (s.gpr .rsi) (n + 1))
    (hs : Mem.Sep (s.gpr .rdi) 256 (s.gpr .rsi) (n + 1)) :
    WP isa (.loop (.block applyStep) .ne) s (LoopPost s ctx (n + 1)) := by
  induction n generalizing s ctx with
  | zero =>
    have hd1 : InRegions s.wr (s.gpr .rsi) 1 := hd
    have hctx : ({ table := (contextAt s.mem (s.gpr .rdi)).table, i := ctx.i, j := ctx.j } :
        Context) = ctx := context_ext htable rfl rfl
    have hstep := apply_step_table s ctx.i ctx.j hcx h8 hp hd1 hs
    rw [hctx] at hstep
    obtain ⟨tr, t, he, ht⟩ := hstep
    obtain ⟨htab, hti, htj, hbyte, hf, hrd, hwr, hp0, _, hcount, hz⟩ := ht
    have hz' : t.zf = some true := by rw [hz, hlen]; rfl
    have hbytes (m : Mem) : bytesAt m (s.gpr .rsi) 1 = [m (s.gpr .rsi)] := by
      simp [bytesAt]
    refine ⟨_, t, .loopExit he ?_, ?_⟩
    · simp only [eval, hz', Option.map_some]
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
  | succ n ih =>
    have hd1 : InRegions s.wr (s.gpr .rsi) 1 := by
      have hh := region_offset _ _ _ 0 1 (by decide) (by omega) hd
      simpa only [BitVec.add_zero] using hh
    have hs1 : Mem.Sep (s.gpr .rdi) 256 (s.gpr .rsi) 1 := fun x hx hy => hs x hx (by omega)
    have hctx : ({ table := (contextAt s.mem (s.gpr .rdi)).table, i := ctx.i, j := ctx.j } :
        Context) = ctx := context_ext htable rfl rfl
    have hstep := apply_step_table s ctx.i ctx.j hcx h8 hp hd1 hs1
    rw [hctx] at hstep
    obtain ⟨tr, t, he, ht⟩ := hstep
    obtain ⟨htab, hti, htj, hbyte, hf, hrd, hwr, hp0, hdptr, hcount, hz⟩ := ht
    have htail : bytesAt t.mem (s.gpr .rsi + 1#64) (n + 1) =
        bytesAt s.mem (s.gpr .rsi + 1#64) (n + 1) := by
      obtain ⟨_, u, he', hh⟩ := apply_step_tail s ctx.i ctx.j (n + 1) hn hcx h8 hp hd1 hs
      obtain ⟨_, rfl⟩ := Exec.det he' he
      exact hh
    have htlen : t.gpr .rdx = BitVec.ofNat 64 (n + 1) := by
      rw [hcount, hlen]
      exact Offset.ofNat_sub_ofNat (by omega)
    have hpt : InRegions t.wr (t.gpr .rdi) 256 := by rw [hwr, hp0]; exact hp
    have hdt : InRegions t.wr (t.gpr .rsi) (n + 1) := by
      rw [hwr, hdptr]
      exact region_offset _ _ _ 1 (n + 1) (by decide) (by omega) hd
    have hst : Mem.Sep (t.gpr .rdi) 256 (t.gpr .rsi) (n + 1) := by
      rw [hp0, hdptr]
      exact sep_tail hn hs
    have htab' : (contextAt t.mem (t.gpr .rdi)).table = (step ctx).1.table := by
      rw [hp0]; exact htab
    obtain ⟨tr', u, he', hu⟩ := ih t (step ctx).1 (by omega) htab' hti htj htlen hpt hdt hst
    refine ⟨_, u, .loopNext he ?_ he', ?_⟩
    · have hnz : BitVec.ofNat 64 (n + 1 + 1) - 1#64 ≠ 0#64 := by
        rw [Offset.ofNat_sub_ofNat (by omega)]
        intro hz0
        have hh := congrArg BitVec.toNat hz0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hh
        change n + 1 + 1 - 1 = 0 at hh
        omega
      rw [hlen] at hz
      simp only [eval, hz, Option.map_some, beq_eq_false_iff_ne.mpr hnz, Bool.not_false]
    · have hresult : update ctx (bytesAt s.mem (s.gpr .rsi) (n + 1 + 1)) =
          ((update (step ctx).1 (bytesAt t.mem (t.gpr .rsi) (n + 1))).1,
            (s.mem (s.gpr .rsi) ^^^ (step ctx).2) ::
              (update (step ctx).1 (bytesAt t.mem (t.gpr .rsi) (n + 1))).2) := by
        rw [bytes_cons, hdptr, htail]
        rfl
      constructor
      · rw [hresult, ← hp0]; exact hu.table
      · rw [hresult]; exact hu.i
      · rw [hresult]; exact hu.j
      · rw [bytes_cons, hresult]
        have hh : u.mem (s.gpr .rsi) = t.mem (s.gpr .rsi) := by
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

theorem apply_finish (s : State) (ctx : Context) (d : Addr) (n : Nat) (hn : n < 2 ^ 64)
    (htable : (contextAt s.mem (s.gpr .rdi)).table = ctx.table)
    (hcx : s.gpr .rcx = ctx.i.setWidth 64) (h8 : s.gpr .r8 = ctx.j.setWidth 64)
    (hp : InRegions s.wr (s.gpr .rdi) 258)
    (hs : Mem.Sep d n (s.gpr .rdi) 258) :
    WP isa (.block [.store8 (at_ .rdi 256) .rcx, .store8 (at_ .rdi 257) .r8]) s fun t =>
      contextAt t.mem (s.gpr .rdi) = ctx ∧ bytesAt t.mem d n = bytesAt s.mem d n ∧
      t.mem = (s.mem.write (s.gpr .rdi + 256#64) 1 ctx.i).write (s.gpr .rdi + 257#64) 1 ctx.j := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [h256, h257, hcx, h8, writeW_byte8, low_byte]
  refine ⟨?_, ?_⟩
  · rw [context_finish, htable]
  · rw [bytes_write_sep _ _ _ _ _ hn (sep_offset_right hs (by decide) (by decide)),
      bytes_write_sep _ _ _ _ _ hn (sep_offset_right hs (by decide) (by decide))]

theorem apply_start (s : State) (hp : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 258) :
    WP isa (.block [.movzx8 .rcx (at_ .rdi 256), .movzx8 .r8 (at_ .rdi 257),
      .alu .test .rdx (.reg .rdx)]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = s.gpr .rdx ∧
      t.gpr .rcx = (contextAt s.mem (s.gpr .rdi)).i.setWidth 64 ∧
      t.gpr .r8 = (contextAt s.mem (s.gpr .rdi)).j.setWidth 64 ∧
      t.zf = some (s.gpr .rdx &&& s.gpr .rdx == 0#64) := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [h256, h257, contextAt]
  exact ⟨rfl, rfl, rfl⟩

/-- Memory changed only within the context and the data. -/
def ApplyFrame (p d : Addr) (n : Nat) (m m' : Mem) : Prop :=
  ∀ x, ¬ (x - p).toNat < 258 → ¬ (x - d).toNat < n → m' x = m x

theorem apply_ok (s : State)
    (hp : InRegions s.wr (s.gpr .rdi) 258)
    (hd : InRegions s.wr (s.gpr .rsi) (s.gpr .rdx).toNat)
    (hs : Mem.Sep (s.gpr .rdi) 258 (s.gpr .rsi) (s.gpr .rdx).toNat) :
    WP isa VG.Impl.Rc4.X86_64.apply s fun t =>
      let result := update (contextAt s.mem (s.gpr .rdi))
        (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
      (contextAt t.mem (s.gpr .rdi) = result.1 ∧
        bytesAt t.mem (s.gpr .rsi) (s.gpr .rdx).toNat = result.2) ∧
      ApplyFrame (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx).toNat s.mem t.mem := by
  have hpRead : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 258 := by
    obtain ⟨region, hr, hc⟩ := hp
    exact ⟨region, List.mem_append_right _ hr, hc⟩
  unfold VG.Impl.Rc4.X86_64.apply
  refine WP.seq (WP.mono (apply_start s hpRead) fun a ha => ?_)
  obtain ⟨ham, har, haw, ha0, ha1, ha2, ha12, ha13, haz⟩ := ha
  refine WP.ite (s.gpr .rdx == 0#64) (by simp only [eval, haz, BitVec.and_self]) (fun hz => ?_)
    (fun hnz => ?_)
  · have hz' : s.gpr .rdx = 0#64 := beq_iff_eq.mp hz
    refine WP.block_nil ?_
    simp only [hz', ham]
    exact ⟨⟨context_ext rfl rfl rfl, rfl⟩, fun _ _ _ => rfl⟩
  · have hnz' : s.gpr .rdx ≠ 0#64 := beq_eq_false_iff_ne.mp hnz
    obtain ⟨n, hnEq⟩ := Nat.exists_eq_succ_of_ne_zero (show (s.gpr .rdx).toNat ≠ 0 by
      intro h; exact hnz' (BitVec.eq_of_toNat_eq h))
    change (s.gpr .rdx).toNat = n + 1 at hnEq
    have hbound : n + 1 < 2 ^ 64 := by rw [← hnEq]; exact (s.gpr .rdx).isLt
    have hpa : InRegions a.wr (a.gpr .rdi) 256 := by
      rw [haw, ha0]
      have hh := region_offset _ _ _ 0 256 (by decide) (by decide) hp
      simpa only [BitVec.add_zero] using hh
    have hda : InRegions a.wr (a.gpr .rsi) (n + 1) := by rw [haw, ha1, ← hnEq]; exact hd
    have hsa : Mem.Sep (a.gpr .rdi) 256 (a.gpr .rsi) (n + 1) := by
      rw [ha0, ha1, ← hnEq]
      exact fun x hx hy => hs x (by omega) hy
    have htable : (contextAt a.mem (a.gpr .rdi)).table = (contextAt s.mem (s.gpr .rdi)).table := by
      rw [ham, ha0]
    have hlen : a.gpr .rdx = BitVec.ofNat 64 (n + 1) := by
      rw [ha2, ← hnEq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine WP.seq (WP.mono (apply_loop n a (contextAt s.mem (s.gpr .rdi)) hbound htable ha12 ha13
      hlen hpa hda hsa) fun b hb => ?_)
    have hpb : InRegions b.wr (b.gpr .rdi) 258 := by rw [hb.wr, hb.p, haw, ha0]; exact hp
    have hsb : Mem.Sep (s.gpr .rsi) (n + 1) (b.gpr .rdi) 258 := by
      rw [hb.p, ha0, ← hnEq]
      exact sep_symm hs
    have htab : (contextAt b.mem (b.gpr .rdi)).table =
        (update (contextAt s.mem (s.gpr .rdi)) (bytesAt a.mem (a.gpr .rsi) (n + 1))).1.table := by
      rw [hb.p]; exact hb.table
    refine WP.mono (apply_finish b _ (s.gpr .rsi) (n + 1) (by omega) htab hb.i hb.j hpb hsb)
      fun t ⟨htc, htd, htm⟩ => ?_
    have hdata := hb.data
    rw [ha1, ham] at hdata
    rw [hb.p, ha0, ham, ha1] at htc
    rw [hnEq]
    refine ⟨⟨htc, htd.trans hdata⟩, ?_⟩
    intro x hx hy
    have hf := hb.frame
    rw [ha0, ha1, ham] at hf
    rw [htm, hb.p, ha0]
    have h1 : x ≠ s.gpr .rdi + 256#64 := by
      intro he; apply hx; rw [he, Mem.sub_ofNat_toNat _ (by decide)]; decide
    have h2 : x ≠ s.gpr .rdi + 257#64 := by
      intro he; apply hx; rw [he, Mem.sub_ofNat_toNat _ (by decide)]; decide
    rw [write_byte, ite_eq_right h2, write_byte, ite_eq_right h1]
    exact hf x (by omega) hy

end VG.Proof.Rc4.X86_64
