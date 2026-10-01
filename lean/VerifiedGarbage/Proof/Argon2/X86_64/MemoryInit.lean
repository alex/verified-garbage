import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitLoop
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitSetup
import VerifiedGarbage.Proof.Argon2.Dimensions

/-! # Functional correctness of complete memory initialization -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Proof.Argon2.X86_64.Initial (wordAt)
open VG.Spec.Blake2 (bytesAt)

theorem Cleared.frame {s t : State} {memory : Addr} {blocks : Nat}
    (h : Cleared s t memory blocks) (bound : 1024 * blocks < 2 ^ 64) :
    Frame [⟨memory, 1024 * blocks⟩] s.mem t.mem := by
  rw [h.mem]
  simpa only [show 8 * (128 * blocks) = 1024 * blocks by omega] using
    clearMem_frame s.mem memory (128 * blocks) (by omega)

theorem Cleared.word {s t : State} {memory : Addr} {blocks d : Nat}
    (h : Cleared s t memory blocks) (space : Space s memory (1024 * blocks))
    (offset : d + 8 ≤ 272) : wordAt t d = wordAt s d := by
  unfold wordAt
  rw [h.other .rbp (by decide) (by decide) (by decide)]
  apply (h.frame space.bound).readW (r := ⟨s.gpr .rbp, 272⟩)
    (Offset.contains_base _ offset (by omega)) ?_ (by decide)
  intro r hr; simp only [List.mem_singleton] at hr; subst r
  exact space.frameMatrix

theorem code_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s : State) (memory : Addr) (lanes q : Nat) (lo : 1 ≤ lanes) (hq : 2 ≤ q)
    (lanesBound : lanes < 2 ^ 64) (space : Space s memory (1024 * (lanes * q)))
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 184) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 240) 8)
    (memoryWord : wordAt s memoryOffset = memory)
    (lanesWord : wordAt s VG.Impl.Argon2.X86_64.Initial.lanesOffset = BitVec.ofNat 64 lanes)
    (blocksWord : wordAt s blocksOffset = BitVec.ofNat 64 (lanes * q))
    (laneLength : s.gpr .r13 = BitVec.ofNat 64 q) :
    WP isa (code name (HPrime.hash v)) s fun t =>
      Initialized t.mem memory lanes q lanes (bytesAt s.mem (s.gpr .rbp) 64) ∧
      t.gpr .rbp = s.gpr .rbp ∧ t.gpr .rbx = s.gpr .rbx ∧ t.gpr .rsp = s.gpr .rsp ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨memory, 1024 * (lanes * q)⟩, ⟨s.gpr .rbx, 16384⟩,
        below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem t.mem := by
  unfold code lanesSetupCode
  have blocksPositive : 1 ≤ lanes * q := by
    have mul := Nat.mul_le_mul_right q lo
    rw [Nat.one_mul] at mul; omega
  refine WP.seq ((clear_ok s memory (lanes * q) blocksPositive space.bound memoryRead
    blocksRead memoryWord blocksWord space.matrix).mono ?_)
  intro a ha
  have bpA := ha.other .rbp (by decide) (by decide) (by decide)
  have bxA := ha.other .rbx (by decide) (by decide) (by decide)
  have spA := ha.other .rsp (by decide) (by decide) (by decide)
  have spaceA := space.same ha.wr bpA bxA spA
  have hashA : bytesAt a.mem (a.gpr .rbp) 64 = bytesAt s.mem (s.gpr .rbp) 64 := by
    rw [bpA]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    exact (ha.frame space.bound).bytes (R := ⟨s.gpr .rbp, 64⟩) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact space.frameMatrix.sub_left (Region.sub_prefix (by decide)))
      (show (64 : Nat) ≤ 2 ^ 64 from by decide) hi
  refine WP.seq ((lanesSetup_ok a memory lanes q
    (by rw [ha.rd, ha.wr, bpA]; exact memoryRead)
    (by rw [ha.rd, ha.wr, bpA]; exact lanesRead)
    ((ha.word space (by decide)).trans memoryWord)
    ((ha.word space (by decide)).trans lanesWord)
    ((ha.other .r13 (by decide) (by decide) (by decide)).trans laneLength)).mono ?_)
  intro b hb
  have bpB := hb.other .rbp (by decide) (by decide) (by decide) (by decide)
  have bxB := hb.other .rbx (by decide) (by decide) (by decide) (by decide)
  have spB := hb.other .rsp (by decide) (by decide) (by decide) (by decide)
  have spaceB := spaceA.same hb.wr bpB bxB spB
  refine (lanesLoop_ok v name b memory lanes q (bytesAt s.mem (s.gpr .rbp) 64)
    spaceB lo lanesBound hq hb.destination hb.lane hb.remaining hb.stride ?_ ?_).mono ?_
  · rw [hb.mem, ha.mem]
    exact initialized_zero s.mem memory lanes q space.bound _
  · rw [hb.mem, bpB]; exact hashA
  · intro t ht
    refine ⟨ht.initialized, ht.keeps.rbp.trans (bpB.trans bpA),
      ht.keeps.rbx.trans (bxB.trans bxA), ht.keeps.rsp.trans (spB.trans spA),
      ht.keeps.rd.trans (hb.rd.trans ha.rd), ht.keeps.wr.trans (hb.wr.trans ha.wr), ?_⟩
    have fb : Frame [⟨memory, 1024 * (lanes * q)⟩, ⟨s.gpr .rbx, 16384⟩,
        below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem b.mem := by
      rw [hb.mem]
      exact (ha.frame space.bound).mono (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact List.mem_cons_self ..)
    apply fb.trans
    have f := ht.keeps.frame
    rw [bpB, bpA, bxB, bxA, spB, spA] at f
    exact f

/-- Every cell agrees with the reviewed initialization spec, in lane-major order. -/
theorem Initialized.spec {m : Mem} {base : Addr} {p : Spec.Argon2.Params}
    {h0 : List Byte} (hl : 0 < p.lanes) (hq : 0 < p.laneLen)
    (h : Initialized m base p.lanes p.laneLen p.lanes h0)
    (k : Nat) (hk : k < p.blocks) :
    Spec.Argon2.blockAt m (base + BitVec.ofNat 64 (1024 * k)) =
      (Spec.Argon2.initMemory p h0).memory[k]'(by
        rw [Proof.Argon2.initMemory_size]; exact hk) := by
  have blocks := Proof.Argon2.blocks_lanes p hl
  have lane : k / p.laneLen < p.lanes := by
    apply (Nat.div_lt_iff_lt_mul hq).mpr
    simpa only [blocks] using hk
  have cell := h (k / p.laneLen) lane (k % p.laneLen) (Nat.mod_lt _ hq)
  rw [Nat.mul_comm (k / p.laneLen) p.laneLen, Nat.div_add_mod] at cell
  simp only [lane, true_and] at cell
  rw [Proof.Argon2.initMemory_cell p h0 k hk]
  exact cell

end VG.Proof.Argon2.X86_64.MemoryInit
