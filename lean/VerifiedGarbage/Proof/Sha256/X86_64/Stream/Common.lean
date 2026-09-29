import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Compress
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Impl.Sha256.X86_64.Stream

/-!
# Streaming SHA-256 on x86-64: common lemmas

Untrusted: everything here is checked by Lean. The call of the compression
function (`compressAt`), for either `Callee`, and memory written byte by byte.
-/

namespace VG.Proof.Sha256.X86_64.Stream

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Stream
open VG.Impl.Sha256.X86_64 (at_)
open VG.Proof.Sha256.X86_64 (ea_at contains_offset contains_offset' toNat_ofNat_lt compress_verified)
open VG.Spec.Sha256 (HashValue stateAt blockAt compressBlocks compress parseBlock bytesAt)

/-! ## The compression functions -/

/-- What `compressAt` needs of the compression function it calls: that it is
correct and constant time, does not touch `rsp` or the stack, and keeps
`rdi` and `rcx`. -/
structure _root_.VG.Impl.Sha256.X86_64.Stream.Callee.Ok (f : Callee) : Prop where
  verified : ∀ s, Proof.Sha256.compressX86_64.pre s →
    ∃ t s', Exec isa f.code s t s' ∧ abiPreserved s s' ∧ Proof.Sha256.compressX86_64.post s s'
  ct : ConstantTime isa Proof.Sha256.compressX86_64.pre Proof.Sha256.compressX86_64.pub f.code
  nosp : NoSp f.code
  depth : f.code.depth = 0
  keeps_rdi : ∀ i ∈ instrs f.code, Taint.clobbers i .rdi = false
  keeps_rcx : ∀ i ∈ instrs f.code, Taint.clobbers i .rcx = false

/-- The facts about the instructions of `f`, from one kernel check each. -/
theorem _root_.VG.Impl.Sha256.X86_64.Stream.Callee.Ok.of_verified {f : Callee} (hv : ∀ s, Proof.Sha256.compressX86_64.pre s →
      ∃ t s', Exec isa f.code s t s' ∧ abiPreserved s s' ∧ Proof.Sha256.compressX86_64.post s s')
    (hct : ConstantTime isa Proof.Sha256.compressX86_64.pre Proof.Sha256.compressX86_64.pub f.code)
    (hk : ((instrs f.code).all fun i => !Taint.clobbers i .rdi && !Taint.clobbers i .rcx &&
      !Taint.clobbers i .rsp) = true)
    (hd : f.code.depth = 0) : f.Ok := by
  have h := fun i hi => List.all_eq_true.mp hk i hi
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨hv, hct, fun i hi => (h i hi).2, hd, fun i hi => (h i hi).1.1, fun i hi => (h i hi).1.2⟩

theorem scalar_ok : Callee.scalar.Ok :=
  .of_verified compress_verified.1 compress_verified.2.1 (by rw [← Code.allInstrs_eq]; decide +kernel) (by decide +kernel)

theorem shani_ok : Callee.shani.Ok :=
  .of_verified Proof.Sha256.X86_64.ShaNi.compress_verified.1
    Proof.Sha256.X86_64.ShaNi.compress_verified.2.1 (by rw [← Code.allInstrs_eq]; decide +kernel)
    (by decide +kernel)

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

/-- A region disjoint from the return address of a call reads the same on
entry to the callee. -/
theorem callEntry_byte (s : State) {R : Region} (hd : (below (s.gpr .rsp) 8).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    s.callEntry.mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (s.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using hd.symm) hR hi

/-- What the call of the compression function in `compressAt` needs of the
state `s` before it: the hash value `st` at `rbx`, the scratch space `scr` at
`r15` and the block `src` at `rsi` do not overlap each other or the return
address, and may be accessed. -/
structure CallOk (s : State) (st scr src : Addr) : Prop where
  rbx : s.gpr .rbx = st
  r15 : s.gpr .r15 = scr
  rsi : s.gpr .rsi = src
  d₁ : Region.Disjoint ⟨st, 32⟩ ⟨scr, 112⟩
  d₂ : Region.Disjoint ⟨src, 64⟩ ⟨st, 32⟩
  d₃ : Region.Disjoint ⟨src, 64⟩ ⟨scr, 112⟩
  d₄ : (below (s.gpr .rsp) 8).Disjoint ⟨st, 32⟩
  d₅ : (below (s.gpr .rsp) 8).Disjoint ⟨scr, 112⟩
  d₆ : (below (s.gpr .rsp) 8).Disjoint ⟨src, 64⟩
  hc : Covers [⟨src, 64⟩, ⟨st, 32⟩, ⟨scr, 112⟩] (s.rd ++ s.wr)
  hw : Covers [⟨st, 32⟩, ⟨scr, 112⟩] s.wr

/-- The arguments of the call, set up from `σ`. -/
structure Setup (σ s : State) : Prop where
  rdi : s.gpr .rdi = σ.gpr .rbx
  rdx : s.gpr .rdx = 1
  rcx : s.gpr .rcx = σ.gpr .r15
  rsi : s.gpr .rsi = σ.gpr .rsi
  cs : ∀ r ∈ calleeSaved, s.gpr r = σ.gpr r
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  mem : s.mem = σ.mem

theorem setup_ok (s : State) :
    WP isa (.block [.mov .rdi (.reg .rbx), .mov32 .rdx (.imm 1), .mov .rcx (.reg .r15)]) s (Setup s) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, readSrc32, isa, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by simp [State.setReg, State.setReg32], by simp [State.setReg, State.setReg32],
    by simp [State.setReg, State.setReg32], by simp [State.setReg, State.setReg32],
    fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [State.setReg, State.setReg32]

/-- The call's precondition, narrowed to the regions it is given. -/
theorem call_hyps {σ s : State} {st scr src : Addr} (h : CallOk σ st scr src) (hs : Setup σ s) :
    Proof.Sha256.compressX86_64.pre (s.callEntry.withRegions [⟨src, 64 * 1⟩] [⟨st, 32⟩, ⟨scr, 112⟩]) ∧
    Covers ([⟨src, 64 * 1⟩] ++ [⟨st, 32⟩, ⟨scr, 112⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨st, 32⟩, ⟨scr, 112⟩] s.wr := by
  have hsp : s.gpr .rsp = σ.gpr .rsp := hs.cs _ (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Sha256.compressX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp),
      hne _ (by decide : Reg.rcx ≠ .rsp), hs.rdi, hs.rdx, hs.rcx, hs.rsi, h.rbx, h.r15, h.rsi, hsp]
    exact ⟨by simp, by simp, h.d₁, h.d₂, h.d₃, h.d₄, h.d₅⟩
  · rw [hs.rd, hs.wr]; simpa using h.hc
  · rw [hs.wr]; exact h.hw

/-- Compressing the block at `rsi` into the hash value at `rbx`, with scratch
space at `r15`, by calling the compression function `f`. -/
theorem compressAt_ok {f : Callee} (hf : f.Ok) {s : State} {st scr src : Addr}
    (h : CallOk s st scr src) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 32⟩, ⟨scr, 112⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
      stateAt s'.mem st = compress (stateAt s.mem st) (blockAt s.mem src) →
      s'.gpr .rdi = st → s'.gpr .rcx = scr → Q s') :
    WP isa (compressAt f) s Q := by
  unfold compressAt
  refine WP.seq (WP.mono (setup_ok s) fun s₁ hs => ?_)
  have e₁ : s₁.gpr .rdi = st := hs.rdi.trans h.rbx
  have e₂ := hs.rdx
  have e₃ : s₁.gpr .rcx = scr := hs.rcx.trans h.r15
  have e₄ : s₁.gpr .rsi = src := hs.rsi.trans h.rsi
  have e₅ := hs.cs
  have hsp : s₁.gpr .rsp = s.gpr .rsp := e₅ _ (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr _ h
  obtain ⟨hpre, hc, hw⟩ := call_hyps h hs
  refine WP.seq (WP.call (k := Proof.Sha256.compressX86_64) hf.verified hf.nosp (by rw [hf.depth]; decide)
    (rd := [⟨src, 64 * 1⟩]) (wr := [⟨st, 32⟩, ⟨scr, 112⟩]) hpre hc hw ?_)
  intro s₂ hrd hwr hcs hfr hkeep ⟨s₃, hm₃, _, hpost⟩
  have k₁ := hkeep .rdi hf.keeps_rdi
  have k₃ := hkeep .rcx hf.keeps_rcx
  simp only [Proof.Sha256.compressX86_64, State.withRegions_gpr, State.withRegions_mem,
    hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
    hne _ (by decide : Reg.rdx ≠ .rsp), e₁, e₂, e₄, hm₃] at hpost
  rw [show (1 : BitVec 64).toNat = 1 from rfl, compressBlocks_one] at hpost
  have hst : stateAt s₁.callEntry.mem st = stateAt s.mem st :=
    (Proof.Sha256.Stream.stateAt_congr fun i hi => callEntry_byte s₁ (R := ⟨st, 32⟩) (by rw [hsp]; exact h.d₄)
      (by simp) hi).trans (by rw [hs.mem])
  have hblk : blockAt s₁.callEntry.mem src = blockAt s.mem src := by
    simp only [Spec.Sha256.blockAt]
    apply Proof.Sha256.Stream.parseBlock_congr
    intro k hk
    rw [callEntry_byte s₁ (R := ⟨src, 64⟩) (by rw [hsp]; exact h.d₆) (by simp) hk, hs.mem]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, isa, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine hQ _ (hrd.trans hs.rd) (hwr.trans hs.wr) (fun r hr => ?_) (by
    rw [hf.depth, hsp, hs.mem] at hfr; simpa [State.setReg] using hfr)
    (by simp only [State.setReg]; rw [hpost, hst, hblk]) (by simp [State.setReg, k₁, e₁])
    (by simp [State.setReg, k₃, e₃])
  have h₂ := hcs r hr
  simp only [State.setReg]
  by_cases h15 : r = .r15
  · subst h15; simp [k₃, e₃, h.r15]
  · by_cases hbx : r = .rbx
    · subst hbx; simp [k₁, e₁, h.rbx]
    · simp [h15, hbx, h₂, e₅ r hr]

/-- `compressAt` is constant time for any compression function `f`, in runs
that agree on its arguments. -/
theorem compressAt_rel {f : Callee} (hf : f.Ok) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → (∃ a b c, CallOk s₁ a b c) ∧ (∃ a b c, CallOk s₂ a b c) ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .r15 = s₂.gpr .r15 ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (compressAt f) fun _ _ => True := by
  unfold compressAt
  have su := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov .rdi (.reg .rbx), .mov32 .rdx (.imm 1), .mov .rcx (.reg .r15)])
    (by taint_decide)).wpDep (F := Setup) fun s₁ s₂ _ => ⟨setup_ok s₁, setup_ok s₂⟩
  have cl := RelCT.callEx (n := f.name) (k := Proof.Sha256.compressX86_64)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ Setup σ₁ s₁ ∧ Setup σ₂ s₂) hf.verified hf.ct
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨⟨_, _, _, k₁⟩, ⟨_, _, _, k₂⟩, ebx, e15, esi, esp⟩ := hP _ _ hp
      obtain ⟨p₁, c₁, w₁⟩ := call_hyps k₁ h₁
      obtain ⟨p₂, c₂, w₂⟩ := call_hyps k₂ h₂
      refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂, ?_⟩
      · simp only [Proof.Sha256.compressX86_64, State.withRegions_gpr,
          State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp)]
        exact ⟨by rw [h₁.rdi, h₂.rdi, ebx], by rw [h₁.rsi, h₂.rsi, esi], by rw [h₁.rdx, h₂.rdx],
          by rw [h₁.rcx, h₂.rcx, e15]⟩
      · rw [h₁.cs _ (by simp [calleeSaved]), h₂.cs _ (by simp [calleeSaved]), esp]
  have tl := RelCT.taint (A := taint) (P := fun _ _ => True) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block [.mov .rbx (.reg .rdi), .mov .r15 (.reg .rcx)])
    (by taint_decide)
  exact su.seq (cl.seq tl)

/-! ## One instruction at a time

Weakest-precondition rules for the instruction forms used here, exposing
only what changes, so that proofs about a block stay small. -/

/-- `s'` is `s` with register `d` set to `v` (flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.flags (s : State) {w : Nat} (d : Reg) (x : BitVec w) (c o : Bool) (v : BitVec 64) :
    Upd s ((arithFlags s x c o).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr r) → s'.zf = s.zf → s'.cf = s.cf →
    WP isa (.block is) s' Q) : WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl rfl)

theorem wp_mov32i {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (v.setWidth 64) → s'.zf = s.zf →
    s'.cf = s.cf → WP isa (.block is) s' Q) : WP isa (.block (.mov32 d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl rfl)

theorem wp_addi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d - v.signExtend 64) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_sub {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d - s.gpr r) → s'.zf = some (s.gpr d - s.gpr r == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_add {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d + s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_mov32m {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem.readW a 32).setWidth 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, readSrc32, State.load32, State.setReg32, ha, hin]

theorem wp_bswap32 {d : Reg}
    (k : ∀ s', Upd s s' d ((bswap32 ((s.gpr d).setWidth 32)).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.bswap32 d :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_store32 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr r).setWidth 32) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store32 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r).setWidth 32) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store32, ha, hout]

theorem wp_movm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' d (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d (s.mem.readW a 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, readSrc, State.load64, ha, hin]

theorem wp_andi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- `cmp d, r`: CF is `d < r` (unsigned). -/
theorem wp_cmp {d r : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (s.gpr r).toNat)) →
      s'.zf = some (s.gpr d - s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

theorem wp_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (v.signExtend 64).toNat)) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

theorem wp_test {d : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl)

theorem wp_movzx8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' d ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem a).setWidth 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, State.load8, ha, hin]

theorem wp_store8 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr r).setWidth 8) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r).setWidth 8) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store8, ha, hout]

theorem wp_store {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a (s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store64, ha, hout]

theorem wp_bswap {d : Reg}
    (k : ∀ s', Upd s s' d (bswap64 (s.gpr d)) → WP isa (.block is) s' Q) :
    WP isa (.block (.bswap d :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

end

/-! ## Byte order -/

theorem bswap32_bytes' (w : BitVec 32) :
    (List.range 4).map (fun j => (bswap32 w).extractLsb' (8 * j) 8) = Spec.Sha256.wordBytes w := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, Spec.Sha256.wordBytes, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [bswap32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    interval_cases i <;> simp

theorem bswap64_bytes (x : BitVec 64) :
    (List.range 8).map (fun j => (bswap64 x).extractLsb' (8 * j) 8) =
      (List.range 8).reverse.map (fun i => x.extractLsb' (8 * i) 8) := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.reverse_cons, List.reverse_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [bswap64, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    interval_cases i <;> simp

/-! ## Lemmas shared by `update` and `finalize` -/

theorem and63 (x : BitVec 64) : x &&& (63#32).signExtend 64 = BitVec.ofNat 64 (x.toNat % 64) := by
  rw [show (63#32).signExtend 64 = 63#64 by decide]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem restore_eq : restore = [
    .mov .rbx (.mem (at_ .r15 112)), .mov .rbp (.mem (at_ .r15 120)), .mov .r12 (.mem (at_ .r15 128)),
    .mov .r13 (.mem (at_ .r15 136)), .mov .r14 (.mem (at_ .r15 144)), .mov .r15 (.mem (at_ .r15 152))] :=
  rfl

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  rw [BitVec.ofNat_add]; rfl

theorem ofNat_pred {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, ofNat_succ, Nat.add_sub_cancel, BitVec.add_sub_cancel]

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem bytesAt_getD {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (h : bytesAt m p n = l) {k : Nat}
    (hk : k < n) : m (p + BitVec.ofNat 64 k) = l.getD k 0 := by
  subst h; simp [bytesAt, List.getD_eq_getElem?_getD, hk]

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  conv_lhs => rw [show a = (a - b) + b by omega, BitVec.ofNat_add]
  rw [BitVec.add_sub_cancel]

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

end VG.Proof.Sha256.X86_64.Stream
