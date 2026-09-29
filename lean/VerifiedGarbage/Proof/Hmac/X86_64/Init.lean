import VerifiedGarbage.Proof.Hmac.X86_64.Common
import VerifiedGarbage.Proof.Hmac.X86_64.Contract
import Mathlib.Tactic.Set

/-!
# HMAC-SHA-256 on x86-64: `init`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Hmac.X86_64.Init

open VG VG.X86_64 VG.Impl.Hmac.X86_64
open VG.Impl.Sha256.X86_64 (at_)
open VG.Impl.Sha256.X86_64.Stream (Callee save restore compressAt)
open VG.Proof.Hmac.X86_64
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame repr_congr repr_nil repr_append_block)
open VG.Proof.Sha256.X86_64 (ea_at contains_offset contains_offset' toNat_ofNat_lt sub_offset ofInt_natCast
  writeState stateAt_writeState readW_writeW_save)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov wp_mov32i wp_addi wp_cmp wp_cmpi wp_test wp_movzx8 wp_store8
  CallOk compressAt_ok compressAt_rel ofNat_succ sub_beq ofNat_beq_zero)
open VG.Proof.Sha256.X86_64.Stream.Update (Saved saveMem saveMem_saved saveMem_frame)
open VG.Spec.Sha256 (bytesAt stateAt Repr H0)
open VG.Spec.Hmac (xorPad ipad opad blockKey sha256)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .rdi
abbrev out : Addr := s₀.gpr .rsi
abbrev kp : Addr := s₀.gpr .rdx
abbrev kl : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev inR : Region := ⟨inn s₀, 96⟩
abbrev outR : Region := ⟨out s₀, 96⟩
abbrev kR : Region := ⟨kp s₀, kl s₀⟩
abbrev scR : Region := ⟨scr s₀, 160⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- Where the calls of the compression function store their return address. -/
abbrev stkR : Region := below (s₀.gpr .rsp) 8

/-- The key, padded with zeros to a block. -/
def K0 : List Byte := bytesAt s₀.mem (kp s₀) (kl s₀) ++ List.replicate (64 - kl s₀) 0

end

structure Pre (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ 64
  rd : s₀.rd = [kR s₀]
  wr : s₀.wr = [inR s₀, outR s₀, scR s₀]
  i_o : (inR s₀).Disjoint (outR s₀)
  i_s : (inR s₀).Disjoint (scR s₀)
  o_s : (outR s₀).Disjoint (scR s₀)
  k_i : (kR s₀).Disjoint (inR s₀)
  k_o : (kR s₀).Disjoint (outR s₀)
  k_s : (kR s₀).Disjoint (scR s₀)
  ret_i : (retR s₀).Disjoint (inR s₀)
  ret_o : (retR s₀).Disjoint (outR s₀)
  ret_s : (retR s₀).Disjoint (scR s₀)
  stk_i : (stkR s₀).Disjoint (inR s₀)
  stk_o : (stkR s₀).Disjoint (outR s₀)
  stk_k : (stkR s₀).Disjoint (kR s₀)
  stk_s : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Hmac.initSha256X86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-- The return address and the 8 bytes below it. -/
theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

theorem K0_length (s₀ : State) (hp : Pre s₀) : (K0 s₀).length = 64 := by
  simp [K0, bytesAt_length]; have := hp.kl_le; omega

theorem blockKey_eq {s₀ : State} (hp : Pre s₀) :
    blockKey sha256 (bytesAt s₀.mem (kp s₀) (kl s₀)) = K0 s₀ := by
  have := hp.kl_le
  simp [blockKey, sha256, K0, bytesAt_length, show ¬ (64 < kl s₀) by omega]

/-! ## Prologue -/

set_option simprocs false in
theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save .r8)) s₀ fun s =>
      s.mem = saveMem s₀ ∧ s.gpr = s₀.gpr ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have o : ∀ d : Nat, d + 8 ≤ 160 → InRegions s₀.wr (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨scR s₀, by simp [hp.wr], contains_offset' hd (by omega)⟩
  have o0 := o 112 (by omega); have o1 := o 120 (by omega); have o2 := o 128 (by omega)
  have o3 := o 136 (by omega); have o4 := o 144 (by omega); have o5 := o 152 (by omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [save, Impl.Sha256.X86_64.Stream.saved, List.map_cons,
    List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec,
        isa, ea_at, State.store64, o0, o1, o2, o3, o4, o5, ite_true,
    Option.some.injEq, exists_eq_left']
  trivial

theorem h0_eq (b : Reg) : h0 b = [
    .mov32 .rax (.imm 0x6a09e667), .store32 (at_ b (4 * 0)) .rax,
    .mov32 .rax (.imm 0xbb67ae85), .store32 (at_ b (4 * 1)) .rax,
    .mov32 .rax (.imm 0x3c6ef372), .store32 (at_ b (4 * 2)) .rax,
    .mov32 .rax (.imm 0xa54ff53a), .store32 (at_ b (4 * 3)) .rax,
    .mov32 .rax (.imm 0x510e527f), .store32 (at_ b (4 * 4)) .rax,
    .mov32 .rax (.imm 0x9b05688c), .store32 (at_ b (4 * 5)) .rax,
    .mov32 .rax (.imm 0x1f83d9ab), .store32 (at_ b (4 * 6)) .rax,
    .mov32 .rax (.imm 0x5be0cd19), .store32 (at_ b (4 * 7)) .rax] := rfl

set_option simprocs false in
/-- `H⁽⁰⁾` stored at `b`. -/
theorem h0_ok {b : Reg} (hb : b ≠ .rax) {s : State} {rest : List Instr} {Q : State → Prop}
    (hin : ∀ k < 8, InRegions s.wr (s.gpr b + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4)
    (k : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeState s.mem (s.gpr b) H0 → WP isa (.block rest) s' Q) :
    WP isa (.block (h0 b ++ rest)) s Q := by
  refine WP.block_append (WP.of_runBlock ?_)
  have o0 := hin 0 (by omega); have o1 := hin 1 (by omega); have o2 := hin 2 (by omega)
  have o3 := hin 3 (by omega); have o4 := hin 4 (by omega); have o5 := hin 5 (by omega)
  have o6 := hin 6 (by omega); have o7 := hin 7 (by omega)
  rw [h0_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc32, isa, ea_at, State.store32,
    State.setReg32, State.setReg, hb, o0, o1, o2, o3, o4, o5, o6, o7, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact k _ (fun r hr => by simp [hr]) rfl rfl rfl

/-- Writing a hash value stays within its 32 bytes. -/
theorem writeState_frame (m : Mem) (p : Addr) (v : Spec.Sha256.HashValue) :
    Frame [⟨p, 32⟩] m (writeState m p v) := by
  have c : ∀ k, k < 8 → (⟨p, 32⟩ : Region).Contains (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) (32 / 8) :=
    fun k hk => contains_offset' (by omega) (by omega)
  simp only [writeState]
  refine (((((((((Frame.refl _ _).writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _
    (c 2 ?_)).writeW ?_ _ (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _
    (c 6 ?_)).writeW ?_ _ (c 7 ?_)) <;> simp

/-! ## The key block -/

/-- The memory while building the two buffers: `j` bytes of `K₀ ⊕ ipad` and
`K₀ ⊕ opad` are written. -/
structure BufMem (s₀ : State) (j : Nat) (m : Mem) : Prop where
  stI : stateAt m (inn s₀) = H0
  stO : stateAt m (out s₀) = H0
  bufI : bytesAt m (inn s₀ + 32) j = ((K0 s₀).take j).map (· ^^^ ipad)
  bufO : bytesAt m (out s₀ + 32) j = ((K0 s₀).take j).map (· ^^^ opad)
  saved : Saved s₀ m
  frame : Frame [inR s₀, outR s₀, scR s₀] s₀.mem m

structure Buf (s₀ : State) (j : Nat) (s : State) : Prop where
  j_le : j ≤ 64
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = inn s₀
  r12 : s.gpr .r12 = out s₀
  r15 : s.gpr .r15 = scr s₀
  rbp : s.gpr .rbp = kp s₀
  r13 : s.gpr .r13 = s₀.gpr .rcx
  r14 : s.gpr .r14 = BitVec.ofNat 64 j
  rsp : s.gpr .rsp = s₀.gpr .rsp
  mem : BufMem s₀ j s.mem

theorem sub32 (p : Addr) : Region.Sub ⟨p, 32⟩ ⟨p, 96⟩ := Region.sub_prefix (by omega)

/-- `Saved` survives a write outside the scratch space's save area. -/
theorem saved_frame {s₀ : State} {m m' : Mem} (h : Saved s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (scR s₀).Disjoint r) : Saved s₀ m' := by
  intro p hp'
  rw [← h p hp']
  simp only [Impl.Sha256.X86_64.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  have hd' : 112 ≤ p.2 ∧ p.2 + 8 ≤ 160 := by rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  refine hf.readW (r := ⟨scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  exact (hd r hr).sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega) (by omega))

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save .r8 ++ ([.mov .rbx (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r15 (.reg .r8),
      .mov .rbp (.reg .rdx), .mov .r13 (.reg .rcx)] : List Instr) ++ h0 .rbx ++ h0 .r12 ++
      ([.mov32 .r14 (.imm 0), .alu .test .r13 (.reg .r13)] : List Instr))) s₀
      fun s => Buf s₀ 0 s ∧ s.zf = some (decide (kl s₀ = 0)) := by
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (save_ok hp) fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => ?_)
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    wp_mov fun s₆ u₆ _ _ => ?_
  have k₆ : ∀ r, r ∉ [Reg.rbx, .r12, .r15, .rbp, .r13] → s₆.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other r hr.2.2.2.2, u₅.other r hr.2.2.2.1, u₄.other r hr.2.2.1, u₃.other r hr.2.1,
      u₂.other r hr.1, g₁]
  have hbx : s₆.gpr .rbx = inn s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, g₁]
  have h12 : s₆.gpr .r12 = out s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      g₁]
  have h15 : s₆.gpr .r15 = scr s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      g₁]
  have hbp : s₆.gpr .rbp = kp s₀ := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      g₁]
  have h13 : s₆.gpr .r13 = s₀.gpr .rcx := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      g₁]
  have m₆ : s₆.mem = saveMem s₀ := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  refine h0_ok (by decide) (fun k hk => ⟨inR s₀, by simp [wr₆, hp.wr], by
    rw [hbx]; exact contains_offset' (by omega) (by omega)⟩) fun s₇ g₇ rd₇ wr₇ m₇ => ?_
  refine h0_ok (by decide) (fun k hk => ⟨outR s₀, by simp [wr₇, wr₆, hp.wr], by
    rw [g₇ _ (by decide), h12]; exact contains_offset' (by omega) (by omega)⟩) fun s₈ g₈ rd₈ wr₈ m₈ => ?_
  refine wp_mov32i fun s₉ u₉ _ _ => wp_test fun s₁₀ g₁₀ m₁₀ rd₁₀ wr₁₀ z₁₀ => WP.block_nil ⟨?_, ?_⟩
  have k : ∀ r, r ≠ .rax → r ≠ .r14 → s₁₀.gpr r = s₆.gpr r := fun r h h' => by
    rw [g₁₀, u₉.other r h', g₈ r h, g₇ r h]
  rw [hbx] at m₇
  rw [g₇ _ (by decide), h12] at m₈
  have hm : s₁₀.mem = writeState (writeState (saveMem s₀) (inn s₀) H0) (out s₀) H0 := by
    rw [m₁₀, u₉.mem, m₈, m₇, m₆]
  have fI := writeState_frame (saveMem s₀) (inn s₀) H0
  have fO := writeState_frame (writeState (saveMem s₀) (inn s₀) H0) (out s₀) H0
  have ds : ∀ p : Addr, ∀ r : Region, r.Disjoint ⟨p, 96⟩ → r.Disjoint ⟨p, 32⟩ :=
    fun p r h => h.sub_right (sub32 p)
  refine ⟨by omega, by rw [rd₁₀, u₉.rd, rd₈, rd₇, rd₆], by rw [wr₁₀, u₉.wr, wr₈, wr₇, wr₆],
    by rw [k _ (by decide) (by decide), hbx], by rw [k _ (by decide) (by decide), h12],
    by rw [k _ (by decide) (by decide), h15], by rw [k _ (by decide) (by decide), hbp],
    by rw [k _ (by decide) (by decide), h13], by rw [g₁₀, u₉.gpr]; rfl,
    by rw [k _ (by decide) (by decide), k₆ _ (by decide)], ⟨?_, ?_, by simp [bytesAt], by simp [bytesAt],
    ?_, ?_⟩⟩
  · rw [hm]
    refine (Proof.Sha256.Stream.stateAt_congr fun i hi => ?_).trans (stateAt_writeState (saveMem s₀) _ _)
    exact fO.bytes (R := ⟨inn s₀, 32⟩) (by simpa using ds _ _ (hp.i_o.sub_left (sub32 _))) (by simp) hi
  · rw [hm, stateAt_writeState]
  · rw [hm]
    refine saved_frame (saved_frame saveMem_saved fI ?_) fO ?_ <;> simp only [List.mem_singleton] <;>
      rintro r rfl
    · exact ds _ _ hp.i_s.symm
    · exact ds _ _ hp.o_s.symm
  · rw [hm]
    refine ((saveMem_frame.mono ?_).trans (fI.sub ?_)).trans (fO.sub ?_)
    · simp
    · simp only [List.mem_singleton]; rintro r rfl; exact ⟨inR s₀, by simp, sub32 _⟩
    · simp only [List.mem_singleton]; rintro r rfl; exact ⟨outR s₀, by simp, sub32 _⟩
  · rw [z₁₀, u₉.other _ (by decide), g₈ _ (by decide), g₇ _ (by decide), h13, BitVec.and_self]
    by_cases h : kl s₀ = 0
    · simp [h, BitVec.eq_of_toNat_eq (show (s₀.gpr .rcx).toNat = (0 : BitVec 64).toNat from h)]
    · simp only [h, decide_false]
      simp only [Option.some.injEq, beq_eq_false_iff_ne, ne_eq]
      intro h'; exact h (by show (s₀.gpr .rcx).toNat = 0; rw [h']; rfl)

/-- A byte written right after `j` bytes. -/
theorem bytesAt_snoc (m : Mem) (p : Addr) {j : Nat} (hj : j + 1 < 2 ^ 64) (x : Byte) :
    bytesAt (m.writeW (p + BitVec.ofNat 64 j) x) p (j + 1) = bytesAt m p j ++ [x] := by
  rw [bytesAt_add]
  congr 1
  · simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    simp only [Mem.writeW]
    refine Mem.write_apply ?_
    rw [show p + BitVec.ofNat 64 i - (p + BitVec.ofNat 64 j) = BitVec.ofNat 64 i - BitVec.ofNat 64 j by bv_omega,
      BitVec.toNat_sub, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
    omega
  · have e : p + BitVec.ofNat 64 j + BitVec.ofNat 64 0 - (p + BitVec.ofNat 64 j) = 0 := by bv_omega
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, Mem.writeW, Mem.write, e,
]
    simp

/-- The two buffer bytes `j`. -/
theorem buf_write {s₀ : State} (hp : Pre s₀) {j : Nat} {m : Mem} (h : BufMem s₀ j m) (hj : j < 64) :
    BufMem s₀ (j + 1) ((m.writeW (inn s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j]'(by rw [K0_length s₀ hp]; omega) ^^^ ipad)).writeW
      (out s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j]'(by rw [K0_length s₀ hp]; omega) ^^^ opad)) := by
  have hl : j < (K0 s₀).length := by rw [K0_length s₀ hp]; omega
  set x := (K0 s₀)[j] ^^^ ipad
  set y := (K0 s₀)[j] ^^^ opad
  let bI : Region := ⟨inn s₀ + 32, 64⟩
  let bO : Region := ⟨out s₀ + 32, 64⟩
  have sI : Region.Sub bI (inR s₀) := sub_offset (off := 32) (by omega) (by omega)
  have sO : Region.Sub bO (outR s₀) := sub_offset (off := 32) (by omega) (by omega)
  have f₁ : Frame [bI] m (m.writeW (inn s₀ + 32 + BitVec.ofNat 64 j) x) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) x (contains_offset (by omega) (by omega))
  have f₂ : Frame [bO] (m.writeW (inn s₀ + 32 + BitVec.ofNat 64 j) x)
      ((m.writeW (inn s₀ + 32 + BitVec.ofNat 64 j) x).writeW (out s₀ + 32 + BitVec.ofNat 64 j) y) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) y (contains_offset (by omega) (by omega))
  have F := (f₁.mono (rs' := [bI, bO]) (by simp)).trans (f₂.mono (by simp))
  have dIO : bI.Disjoint bO := (hp.i_o.sub_left sI).sub_right sO
  have st : ∀ p : Addr, (∀ r ∈ [bI, bO], Region.Disjoint ⟨p, 32⟩ r) →
      stateAt ((m.writeW (inn s₀ + 32 + BitVec.ofNat 64 j) x).writeW (out s₀ + 32 + BitVec.ofNat 64 j) y) p =
        stateAt m p :=
    fun p hd => Proof.Sha256.Stream.stateAt_congr fun i hi => F.bytes (R := ⟨p, 32⟩) hd (by simp) hi
  have self : ∀ q : Addr, Region.Disjoint ⟨q, 32⟩ ⟨q + 32, 64⟩ := fun q a h₁ h₂ => by
    simp only [Region.Contains] at h₁ h₂; bv_omega
  refine ⟨?_, ?_, ?_, ?_, saved_frame h.saved F ?_, h.frame.trans (F.sub ?_)⟩
  · rw [st _ ?_, h.stI]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact self _
    · exact (hp.i_o.sub_left (sub32 _)).sub_right sO
  · rw [st _ ?_, h.stO]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact (hp.i_o.symm.sub_left (sub32 _)).sub_right sI
    · exact self _
  · rw [Proof.Sha256.Stream.bytesAt_congr (fun i hi => f₂.bytes (R := ⟨inn s₀ + 32, j + 1⟩) ?_ (by simp; omega) hi),
      bytesAt_snoc _ _ (by omega), h.bufI, List.take_succ_eq_append_getElem hl, List.map_append]
    · rfl
    · simp only [List.mem_singleton]; rintro r rfl
      exact dIO.sub_left (Region.sub_prefix (by omega))
  · rw [bytesAt_snoc _ _ (by omega),
      Proof.Sha256.Stream.bytesAt_congr (fun i hi => f₁.bytes (R := ⟨out s₀ + 32, j⟩) ?_ (by simp; omega) hi),
      h.bufO, List.take_succ_eq_append_getElem hl, List.map_append]
    · rfl
    · simp only [List.mem_singleton]; rintro r rfl
      exact dIO.symm.sub_left (Region.sub_prefix (by omega))
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.i_s.symm.sub_right sI
    · exact hp.o_s.symm.sub_right sO
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact ⟨inR s₀, by simp, sI⟩
    · exact ⟨outR s₀, by simp, sO⟩

/-! ## The key and pad loops -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov32r {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr r).setWidth 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.reg r) :: is)) s Q :=
  Proof.Sha256.X86_64.Stream.WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_xor32i {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (((s.gpr d).setWidth 32 ^^^ v).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu32 .xor d (.imm v) :: is)) s Q :=
  Proof.Sha256.X86_64.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

end

theorem xor_byte (b : Byte) (v : BitVec 32) :
    ((((b.setWidth 64).setWidth 32) ^^^ v).setWidth 64).setWidth 8 = b ^^^ v.setWidth 8 := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

theorem xor_byte' (b : Byte) (v : BitVec 32) :
    ((((((b.setWidth 64).setWidth 32).setWidth 64).setWidth 32) ^^^ v).setWidth 64).setWidth 8 =
      b ^^^ v.setWidth 8 := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

theorem K0_lt {s₀ : State} {j : Nat} (hj : j < kl s₀) (h : j < (K0 s₀).length) :
    (K0 s₀)[j] = s₀.mem (kp s₀ + BitVec.ofNat 64 j) := by
  simp only [K0]
  rw [List.getElem_append_left (by rw [bytesAt_length]; exact hj)]
  simp [bytesAt]

theorem K0_ge {s₀ : State} {j : Nat} (hj : kl s₀ ≤ j) (h : j < (K0 s₀).length) : (K0 s₀)[j] = 0 := by
  simp only [K0]
  rw [List.getElem_append_right (by rw [bytesAt_length]; exact hj)]
  simp

theorem bufAt_ea (s : State) (b : Reg) (j : Nat) (hr14 : s.gpr .r14 = BitVec.ofNat 64 j) :
    s.ea (bufAt b) = s.gpr b + 32 + BitVec.ofNat 64 j := by
  simp only [State.ea, bufAt, hr14, BitVec.mul_one, show BitVec.ofInt 64 32 = 32 from rfl]
  ac_rfl

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
theorem sx64 : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 := by decide

/-- The key loop's body: byte `j` of the key. -/
def keyBody : List Instr :=
  [.movzx8 .rax { base := .rbp, index := some .r14, scale := 1 }, .mov32 .rcx (.reg .rax),
    .alu32 .xor .rax (.imm 0x36), .store8 (bufAt .rbx) .rax, .alu32 .xor .rcx (.imm 0x5c),
    .store8 (bufAt .r12) .rcx, .alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r13)]

theorem keyLoop_eq : keyLoop = .loop (.block keyBody) .ne := rfl

theorem key_step {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : j < kl s₀) {s : State} (h : Buf s₀ j s) :
    WP isa (.block keyBody) s fun s' => Buf s₀ (j + 1) s' ∧ s'.zf = some (decide (j + 1 = kl s₀)) := by
  have hkl := hp.kl_le
  have hl : j < (K0 s₀).length := by rw [K0_length s₀ hp]; omega
  have hin : InRegions (s.rd ++ s.wr) (kp s₀ + BitVec.ofNat 64 j) 1 :=
    ⟨kR s₀, by simp [h.rd, hp.rd], contains_offset (by omega) (by omega)⟩
  have hbyte : s.mem (kp s₀ + BitVec.ofNat 64 j) = (K0 s₀)[j] := by
    rw [K0_lt hj hl]
    refine h.mem.frame.bytes (R := kR s₀) ?_ (by show kl s₀ ≤ 2 ^ 64; omega) hj
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.k_i
    · exact hp.k_o
    · exact hp.k_s
  have hoI : InRegions s.wr (inn s₀ + 32 + BitVec.ofNat 64 j) 1 :=
    ⟨inR s₀, by simp [h.wr, hp.wr], by
      rw [BitVec.add_assoc, show (32 : Addr) + BitVec.ofNat 64 j = BitVec.ofNat 64 (32 + j) by
        rw [BitVec.ofNat_add]; rfl]
      exact contains_offset (by omega) (by omega)⟩
  have hoO : InRegions s.wr (out s₀ + 32 + BitVec.ofNat 64 j) 1 :=
    ⟨outR s₀, by simp [h.wr, hp.wr], by
      rw [BitVec.add_assoc, show (32 : Addr) + BitVec.ofNat 64 j = BitVec.ofNat 64 (32 + j) by
        rw [BitVec.ofNat_add]; rfl]
      exact contains_offset (by omega) (by omega)⟩
  unfold keyBody
  refine wp_movzx8 (a := kp s₀ + BitVec.ofNat 64 j) (by simp [State.ea, h.rbp, h.r14]) hin fun s₁ u₁ => ?_
  refine wp_mov32r fun s₂ u₂ => wp_xor32i fun s₃ u₃ => ?_
  refine wp_store8 (a := inn s₀ + 32 + BitVec.ofNat 64 j) ?_ (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hoI)
    fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  · rw [bufAt_ea _ _ j (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r14]),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.rbx]
  refine wp_xor32i fun s₅ u₅ => ?_
  refine wp_store8 (a := out s₀ + 32 + BitVec.ofNat 64 j) ?_
    (by rw [u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr]; exact hoO) fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  · rw [bufAt_ea _ _ j (by rw [u₅.other _ (by decide), g₄, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.r14]), u₅.other _ (by decide), g₄, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r12]
  refine wp_addi fun s₇ u₇ => wp_cmp fun s₈ g₈ m₈ rd₈ wr₈ _ z₈ => WP.block_nil ?_
  have k : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r14 → s₈.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [g₈, u₇.other r h3, g₆, u₅.other r h2, g₄, u₃.other r h1, u₂.other r h2, u₁.other r h1]
  have h14 : s₈.gpr .r14 = BitVec.ofNat 64 (j + 1) := by
    rw [g₈, u₇.gpr, g₆, u₅.other _ (by decide), g₄, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.r14, sx1, ofNat_succ]
  refine ⟨?_, ?_⟩
  · refine ⟨by omega, by rw [rd₈, u₇.rd, rd₆, u₅.rd, rd₄, u₃.rd, u₂.rd, u₁.rd, h.rd],
      by rw [wr₈, u₇.wr, wr₆, u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr, h.wr],
      by rw [k _ (by decide) (by decide) (by decide), h.rbx], by rw [k _ (by decide) (by decide) (by decide), h.r12],
      by rw [k _ (by decide) (by decide) (by decide), h.r15], by rw [k _ (by decide) (by decide) (by decide), h.rbp],
      by rw [k _ (by decide) (by decide) (by decide), h.r13], h14,
      by rw [k _ (by decide) (by decide) (by decide), h.rsp], ?_⟩
    have v₁ : (s₃.gpr .rax).setWidth 8 = (K0 s₀)[j] ^^^ ipad := by
      rw [u₃.gpr, u₂.other .rax (by decide), u₁.gpr, xor_byte, hbyte]; rfl
    have v₂ : (s₅.gpr .rcx).setWidth 8 = (K0 s₀)[j] ^^^ opad := by
      rw [u₅.gpr, g₄, u₃.other .rcx (by decide), u₂.gpr, u₁.gpr, xor_byte', hbyte]; rfl
    have hm : s₈.mem = (s.mem.writeW (inn s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j] ^^^ ipad)).writeW
        (out s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j] ^^^ opad) := by
      rw [m₈, u₇.mem, m₆, v₂, u₅.mem, m₄, v₁, u₃.mem, u₂.mem, u₁.mem]
    rw [hm]
    exact buf_write hp h.mem (by omega)
  · rw [z₈, ← g₈, h14, g₈, ← g₈, k _ (by decide) (by decide) (by decide), h.r13,
      show s₀.gpr .rcx = BitVec.ofNat 64 (kl s₀) by simp, sub_beq (by omega) (by omega)]

def padBody : List Instr :=
  [.store8 (bufAt .rbx) .rax, .store8 (bufAt .r12) .rcx, .alu .add .r14 (.imm 1), .alu .cmp .r14 (.imm 64)]

theorem padLoop_eq : padLoop = .loop (.block padBody) .ne := rfl

/-- In the pad loop, `rax` and `rcx` hold `ipad` and `opad`. -/
structure Pad (s₀ : State) (j : Nat) (s : State) : Prop extends Buf s₀ j s where
  rax : s.gpr .rax = (0x36 : BitVec 32).setWidth 64
  rcx : s.gpr .rcx = (0x5c : BitVec 32).setWidth 64

theorem pad_step {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : kl s₀ ≤ j) (hj' : j < 64) {s : State}
    (h : Pad s₀ j s) :
    WP isa (.block padBody) s fun s' => Pad s₀ (j + 1) s' ∧ s'.zf = some (decide (j + 1 = 64)) := by
  have hl : j < (K0 s₀).length := by rw [K0_length s₀ hp]; omega
  have hoI : InRegions s.wr (inn s₀ + 32 + BitVec.ofNat 64 j) 1 :=
    ⟨inR s₀, by simp [h.wr, hp.wr], by
      rw [BitVec.add_assoc, show (32 : Addr) + BitVec.ofNat 64 j = BitVec.ofNat 64 (32 + j) by
        rw [BitVec.ofNat_add]; rfl]
      exact contains_offset (by omega) (by omega)⟩
  have hoO : InRegions s.wr (out s₀ + 32 + BitVec.ofNat 64 j) 1 :=
    ⟨outR s₀, by simp [h.wr, hp.wr], by
      rw [BitVec.add_assoc, show (32 : Addr) + BitVec.ofNat 64 j = BitVec.ofNat 64 (32 + j) by
        rw [BitVec.ofNat_add]; rfl]
      exact contains_offset (by omega) (by omega)⟩
  unfold padBody
  refine wp_store8 (a := inn s₀ + 32 + BitVec.ofNat 64 j) (by rw [bufAt_ea _ _ j h.r14, h.rbx]) hoI
    fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  refine wp_store8 (a := out s₀ + 32 + BitVec.ofNat 64 j) (by rw [bufAt_ea _ _ j (by rw [g₁, h.r14]), g₁, h.r12])
    (by rw [wr₁]; exact hoO) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun s₃ u₃ => wp_cmpi fun s₄ g₄ m₄ rd₄ wr₄ _ z₄ => WP.block_nil ?_
  have k : ∀ r, r ≠ .r14 → s₄.gpr r = s.gpr r := fun r h1 => by rw [g₄, u₃.other r h1, g₂, g₁]
  have h14 : s₄.gpr .r14 = BitVec.ofNat 64 (j + 1) := by
    rw [g₄, u₃.gpr, g₂, g₁, h.r14, sx1, ofNat_succ]
  have hm : s₄.mem = (s.mem.writeW (inn s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j] ^^^ ipad)).writeW
      (out s₀ + 32 + BitVec.ofNat 64 j) ((K0 s₀)[j] ^^^ opad) := by
    rw [m₄, u₃.mem, m₂, m₁, g₁, h.rax, h.rcx, K0_ge hj hl]
    rfl
  refine ⟨⟨⟨by omega, by rw [rd₄, u₃.rd, rd₂, rd₁, h.rd], by rw [wr₄, u₃.wr, wr₂, wr₁, h.wr],
      by rw [k _ (by decide), h.rbx], by rw [k _ (by decide), h.r12], by rw [k _ (by decide), h.r15],
      by rw [k _ (by decide), h.rbp], by rw [k _ (by decide), h.r13], h14, by rw [k _ (by decide), h.rsp],
      by rw [hm]; exact buf_write hp h.mem hj'⟩, by rw [k _ (by decide), h.rax],
      by rw [k _ (by decide), h.rcx]⟩, ?_⟩
  rw [z₄, ← g₄, h14, sx64, sub_beq (by omega) (by omega)]

theorem key_loop_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Buf s₀ 0 s) (hk : 0 < kl s₀) :
    WP isa keyLoop s (Buf s₀ (kl s₀)) := by
  rw [keyLoop_eq]
  refine WP.loop (M := isa) (fun n s => ∃ j, n = kl s₀ - j ∧ j < kl s₀ ∧ Buf s₀ j s) ?_ (kl s₀) s
    ⟨0, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, hb⟩
  refine WP.mono (key_step hp hj hb) fun s' ⟨hb', hz⟩ => ?_
  by_cases hl : j + 1 = kl s₀
  · refine .inl ⟨by simp [eval, hz, hl], ?_⟩
    rwa [hl] at hb'
  · exact .inr ⟨by simp [eval, hz, hl], _, by omega, j + 1, rfl, by omega, hb'⟩

theorem pad_loop_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Pad s₀ (kl s₀) s) (hk : kl s₀ < 64) :
    WP isa padLoop s (Buf s₀ 64) := by
  rw [padLoop_eq]
  refine WP.loop (M := isa) (fun n s => ∃ j, n = 64 - j ∧ kl s₀ ≤ j ∧ j < 64 ∧ Pad s₀ j s) ?_ (64 - kl s₀) s
    ⟨kl s₀, rfl, (Nat.le_refl _), hk, h⟩
  rintro n s ⟨j, rfl, hj, hj', hb⟩
  refine WP.mono (pad_step hp hj hj' hb) fun s' ⟨hb', hz⟩ => ?_
  by_cases hl : j + 1 = 64
  · refine .inl ⟨by simp [eval, hz, hl], ?_⟩
    rw [hl] at hb'; exact hb'.toBuf
  · exact .inr ⟨by simp [eval, hz, hl], _, by omega, j + 1, rfl, by omega, by omega, hb'⟩

/-! ## The two compressions -/

/-- `Saved` survives a write outside the save area `scratch[112..160)`. -/
theorem saved_frame' {s₀ : State} {m m' : Mem} (h : Saved s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 112, 48⟩ r) : Saved s₀ m' := by
  intro p hp'
  rw [← h p hp']
  refine hf.readW (r := ⟨scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  refine (hd r hr).sub_left ?_
  simp only [Impl.Sha256.X86_64.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · intro a ha; simp only [Region.Contains, ofInt_natCast] at *; bv_omega

theorem blockAt_eq {m : Mem} {p : Addr} {xs : List Byte} (h : bytesAt m p 64 = xs) :
    Spec.Sha256.blockAt m p = Spec.Sha256.parseBlock fun k => xs.getD k 0 :=
  Proof.Sha256.Stream.parseBlock_congr fun _ hk =>
    Proof.Sha256.X86_64.Stream.bytesAt_getD h hk

/-- A state with `H⁽⁰⁾` and a full buffer `xs`, compressed, represents `xs`. -/
theorem repr_block {m m' : Mem} {p : Addr} {xs : List Byte} (hst : stateAt m p = H0)
    (hb : bytesAt m (p + 32) 64 = xs) (hx : xs.length = 64)
    (hs : stateAt m' p = Spec.Sha256.compress (stateAt m p) (Spec.Sha256.blockAt m (p + 32))) :
    Repr m' p xs := by
  have := repr_append_block (mem' := m') (xs := xs) (repr_nil hst) (by simp [hx])
    (by rw [hs, blockAt_eq hb]; simp)
  simpa using this

/-- The call of the compression function on the state at `p` (the inner or
the outer one) may be made. -/
theorem callOk {s₀ : State} (hp : Pre s₀) {p : Addr} (hpR : p = inn s₀ ∨ p = out s₀) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hbx : s.gpr .rbx = p) (h15 : s.gpr .r15 = scr s₀)
    (hsi : s.gpr .rsi = p + 32) (hsp : s.gpr .rsp = s₀.gpr .rsp) :
    CallOk s p (scr s₀) (p + 32) := by
  have hs : Region.Disjoint ⟨p, 96⟩ (scR s₀) ∧ Region.Disjoint (stkR s₀) ⟨p, 96⟩ ∧ ⟨p, 96⟩ ∈ s₀.wr := by
    rcases hpR with rfl | rfl
    · exact ⟨hp.i_s, hp.stk_i, by simp [hp.wr]⟩
    · exact ⟨hp.o_s, hp.stk_o, by simp [hp.wr]⟩
  obtain ⟨d, dr, hm⟩ := hs
  have e32 : Region.Sub ⟨p, 32⟩ ⟨p, 96⟩ := Region.sub_prefix (by omega)
  have eb : Region.Sub ⟨p + 32, 64⟩ ⟨p, 96⟩ := sub_offset (off := 32) (by omega) (by omega)
  have e112 : Region.Sub ⟨scr s₀, 112⟩ (scR s₀) := Region.sub_prefix (by omega)
  refine ⟨hbx, h15, hsi, (d.sub_left e32).sub_right e112, ?_,
    (d.sub_left eb).sub_right e112, by rw [hsp]; exact dr.sub_right e32,
    by rw [hsp]; exact hp.stk_s.sub_right e112, by rw [hsp]; exact dr.sub_right eb, ?_, ?_⟩
  · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
  · rw [hrd, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨p, 96⟩, by simp [hm], 32, rfl, by simp⟩
    · exact ⟨⟨p, 96⟩, by simp [hm], 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp [hp.wr], 0, by simp, by simp⟩
  · rw [hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨p, 96⟩, hm, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp [hp.wr], 0, by simp, by simp⟩

/-- The compression of the block in the buffer of the state at `p`
(the inner or the outer one), by the compression function `f`. -/
theorem compress_ok {f : Callee} (hf : f.Ok) {s₀ : State} (hp : Pre s₀) {p : Addr}
    (hpR : p = inn s₀ ∨ p = out s₀) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hbx : s.gpr .rbx = p) (h15 : s.gpr .r15 = scr s₀)
    (hsi : s.gpr .rsi = p + 32) (hsp : s.gpr .rsp = s₀.gpr .rsp) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨p, 32⟩, ⟨scr s₀, 112⟩, stkR s₀] s.mem s'.mem →
      stateAt s'.mem p = Spec.Sha256.compress (stateAt s.mem p) (Spec.Sha256.blockAt s.mem (p + 32)) →
      Q s') :
    WP isa (compressAt f) s Q :=
  compressAt_ok hf (callOk hp hpR hrd hwr hbx h15 hsi hsp)
    fun s' hrd' hwr' hcs hfr hst _ _ => hQ s' hrd' hwr' hcs (by rw [hsp] at hfr; exact hfr) hst

/-- A state that a write outside it keeps. -/
theorem state_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 96⟩ r) :
    stateAt m' p = stateAt m p ∧ bytesAt m' (p + 32) 64 = bytesAt m (p + 32) 64 := by
  refine ⟨Proof.Sha256.Stream.stateAt_congr fun i hi =>
      hf.bytes (R := ⟨p, 32⟩) (fun r hr => (hd r hr).sub_left (sub32 p)) (by simp) hi,
    Proof.Sha256.Stream.bytesAt_congr fun i hi =>
      hf.bytes (R := ⟨p + 32, 64⟩) (fun r hr => (hd r hr).sub_left (sub_offset (off := 32) (by omega) (by omega)))
        (by simp) hi⟩

theorem save_sub (s₀ : State) : Region.Sub ⟨scr s₀ + BitVec.ofNat 64 112, 48⟩ (scR s₀) :=
  sub_offset (by omega) (by omega)

set_option simprocs false in
theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hwr : s.wr = s₀.wr)
    (h15 : s.gpr .r15 = scr s₀) (hsp : s.gpr .rsp = s₀.gpr .rsp) (hsv : Saved s₀ s.mem)
    (hfr : Frame [inR s₀, outR s₀, scR s₀, stkR s₀] s₀.mem s.mem)
    (hI : Repr s.mem (inn s₀) (xorPad (K0 s₀) ipad)) (hO : Repr s.mem (out s₀) (xorPad (K0 s₀) opad)) :
    WP isa (.block restore) s fun s' => gprPreserved s₀ s' ∧ Proof.Hmac.initSha256X86_64.post s₀ s' := by
  have i : ∀ d : Nat, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨scR s₀, by simp [hwr, hp.wr], contains_offset' hd (by omega)⟩
  have i0 := i 112 (by omega); have i1 := i 120 (by omega); have i2 := i 128 (by omega)
  have i3 := i 136 (by omega); have i4 := i 144 (by omega); have i5 := i 152 (by omega)
  have g0 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((112 : Nat) : Int)) 64 = s₀.gpr .rbx :=
    hsv (.rbx, 112) (by simp [Impl.Sha256.X86_64.Stream.saved])
  have g1 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((120 : Nat) : Int)) 64 = s₀.gpr .rbp :=
    hsv (.rbp, 120) (by simp [Impl.Sha256.X86_64.Stream.saved])
  have g2 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((128 : Nat) : Int)) 64 = s₀.gpr .r12 :=
    hsv (.r12, 128) (by simp [Impl.Sha256.X86_64.Stream.saved])
  have g3 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((136 : Nat) : Int)) 64 = s₀.gpr .r13 :=
    hsv (.r13, 136) (by simp [Impl.Sha256.X86_64.Stream.saved])
  have g4 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((144 : Nat) : Int)) 64 = s₀.gpr .r14 :=
    hsv (.r14, 144) (by simp [Impl.Sha256.X86_64.Stream.saved])
  have g5 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((152 : Nat) : Int)) 64 = s₀.gpr .r15 :=
    hsv (.r15, 152) (by simp [Impl.Sha256.X86_64.Stream.saved])
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hfr.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_i, hp.ret_o, hp.ret_s, ret_stk s₀⟩)
      (by decide)
  apply WP.of_runBlock
  rw [Proof.Sha256.X86_64.Stream.restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at, State.load64,
    State.setReg, h15, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, hret⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hsp]
  · simp only [Proof.Hmac.initSha256X86_64]
    rw [blockKey_eq hp]
    exact ⟨hI, hO⟩

/-! ## Correctness -/

theorem sx32 : BitVec.signExtend 64 (32 : BitVec 32) = (32 : BitVec 64) := by decide

theorem buf_full {s₀ : State} (hp : Pre s₀) {m : Mem} (h : BufMem s₀ 64 m) :
    bytesAt m (inn s₀ + 32) 64 = xorPad (K0 s₀) ipad ∧ bytesAt m (out s₀ + 32) 64 = xorPad (K0 s₀) opad := by
  rw [h.bufI, h.bufO, List.take_of_length_le (by rw [K0_length s₀ hp])]
  exact ⟨rfl, rfl⟩

/-- After `initKeys`: both buffers hold their key blocks, and `rsi` points
at the inner one. -/
def Keyed (s₀ s : State) : Prop := Buf s₀ 64 s ∧ s.gpr .rsi = inn s₀ + 32

theorem keys_ok {s₀ : State} (hp : Pre s₀) : WP isa initKeys s₀ (Keyed s₀) := by
  have hkl := hp.kl_le
  unfold initKeys
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, z₁⟩ => ?_)
  -- The key.
  refine WP.seq (WP.mono (Q := Buf s₀ (kl s₀)) ?_ fun s₂ h₂ => ?_)
  · refine WP.ite (decide (kl s₀ = 0)) (by simp [eval, z₁]) (fun hb => WP.block_nil ?_)
      (fun hb => key_loop_ok hp h₁ ?_)
    · simp only [decide_eq_true_eq] at hb; rw [hb]; exact h₁
    · simp only [decide_eq_false_iff_not] at hb; omega
  -- The padding.
  refine WP.seq (wp_mov32i fun s₃ u₃ _ _ => wp_mov32i fun s₄ u₄ _ _ =>
    wp_cmpi fun s₅ g₅ m₅ rd₅ wr₅ _ z₅ => WP.block_nil ?_)
  have k₅ : ∀ r, r ≠ .rax → r ≠ .rcx → s₅.gpr r = s₂.gpr r := fun r h h' => by
    rw [g₅, u₄.other r h', u₃.other r h]
  have hP : Pad s₀ (kl s₀) s₅ :=
    ⟨⟨h₂.j_le, by rw [rd₅, u₄.rd, u₃.rd, h₂.rd], by rw [wr₅, u₄.wr, u₃.wr, h₂.wr],
      by rw [k₅ _ (by decide) (by decide), h₂.rbx], by rw [k₅ _ (by decide) (by decide), h₂.r12],
      by rw [k₅ _ (by decide) (by decide), h₂.r15], by rw [k₅ _ (by decide) (by decide), h₂.rbp],
      by rw [k₅ _ (by decide) (by decide), h₂.r13], by rw [k₅ _ (by decide) (by decide), h₂.r14],
      by rw [k₅ _ (by decide) (by decide), h₂.rsp], by rw [m₅, u₄.mem, u₃.mem]; exact h₂.mem⟩,
      by rw [g₅, u₄.other _ (by decide), u₃.gpr], by rw [g₅, u₄.gpr]⟩
  have hz : s₅.zf = some (decide (kl s₀ = 64)) := by
    rw [z₅, ← g₅, hP.r14, sx64, sub_beq (by omega) (by omega)]
  refine WP.seq (WP.mono (Q := Buf s₀ 64) ?_ fun s₆ h₆ => ?_)
  · refine WP.ite (decide (kl s₀ = 64)) (by simp [eval, hz]) (fun hb => WP.block_nil ?_)
      (fun hb => pad_loop_ok hp hP ?_)
    · simp only [decide_eq_true_eq] at hb; rw [← hb]; exact hP.toBuf
    · simp only [decide_eq_false_iff_not] at hb; omega
  refine wp_mov fun s₇ u₇ _ _ => wp_addi fun s₈ u₈ => WP.block_nil ⟨?_, ?_⟩
  · have k₈ : ∀ r, r ≠ .rsi → s₈.gpr r = s₆.gpr r := fun r h => by rw [u₈.other r h, u₇.other r h]
    exact ⟨h₆.j_le, by rw [u₈.rd, u₇.rd, h₆.rd], by rw [u₈.wr, u₇.wr, h₆.wr],
      by rw [k₈ _ (by decide), h₆.rbx], by rw [k₈ _ (by decide), h₆.r12], by rw [k₈ _ (by decide), h₆.r15],
      by rw [k₈ _ (by decide), h₆.rbp], by rw [k₈ _ (by decide), h₆.r13], by rw [k₈ _ (by decide), h₆.r14],
      by rw [k₈ _ (by decide), h₆.rsp], by rw [u₈.mem, u₇.mem]; exact h₆.mem⟩
  · rw [u₈.gpr, u₇.gpr, h₆.rbx, sx32]

theorem correct {f : Callee} (hf : f.Ok) {s₀ : State} (hp : Pre s₀) :
    WP isa (init f) s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Hmac.initSha256X86_64.post s₀ s' := by
  unfold init
  refine WP.seq (WP.mono (keys_ok hp) fun s₈ ⟨h₈, si₈⟩ => ?_)
  obtain ⟨bI, bO⟩ := buf_full hp h₈.mem
  -- The inner block.
  refine WP.seq (compress_ok hf hp (.inl rfl) h₈.rd h₈.wr h₈.rbx h₈.r15 si₈ h₈.rsp
    fun s₉ rd₉ wr₉ cs₉ fr₉ st₉ => ?_)
  have hI₉ : Repr s₉.mem (inn s₀) (xorPad (K0 s₀) ipad) :=
    repr_block h₈.mem.stI bI (by simp [xorPad, K0_length s₀ hp]) st₉
  have dO : ∀ r ∈ [(⟨inn s₀, 32⟩ : Region), ⟨scr s₀, 112⟩, stkR s₀], Region.Disjoint ⟨out s₀, 96⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o.symm.sub_right (sub32 _)
    · exact hp.o_s.sub_right (Region.sub_prefix (by omega))
    · exact hp.stk_o.symm
  obtain ⟨sO₉, bO₉⟩ := state_frame fr₉ dO
  have sv₉ : Saved s₀ s₉.mem := by
    refine saved_frame' h₈.mem.saved fr₉ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact (hp.i_s.symm.sub_left (save_sub s₀)).sub_right (sub32 _)
    · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
    · exact hp.stk_s.symm.sub_left (save_sub s₀)
  have f₉ : Frame [inR s₀, outR s₀, scR s₀, stkR s₀] s₀.mem s₉.mem := by
    refine Frame.trans (Frame.mono h₈.mem.frame (by simp)) (fr₉.sub ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact ⟨inR s₀, by simp, sub32 _⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  -- The outer block.
  refine WP.seq (wp_mov fun s₁₀ u₁₀ _ _ => wp_mov fun s₁₁ u₁₁ _ _ => wp_addi fun s₁₂ u₁₂ => WP.block_nil ?_)
  have k₁₂ : ∀ r, r ≠ .rsi → r ≠ .rbx → s₁₂.gpr r = s₉.gpr r := fun r h h' => by
    rw [u₁₂.other r h, u₁₁.other r h, u₁₀.other r h']
  have m₁₂ : s₁₂.mem = s₉.mem := by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem]
  have r12₉ : s₉.gpr .r12 = out s₀ := by rw [cs₉ _ (by decide), h₈.r12]
  have r15₉ : s₉.gpr .r15 = scr s₀ := by rw [cs₉ _ (by decide), h₈.r15]
  have rsp₉ : s₉.gpr .rsp = s₀.gpr .rsp := by rw [cs₉ _ (by decide), h₈.rsp]
  refine WP.seq (compress_ok hf hp (.inr rfl) (by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, rd₉, h₈.rd])
    (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, wr₉, h₈.wr])
    (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, r12₉])
    (by rw [k₁₂ _ (by decide) (by decide), r15₉])
    (by rw [u₁₂.gpr, u₁₁.gpr, u₁₀.other _ (by decide), r12₉, sx32])
    (by rw [k₁₂ _ (by decide) (by decide), rsp₉])
    fun s₁₃ rd₁₃ wr₁₃ cs₁₃ fr₁₃ st₁₃ => ?_)
  have hO : Repr s₁₃.mem (out s₀) (xorPad (K0 s₀) opad) :=
    repr_block (by rw [m₁₂, sO₉]; exact h₈.mem.stO) (by rw [m₁₂, bO₉]; exact bO)
      (by simp [xorPad, K0_length s₀ hp]) st₁₃
  have hI : Repr s₁₃.mem (inn s₀) (xorPad (K0 s₀) ipad) := by
    refine repr_congr (fun i hi => fr₁₃.bytes (R := inR s₀) ?_ (by simp) hi) (m₁₂ ▸ hI₉)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o.sub_right (sub32 _)
    · exact hp.i_s.sub_right (Region.sub_prefix (by omega))
    · exact hp.stk_i.symm
  refine epilogue_ok hp (by rw [wr₁₃, u₁₂.wr, u₁₁.wr, u₁₀.wr, wr₉, h₈.wr])
    (by rw [cs₁₃ _ (by decide), k₁₂ _ (by decide) (by decide), r15₉])
    (by rw [cs₁₃ _ (by decide), k₁₂ _ (by decide) (by decide), rsp₉]) ?_ ?_ hI hO
  · refine saved_frame' (by rw [m₁₂]; exact sv₉) fr₁₃ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact (hp.o_s.symm.sub_left (save_sub s₀)).sub_right (sub32 _)
    · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
    · exact hp.stk_s.symm.sub_left (save_sub s₀)
  · refine (m₁₂ ▸ f₉).trans (fr₁₃.sub ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact ⟨outR s₀, by simp, sub32 _⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-! ## Constant time

This holds for any compression function `f` (`Callee.Ok`), so it is proven
once for every implementation, by relating two runs (`RelCT`), as for the
streaming SHA-256 functions: correctness determines the registers each piece
between the calls uses from the public arguments alone, the taint analysis
proves each such piece constant time, and the calls are constant time by
`compressAt_rel`. -/

/-- The registers that hold public values across the calls. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r12 : s.gpr .r12 = out s₀
  r15 : s.gpr .r15 = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp

/-- Before the compression of the state at `p`. -/
def At (s₀ : State) (p : Addr) (s : State) : Prop := KR s₀ s ∧ s.gpr .rbx = p ∧ s.gpr .rsi = p + 32

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

theorem keyed_at {s₀ s : State} (h : Keyed s₀ s) : At s₀ (inn s₀) s :=
  ⟨⟨h.1.rd, h.1.wr, h.1.r12, h.1.r15, h.1.rsp⟩, h.1.rbx, h.2⟩

theorem cmp_kr {f : Callee} (hf : f.Ok) {s₀ : State} (hp : Pre s₀) {p : Addr} (hpR : p = inn s₀ ∨ p = out s₀)
    {s : State} (h : At s₀ p s) : WP isa (compressAt f) s (KR s₀) :=
  compress_ok hf hp hpR h.1.rd h.1.wr h.2.1 h.1.r15 h.2.2 h.1.rsp fun _ rd wr cs _ _ =>
    ⟨rd.trans h.1.rd, wr.trans h.1.wr, (cs _ (by decide)).trans h.1.r12, (cs _ (by decide)).trans h.1.r15,
      (cs _ (by decide)).trans h.1.rsp⟩

/-- Setting up the outer compression. -/
theorem mid_ok {s₀ s : State} (h : KR s₀ s) :
    WP isa (.block [.mov .rbx (.reg .r12), .mov .rsi (.reg .r12), .alu .add .rsi (.imm 32)]) s
      (At s₀ (out s₀)) :=
  wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_addi fun s₃ u₃ => WP.block_nil
    ⟨⟨by rw [u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₃.wr, u₂.wr, u₁.wr, h.wr],
      by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r12],
      by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r15],
      by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.rsp]⟩,
      by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.r12],
      by rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide), h.r12, sx32]⟩

section
variable {f : Callee} (hf : f.Ok) {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀')
  (hq : PubEq s₀ s₀')
include hf hp hp' hq

/-- The compression of the state at `p`, the same in both runs. -/
theorem cmp_rel {p : Addr} (hpR : p = inn s₀ ∨ p = out s₀) :
    RelCT isa (fun s s' => At s₀ p s ∧ At s₀' p s') (compressAt f) fun s s' => KR s₀ s ∧ KR s₀' s' := by
  have hpR' : p = inn s₀' ∨ p = out s₀' := by
    show p = s₀'.gpr .rdi ∨ p = s₀'.gpr .rsi; rw [← hq.rdi, ← hq.rsi]; exact hpR
  exact ((compressAt_rel hf fun s s' ⟨⟨k, bx, si⟩, ⟨k', bx', si'⟩⟩ =>
      ⟨⟨_, _, _, callOk hp hpR k.rd k.wr bx k.r15 si k.rsp⟩,
        ⟨_, _, _, callOk hp' hpR' k'.rd k'.wr bx' k'.r15 si' k'.rsp⟩,
        by rw [bx, bx'], by rw [k.r15, k'.r15]; exact hq.r8, by rw [si, si'],
        by rw [k.rsp, k'.rsp]; exact hq.rsp⟩).wp
    fun _ _ h => ⟨cmp_kr hf hp hpR h.1, cmp_kr hf hp' hpR' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem init_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (init f) fun _ _ => True := by
  have keys : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') initKeys
      fun s s' => At s₀ (inn s₀) s ∧ At s₀' (inn s₀) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) (c := initKeys) (by taint_decide)).wp
      fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact ⟨keys_ok hp, keys_ok hp'⟩).mono (fun _ _ h => h)
      fun _ _ h => ⟨keyed_at h.2.1, by rw [show inn s₀ = inn s₀' from hq.rdi]; exact keyed_at h.2.2⟩
  have agree : ∀ s s', KR s₀ s → KR s₀' s' → ∀ r ∈ [Reg.r12, .r15, .rsp], s.gpr r = s'.gpr r := by
    intro s s' h h' r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.r12, h'.r12]; exact hq.rsi
    · rw [h.r15, h'.r15]; exact hq.r8
    · rw [h.rsp, h'.rsp]; exact hq.rsp
  have mid : RelCT isa (fun s s' => KR s₀ s ∧ KR s₀' s')
      (.block [.mov .rbx (.reg .r12), .mov .rsi (.reg .r12), .alu .add .rsi (.imm 32)])
      fun s s' => At s₀ (out s₀) s ∧ At s₀' (out s₀) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.r12, .r15, .rsp])
      (fun _ _ h => Taint.agree_ofRegs (agree _ _ h.1 h.2)) (by taint_decide)).wp
      fun _ _ h => ⟨mid_ok h.1, mid_ok h.2⟩).mono (fun _ _ h => h)
      fun _ _ h => ⟨h.2.1, by rw [show out s₀ = out s₀' from hq.rsi]; exact h.2.2⟩
  have epi : RelCT isa (fun s s' => KR s₀ s ∧ KR s₀' s') (.block restore) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r12, .r15, .rsp])
      (fun _ _ h => Taint.agree_ofRegs (agree _ _ h.1 h.2)) (by taint_decide)
  exact keys.seq ((cmp_rel hf hp hp' hq (.inl rfl)).seq (mid.seq ((cmp_rel hf hp hp' hq (.inr rfl)).seq epi)))

end

/-- A state satisfying the precondition (with an empty key). -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .r8 => 0x4000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x2000, 96⟩, ⟨0x4000, 160⟩]

theorem verified_of {f : Callee} (hf : f.Ok) (hm : (init f).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (init f) Proof.Hmac.initSha256X86_64 := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct hf (pre_of hs)
    exact ⟨t, s', he, abiPreserved_of_exec hm he h.1, h.2⟩
  · obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
    exact (init_rel hf (pre_of h₁) (pre_of h₂) ⟨p1, p2, p3, p4, p5, p6⟩ _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨sat, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, sat] at h₁ h₂
      bv_omega

end VG.Proof.Hmac.X86_64.Init
