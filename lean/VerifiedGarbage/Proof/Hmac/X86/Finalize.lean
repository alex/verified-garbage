import VerifiedGarbage.Proof.Hmac.X86.Common
import VerifiedGarbage.Spec.Hmac.X86

/-!
# HMAC-SHA-256 on x86 (32-bit): `finalize`

Untrusted: everything here is checked by Lean. The inner hash is the code of
`vg_sha256_finalize` up to writing the digest (`finalizeHash`), run on our
state with its permissions narrowed to those of `vg_sha256_finalize` and
reasoned about with that function's own proof (`WP.narrow`); the outer hash
is one inlined compression of a block laid out at known offsets.
-/

namespace VG.Proof.Hmac.X86.Finalize

open VG VG.X86 VG.Impl.Hmac.X86
open VG.Impl.Sha256.X86 (at_)
open VG.Impl.Sha256.X86.Stream (compressAt restore saved)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame repr_congr compressList_append hash_one lenBytes rest)
open VG.Proof.Hmac.X86
open VG.Spec.Sha256 (HashValue stateAt blockAt compress parseBlock bytesAt wordBytes countX86 Repr)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey sha256 countFinalizeX86)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev inn : BitVec 32 := arg s₀ 0
abbrev ou : BitVec 32 := arg s₀ 1
abbrev out : BitVec 32 := arg s₀ 4
abbrev scr : BitVec 32 := arg s₀ 5
abbrev inA : Addr := (inn s₀).setWidth 64
abbrev ouA : Addr := (ou s₀).setWidth 64
abbrev outA : Addr := (out s₀).setWidth 64
abbrev scA : Addr := (scr s₀).setWidth 64
abbrev inR : Region := ⟨inA s₀, 96⟩
abbrev ouR : Region := ⟨ouA s₀, 96⟩
abbrev outR : Region := ⟨outA s₀, 32⟩
abbrev scR : Region := ⟨scA s₀, 240⟩
abbrev argR : Region := ⟨addr (esp₀ s₀) 4, 24⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩

/-- The regions `vg_sha256_finalize` gets: its state (our inner state), its
output (ours), the first 160 bytes of our scratch space, and the first 20
bytes of our arguments. -/
abbrev finW : List Region := [inR s₀, outR s₀, ⟨scA s₀, 160⟩, ⟨addr (esp₀ s₀) 4, 20⟩]

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [ouR s₀]
  wr : s₀.wr = [inR s₀, outR s₀, scR s₀, argR s₀]
  in_out : (inR s₀).Disjoint (outR s₀)
  in_scr : (inR s₀).Disjoint (scR s₀)
  out_scr : (outR s₀).Disjoint (scR s₀)
  a_in : (argR s₀).Disjoint (inR s₀)
  a_out : (argR s₀).Disjoint (outR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  o_in : (ouR s₀).Disjoint (inR s₀)
  o_out : (ouR s₀).Disjoint (outR s₀)
  o_scr : (ouR s₀).Disjoint (scR s₀)
  o_a : (ouR s₀).Disjoint (argR s₀)
  ret_in : (retR s₀).Disjoint (inR s₀)
  ret_out : (retR s₀).Disjoint (outR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  in_fit : (inn s₀).toNat + 96 ≤ 2 ^ 32
  ou_fit : (ou s₀).toNat + 96 ≤ 2 ^ 32
  out_fit : (out s₀).toNat + 32 ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 240 ≤ 2 ^ 32
  sp_fit : (esp₀ s₀).toNat + 28 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : Spec.Hmac.finalizeSha256X86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem scr_in {d n : Nat} (hd : d + n ≤ 240) (hn : 0 < n) : (scR s₀).Contains (addr (scr s₀) d) n :=
  contains_addr hd hn hp.scr_fit

theorem in_in {d n : Nat} (hd : d + n ≤ 96) (hn : 0 < n) : (inR s₀).Contains (addr (inn s₀) d) n :=
  contains_addr hd hn hp.in_fit

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  simp only [Region.Contains]
  rw [addr_eq (by omega), addr_eq (by omega),
    show (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d - ((esp₀ s₀).setWidth 64 + BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (d - 4) by
      rw [show d = (d - 4) + 4 by omega, BitVec.ofNat_add]; bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A word of the scratch space, as a region. -/
theorem scr_sub {d : Nat} (hd : d + 4 ≤ 240) : Region.Sub ⟨addr (scr s₀) d, 4⟩ (scR s₀) := by
  rw [addr_eq (by have := hp.scr_fit; omega)]
  exact sub_offset hd (by omega)

/-- An argument word, as a region. -/
theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  intro a ha
  simp only [Region.Contains] at ha ⊢
  rw [addr_eq (by omega)] at ha
  rw [addr_eq (by omega)]
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem arg_scr_sep {d e : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) (he : e + 4 ≤ 240) :
    Mem.Sep (addr (esp₀ s₀) d) 4 (addr (scr s₀) e) 4 := by
  intro x hx hy
  exact hp.a_scr x (hp.arg_sub hd₁ hd x (by simp only [Region.Contains]; omega))
    (hp.scr_sub he x (by simp only [Region.Contains]; omega))

theorem scr_arg_sep {d e : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) (he : e + 4 ≤ 240) :
    Mem.Sep (addr (scr s₀) e) 4 (addr (esp₀ s₀) d) 4 := by
  intro x hx hy
  exact hp.a_scr x (hp.arg_sub hd₁ hd x (by simp only [Region.Contains]; omega))
    (hp.scr_sub he x (by simp only [Region.Contains]; omega))

end Pre

theorem ret_a {s₀ : State} (hp : Pre s₀) : (retR s₀).Disjoint (argR s₀) := by
  have := hp.sp_fit
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [addr_eq (by omega)] at h₂
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

/-! ## Rearranging the arguments -/

/-- Memory after the prologue: `outer` in `scratch[176]`, and the arguments
of `vg_sha256_finalize`. -/
def proMem (s₀ : State) : Mem :=
  ((((s₀.mem.writeW (addr (scr s₀) 176) (ou s₀)).writeW (addr (esp₀ s₀) 8) (arg s₀ 2)).writeW
    (addr (esp₀ s₀) 12) (arg s₀ 3)).writeW (addr (esp₀ s₀) 16) (out s₀)).writeW (addr (esp₀ s₀) 20) (scr s₀)

theorem proMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scR s₀, argR s₀] s₀.mem (proMem s₀) := by
  simp only [proMem]
  exact (((((Frame.refl _ _).writeW (by simp) _ (hp.scr_in (d := 176) (by omega) (by omega))).writeW (by simp) _
    (hp.arg_in (d := 8) (by omega) (by omega))).writeW (by simp) _ (hp.arg_in (d := 12) (by omega) (by omega))).writeW
    (by simp) _ (hp.arg_in (d := 16) (by omega) (by omega))).writeW (by simp) _
    (hp.arg_in (d := 20) (by omega) (by omega))

/-- Reading an argument word after the prologue. -/
theorem proMem_arg {s₀ : State} (hp : Pre s₀) (i : Nat) (hi : i < 5) :
    (proMem s₀).readW (addr (esp₀ s₀) (4 + 4 * i)) 32 =
      [inn s₀, arg s₀ 2, arg s₀ 3, out s₀, scr s₀].getD i 0 := by
  have := hp.sp_fit
  have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), 4 ≤ d → d + 4 ≤ 28 → 4 ≤ e → e + 4 ≤ 28 →
      d + 4 ≤ e ∨ e + 4 ≤ d →
      (m.writeW (addr (esp₀ s₀) e) v).readW (addr (esp₀ s₀) d) 32 = m.readW (addr (esp₀ s₀) d) 32 :=
    fun m v d e _ h₂ _ h₄ h => readW_writeW_addr m v (by omega) (by omega) h
  have s176 : ∀ d, 4 ≤ d → d + 4 ≤ 28 →
      (s₀.mem.writeW (addr (scr s₀) 176) (ou s₀)).readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 :=
    fun d h₁ h₂ => Mem.readW_writeW_sep (hp.arg_scr_sep h₁ h₂ (by omega)) (by decide)
  interval_cases i <;> simp only [proMem, List.getD_cons_zero, List.getD_cons_succ]
  · rw [w _ _ 4 20 (by omega) (by omega) (by omega) (by omega) (by omega),
      w _ _ 4 16 (by omega) (by omega) (by omega) (by omega) (by omega),
      w _ _ 4 12 (by omega) (by omega) (by omega) (by omega) (by omega),
      w _ _ 4 8 (by omega) (by omega) (by omega) (by omega) (by omega), s176 4 (by omega) (by omega)]; rfl
  · rw [w _ _ 8 20 (by omega) (by omega) (by omega) (by omega) (by omega),
      w _ _ 8 16 (by omega) (by omega) (by omega) (by omega) (by omega),
      w _ _ 8 12 (by omega) (by omega) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [w _ _ 12 20 (by omega) (by omega) (by omega) (by omega) (by omega),
      w _ _ 12 16 (by omega) (by omega) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [w _ _ 16 20 (by omega) (by omega) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

theorem proMem_176 {s₀ : State} (hp : Pre s₀) : (proMem s₀).readW (addr (scr s₀) 176) 32 = ou s₀ := by
  simp only [proMem]
  rw [Mem.readW_writeW_sep (hp.scr_arg_sep (d := 20) (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (hp.scr_arg_sep (d := 16) (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (hp.scr_arg_sep (d := 12) (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (hp.scr_arg_sep (d := 8) (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self32]

/-- After the prologue. -/
structure Pro (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  gpr : ∀ r, r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  mem : s.mem = proMem s₀

set_option maxHeartbeats 4000000 in
theorem pro_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block [.mov .edx (.mem (at_ .esp 24)), .mov .ecx (.mem (at_ .esp 8)), .store (at_ .edx 176) .ecx,
      .mov .ecx (.mem (at_ .esp 12)), .store (at_ .esp 8) .ecx,
      .mov .ecx (.mem (at_ .esp 16)), .store (at_ .esp 12) .ecx,
      .mov .ecx (.mem (at_ .esp 20)), .store (at_ .esp 16) .ecx, .store (at_ .esp 20) .edx]) s₀ (Pro s₀) := by
  have hsp := hp.sp_fit
  have rin : ∀ (s : State), s.rd = s₀.rd → s.wr = s₀.wr → ∀ d, 4 ≤ d → d + 4 ≤ 28 →
      InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
    fun s h₁ h₂ d h₃ h₄ => ⟨argR s₀, by simp [h₁, h₂, hp.wr], hp.arg_in h₃ h₄⟩
  have win : ∀ (s : State), s.wr = s₀.wr → ∀ d, 4 ≤ d → d + 4 ≤ 28 → InRegions s.wr (addr (esp₀ s₀) d) 4 :=
    fun s h₂ d h₃ h₄ => ⟨argR s₀, by simp [h₂, hp.wr], hp.arg_in h₃ h₄⟩
  refine wp_movm (a := addr (esp₀ s₀) 24) (ea_at _ _ _) (rin _ rfl rfl 24 (by omega) (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .edx = scr s₀ := u₁.gpr
  have sp₁ : s₁.gpr .esp = esp₀ s₀ := u₁.other _ (by decide)
  refine wp_movm (a := addr (esp₀ s₀) 8) (by rw [ea_at, sp₁]) (by rw [u₁.rd, u₁.wr]; exact rin _ rfl rfl 8 (by omega) (by omega))
    fun s₂ u₂ => ?_
  refine wp_store (a := addr (scr s₀) 176) (by rw [ea_at, u₂.other _ (by decide), e₁])
    (by rw [u₂.wr, u₁.wr]; exact ⟨scR s₀, by simp [hp.wr], hp.scr_in (by omega) (by omega)⟩) fun s₃ u₃ => ?_
  have ld : ∀ d, 4 ≤ d → d + 4 ≤ 28 →
      (s₀.mem.writeW (addr (scr s₀) 176) (ou s₀)).readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 :=
    fun d h₁ h₂ => Mem.readW_writeW_sep (hp.arg_scr_sep h₁ h₂ (by omega)) (by decide)
  have m₃ : s₃.mem = s₀.mem.writeW (addr (scr s₀) 176) (ou s₀) := by
    rw [u₃.mem, u₂.gpr, u₂.mem, u₁.mem]; rfl
  have g₃ : ∀ r, r ≠ .ecx → r ≠ .edx → s₃.gpr r = s₀.gpr r := fun r h h' => by
    rw [u₃.gpr, u₂.other r h, u₁.other r h']
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have sp₃ : s₃.gpr .esp = esp₀ s₀ := g₃ _ (by decide) (by decide)
  have ed₃ : s₃.gpr .edx = scr s₀ := by rw [u₃.gpr, u₂.other _ (by decide), e₁]
  refine wp_movm (a := addr (esp₀ s₀) 12) (by rw [ea_at, sp₃]) (rin _ rd₃ wr₃ 12 (by omega) (by omega))
    fun s₄ u₄ => ?_
  refine wp_store (a := addr (esp₀ s₀) 8) (by rw [ea_at, u₄.other _ (by decide), sp₃])
    (by rw [u₄.wr]; exact win _ wr₃ 8 (by omega) (by omega)) fun s₅ u₅ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 16) (by rw [ea_at, u₅.gpr, u₄.other _ (by decide), sp₃])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact rin _ rd₃ wr₃ 16 (by omega) (by omega)) fun s₆ u₆ => ?_
  refine wp_store (a := addr (esp₀ s₀) 12) (by rw [ea_at, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), sp₃])
    (by rw [u₆.wr, u₅.wr, u₄.wr]; exact win _ wr₃ 12 (by omega) (by omega)) fun s₇ u₇ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 20)
    (by rw [ea_at, u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), sp₃])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact rin _ rd₃ wr₃ 20 (by omega) (by omega))
    fun s₈ u₈ => ?_
  have g₈ : ∀ r, r ≠ .ecx → s₈.gpr r = s₃.gpr r := fun r h => by
    rw [u₈.other r h, u₇.gpr, u₆.other r h, u₅.gpr, u₄.other r h]
  refine wp_store (a := addr (esp₀ s₀) 16) (by rw [ea_at, g₈ _ (by decide), sp₃])
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr]; exact win _ wr₃ 16 (by omega) (by omega)) fun s₉ u₉ => ?_
  refine wp_store (a := addr (esp₀ s₀) 20) (by rw [ea_at, u₉.gpr, g₈ _ (by decide), sp₃])
    (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr]; exact win _ wr₃ 20 (by omega) (by omega))
    fun s₁₀ u₁₀ => WP.block_nil ⟨?_, ?_, fun r h h' => ?_, ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃]
  · rw [u₁₀.gpr, u₉.gpr, g₈ r h, g₃ r h h']
  · -- The values read are the original arguments, unchanged by the earlier stores.
    have a : ∀ d, 4 ≤ d → d + 4 ≤ 28 → s₃.mem.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 :=
      fun d h₁ h₂ => by rw [m₃, ld d h₁ h₂]
    have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ 28 → e + 4 ≤ 28 → d + 4 ≤ e ∨ e + 4 ≤ d →
        (m.writeW (addr (esp₀ s₀) e) v).readW (addr (esp₀ s₀) d) 32 = m.readW (addr (esp₀ s₀) d) 32 :=
      fun m v d e h₂ h₄ h => readW_writeW_addr m v (by omega) (by omega) h
    have m₅ : s₅.mem = s₃.mem.writeW (addr (esp₀ s₀) 8) (arg s₀ 2) := by
      rw [u₅.mem, u₄.gpr, u₄.mem, a 12 (by omega) (by omega)]; rfl
    have m₇ : s₇.mem = (s₃.mem.writeW (addr (esp₀ s₀) 8) (arg s₀ 2)).writeW (addr (esp₀ s₀) 12) (arg s₀ 3) := by
      rw [u₇.mem, u₆.gpr, u₆.mem, m₅, w _ _ 16 8 (by omega) (by omega) (by omega), a 16 (by omega) (by omega)]; rfl
    have m₉ : s₉.mem = s₇.mem.writeW (addr (esp₀ s₀) 16) (out s₀) := by
      rw [u₉.mem, u₈.gpr, u₈.mem, m₇, w _ _ 20 12 (by omega) (by omega) (by omega),
        w _ _ 20 8 (by omega) (by omega) (by omega), a 20 (by omega) (by omega)]; rfl
    rw [u₁₀.mem, m₉, m₇, u₉.gpr, g₈ _ (by decide), ed₃, m₃]; rfl

/-! ## The inner hash -/

abbrev SPre := VG.Proof.Sha256.X86.Stream.Finalize.Pre
abbrev SDone := VG.Proof.Sha256.X86.Stream.Finalize.Done

theorem finalizeHash_eq : finalizeHash = .seq (.block ([.mov .eax (.mem (at_ .esp 20))] ++
      VG.Impl.Sha256.X86.Stream.save .eax ++
      [.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
       .mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp 128) .ecx,
       .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp 132) .ecx,
       .mov .ecx (.mem (at_ .esp 16)), .store (at_ .ebp 136) .ecx,
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm 63),
       .mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .mov .ecx (.imm 0x80),
       .store8 (at_ .edx 32) .cl, .alu .add .edi (.imm 1),
       .mov .esi (.imm 0), .alu .cmp .edi (.imm 57)]))
    (.seq (.ite .ae (.block [.mov .esi (.imm 1)]) (.block []))
      (.loop VG.Impl.Sha256.X86.Stream.finalizeBody .e)) := rfl

/-- `vg_sha256_finalize` up to writing the digest, from its precondition. -/
theorem hash_ok {s : State} (hp : SPre s) : WP isa finalizeHash s (SDone s) := by
  rw [finalizeHash_eq, ← VG.Proof.Sha256.X86.Stream.Finalize.seq_assoc]
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86.Stream.Finalize.prologue_ok hp) fun s₁ ⟨k, hL⟩ => ?_)
  refine WP.loop (M := isa) (fun i s' => ∃ n, VG.Proof.Sha256.X86.Stream.Finalize.LInv s i n s') ?_ k s₁ ⟨_, hL⟩
  rintro i s' ⟨n, hL⟩
  refine WP.mono (VG.Proof.Sha256.X86.Stream.Finalize.body_ok hp hL) fun s'' h => ?_
  rcases h with ⟨he, hD⟩ | ⟨he, rfl, hL'⟩
  · exact .inl ⟨he, hD⟩
  · exact .inr ⟨he, 0, by omega, 0, hL'⟩

/-- The state after the prologue, with the permissions of `vg_sha256_finalize`. -/
abbrev narrow (s₀ s : State) : State := s.withRegions [] (finW s₀)

theorem narrow_arg {s₀ s : State} (hp : Pre s₀) (h : Pro s₀ s) {i : Nat} (hi : i < 5) :
    arg (narrow s₀ s) i = [inn s₀, arg s₀ 2, arg s₀ 3, out s₀, scr s₀].getD i 0 := by
  have sp : s.gpr .esp = esp₀ s₀ := h.gpr _ (by decide) (by decide)
  show s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = _
  rw [h.mem, sp]; exact proMem_arg hp i hi

theorem narrow_pre {s₀ s : State} (hp : Pre s₀) (h : Pro s₀ s) : SPre (narrow s₀ s) := by
  have sp : s.gpr .esp = esp₀ s₀ := h.gpr .esp (by decide) (by decide)
  have a0 : arg (narrow s₀ s) 0 = inn s₀ := narrow_arg hp h (by omega)
  have a3 : arg (narrow s₀ s) 3 = out s₀ := narrow_arg hp h (by omega)
  have a4 : arg (narrow s₀ s) 4 = scr s₀ := narrow_arg hp h (by omega)
  have s160 : Region.Sub ⟨scA s₀, 160⟩ (scR s₀) := Region.sub_prefix (by omega)
  have a20 : Region.Sub ⟨addr (esp₀ s₀) 4, 20⟩ (argR s₀) := Region.sub_prefix (by omega)
  have fs := hp.scr_fit
  have fsp := hp.sp_fit
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show finW s₀ = [⟨(arg (narrow s₀ s) 0).setWidth 64, 96⟩, ⟨(arg (narrow s₀ s) 3).setWidth 64, 32⟩,
      ⟨(arg (narrow s₀ s) 4).setWidth 64, 160⟩, ⟨addr (s.gpr .esp) 4, 20⟩]
    rw [a0, a3, a4, sp]
  · show Region.Disjoint ⟨(arg (narrow s₀ s) 0).setWidth 64, 96⟩ ⟨(arg (narrow s₀ s) 3).setWidth 64, 32⟩
    rw [a0, a3]; exact hp.in_out
  · show Region.Disjoint ⟨(arg (narrow s₀ s) 0).setWidth 64, 96⟩ ⟨(arg (narrow s₀ s) 4).setWidth 64, 160⟩
    rw [a0, a4]; exact hp.in_scr.sub_right s160
  · show Region.Disjoint ⟨(arg (narrow s₀ s) 3).setWidth 64, 32⟩ ⟨(arg (narrow s₀ s) 4).setWidth 64, 160⟩
    rw [a3, a4]; exact hp.out_scr.sub_right s160
  · show Region.Disjoint ⟨addr (s.gpr .esp) 4, 20⟩ ⟨(arg (narrow s₀ s) 0).setWidth 64, 96⟩
    rw [a0, sp]; exact hp.a_in.sub_left a20
  · show Region.Disjoint ⟨addr (s.gpr .esp) 4, 20⟩ ⟨(arg (narrow s₀ s) 3).setWidth 64, 32⟩
    rw [a3, sp]; exact hp.a_out.sub_left a20
  · show Region.Disjoint ⟨addr (s.gpr .esp) 4, 20⟩ ⟨(arg (narrow s₀ s) 4).setWidth 64, 160⟩
    rw [a4, sp]; exact (hp.a_scr.sub_left a20).sub_right s160
  · show Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg (narrow s₀ s) 0).setWidth 64, 96⟩
    rw [a0, sp]; exact hp.ret_in
  · show Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg (narrow s₀ s) 3).setWidth 64, 32⟩
    rw [a3, sp]; exact hp.ret_out
  · show Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg (narrow s₀ s) 4).setWidth 64, 160⟩
    rw [a4, sp]; exact hp.ret_scr.sub_right s160
  · show (arg (narrow s₀ s) 0).toNat + 96 ≤ 2 ^ 32
    rw [a0]; exact hp.in_fit
  · show (arg (narrow s₀ s) 3).toNat + 32 ≤ 2 ^ 32
    rw [a3]; exact hp.out_fit
  · show (arg (narrow s₀ s) 4).toNat + 160 ≤ 2 ^ 32
    rw [a4]; omega
  · show (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
    rw [sp]; omega

end VG.Proof.Hmac.X86.Finalize
