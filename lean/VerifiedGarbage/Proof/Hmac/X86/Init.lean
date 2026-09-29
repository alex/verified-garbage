import VerifiedGarbage.Proof.Hmac.X86.Finalize
import VerifiedGarbage.Proof.Hmac.X86_64.Init
import VerifiedGarbage.Proof.Sha256.AArch64.Compress
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Spec.Hmac.Contract

/-!
# HMAC-SHA-256 on x86 (32-bit): `init`

Untrusted: everything here is checked by Lean. The prologue saves our
caller's registers in `scratch[112..128)` and stores `H⁽⁰⁾` in both states;
the key loop and the pad loop then fill the inner buffer with `K₀ ⊕ ipad`
a byte at a time (invariant `Buf`: `j` bytes written, `edx` at byte `j`),
the outer buffer is computed from it a word at a time (`xorWords_ok`), and
each buffer is compressed with the inlined compression function
(`compBuf_ok`, via `compressAt_ok`), after which each state represents its
block (`X86_64.Init.repr_block`).
-/

namespace VG.Proof.Hmac.X86.Init

open VG VG.X86 VG.Impl.Hmac.X86
open VG.Impl.Sha256.X86 (at_)
open VG.Impl.Sha256.X86.Stream (compressAt save restore saved)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame writeBytes_append repr_congr)
open VG.Proof.Hmac.X86
open VG.Proof.Hmac.X86_64 (bytesAt_length)
open VG.Spec.Sha256 (HashValue stateAt blockAt compress bytesAt Repr H0)
open VG.Spec.Hmac (xorPad ipad opad blockKey sha256)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev inn : BitVec 32 := arg s₀ 0
abbrev ou : BitVec 32 := arg s₀ 1
abbrev kp : BitVec 32 := arg s₀ 2
abbrev kl : Nat := (arg s₀ 3).toNat
abbrev scr : BitVec 32 := arg s₀ 4
abbrev inA : Addr := (inn s₀).setWidth 64
abbrev ouA : Addr := (ou s₀).setWidth 64
abbrev kA : Addr := (kp s₀).setWidth 64
abbrev scA : Addr := (scr s₀).setWidth 64
abbrev inR : Region := ⟨inA s₀, 96⟩
abbrev ouR : Region := ⟨ouA s₀, 96⟩
abbrev kR : Region := ⟨kA s₀, kl s₀⟩
abbrev scR : Region := ⟨scA s₀, 160⟩
abbrev argR : Region := ⟨addr (esp₀ s₀) 4, 20⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩

/-- The key, padded with zeros to a block. -/
def K0 : List Byte := bytesAt s₀.mem (kA s₀) (kl s₀) ++ List.replicate (64 - kl s₀) 0

end

structure Pre (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ 64
  rd : s₀.rd = [kR s₀]
  wr : s₀.wr = [inR s₀, ouR s₀, scR s₀, argR s₀]
  i_o : (inR s₀).Disjoint (ouR s₀)
  i_s : (inR s₀).Disjoint (scR s₀)
  o_s : (ouR s₀).Disjoint (scR s₀)
  a_i : (argR s₀).Disjoint (inR s₀)
  a_o : (argR s₀).Disjoint (ouR s₀)
  a_s : (argR s₀).Disjoint (scR s₀)
  k_i : (kR s₀).Disjoint (inR s₀)
  k_o : (kR s₀).Disjoint (ouR s₀)
  k_s : (kR s₀).Disjoint (scR s₀)
  k_a : (kR s₀).Disjoint (argR s₀)
  ret_i : (retR s₀).Disjoint (inR s₀)
  ret_o : (retR s₀).Disjoint (ouR s₀)
  ret_s : (retR s₀).Disjoint (scR s₀)
  in_fit : (inn s₀).toNat + 96 ≤ 2 ^ 32
  ou_fit : (ou s₀).toNat + 96 ≤ 2 ^ 32
  k_fit : (kp s₀).toNat + kl s₀ ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 160 ≤ 2 ^ 32
  sp_fit : (esp₀ s₀).toNat + 24 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : Proof.Hmac.initSha256X86.pre s₀) : Pre s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩

/-! ## Regions and the key -/

theorem K0_length (s₀ : State) (hp : Pre s₀) : (K0 s₀).length = 64 := by
  simp [K0, bytesAt_length]; have := hp.kl_le; omega

theorem blockKey_eq {s₀ : State} (hp : Pre s₀) :
    blockKey sha256 (bytesAt s₀.mem (kA s₀) (kl s₀)) = K0 s₀ := by
  have := hp.kl_le
  simp [blockKey, sha256, K0, bytesAt_length, show ¬ (64 < kl s₀) by omega]

theorem K0_lt {s₀ : State} {j : Nat} (hj : j < kl s₀) (h : j < (K0 s₀).length) :
    (K0 s₀)[j] = s₀.mem (kA s₀ + BitVec.ofNat 64 j) := by
  simp only [K0]
  rw [List.getElem_append_left (by rw [bytesAt_length]; exact hj)]
  simp [bytesAt]

theorem K0_ge {s₀ : State} {j : Nat} (hj : kl s₀ ≤ j) (h : j < (K0 s₀).length) : (K0 s₀)[j] = 0 := by
  simp only [K0]
  rw [List.getElem_append_right (by rw [bytesAt_length]; exact hj)]
  simp

theorem ret_a {s₀ : State} (hp : Pre s₀) : (retR s₀).Disjoint (argR s₀) := by
  have := hp.sp_fit
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [addr_eq (by omega)] at h₂
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem scr_in {d n : Nat} (hd : d + n ≤ 160) (hn : 0 < n) : (scR s₀).Contains (addr (scr s₀) d) n :=
  contains_addr hd hn hp.scr_fit

theorem in_in {d n : Nat} (hd : d + n ≤ 96) (hn : 0 < n) : (inR s₀).Contains (addr (inn s₀) d) n :=
  contains_addr hd hn hp.in_fit

theorem ou_in {d n : Nat} (hd : d + n ≤ 96) (hn : 0 < n) : (ouR s₀).Contains (addr (ou s₀) d) n :=
  contains_addr hd hn hp.ou_fit

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  simp only [Region.Contains]
  rw [addr_eq (by omega), addr_eq (by omega),
    show (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d - ((esp₀ s₀).setWidth 64 + BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (d - 4) by
      rw [show d = (d - 4) + 4 by omega, BitVec.ofNat_add]; bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A word of the scratch space, as a region. -/
theorem scr_sub {d : Nat} (hd : d + 4 ≤ 160) : Region.Sub ⟨addr (scr s₀) d, 4⟩ (scR s₀) := by
  rw [addr_eq (by have := hp.scr_fit; omega)]
  exact sub_offset hd (by omega)

/-- An argument word, as a region. -/
theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  intro a ha
  simp only [Region.Contains] at ha ⊢
  rw [addr_eq (by omega)] at ha
  rw [addr_eq (by omega)]
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

/-- The argument words lie outside `inner`, `outer` and `scratch`. -/
theorem arg_disj {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) :
    ∀ r ∈ [inR s₀, ouR s₀, scR s₀], Region.Disjoint ⟨addr (esp₀ s₀) d, 4⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.a_i.sub_left (hp.arg_sub hd₁ hd)
  · exact hp.a_o.sub_left (hp.arg_sub hd₁ hd)
  · exact hp.a_s.sub_left (hp.arg_sub hd₁ hd)

end Pre

/-! ## The saved registers -/

/-- Our caller's `ebx, esi, edi, ebp` in `scratch[112..128)`. -/
def Saved (s₀ : State) (m : Mem) : Prop := ∀ p ∈ saved, m.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1

theorem saved_off {p : Reg × Nat} (h : p ∈ saved) : 112 ≤ p.2 ∧ p.2 + 4 ≤ 128 := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp

theorem saved_frame {s₀ : State} {m m' : Mem} (h : Saved s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ d, 112 ≤ d → d + 4 ≤ 128 → ∀ r ∈ rs, Region.Disjoint ⟨addr (scr s₀) d, 4⟩ r) : Saved s₀ m' := by
  intro p hp'
  rw [← h p hp']
  have := saved_off hp'
  exact hf.readW (Region.contains_self _ _) (hd p.2 this.1 this.2) (by decide)

/-- The save area lies outside a region disjoint from `scratch`. -/
theorem save_disj {s₀ : State} (hp : Pre s₀) {R : Region} (hR : R.Disjoint (scR s₀)) :
    ∀ d, 112 ≤ d → d + 4 ≤ 128 → Region.Disjoint ⟨addr (scr s₀) d, 4⟩ R :=
  fun _ _ hd => hR.symm.sub_left (hp.scr_sub (by omega))

/-- And outside the first 112 bytes of `scratch`. -/
theorem save_disj112 {s₀ : State} (hp : Pre s₀) :
    ∀ d, 112 ≤ d → d + 4 ≤ 128 → Region.Disjoint ⟨addr (scr s₀) d, 4⟩ ⟨scA s₀, 112⟩ := by
  intro d h₁ h₂ a ha hb
  have := hp.scr_fit
  simp only [Region.Contains] at ha hb
  rw [addr_eq (by omega)] at ha
  bv_omega

/-! ## Prologue -/

/-- The memory after saving our caller's registers. -/
def saveMem (s₀ : State) : Mem :=
  (((s₀.mem.writeW (addr (scr s₀) 112) (s₀.gpr .ebx)).writeW (addr (scr s₀) 116) (s₀.gpr .esi)).writeW
    (addr (scr s₀) 120) (s₀.gpr .edi)).writeW (addr (scr s₀) 124) (s₀.gpr .ebp)

/-- And after storing `H⁽⁰⁾` in both states. -/
def proMem (s₀ : State) : Mem :=
  Proof.Sha256.AArch64.writeState (Proof.Sha256.AArch64.writeState (saveMem s₀) (inA s₀) H0) (ouA s₀) H0

theorem saveMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d, d + 4 ≤ 160 → (scR s₀).Contains (addr (scr s₀) d) (32 / 8) := fun d hd => hp.scr_in hd (by omega)
  simp only [saveMem]
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 112 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 116 (by omega))).writeW (List.mem_singleton_self _) _
    (c 120 (by omega))).writeW (List.mem_singleton_self _) _ (c 124 (by omega))

theorem saveMem_saved {s₀ : State} (hp : Pre s₀) : Saved s₀ (saveMem s₀) := by
  have hs := hp.scr_fit
  have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ 160 → e + 4 ≤ 160 → d + 4 ≤ e ∨ e + 4 ≤ d →
      (m.writeW (addr (scr s₀) e) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
    fun m v d e h₁ h₂ h => readW_writeW_addr m v (by omega) (by omega) h
  intro p hp'
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl <;> simp only [saveMem]
  · rw [w _ _ 112 124 (by omega) (by omega) (by omega), w _ _ 112 120 (by omega) (by omega) (by omega),
      w _ _ 112 116 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [w _ _ 116 124 (by omega) (by omega) (by omega), w _ _ 116 120 (by omega) (by omega) (by omega),
      Mem.readW_writeW_self32]
  · rw [w _ _ 120 124 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

/-- Writing a hash value stays within its 32 bytes. -/
theorem writeState_frame (m : Mem) (p : Addr) (v : HashValue) :
    Frame [⟨p, 32⟩] m (Proof.Sha256.AArch64.writeState m p v) := by
  have c : ∀ k, k < 8 → (⟨p, 32⟩ : Region).Contains (p + BitVec.ofNat 64 (4 * k)) (32 / 8) :=
    fun k hk => contains_offset (by omega) (by omega)
  unfold Proof.Sha256.AArch64.writeState
  exact ((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 1 (by omega))).writeW (List.mem_singleton_self _) _
    (c 2 (by omega))).writeW (List.mem_singleton_self _) _ (c 3 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 4 (by omega))).writeW (List.mem_singleton_self _) _
    (c 5 (by omega))).writeW (List.mem_singleton_self _) _ (c 6 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 7 (by omega))

theorem sub32 (p : Addr) : Region.Sub ⟨p, 32⟩ ⟨p, 96⟩ := Region.sub_prefix (by omega)

theorem proMem_frame {s₀ : State} (hp : Pre s₀) : Frame [inR s₀, ouR s₀, scR s₀] s₀.mem (proMem s₀) := by
  refine (((saveMem_frame hp).mono (by simp)).trans ((writeState_frame _ _ _).sub ?_)).trans
    ((writeState_frame _ _ _).sub ?_)
  · simp only [List.mem_singleton]; rintro r rfl; exact ⟨inR s₀, by simp, sub32 _⟩
  · simp only [List.mem_singleton]; rintro r rfl; exact ⟨ouR s₀, by simp, sub32 _⟩

theorem proMem_saved {s₀ : State} (hp : Pre s₀) : Saved s₀ (proMem s₀) := by
  refine saved_frame (saved_frame (saveMem_saved hp) (writeState_frame _ _ _) ?_) (writeState_frame _ _ _) ?_
  · intro d h₁ h₂ r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact save_disj hp (hp.i_s.sub_left (sub32 _)) d h₁ h₂
  · intro d h₁ h₂ r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact save_disj hp (hp.o_s.sub_left (sub32 _)) d h₁ h₂

theorem proMem_stI {s₀ : State} (hp : Pre s₀) : stateAt (proMem s₀) (inA s₀) = H0 := by
  refine (Proof.Sha256.Stream.stateAt_congr fun i hi => ?_).trans
    (Proof.Sha256.AArch64.stateAt_writeState (saveMem s₀) _ _)
  exact frame_bytes (writeState_frame _ _ _) (R := ⟨inA s₀, 32⟩)
    (by simpa using (hp.i_o.sub_left (sub32 _)).sub_right (sub32 _)) (by simp) hi

theorem proMem_stO {s₀ : State} : stateAt (proMem s₀) (ouA s₀) = H0 :=
  Proof.Sha256.AArch64.stateAt_writeState _ _ _

/-- Reading an argument word from memory that differs only in `inner`, `outer` and `scratch`. -/
theorem arg_frame {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [inR s₀, ouR s₀, scR s₀] s₀.mem m)
    {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) :
    m.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 :=
  hf.readW (Region.contains_self _ _) (hp.arg_disj hd₁ hd) (by decide)

/-- The two instructions storing the word `x` at `[b + 4 * k]`. -/
def wordB (b : Reg) (x : BitVec 32) (k : Nat) : List Instr := [.mov .ecx (.imm x), .store (at_ b (4 * k)) .ecx]

theorem h0_eq (b : Reg) : h0 b = wordB b H0[0] 0 ++ wordB b H0[1] 1 ++ wordB b H0[2] 2 ++ wordB b H0[3] 3 ++
    wordB b H0[4] 4 ++ wordB b H0[5] 5 ++ wordB b H0[6] 6 ++ wordB b H0[7] 7 := rfl

theorem wordB_ok {b : Reg} (hb : b ≠ .ecx) {x : BitVec 32} {k : Nat} {rest : List Instr} {s : State}
    {Q : State → Prop} {st : BitVec 32} (hst : s.gpr b = st) (hout : InRegions s.wr (addr st (4 * k)) 4)
    (kk : ∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = s.mem.writeW (addr st (4 * k)) x → WP isa (.block rest) s' Q) :
    WP isa (.block (wordB b x k ++ rest)) s Q := by
  simp only [wordB, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ u₁ => wp_store (a := addr st (4 * k))
    (by rw [ea_at, u₁.other _ hb, hst]) (by rw [u₁.wr]; exact hout) fun s₂ u₂ => ?_
  refine kk s₂ (fun r hr => by rw [u₂.gpr, u₁.other r hr]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) ?_
  rw [u₂.mem, u₁.gpr, u₁.mem]

/-- `H⁽⁰⁾` stored at `[b]`. -/
theorem h0_ok {b : Reg} (hb : b ≠ .ecx) {st : BitVec 32} (hfit : st.toNat + 32 ≤ 2 ^ 32) {rest : List Instr}
    {s : State} {Q : State → Prop} (hst : s.gpr b = st) (hout : ∀ k < 8, InRegions s.wr (addr st (4 * k)) 4)
    (kk : ∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = Proof.Sha256.AArch64.writeState s.mem (st.setWidth 64) H0 → WP isa (.block rest) s' Q) :
    WP isa (.block (h0 b ++ rest)) s Q := by
  rw [h0_eq]
  simp only [List.append_assoc]
  refine wordB_ok hb hst (hout 0 (by omega)) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  refine wordB_ok hb (by rw [g₁ _ hb, hst]) (by rw [wr₁]; exact hout 1 (by omega)) fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  refine wordB_ok hb (by rw [g₂ _ hb, g₁ _ hb, hst]) (by rw [wr₂, wr₁]; exact hout 2 (by omega))
    fun s₃ g₃ rd₃ wr₃ m₃ => ?_
  refine wordB_ok hb (by rw [g₃ _ hb, g₂ _ hb, g₁ _ hb, hst]) (by rw [wr₃, wr₂, wr₁]; exact hout 3 (by omega))
    fun s₄ g₄ rd₄ wr₄ m₄ => ?_
  refine wordB_ok hb (by rw [g₄ _ hb, g₃ _ hb, g₂ _ hb, g₁ _ hb, hst])
    (by rw [wr₄, wr₃, wr₂, wr₁]; exact hout 4 (by omega)) fun s₅ g₅ rd₅ wr₅ m₅ => ?_
  refine wordB_ok hb (by rw [g₅ _ hb, g₄ _ hb, g₃ _ hb, g₂ _ hb, g₁ _ hb, hst])
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact hout 5 (by omega)) fun s₆ g₆ rd₆ wr₆ m₆ => ?_
  refine wordB_ok hb (by rw [g₆ _ hb, g₅ _ hb, g₄ _ hb, g₃ _ hb, g₂ _ hb, g₁ _ hb, hst])
    (by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hout 6 (by omega)) fun s₇ g₇ rd₇ wr₇ m₇ => ?_
  refine wordB_ok hb (by rw [g₇ _ hb, g₆ _ hb, g₅ _ hb, g₄ _ hb, g₃ _ hb, g₂ _ hb, g₁ _ hb, hst])
    (by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hout 7 (by omega)) fun s₈ g₈ rd₈ wr₈ m₈ => ?_
  refine kk s₈ (fun r h => by rw [g₈ r h, g₇ r h, g₆ r h, g₅ r h, g₄ r h, g₃ r h, g₂ r h, g₁ r h])
    (by rw [rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]) (by rw [wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]) ?_
  have ha : ∀ k, k < 8 → addr st (4 * k) = st.setWidth 64 + BitVec.ofNat 64 (4 * k) :=
    fun k hk => addr_eq (by omega)
  rw [m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁, ha 0 (by omega), ha 1 (by omega), ha 2 (by omega),
    ha 3 (by omega), ha 4 (by omega), ha 5 (by omega), ha 6 (by omega), ha 7 (by omega)]
  rfl

/-! ## The loop invariants -/

/-- The memory while building the inner buffer: `j` bytes of `K₀ ⊕ ipad` are written. -/
structure BufMem (s₀ : State) (j : Nat) (m : Mem) : Prop where
  stI : stateAt m (inA s₀) = H0
  stO : stateAt m (ouA s₀) = H0
  buf : bytesAt m (inA s₀ + 32) j = ((K0 s₀).take j).map (· ^^^ ipad)
  saved : Saved s₀ m
  frame : Frame [inR s₀, ouR s₀, scR s₀] s₀.mem m

structure Buf (s₀ : State) (j : Nat) (s : State) : Prop where
  j_le : j ≤ 64
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = inn s₀
  esi : s.gpr .esi = ou s₀
  ebp : s.gpr .ebp = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  edx : s.gpr .edx = inn s₀ + BitVec.ofNat 32 (32 + j)
  mem : BufMem s₀ j s.mem

/-- In the key loop, `edi` points at key byte `j` and `ecx` counts the bytes left. -/
structure Key (s₀ : State) (j : Nat) (s : State) : Prop extends Buf s₀ j s where
  edi : s.gpr .edi = kp s₀ + BitVec.ofNat 32 j
  ecx : s.gpr .ecx = BitVec.ofNat 32 (kl s₀ - j)

theorem proMem_buf {s₀ : State} (hp : Pre s₀) : BufMem s₀ 0 (proMem s₀) :=
  ⟨proMem_stI hp, proMem_stO, by simp [bytesAt], proMem_saved hp, proMem_frame hp⟩

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (([.mov .eax (.mem (at_ .esp 20))] : List Instr) ++ save .eax ++
      ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .esi (.mem (at_ .esp 8))] : List Instr) ++
      h0 .ebx ++ h0 .esi ++
      ([.mov .edi (.mem (at_ .esp 12)), .mov .ecx (.mem (at_ .esp 16)), .mov .edx (.reg .ebx),
       .alu .add .edx (.imm 32), .alu .test .ecx (.reg .ecx)] : List Instr))) s₀
      fun s => Key s₀ 0 s ∧ s.zf = some (decide (kl s₀ = 0)) := by
  have hsp := hp.sp_fit
  have rin : ∀ (s : State), s.rd = s₀.rd → s.wr = s₀.wr → ∀ d, 4 ≤ d → d + 4 ≤ 24 →
      InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
    fun s h₁ h₂ d h₃ h₄ => ⟨argR s₀, by simp [h₁, h₂, hp.wr], hp.arg_in h₃ h₄⟩
  have sin : ∀ d, d + 4 ≤ 160 → InRegions s₀.wr (addr (scr s₀) d) 4 :=
    fun d hd => ⟨scR s₀, by simp [hp.wr], hp.scr_in hd (by omega)⟩
  have argSave : ∀ e, 4 ≤ e → e + 4 ≤ 24 →
      (saveMem s₀).readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 :=
    fun e h₁ h₂ => arg_frame hp ((saveMem_frame hp).mono (by simp)) h₁ h₂
  simp only [List.append_assoc, List.cons_append, List.nil_append, save, saved, List.map_cons, List.map_nil]
  refine wp_movm (a := addr (esp₀ s₀) 20) (ea_at _ _ _) (rin _ rfl rfl 20 (by omega) (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_store (a := addr (scr s₀) 112) (by rw [ea_at, e₁]) (by rw [u₁.wr]; exact sin 112 (by omega))
    fun s₂ u₂ => ?_
  refine wp_store (a := addr (scr s₀) 116) (by rw [ea_at, u₂.gpr, e₁]) (by rw [u₂.wr, u₁.wr]; exact sin 116 (by omega))
    fun s₃ u₃ => ?_
  refine wp_store (a := addr (scr s₀) 120) (by rw [ea_at, u₃.gpr, u₂.gpr, e₁])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact sin 120 (by omega)) fun s₄ u₄ => ?_
  refine wp_store (a := addr (scr s₀) 124) (by rw [ea_at, u₄.gpr, u₃.gpr, u₂.gpr, e₁])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact sin 124 (by omega)) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have m₅ : s₅.mem = saveMem s₀ := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem,
      u₁.other .ebx (by decide), u₁.other .esi (by decide), u₁.other .edi (by decide), u₁.other .ebp (by decide)]
    rfl
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₅ : s₅.gpr .esp = esp₀ s₀ := by rw [g₅, u₁.other _ (by decide)]
  refine wp_mov fun s₆ u₆ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 4) (by rw [ea_at, u₆.other _ (by decide), sp₅])
    (rin _ (by rw [u₆.rd, rd₅]) (by rw [u₆.wr, wr₅]) 4 (by omega) (by omega)) fun s₇ u₇ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 8) (by rw [ea_at, u₇.other _ (by decide), u₆.other _ (by decide), sp₅])
    (rin _ (by rw [u₇.rd, u₆.rd, rd₅]) (by rw [u₇.wr, u₆.wr, wr₅]) 8 (by omega) (by omega)) fun s₈ u₈ => ?_
  have ebp₈ : s₈.gpr .ebp = scr s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅, e₁]
  have ebx₈ : s₈.gpr .ebx = inn s₀ := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.mem, m₅, argSave 4 (by omega) (by omega)]; rfl
  have esi₈ : s₈.gpr .esi = ou s₀ := by
    rw [u₈.gpr, u₇.mem, u₆.mem, m₅, argSave 8 (by omega) (by omega)]; rfl
  have g₈ : ∀ r, r ≠ .ebx → r ≠ .esi → r ≠ .ebp → s₈.gpr r = s₅.gpr r := fun r h₁ h₂ h₃ => by
    rw [u₈.other r h₂, u₇.other r h₁, u₆.other r h₃]
  have rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, rd₅]
  have wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, wr₅]
  have m₈ : s₈.mem = saveMem s₀ := by rw [u₈.mem, u₇.mem, u₆.mem, m₅]
  refine h0_ok (by decide) (st := inn s₀) (by have := hp.in_fit; omega) ebx₈
    (fun k hk => ⟨inR s₀, by simp [wr₈, hp.wr], hp.in_in (by omega) (by omega)⟩) fun s₉ g₉ rd₉ wr₉ m₉ => ?_
  refine h0_ok (by decide) (st := ou s₀) (by have := hp.ou_fit; omega) (by rw [g₉ _ (by decide), esi₈])
    (fun k hk => ⟨ouR s₀, by simp [wr₉, wr₈, hp.wr], hp.ou_in (by omega) (by omega)⟩)
    fun s₁₀ g₁₀ rd₁₀ wr₁₀ m₁₀ => ?_
  have m₁₀' : s₁₀.mem = proMem s₀ := by rw [m₁₀, m₉, m₈]; rfl
  have g₁₀' : ∀ r, r ≠ .ecx → s₁₀.gpr r = s₈.gpr r := fun r h => by rw [g₁₀ r h, g₉ r h]
  have rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₉, rd₈]
  have wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₉, wr₈]
  have sp₁₀ : s₁₀.gpr .esp = esp₀ s₀ := by
    rw [g₁₀' _ (by decide), g₈ _ (by decide) (by decide) (by decide), sp₅]
  have argPro : ∀ e, 4 ≤ e → e + 4 ≤ 24 →
      (proMem s₀).readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 :=
    fun e h₁ h₂ => arg_frame hp (proMem_frame hp) h₁ h₂
  refine wp_movm (a := addr (esp₀ s₀) 12) (by rw [ea_at, sp₁₀]) (rin _ rd₁₀' wr₁₀' 12 (by omega) (by omega))
    fun s₁₁ u₁₁ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 16) (by rw [ea_at, u₁₁.other _ (by decide), sp₁₀])
    (rin _ (by rw [u₁₁.rd, rd₁₀']) (by rw [u₁₁.wr, wr₁₀']) 16 (by omega) (by omega)) fun s₁₂ u₁₂ => ?_
  refine wp_mov fun s₁₃ u₁₃ => wp_addi fun s₁₄ u₁₄ => wp_test fun s₁₅ f₁₅ z₁₅ => WP.block_nil ?_
  have g₁₅ : ∀ r, r ≠ .ecx → r ≠ .edi → r ≠ .edx → s₁₅.gpr r = s₈.gpr r := fun r h₁ h₂ h₃ => by
    rw [f₁₅.gpr, u₁₄.other r h₃, u₁₃.other r h₃, u₁₂.other r h₁, u₁₁.other r h₂, g₁₀' r h₁]
  have ecx₁₅ : s₁₅.gpr .ecx = arg s₀ 3 := by
    rw [f₁₅.gpr, u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.mem, m₁₀',
      argPro 16 (by omega) (by omega)]; rfl
  have e3 : arg s₀ 3 = BitVec.ofNat 32 (kl s₀) := by simp
  refine ⟨⟨⟨by omega, by rw [f₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, rd₁₀'],
    by rw [f₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, wr₁₀'],
    by rw [g₁₅ _ (by decide) (by decide) (by decide), ebx₈],
    by rw [g₁₅ _ (by decide) (by decide) (by decide), esi₈],
    by rw [g₁₅ _ (by decide) (by decide) (by decide), ebp₈],
    by rw [g₁₅ _ (by decide) (by decide) (by decide), g₈ _ (by decide) (by decide) (by decide), sp₅], ?_,
    by rw [f₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀']; exact proMem_buf hp⟩, ?_, ?_⟩, ?_⟩
  · rw [f₁₅.gpr, u₁₄.gpr, u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      g₁₀' _ (by decide), ebx₈]
    rfl
  · rw [f₁₅.gpr, u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr,
      m₁₀', argPro 12 (by omega) (by omega)]
    simp; rfl
  · rw [ecx₁₅, e3, Nat.sub_zero]
  · rw [z₁₅, ← f₁₅.gpr, ecx₁₅, BitVec.and_self, e3, ofNat_beq_zero (by have := (arg s₀ 3).isLt; omega)]

/-! ## The key and pad loops -/

theorem wp_xori {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem xor_byte (b : Byte) (v : BitVec 32) : ((b.setWidth 32) ^^^ v).setWidth 8 = b ^^^ v.setWidth 8 := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

/-- Byte `j` of the inner buffer, as the loops address it. -/
theorem edx_addr {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : j < 64) :
    addr (inn s₀ + BitVec.ofNat 32 (32 + j)) 0 = inA s₀ + 32 + BitVec.ofNat 64 j := by
  have := hp.in_fit
  rw [addr_add_ofNat (by omega), Nat.add_zero, BitVec.ofNat_add, ← BitVec.add_assoc]; rfl

theorem edx_succ (x : BitVec 32) (j : Nat) :
    x + BitVec.ofNat 32 (32 + j) + 1 = x + BitVec.ofNat 32 (32 + (j + 1)) := by
  rw [← Nat.add_assoc, ofNat_succ, BitVec.add_assoc]

theorem cmp_end (x : BitVec 32) {j : Nat} (hj : j ≤ 64) :
    (x + BitVec.ofNat 32 (32 + j) - (x + 96) == 0) = decide (j = 64) := by
  have e : x + BitVec.ofNat 32 (32 + j) - (x + 96) = BitVec.ofNat 32 (32 + j) - BitVec.ofNat 32 96 := by
    generalize BitVec.ofNat 32 (32 + j) = y
    rw [show BitVec.ofNat 32 96 = 96 from rfl]
    bv_omega
  rw [e, sub_beq (by omega) (by omega)]
  exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩

/-- Byte `j` of the inner buffer. -/
theorem buf_write {s₀ : State} (hp : Pre s₀) {j : Nat} {m : Mem} (h : BufMem s₀ j m) (hj : j < 64) :
    BufMem s₀ (j + 1) (m.writeW (inA s₀ + 32 + BitVec.ofNat 64 j)
      ((K0 s₀)[j]'(by rw [K0_length s₀ hp]; omega) ^^^ ipad)) := by
  have hl : j < (K0 s₀).length := by rw [K0_length s₀ hp]; omega
  set x := (K0 s₀)[j] ^^^ ipad
  let bI : Region := ⟨inA s₀ + 32, 64⟩
  have sI : Region.Sub bI (inR s₀) := sub_offset (off := 32) (by omega) (by omega)
  have F : Frame [bI] m (m.writeW (inA s₀ + 32 + BitVec.ofNat 64 j) x) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) x (contains_offset (by omega) (by omega))
  have st : ∀ p : Addr, Region.Disjoint ⟨p, 32⟩ bI →
      stateAt (m.writeW (inA s₀ + 32 + BitVec.ofNat 64 j) x) p = stateAt m p :=
    fun p hd => Proof.Sha256.Stream.stateAt_congr fun i hi =>
      frame_bytes F (R := ⟨p, 32⟩) (by simpa using hd) (by simp) hi
  have self : Region.Disjoint ⟨inA s₀, 32⟩ bI := fun a h₁ h₂ => by
    simp only [Region.Contains, bI] at h₁ h₂; bv_omega
  refine ⟨?_, ?_, ?_, saved_frame h.saved F ?_, h.frame.trans (F.sub ?_)⟩
  · rw [st _ self, h.stI]
  · rw [st _ ((hp.i_o.symm.sub_left (sub32 _)).sub_right sI), h.stO]
  · rw [VG.Proof.Hmac.X86_64.Init.bytesAt_snoc _ _ (by omega), h.buf, List.take_succ_eq_append_getElem hl,
      List.map_append]
    rfl
  · intro d h₁ h₂ r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact save_disj hp (hp.i_s.sub_left sI) d h₁ h₂
  · simp only [List.mem_singleton]; rintro r rfl; exact ⟨inR s₀, by simp, sI⟩

def keyBody : List Instr :=
  [.movzx8 .eax (at_ .edi 0), .alu .xor .eax (.imm 0x36), .store8 (at_ .edx 0) .al,
    .alu .add .edi (.imm 1), .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]

theorem keyLoop_eq : keyLoop = .loop (.block keyBody) .ne := rfl

theorem in_buf {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : j < 64) {wr : List Region} (hwr : wr = s₀.wr) :
    InRegions wr (inA s₀ + 32 + BitVec.ofNat 64 j) 1 :=
  ⟨inR s₀, by simp [hwr, hp.wr], by
    rw [BitVec.add_assoc, show (32 : Addr) + BitVec.ofNat 64 j = BitVec.ofNat 64 (32 + j) by
      rw [BitVec.ofNat_add]; rfl]
    exact contains_offset (by omega) (by omega)⟩

theorem key_step {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : j < kl s₀) {s : State} (h : Key s₀ j s) :
    WP isa (.block keyBody) s fun s' => Key s₀ (j + 1) s' ∧ s'.zf = some (decide (j + 1 = kl s₀)) := by
  have hkl := hp.kl_le
  have fk := hp.k_fit
  have hl : j < (K0 s₀).length := by rw [K0_length s₀ hp]; omega
  have hin : InRegions (s.rd ++ s.wr) (kA s₀ + BitVec.ofNat 64 j) 1 :=
    ⟨kR s₀, by simp [h.rd, hp.rd], contains_offset (by omega) (by omega)⟩
  have hbyte : s.mem (kA s₀ + BitVec.ofNat 64 j) = (K0 s₀)[j] := by
    rw [K0_lt hj hl]
    refine frame_bytes h.mem.frame (R := kR s₀) ?_ (by show kl s₀ ≤ 2 ^ 64; omega) hj
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hp.k_i, hp.k_o, hp.k_s]
  unfold keyBody
  refine wp_movzx8 (a := kA s₀ + BitVec.ofNat 64 j)
    (by rw [ea_at, h.edi, addr_add_ofNat (by omega), Nat.add_zero]) hin fun s₁ u₁ => ?_
  refine wp_xori fun s₂ u₂ => ?_
  refine wp_store8 (a := inA s₀ + 32 + BitVec.ofNat 64 j)
    (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), h.edx, edx_addr hp (by omega)])
    (in_buf hp (by omega) (by rw [u₂.wr, u₁.wr, h.wr])) fun s₃ u₃ => ?_
  refine wp_addi fun s₄ u₄ => wp_addi fun s₅ u₅ => wp_subi fun s₆ u₆ z₆ => WP.block_nil ?_
  have k : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → s₆.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₆.other r h4, u₅.other r h3, u₄.other r h2, u₃.gpr, u₂.other r h1, u₁.other r h1]
  have v : (s₂.gpr Reg8.al.reg).setWidth 8 = (K0 s₀)[j] ^^^ ipad := by
    show (s₂.gpr .eax).setWidth 8 = _
    rw [u₂.gpr, u₁.gpr, xor_byte, hbyte]; rfl
  have ecx₅ : s₅.gpr .ecx = BitVec.ofNat 32 (kl s₀ - j) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      h.ecx]
  refine ⟨⟨⟨by omega, by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
      by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
      by rw [k _ (by decide) (by decide) (by decide) (by decide), h.ebx],
      by rw [k _ (by decide) (by decide) (by decide) (by decide), h.esi],
      by rw [k _ (by decide) (by decide) (by decide) (by decide), h.ebp],
      by rw [k _ (by decide) (by decide) (by decide) (by decide), h.esp], ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.edx, edx_succ]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, v, u₂.mem, u₁.mem]
    exact buf_write hp h.mem (by omega)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.edi, ofNat_succ, BitVec.add_assoc]
  · rw [u₆.gpr, ecx₅, ofNat_pred (by omega), show kl s₀ - j - 1 = kl s₀ - (j + 1) by omega]
  · rw [z₆, ecx₅, ofNat_pred (by omega), ofNat_beq_zero (by omega)]
    exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩)

def padBody : List Instr := [.store8 (at_ .edx 0) .cl, .alu .add .edx (.imm 1), .alu .cmp .edx (.reg .eax)]

theorem padLoop_eq : padLoop = .loop (.block padBody) .ne := rfl

/-- In the pad loop, `eax` is the end of the inner buffer and `ecx` is `ipad`. -/
structure Pad (s₀ : State) (j : Nat) (s : State) : Prop extends Buf s₀ j s where
  eax : s.gpr .eax = inn s₀ + 96
  ecx : s.gpr .ecx = 0x36

theorem pad_step {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : kl s₀ ≤ j) (hj' : j < 64) {s : State}
    (h : Pad s₀ j s) :
    WP isa (.block padBody) s fun s' => Pad s₀ (j + 1) s' ∧ s'.zf = some (decide (j + 1 = 64)) := by
  have hl : j < (K0 s₀).length := by rw [K0_length s₀ hp]; omega
  unfold padBody
  refine wp_store8 (a := inA s₀ + 32 + BitVec.ofNat 64 j) (by rw [ea_at, h.edx, edx_addr hp hj'])
    (in_buf hp hj' h.wr) fun s₁ u₁ => ?_
  refine wp_addi fun s₂ u₂ => wp_cmp fun s₃ f₃ _ z₃ => WP.block_nil ?_
  have k : ∀ r, r ≠ .edx → s₃.gpr r = s.gpr r := fun r h1 => by
    rw [f₃.gpr, u₂.other r h1, u₁.gpr]
  have v : (s.gpr Reg8.cl.reg).setWidth 8 = (K0 s₀)[j] ^^^ ipad := by
    show (s.gpr .ecx).setWidth 8 = _
    rw [h.ecx, K0_ge hj hl]; rfl
  have edx₂ : s₂.gpr .edx = inn s₀ + BitVec.ofNat 32 (32 + (j + 1)) := by
    rw [u₂.gpr, u₁.gpr, h.edx, edx_succ]
  refine ⟨⟨⟨by omega, by rw [f₃.rd, u₂.rd, u₁.rd, h.rd], by rw [f₃.wr, u₂.wr, u₁.wr, h.wr],
      by rw [k _ (by decide), h.ebx], by rw [k _ (by decide), h.esi], by rw [k _ (by decide), h.ebp],
      by rw [k _ (by decide), h.esp], by rw [f₃.gpr, edx₂], ?_⟩,
      by rw [k _ (by decide), h.eax], by rw [k _ (by decide), h.ecx]⟩, ?_⟩
  · rw [f₃.mem, u₂.mem, u₁.mem, v]
    exact buf_write hp h.mem hj'
  · rw [z₃, edx₂, u₂.other _ (by decide), u₁.gpr, h.eax, cmp_end _ (by omega)]

theorem key_loop_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Key s₀ 0 s) (hk : 0 < kl s₀) :
    WP isa keyLoop s (Buf s₀ (kl s₀)) := by
  rw [keyLoop_eq]
  refine WP.loop (M := isa) (fun n s => ∃ j, n = kl s₀ - j ∧ j < kl s₀ ∧ Key s₀ j s) ?_ (kl s₀) s
    ⟨0, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, hb⟩
  refine WP.mono (key_step hp hj hb) fun s' ⟨hb', hz⟩ => ?_
  by_cases hl : j + 1 = kl s₀
  · refine .inl ⟨by simp [eval, hz, hl], ?_⟩
    rw [hl] at hb'; exact hb'.toBuf
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

/-! ## The outer buffer -/

/-- A word read from memory, XORed with `0x6a` repeated, is its bytes XORed with `0x6a`. -/
theorem writeW_xor (m m' : Mem) (d a : Addr) :
    m.writeW d (m'.readW a 32 ^^^ 0x6a6a6a6a) = writeBytes m d ((bytesAt m' a 4).map (· ^^^ 0x6a)) := by
  rw [Finalize.writeW_le]
  congr 1
  simp only [Finalize.le, bytesAt, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  simp only [Function.comp]
  rw [BitVec.extractLsb'_xor, Mem.readW_byte m' a hj]
  congr 1
  interval_cases j <;> rfl

/-- Bytes `[A + a, A + a + 4)` of a range `[A, A + a + 4)` separate from `[B, B + b)`. -/
theorem sep_last {A B : Addr} {a b : Nat} (h : Mem.Sep A (a + 4) B b) (ha : a + 4 < 2 ^ 64) :
    Mem.Sep (A + BitVec.ofNat 64 a) 4 B b := by
  intro z hz hb
  refine h z ?_ hb
  rw [show z - A = (z - (A + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by bv_omega, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega)]
  have := Nat.mod_le ((z - (A + BitVec.ofNat 64 a)).toNat + a) (2 ^ 64)
  omega

/-- The outer buffer, a word at a time: `n` words of the inner buffer, XORed
with `0x6a6a6a6a`. -/
theorem xorWords_ok {x y : BitVec 32} (n : Nat) : ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr .ebx = x → s.gpr .esi = y → x.toNat + 32 + 4 * n ≤ 2 ^ 32 → y.toNat + 32 + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions (s.rd ++ s.wr) (addr x (32 + 4 * k)) 4) →
    (∀ k < n, InRegions s.wr (addr y (32 + 4 * k)) 4) →
    Mem.Sep (x.setWidth 64 + BitVec.ofNat 64 32) (4 * n) (y.setWidth 64 + BitVec.ofNat 64 32) (4 * n) →
    (∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (y.setWidth 64 + BitVec.ofNat 64 32)
        ((bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 32) (4 * n)).map (· ^^^ 0x6a)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap opadWord ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, Proof.Sha256.Stream.writeBytes_nil])
  | succ n ih =>
    intro rest s Q hx hy fx fy hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q hx hy (by omega) (by omega) (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun a ha hb => hsep a (by omega) (by omega)) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [opadWord, List.cons_append, List.nil_append]
    refine wp_movm (a := addr x (32 + 4 * n)) (by rw [ea_at, g₁ _ (by decide), hx])
      (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => wp_xori fun s₃ u₃ => ?_
    refine wp_store (a := addr y (32 + 4 * n))
      (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), hy])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega)) fun s₄ u₄ => ?_
    refine k s₄ (fun r hr => by rw [u₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr])
      (by rw [u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]) ?_
    set A := x.setWidth 64 + BitVec.ofNat 64 32
    set B := y.setWidth 64 + BitVec.ofNat 64 32
    set xs := (bytesAt s.mem A (4 * n)).map (· ^^^ (0x6a : Byte))
    have hl : xs.length = 4 * n := by simp [xs, bytesAt_length]
    have hsep' : Mem.Sep (A + BitVec.ofNat 64 (4 * n)) 4 B xs.length := by
      rw [hl]
      refine sep_last (fun z h₁ h₂ => hsep z (by omega) (by omega)) (by omega)
    have e := writeBytes_append s.mem B xs ((bytesAt s.mem (A + BitVec.ofNat 64 (4 * n)) 4).map (· ^^^ 0x6a))
      (by simp [hl, bytesAt_length]; omega)
    rw [hl] at e
    rw [u₄.mem, u₃.gpr, u₂.gpr, u₃.mem, u₂.mem, m₁, addr_word fx (by omega : n < n + 1),
      addr_word fy (by omega : n < n + 1), readW_writeBytes_sep _ _ hsep', writeW_xor, e,
      show 4 * (n + 1) = 4 * n + 4 by omega, VG.Proof.Hmac.X86_64.bytesAt_add, List.map_append]

/-- `K₀ ⊕ ipad ⊕ 0x6a = K₀ ⊕ opad`. -/
theorem xorPad_6a (k : List Byte) : (xorPad k ipad).map (· ^^^ 0x6a) = xorPad k opad := by
  simp only [xorPad, List.map_map]
  refine List.map_congr_left fun b _ => ?_
  simp only [Function.comp, BitVec.xor_assoc]
  rfl

/-! ## The compressions -/

theorem compBuf_ok {s₀ s : State} (hp : Pre s₀) {b : Reg} {x : BitVec 32} (hx : x = inn s₀ ∨ x = ou s₀)
    (hb : b = .ebx ∨ b = .esi) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hbx : s.gpr b = x)
    (hebp : s.gpr .ebp = scr s₀) (hsp : s.gpr .esp = esp₀ s₀) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s₀.rd → s'.wr = s₀.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨x.setWidth 64, 32⟩, ⟨scA s₀, 112⟩, argR s₀] s.mem s'.mem →
      stateAt s'.mem (x.setWidth 64) =
        compress (stateAt s.mem (x.setWidth 64)) (blockAt s.mem (x.setWidth 64 + 32)) → Q s') :
    WP isa (compressBuf b) s Q := by
  have fs := hp.scr_fit
  have fsp := hp.sp_fit
  obtain ⟨fx, dS, dA, dR, hm⟩ : x.toNat + 96 ≤ 2 ^ 32 ∧ Region.Disjoint ⟨x.setWidth 64, 96⟩ (scR s₀) ∧
      (argR s₀).Disjoint ⟨x.setWidth 64, 96⟩ ∧ (retR s₀).Disjoint ⟨x.setWidth 64, 96⟩ ∧
      (⟨x.setWidth 64, 96⟩ : Region) ∈ s₀.wr := by
    rcases hx with rfl | rfl
    · exact ⟨hp.in_fit, hp.i_s, hp.a_i, hp.ret_i, by simp [hp.wr]⟩
    · exact ⟨hp.ou_fit, hp.o_s, hp.a_o, hp.ret_o, by simp [hp.wr]⟩
  have hb' : b ≠ .eax := by rcases hb with rfl | rfl <;> decide
  have ain : ∀ d, 4 ≤ d → d + 4 ≤ 24 → InRegions s.wr (addr (esp₀ s₀) d) 4 :=
    fun d h₁ h₂ => ⟨argR s₀, by simp [hwr, hp.wr], hp.arg_in h₁ h₂⟩
  unfold compressBuf
  refine WP.seq (wp_store (a := addr (esp₀ s₀) 4) (by rw [ea_at, hsp]) (ain 4 (by omega) (by omega))
    fun s₁ u₁ => ?_)
  refine wp_store (a := addr (esp₀ s₀) 16) (by rw [ea_at, u₁.gpr, hsp])
    (by rw [u₁.wr]; exact ain 16 (by omega) (by omega)) fun s₂ u₂ => ?_
  refine wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ => WP.block_nil ?_
  have g₄ : ∀ r, r ≠ .eax → s₄.gpr r = s.gpr r := fun r h => by
    rw [u₄.other r h, u₃.other r h, u₂.gpr, u₁.gpr]
  have m₄ : s₄.mem = (s.mem.writeW (addr (esp₀ s₀) 4) x).writeW (addr (esp₀ s₀) 16) (scr s₀) := by
    rw [u₄.mem, u₃.mem, u₂.mem, u₁.gpr, hebp, u₁.mem, hbx]
  have rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, hrd]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hwr]
  have sp₄ : s₄.gpr .esp = esp₀ s₀ := by rw [g₄ _ (by decide), hsp]
  have eax₄ : s₄.gpr .eax = x + 32 := by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hbx]
  have h4 : s₄.mem.readW (addr (s₄.gpr .esp) 4) 32 = x := by
    rw [sp₄, m₄, readW_writeW_addr _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  have h16 : s₄.mem.readW (addr (s₄.gpr .esp) 16) 32 = scr s₀ := by
    rw [sp₄, m₄, Mem.readW_writeW_self32]
  have fr₄ : Frame [argR s₀] s.mem s₄.mem := by
    rw [m₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hp.arg_in (d := 4) (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (hp.arg_in (d := 16) (by omega) (by omega))
  have hbA : (x + 32).setWidth 64 = x.setWidth 64 + 32 := addr_eq (x := x) (k := 32) (by omega)
  have s32 : Region.Sub ⟨x.setWidth 64, 32⟩ ⟨x.setWidth 64, 96⟩ := sub32 _
  have s112 : Region.Sub ⟨scA s₀, 112⟩ (scR s₀) := Region.sub_prefix (by omega)
  have a16 : Region.Sub ⟨addr (esp₀ s₀) 4, 16⟩ (argR s₀) := Region.sub_prefix (by omega)
  have b64 : Region.Sub ⟨(x + 32).setWidth 64, 64⟩ ⟨x.setWidth 64, 96⟩ := by
    rw [hbA]; exact sub_offset (off := 32) (by omega) (by omega)
  refine compressAt_ok (st := x) (scr := scr s₀) (blk := x + 32) h4 h16 eax₄ (by rw [sp₄]; omega) (by omega)
    (by rw [show (x + 32).toNat = x.toNat + 32 by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by simp; omega)]; omega) (by omega)
    ((dS.sub_left s32).sub_right s112) ?_ ((dS.sub_left b64).sub_right s112)
    (by rw [sp₄]; exact (dA.sub_left a16).sub_right s32)
    (by rw [sp₄]; exact (hp.a_s.sub_left a16).sub_right s112)
    (by rw [sp₄]; exact dR.sub_right s32) (by rw [sp₄]; exact hp.ret_s.sub_right s112)
    (by rw [sp₄]; exact (dA.sub_left a16).symm.sub_left b64) ?_ ?_ ?_
  · rw [hbA]
    intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    bv_omega
  · rw [sp₄, rd₄, wr₄]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ hm, 32, hbA, by simp⟩
    · exact ⟨argR s₀, by simp [hp.wr], 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ hm, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp [hp.wr], 0, by simp, by simp⟩
  · rw [sp₄, wr₄]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, hm, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp [hp.wr], 0, by simp, by simp⟩
    · exact ⟨argR s₀, by simp [hp.wr], 0, by simp, by simp⟩
  · intro s' h₁ h₂ h₃ h₅ _ _ h₇
    rw [sp₄] at h₅
    refine hQ s' (h₁.trans rd₄) (h₂.trans wr₄) (fun r hr => by
      rw [h₃ r hr, g₄ r (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]) ?_ ?_
    · refine (fr₄.mono (by simp)).trans (h₅.sub ?_)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨argR s₀, by simp, a16⟩
    · have hst : stateAt s₄.mem (x.setWidth 64) = stateAt s.mem (x.setWidth 64) :=
        Proof.Sha256.Stream.stateAt_congr fun i hi =>
          frame_bytes fr₄ (R := ⟨x.setWidth 64, 32⟩) (by simpa using dA.symm.sub_left s32) (by simp) hi
      have hblk : blockAt s₄.mem (x.setWidth 64 + 32) = blockAt s.mem (x.setWidth 64 + 32) := by
        simp only [blockAt]
        apply Proof.Sha256.Stream.parseBlock_congr
        intro k hk
        exact frame_bytes fr₄ (R := ⟨x.setWidth 64 + 32, 64⟩)
          (by simpa using dA.symm.sub_left (sub_offset (off := 32) (by omega) (by omega))) (by simp) hk
      rw [h₇, hst, hbA, hblk]

/-! ## Epilogue -/

theorem epilogue_ok {s₀ s : State} (hp : Pre s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hebp : s.gpr .ebp = scr s₀) (hsp : s.gpr .esp = esp₀ s₀) (hsv : Saved s₀ s.mem) :
    WP isa (.block (.mov .eax (.reg .ebp) :: restore .eax)) s fun s' =>
      s'.mem = s.mem ∧ ∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r := by
  have sin : ∀ d, d + 4 ≤ 160 → InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
    fun d hd => ⟨scR s₀, by simp [hrd, hwr, hp.wr], hp.scr_in hd (by omega)⟩
  refine wp_mov fun s₃ u₃ => ?_
  have e₃ : s₃.gpr .eax = scr s₀ := by rw [u₃.gpr, hebp]
  have sin₃ : ∀ d, d + 4 ≤ 160 → InRegions (s₃.rd ++ s₃.wr) (addr (scr s₀) d) 4 :=
    fun d hd => by rw [u₃.rd, u₃.wr]; exact sin d hd
  have rs : ∀ p ∈ saved, s₃.mem.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1 := by
    intro p hp'; rw [u₃.mem]; exact hsv p hp'
  simp only [restore, saved, List.map_cons, List.map_nil]
  refine wp_movm (a := addr (scr s₀) 112) (by rw [ea_at, e₃]) (sin₃ 112 (by omega)) fun s₄ u₄ => ?_
  refine wp_movm (a := addr (scr s₀) 116) (by rw [ea_at, u₄.other _ (by decide), e₃])
    (by rw [u₄.rd, u₄.wr]; exact sin₃ 116 (by omega)) fun s₅ u₅ => ?_
  refine wp_movm (a := addr (scr s₀) 120) (by rw [ea_at, u₅.other _ (by decide), u₄.other _ (by decide), e₃])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact sin₃ 120 (by omega)) fun s₆ u₆ => ?_
  refine wp_movm (a := addr (scr s₀) 124)
    (by rw [ea_at, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), e₃])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact sin₃ 124 (by omega)) fun s₇ u₇ => WP.block_nil ?_
  refine ⟨by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem], fun r hr => ?_⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
    exact rs (.ebx, 112) (by simp [saved])
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem]
    exact rs (.esi, 116) (by simp [saved])
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem]
    exact rs (.edi, 120) (by simp [saved])
  · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem]
    exact rs (.ebp, 124) (by simp [saved])
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), hsp]

/-! ## Correctness -/

/-- Everything we may write. -/
abbrev allR (s₀ : State) : List Region := [inR s₀, ouR s₀, scR s₀, argR s₀]

theorem callee_ne_eax {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .eax := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Hmac.initSha256X86.post s₀ s' := by
  have hkl := hp.kl_le
  have fi := hp.in_fit
  have fo := hp.ou_fit
  have fs := hp.scr_fit
  unfold init
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, z₁⟩ => ?_)
  -- The key.
  refine WP.seq (WP.mono (Q := Buf s₀ (kl s₀)) ?_ fun s₂ h₂ => ?_)
  · refine WP.ite (decide (kl s₀ = 0)) (by simp [eval, z₁]) (fun hb => WP.block_nil ?_)
      (fun hb => key_loop_ok hp h₁ ?_)
    · rw [of_decide_eq_true hb]; exact h₁.toBuf
    · have := of_decide_eq_false hb; omega
  -- The padding.
  refine WP.seq (wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_movi fun s₅ u₅ =>
    wp_cmp fun s₆ f₆ _ z₆ => WP.block_nil ?_)
  have k₆ : ∀ r, r ≠ .eax → r ≠ .ecx → s₆.gpr r = s₂.gpr r := fun r h h' => by
    rw [f₆.gpr, u₅.other r h', u₄.other r h, u₃.other r h]
  have eax₆ : s₆.gpr .eax = inn s₀ + 96 := by
    rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, h₂.ebx]
  have hP : Pad s₀ (kl s₀) s₆ :=
    ⟨⟨h₂.j_le, by rw [f₆.rd, u₅.rd, u₄.rd, u₃.rd, h₂.rd], by rw [f₆.wr, u₅.wr, u₄.wr, u₃.wr, h₂.wr],
      by rw [k₆ _ (by decide) (by decide), h₂.ebx], by rw [k₆ _ (by decide) (by decide), h₂.esi],
      by rw [k₆ _ (by decide) (by decide), h₂.ebp], by rw [k₆ _ (by decide) (by decide), h₂.esp],
      by rw [k₆ _ (by decide) (by decide), h₂.edx], by rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem]; exact h₂.mem⟩,
      eax₆, by rw [f₆.gpr, u₅.gpr]⟩
  have hz : s₆.zf = some (decide (kl s₀ = 64)) := by
    rw [z₆, ← f₆.gpr, k₆ _ (by decide) (by decide), h₂.edx, eax₆, cmp_end _ hkl]
  refine WP.seq (WP.mono (Q := Buf s₀ 64) ?_ fun s₇ h₇ => ?_)
  · refine WP.ite (decide (kl s₀ = 64)) (by simp [eval, hz]) (fun hb => WP.block_nil ?_)
      (fun hb => pad_loop_ok hp hP ?_)
    · rw [← of_decide_eq_true hb]; exact hP.toBuf
    · have := of_decide_eq_false hb; omega
  -- The outer buffer.
  have hbufI : bytesAt s₇.mem (inA s₀ + 32) 64 = xorPad (K0 s₀) ipad := by
    rw [h₇.mem.buf, List.take_of_length_le (by rw [K0_length s₀ hp])]; rfl
  refine WP.seq ?_
  rw [← List.append_nil ((List.range 16).flatMap opadWord)]
  refine xorWords_ok 16 [] s₇ _ h₇.ebx h₇.esi (by omega) (by omega)
    (fun k hk => ⟨inR s₀, by simp [h₇.rd, h₇.wr, hp.wr], hp.in_in (by omega) (by omega)⟩)
    (fun k hk => ⟨ouR s₀, by simp [h₇.wr, hp.wr], hp.ou_in (by omega) (by omega)⟩)
    (hp.i_o.sep (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega)))
    fun s₈ g₈ rd₈ wr₈ m₈ => WP.block_nil ?_
  set ob := (bytesAt s₇.mem (inA s₀ + BitVec.ofNat 64 32) (4 * 16)).map (· ^^^ (0x6a : Byte)) with hob
  have hobl : ob.length = 64 := by simp [ob, bytesAt_length]
  have hob' : ob = xorPad (K0 s₀) opad := by
    rw [hob, show 4 * 16 = 64 from rfl, show inA s₀ + BitVec.ofNat 64 32 = inA s₀ + 32 from rfl, hbufI,
      xorPad_6a]
  let bO : Region := ⟨ouA s₀ + BitVec.ofNat 64 32, 64⟩
  have sO : Region.Sub bO (ouR s₀) := sub_offset (by omega) (by omega)
  have F₈ : Frame [bO] s₇.mem s₈.mem := by
    rw [m₈]; exact writeBytes_frame _ _ _ (by rw [hobl]; exact Region.contains_self _ _)
  have bOd : ∀ R : Region, R.Disjoint (ouR s₀) → ∀ r ∈ [bO], R.Disjoint r := fun R h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right sO
  have stI₈ : stateAt s₈.mem (inA s₀) = H0 := by
    rw [← h₇.mem.stI]
    exact Proof.Sha256.Stream.stateAt_congr fun i hi =>
      frame_bytes F₈ (R := ⟨inA s₀, 32⟩) (bOd _ (hp.i_o.sub_left (sub32 _))) (by simp) hi
  have bI₈ : bytesAt s₈.mem (inA s₀ + 32) 64 = xorPad (K0 s₀) ipad := by
    rw [← hbufI]
    exact Proof.Sha256.Stream.bytesAt_congr fun i hi =>
      frame_bytes F₈ (R := ⟨inA s₀ + 32, 64⟩)
        (bOd _ (hp.i_o.sub_left (sub_offset (off := 32) (by omega) (by omega)))) (by simp) hi
  have stO₈ : stateAt s₈.mem (ouA s₀) = H0 := by
    rw [← h₇.mem.stO]
    refine Proof.Sha256.Stream.stateAt_congr fun i hi => frame_bytes F₈ (R := ⟨ouA s₀, 32⟩) ?_ (by simp) hi
    simp only [List.mem_singleton]; rintro r rfl
    intro a h₁ h₂
    simp only [Region.Contains, bO] at h₁ h₂
    bv_omega
  have bO₈ : bytesAt s₈.mem (ouA s₀ + 32) 64 = xorPad (K0 s₀) opad := by
    rw [m₈, ← hob']
    have := VG.Proof.Hmac.X86_64.bytesAt_writeBytes_self s₇.mem (ouA s₀ + BitVec.ofNat 64 32) ob (by omega)
    rw [hobl] at this
    exact this
  have sv₈ : Saved s₀ s₈.mem := saved_frame h₇.mem.saved F₈ fun d h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact save_disj hp (hp.o_s.sub_left sO) d h₁ h₂
  have f₈ : Frame [inR s₀, ouR s₀, scR s₀] s₀.mem s₈.mem :=
    h₇.mem.frame.trans (F₈.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨ouR s₀, by simp, sO⟩)
  -- The inner block.
  refine WP.seq (compBuf_ok hp (x := inn s₀) (.inl rfl) (b := .ebx) (.inl rfl) (by rw [rd₈, h₇.rd])
    (by rw [wr₈, h₇.wr]) (by rw [g₈ _ (by decide), h₇.ebx]) (by rw [g₈ _ (by decide), h₇.ebp])
    (by rw [g₈ _ (by decide), h₇.esp]) fun s₉ rd₉ wr₉ cs₉ fr₉ st₉ => ?_)
  have hI₉ : Repr s₉.mem (inA s₀) (xorPad (K0 s₀) ipad) :=
    VG.Proof.Hmac.X86_64.Init.repr_block stI₈ bI₈ (by simp [xorPad, K0_length s₀ hp]) st₉
  have dO : ∀ r ∈ [(⟨inA s₀, 32⟩ : Region), ⟨scA s₀, 112⟩, argR s₀], Region.Disjoint (ouR s₀) r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o.symm.sub_right (sub32 _)
    · exact hp.o_s.sub_right (Region.sub_prefix (by omega))
    · exact hp.a_o.symm
  have stO₉ : stateAt s₉.mem (ouA s₀) = H0 := by
    rw [← stO₈]
    exact Proof.Sha256.Stream.stateAt_congr fun i hi =>
      frame_bytes fr₉ (R := ⟨ouA s₀, 32⟩) (fun r hr => (dO r hr).sub_left (sub32 _)) (by simp) hi
  have bO₉ : bytesAt s₉.mem (ouA s₀ + 32) 64 = xorPad (K0 s₀) opad := by
    rw [← bO₈]
    exact Proof.Sha256.Stream.bytesAt_congr fun i hi =>
      frame_bytes fr₉ (R := ⟨ouA s₀ + 32, 64⟩)
        (fun r hr => (dO r hr).sub_left (sub_offset (off := 32) (by omega) (by omega))) (by simp) hi
  have sv₉ : Saved s₀ s₉.mem := saved_frame sv₈ fr₉ fun d h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact save_disj hp (hp.i_s.sub_left (sub32 _)) d h₁ h₂
    · exact save_disj112 hp d h₁ h₂
    · exact save_disj hp hp.a_s d h₁ h₂
  have f₉ : Frame (allR s₀) s₀.mem s₉.mem := (f₈.mono (by simp)).trans (fr₉.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨inR s₀, by simp, sub32 _⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨argR s₀, by simp, fun _ h => h⟩)
  have cs₉' : ∀ r ∈ calleeSaved, s₉.gpr r = s₇.gpr r := fun r hr => by
    rw [cs₉ r hr, g₈ r (callee_ne_eax hr)]
  -- The outer block.
  refine WP.seq (compBuf_ok hp (x := ou s₀) (.inr rfl) (b := .esi) (.inr rfl) rd₉ wr₉
    (by rw [cs₉' _ (by decide), h₇.esi]) (by rw [cs₉' _ (by decide), h₇.ebp])
    (by rw [cs₉' _ (by decide), h₇.esp]) fun s₁₀ rd₁₀ wr₁₀ cs₁₀ fr₁₀ st₁₀ => ?_)
  have hO : Repr s₁₀.mem (ouA s₀) (xorPad (K0 s₀) opad) :=
    VG.Proof.Hmac.X86_64.Init.repr_block stO₉ bO₉ (by simp [xorPad, K0_length s₀ hp]) st₁₀
  have hI : Repr s₁₀.mem (inA s₀) (xorPad (K0 s₀) ipad) := by
    refine repr_congr (fun i hi => frame_bytes fr₁₀ (R := inR s₀) ?_ (by simp) hi) hI₉
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o.sub_right (sub32 _)
    · exact hp.i_s.sub_right (Region.sub_prefix (by omega))
    · exact hp.a_i.symm
  have sv₁₀ : Saved s₀ s₁₀.mem := saved_frame sv₉ fr₁₀ fun d h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact save_disj hp (hp.o_s.sub_left (sub32 _)) d h₁ h₂
    · exact save_disj112 hp d h₁ h₂
    · exact save_disj hp hp.a_s d h₁ h₂
  have f₁₀ : Frame (allR s₀) s₀.mem s₁₀.mem := f₉.trans (fr₁₀.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ouR s₀, by simp, sub32 _⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨argR s₀, by simp, fun _ h => h⟩)
  have cs₁₀' : ∀ r ∈ calleeSaved, s₁₀.gpr r = s₇.gpr r := fun r hr => by rw [cs₁₀ r hr, cs₉' r hr]
  -- Epilogue.
  refine WP.mono (epilogue_ok hp rd₁₀ wr₁₀ (by rw [cs₁₀' _ (by decide), h₇.ebp])
    (by rw [cs₁₀' _ (by decide), h₇.esp]) sv₁₀) fun s' ⟨m', cs'⟩ => ⟨⟨cs', ?_⟩, ?_⟩
  · rw [m']
    refine f₁₀.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [allR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hp.ret_i, hp.ret_o, hp.ret_s, ret_a hp]
  · show Repr s'.mem (inA s₀) (xorPad (blockKey sha256 (bytesAt s₀.mem (kA s₀) (kl s₀))) ipad) ∧
      Repr s'.mem (ouA s₀) (xorPad (blockKey sha256 (bytesAt s₀.mem (kA s₀) (kl s₀))) opad)
    rw [blockKey_eq hp, m']
    exact ⟨hI, hO⟩

/-! ## Constant time -/

/-- The initial taint: `esp + 4` is the base of the (public) arguments, whose
words at offsets 0, 4 and 16 are the base addresses of `inner`, `outer` and
`scratch`. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [96, 96, 160, 20], bases := [(.esp, 3, 4)],
    slots := [(3, 0, 20)], wbases := [(3, 0, 0), (3, 4, 1), (3, 16, 2)] }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hi := hp.in_fit; have ho := hp.ou_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, ?_, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.i_o, hp.i_s, hp.a_i.symm⟩, ⟨hp.o_s, hp.a_o.symm⟩, hp.a_s.symm, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · simp only [addr_toNat]; omega
    · simp only [addr_toNat]; omega
    · simp only [addr_toNat]; omega
    · simp only; rw [addr_eq (by omega), BitVec.toNat_add, addr_toNat, BitVec.toNat_ofNat]; omega
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'
    subst hp'
    simp [VG.X86.Taint.region, hp.wr]
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (esp₀ s) 4 + BitVec.ofNat 64 0) 32) 0 = inA s
      simp [addr, inn, arg, argAddr]
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (esp₀ s) 4 + BitVec.ofNat 64 4) 32) 0 = ouA s
      rw [VG.Proof.Sha256.X86.Stream.Finalize.argWord_eq hs (k := 4) (by omega)]
      simp [addr, ou, arg]
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (esp₀ s) 4 + BitVec.ofNat 64 16) 32) 0 = scA s
      rw [VG.Proof.Sha256.X86.Stream.Finalize.argWord_eq hs (k := 16) (by omega)]
      simp [addr, scr, arg]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Hmac.initSha256X86.pre s₁) (h₂ : Proof.Hmac.initSha256X86.pre s₂)
    (hpub : Proof.Hmac.initSha256X86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂, ?_, ?_,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [inR, ouR, scR, argR, inA, ouA, scA, inn, ou, scr, esp₀, ha 0 (by omega), ha 1 (by omega),
      ha 4 (by omega), hesp]
  · intro sl hsl
    simp only [τ₀, List.mem_singleton] at hsl
    subst hsl; decide
  · intro sl hsl k _ hk
    simp only [τ₀, List.mem_singleton] at hsl
    subst hsl
    simp only [Nat.zero_add] at hk
    simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp₁.wr, hp₂.wr]
    show s₁.mem (addr (esp₀ s₁) 4 + BitVec.ofNat 64 k) = s₂.mem (addr (esp₀ s₂) 4 + BitVec.ofNat 64 k)
    rw [VG.Proof.Sha256.X86.Stream.Finalize.argWord_eq hp₁.sp_fit hk,
      VG.Proof.Sha256.X86.Stream.Finalize.argWord_eq hp₂.sp_fit hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

/-- Memory holding the arguments `0x1000, 0x1100, 0x1200, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x11 else if a = 0x400D then 0x12 else
  if a = 0x4015 then 0x30 else 0

/-- A state satisfying the precondition (with an empty key). -/
def sat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x1200, 0⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x1100, 96⟩, ⟨0x3000, 160⟩, ⟨0x4004, 20⟩]

theorem init_correct (s : State) (hs : Proof.Hmac.initSha256X86.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ Proof.Hmac.initSha256X86.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, h⟩

theorem init_ct : ConstantTime isa Proof.Hmac.initSha256X86.pre Proof.Hmac.initSha256X86.pub init :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

/-- `initSha256X86` with the 608 bytes of scratch of the shared contract
(sized for the x86-64 AVX2 compression function), of which the code uses 160. -/
def initWide : Contract isa :=
  { Proof.Hmac.initSha256X86 with
    pre := fun s =>
      let inner : Region := ⟨(arg s 0).setWidth 64, 96⟩
      let outer : Region := ⟨(arg s 1).setWidth 64, 96⟩
      let key : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 608⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      (arg s 3).toNat ≤ 64 ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch, args] ∧
      inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
      args.Disjoint inner ∧ args.Disjoint outer ∧ args.Disjoint scratch ∧
      key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧ key.Disjoint args ∧
      ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 96 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 96 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 608 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

/-- The regions `initSha256X86` lets the code write. -/
def narrowWr (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 96⟩, ⟨(arg s 1).setWidth 64, 96⟩, ⟨(arg s 4).setWidth 64, 160⟩,
    ⟨argAddr s 0, 20⟩]

/-- Rewrites the contracts at a narrowed state (`arg` does not unfold
cheaply). -/
local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Hmac.initSha256X86, VG.Proof.Hmac.X86.Init.initWide, VG.Proof.Hmac.X86.Init.narrowWr, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions,
    VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem, VG.X86.State.withRegions_rd,
    VG.X86.State.withRegions_wr] $(loc)?)

theorem initWide_pre (s : State) (h : initWide.pre s) :
    Proof.Hmac.initSha256X86.pre (s.withRegions s.rd (narrowWr s)) := by
  obtain ⟨h₁, h₂, _, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉,
    h₂₀, h₂₁⟩ := h
  narrow
  exact ⟨h₁, h₂, trivial, h₄, h₅.sub_right (Region.sub_of_ble rfl),
    h₆.sub_right (Region.sub_of_ble rfl), h₇, h₈, h₉.sub_right (Region.sub_of_ble rfl), h₁₀, h₁₁,
    h₁₂.sub_right (Region.sub_of_ble rfl), h₁₃, h₁₄, h₁₅, h₁₆.sub_right (Region.sub_of_ble rfl), h₁₇,
    h₁₈, h₁₉, Region.end_le_of_ble rfl h₂₀, h₂₁⟩

/-- A state satisfying `initWide.pre`. -/
def wideSat : State :=
  { sat with wr := [⟨0x1000, 96⟩, ⟨0x1100, 96⟩, ⟨0x3000, 608⟩, ⟨0x4004, 20⟩] }

theorem initWide_implies : initWide.Implies (Spec.Hmac.initSha256Contract X86.abi) := by
  have a0 : arg wideSat 0 = 0x1000 := by decide
  have a1 : arg wideSat 1 = 0x1100 := by decide
  have a2 : arg wideSat 2 = 0x1200 := by decide
  have a3 : arg wideSat 3 = 0 := by decide
  have a4 : arg wideSat 4 = 0x3000 := by decide
  have e : argAddr wideSat 0 = 0x4004 := by decide
  have esp : wideSat.gpr .esp = 0x4000 := rfl
  sig_implies [Spec.Hmac.initSha256Contract, Spec.Hmac.initSha256Sig, initWide,
    Proof.Hmac.initSha256X86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp] using wideSat

/-- The proof is written against `initSha256X86`, widened to the shared
contract's scratch. -/
theorem init_verified :
    Verified X86.target Impl.Hmac.X86.init (Spec.Hmac.initSha256Contract X86.abi) :=
  have hsat := initWide_implies.sat_left
  (Verified.widen (Verified.of_correct init_correct init_ct
    (.refl (hsat.elim fun s hs => ⟨_, initWide_pre s hs⟩)))
    narrowWr initWide_pre
    (fun _ h => by
      obtain ⟨_, _, h₃, _⟩ := h
      rw [h₃]
      exact .cons (Region.prefix_of_ble rfl) (.cons (Region.prefix_of_ble rfl)
        (.cons (Region.prefix_of_ble rfl) (.cons (Region.prefix_of_ble rfl) .nil))))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat).of_implies initWide_implies

end VG.Proof.Hmac.X86.Init
