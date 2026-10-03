import VerifiedGarbage.Proof.Argon2.X86.Derive.Correct
import VerifiedGarbage.Proof.Argon2.X86.HPrime.CallsCT

/-!
# Argon2 on x86 (32-bit): the derivation's taint analysis

The body reads its arguments through `ebp`, which the taint analysis only
knows to be public through `esp`. So its pieces are analysed from states
with more permissions (`RelCT.taintW`, by `Exec.widen`): the locals and the
saved registers as one writable region, the memory matrix, `scratch`, the
output, and the arguments (`wide`). `τB sl` makes `esp` and `ebp`, the
arguments and the locals' slots `sl` public, and knows which arguments are
the base addresses of the matrix, `scratch` and the output; `agreeB` gives it
from what two runs of the body are known to share.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Blake2 (bytesAt)

/-- Two runs leak the same trace if, from states with more permissions, the
taint analysis proves it. -/
theorem RelCT.taintW {P : State → State → Prop} {c : Prog isa} (τ : VG.X86.Taint.T)
    (hp : ∀ s₁ s₂, P s₁ s₂ → ∃ w₁ w₂, Covers s₁.wr w₁ ∧ Covers s₂.wr w₂ ∧
      VG.X86.Taint.Agree τ (s₁.withRegions s₁.rd w₁) (s₂.withRegions s₂.rd w₂))
    {hc : VG.Taint.Hint VG.X86.Taint.T} (h : (VG.Taint.check taint τ c hc).isSome = true) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨w₁, w₂, c₁, c₂, ag⟩ := hp _ _ hP
  have e₁' := Exec.widen e₁ (Covers.append (Covers.refl _) c₁) c₁
  have e₂' := Exec.widen e₂ (Covers.append (Covers.refl _) c₂) c₂
  exact ⟨((VG.RelCT.taint (A := taint) (P := fun a b => a = s₁.withRegions s₁.rd w₁ ∧
    b = s₂.withRegions s₂.rd w₂) τ (fun _ _ ⟨h₁, h₂⟩ => by subst h₁ h₂; exact ag) h) _ _ _ _ _ _
    ⟨rfl, rfl⟩ e₁' e₂').1, trivial⟩

/-- As `RelCT.taintW`, with what each run satisfies by correctness. -/
theorem rel_taintW {F₁ F₂ G₁ G₂ : State → Prop} {R : State → State → Prop} {c : Prog isa} (τ : VG.X86.Taint.T)
    (hp : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ → R s₁ s₂ → ∃ w₁ w₂, Covers s₁.wr w₁ ∧ Covers s₂.wr w₂ ∧
      VG.X86.Taint.Agree τ (s₁.withRegions s₁.rd w₁) (s₂.withRegions s₂.rd w₂))
    (hc : ∃ hc, (VG.Taint.check taint τ c hc).isSome = true)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ ∧ R s₁ s₂) c fun t₁ t₂ => G₁ t₁ ∧ G₂ t₂ := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taintW (P := fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ ∧ R s₁ s₂) τ
    (fun s₁ s₂ h => hp s₁ s₂ h.1 h.2.1 h.2.2) hc).wp fun s₁ s₂ h => ⟨hw₁ s₁ h.1, hw₂ s₂ h.2.1⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## The regions -/

/-- The regions the taint analysis of the body knows: the locals and saved
registers, the memory matrix, `scratch`, the output and the arguments. -/
def wide (s₀ : State) : List Region :=
  [⟨(E s₀).setWidth 64, 160⟩, memR s₀, scrR s₀, outR s₀, argR s₀]

/-- The taint state of the body, with the locals' slots `sl` and the registers
`rs` public. -/
def τB (sl : List (Nat × Nat × Nat)) (rs : List Reg := []) : VG.X86.Taint.T :=
  { regs := .ofList (.esp :: .ebp :: rs), flags := false, lens := [160, 1024, 16384, 0, 72],
    bases := [(.ebp, 4, 164), (.ebp, 0, 0), (.esp, 4, 164), (.esp, 0, 0)], slots := sl ++ [(4, 0, 72)],
    wbases := [(4, 52, 1), (4, 60, 2), (4, 64, 3)] }


section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The writable regions of the body: frames within the 160 bytes above `E`, and the caller's. -/
theorem entry_wr_cases {r : Region} (hr : r ∈ (entry s₀).wr) : r ∈ s₀.wr ∨
    ∃ x : BitVec 32, ∃ n, r = ⟨x.setWidth 64, n⟩ ∧ (E s₀).toNat ≤ x.toNat ∧ x.toNat + n ≤ (E s₀).toNat + 160 := by
  have hlo : 244 ≤ (s₀.gpr .esp).toNat := hp.esp_lo
  have hE0 : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE := E_nat hp
  have n₁ := pushed_esp_nat (rs := [.ebp]) (s := s₀) (by simp only [List.length_singleton]; omega)
  have n₂ := pushed_esp_nat (rs := [.edi]) (s := pushed [.ebp] s₀)
    (by simp only [List.length_singleton] at n₁ ⊢; omega)
  have n₃ := pushed_esp_nat (rs := [.esi]) (s := pushed [.edi] (pushed [.ebp] s₀))
    (by simp only [List.length_singleton] at n₁ n₂ ⊢; omega)
  have n₄ := pushed_esp_nat (rs := [.ebx]) (s := pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀)))
    (by simp only [List.length_singleton] at n₁ n₂ n₃ ⊢; omega)
  simp only [List.length_singleton, Nat.mul_one] at n₁ n₂ n₃ n₄
  have w : ∀ (x : BitVec 32) (n : Nat), n ≤ x.toNat → (E s₀).toNat ≤ x.toNat - n → x.toNat ≤ (E s₀).toNat + 160 →
      (E s₀).toNat ≤ (x - BitVec.ofNat 32 n).toNat ∧ (x - BitVec.ofNat 32 n).toNat + n ≤ (E s₀).toNat + 160 :=
    fun x n h₁ h₂ h₃ => by rw [sub_nat h₁]; omega
  simp only [entry, pushed_wr, List.mem_cons, List.length_singleton, List.length_replicate, Nat.mul_one,
    Nat.reduceMul] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | hr
  · exact .inr ⟨_, _, rfl, w _ _ (by omega) (by omega) (by omega)⟩
  · exact .inr ⟨_, _, rfl, w _ _ (by omega) (by omega) (by omega)⟩
  · exact .inr ⟨_, _, rfl, w _ _ (by omega) (by omega) (by omega)⟩
  · exact .inr ⟨_, _, rfl, w _ _ (by omega) (by omega) (by omega)⟩
  · exact .inr ⟨_, _, rfl, w _ _ (by omega) (by omega) (by omega)⟩
  · exact .inl hr

theorem covers_wide : Covers (entry s₀).wr (wide s₀) := by
  have hE := E_hi hp
  refine Covers.of_sub fun r hr => ?_
  rcases entry_wr_cases hp hr with hr | ⟨x, n, rfl, h₁, h₂⟩
  · rw [hp.wr] at hr
    exact ⟨r, by simp only [wide, List.mem_cons] at hr ⊢; simp at hr; rcases hr with h | h | h <;> simp [h],
      0, by simp, by simp⟩
  · refine ⟨⟨(E s₀).setWidth 64, 160⟩, by simp [wide], x.toNat - (E s₀).toNat, ?_, by simp only; omega⟩
    show x.setWidth 64 = (E s₀).setWidth 64 + BitVec.ofNat 64 (x.toNat - (E s₀).toNat)
    rw [← HPrime.setWidth_add (by omega)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [add_nat (by omega)]; omega

end

/-- What two runs share: the stack pointer and the arguments. -/
def Pub2 (s₀₁ s₀₂ : State) : Prop := E0 s₀₁ = E0 s₀₂ ∧ ∀ i < 18, arg s₀₁ i = arg s₀₂ i

theorem Pub2.E {s₀₁ s₀₂ : State} (h : Pub2 s₀₁ s₀₂) : E s₀₁ = E s₀₂ := by
  show E0 s₀₁ - BitVec.ofNat 32 160 = E0 s₀₂ - BitVec.ofNat 32 160
  rw [h.1]

theorem Pub2.wide_eq {s₀₁ s₀₂ : State} (h : Pub2 s₀₁ s₀₂) : wide s₀₁ = wide s₀₂ := by
  have e : s₀₁.gpr .esp = s₀₂.gpr .esp := h.1
  unfold wide
  rw [h.E, show memR s₀₁ = memR s₀₂ by simp only [memR, memP, blocksN, h.2 13 (by decide), h.2 14 (by decide)],
    show scrR s₀₁ = scrR s₀₂ by simp only [scrR, scrP, h.2 15 (by decide)],
    show outR s₀₁ = outR s₀₂ by simp only [outR, outP, outL, h.2 16 (by decide), h.2 17 (by decide)],
    show argR s₀₁ = argR s₀₂ by simp only [argR, argAddr, e]]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- Word `i` of the arguments, in the widened regions' terms. -/
theorem arg_byteAddr {i : Nat} (hi : i < 18) :
    argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) = argAddr s₀ i := by
  have := hp.esp_hi
  have := hp.esp_lo
  have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  simp only [argAddr]
  rw [← HPrime.setWidth_add (by rw [add_nat (by omega)]; omega), BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem wf_wide (sl : List (Nat × Nat × Nat)) (rs : List Reg) {s : State} (h : Inv s₀ s) :
    VG.X86.Taint.Wf (τB sl rs) (s.withRegions s.rd (wide s₀)) := by
  have hlo := hp.esp_lo
  have hhi := hp.esp_hi
  have hE := E_nat hp
  have hE0 : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have b1 := blocks_pos hp
  have hm := hp.mem_fits
  have hs := hp.scr_fits
  have ho := hp.out_fits
  have aR : (argR s₀) = ⟨(E0 s₀ + BitVec.ofNat 32 4).setWidth 64, 72⟩ := rfl
  have a4 : (E0 s₀ + BitVec.ofNat 32 4).toNat = (E0 s₀).toNat + 4 := add_nat (by omega)
  have locS : Region.Sub ⟨(E s₀).setWidth 64, 160⟩ (stkR s₀) := by
    simpa using frame_stk hp (d := 0) (n := 160) (by decide)
  refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp' => ?_, fun p hp' => ?_, fun h0 => absurd h0 (Nat.lt_irrefl 0),
    fun _ h' => (List.not_mem_nil h').elim, by simp; exact (s.gpr .esp).isLt,
    fun _ h' => by simp [τB, VG.X86.Taint.frameList] at h', fun h0 => absurd h0 (Nat.lt_irrefl 0)⟩
  · simp only [State.withRegions_wr, wide, τB]
    refine .cons (by simp) (.cons ?_ (.cons (by simp) (.cons (by simp) (.cons (by simp) .nil))))
    show 1024 ≤ blocksN s₀ * 1024; omega
  · simp only [State.withRegions_wr, wide]
    have d1 := (hp.stk_all (memR s₀) (by simp)).sub_left locS
    have d2 := (hp.stk_all (scrR s₀) (by simp)).sub_left locS
    have d3 := (hp.stk_all (outR s₀) (by simp)).sub_left locS
    have d4 : Region.Disjoint ⟨(E s₀).setWidth 64, 160⟩ (argR s₀) := by
      rw [aR]; exact disj32 (.inl (by rw [a4]; omega)) (by omega) (by rw [a4]; omega)
    have r1 := hp.ro_w (argR s₀) (by simp) (memR s₀) (by simp)
    have r2 := hp.ro_w (argR s₀) (by simp) (scrR s₀) (by simp)
    have r3 := hp.ro_w (argR s₀) (by simp) (outR s₀) (by simp)
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons (fun _ h => (List.not_mem_nil h).elim) .nil))))
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [d1, d2, d3, d4]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.mem_scr, hp.mem_out, r1.symm]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hp.scr_out, r2.symm]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact r3.symm
  · simp only [State.withRegions_wr, wide, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl) <;> simp only [toNat_w]
    · omega
    · exact hm
    · exact hs
    · exact ho
    · show ((E0 s₀ + BitVec.ofNat 32 4).setWidth 64).toNat + 72 ≤ 2 ^ 32
      rw [toNat_w, a4]; omega
  · simp only [τB, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl
    · show addr (s.gpr .ebp) 164 = argAddr s₀ 0
      rw [h.ebp]; exact arg_addr hp (i := 0) (by decide)
    · show addr (s.gpr .ebp) 0 = (E s₀).setWidth 64
      rw [h.ebp]; simp [addr]
    · show addr (s.gpr .esp) 164 = argAddr s₀ 0
      rw [h.esp]; exact arg_addr hp (i := 0) (by decide)
    · show addr (s.gpr .esp) 0 = (E s₀).setWidth 64
      rw [h.esp]; simp [addr]
  · simp only [τB, List.mem_cons, List.not_mem_nil, or_false] at hp'
    have wb : ∀ i, i < 18 → (s.withRegions s.rd (wide s₀)).mem.readW
        (VG.X86.Taint.byteAddr (s.withRegions s.rd (wide s₀)) 4 (4 * i)) 32 = arg s₀ i := fun i hi => by
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, State.withRegions_wr, State.withRegions_mem, wide,
        List.getD_cons_succ, List.getD_cons_zero, argR]
      rw [arg_byteAddr hp hi, ← arg_addr hp hi]
      exact h.arg hp hi
    rcases hp' with rfl | rfl | rfl
    · refine ⟨by show 52 + 4 ≤ 72; decide, ?_⟩
      show addr ((s.withRegions s.rd (wide s₀)).mem.readW
        (VG.X86.Taint.byteAddr (s.withRegions s.rd (wide s₀)) 4 (4 * 13)) 32) 0 = (memP s₀).setWidth 64
      rw [wb 13 (by decide)]; simp [addr]
    · refine ⟨by show 60 + 4 ≤ 72; decide, ?_⟩
      show addr ((s.withRegions s.rd (wide s₀)).mem.readW
        (VG.X86.Taint.byteAddr (s.withRegions s.rd (wide s₀)) 4 (4 * 15)) 32) 0 = (scrP s₀).setWidth 64
      rw [wb 15 (by decide)]; simp [addr]
    · refine ⟨by show 64 + 4 ≤ 72; decide, ?_⟩
      show addr ((s.withRegions s.rd (wide s₀)).mem.readW
        (VG.X86.Taint.byteAddr (s.withRegions s.rd (wide s₀)) 4 (4 * 16)) 32) 0 = (outP s₀).setWidth 64
      rw [wb 16 (by decide)]; simp [addr]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A byte of the locals, from its word. -/
theorem loc_byte (m : Mem) {k : Nat} (hk : k < 160) :
    m ((E s₀).setWidth 64 + BitVec.ofNat 64 k) =
      (m.readW (addr (E s₀) (4 * (k / 4))) 32).extractLsb' (8 * (k % 4)) 8 := by
  have := E_hi hp
  rw [addr_eq (by omega), ← Mem.readW_byte m _ (Nat.mod_lt _ (by decide)), BitVec.add_assoc,
    BitVec.ofNat_add_ofNat, Nat.div_add_mod]

/-- A byte of the arguments, from its word. -/
theorem arg_byte {s : State} (h : Inv s₀ s) {k : Nat} (hk : k < 72) :
    s.mem (argAddr s₀ 0 + BitVec.ofNat 64 k) = (arg s₀ (k / 4)).extractLsb' (8 * (k % 4)) 8 := by
  rw [show argAddr s₀ 0 + BitVec.ofNat 64 k = argAddr s₀ 0 + BitVec.ofNat 64 (4 * (k / 4)) +
      BitVec.ofNat 64 (k % 4) by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod],
    Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), arg_byteAddr hp (by omega), ← arg_addr hp (by omega),
    h.arg hp (by omega)]

end

/-- The taint analysis's knowledge of the body, from what two runs share and
the values of the locals' slots `sl` in both. -/
theorem agreeB {s₀₁ s₀₂ s₁ s₂ : State} (hp₁ : DPre s₀₁) (hp₂ : DPre s₀₂) (pb : Pub2 s₀₁ s₀₂)
    (h₁ : Inv s₀₁ s₁) (h₂ : Inv s₀₂ s₂) (sl : List (Nat × Nat × Nat)) (rs : List Reg)
    (hrs : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hok : VG.X86.Taint.SlotsOk (τB sl rs))
    (hsl : ∀ x ∈ sl, x.1 = 0 ∧ ∀ k, x.2.1 ≤ k → k < x.2.1 + x.2.2 →
      lw s₀₁ s₁ (4 * (k / 4)) = lw s₀₂ s₂ (4 * (k / 4))) :
    ∃ w₁ w₂, Covers s₁.wr w₁ ∧ Covers s₂.wr w₂ ∧
      VG.X86.Taint.Agree (τB sl rs) (s₁.withRegions s₁.rd w₁) (s₂.withRegions s₂.rd w₂) := by
  refine ⟨wide s₀₁, wide s₀₂, by rw [h₁.wr]; exact covers_wide hp₁, by rw [h₂.wr]; exact covers_wide hp₂,
    ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => pb.wide_eq, wf_wide hp₁ sl rs h₁, wf_wide hp₂ sl rs h₂, hok,
      fun x hx k hk₁ hk₂ => ?_, fun h0 => absurd h0 (Nat.lt_irrefl 0),
      fun _ _ h0 => absurd h0 (Nat.not_lt_zero _)⟩⟩
  · simp only [τB, RegSet.mem_ofList, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · rw [State.withRegions_gpr, State.withRegions_gpr, h₁.esp, h₂.esp, pb.E]
    · rw [State.withRegions_gpr, State.withRegions_gpr, h₁.ebp, h₂.ebp, pb.E]
    · rw [State.withRegions_gpr, State.withRegions_gpr]; exact hrs r hr
  · simp only [τB, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · obtain ⟨x0, hk⟩ := hsl x hx
      have hlen := hok x (by simp [τB, hx])
      rw [x0] at hlen
      simp only [τB, List.getD_cons_zero] at hlen
      have k160 : k < 160 := by omega
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, State.withRegions_wr, State.withRegions_mem, x0,
        wide, List.getD_cons_zero]
      rw [loc_byte hp₁ s₁.mem k160, loc_byte hp₂ s₂.mem k160]
      exact congrArg _ (hk k hk₁ hk₂)
    · simp only at hk₁ hk₂
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, State.withRegions_wr, State.withRegions_mem,
        wide, List.getD_cons_succ, List.getD_cons_zero]
      rw [arg_byte hp₁ h₁ (by omega), arg_byte hp₂ h₂ (by omega), pb.2 _ (by omega)]
end VG.Proof.Argon2.X86.Derive
