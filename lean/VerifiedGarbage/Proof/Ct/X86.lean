import VerifiedGarbage.Impl.Ct.X86
import VerifiedGarbage.Proof.Ct.Common32
import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
import VerifiedGarbage.Proof.Framework.X86.ArgTaint
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ct.Contract

namespace VG.Proof.Ct.X86
open VG VG.X86 VG.Impl.Ct.X86 VG.Proof.MlDsa.X86.Pack

-- Indices here are after saving EBX: original argument 0 is now slot 1.
def A (s : State) := arg s 1
def N (s : State) := arg s 2
def B (s : State) := arg s 3
def K (s : State) := arg s 4

def Pre (s : State) : Prop :=
  (∀ k, 1 ≤ k → k ≤ 4 → InRegions (s.rd ++ s.wr) (argAddr s k) 4) ∧
  InRegions (s.rd ++ s.wr) ((A s).setWidth 64) (N s).toNat ∧
  InRegions (s.rd ++ s.wr) ((B s).setWidth 64) (K s).toNat ∧
  (A s).toNat + (N s).toNat ≤ 2^32 ∧ (B s).toNat + (K s).toNat ≤ 2^32

def Post (s t : State) : Prop := t.gpr .eax = if Spec.Ct.eq
  (Spec.Ct.bytesAt s.mem ((A s).setWidth 64) (N s).toNat)
  (Spec.Ct.bytesAt s.mem ((B s).setWidth 64) (K s).toNat) then 1 else 0

def Inv (s₀ : State) (i : Nat) (s : State) : Prop :=
  Keep [.eax,.ecx,.edx,.ebx] s₀ s ∧ s.mem = s₀.mem ∧ s.gpr .ecx = BitVec.ofNat 32 i ∧
  s.gpr .ebx = (diff s₀.mem ((A s₀).setWidth 64) ((B s₀).setWidth 64) i).setWidth 32

theorem add0 (a : BitVec 32) : a+0=a := BitVec.add_zero a

theorem arg_ea (s : State) (k : Nat) :
    (s.gpr .esp + BitVec.ofNat 32 (4+4*k)).setWidth 64 = argAddr s k := rfl

theorem sub_beq (a b : BitVec 32) : (a-b==0) = (a==b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  bv_omega

theorem reads_args (s₀ s : State) (hp : Pre s₀)
    (hk : Keep [.eax,.ecx,.edx,.ebx] s₀ s) (hm : s.mem = s₀.mem)
    (k : Nat) (h₁ : 1 ≤ k) (h₄ : k ≤ 4) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ k) 4 ∧ s.mem.readW (argAddr s₀ k) 32 = arg s₀ k := by
  refine ⟨?_, ?_⟩
  · rw [hk.2.1,hk.2.2]; exact hp.1 k h₁ h₄
  · rw [hm]; rfl

theorem reads_byte {rs : List Region} {p : Addr} {n i : Nat} (h : InRegions rs p n)
    (hi : i < n) (hn : n < 2^64) : InRegions rs (p+BitVec.ofNat 64 i) 1 := by
  obtain ⟨r,hr,hc⟩ := h
  exact ⟨r,hr,hc.byte (by rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi)⟩

theorem step_ok (s₀ s : State) (hp : Pre s₀) (hlen : K s₀ = N s₀)
    (i : Nat) (hi : i < (N s₀).toNat) (h : Inv s₀ i s) :
    WP isa (.block step) s fun t => Inv s₀ (i+1) t ∧ t.zf = some (BitVec.ofNat 32 (i+1) == N s₀) := by
  obtain ⟨hk,hm,hx,hd⟩ := h
  have hsp := hk.gpr (r := .esp) (by decide)
  obtain ⟨hra,_⟩ := reads_args s₀ s hp hk hm 1 (by decide) (by decide)
  obtain ⟨hrn,_⟩ := reads_args s₀ s hp hk hm 2 (by decide) (by decide)
  obtain ⟨hrb,_⟩ := reads_args s₀ s hp hk hm 3 (by decide) (by decide)
  have hn := (N s₀).isLt
  have hreadA := reads_byte hp.2.1 hi (by omega)
  have hreadB := reads_byte hp.2.2.1 (by rw [hlen]; exact hi) (by rw [hlen]; omega)
  rw [← hk.2.1, ← hk.2.2] at hreadA hreadB
  have ha : (A s₀ + BitVec.ofNat 32 i).setWidth 64 = (A s₀).setWidth 64 + BitVec.ofNat 64 i :=
    VG.Proof.MlKem.X86.ea_off (by have := hp.2.2.2.1; omega)
  have hb : (B s₀ + BitVec.ofNat 32 i).setWidth 64 = (B s₀).setWidth 64 + BitVec.ofNat 64 i :=
    VG.Proof.MlKem.X86.ea_off (by have := hp.2.2.2.2; rw [hlen] at this; omega)
  have hadd : BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i+1) := by rw [BitVec.ofNat_add]; rfl
  unfold step
  refine WP.mono (WP.keep [.eax,.ecx,.edx,.ebx] (Q := fun t => t.mem = s₀.mem ∧
    t.gpr .ecx = BitVec.ofNat 32 (i+1) ∧
    t.gpr .ebx = (diff s₀.mem ((A s₀).setWidth 64) ((B s₀).setWidth 64) (i+1)).setWidth 32 ∧
    t.zf = some (BitVec.ofNat 32 (i+1) == N s₀)) ?_ (by rfl)) ?_
  · xrun [State.ea,hsp,hx,hd,hm,arg_ea s₀ 1,arg_ea s₀ 2,arg_ea s₀ 3,
      hra,hrn,hrb,
      (show s₀.mem.readW (argAddr s₀ 1) 32 = A s₀ from rfl),
      (show s₀.mem.readW (argAddr s₀ 2) 32 = N s₀ from rfl),
      (show s₀.mem.readW (argAddr s₀ 3) 32 = B s₀ from rfl),ha,hb,hreadA,hreadB,hadd,add0,
      (show ∀ a : BitVec 32, a + BitVec.ofNat 32 0 = a from BitVec.add_zero),
      sub_beq,← BitVec.setWidth_xor,← BitVec.setWidth_or]
    rfl
  · intro t ⟨⟨hm',hx',hd',hz⟩,hk'⟩
    exact ⟨⟨(hk.trans hk').mono (by simp),hm',hx',hd'⟩,hz⟩

theorem loop_ok (s₀ s : State) (hp : Pre s₀) (hlen : K s₀ = N s₀)
    (i : Nat) (hi : i < (N s₀).toNat) (h : Inv s₀ i s) :
    WP isa (.loop (.block step) .ne) s (Inv s₀ (N s₀).toNat) := by
  let n := (N s₀).toNat
  refine WP.loop (M := isa) (fun rem t => ∃ j, j<n ∧ rem=n-j ∧ Inv s₀ j t)
    ?_ (n-i) s ⟨i,hi,rfl,h⟩
  intro rem t ⟨j,hj,hr,ht⟩
  refine WP.mono (step_ok s₀ t hp hlen j hj ht) fun u ⟨hu,hz⟩ => ?_
  by_cases he : j+1=n
  · exact .inl ⟨by simp [eval,hz,he,n],by simpa only [he] using hu⟩
  · have hne : BitVec.ofNat 32 (j+1) ≠ N s₀ := by
      have := (N s₀).isLt
      dsimp [n] at hj he
      bv_omega
    exact .inr ⟨by simp only [eval,hz,beq_eq_false_iff_ne.mpr hne,Option.map_some]; rfl,
      n-(j+1),by omega,j+1,by omega,rfl,hu⟩

theorem finish_ok (s : State) (d : Byte) (h : s.gpr .ebx = d.setWidth 32) :
    WP isa finish s fun t => t.mem=s.mem ∧ t.gpr .eax = if d=0 then 1 else 0 := by
  unfold finish
  xrun [h]
  exact result32 d

theorem equal_ok (s₀ s : State) (hp : Pre s₀) (hlen : K s₀ = N s₀)
    (hk : Keep [.eax,.ecx,.edx,.ebx] s₀ s) (hm : s.mem=s₀.mem) :
    WP isa equal s fun t => t.mem=s₀.mem ∧ Post s₀ t := by
  have hsp := hk.gpr (r := .esp) (by decide)
  obtain ⟨hrn,_⟩ := reads_args s₀ s hp hk hm 2 (by decide) (by decide)
  have start : WP isa (.block [.mov .ebx (.imm 0), .mov .ecx (.imm 0),
      .mov .eax (.mem {base := .esp, disp := 12}), .alu .cmp .ecx (.reg .eax)]) s fun t =>
      Inv s₀ 0 t ∧ t.zf = some (N s₀ == 0) := by
    refine WP.mono (WP.keep [.eax,.ecx,.edx,.ebx] (Q := fun t => t.mem=s₀.mem ∧
      t.gpr .ecx=0 ∧ t.gpr .ebx=0 ∧ t.zf=some (N s₀ == 0)) ?_ (by rfl)) ?_
    · xrun [State.ea,hsp,hm,arg_ea s₀ 2,hrn,
        (show s₀.mem.readW (argAddr s₀ 2) 32 = N s₀ from rfl),sub_beq]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      exact eq_comm
    · intro t ⟨⟨hm',hx,hd,hz⟩,hk'⟩
      exact ⟨⟨(hk.trans hk').mono (by simp),hm',hx,hd⟩,hz⟩
  unfold equal
  refine WP.seq (WP.mono start fun t ⟨ht,hz⟩ => WP.seq ?_)
  have middle : WP isa (.ite .e (.block []) (.loop (.block step) .ne)) t (Inv s₀ (N s₀).toNat) := by
    by_cases he : N s₀=0
    · refine WP.ite true (by simp [eval,hz,he]) (fun _ => WP.block_nil ?_) (by simp)
      simpa only [he,show (0 : BitVec 32).toNat=0 from rfl] using ht
    · exact WP.ite false (by simp only [eval,hz,beq_eq_false_iff_ne.mpr he]) (by simp)
        (fun _ => loop_ok s₀ t hp hlen 0 (by bv_omega) ht)
  refine WP.mono middle fun u hu => WP.mono (finish_ok u _ hu.2.2.2) fun v ⟨hmv,hv⟩ => ?_
  refine ⟨hmv.trans hu.2.1, ?_⟩
  unfold Post
  rw [hlen,diff_spec]
  simpa only [decide_eq_true_eq] using hv

theorem body_ok (s₀ : State) (hp : Pre s₀) :
    WP isa body s₀ fun t => t.mem=s₀.mem ∧ Post s₀ t := by
  have hrn := hp.1 2 (by decide) (by decide)
  have hrk := hp.1 4 (by decide) (by decide)
  have start : WP isa (.block [.mov .eax (.mem {base := .esp, disp := 12}),
      .mov .edx (.mem {base := .esp, disp := 20}), .alu .cmp .eax (.reg .edx)]) s₀ fun t =>
      Keep [.eax,.ecx,.edx,.ebx] s₀ t ∧ t.mem=s₀.mem ∧ t.zf=some (N s₀ == K s₀) := by
    refine WP.mono (WP.keep [.eax,.ecx,.edx,.ebx] (Q := fun t =>
      t.mem=s₀.mem ∧ t.zf=some (N s₀ == K s₀)) ?_ (by rfl)) ?_
    · xrun [State.ea,arg_ea s₀ 2,arg_ea s₀ 4,hrn,hrk,
        (show s₀.mem.readW (argAddr s₀ 2) 32 = N s₀ from rfl),
        (show s₀.mem.readW (argAddr s₀ 4) 32 = K s₀ from rfl),sub_beq]
    · intro t ⟨h,hk⟩; exact ⟨hk,h⟩
  unfold body
  refine WP.seq (WP.mono start fun t ⟨hk,hm,hz⟩ => ?_)
  by_cases he : N s₀=K s₀
  · exact WP.ite true (by simp [eval,hz,he]) (fun _ => equal_ok s₀ t hp he.symm hk hm) (by simp)
  · refine WP.ite false (by simp [eval,hz,he]) (by simp) (fun _ => ?_)
    have hn : (N s₀).toNat ≠ (K s₀).toNat := fun h => he (BitVec.eq_of_toNat_eq h)
    xrun [hm,Post,lengths_ne _ _ _ hn]

def frameR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 4#64,4⟩

def contract : Contract isa where
  pre s := s.rd = [⟨(arg s 0).setWidth 64,(arg s 1).toNat⟩,
      ⟨(arg s 2).setWidth 64,(arg s 3).toNat⟩,⟨argAddr s 0,16⟩] ∧ s.wr=[] ∧
    (arg s 0).toNat+(arg s 1).toNat ≤ 2^32 ∧ (arg s 2).toNat+(arg s 3).toNat ≤ 2^32 ∧
    4 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat+20 ≤ 2^32 ∧
    Region.Disjoint ⟨(arg s 0).setWidth 64,(arg s 1).toNat⟩ (frameR s) ∧
    Region.Disjoint ⟨(arg s 2).setWidth 64,(arg s 3).toNat⟩ (frameR s)
  post s t := t.gpr .eax = if Spec.Ct.eq
    (Spec.Ct.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
    (Spec.Ct.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) then 1 else 0
  pub s t := s.gpr .esp=t.gpr .esp ∧ ∀ i<4, arg s i=arg t i

theorem frame_mem (s : State) (h : 4 ≤ (s.gpr .esp).toNat) :
    Frame [frameR s] s.mem (pushed [.ebx] s).mem := by
  have hf := pushed_frame (rs := [.ebx]) (s := s) (by decide) h
  change Frame [⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64,4⟩] _ _ at hf
  rw [Taint.sub_setWidth h] at hf
  exact hf

theorem arg_shift_addr (s : State) (k : Nat) :
    argAddr (pushed [.ebx] s) (k+1) = argAddr s k := by
  unfold argAddr
  rw [pushed_esp]
  have hn : 4+4*(k+1) = 4+(4+4*k) := by omega
  rw [hn,BitVec.ofNat_add,← BitVec.add_assoc]
  rw [show 4*([Reg.ebx] : List Reg).length = 4 from rfl, BitVec.sub_add_cancel]

theorem arg_addr (s : State) (hn : (s.gpr .esp).toNat+20 ≤ 2^32) (k : Nat) (hk : k<4) :
    argAddr s k = (s.gpr .esp).setWidth 64+BitVec.ofNat 64 (4+4*k) :=
  VG.Proof.MlKem.X86.ea_off (by omega)

theorem arg_contains (s : State) (hp : contract.pre s) (k : Nat) (hk : k<4) :
    (⟨argAddr s 0,16⟩ : Region).Contains (argAddr s k) 4 := by
  rw [arg_addr s hp.2.2.2.2.2.1 0 (by decide),arg_addr s hp.2.2.2.2.2.1 k hk]
  exact Offset.contains _ (by omega) (by omega) (by decide)

theorem arg_frame_disjoint (s : State) (hp : contract.pre s) :
    Region.Disjoint ⟨argAddr s 0,16⟩ (frameR s) := by
  rw [arg_addr s hp.2.2.2.2.2.1 0 (by decide)]
  exact (Offset.disjoint_below_above (s.gpr .esp |>.setWidth 64) (m := 4) (a := 4) (l := 16)
    (by decide)).symm

theorem arg_shift (s : State) (hp : contract.pre s) (k : Nat) (hk : k<4) :
    arg (pushed [.ebx] s) (k+1) = arg s k := by
  unfold arg
  rw [arg_shift_addr]
  exact (frame_mem s hp.2.2.2.2.1).readW (arg_contains s hp k hk)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact arg_frame_disjoint s hp) (by decide)

theorem pushed_pre (s : State) (hp : contract.pre s) : Pre (pushed [.ebx] s) := by
  have ha := arg_shift s hp 0 (by decide)
  have hn := arg_shift s hp 1 (by decide)
  have hb := arg_shift s hp 2 (by decide)
  have hk := arg_shift s hp 3 (by decide)
  unfold Pre A N B K
  rw [ha,hn,hb,hk]
  refine ⟨?_,?_,?_,hp.2.2.1,hp.2.2.2.1⟩
  · intro k h1 h4
    have he : k=(k-1)+1 := by omega
    rw [he,arg_shift_addr]
    exact ⟨⟨argAddr s 0,16⟩,by rw [pushed_rd,hp.1]; simp,
      arg_contains s hp (k-1) (by omega)⟩
  · exact ⟨_,by rw [pushed_rd,hp.1]; simp,Region.contains_self _ _⟩
  · exact ⟨_,by rw [pushed_rd,hp.1]; simp,Region.contains_self _ _⟩

theorem push_bytes (s : State) (hp : contract.pre s) (p : Addr) (n : Nat)
    (hd : Region.Disjoint ⟨p,n⟩ (frameR s)) (hn : n ≤ 2^64) :
    Spec.Ct.bytesAt (pushed [.ebx] s).mem p n = Spec.Ct.bytesAt s.mem p n := by
  unfold Spec.Ct.bytesAt
  apply List.map_congr_left
  intro i hi
  exact (frame_mem s hp.2.2.2.2.1).bytes (R := ⟨p,n⟩)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hd) hn (List.mem_range.mp hi)

theorem correct (s : State) (hp : contract.pre s) :
    WP isa eq s fun t => abiPreserved s t ∧ contract.post s t := by
  unfold eq
  have noSp : NoSp body := by intro i hi; have h : body.allInstrs (fun i => !Taint.clobbers i .esp)=true := by decide +kernel
                              rw [Code.allInstrs_eq] at h
                              simpa only [Bool.not_eq_true'] using List.all_eq_true.mp h i hi
  apply WP.frame (rs := [.ebx]) (by decide) (by decide) (by decide) hp.2.2.2.2.1 noSp
  obtain ⟨tr,t,he,⟨hm,ho⟩,hk⟩ := WP.keep [.eax,.ecx,.edx,.ebx] (body_ok (pushed [.ebx] s) (pushed_pre s hp)) (by rfl)
  have hsp := hk.gpr (r := .esp) (by decide)
  refine ⟨tr,t,he,⟨?_,?_⟩,?_⟩
  · intro r hr
    by_cases hb : r=.ebx
    · subst r
      change (popReg t .ebx 1).gpr .ebx=s.gpr .ebx
      simp only [popReg,State.setReg,reduceCtorEq,ite_true,ite_false]
      rw [hm,hsp]
      have hw := pushed_word (rs := [.ebx]) (s := s) (by decide) hp.2.2.2.2.1 (i := 0) (by decide)
      change (pushed [.ebx] s).mem.readW (((pushed [.ebx] s).gpr .esp + BitVec.ofNat 32 0).setWidth 64) 32 = s.gpr .ebx at hw
      simpa only [BitVec.add_zero] using hw
    · by_cases hs : r=.esp
      · subst r
        change (popReg t .ebx 1).gpr .esp=s.gpr .esp
        rw [(popReg_eq t .ebx 1).2.2.1,hsp,pushed_esp]
        exact BitVec.sub_add_cancel _ _
      · change (popReg t .ebx 1).gpr r=s.gpr r
        rw [(popReg_eq t .ebx 1).2.2.2 r hs hb,hk.gpr (by cases r <;> simp_all [calleeSaved]),pushed_gpr _ _ hs]
  · change (popReg t .ebx 1).mem.readW ((s.gpr .esp).setWidth 64) 32 = _
    rw [(popReg_rest t .ebx 1).1,hm]
    apply (frame_mem s hp.2.2.2.2.1).readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.base_disjoint_below _ (by decide)
  · change (popReg t .ebx 1).gpr .eax = _
    rw [(popReg_eq t .ebx 1).2.2.2 .eax (by decide) (by decide)]
    unfold Post A N B K at ho
    rw [arg_shift s hp 0 (by decide),arg_shift s hp 1 (by decide),arg_shift s hp 2 (by decide),
      arg_shift s hp 3 (by decide)] at ho
    rw [push_bytes s hp _ _ hp.2.2.2.2.2.2.1 (by have := (arg s 1).isLt; omega),
      push_bytes s hp _ _ hp.2.2.2.2.2.2.2 (by have := (arg s 3).isLt; omega)] at ho
    exact ho

-- The body sees the original public arguments above the saved EBX word.
def bodyTaint : VG.X86.Taint.T := { argTaint [] 20 with stk := [some 4] }

theorem pushed_argByte (s : State) (hp : contract.pre s) (k : Nat) :
    Taint.argByte (pushed [.ebx] s) (4+k) = Taint.argByte s k := by
  unfold Taint.argByte
  rw [pushed_esp]
  change (s.gpr .esp-4#32).setWidth 64+BitVec.ofNat 64 (4+k) = _
  rw [Taint.sub_setWidth hp.2.2.2.2.1,BitVec.ofNat_add,← BitVec.add_assoc,BitVec.sub_add_cancel]

theorem body_wf (s : State) (hp : contract.pre s) : Taint.Wf bodyTaint (pushed [.ebx] s) := by
  refine ⟨fun h => absurd rfl h, (fun _ h => nomatch h), (fun _ h => nomatch h),
    ?_, (fun _ h => nomatch h), ?_, ?_, fun h => by contradiction⟩
  · intro _
    constructor
    · change ((pushed [.ebx] s).gpr .esp).toNat+4+20 ≤ 2^32
      rw [pushed_esp]
      change (s.gpr .esp-4#32).toNat+4+20 ≤ 2^32
      rw [sub_toNat hp.2.2.2.2.1]
      have := hp.2.2.2.2.2.1
      omega
    · change ∀ r ∈ (pushed [.ebx] s).wr, Region.Disjoint ⟨Taint.argByte (pushed [.ebx] s) (4+0),20⟩ r
      rw [pushed_argByte s hp,pushed_wr,hp.2.1]
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      change Region.Disjoint ⟨(s.gpr .esp).setWidth 64+0#64,20⟩ ⟨(s.gpr .esp-4#32).setWidth 64,4⟩
      rw [BitVec.add_zero,Taint.sub_setWidth hp.2.2.2.2.1]
      exact Offset.base_disjoint_below _ (by decide)
  · change ((pushed [.ebx] s).gpr .esp).toNat+4 < 2^32
    rw [pushed_esp]
    change (s.gpr .esp-4#32).toNat+4 < 2^32
    rw [sub_toNat hp.2.2.2.2.1]
    have := (s.gpr .esp).isLt
    omega
  · intro p hp'
    obtain rfl := List.mem_singleton.mp hp'
    change (pushed [.ebx] s).wr[0]? = some ⟨((pushed [.ebx] s).gpr .esp+0#32).setWidth 64,4⟩
    rw [pushed_wr,pushed_esp,BitVec.add_zero]
    rfl

theorem body_agree (s t : State) (hs : contract.pre s) (ht : contract.pre t)
    (hp : contract.pub s t) : VG.X86.Taint.Agree bodyTaint (pushed [.ebx] s) (pushed [.ebx] t) := by
  have hsp : (pushed [.ebx] s).gpr .esp = (pushed [.ebx] t).gpr .esp := by
    rw [pushed_esp,pushed_esp,hp.1]
  refine ⟨⟨?_,(fun h => nomatch h)⟩,fun h => absurd rfl h,body_wf s hs,body_wf t ht,
    (fun _ h => nomatch h),(fun _ h => nomatch h),fun _ => hsp,?_⟩
  · intro r hr
    have he : r=.esp := by simpa only [bodyTaint,argTaint,RegSet.mem_ofList,List.mem_singleton] using hr
    subst r
    exact hsp
  · intro k h4 hk
    change (pushed [.ebx] s).mem (Taint.argByte (pushed [.ebx] s) (4+k)) =
      (pushed [.ebx] t).mem (Taint.argByte (pushed [.ebx] t) (4+k))
    have read (u : State) (hu : contract.pre u) :
        (pushed [.ebx] u).mem (Taint.argByte (pushed [.ebx] u) (4+k)) =
          u.mem (Taint.argByte u k) := by
      rw [pushed_argByte u hu]
      apply frame_mem u hu.2.2.2.2.1
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact (Offset.disjoint_below (u.gpr .esp |>.setWidth 64) (n := 4) (d := k) (k := 1)
        (by change k<20 at hk; omega)) _ (Region.contains_self _ _)
    rw [read s hs,read t ht]
    have ha := agree_argTaint (k := 4) (rs := []) (s₁ := s) (s₂ := t)
      (fun _ h => nomatch h) hp.1
      ⟨hs.2.2.2.2.2.1,by rw [hs.2.1]; simp⟩
      ⟨ht.2.2.2.2.2.1,by rw [ht.2.1]; simp⟩ hp.2
    simpa only [argTaint,Taint.depth,Nat.zero_add] using ha.argMem k h4 hk

theorem body_ct : ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree bodyTaint) body :=
  VG.Taint.constantTime (A := taint) bodyTaint (fun _ _ _ _ h => h) (by taint_decide)

theorem constantTime : ConstantTime isa contract.pre contract.pub eq := by
  intro s t ts tt s' t' hs ht hp es et
  have hrel := RelCT.frame (rs := [.ebx]) (r := .ebx) (k := 1) (body := body)
    (P := fun s t => contract.pre s ∧ contract.pre t ∧ contract.pub s t)
    (fun _ _ h => h.2.2.1) (by
      rintro _ _ ta tb a' b' ⟨a,b,⟨ha,hb,hpub⟩,rfl,rfl⟩ ea eb
      exact ⟨body_ct _ _ _ _ _ _ trivial trivial (body_agree a b ha hb hpub) ea eb,trivial⟩)
  exact (hrel _ _ _ _ _ _ ⟨hs,ht,hp⟩ es et).1

def sat : State where
  gpr r := if r=.esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0,0⟩,⟨0,0⟩,⟨0x4004,16⟩]
  wr := []

theorem verified : Verified target eq (Spec.Ct.eqContract abi 4) := by
  apply Verified.of_correct (k := contract)
  · exact correct
  · exact constantTime
  · refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
    · sig_implies_pre [Spec.Ct.eqContract,Spec.Ct.eqSig,contract,frameR,abi,argSlots,argVal,argBytes]
    · intro s t _ h
      sig_post [Spec.Ct.eqContract,Spec.Ct.eqSig,abi,argSlots,argVal,argBytes]
      rw [BitVec.setWidth_append_eq_right]
      exact h
    · sig_implies_pub [Spec.Ct.eqContract,Spec.Ct.eqSig,contract,abi,argSlots,argVal,argBytes]
    · sig_implies_sat [Spec.Ct.eqContract,Spec.Ct.eqSig,abi,argSlots,argVal,argBytes]
        [sat,arg,argAddr,Mem.readW,Mem.read] using sat
end VG.Proof.Ct.X86
